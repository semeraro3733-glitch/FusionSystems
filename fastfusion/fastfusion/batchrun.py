"""Checkpointed batch driver: runs the full proto-essential-subgroup search
(protoessential.py) over every group SmallGroup(size, idx), idx in a given
range, pulling presentations and Aut(S) generators from GAP's SmallGroups
library via the bridge (bridge/export_batch.g).

This exists because the task is "every group of order 5^7 (34297 of them)
and 3^8 (1396077)", not a handful of hand-picked examples, and -- after
investigating and rejecting two candidate group-level shortcuts (see
README/commit history: both turned out to characterise exotic-fusion-system
support, not the presence of proto-essential subgroups, and were confirmed
wrong by direct counterexample) -- there is no known way to skip a group
entirely. The only available speedup is running the validated per-group
pipeline on every group, as fast and as unattended as possible.

Design, driven by running this for days unattended:
  * GAP export happens in chunks (one `gap` subprocess per
    `export_chunk_size` groups), amortising GAP's startup/package-load cost.
    A chunk that fails (GAP crash, hang) is bisected and retried on each
    half independently, isolating a single pathological index to its own
    export call instead of losing a whole chunk's progress; an index that
    still fails on its own is recorded as an export error and skipped.
  * Each group's pipeline run happens in its own short-lived OS process
    (_run_one_group.py), so a wall-clock timeout can simply kill that
    process without disturbing the driver or any other group, and a crash
    (segfault, OOM) in one group can't take the batch down.
  * Results are appended to `results_path` as one JSON line per group, as
    soon as that group finishes -- so killing and restarting this driver at
    any point resumes from the last completed group, never redoing work.

Usage:
    python3 -m fastfusion.batchrun <size> <start> <stop> <results.jsonl> \\
        [--workers 4] [--export-chunk-size 500] [--timeout 1800]
"""
from __future__ import annotations

import concurrent.futures
import json
import os
import subprocess
import sys
import tempfile
import time
from typing import List, Optional, Set

BRIDGE_DIR = os.path.join(os.path.dirname(__file__), "..", "bridge")
WORKER_SCRIPT = os.path.join(os.path.dirname(__file__), "_run_one_group.py")

DEFAULT_TIMEOUT_SECONDS = 1800  # generous given the ~30-45s/group observed average


def done_indices(results_path: str) -> Set[int]:
    done = set()
    if not os.path.exists(results_path):
        return done
    with open(results_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                continue
            if "index" in rec:
                done.add(rec["index"])
    return done


def _export_chunk(size: int, lo: int, hi: int, outfile: str, timeout: int) -> None:
    subprocess.run(
        ["gap", "-q", "-b", "-c",
         f'Read("export_batch.g"); RunExportBatch({size},{lo},{hi},"{outfile}"); QUIT;'],
        cwd=BRIDGE_DIR, stdin=subprocess.DEVNULL, capture_output=True, text=True,
        timeout=timeout, check=True,
    )


def export_range(size: int, lo: int, hi: int, workdir: str) -> List[dict]:
    """Export SmallGroup(size, idx) for idx in [lo, hi] via GAP, returning
    one decoded JSON record per index. On any failure, bisects the range and
    retries each half on its own (see module docstring); a singleton range
    that fails on its own is reported as a one-entry "error" record rather
    than retried indefinitely."""
    timeout = max(600, (hi - lo + 1) * 30)
    export_path = os.path.join(workdir, f"export_{size}_{lo}_{hi}.jsonl")
    failed = False
    try:
        _export_chunk(size, lo, hi, export_path, timeout)
        records = []
        with open(export_path) as f:
            for line in f:
                line = line.strip()
                if line:
                    records.append(json.loads(line))
        if len(records) != hi - lo + 1:
            failed = True
        else:
            return records
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, json.JSONDecodeError):
        failed = True
    finally:
        if os.path.exists(export_path):
            os.remove(export_path)
    assert failed
    if lo == hi:
        return [{"size": size, "index": lo, "error": "GAP export failed for this index"}]
    mid = (lo + hi) // 2
    return export_range(size, lo, mid, workdir) + export_range(size, mid + 1, hi, workdir)


def run_one_group(rec: dict, workdir: str, timeout: int) -> dict:
    rec_path = os.path.join(workdir, f"rec_{rec['size']}_{rec['index']}.json")
    with open(rec_path, "w") as f:
        json.dump(rec, f)
    t0 = time.time()
    try:
        proc = subprocess.run(
            [sys.executable, WORKER_SCRIPT, rec_path],
            capture_output=True, text=True, timeout=timeout,
        )
        if proc.returncode != 0:
            return {"size": rec["size"], "index": rec["index"],
                    "error": f"worker exited {proc.returncode}: {proc.stderr[-2000:]}",
                    "time_seconds": time.time() - t0}
        return json.loads(proc.stdout.strip().splitlines()[-1])
    except subprocess.TimeoutExpired:
        return {"size": rec["size"], "index": rec["index"],
                "error": f"timeout after {timeout}s", "time_seconds": time.time() - t0}
    finally:
        if os.path.exists(rec_path):
            os.remove(rec_path)


def run_batch(size: int, start: int, stop: int, results_path: str,
              workers: int = 4, export_chunk_size: int = 500,
              timeout: int = DEFAULT_TIMEOUT_SECONDS,
              workdir: Optional[str] = None) -> None:
    done = done_indices(results_path)
    todo = [i for i in range(start, stop + 1) if i not in done]
    if not todo:
        print(f"nothing to do: all {stop - start + 1} groups already in {results_path}", flush=True)
        return
    print(f"{len(todo)}/{stop - start + 1} groups remaining in [{start},{stop}] "
          f"({len(done)} already done)", flush=True)

    owns_workdir = workdir is None
    if workdir is None:
        workdir = tempfile.mkdtemp(prefix=f"ffexport_{size}_")
    os.makedirs(workdir, exist_ok=True)

    t_start = time.time()
    n_completed = 0
    with open(results_path, "a") as out:
        for chunk_start in range(0, len(todo), export_chunk_size):
            chunk = todo[chunk_start:chunk_start + export_chunk_size]
            chunk_set = set(chunk)
            t0 = time.time()
            exported = export_range(size, min(chunk), max(chunk), workdir)
            records, export_errors = [], []
            for rec in exported:
                if rec["index"] not in chunk_set:
                    continue
                (export_errors if "error" in rec else records).append(rec)
            print(f"[export] {len(records)} ok, {len(export_errors)} failed, "
                  f"range [{min(chunk)},{max(chunk)}] in {time.time() - t0:.1f}s", flush=True)

            for rec in export_errors:
                out.write(json.dumps(rec) + "\n")
                out.flush()
                n_completed += 1
                print(f"  idx={rec['index']}: EXPORT ERROR: {rec['error']}", flush=True)

            with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
                futures = {pool.submit(run_one_group, rec, workdir, timeout): rec for rec in records}
                for fut in concurrent.futures.as_completed(futures):
                    result = fut.result()
                    out.write(json.dumps(result) + "\n")
                    out.flush()
                    n_completed += 1
                    if result.get("error"):
                        print(f"  idx={result['index']}: ERROR: {result['error'][:200]}", flush=True)
                    else:
                        print(f"  idx={result['index']}: "
                              f"{result['num_essential_aut_classes']} essential class(es) "
                              f"({result['time_seconds']:.1f}s)", flush=True)
                    if n_completed % 20 == 0:
                        elapsed = time.time() - t_start
                        rate = n_completed / elapsed
                        remaining = len(todo) - n_completed
                        eta_h = remaining / rate / 3600 if rate > 0 else float("inf")
                        print(f"[progress] {n_completed}/{len(todo)} done, "
                              f"{elapsed / 60:.1f}min elapsed, ETA {eta_h:.1f}h", flush=True)

    if owns_workdir:
        try:
            os.rmdir(workdir)
        except OSError:
            pass
    print(f"batch complete: {n_completed} groups in {(time.time() - t_start) / 3600:.2f}h", flush=True)


def main():
    import argparse
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("size", type=int)
    ap.add_argument("start", type=int)
    ap.add_argument("stop", type=int)
    ap.add_argument("results_path")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--export-chunk-size", type=int, default=500)
    ap.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT_SECONDS)
    args = ap.parse_args()
    run_batch(args.size, args.start, args.stop, args.results_path,
              workers=args.workers, export_chunk_size=args.export_chunk_size,
              timeout=args.timeout)


if __name__ == "__main__":
    main()
