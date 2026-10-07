"""Correctness and resumability tests for the checkpointed batch driver
(fastfusion/batchrun.py) that runs the full pipeline over every group of a
given order. Exercises it on a handful of real groups of order 5^7 so a
regression here is caught before a multi-day unattended run relies on it."""
import json
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from fastfusion.batchrun import done_indices, run_batch


def test_resumable_small_range():
    results_path = tempfile.mktemp(suffix=".jsonl")
    try:
        run_batch(78125, 1, 4, results_path, workers=2, export_chunk_size=4, timeout=300)
        recs = {}
        with open(results_path) as f:
            for line in f:
                r = json.loads(line)
                recs[r["index"]] = r
        assert set(recs) == {1, 2, 3, 4}
        for idx, r in recs.items():
            assert r.get("error") is None, f"idx={idx}: {r.get('error')}"
            assert r["num_raw_candidates"] >= 0
            assert r["num_essential_aut_classes"] == len(r["essentials"])

        # idx=1 is elementary abelian (rank 7): no proto-essential subgroups
        # possible by construction (central_series_candidates needs A
        # properly inside S' = 1).
        assert recs[1]["num_raw_candidates"] == 0
        assert recs[1]["num_essential_aut_classes"] == 0

        # Resuming with the same range must be a no-op: no new lines added.
        before = done_indices(results_path)
        run_batch(78125, 1, 4, results_path, workers=2)
        after = done_indices(results_path)
        assert before == after == {1, 2, 3, 4}
        with open(results_path) as f:
            assert sum(1 for _ in f) == 4

        # Extending the range only adds the new indices, not re-running 1-4.
        run_batch(78125, 1, 6, results_path, workers=2, export_chunk_size=4, timeout=300)
        with open(results_path) as f:
            all_idx = [json.loads(line)["index"] for line in f]
        assert sorted(all_idx) == [1, 2, 3, 4, 5, 6]
    finally:
        if os.path.exists(results_path):
            os.unlink(results_path)


def test_timeout_is_recorded_and_resumable():
    results_path = tempfile.mktemp(suffix=".jsonl")
    try:
        run_batch(78125, 2, 2, results_path, workers=1, export_chunk_size=1, timeout=1)
        with open(results_path) as f:
            lines = [json.loads(l) for l in f]
        assert len(lines) == 1
        assert lines[0]["index"] == 2
        assert "timeout" in lines[0]["error"]

        # A pathological per-group timeout must not leave the GAP/worker
        # subprocess running in the background.
        import time
        time.sleep(0.5)
        out = subprocess.run(["ps", "aux"], capture_output=True, text=True).stdout
        assert "_run_one_group.py" not in out
    finally:
        if os.path.exists(results_path):
            os.unlink(results_path)


if __name__ == "__main__":
    test_resumable_small_range()
    print("test_resumable_small_range PASSED")
    test_timeout_is_recorded_and_resumable()
    print("test_timeout_is_recorded_and_resumable PASSED")
