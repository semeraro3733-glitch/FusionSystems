#!/usr/bin/env python3
"""Summarise data/stage1b.txt: id;status;|Aut(S)|=..;[|Aut:O^3|=..;][reason;]protos;time
A proto is [order,index,elab,abelian,rank,nS]."""
import os, re, sys, collections
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
def read_joined(fn):
    out, cur = [], ""
    with open(fn) as f:
        for line in f:
            line = line.rstrip("\n")
            if line.endswith("\\"):
                cur += line[:-1]; continue
            cur += line
            if cur.strip(): out.append(cur)
            cur = ""
    return out
lines = read_joined(os.path.join(base, "data", "stage1b.txt"))
proto_re = re.compile(r"\[(\d+),(\d+),(true|false),(true|false),(\d+),(\d+)\]")
status = collections.Counter(); reasons = collections.Counter(); surv = []
for line in lines:
    p = line.split(";")
    if len(p) < 3 or not p[0].isdigit(): continue
    gid = int(p[0]); st = p[1]; status[st] += 1
    if st == "reject":
        reasons[[x for x in p if "(R" in x or "Stage 1a" in x][0] if any("(R" in x or "Stage 1a" in x for x in p) else p[3]] += 1
    elif st == "survive":
        protos = [(int(o), int(i), e == "true", a == "true", int(r), int(n)) for (o, i, e, a, r, n) in proto_re.findall(line)]
        aut = [x for x in p if x.startswith("|Aut(S)|=")][0][9:]
        surv.append((gid, int(aut), protos))
def difficulty(s):
    gid, aut, protos = s
    el = max([o for (o, i, e, a, r, n) in protos if e], default=1)
    ab = max([o for (o, i, e, a, r, n) in protos if a], default=1)
    return (el, ab, len(protos), gid)
surv.sort(key=difficulty)
print("stage 1b: %d groups, status %s" % (sum(status.values()), dict(status)))
for r, c in reasons.most_common(): print("   %5d  %s" % (c, r))
print("survivors by difficulty (id, |Aut(S)|, protos [order,index,elab,abelian,rank,#S-classes]):")
for gid, aut, protos in surv:
    print("   %7d  %12d  %s" % (gid, aut, " ".join("[%d,%d,%s,%s,%d,%d]" % (o, i, "e" if e else "-", "a" if a else "-", r, n) for (o, i, e, a, r, n) in protos)))
with open(os.path.join(base, "data", "stage1b_survivors.txt"), "w") as f:
    for gid, aut, protos in surv:
        f.write("%d;%d;%s\n" % (gid, aut, " ".join("[%d,%d,%s,%s,%d,%d]" % (o, i, str(e).lower(), str(a).lower(), r, n) for (o, i, e, a, r, n) in protos)))
