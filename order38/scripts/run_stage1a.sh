#!/bin/sh
# Stage 1a over all groups of order 3^8 in NPROC parallel GAP processes.
# Resumable: each process appends to data/stage1a_<r>.txt and continues
# after the last id it has written.
#   usage: sh run_stage1a.sh [NPROC] [LAST]
NPROC=${1:-4}
LAST=${2:-1396077}
DIR=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$DIR/data/stage1a" "$DIR/logs"
r=0
while [ $r -lt $NPROC ]; do
  out="$DIR/data/stage1a/part_$r.txt"
  prog="$DIR/data/stage1a/progress_$r.txt"
  start=$((r+1))
  if [ -s "$out" ]; then
    last=$(tail -n 1 "$out" | cut -d';' -f1)
    start=$((last+NPROC))
  fi
  pidfile="$DIR/data/stage1a/pid_$r.txt"
  if [ -s "$pidfile" ] && kill -0 "$(cat "$pidfile")" 2>/dev/null; then
    echo "process $r: still running (pid $(cat "$pidfile"))"
  elif [ $start -le $LAST ]; then
    nohup gap -q -b -o 2g -l ";$DIR/../gap" -c "Read(\"$DIR/scripts/reduce.g\"); FS38_Run($start, $NPROC, $LAST, \"$out\", \"$prog\"); QUIT;" \
      > "$DIR/logs/stage1a_$r.log" 2>&1 &
    echo $! > "$pidfile"
    echo "process $r: ids $start, $((start+NPROC)), ... <= $LAST (pid $!)"
  else
    echo "process $r: done"
  fi
  r=$((r+1))
done
