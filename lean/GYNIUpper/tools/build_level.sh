#!/usr/bin/env bash
# Build the kernel-check files and the main file of one level (data files must be built already).
# usage: bash GYNIUpper/tools/build_level.sh L8 2000
set -uo pipefail
cd "$(dirname "$0")/../.."
LV="$1"; PK="${2:-2000}"
t0=$(date +%s)
for f in GYNIUpper/$LV/Chk*.lean; do
  m="$LV/$(basename "$f" .lean)"
  echo "== GYNIUpper/$m.lean (start $(date +%H:%M:%S))"
  bash GYNIUpper/tools/ub_one.sh "GYNIUpper/$m" "$PK" 2>&1 | grep -E "error|RESULT" | head -20
done
echo "== GYNIUpper/$LV/Main.lean (start $(date +%H:%M:%S))"
bash GYNIUpper/tools/ub_one.sh "GYNIUpper/$LV/Main" 3800 2>&1 | grep -E -A8 "error|RESULT" | head -40
echo "== build_level $LV done: $(( $(date +%s) - t0 )) s"
