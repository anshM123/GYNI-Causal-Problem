#!/usr/bin/env bash
# GYNIUpper, Lueders normal form (Lemma 1 of the GYNI upper-bound proof): compile the Lueders files
# in order, print the axioms of the main theorems, and grep for forbidden keywords.
#
# Run from anywhere (Windows, Git Bash, Lean toolchain in %USERPROFILE%\.elan\bin):
#   bash GYNIUpper/check_lueders.sh 2>&1 | tee GYNIUpper/logs_lueders/check_lueders.log
#
# Every file is elaborated by `lake env lean` (one process at a time; the .olean goes to the
# git-ignored .lake/build/lib/lean/GYNIUpper/). Before each Lean process, GYNIUpper/lueders_step.ps1
# waits (polling every 60 s) until no other lean.exe runs and Available MBytes >= expected peak
# working set + 1500 MB; afterwards it prints wall time, peak working set and peak private bytes.
# A process that dies without a Lean error (out-of-memory guard) is retried once after 2 minutes.
set -euo pipefail
cd "$(dirname "$0")/.."
STEP="powershell -NoProfile -ExecutionPolicy Bypass -File GYNIUpper/lueders_step.ps1"
t0=$(date +%s)
for f in LuedersChoi LuedersDilation LuedersNormalForm; do
  echo "== GYNIUpper/$f.lean  (start $(date +%H:%M:%S))"
  $STEP -File "GYNIUpper/$f.lean" -Olean ".lake/build/lib/lean/GYNIUpper/$f.olean" -PeakMB 3500
done
echo "== GYNIUpper/AxiomsLueders.lean  (start $(date +%H:%M:%S))"
$STEP -File "GYNIUpper/AxiomsLueders.lean" -PeakMB 3500
echo "== forbidden keywords (sorry/admit/axiom/native_decide) in the Lueders files:"
grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' \
  GYNIUpper/Lueders*.lean GYNIUpper/AxiomsLueders.lean || echo "none"
echo "== check_lueders.sh done: $(( $(date +%s) - t0 )) s"
