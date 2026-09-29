#!/usr/bin/env bash
# GYNIUpper, upper bound: compiles every file of the upper-bound formalisation in dependency order
# and greps for forbidden keywords.
#
# Run from anywhere (Windows, Git Bash, Lean toolchain in %USERPROFILE%\.elan\bin):
#   bash GYNIUpper/check_upper.sh 2>&1 | tee GYNIUpper/logs_upper/check_upper.log
#
# Every file is elaborated by `lake env lean` (one process at a time; the .olean goes to
# .lake/build/lib/lean/GYNIUpper/). Before each Lean process, tools/ub_step.ps1 waits (polling
# every 60 s) until no other lean.exe runs and Available MBytes >= expected peak working set
# + 1.5 GB (second argument of `build`, measured); afterwards it prints wall time, peak working set
# and peak private bytes. A process that dies without a Lean error is retried once after 2 minutes.
#
# Prerequisites (built by GYNIProof/check.sh and GYNIUpper/check_lueders.sh, not rebuilt here):
# GYNIProof/{IntLit,Data,Core,Defs,BlockPSD}.olean and GYNIUpper/Lueders{Choi,Dilation,NormalForm}.olean.
# The generated files L2/*.lean and L8/*.lean are reproduced by
#   python GYNIUpper/tools/make_cert.py 2 1e-7            (level-2 certificate, data/cert3_L2.pkl)
#   python GYNIUpper/tools/averaged_cert.py <cert> <avg>  (symmetry-free certificate)
#   python GYNIUpper/tools/export_lean.py <avg> GYNIUpper/L<k> L<k> 24 <rows/thm> <rows/file> <words/file>
set -euo pipefail
cd "$(dirname "$0")/.."
STEP="powershell -NoProfile -ExecutionPolicy Bypass -File GYNIUpper/tools/ub_step.ps1"
t0=$(date +%s)
build() { # $1 = module path below GYNIUpper/ (without .lean), $2 = expected peak working set (MB)
  echo "== GYNIUpper/$1.lean  (start $(date +%H:%M:%S))"
  $STEP -File "GYNIUpper/$1.lean" -Olean ".lake/build/lib/lean/GYNIUpper/$1.olean" -PeakMB "$2"
}
for f in GYNIProof/IntLit GYNIProof/Data GYNIProof/Core GYNIProof/Defs GYNIProof/BlockPSD \
    GYNIUpper/LuedersChoi GYNIUpper/LuedersDilation GYNIUpper/LuedersNormalForm; do
  test -f ".lake/build/lib/lean/$f.olean" || { echo "missing prerequisite $f.olean"; exit 1; }
done
# 1. Mathlib-free core
build UBCheck 1000
# 2. theory (Mathlib)
for f in UBBasic UBScalarTrace UBMoment UBDuality UBPacked UBPSD UBClass UBLevel UBLevelMain \
    UBBridge; do
  build "$f" 3800
done
# 3. levels 2 and 8: data, kernel checks, main theorems
level() { # $1 = L2 or L8, $2 = peak for data files, $3 = peak for check files
  build "$1/Params" 1000
  for f in GYNIUpper/$1/Phi*.lean GYNIUpper/$1/Fac*.lean GYNIUpper/$1/Col*.lean; do
    build "$1/$(basename "$f" .lean)" "$2"
  done
  build "$1/Blocks" 1000
  for f in GYNIUpper/$1/Chk*.lean; do
    build "$1/$(basename "$f" .lean)" "$3"
  done
  build "$1/Main" 3800
}
level L2 1000 1000
level L8 1000 2500
# 4. headline theorems and axioms
build UpperBound 3800
echo "== GYNIUpper/AxiomsUpper.lean  (start $(date +%H:%M:%S))"
$STEP -File "GYNIUpper/AxiomsUpper.lean" -PeakMB 3800
echo "== forbidden keywords (sorry/admit/axiom/native_decide) in GYNIUpper/**/*.lean:"
grep -rnE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' GYNIUpper --include=*.lean || echo "none"
echo "== check_upper.sh done: $(( $(date +%s) - t0 )) s"
