#!/usr/bin/env bash
# GYNIProof, the three 256 x 256 blocks and the unconditional main theorems.
# Requires a successful `bash GYNIProof/check.sh` first (uses its .olean files).
#
#   bash GYNIProof/check_big.sh 2>&1 | tee GYNIProof/logs/check_big.log
#
# Same RAM rules as check.sh (tools/lean_step.ps1: no other lean.exe, Available >= expected peak
# working set + 1.5 GB). Per block `b` (Mathlib-free unless noted): 16 data files Big/D_b_q (16 rows
# of L and E each, and their packed columns), the packed columns Big/P_b, the parameter/bound/length
# checks CertBigShape_b, 16 chunk column checks CertBigCols_b_q, their combination CertBigComb_b,
# 16 row checks CertBigRows_b_q, and the Mathlib assembly CertBig_b (`cert_b : BlockPSD ..`).
# Then Main.lean (unconditional theorems) and AxiomsMain.lean.
set -euo pipefail
cd "$(dirname "$0")/.."
STEP="powershell -NoProfile -ExecutionPolicy Bypass -File GYNIProof/tools/lean_step.ps1"
t0=$(date +%s)
build() {
  echo "== GYNIProof/$1.lean  (start $(date +%H:%M:%S))"
  $STEP -File "GYNIProof/$1.lean" -Olean ".lake/build/lib/lean/GYNIProof/$1.olean" -PeakMB "$2"
}
for b in 0_0 0_13 13_13; do
  for q in $(seq 0 15); do build "Big/D_${b}_${q}" 800; done
  build "Big/P_${b}" 800
  build "CertBigShape_${b}" 1500
  for q in $(seq 0 15); do build "CertBigCols_${b}_${q}" 1500; done
  build "CertBigComb_${b}" 1500
  for q in $(seq 0 15); do build "CertBigRows_${b}_${q}" 1500; done
  build "CertBig_${b}" 3500
done
build Main 3500
echo "== GYNIProof/AxiomsMain.lean  (start $(date +%H:%M:%S))"
$STEP -File "GYNIProof/AxiomsMain.lean" -PeakMB 3500
echo "== forbidden keywords (sorry/admit/axiom/native_decide) in GYNIProof/**/*.lean:"
grep -rnE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' GYNIProof --include=*.lean || echo "none"
echo "== check_big.sh done: $(( $(date +%s) - t0 )) s"
