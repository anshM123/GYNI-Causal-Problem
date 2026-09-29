#!/usr/bin/env bash
# Compile one GYNIUpper module with the RAM-aware wrapper: ub_one.sh <Module path below formal-conjectures, no .lean> <peakMB>
# Example: bash GYNIUpper/tools/ub_one.sh GYNIUpper/UBBasic 3600
set -uo pipefail
cd "$(dirname "$0")/../.."
M="$1"; PK="${2:-3600}"
powershell -NoProfile -ExecutionPolicy Bypass -File GYNIUpper/tools/ub_step.ps1 -File "$M.lean" -Olean ".lake/build/lib/lean/$M.olean" -PeakMB "$PK"
