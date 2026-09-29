"""Summarize GYNIProof check logs: one row per Lean process (wall time, peak working set, peak
private bytes), grouped totals, and the maxima.  Usage:
    python GYNIProof/tools/log_table.py GYNIProof/logs/check_conditional.log [GYNIProof/logs/check_big.log]
"""
import re
import sys
from collections import OrderedDict

PAT = re.compile(r"RESULT GYNIProof/(\S+)\.lean: exit=(\d+) wall=([\d.,]+)s peakWS=([\d,]+)MB "
                 r"peakPrivate=([\d,]+)MB(?: \(attempt (\d)\))?")


def group(name):
    for pre, g in [("Big/D_", "Big/D_* (48 data files)"), ("Big/P_", "Big/P_* (3)"),
                   ("CertBigRows_", "CertBigRows_* (48)"), ("CertBigShape_", "CertBigShape_* (3)"),
                   ("CertBig_", "CertBig_* (3, Mathlib)"), ("CertSmall", "CertSmall0..7"),
                   ("CertMid", "CertMid0..15")]:
        if name.startswith(pre):
            return g
    return name


def main(paths):
    rows = []
    for p in paths:
        with open(p, encoding="utf-8", errors="replace") as f:
            for line in f:
                m = PAT.search(line)
                if m:
                    name, code, wall, ws, priv, att = m.groups()
                    rows.append((name, int(code), float(wall.replace(",", "")), int(ws.replace(",", "")),
                                 int(priv.replace(",", "")), int(att or 1)))
    groups = OrderedDict()
    for r in rows:
        g = groups.setdefault(group(r[0]), [0, 0.0, 0, 0, 0])
        g[0] += 1
        g[1] += r[2]
        g[2] = max(g[2], r[3])
        g[3] = max(g[3], r[4])
        g[4] += (r[1] != 0)
    print("| file(s) | processes | total wall (s) | max peak WS (MB) | max peak private (MB) | failures |")
    print("|---|---|---|---|---|---|")
    for g, (n, wall, ws, priv, fails) in groups.items():
        print(f"| `{g}` | {n} | {wall:.0f} | {ws} | {priv} | {fails} |")
    tot = sum(r[2] for r in rows)
    print(f"\nTotal Lean wall time: {tot:.0f} s ({tot/60:.1f} min) over {len(rows)} processes; "
          f"max peak WS {max(r[3] for r in rows)} MB, max peak private {max(r[4] for r in rows)} MB; "
          f"non-zero exits: {sum(r[1] != 0 for r in rows)}; retries: {sum(r[5] > 1 for r in rows)}.")


if __name__ == "__main__":
    main(sys.argv[1:])
