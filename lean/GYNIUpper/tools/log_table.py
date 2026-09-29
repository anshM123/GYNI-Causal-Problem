"""Markdown table (file, wall time, peak working set, peak private bytes) from a check_upper.sh log.

usage: python GYNIUpper/tools/log_table.py GYNIUpper/logs_upper/check_upper.log"""
import re
import sys

PAT = re.compile(r"RESULT (\S+): exit=(\d+) wall=([\d.,]+)s peakWS=([\d,]+)MB peakPrivate=([\d,]+)MB \(attempt (\d)\)")


def main(path):
    rows = []
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            m = PAT.search(line)
            if m:
                name, code, wall, ws, priv, att = m.groups()
                rows.append((name.replace("\\", "/"), int(code), float(wall.replace(",", "")),
                             int(ws.replace(",", "")), int(priv.replace(",", "")), int(att)))
    print("| file | exit | wall (s) | peak working set (MB) | peak private (MB) |")
    print("|---|---|---|---|---|")
    tot = 0.0
    for name, code, wall, ws, priv, att in rows:
        tot += wall
        print(f"| `{name}` | {code} | {wall:.1f} | {ws:,} | {priv:,} |")
    print(f"\n{len(rows)} files, total wall time of the Lean processes {tot:.0f} s ({tot/60:.1f} min); "
          f"max peak working set {max(r[3] for r in rows):,} MB.")


if __name__ == "__main__":
    main(sys.argv[1])
