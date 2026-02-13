#!/usr/bin/env python3
"""Summarize JaCoCo CSV report by package.

Usage:
    python tools/coverage-summary.py [path/to/jacocoTestReport.csv]

Defaults to macro-core's report if no argument given.
"""

import csv
import sys
from collections import defaultdict
from pathlib import Path


def pct(covered: int, missed: int) -> str:
    total = covered + missed
    if total == 0:
        return "  n/a"
    return f"{covered * 100 / total:5.1f}%"


def main():
    if len(sys.argv) > 1:
        csv_path = Path(sys.argv[1])
    else:
        csv_path = Path(__file__).resolve().parent.parent / "macro-core" / "build" / "reports" / "jacoco" / "test" / "jacocoTestReport.csv"

    if not csv_path.exists():
        print(f"Not found: {csv_path}", file=sys.stderr)
        print("Run './gradlew :macro-core:test :macro-core:jacocoTestReport' first.", file=sys.stderr)
        sys.exit(1)

    # instruction_missed, instruction_covered, branch_missed, branch_covered, line_missed, line_covered
    by_pkg: dict[str, list[int]] = defaultdict(lambda: [0, 0, 0, 0, 0, 0])

    with open(csv_path, newline="") as f:
        for row in csv.DictReader(f):
            s = by_pkg[row["PACKAGE"]]
            s[0] += int(row["INSTRUCTION_MISSED"])
            s[1] += int(row["INSTRUCTION_COVERED"])
            s[2] += int(row["BRANCH_MISSED"])
            s[3] += int(row["BRANCH_COVERED"])
            s[4] += int(row["LINE_MISSED"])
            s[5] += int(row["LINE_COVERED"])

    grand = [0, 0, 0, 0, 0, 0]

    print(f"{'Package':<50} {'Instr%':>7} {'Branch%':>8} {'Line%':>7}")
    print("-" * 80)

    for pkg in sorted(by_pkg):
        s = by_pkg[pkg]
        for i in range(6):
            grand[i] += s[i]
        print(f"{pkg:<50} {pct(s[1], s[0]):>7} {pct(s[3], s[2]):>8} {pct(s[5], s[4]):>7}")

    print("-" * 80)
    print(f"{'TOTAL':<50} {pct(grand[1], grand[0]):>7} {pct(grand[3], grand[2]):>8} {pct(grand[5], grand[4]):>7}")


if __name__ == "__main__":
    main()
