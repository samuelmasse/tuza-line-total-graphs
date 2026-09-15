"""Check the paper's finite-base recipe against the exact Lean witness lists."""

from __future__ import annotations

import json
import re
from itertools import combinations
from pathlib import Path
from typing import TypedDict

Triangle = frozenset[int]


class CertificateCheck(TypedDict):
    order: int
    triangles: int
    cover_cost: int
    required_slack: int
    pair_checks: int


def paper_witness(n: int) -> list[Triangle]:
    if n <= 2:
        return []
    r = n // 2
    triangles = [frozenset((i, j, r + (i + j) % r)) for i in range(r) for j in range(i + 1, r)]
    if n % 2 == 0 and n >= 6:
        triangles.append(frozenset((r, r + 1, r + 2)))
    elif n % 2 == 1:
        count = r if r % 2 == 1 else r // 2
        triangles.extend(frozenset((2 * r, i, r + 2 * i % r)) for i in range(count))
    return triangles


def check() -> list[CertificateCheck]:
    root = Path(__file__).resolve().parents[1]
    source = (root / "Tuza" / "CliqueFiniteCertificates.lean").read_text(encoding="utf-8")
    pattern = r"private def cliqueBase(\d+) : List \(Finset \(Fin \d+\)\) := (\[[^\n]*\])"
    matches = re.findall(pattern, source)
    if [int(n) for n, _ in matches] != list(range(21)):
        raise ValueError("Expected exactly the Lean base declarations 0 through 20")
    manuscript = (root / "paper" / "main.tex").read_text(encoding="utf-8")
    expected_sizes = [
        int(value)
        for row in re.findall(r"p_n&([0-9&]+)\.?\s*\n", manuscript)
        for value in row.split("&")
    ]
    if len(expected_sizes) != 21:
        raise ValueError("Expected 21 certificate counts in the paper's tables")
    report: list[CertificateCheck] = []
    for n_text, body in matches:
        n = int(n_text)
        literal = [
            frozenset(int(v.strip()) for v in triple.split(","))
            for triple in re.findall(r"\{([^}]+)\}", body)
        ]
        proposed = paper_witness(n)
        if literal != proposed:
            raise ValueError(f"Paper recipe differs from Lean's exact list at {n}")
        if len(proposed) != expected_sizes[n]:
            raise ValueError(f"Paper table differs from list length at {n}")
        for triangle in proposed:
            if len(triangle) != 3 or not triangle <= frozenset(range(n)):
                raise ValueError(f"Invalid triangle at order {n}: {triangle}")
        pair_checks = 0
        for first, second in combinations(proposed, 2):
            pair_checks += 1
            if len(first & second) > 1:
                raise ValueError(f"Packing conflict at order {n}")
        cost = n * (n - 1) // 2 - n * n // 4
        slack = 2 if n >= 6 and n % 2 == 0 else 0
        if cost + slack > 2 * len(proposed):
            raise ValueError(f"Insufficient packing size at order {n}")
        report.append(
            {
                "order": n,
                "triangles": len(proposed),
                "cover_cost": cost,
                "required_slack": slack,
                "pair_checks": pair_checks,
            }
        )
    return report


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
