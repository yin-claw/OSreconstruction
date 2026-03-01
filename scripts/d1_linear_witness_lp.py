#!/usr/bin/env python3
"""
LP probe for the d=1 linear witness reduction.

Witness ansatz:
  w_k = (i*T_k, R_k)

For fixed lambda and permutation p, ET/FT step inequalities reduce to:
  DeltaT_p(k) + lambda * DeltaR_p(k) > 0.

This script solves a scaled non-strict version:
  DeltaT_p(k) + lambda * DeltaR_p(k) >= 1
for all required steps, plus FT base constraints:
  T_0 >= 1, T_k - T_{k-1} >= 1.

Usage examples:
  python scripts/d1_linear_witness_lp.py --n 4 --i 0 --sigma 0,2,3,1
  python scripts/d1_linear_witness_lp.py --n 5 --exhaustive
"""

from __future__ import annotations

import argparse
import itertools
from typing import Dict, List, Sequence, Tuple

try:
    from scipy.optimize import linprog
except Exception as ex:  # pragma: no cover
    raise SystemExit(f"scipy is required: {ex}")


def parse_sigma(text: str, n: int) -> Tuple[int, ...]:
    vals = tuple(int(x.strip()) for x in text.split(",") if x.strip() != "")
    if len(vals) != n:
        raise ValueError(f"sigma must have {n} entries, got {len(vals)}")
    if sorted(vals) != list(range(n)):
        raise ValueError("sigma must be a permutation of 0..n-1")
    return vals


def tau_adjacent(n: int, i: int) -> Tuple[int, ...]:
    t = list(range(n))
    t[i], t[i + 1] = t[i + 1], t[i]
    return tuple(t)


def add_geq_ineq(
    A_ub: List[List[float]],
    b_ub: List[float],
    num_vars: int,
    coeffs: Dict[int, float],
    rhs: float,
) -> None:
    # coeffs.x >= rhs  ->  -coeffs.x <= -rhs
    row = [0.0] * num_vars
    for idx, val in coeffs.items():
        row[idx] = val
    A_ub.append([-v for v in row])
    b_ub.append(-rhs)


def feasible_system(
    n: int,
    sigma: Tuple[int, ...],
    i: int,
    lambda_tau: float,
    lambda_sigma: float,
) -> Tuple[bool, Sequence[float] | None]:
    tau = tau_adjacent(n, i)
    num_vars = 2 * n  # [T_0..T_{n-1}, R_0..R_{n-1}]
    A_ub: List[List[float]] = []
    b_ub: List[float] = []

    # FT positivity for identity steps
    add_geq_ineq(A_ub, b_ub, num_vars, {0: 1.0}, 1.0)
    for k in range(1, n):
        add_geq_ineq(A_ub, b_ub, num_vars, {k: 1.0, k - 1: -1.0}, 1.0)

    def add_perm_constraints(p: Tuple[int, ...], lam: float) -> None:
        j0 = p[0]
        add_geq_ineq(A_ub, b_ub, num_vars, {j0: 1.0, n + j0: lam}, 1.0)
        for k in range(1, n):
            j = p[k]
            jm = p[k - 1]
            add_geq_ineq(
                A_ub,
                b_ub,
                num_vars,
                {j: 1.0, jm: -1.0, n + j: lam, n + jm: -lam},
                1.0,
            )

    add_perm_constraints(tau, lambda_tau)
    add_perm_constraints(sigma, lambda_sigma)

    result = linprog(
        c=[0.0] * num_vars,
        A_ub=A_ub,
        b_ub=b_ub,
        bounds=[(None, None)] * num_vars,
        method="highs",
    )
    if not result.success:
        return False, None
    return True, result.x


def lambda_grid() -> List[float]:
    return [-2.0, -1.5, -1.0, -0.75, -0.5, -0.25, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0]


def solve_one(n: int, sigma: Tuple[int, ...], i: int) -> None:
    found = False
    for lt, ls in itertools.product(lambda_grid(), lambda_grid()):
        ok, x = feasible_system(n, sigma, i, lt, ls)
        if not ok:
            continue
        found = True
        t = x[:n]
        r = x[n:]
        print("feasible: yes")
        print(f"lambda_tau={lt}, lambda_sigma={ls}")
        print("T=", [float(v) for v in t])
        print("R=", [float(v) for v in r])
        break
    if not found:
        print("feasible: no (on current lambda grid)")


def solve_exhaustive(n: int) -> None:
    ident = tuple(range(n))
    perms = list(itertools.permutations(range(n)))
    total = 0
    misses = 0
    for i in range(n - 1):
        tau = tau_adjacent(n, i)
        ok_i = 0
        tot_i = 0
        for sigma in perms:
            if sigma == ident or sigma == tau:
                continue
            tot_i += 1
            total += 1
            hit = False
            for lt, ls in itertools.product(lambda_grid(), lambda_grid()):
                ok, _ = feasible_system(n, sigma, i, lt, ls)
                if ok:
                    hit = True
                    break
            if hit:
                ok_i += 1
            else:
                misses += 1
                print(f"MISS i={i} sigma={sigma}")
        print(f"i={i}: {ok_i}/{tot_i}")
    print(f"total={total}, misses={misses}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--i", type=int, default=None)
    parser.add_argument("--sigma", type=str, default=None)
    parser.add_argument("--exhaustive", action="store_true")
    args = parser.parse_args()

    if args.n < 2:
        raise SystemExit("n must be >= 2")

    if args.exhaustive:
        solve_exhaustive(args.n)
        return

    if args.i is None or args.sigma is None:
        raise SystemExit("for non-exhaustive mode, provide --i and --sigma")
    if not (0 <= args.i < args.n - 1):
        raise SystemExit("i must satisfy 0 <= i < n-1")

    sigma = parse_sigma(args.sigma, args.n)
    solve_one(args.n, sigma, args.i)


if __name__ == "__main__":
    main()
