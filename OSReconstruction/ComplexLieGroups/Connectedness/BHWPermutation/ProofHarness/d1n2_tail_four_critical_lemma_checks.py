#!/usr/bin/env python3
"""
Numerical stress tests for the 4 critical deferred d=1,n=2 lemmas in Tail.lean:

1) blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred
2) blocker_d1N2InvariantBridgeAnalyticity_fromSource_deferred
3) blocker_d1N2InvariantBridgePreconnected_fromSource_deferred
4) blocker_d1N2InvariantBridgeCorrection_fromSource_deferred

Important:
- These are heuristic falsification checks, not formal proofs.
- Each test works in finite-dimensional ansatz spaces and finite random samples.
"""

from __future__ import annotations

import argparse
import cmath
import math
import random
from dataclasses import dataclass
from typing import List, Sequence, Tuple

import numpy as np


Complex4 = Tuple[complex, complex, complex, complex]
Real4 = Tuple[float, float, float, float]


def invariants_from_uv(u0: complex, v0: complex, u1: complex, v1: complex) -> Complex4:
    q0 = -(u0 * v0)
    q1 = -(u1 * v1)
    p = -0.5 * (u0 * v1 + u1 * v0)
    s = u0 * v1 - u1 * v0
    return (q0, q1, p, s)


def quadric_residual(inv: Complex4) -> complex:
    q0, q1, p, s = inv
    return s**2 - 4 * (p**2 - q0 * q1)


def in_ft_uv(u0: complex, v0: complex, u1: complex, v1: complex, eps: float = 0.0) -> bool:
    return (
        u0.imag > eps
        and v0.imag > eps
        and (u1 - u0).imag > eps
        and (v1 - v0).imag > eps
    )


def sample_ft_uv(rng: random.Random) -> Complex4:
    b0 = rng.uniform(0.2, 3.0)
    d0 = rng.uniform(0.2, 3.0)
    db = rng.uniform(0.2, 3.0)
    dd = rng.uniform(0.2, 3.0)
    u0 = complex(rng.uniform(-3.0, 3.0), b0)
    v0 = complex(rng.uniform(-3.0, 3.0), d0)
    u1 = u0 + complex(rng.uniform(-3.0, 3.0), db)
    v1 = v0 + complex(rng.uniform(-3.0, 3.0), dd)
    return (u0, v0, u1, v1)


def sample_real_ft_uv(rng: random.Random) -> Complex4:
    # Purely imaginary light-cone coordinates with FT positivity.
    u0_im = rng.uniform(0.2, 3.0)
    v0_im = rng.uniform(0.2, 3.0)
    du_im = rng.uniform(0.2, 3.0)
    dv_im = rng.uniform(0.2, 3.0)
    u0 = complex(0.0, u0_im)
    v0 = complex(0.0, v0_im)
    u1 = complex(0.0, u0_im + du_im)
    v1 = complex(0.0, v0_im + dv_im)
    return (u0, v0, u1, v1)


def sample_phase_locked_real_invariant_ft_uv(rng: random.Random) -> Complex4:
    # Construct z in FT with invariants exactly real by phase-locked light-cone data:
    # u_k = r_k e^{iθ}, v_k = -t_k e^{-iθ} with 0 < θ < π, r1 > r0, t1 > t0.
    theta = rng.uniform(0.12, math.pi - 0.12)
    r0 = rng.uniform(0.25, 3.5)
    r1 = r0 + rng.uniform(0.2, 3.5)
    t0 = rng.uniform(0.25, 3.5)
    t1 = t0 + rng.uniform(0.2, 3.5)
    u0 = r0 * cmath.exp(1j * theta)
    u1 = r1 * cmath.exp(1j * theta)
    v0 = -t0 * cmath.exp(-1j * theta)
    v1 = -t1 * cmath.exp(-1j * theta)
    return (u0, v0, u1, v1)


def swap_then_lorentz_uv(
    u0: complex, v0: complex, u1: complex, v1: complex, lam: complex
) -> Complex4:
    # swap first, then complex boost: (u,v) -> (lam*u, lam^-1*v)
    inv_lam = 1.0 / lam
    y0u, y0v = lam * u1, inv_lam * v1
    y1u, y1v = lam * u0, inv_lam * v0
    return (y0u, y0v, y1u, y1v)


def random_nonzero_complex_scale(rng: random.Random) -> complex:
    r = rng.uniform(0.2, 4.0)
    th = rng.uniform(-math.pi, math.pi)
    return cmath.rect(r, th)


def close_inv(a: Complex4, b: Complex4, tol: float = 1e-7) -> bool:
    return max(abs(a[i] - b[i]) for i in range(4)) <= tol


def sample_forwardizable_invariant(
    rng: random.Random,
    lam_trials: int,
    eps: float,
    real_only: bool = False,
) -> Complex4 | None:
    z = sample_real_ft_uv(rng) if real_only else sample_ft_uv(rng)
    u0, v0, u1, v1 = z
    if not in_ft_uv(u0, v0, u1, v1, eps):
        return None
    inv = invariants_from_uv(u0, v0, u1, v1)
    q0, q1, p, s = inv
    if abs(q0) <= eps or abs(q1) <= eps:
        return None
    if real_only and max(abs(q0.imag), abs(q1.imag), abs(p.imag), abs(s.imag)) > 1e-8:
        return None

    for _ in range(lam_trials):
        lam = random_nonzero_complex_scale(rng)
        y = swap_then_lorentz_uv(u0, v0, u1, v1, lam)
        if not in_ft_uv(*y, eps):
            continue
        inv_y = invariants_from_uv(*y)
        target = (q1, q0, p, -s)
        if close_inv(inv_y, target):
            return inv
    return None


def orig_witness_cond(q0: complex, p: complex, s: complex, v0: complex, eps: float) -> bool:
    if abs(q0) <= eps or abs(v0) <= eps:
        return False
    return (
        (v0.imag > eps)
        and (((-q0) / v0).imag > eps)
        and (((q0 - p - s / 2) / v0).imag > eps)
        and ((((p - s / 2 - q0) * v0 / q0).imag) > eps)
    )


def swap_witness_cond(q1: complex, p: complex, s: complex, w0: complex, eps: float) -> bool:
    if abs(q1) <= eps or abs(w0) <= eps:
        return False
    return (
        (w0.imag > eps)
        and (((-q1) / w0).imag > eps)
        and (((q1 - p + s / 2) / w0).imag > eps)
        and ((((p + s / 2 - q1) * w0 / q1).imag) > eps)
    )


def is_real_spacelike_correction_tuple(inv: Complex4, eps: float) -> bool:
    q0, q1, p, s = inv
    if abs(quadric_residual(inv)) > 1e-8:
        return False
    if max(abs(q0.imag), abs(q1.imag), abs(p.imag), abs(s.imag)) > 1e-8:
        return False
    return (q0.real + q1.real - 2.0 * p.real) > eps


def sample_real_spacelike_invariant_from_z_family(
    rng: random.Random, eps: float
) -> Complex4 | None:
    # Real FT light-cone coordinates directly produce real invariant tuples.
    z = sample_real_ft_uv(rng)
    if not in_ft_uv(*z, eps):
        return None
    inv = invariants_from_uv(*z)
    if is_real_spacelike_correction_tuple(inv, eps):
        return inv
    return None


def sample_real_spacelike_invariant_from_phase_locked_z_family(
    rng: random.Random, eps: float
) -> Complex4 | None:
    # A second explicit z-family with complex phases but exactly real invariants.
    z = sample_phase_locked_real_invariant_ft_uv(rng)
    if not in_ft_uv(*z, eps):
        return None
    inv = invariants_from_uv(*z)
    if is_real_spacelike_correction_tuple(inv, eps):
        return inv
    return None


def direct_real_correction_hit_count_from_z_family(
    rng: random.Random, eps: float, attempts: int
) -> int:
    hits = 0
    for _ in range(attempts):
        if rng.random() < 0.5:
            inv = sample_real_spacelike_invariant_from_z_family(rng, eps)
        else:
            inv = sample_real_spacelike_invariant_from_phase_locked_z_family(rng, eps)
        if inv is not None:
            hits += 1
    return hits


def sample_real_spacelike_invariants(rng: random.Random) -> Complex4:
    while True:
        t0 = rng.uniform(-3.0, 3.0)
        x0 = rng.uniform(-3.0, 3.0)
        dt = rng.uniform(-3.0, 3.0)
        dx = rng.uniform(-3.0, 3.0)
        if dx * dx - dt * dt <= 0.25:
            continue
        t1 = t0 + dt
        x1 = x0 + dx
        u0, v0 = t0 + x0, t0 - x0
        u1, v1 = t1 + x1, t1 - x1
        q0, q1, p, s = invariants_from_uv(complex(u0), complex(v0), complex(u1), complex(v1))
        return (q0, q1, p, s)


def sample_intrinsic_real_quadric_spacelike_invariant(
    rng: random.Random, eps: float
) -> Complex4 | None:
    # Intrinsic sampler in (q0,q1,p,s): does not start from z-coordinates.
    q0 = rng.uniform(-6.0, 6.0)
    q1 = rng.uniform(-6.0, 6.0)
    p = rng.uniform(-6.0, 6.0)
    if q0 + q1 - 2.0 * p <= eps:
        return None
    delta = p * p - q0 * q1
    if delta < -1e-12:
        return None
    s = 2.0 * math.sqrt(max(delta, 0.0))
    if rng.random() < 0.5:
        s = -s
    return (complex(q0), complex(q1), complex(p), complex(s))


def sample_intrinsic_real_quadric_spacelike_near_q0_zero(
    rng: random.Random, eps: float
) -> Complex4 | None:
    # Edge sampler stressing q0≈0 branch in invariant->(u,v) reconstruction.
    q0 = rng.uniform(-1e-7, 1e-7)
    q1 = rng.uniform(-8.0, 8.0)
    p = rng.uniform(-8.0, 8.0)
    if q0 + q1 - 2.0 * p <= eps:
        return None
    delta = p * p - q0 * q1
    if delta < -1e-12:
        return None
    s = 2.0 * math.sqrt(max(delta, 0.0))
    if rng.random() < 0.5:
        s = -s
    return (complex(q0), complex(q1), complex(p), complex(s))


def as_real4_if_close(inv: Complex4, tol: float = 1e-8) -> Real4 | None:
    q0, q1, p, s = inv
    if max(abs(q0.imag), abs(q1.imag), abs(p.imag), abs(s.imag)) > tol:
        return None
    return (q0.real, q1.real, p.real, s.real)


def reconstruct_real_uv_from_invariants(inv: Real4, eps: float) -> Tuple[Real4, str] | None:
    q0, q1, p, s = inv
    a = -p + s / 2.0  # u0 * v1
    b = -p - s / 2.0  # u1 * v0

    # Prefer the numerically safer generic branch: divide by the larger of |q0|,|q1|.
    branch_cut = max(1e-6, math.sqrt(max(eps, 1e-16)))
    q0_good = abs(q0) > branch_cut
    q1_good = abs(q1) > branch_cut
    if q0_good or q1_good:
        if abs(q0) >= abs(q1) and q0_good:
            # Generic branch using q0 = -u0*v0 with u0 fixed.
            u0 = 1.0
            v0 = -q0
            u1 = b / v0
            v1 = a
            return ((u0, v0, u1, v1), "q0_nonzero")
        # Symmetric generic branch using q1 = -u1*v1 with u1 fixed.
        u1 = 1.0
        v1 = -q1
        u0 = a / v1
        v0 = b
        return ((u0, v0, u1, v1), "q1_nonzero")

    # Degenerate corner q0=q1=0. Then quadric implies a*b=0.
    if abs(a) <= eps and abs(b) <= eps:
        return ((0.0, 1.0, 1.0, 0.0), "degenerate_a0_b0")
    if abs(a) <= eps:
        return ((0.0, 1.0, b, 0.0), "degenerate_a0")
    if abs(b) <= eps:
        return ((a, 0.0, 0.0, 1.0), "degenerate_b0")
    return None


@dataclass
class ReconstructionCheckStats:
    checked: int
    failures: int
    max_invariant_error: float
    nonreal_inputs: int
    branch_counts: dict[str, int]


def run_reconstruction_checks(
    samples: Sequence[Complex4], eps: float, err_tol: float
) -> ReconstructionCheckStats:
    checked = 0
    failures = 0
    max_err = 0.0
    nonreal = 0
    branch_counts: dict[str, int] = {}
    for inv in samples:
        r = as_real4_if_close(inv)
        if r is None:
            nonreal += 1
            continue
        checked += 1
        rec = reconstruct_real_uv_from_invariants(r, eps)
        if rec is None:
            failures += 1
            continue
        (u0, v0, u1, v1), branch = rec
        branch_counts[branch] = branch_counts.get(branch, 0) + 1
        inv_rec = invariants_from_uv(complex(u0), complex(v0), complex(u1), complex(v1))
        err = max(abs(inv_rec[i] - inv[i]) for i in range(4))
        max_err = max(max_err, err)
        if err > err_tol:
            failures += 1
    return ReconstructionCheckStats(
        checked=checked,
        failures=failures,
        max_invariant_error=max_err,
        nonreal_inputs=nonreal,
        branch_counts=branch_counts,
    )


def collect_samples(
    sampler,
    n: int,
    max_attempts: int,
) -> List[Complex4]:
    out: List[Complex4] = []
    attempts = 0
    while len(out) < n and attempts < max_attempts:
        attempts += 1
        item = sampler()
        if item is not None:
            out.append(item)
    return out


def monomial_exponents(max_degree: int) -> List[Tuple[int, int, int, int]]:
    out: List[Tuple[int, int, int, int]] = []
    for a in range(max_degree + 1):
        for b in range(max_degree + 1 - a):
            for c in range(max_degree + 1 - a - b):
                for d in range(max_degree + 1 - a - b - c):
                    out.append((a, b, c, d))
    return out


@dataclass
class AntiBasisTerm:
    exp: Tuple[int, int, int, int]

    def eval(self, q0: complex, q1: complex, p: complex, s: complex) -> complex:
        a, b, c, d = self.exp
        lhs = (q0**a) * (q1**b) * (p**c) * (s**d)
        rhs = (q1**a) * (q0**b) * (p**c) * ((-s) ** d)
        return lhs - rhs


def build_antisym_basis(max_degree: int) -> List[AntiBasisTerm]:
    basis: List[AntiBasisTerm] = []
    probe = (
        complex(1.1, 0.2),
        complex(-0.7, 0.6),
        complex(0.4, -0.8),
        complex(0.9, 0.5),
    )
    for exp in monomial_exponents(max_degree):
        term = AntiBasisTerm(exp)
        if abs(term.eval(*probe)) > 1e-12:
            basis.append(term)
    return basis


def build_constraint_matrix(
    basis: Sequence[AntiBasisTerm], samples: Sequence[Complex4]
) -> np.ndarray:
    mat = np.zeros((len(samples), len(basis)), dtype=np.complex128)
    for i, (q0, q1, p, s) in enumerate(samples):
        for j, term in enumerate(basis):
            mat[i, j] = term.eval(q0, q1, p, s)
    return mat


def nullspace_svd(mat: np.ndarray, tol: float) -> np.ndarray:
    if mat.shape[0] == 0:
        # No constraints: full space is the nullspace.
        return np.eye(mat.shape[1], dtype=np.complex128)
    _u, sing, vh = np.linalg.svd(mat, full_matrices=True)
    rank = int(np.sum(sing > tol))
    return vh[rank:].conj().T


def evaluate_g(coeff: np.ndarray, basis: Sequence[AntiBasisTerm], inv: Complex4) -> complex:
    q0, q1, p, s = inv
    vals = np.array([term.eval(q0, q1, p, s) for term in basis], dtype=np.complex128)
    return complex(np.dot(vals, coeff))


def candidate_coeffs(
    ns: np.ndarray,
    rng_np: np.random.Generator,
    random_combos: int,
) -> List[np.ndarray]:
    out: List[np.ndarray] = []
    if ns.shape[1] == 0:
        return out
    for j in range(min(3, ns.shape[1])):
        c = ns[:, j]
        nrm = np.linalg.norm(c)
        if nrm > 0:
            out.append(c / nrm)
    for _ in range(random_combos):
        combo = rng_np.normal(size=ns.shape[1]) + 1j * rng_np.normal(size=ns.shape[1])
        c = ns @ combo
        nrm = np.linalg.norm(c)
        if nrm > 0:
            out.append(c / nrm)
    return out


def worst_value_over_samples(
    coeffs: Sequence[np.ndarray],
    basis: Sequence[AntiBasisTerm],
    samples: Sequence[Complex4],
) -> float:
    worst = 0.0
    for c in coeffs:
        for inv in samples:
            worst = max(worst, abs(evaluate_g(c, basis, inv)))
    return worst


def wirtinger_dbar_residual(
    coeff: np.ndarray,
    basis: Sequence[AntiBasisTerm],
    inv: Complex4,
    var_idx: int,
    h: float,
) -> float:
    arr = [inv[0], inv[1], inv[2], inv[3]]

    def eval_at(z: complex) -> complex:
        old = arr[var_idx]
        arr[var_idx] = z
        val = evaluate_g(coeff, basis, (arr[0], arr[1], arr[2], arr[3]))
        arr[var_idx] = old
        return val

    z0 = arr[var_idx]
    fxp = eval_at(z0 + h)
    fxm = eval_at(z0 - h)
    fyp = eval_at(z0 + 1j * h)
    fym = eval_at(z0 - 1j * h)
    dfdx = (fxp - fxm) / (2.0 * h)
    dfdy = (fyp - fym) / (2.0 * h)
    dbar = 0.5 * (dfdx + 1j * dfdy)
    return abs(dbar)


class UnionFind:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a: int, b: int) -> None:
        ra = self.find(a)
        rb = self.find(b)
        if ra == rb:
            return
        if self.size[ra] < self.size[rb]:
            ra, rb = rb, ra
        self.parent[rb] = ra
        self.size[ra] += self.size[rb]

    def component_sizes(self) -> List[int]:
        roots = {}
        for i in range(len(self.parent)):
            r = self.find(i)
            roots[r] = roots.get(r, 0) + 1
        return sorted(roots.values(), reverse=True)


def connectivity_graph_components(samples: Sequence[Complex4], knn_k: int) -> Tuple[int, List[int]]:
    n = len(samples)
    if n == 0:
        return (0, [])
    pts = np.zeros((n, 8), dtype=np.float64)
    for i, (q0, q1, p, s) in enumerate(samples):
        pts[i, :] = [
            q0.real, q0.imag, q1.real, q1.imag, p.real, p.imag, s.real, s.imag
        ]
    # Pairwise distances
    dif = pts[:, None, :] - pts[None, :, :]
    dist = np.linalg.norm(dif, axis=2)
    uf = UnionFind(n)
    k = max(1, min(knn_k, n - 1))
    for i in range(n):
        nbrs = np.argsort(dist[i])[1 : k + 1]
        for j in nbrs:
            uf.union(i, int(j))
    sizes = uf.component_sizes()
    return (len(sizes), sizes)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=20260304)
    parser.add_argument("--degree", type=int, default=6)
    parser.add_argument("--svd-tol", type=float, default=1e-10)
    parser.add_argument("--eps", type=float, default=1e-10)
    parser.add_argument("--lam-trials", type=int, default=140)
    parser.add_argument("--source-real-spacelike-samples", type=int, default=2500)
    parser.add_argument("--source-real-spacelike-z-samples", type=int, default=1500)
    parser.add_argument("--real-correction-samples", type=int, default=1400)
    parser.add_argument("--complex-domain-samples", type=int, default=1800)
    parser.add_argument("--random-null-combos", type=int, default=20)
    parser.add_argument("--knn-k", type=int, default=10)
    parser.add_argument("--fd-step", type=float, default=1e-6)
    parser.add_argument("--fd-samples", type=int, default=180)
    parser.add_argument("--direct-real-correction-z-search-trials", type=int, default=30000)
    parser.add_argument("--report-threshold", type=float, default=1e-6)
    parser.add_argument("--boundary-intrinsic-samples", type=int, default=30000)
    parser.add_argument("--boundary-z-constructed-samples", type=int, default=30000)
    parser.add_argument("--boundary-near-q0-zero-samples", type=int, default=12000)
    parser.add_argument("--boundary-reconstruct-tol", type=float, default=1e-7)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    rng_np = np.random.default_rng(args.seed)

    basis = build_antisym_basis(args.degree)
    print("=== Setup ===")
    print(f"seed={args.seed}")
    print(f"degree={args.degree}")
    print(f"antisym_basis_size={len(basis)}")

    # Local-comm source constraints: sampled real spacelike tuples.
    source_real_spacelike_intrinsic = [
        sample_real_spacelike_invariants(rng) for _ in range(args.source_real_spacelike_samples)
    ]
    source_real_spacelike_from_z = collect_samples(
        lambda: sample_real_spacelike_invariant_from_phase_locked_z_family(rng, args.eps),
        n=args.source_real_spacelike_z_samples,
        max_attempts=30 * args.source_real_spacelike_z_samples,
    )
    source_real_spacelike = source_real_spacelike_intrinsic + source_real_spacelike_from_z
    amat_source = build_constraint_matrix(basis, source_real_spacelike)
    ns_source = nullspace_svd(amat_source, tol=args.svd_tol)
    coeffs_source = candidate_coeffs(ns_source, rng_np, args.random_null_combos)

    print("\n=== Source Constraint Ansatz Space ===")
    print(f"source_real_spacelike_intrinsic_samples={len(source_real_spacelike_intrinsic)}")
    print(f"source_real_spacelike_from_z_samples={len(source_real_spacelike_from_z)}")
    print(f"source_real_spacelike_total_samples={len(source_real_spacelike)}")
    print(f"source_constraint_nullspace_dim={ns_source.shape[1]}")

    # Real correction-anchor tuples: quadric + real slice + spacelike inequality.
    real_correction_from_real_ft_z = collect_samples(
        lambda: sample_real_spacelike_invariant_from_z_family(rng, args.eps),
        n=args.real_correction_samples,
        max_attempts=20 * args.real_correction_samples,
    )
    real_correction_from_phase_locked_z = collect_samples(
        lambda: sample_real_spacelike_invariant_from_phase_locked_z_family(rng, args.eps),
        n=args.real_correction_samples,
        max_attempts=30 * args.real_correction_samples,
    )
    real_correction_intrinsic = [
        sample_real_spacelike_invariants(rng) for _ in range(args.real_correction_samples)
    ]
    real_correction = (
        real_correction_from_real_ft_z
        + real_correction_from_phase_locked_z
        + real_correction_intrinsic
    )

    # Complex witnessed tuples in D.
    complex_domain = collect_samples(
        lambda: sample_forwardizable_invariant(
            rng, args.lam_trials, args.eps, real_only=False
        ),
        n=args.complex_domain_samples,
        max_attempts=60 * args.complex_domain_samples,
    )

    print("\n=== Sampled Domains ===")
    print(f"real_correction_from_real_ft_z_samples={len(real_correction_from_real_ft_z)}")
    print(f"real_correction_from_phase_locked_z_samples={len(real_correction_from_phase_locked_z)}")
    print(f"real_correction_intrinsic_samples={len(real_correction_intrinsic)}")
    print(f"real_correction_total_samples={len(real_correction)}")
    print(f"complex_domain_samples_collected={len(complex_domain)}")
    print(
        "complex_domain_construction="
        + "z_in_FT + explicit swap_then_lorentz(z,lam) witness in FT"
    )
    print(
        "direct_real_correction_hits_from_z_family="
        + f"{direct_real_correction_hit_count_from_z_family(rng, args.eps, args.direct_real_correction_z_search_trials)}"
        + f"/{args.direct_real_correction_z_search_trials}"
    )
    if not real_correction:
        print(
            "warning=NO_REAL_CORRECTION_SAMPLES_FOUND "
            "(quadric+real-slice+spacelike samples not found; check sampler settings)"
        )
    if complex_domain:
        max_quadric = max(abs(quadric_residual(inv)) for inv in complex_domain)
        print(f"max_quadric_residual_complex_domain={max_quadric:.3e}")

    # Test 4: BridgeCorrection_fromSource (heuristic falsification).
    # If source-constrained antisymmetric ansatz can be nonzero on correction-anchor points,
    # that's evidence against the bridge-correction claim in this ansatz.
    worst_corr = worst_value_over_samples(coeffs_source, basis, real_correction)
    print("\n=== Test 4: BridgeCorrection_fromSource (Heuristic) ===")
    print(f"worst_|g|_on_real_correction_domain={worst_corr:.6e}")
    print(f"report_threshold={args.report_threshold:.1e}")
    if not real_correction:
        print("status=INCONCLUSIVE_NO_REAL_CORRECTION_SAMPLES")
    else:
        print(
            "status="
            + (
                "NO_NUMERIC_FALSIFIER_FOUND"
                if worst_corr <= args.report_threshold
                else "POTENTIAL_FALSIFIER_FOUND"
            )
        )

    # Test 1: Core theorem (analyticity+connectedness+correction -> g=0 on D),
    # using correction-sampled constraints (real quadric/slice/spacelike tuples).
    amat_corr = build_constraint_matrix(basis, real_correction)
    ns_corr = nullspace_svd(amat_corr, tol=args.svd_tol)
    coeffs_corr = candidate_coeffs(ns_corr, rng_np, args.random_null_combos)
    worst_core = worst_value_over_samples(coeffs_corr, basis, complex_domain)
    print("\n=== Test 1: Invariant Core Theorem (Heuristic) ===")
    print(f"correction_constraint_nullspace_dim={ns_corr.shape[1]}")
    print(f"worst_|g|_on_complex_witnessed_domain={worst_core:.6e}")
    print(f"report_threshold={args.report_threshold:.1e}")
    if not real_correction:
        print("status=INCONCLUSIVE_EMPTY_CORRECTION_ANCHOR_SET")
        print("note=CORE_TEST_USED_EMPTY_CORRECTION_CONSTRAINT_SET")
    else:
        print(
            "status="
            + (
                "NO_NUMERIC_FALSIFIER_FOUND"
                if worst_core <= args.report_threshold
                else "POTENTIAL_FALSIFIER_FOUND"
            )
        )

    # Test 2: BridgeAnalyticity_fromSource (pointwise differentiability surrogate).
    # Evaluate anti-holomorphic finite-difference residual on sampled complex witnessed points.
    fd_points = complex_domain[: min(len(complex_domain), args.fd_samples)]
    worst_dbar = 0.0
    for coeff in coeffs_source:
        for inv in fd_points:
            for var_idx in range(4):
                worst_dbar = max(
                    worst_dbar,
                    wirtinger_dbar_residual(coeff, basis, inv, var_idx, args.fd_step),
                )
    print("\n=== Test 2: BridgeAnalyticity_fromSource (Numerical Surrogate) ===")
    print(f"fd_points_used={len(fd_points)}")
    print(f"fd_step={args.fd_step:.1e}")
    print(f"max_wirtinger_dbar_residual={worst_dbar:.6e}")
    if not coeffs_source:
        print("note=NO_NONZERO_SOURCE_CONSTRAINED_ANTISYMMETRIC_MODE_IN_ANSATZ")

    # Test 3: BridgePreconnected_fromSource (connectivity surrogate).
    components, sizes = connectivity_graph_components(complex_domain, args.knn_k)
    largest = sizes[0] if sizes else 0
    frac = (largest / len(complex_domain)) if complex_domain else 0.0
    print("\n=== Test 3: BridgePreconnected_fromSource (Graph Surrogate) ===")
    print(f"knn_k={args.knn_k}")
    print(f"graph_components={components}")
    print(f"largest_component_size={largest}")
    print(f"largest_component_fraction={frac:.6f}")
    print("component_sizes_top10=" + str(sizes[:10]))

    # Test 5: ForwardWitnessEq_field_deferred (source-to-forwardizable surrogate).
    # This uses only source-side sampled constraints, then probes complex
    # forwardizable tuples.
    worst_forward = worst_value_over_samples(coeffs_source, basis, complex_domain)
    print("\n=== Test 5: ForwardWitnessEq_field_deferred (Heuristic) ===")
    print(f"worst_|g|_on_complex_forwardizable_domain_from_source_constraints={worst_forward:.6e}")
    print(f"report_threshold={args.report_threshold:.1e}")
    print(
        "status="
        + (
            "NO_NUMERIC_FALSIFIER_FOUND"
            if worst_forward <= args.report_threshold
            else "POTENTIAL_FALSIFIER_FOUND"
        )
    )

    # Test 6: BoundaryIdentification geometry core (real tuple -> real witness config).
    # This checks the geometric existence content numerically:
    # for real quadric+spacelike tuples, reconstruct real light-cone coordinates
    # (u0,v0,u1,v1) and verify invariants close back to the input.
    boundary_intrinsic = collect_samples(
        lambda: sample_intrinsic_real_quadric_spacelike_invariant(rng, args.eps),
        n=args.boundary_intrinsic_samples,
        max_attempts=80 * args.boundary_intrinsic_samples,
    )
    boundary_near_q0 = collect_samples(
        lambda: sample_intrinsic_real_quadric_spacelike_near_q0_zero(rng, args.eps),
        n=args.boundary_near_q0_zero_samples,
        max_attempts=120 * args.boundary_near_q0_zero_samples,
    )
    boundary_from_z = collect_samples(
        lambda: sample_real_spacelike_invariant_from_phase_locked_z_family(rng, args.eps),
        n=args.boundary_z_constructed_samples,
        max_attempts=80 * args.boundary_z_constructed_samples,
    )
    stats_intrinsic = run_reconstruction_checks(
        boundary_intrinsic, args.eps, args.boundary_reconstruct_tol
    )
    stats_near_q0 = run_reconstruction_checks(
        boundary_near_q0, args.eps, args.boundary_reconstruct_tol
    )
    stats_from_z = run_reconstruction_checks(
        boundary_from_z, args.eps, args.boundary_reconstruct_tol
    )
    total_checked = (
        stats_intrinsic.checked + stats_near_q0.checked + stats_from_z.checked
    )
    total_failures = (
        stats_intrinsic.failures + stats_near_q0.failures + stats_from_z.failures
    )
    overall_max_err = max(
        stats_intrinsic.max_invariant_error,
        stats_near_q0.max_invariant_error,
        stats_from_z.max_invariant_error,
    )
    aggregate_branches: dict[str, int] = {}
    for d in [stats_intrinsic.branch_counts, stats_near_q0.branch_counts, stats_from_z.branch_counts]:
        for k, v in d.items():
            aggregate_branches[k] = aggregate_branches.get(k, 0) + v
    print("\n=== Test 6: BoundaryIdentification Geometry (Reconstruction) ===")
    print(f"boundary_intrinsic_samples_collected={len(boundary_intrinsic)}")
    print(f"boundary_near_q0_samples_collected={len(boundary_near_q0)}")
    print(f"boundary_from_z_samples_collected={len(boundary_from_z)}")
    print(f"boundary_reconstruction_checked={total_checked}")
    print(f"boundary_reconstruction_failures={total_failures}")
    print(f"boundary_max_invariant_reconstruction_error={overall_max_err:.6e}")
    print(f"boundary_reconstruct_tol={args.boundary_reconstruct_tol:.1e}")
    print(
        "boundary_nonreal_inputs_skipped="
        + str(stats_intrinsic.nonreal_inputs + stats_near_q0.nonreal_inputs + stats_from_z.nonreal_inputs)
    )
    print("boundary_reconstruction_branch_counts=" + str(aggregate_branches))
    print(
        "status="
        + (
            "NO_NUMERIC_FALSIFIER_FOUND"
            if (total_checked > 0 and total_failures == 0 and overall_max_err <= args.boundary_reconstruct_tol)
            else "POTENTIAL_FALSIFIER_FOUND"
        )
    )


if __name__ == "__main__":
    main()
