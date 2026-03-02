# d=1,n=2 Lorentz-Invariant Route

Last updated: 2026-03-02

## Purpose

This note documents the dedicated `d=1,n=2` invariant infrastructure added in:

- `D1N2LorentzInvariantRoute.lean`

The goal is to isolate the blocker proof into a clean model statement:

1. Build `(Q₀,Q₁,P,S)` invariants.
2. Prove their Lorentz behavior and swap behavior.
3. Reduce the adjacent-swap forward equality to a single model hypothesis on `F`.

## Core definitions now available

- `D1N2Config := Fin 2 → Fin (1 + 1) → ℂ`
- `d1MinkowskiBilinC : D1Vec → D1Vec → ℂ`
- `d1Q0 d1Q1 d1P01 d1S01 : D1N2Config → ℂ`
- light-cone coordinates/invariants:
  - `d1U0 d1V0 d1U1 d1V1`
  - `d1R01 d1T01`
- `d1InvariantTriple : D1N2Config → ℂ × ℂ × ℂ`
- `d1InvariantQuad : D1N2Config → ℂ × ℂ × ℂ × ℂ`

## Proven geometric/algebraic facts

1. Bilinear invariance:
   - `d1MinkowskiBilinC_lorentzVecAct`
2. Invariant coordinates are Lorentz-invariant:
   - `d1Q0_lorentzAction`
   - `d1Q1_lorentzAction`
   - `d1P01_lorentzAction`
   - `d1S01_lorentzAction`
   - `d1InvariantTriple_lorentzAction`
   - `d1InvariantQuad_lorentzAction`
3. Swap action on invariant coordinates:
   - `d1Q0_swap01` and `d1Q1_swap01` (exchange)
   - `d1P01_swap01` (fixed)
   - `d1S01_swap01` (sign flip)
   - `d1InvariantTriple_swap01`
   - `d1InvariantQuad_swap01` with
     `(Q₀,Q₁,P,S) ↦ (Q₁,Q₀,P,-S)`
4. Real spacelike expression as `Q₀+Q₁-2P`:
   - `d1_adj_spacelike_expr_eq_q0q1p`
   - `d1_n2_local_comm_of_invariant_ineq`
5. Invariant-quadric relation:
   - `d1_invariant_quadric_relation` proving
     `S^2 = 4 (P^2 - Q0*Q1)`
6. Light-cone algebra relations:
   - `d1Q0_eq_neg_U0_mul_V0`, `d1Q1_eq_neg_U1_mul_V1`
   - `d1_two_mul_P01_eq_neg_R01_add_T01`
   - `d1S01_eq_R01_sub_T01`
   - `d1_R01_mul_T01_eq_Q0_mul_Q1`
   - `d1R01_swap01`, `d1T01_swap01`
7. FT realization bridge:
   - `exists_forward_with_swappedInvariantQuad_of_forwardizedSwap`
     (if `Γ·(swap·w) ∈ FT`, the swapped-sign invariants of `w` are realized by an `FT` point)
8. Explicit scalar-boost orbit classification on `FT`:
   - `d1ScalarBoostMatrix`, `d1ScalarBoost`
   - `d1UAt_scalarBoost`, `d1VAt_scalarBoost`
   - `d1_exists_lorentz_of_sameInvariantQuad_on_FT`
     (equal signed quadruples on `FT_{1,2}` imply same complex-Lorentz orbit)

## Reduction theorem now available

- `d1_n2_forward_swap_eq_of_invariantModel`
- `d1_n2_invariantKernelSwapRule_of_forwardSwapEq`
- `d1_n2_forwardSwapEq_iff_invariantKernelSwapRule`
- `d1_n2_forward_swap_eq_of_invariantModel_fun`
- `d1_n2_extendF_swap_eq_on_adjSwapExtendedOverlap_of_invariantModel`

These theorems prove:

- If `F` factors on `FT` through a kernel `f(Q₀,Q₁,P,S)`,
- and `f` satisfies the swap relation for `FT` points `z` that admit a
  forwardizing witness `Γ` with `Γ·(swap·z) ∈ FT`,
- then the full adjacent-swap forward equality follows for every complex Lorentz witness `Γ`.

So the remaining burden in this route is not the algebraic Lorentz/swap layer; it is to construct:

- `d1N2InvariantModel F`

from the existing analytic assumptions (`hF_holo`, `hF_lorentz`, `hF_bv`, `hF_local`)
plus the invariant-function identity-theorem argument on the invariant variety.

This is represented in blockers by:

- `blocker_d1N2InvariantModel_core_deferred`
- `blocker_d1N2ForwardSwapEq_on_FT_deferred`
- `blocker_d1N2SameInvariantQuad_on_FT_implies_eq_deferred`
- `blocker_d1N2InvariantFactorization_on_FT_deferred`
- `blocker_d1N2InvariantKernelSwapRule_deferred`
- (proved wrapper) `blocker_d1N2InvariantModel_of_wightman_d1_swap01_deferred`

Current status of these blockers:

1. `blocker_d1N2OrbitDecomposition_of_sameInvariantQuad_on_FT_deferred` is now
   proved (via `d1_exists_lorentz_of_sameInvariantQuad_on_FT`).
2. `blocker_d1N2InvariantFactorization_on_FT_deferred` is now a proved wrapper
   reducing factorization to `blocker_d1N2SameInvariantQuad_on_FT_implies_eq_deferred`.
3. `blocker_d1N2InvariantModel_core_deferred` is the only remaining
   deferred theorem in the `d=1,n=2` Lorentz route.
4. `blocker_d1N2SameInvariantQuad_on_FT_implies_eq_deferred` is now proved
   directly from:
   - `d1_exists_lorentz_of_sameInvariantQuad_on_FT`, and
   - `complex_lorentz_invariance`.
   It no longer depends on the forward-swap deferred theorem.
5. `blocker_d1N2ForwardSwapEq_on_FT_core_deferred` is now proved by reduction
   from `blocker_d1N2InvariantModel_core_deferred` via
   `d1_n2_forward_swap_eq_of_invariantModel`.
6. `blocker_d1N2InvariantModel_of_wightman_d1_swap01_deferred` is now a proved
   wrapper combining:
   - factorization wrapper above, and
   - `blocker_d1N2InvariantKernelSwapRule_deferred`.
7. `blocker_d1N2ForwardSwapEq_on_FT_deferred` is now an alias wrapper to
   `blocker_d1N2ForwardSwapEq_on_FT_core_deferred`.
8. `blocker_d1N2InvariantModel_core_deferred` is now the explicit deferred
   Lorentz-invariant model-construction statement (the intended single local
   `sorry` in this `d=1,n=2` subroute).
9. The chain has one explicit unresolved analytic core:
   `blocker_d1N2InvariantModel_core_deferred`.
10. Logical bridge now formalized in route infrastructure:
   - `d1_n2_invariantKernelSwapRule_of_forwardSwapEq` packages the direction
     `forward-swap equality => kernel swap rule` for any `FT` factorization
     `hf_onFT`. This isolates exactly what remains to be supplied analytically.
   - `d1_n2_forwardSwapEq_iff_invariantKernelSwapRule` records the full
     equivalence (for fixed `hf_onFT`), making the remaining blocker content
     mathematically explicit.

## Relation to current blocker status

This file does not add axioms and does not alter the top-level BHW theorem statement.
It provides a clean decomposition of the `d=1,n=2` step:

1. Algebraic Lorentz/swap layer (completed here and compiled).
2. Analytic model-construction layer (remaining, deferred in a small set of explicit theorems).
