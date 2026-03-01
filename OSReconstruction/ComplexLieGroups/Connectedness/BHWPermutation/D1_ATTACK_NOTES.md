# d=1 Attack Notes for `PermutationFlow` Blocker

This note targets the `d = 1` sub-branch of the remaining sorry in
`PermutationFlow.lean` (`iterated_eow_permutation_extension`).

## Status Update (2026-02-28, axiom-free rollback)

- `PermutationFlow.lean` currently has three `sorry` warnings:
  - `deferred_isConnected_permOrbitSeedSet_dge2`
  - `deferred_isConnected_permOrbitSeedSet_d1`
  - `deferred_exists_open_zero_nhds_d1_holo`
- No `axiom` placeholders are used in this file.
- The active d=1 local blocker is now the direct local-zero theorem
  `deferred_exists_open_zero_nhds_d1_holo` on a prepared neighborhood.

## Status Update (2026-03-01, route correction)

- The active third sorry in `PermutationFlow.lean` is
  `deferred_eventually_zero_nhds_d1_holo`.
- The temporary blocker
  `deferred_eventually_backWitness_nhds_d1` was intentionally dropped from the
  active proof path: its hypothesis target (eventual local exact back-witness)
  is too strong for generic `d=1` overlap geometry.

Reason (explicit pattern):

1. `n=2`, `σ=swap`, pick `Γ = -Id`.
2. Preparedness (`w ∈ FT`, `Γ·(σ·w) ∈ FT`) can hold on an open neighborhood.
3. Generic back-witness equations `Λ·(σ·w)=w` fail by `D1OrbitSet` rigidity
   (`u1 = ±u0` / `v1 = ±v0` constraints).

So the mathematically correct blocker remains local holomorphic gluing
(`eventually zero`), not local back-witness existence.

## Status Correction (2026-02-28, current theorem name)

After the latest refactor, the active d=1 local blocker theorem is:

- `deferred_eventually_zero_nhds_d1_holo`

which feeds `deferred_exists_open_eq_nhds_d1_on_prepared_domain`.

So the three active deferred declarations in `PermutationFlow.lean` are now:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_eventually_zero_nhds_d1_holo`

This third theorem is the local gluing gap for `g(w)=F(Γ·(σ·w))-F(w)`, and is
not currently reduced to pure connectedness.

## Addendum (2026-03-01, theorem audit after code inspection)

The singular blocker
`deferred_eventually_backWitness_nhds_d1` is not just a "hard Lean step"; it
currently asks for a local identification mechanism that is absent from the
hypotheses.

What is available on a prepared domain:

- `w ∈ FT`,
- `σ·w ∈ ET`,
- `Γ·(σ·w) ∈ FT`.

What is *not* available:

- a local family `Λw` with `Λw·(σ·w)=w`.

The back-witness route would immediately prove `g=0` (via FT-side complex
Lorentz invariance), but this route is nongeneric in d=1. This is now formal,
not heuristic, from:

- [`D1OrbitSet.lean`](/Users/xiyin/OSReconstruction/OSReconstruction/ComplexLieGroups/D1OrbitSet.lean):
  - `swap_backWitness_n2_sum_rigidity`
  - `swap_backWitness_n2_diff_rigidity`
  - `not_exists_swap_backWitness_n2_of_sum_generic`
  - `not_exists_swap_backWitness_n2_of_diff_generic`.

So the remaining local gluing input must be something weaker than local
back-witness existence but strong enough to force a uniqueness anchor for
`g(w) = F(Γ·(σ·w)) - F(w)`.

Lean infrastructure added for this exact shape:

- [`PermutationFlow.lean`](/Users/xiyin/OSReconstruction/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean):
  - `eventually_zero_nhds_of_eventually_back_witness_d1`
  - `deferred_eventually_backWitness_nhds_d1`

This upgrades an **eventual** local back-witness condition at `w0` directly to
the target eventual local vanishing of `g`. So future work can focus purely on
supplying that geometric eventual-witness hypothesis (or replacing it with an
equivalent local uniqueness anchor), without touching the analytic plumbing.

Refinement:

- `deferred_eventually_backWitness_nhds_d1` is now geometric-only in its
  statement (no `F`/holomorphic/boundary/locality parameters), making it the
  exact standalone d=1 geometry target.

## Explicit `d=1, n=2` reduction (swap case)

For `n=2`, the only nontrivial permutation is the swap `σ`.
Write

- `w0 = (t0, x0) in C^2`,
- `w1 = (t1, x1) in C^2`,
- `w = (w0, w1)`.

Any `d=1` complex Lorentz element has matrix form

`Λ = [[a, b], [b, a]]` with `a^2 - b^2 = 1`.

The back-witness equation

`Λ · (σ · w) = w`

is exactly:

1. `Λ w1 = w0`
2. `Λ w0 = w1`.

In light-cone coordinates

- `u := t + x`,
- `v := t - x`,
- `lambda := a + b` (so `a - b = lambda^{-1}`),

the two equations become:

1. `u0 = lambda * u1`, `u1 = lambda * u0`
2. `v0 = lambda^{-1} * v1`, `v1 = lambda^{-1} * v0`.

Hence:

- `(1 - lambda^2) * u0 = 0` and `(1 - lambda^2) * u1 = 0`,
- `(1 - lambda^2) * v0 = 0` and `(1 - lambda^2) * v1 = 0`.

So away from degenerate loci (`u0=u1=0` or `v0=v1=0`), we must have
`lambda^2 = 1`.

- If `lambda = 1`, then `u0=u1` and `v0=v1`, so `w0 = w1`.
- If `lambda = -1`, then `u0=-u1` and `v0=-v1`, so `w0 = -w1`.

This shows the back-witness condition is highly nongeneric in the swap case:
it holds on thin algebraic subsets, not on a typical open neighborhood.

This explicit structure is now formalized in Lean:

- `swap_backWitness_n2_component_constraints`
- `swap_backWitness_n2_lightcone_constraints`
- `swap_backWitness_n2_sum_rigidity`
- `swap_backWitness_n2_diff_rigidity`
- `not_exists_swap_backWitness_n2_of_sum_generic`
- `not_exists_swap_backWitness_n2_of_diff_generic`

in [`D1OrbitSet.lean`](/Users/xiyin/OSReconstruction/OSReconstruction/ComplexLieGroups/D1OrbitSet.lean).

Consequence for strategy:

- a proof route that *requires* local back-witness existence on a neighborhood
  is unlikely to succeed in full generality;
- the d=1 local gluing theorem should instead be attacked through a different
  analytic-continuation/uniqueness anchor mechanism on overlap domains.

Current deferred d=1 target in code:

- The deferred local theorem is
  `deferred_exists_open_zero_nhds_d1_holo`:
  at a prepared anchor `(w0, Γ)` and prepared domain `U`, with
  `g(w) := F(Γ·(σ·w)) - F(w)` holomorphic on `U`, produce an open neighborhood
  `W` of `w0` in `U` where `g = 0`.
- `exists_open_nhds_overlap_and_forward_of_anchor_d1` is now proved and
  supplies the prepared neighborhood from anchor data.
- `deferred_exists_open_eq_nhds_d1_at_anchor` and
  `deferred_local_eventually_Feq_d1_at_anchor` are now proved wrappers.
- Inside `deferred_exists_open_eq_nhds_d1_on_prepared_domain`, the deterministic
  analytic setup is now already done:
  - define `φ(w) := Γ·(σ·w)`,
  - prove `MapsTo φ U FT`,
  - prove holomorphicity of `g(w) := F(φ(w)) - F(w)` on `U`.
  The remaining deferred substep is exactly this local zero-neighborhood
  extraction theorem.
- `deferred_forward_eventually_Feq_d1_of_seedConnected_nontrivial` is now a
  proved wrapper: anchor existence is extracted by
  `exists_forward_anchor_with_lorentz_of_seedConnected_d1`, then the remaining
  local gluing is delegated to the theorem above.
- The transport and local-to-open upgrades are now infrastructure:
  `eventually_extendF_base_eq_of_eventually_forward_eq_fixedLorentz`,
  `exists_forward_open_anchor_of_eventuallyEq_local`.
- The forward-base propagation theorem
  `deferred_forward_base_perm_eq_d1_of_seedConnected`
  is now proved from this anchor package via
  `forward_base_eq_of_open_anchor_local`.

## What fails (already formalized)

1. Real-anchor route via Jost witness is unavailable in general:
- no real ET pair / Jost witness for `n=2`, adjacent swap (probe theorem).

2. Midpoint-drop chain route is false in `d=1`:
- the implication
  `Γ·((σ*swap)·w) ∈ FT -> Γ·(σ·w) ∈ FT`
  fails (counterexample theorem in test).

3. Numerical prepared-anchor probe (`d=1`, `n=2`, swap) confirms midpoint bad
   points exist even with prepared conditions:
- found `w ∈ FT` and `Γ·(swap·w) ∈ FT` but `Γ·w ∉ FT`.
- by openness, this yields local prepared domains intersecting
  `midCondBadSet_d1`, so the midpoint-stability blocker is genuinely nontrivial.

So the `d>=2` strategy does not port.

Production helper now added:

- `Adjacency.adjSwap_not_mem_forwardTube_d1`:
  for any adjacent swap in `d=1`, if `z ∈ FT` then `swap(z) ∉ FT`.

This codifies the geometric reason the current midpoint implication orientation
fails in the `π = σ*swap` branch.

## Structural obstruction in current midpoint direction

There is a precise branch where the current midpoint implication direction
cannot be true.

Fix adjacent `i`, define `ip1 := ⟨i.val + 1, hi⟩`, `swap := Equiv.swap i ip1`,
and set `π := σ * swap`.

Then:

1. `π * swap = σ`.
2. On any prepared domain `U`, assumptions give
   `Γ·(σ·w) ∈ FT` for every `w ∈ U`.
   Therefore the midpoint antecedent
   `A(w) := Γ·((π*swap)·w) ∈ FT`
   holds on all `U`.
3. The midpoint consequent is
   `B(w) := Γ·(π·w) ∈ FT = Γ·((σ*swap)·w) ∈ FT`.
   By commutation, this is
   `swap(Γ·(σ·w)) ∈ FT`.
4. In `d = 1`, adjacent swap sends FT points out of FT (time-order reversal
   at the swapped adjacent slot), so preparedness (`Γ·(σ·w) ∈ FT`) forces
   `¬B(w)`.

Hence in this branch we get `A(w) ∧ ¬B(w)` on the prepared neighborhood, so
`midCondBadAtPermStepSet_d1` is not separable from the anchor there. This is a
structural reason the remaining fixed-step closure theorem has resisted proof:
the midpoint orientation itself is misaligned for `d=1`.

## Existing strong d=1 infrastructure

From `D1OrbitSet.lean` and `IndexSetD1.lean`:

- `SO^+(1,1;C)` rapidity normal form (`a + i b`).
- principal imaginary strip control (`|b| < pi`) for orbit witnesses.
- orbit preconnectedness in d=1:
  - `orbitSet_isPreconnected_d1` / wrappers.
- fixed-slice connectedness for ET witnesses:
  - `permLambdaSlice_isConnected_d1_of_perm_mem_ET`.

This is enough to do serious geometric work without introducing assumptions.

## New caveat confirmed in production code

- `forward_base_eq_of_real_open_anchor` (in `OverlapAnchor.lean`) is not the
  missing d=1 bridge: it is stated on `permForwardOverlapSet ⊆ ForwardTube`.
- For `n > 0`, `ForwardTube` has no real points, so the required real-open anchor
  set is empty in the intended applications.
- Conclusion: d=1 still needs a **complex-anchor / gluing** bridge, not a
  real-open-forward-anchor bridge.

## Likely viable theorem shape to add

A d=1 replacement for real-Jost anchoring should avoid real points and use
complex open anchoring in the ET-overlap domain.

Candidate target:

```lean
private theorem extendF_perm_overlap_d1_of_complex_anchor
  ... :
  forall z in ET,
    permAct sigma z in ET ->
    extendF F (permAct sigma z) = extendF F z
```

Proof outline candidate:

1. Set `D := permExtendedOverlapSet (d := 1) n sigma`.
2. Prove `IsConnected D` from connectedness of `permForwardOverlapSet`.
3. Build a complex-open nonempty `V ⊆ D` where equality is known.
4. Apply `extendF_perm_eq_on_connectedDomain_of_openSubset`.
   (or directly `extendF_perm_overlap_of_forward_open_anchor`
   from `OverlapAnchor.lean` after proving connectedness + anchor on
   `permForwardOverlapSet`).

New helper now present in code:

- `exists_overlap_open_anchor_of_eventuallyEq_local`
- `extendF_perm_overlap_of_eventuallyEq_anchor_and_forwardOverlapConnected`

So the local d=1 mission can be phrased as one precise target:

- produce eventual local overlap equality at one complex anchor in `D_σ`.

The only hard part is step (3): constructing `V` without real Jost points.

## Concrete subgoals for step (3)

For a fixed permutation `sigma`:

1. Build an analytic family of overlap witnesses parameterized by d=1 rapidity.
2. Show the family stays inside `D` on an interval (pure-imag rapidity segment).
3. Prove `extendF` equality along that family by adjacent EOW + Lorentz transport.
4. Extract an open neighborhood `V` in complex coordinates.

The rapidity segment lemmas already exist in `D1OrbitSet.lean` and should be
reused directly.

## Why this is plausible

- d=1 group geometry is explicit (one complex rapidity parameter).
- Existing lemmas already control cone membership along rapidity segments.
- This removes dependence on non-existent real spacelike anchors.

## New analysis: orbit-transport route (what almost works, what fails)

This turn we tested a more direct identity strategy for the reduced local
zero theorem `deferred_exists_open_zero_nhds_d1_holo`.

Set

- `z := permAct σ w`,
- `g(w) := F(Γ·z) - F(w)`.

On the prepared neighborhood `U`, we know:

- `w ∈ FT`,
- `z ∈ ET`,
- `Γ·z ∈ FT`.

The tempting idea is:

1. `F(Γ·z)` can be viewed as `extendF F z` (using witness `Γ`).
2. If one can also realize `F(w)` as `extendF F z` via another witness, then
   `g(w)=0`.

Concretely, this would follow if we had a Lorentz element `Λw` with
`Λw·(permAct σ w) = w`. Then:

- both `Λw·z = w` and `Γ·z` are in `FT`,
- complex Lorentz invariance on `FT` gives
  `F(Γ·z) = F(Λw·z) = F(w)`.

### Exact obstruction

Current assumptions do **not** provide such a `Λw`. Membership
`w ∈ permForwardOverlapSet` only gives:

- `w ∈ FT`,
- `permAct σ w ∈ ET`.

This means there exists some witness sending `σ·w` into `FT`, but not
necessarily to the specific target `w`.

So we are missing a theorem of the form:

- "`w` and `σ·w` lie in the same complex Lorentz orbit with a witness inside the
  prepared overlap family",

or an equivalent local anchor theorem that directly forces `g=0` on a
nontrivial uniqueness set.

### Consequence for current blocker

The remaining `sorry` is therefore genuinely a **new d=1 local gluing input**,
not a syntax gap in existing identity-theorem plumbing.

## Minimal corrected local theorem shape (recommended replacement target)

The current fixed-step closure theorem
`deferred_not_mem_closure_midCondBadAtPermStep_d1` is not a viable universal
target under its present assumptions, because the branch
`π * swap(i,i+1) = σ` is formally obstructed.

A mathematically consistent replacement target for the local gluing stage is:

```lean
private theorem deferred_exists_open_backWitness_nhds_d1
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ) (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U) (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n σ ∧
      complexLorentzAction Γ (permAct (d := 1) σ w) ∈ ForwardTube 1 n) :
    ∃ W : Set (Fin n → Fin (1 + 1) → ℂ),
      IsOpen W ∧
      w0 ∈ W ∧
      W ⊆ U ∧
      (∀ w ∈ W, ∃ Λ : ComplexLorentzGroup 1,
        complexLorentzAction Λ (permAct (d := 1) σ w) = w)
```

Why this shape is aligned:

- It matches the already-proved helper
  `g_zero_on_prepared_of_back_witness_d1`.
- It avoids the impossible midpoint implication orientation in d=1.
- It feeds directly into the existing local-zero packaging route
  (`_hBackRoute`) without changing global theorem interfaces.

Minimal downstream consequence:

- If the theorem above is available, `deferred_exists_open_zero_nhds_d1_holo`
  closes without requiring the fixed-step midpoint bad-set closure theorem.

## Immediate coding checklist

1. Add a d=1-specific lemma in `PermutationFlow.lean` that restates the needed
   rapidity-segment invariance in the `permExtendedOverlapSet` language.
2. Add a helper converting d=1 rapidity-strip witnesses to nonempty open anchor
   subsets `V`.
3. Use `extendF_perm_eq_on_connectedDomain_of_openSubset` to close the d=1 branch.

## Current precise blocker shape in code

After latest refactor, the non-connectivity blocker is exactly:

```lean
deferred_not_mem_closure_midCondBadAtPermStep_d1
```

with fixed data:

- `w0 ∈ permForwardOverlapSet (d := 1) n σ`
- `Γ·(σ·w0) ∈ ForwardTube 1 n`

and target (fixed-step closure-separation form):

```lean
w0 ∉ closure (U ∩ midCondBadAtPermStepSet_d1 n Γ π i hi)
```

Inside `deferred_exists_open_zero_nhds_d1_holo`, proved sufficient routes are
now packaged:

```lean
_hBackRoute : (local back-witness pack) -> (local zero-neighborhood pack)
```

using helper lemmas:

- `forward_eq_of_back_witness_d1`
- `g_zero_on_prepared_of_back_witness_d1`

The eventual form is still derived downstream:

```lean
∀ᶠ w in 𝓝 w0,
  w ∈ permForwardOverlapSet (d := 1) n σ →
  F (Γ·(σ·w)) = F w
```

Everything else is now infrastructure/proved assembly:

- anchor existence from seed connectedness:
  `exists_forward_anchor_with_lorentz_of_seedConnected_d1`
- conversion `F`-local-eventual -> `extendF`-local-eventual:
  `eventually_extendF_base_eq_of_eventually_forward_eq_fixedLorentz`
- local-eventual -> explicit open anchor:
  `exists_forward_open_anchor_of_eventuallyEq_local`
- open-anchor propagation on connected forward-overlap:
  `forward_base_eq_of_open_anchor_local`

The midpoint-neighborhood theorem is now proved from the generic topological
reduction `exists_open_midCond_nhds_of_not_mem_closure_bad_d1`; the remaining
work is the single fixed-anchor midpoint-stability neighborhood theorem above.

## 2026-03-01 addendum: current blocker reality check

This note section supersedes the midpoint-focused subgoals above.

### 1. Midpoint route is definitively not the path

In production code (`PermutationFlow.lean`), the `d=1` obstruction branch
`π * swap(i,i+1) = σ` is now formalized and used to show:

- the midpoint implication orientation fails in this branch;
- no local open neighborhood can satisfy that fixed-step midpoint implication.

So the remaining blocker is **not** a missing midpoint argument.

### 2. Current singular local-gluing target

The active third `sorry` is now:

- `deferred_eventually_zero_nhds_d1_holo`

with statement shape:

- prepared domain `U` around anchor `w0`,
- `g(w) := F(Γ·(σ·w)) - F(w)` holomorphic on `U`,
- goal: `∀ᶠ w in 𝓝 w0, w ∈ U → g w = 0`.

### 3. n=2 status: what is proved vs not proved

For `d=1, n=2, σ=swap`, the following are now proved in
`D1OrbitSet.lean`:

- `swap_backWitness_n2_component_constraints`
- `swap_backWitness_n2_lightcone_constraints`
- `swap_backWitness_n2_sum_rigidity`
- `swap_backWitness_n2_diff_rigidity`
- `not_exists_swap_backWitness_n2_of_sum_generic`
- `not_exists_swap_backWitness_n2_of_diff_generic`

Meaning:

- local back-witness existence (`Λ·(swap·w)=w`) is highly nongeneric;
- therefore the "local back-witness neighborhood" route cannot be a universal
  closure mechanism.

Important nuance:

- this does **not** by itself disprove `deferred_eventually_zero_nhds_d1_holo`;
- it only rules out one candidate proof strategy.

### 4. Practical conclusion for ongoing proof work

The remaining non-connectivity gap is now precisely:

- obtain local zero propagation for `g` without relying on midpoint transport
  and without assuming local back-witness existence.

So the next viable attack must be a direct d=1 overlap-domain analytic
continuation/uniqueness mechanism compatible with the existing EOW packaging.

### 5. Hypothesis-audit warning (possible statement-strength issue)

The current `PermutationFlow` final theorem stack assumes:

- holomorphicity on `FT`,
- real Lorentz invariance on `FT`,
- boundary continuity,
- local commutativity at real spacelike adjacent pairs.

No explicit translation/spectral assumptions appear in this stack.

This may matter for the blocker:

- `deferred_eventually_zero_nhds_d1_holo` tries to force local equality of
  `g(w)=F(Γ·(σ·w))-F(w)` from these inputs alone on prepared neighborhoods.
- If the intended classical BHW usage implicitly relies on stronger Wightman
  structure, the present code-level theorem may be formally stronger than what
  is currently encoded.

This does not yet constitute a formal counterexample, but it is a concrete
reason the local d=1 gluing step may be intrinsically underdetermined at the
current hypothesis level.

## Status Update (2026-03-01, non-vacuity sanity check)

A direct numerical search confirms that the prepared-domain hypotheses for the
local d=1 blocker are **non-vacuous** even in the minimal nontrivial case
`n=2`, `σ=swap`.

Search setup (Python sanity probe, not a proof):

- sample `w=(z0,z1)` with `w ∈ FT_{1,2}`,
- sample complex rapidity `ξ` (`Γ = Γ(ξ)` in `SO^+(1,1;C)`),
- test whether `Γ·(σ·w) ∈ FT_{1,2}`.

A hit is found quickly, e.g.

- `ξ = 0.8443316127759455 + 0.8244065231845688 i`,
- `z0 = (0.10624554015472087 + 1.3684699290726963 i,
         -0.3442305867822879 - 0.1705351616021371 i)`,
- `z1 = (0.27710743456580067 + 1.959819968416154 i,
         -1.2936577919277112 + 0.07726390121912452 i)`.

So the local theorem
`deferred_eventually_zero_nhds_d1_holo` is not vacuous by contradiction of
hypotheses; it needs an actual geometric/analytic continuation input.

## Route note (2026-03-01)

A plausible next attack is to reframe the blocker as gluing of two holomorphic
branches on the two-tube pair

- `T1 := FT`,
- `T2 := { w | Γ·(σ·w) ∈ FT }`,

for

- `f1(w) := F(w)` on `T1`,
- `f2(w) := F(Γ·(σ·w))` on `T2`.

The blocker asks for local equality `f1=f2` near the prepared anchor in
`T1 ∩ T2`. Existing code already provides adjacent EOW infrastructure, but this
specific two-tube gluing is not yet packaged as a theorem in the current
modules.

## Status Update (2026-03-01, theorem normalization)

The old local-zero blocker theorem has been normalized:

- `deferred_eventually_zero_nhds_d1_holo` is proved as a wrapper.
- The actual remaining local d=1 blocker is now the core equality theorem
  `deferred_eventually_forward_eq_nhds_d1_holo`.

This removes `g`/difference bookkeeping from the deferred statement and leaves
exactly the geometric-analytic content that still needs to be supplied.

## Status Update (2026-03-01, propagation closed)

Major local-proof progress:

- `deferred_eventually_forward_eq_nhds_d1_holo` no longer contains a `sorry`.
- The proof now uses a standard SCV uniqueness pipeline on a connected ball:
  - define `h(w)=F(Γ·(σ·w))-F(w)`,
  - show `h` holomorphic on `D = ball(w0, ε)`,
  - use `identity_theorem_totally_real_product` from a real-open anchor set in `D`,
  - conclude eventual equality near `w0`.

What remains deferred is exactly the geometric anchor production inside that
ball:

- `deferred_exists_real_open_anchor_eq_d1_on_ball`.

So the d=1 non-connectivity blocker is now reduced to one geometrically clean
local statement, with no remaining analytic plumbing gap.

## Erratum (2026-03-01, authoritative current state)

The immediately preceding "propagation closed" section reflects a reverted
branch. In the active code, the blocker is:

- `deferred_eventually_forward_eq_nhds_d1_holo`.

So the live deferred set is:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_eventually_forward_eq_nhds_d1_holo`

## Practical guidance for next attacks

Use these as hard constraints:

1. Midpoint orientation is structurally obstructed at `π * swap = σ`.
2. Exact local back-witness existence is nongeneric in `d=1` (`n=2` rigidity).

Most promising direction now is a local uniqueness anchor in `Lambda`-slice
variables, not midpoint-step or exact-back-witness routes.

## Update (2026-03-01, route materialized in `PermutationFlow.lean`)

Two slice-route lemmas are now in production code:

1. `forward_eq_of_slice_anchor_d1`
2. `eventually_forward_eq_nhds_of_eventually_slice_anchor_d1`

The active blocker theorem `deferred_eventually_forward_eq_nhds_d1_holo` is
rewritten to reduce directly to one missing eventual hypothesis:

- near `w0`, existence of `Λ₀` with
  `Λ₀·(σ·w) ∈ FT` and `F(Λ₀·(σ·w)) = F(w)`.

This is now the exact unresolved local d=1 content.
