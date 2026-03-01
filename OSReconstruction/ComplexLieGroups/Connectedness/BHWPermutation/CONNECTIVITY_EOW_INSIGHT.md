# Connectivity + EOW Insight (Detailed Discussion)

This note consolidates the precise mathematical conclusions from the recent
discussion and maps them to the current Lean architecture in
`BHWPermutation/PermutationFlow.lean`.

The main point is:

- EOW is the right local analytic bridge from boundary equality to interior
  holomorphic equality.
- Global permutation overlap equality needs more than local gluing: it needs
  a globalization mechanism (connectedness + uniqueness anchor in the target
  domain).

## 0. Update (2026-02-28)

Current compile-facing state in `PermutationFlow.lean`:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_not_mem_closure_midCondBadAtPermStep_d1`

No `axiom` placeholders are used in `PermutationFlow.lean`.
The d=1 local zero-neighborhood theorem currently closes via midpoint-pack
input (`_hMidRoute`).

## 0b. Correction (2026-02-28, current code state)

The active third deferred theorem is now:

- `deferred_eventually_zero_nhds_d1_holo`

not the older midpoint-closure placeholder names.

Current unresolved set in `PermutationFlow.lean`:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_eventually_backWitness_nhds_d1`

## 0c. Addendum (2026-03-01)

The third deferred theorem remains unresolved after targeted d=1 audit.
The obstruction is not parser-level:

- midpoint branch `π * swap = σ` is formally blocked by
  `not_exists_open_midCondAtPermStep_nhds_of_mul_swap_eq_sigma_d1`,
- local back-witness existence is formally nongeneric in `d=1, n=2`
  (`D1OrbitSet` rigidity/no-existence theorems).

Hence the remaining gap is a genuine missing geometric/analytic continuation
input, not a hidden connectedness lemma.

Refactor note:

- `deferred_eventually_zero_nhds_d1_holo` is now proved by reduction to the
  eventual-back-witness form
  (`eventually_zero_nhds_of_eventually_back_witness_d1`).
- The unresolved local geometric content is isolated in
  `deferred_eventually_backWitness_nhds_d1`.

### Precise content of the third blocker

At a prepared anchor/domain `(w0, Γ, U)`, with

- `g(w) := F(Γ·(σ·w)) - F(w)`,
- `DifferentiableOn ℂ g U`,
- preparedness `w ∈ U -> (w ∈ FT and Γ·(σ·w) ∈ FT)`,

prove:

- `∀ᶠ w in 𝓝 w0, w ∈ U -> g w = 0`.

### Why this is not automatic from current assumptions

This would require a local mechanism identifying the two FT-side evaluations
of `F` at `Γ·(σ·w)` and `w`.

Current hypotheses do not provide, for prepared `w`, a witness of the form
`Λw·(σ·w)=w` (or an equivalent local uniqueness-anchor theorem on overlap
domains). So this third theorem is genuinely additional geometric input, not
just connectedness plus identity theorem.

## 0d. Update (2026-03-01, blocker-shape correction)

The active code path has been corrected:

- `deferred_eventually_backWitness_nhds_d1` is no longer used as the third
  deferred theorem.
- `deferred_eventually_zero_nhds_d1_holo` is again the singular local d=1
  gluing blocker.

Rationale:

- exact local back-witness existence is too strong and nongeneric in `d=1`
  (already formalized by `D1OrbitSet` `n=2` rigidity/no-existence lemmas),
- the blocker should therefore stay at the correct analytic target:
  local holomorphic zero propagation for
  `g(w) = F(Γ·(σ·w)) - F(w)` on prepared domains.

## 1. Precise target identity in the blocker

For fixed `σ : Equiv.Perm (Fin n)`, the overlap target is:

`hExtPerm`:
`forall z, z ∈ ExtendedTube d n -> permAct σ z ∈ ExtendedTube d n ->
  extendF F (permAct σ z) = extendF F z`.

Equivalently, if

`Dσ := { z | z ∈ ET and σ·z ∈ ET }`

and

`gσ(z) := extendF F (σ·z) - extendF F z`,

the target is `gσ = 0` on all of `Dσ`.

## 2. What is assumed about `F` initially

In the BHW setup, we assume:

1. Holomorphicity on forward tube:
   `hF_holo : DifferentiableOn ℂ F (ForwardTube d n)`.
2. Lorentz invariance on forward tube:
   `hF_lorentz`.
3. Boundary regularity at real points:
   `hF_bv : ContinuousWithinAt F (ForwardTube d n) (realEmbed x)`.
4. Local commutativity at real spacelike points:
   `hF_local`.

Important:

- We do not assume `F` is holomorphic on ET a priori.
- ET-holomorphicity comes from the extension construction (`extendF` and related
  theorems).

## 3. Why connectedness by itself is insufficient

Connectedness of `Dσ` does not imply `gσ = 0`.

It only gives uniqueness *if* we already know `gσ` vanishes on a uniqueness set
inside `Dσ` (for example:

1. nonempty open complex subset of `Dσ`, or
2. nonempty open subset of a totally real submanifold inside `Dσ` under the
   identity theorem infrastructure used in this project).

So propagation is:

`holomorphic on Dσ + uniqueness-set vanishing + Dσ connected -> global vanishing`.

Not just:

`holomorphic on Dσ + Dσ connected -> global vanishing`.

## 4. Why EOW is essential but still local

Boundary equality data from `hF_bv + hF_local` is on real spacelike points,
which are boundary/edge data relative to tube domains.

EOW gives the local bridge:

1. start with two holomorphic sides (e.g. `F` and `F∘swap` on adjacent tube
   domains),
2. assume matching boundary traces on a real edge set,
3. conclude a holomorphic glued function on a complex neighborhood crossing the
   edge.

This yields interior equality on that local glued neighborhood.

What EOW does not automatically give by itself:

- global equality on all of `Dσ` for arbitrary `σ` without additional cover/
  chain/connectedness arguments.

## 5. "Repeated analytic continuation" vs "connectedness + anchor"

These are two descriptions of the same globalization logic.

### Patchwise continuation view

You prove equality patch by patch:

1. equality on one patch,
2. overlap transfer to neighboring patch,
3. continue along a chain of overlapping patches.

To make this rigorous you still need:

1. enough patches to cover the target component,
2. nontrivial overlaps supplying transfer,
3. no path inconsistency (uniqueness handles this).

### Identity-theorem view

You package the same structure as:

1. connected domain `D`,
2. holomorphic difference `g`,
3. one uniqueness anchor set where `g=0`.

Then identity theorem gives `g=0` on all `D`.

So "repeat extension" is not weaker; it is equivalent proof content reorganized.

## 6. What can be weakened (and what cannot)

`Open` is sufficient but not the only possible anchor shape.

Available weaker route in current code:

- `Adjacency.lean` provides
  `extendF_perm_eq_on_connectedDomain_of_realOpen`,
  i.e. uniqueness propagation from a nonempty open set in the totally-real
  subspace.

Important SCV caveat:

- For multivariable holomorphic functions on product domains
  (`Fin n -> Fin (d+1) -> ℂ`), a mere accumulation-point/frequently-equal
  hypothesis is generally **not** enough for global identity.
- That weaker criterion is a 1D tool; in several variables, zero sets can have
  positive codimension.

So the right statement is:

- We do not need a complex-open anchor specifically.
- But we do need an anchor type that is strong enough for SCV uniqueness
  (complex-open, or totally-real-open with the dedicated theorem).

## 7. Explicit `d = 1, n = 2` framing

For two points `z1, z2` in complexified `1+1` Minkowski:

`z_i = (z_i^0, z_i^1) in C^2`.

Forward tube condition:

`Im(z2^0 - z1^0) > |Im(z2^1 - z1^1)|`.

For swap `σ(1)=2, σ(2)=1`, the overlap domain is:

`Dσ = { z in ET | σ·z in ET }`.

In this case, known probes indicate the naive real-anchor strategy used in
`d>=2` does not transfer uniformly. That is why the remaining `d=1` step is a
separate bridge theorem rather than just reusing the high-dimensional witness
package.

## 8. Existing formal infrastructure (already available)

### Local EOW / adjacency layer

- `eow_adj_swap_on_overlap` (`Adjacency.lean`)
- `extendF_adjSwap_eq_of_connected_overlap` (`Adjacency.lean`)
- `extendF_perm_eq_on_connectedDomain_of_realOpen` (`Adjacency.lean`)

### Open-anchor globalization wrappers

- `extendF_perm_overlap_of_open_anchor_and_forwardOverlapConnected`
  (`OverlapAnchor.lean`)
- `forward_base_eq_of_open_anchor` (`OverlapAnchor.lean`)
- `extendF_perm_overlap_of_forward_open_anchor` (`OverlapAnchor.lean`)

These wrappers can be used when complex-open anchors are easier to construct,
but they are not mandatory if a totally-real uniqueness route is cleaner.

## 9. Current blocker decomposition in `PermutationFlow`

Compile-facing `sorry` obligations are now:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_not_mem_closure_midCondBadAtPermStep_d1`

Interpretation:

1. and 2. are connectivity theorems.
3. is the d=1 fixed-step local geometric closure-separation bridge.

## 10. Why the d=1 geometric bridge is not "just connectivity"

The fixed-step midpoint-closure statement is a local geometric
closure-separation statement.
It is not implied by connectivity alone: it still encodes a nontrivial local
orbit/forward-tube implication schema near the chosen anchor.

In short:

- first two deferred lemmas: pure geometry,
- third deferred lemma: local d=1 geometry for midpoint-bad fixed-step closure.

## 11. Suggested proof shape for the third deferred lemma

There are at least two viable routes.

### Route A: Totally-real anchor route

1. derive connectedness of forward-overlap set from seed connectedness in `d=1`,
2. produce a real-open anchor subset where equality holds (using local EOW and
   `hF_bv/hF_local`),
3. apply `extendF_perm_eq_on_connectedDomain_of_realOpen` style propagation to
   get global ET-overlap equality.

### Route B: Open-anchor route

1. derive forward-overlap connectedness,
2. build nonempty open complex anchor `W` with base equality
   `extendF(σ·w)=F(w)` on `W`,
3. apply `extendF_perm_overlap_of_forward_open_anchor`.

Both routes are valid; A uses weaker anchor assumptions and matches existing
totally-real uniqueness templates, while B offers a cleaner wrapper interface
once an open anchor is available.

## 12. Practical conclusion

The central conceptual confusion is resolved:

1. EOW is enough for local boundary-to-interior transfer.
2. Globalization still needs uniqueness propagation data (anchor + connectedness).
3. This is exactly what the deferred split now isolates.

Therefore, the remaining work is no longer "find the big mysterious analytic
step", but:

1. prove the two connectivity inputs, and
2. implement one concrete `d=1` globalization bridge theorem using existing
   identity-theorem infrastructure.

## 14. New technical obstruction (current turn)

For the reduced local zero theorem
`deferred_exists_open_zero_nhds_d1_holo`, we analyzed the following route:

1. write `g(w) = F(Γ·(σ·w)) - F(w)`,
2. on prepared `U`, reinterpret `F(Γ·(σ·w))` as `extendF F (σ·w)` (valid),
3. try to identify `F(w)` with the same `extendF F (σ·w)` via a second Lorentz
   witness.

This would close the theorem immediately if one had, for each `w ∈ U`, a
Lorentz element `Λw` with
`Λw·(σ·w) = w`.

Then both `Γ·(σ·w)` and `Λw·(σ·w)=w` lie in `FT`, and complex Lorentz
invariance on `FT` forces equality.

### Why it fails now

`w ∈ permForwardOverlapSet` only gives existence of a witness sending `σ·w`
somewhere into `FT`, not specifically to `w`. So the required second witness is
not currently available.

Hence the remaining d=1 local theorem is not a mere rephrasing of connectedness
or identity theorem; it needs an additional geometric/orbit input (or an
equivalent local gluing theorem that bypasses this witness requirement).

## 13. Concrete recipe for the third deferred lemma (`d = 1` bridge)

Target deferred lemma:

- `deferred_extendF_perm_overlap_d1_of_seedConnected`
  (`PermutationFlow.lean`)

Input:

1. `hseed_conn : IsConnected (permOrbitSeedSet (d := 1) n σ)`,
2. analytic hypotheses `hF_holo`, `hF_lorentz`, `hF_bv`, `hF_local`.

Output:

`forall z in ET, σ·z in ET -> extendF(σ·z)=extendF(z)`.

### 13.1 Preferred structure

Use existing wrapper theorem:

1. turn seed connectedness into forward-overlap connectedness:
   `isConnected_permOrbitSeedSet_iff_permForwardOverlapSet` (with `d := 1`),
2. prove base identity on `Ωσ := {w in FT | σ·w in ET}`,
3. apply:
   `extendF_perm_overlap_of_forward_base`.

This keeps the bridge proof short and isolates the hard part in step (2).

### 13.2 What exactly step (2) must prove

Need:

`hBase : forall w in FT, σ·w in ET -> extendF(σ·w)=F(w)`.

Equivalent form:

`g_base(w) := extendF(σ·w) - F(w)` vanishes on all of `Ωσ`.

### 13.3 Two implementation options for `hBase`

Option A (real/totally-real uniqueness):

1. pick connected domain `Ωσ`,
2. prove holomorphicity of `w ↦ extendF(σ·w)` on `Ωσ`,
3. use local EOW/locality to show equality on a nonempty real-open subset
   `V ⊆ Ωσ` (in real subspace),
4. apply identity theorem template (totally-real version) on `Ωσ`.

Option B (open complex anchor):

1. construct nonempty open complex `W ⊆ Ωσ`,
2. prove base equality on `W`,
3. apply `forward_base_eq_of_open_anchor`,
4. then apply `extendF_perm_overlap_of_forward_base`.

Both are valid. Option A requires less topological strength on the anchor set.

Status caveat (important in current code):

- The currently added theorem `forward_base_eq_of_real_open_anchor` is written on
  `Ωσ ⊆ ForwardTube`. For `n > 0`, `ForwardTube` has no real points, so this
  specific theorem cannot directly discharge d = 1.
- The usable totally-real route is still the ET-overlap-domain form
  (`extendF_perm_eq_on_connectedDomain_of_realOpen`), where real Jost anchors can
  exist when available.
- Therefore the d = 1 blocker is now: build a non-real-anchor propagation step
  (complex anchor / gluing chain) or equivalent replacement.

New infrastructure now available in `OverlapAnchor.lean`:

- `exists_overlap_open_anchor_of_eventuallyEq_local`:
  eventual local equality at one complex anchor in `D_σ` gives a nonempty
  complex-open anchor subset.
- `extendF_perm_overlap_of_eventuallyEq_anchor_and_forwardOverlapConnected`:
  combines that extraction with connected propagation on overlap domains.

This repackages the d=1 local target cleanly as:

- construct one complex anchor point in `D_σ` with eventual local equality.

Also now promoted from test/probe to production (`Adjacency.lean`):

- `adjSwap_not_mem_forwardTube_d1`:
  adjacent swap sends any `d=1` forward-tube point out of `FT`.

This is the formal geometric obstruction behind the current midpoint-step
orientation.

## 14. Lean-level proof skeleton (for direct coding)

```
have hFwd_conn : IsConnected (permForwardOverlapSet (d := 1) n σ) := by
  exact (isConnected_permOrbitSeedSet_iff_permForwardOverlapSet (d := 1) n σ).1 hseed_conn

have hBase :
  ∀ w, w ∈ ForwardTube 1 n ->
    permAct (d := 1) σ w ∈ ExtendedTube 1 n ->
    extendF F (permAct (d := 1) σ w) = F w := by
  -- prove by Option A or B

exact extendF_perm_overlap_of_forward_base (d := 1) (n := n)
  F hF_holo hF_lorentz σ hBase
```

This is the intended endpoint for the deferred bridge theorem.

Current code status:

- `deferred_extendF_perm_overlap_d1_of_seedConnected` is now proved by reducing
  to a dedicated base-identity lemma
  `deferred_forward_base_perm_eq_d1_of_seedConnected`.
- `deferred_forward_base_perm_eq_d1_of_seedConnected` is now also proved by
  open-anchor propagation (`forward_base_eq_of_open_anchor_local`).
- The only unresolved non-connectivity content is now the local midpoint
  closure-separation extraction:
  `deferred_not_mem_closure_midCondBadAtPermStep_d1`
  (the genuinely hard branch `σ ≠ 1`, `n ≥ 2`).
  This theorem now has a proved easy branch:
  if `Γ·(π·w0) ∈ FT`, closure separation is immediate from openness/continuity.
  It also has a proved antecedent-closure reduction:
  if `w0 ∉ closure (U ∩ midCondAntecedentAtPermStepSet_d1 n Γ π i hi)`, the
  bad-set closure claim follows by monotonicity.
  The anchor-obstruction pair is now explicit:
  `mem_midCondBadAtPermStep_of_anchor_flags_d1` and
  `mem_closure_midCondBadAtPermStep_of_anchor_bad_d1`.
  The remaining unresolved branch is the intersection regime:
  `Γ·(π·w0) ∉ FT` together with
  `w0 ∈ closure (U ∩ midCondAntecedentAtPermStepSet_d1 n Γ π i hi)`.
  The local zero theorem `deferred_exists_open_zero_nhds_d1_holo` is now proved
  by reducing to this via the midpoint-pack/topological helpers (`_hMidRoute`).
  A proved internal route now isolates the geometric piece:
  inside the theorem, `_hBackRoute` shows that a local back-witness pack
  (`Λw·(σ·w)=w` on an open neighborhood) implies the required zero-neighborhood.
  This route uses explicit transport helpers
  (`forward_eq_of_back_witness_d1`,
  `g_zero_on_prepared_of_back_witness_d1`).
  The neighborhood-preparation step is already proved as
  `exists_open_nhds_overlap_and_forward_of_anchor_d1`, and the at-anchor
  wrapper `deferred_exists_open_eq_nhds_d1_at_anchor` is now assembly, as is
  `deferred_exists_open_eq_nhds_d1_on_prepared_domain`.
  The eventual form
  `deferred_local_eventually_Feq_d1_at_anchor` is now derived from this by
  open-neighborhood-to-eventual conversion.
  The existence half is now separated and proved as
  `exists_forward_anchor_with_lorentz_of_seedConnected_d1`, and the wrapper
  `deferred_forward_eventually_Feq_d1_of_seedConnected_nontrivial` is now
  assembly. The eventual `F` anchor is then upgraded to an eventual `extendF`
  anchor by
  `eventually_extendF_base_eq_of_eventually_forward_eq_fixedLorentz`,
  then to an explicit open anchor by
  `exists_forward_open_anchor_of_eventuallyEq_local`.

## 15. Minimal sublemma checklist for Option A

If following the totally-real route, define these helper goals explicitly:

1. `hOmega_open` and `hOmega_conn` for `Ωσ`.
2. `hDiff_holo` for
   `w ↦ extendF(σ·w) - F(w)` on `Ωσ`.
3. `exists V` with:
   - `IsOpen V` (real topology),
   - `V.Nonempty`,
   - `realEmbed(V) ⊆ Ωσ`,
   - equality on `realEmbed(V)`.
4. one call to the project identity theorem helper.

Having these as named lemmas will make the remaining d=1 anchor theorem mostly
assembly, not monolithic proof search.

## 16. Common failure modes to avoid

1. Trying to deduce global equality from connectedness alone (missing anchor).
2. Using boundary-trace equality directly without first obtaining interior
   uniqueness data (EOW/locality bridge step skipped).
3. Mixing domains:
   proving equality on adjacent-swap overlap but concluding on full `σ`-overlap
   without a chain/globalization argument.
4. Implicitly assuming real Jost witness existence in `d=1`.

## 17. Suggested immediate coding order

1. In `PermutationFlow.lean`, keep the final 3-line assembly in
   `deferred_forward_base_perm_eq_d1_of_seedConnected`
   (`hFwd_conn`, anchor unpack, propagation call).
2. Focus proof work on
   `deferred_exists_open_zero_nhds_d1_holo`
   (with the `_hBackRoute` subgoal as a concrete local geometric target).
3. Fill helpers one by one, testing after each.
4. Keep connectivity lemmas deferred as planned; do not mix geometry closure
   with `hBase` construction.

## 18. Midpoint-orientation obstruction (d=1)

A concrete obstruction emerged for the current midpoint implication orientation.

With `swap := Equiv.swap i ⟨i.val+1, hi⟩`, choose `π := σ * swap`. Then
`π * swap = σ`, so on a prepared domain (`Γ·(σ·w) ∈ FT`) the antecedent

- `A(w) := Γ·((π*swap)·w) ∈ FT`

is automatically true for all `w`.

But the consequent

- `B(w) := Γ·(π·w) ∈ FT = Γ·((σ*swap)·w) ∈ FT`

is equivalent (via Lorentz/permutation commutation) to
`swap(Γ·(σ·w)) ∈ FT`. In `d=1`, adjacent swap reverses the relevant forward-time
ordering at that adjacent slot, so from `Γ·(σ·w) ∈ FT` one gets `¬B(w)`.

So this branch forces `A(w) ∧ ¬B(w)` on the prepared neighborhood. This means
the current fixed-step closure-separation target around the anchor cannot hold
in that branch, and explains persistent failure of the remaining third sorry
under midpoint-style attacks.

Operational consequence:

the d=1 bridge should pivot from midpoint transport to a direct overlap-domain
analytic continuation/gluing statement on `D_σ := ET ∩ σ^{-1}(ET)`.

## 0e. Update (2026-03-01, normalized third blocker)

The third deferred theorem has been normalized to the core local equality form:

- `deferred_eventually_forward_eq_nhds_d1_holo`.

`deferred_eventually_zero_nhds_d1_holo` is now a proved wrapper converting
that equality into `g=0`.

This keeps the blocker mathematically identical while making the pending input
cleaner for further attacks.

## 0f. Update (2026-03-01, local propagation theorem proved)

The prior third blocker
`deferred_eventually_forward_eq_nhds_d1_holo` is now proved.

It is reduced to a connected-ball identity-theorem argument:

- `D := ball(w0, ε) ⊆ U` (open, connected),
- `h(w) := F(Γ·(σ·w)) - F(w)` holomorphic on `D`,
- real-open anchor `V` in `D` with `h(realEmbed x)=0`,
- `identity_theorem_totally_real_product` gives `h=0` on `D`.

Accordingly, the singular d=1 local blocker is now the anchor extraction theorem
`deferred_exists_real_open_anchor_eq_d1_on_ball`.

## 0g. Erratum (2026-03-01, authoritative current state)

The "local propagation theorem proved" section above is from a reverted branch.
Current active third blocker is again:

- `deferred_eventually_forward_eq_nhds_d1_holo`.

## 0h. EOW domain-mismatch note (current obstacle)

A direct EOW transfer for the blocker would compare:

- `f1(w) = F(w)` on `FT`,
- `f2(w) = F(Γ·(σ·w))` on `{w | Γ·(σ·w) ∈ FT}`.

The current formal EOW infrastructure is adjacent-swap oriented and does not
directly provide this mixed `(Γ,σ)` two-domain gluing theorem. So "EOW should
be enough" is mathematically plausible but not yet available in the exact
formal shape needed by `deferred_eventually_forward_eq_nhds_d1_holo`.

## 0i. Update (2026-03-01, slice wrapper installed)

`PermutationFlow.lean` now factors the blocker through a slice continuation
wrapper:

- `forward_eq_of_slice_anchor_d1`
- `eventually_forward_eq_nhds_of_eventually_slice_anchor_d1`.

Therefore the remaining third sorry has a sharply isolated statement:
eventual local existence of a slice anchor carrying the equality
`F(Λ₀·(σ·w)) = F(w)` near the prepared anchor.
