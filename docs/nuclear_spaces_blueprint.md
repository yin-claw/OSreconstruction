# Nuclear Spaces Blueprint

Purpose: this note is the implementation blueprint for the nuclear-space and
Bochner-Minlos packages that feed the Wightman kernel theorem and the Euclidean
measure side.

Supervision correction (`2026-04-15 16:05 UTC`): the nuclear-space layer did not require a new mathematical bridge in this bounded pass. The live shell obstruction turned out to be compiled export / import-surface visibility for the already-written shell-domain nuclearity instance in `OSReconstruction/SCV/PartialFourierSpatial.lean`; after `lake build OSReconstruction.SCV.PartialFourierSpatial`, downstream `OSToWightmanPositivity` imports can synthesize `NuclearSpace (SchwartzMap (NPointDomain d (n + m)) ℂ)` and call `finite_net_of_complex_schwartz_seminorm_of_isVonNBounded` on the actual shell domain.

Supervision correction (`2026-04-15 13:55 UTC`): the shell-local common finite-seminorm theorem has now landed, so the nuclear-space layer remains unchanged and no longer carries the active obstruction. The theorem-3 frontier has moved back to the shell-side strong-topology assembly in `OSToWightmanPositivity.lean`.

Fresh bounded theorem-3 source/doc/Lean correction on the live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T13:55:00Z`):

1. `finite_net_of_complex_schwartz_seminorm_of_isVonNBounded` remains the immediate bounded-set consumer above the producer stack;
2. the new shell-local producer theorem is now live:
   `section43_fixedTimeShellRawCLM_uniformSeminormBound_fixedTime`;
3. the old generic scalar-packaging seam on `.restrictScalars ℝ` was bypassed locally and is no longer the frontier;
4. the next honest shell theorem is therefore
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
5. the remaining blocker is the actual bounded-set / strong-topology convergence assembly, not another producer or seminorm theorem.

Supervision correction (`2026-04-15 12:45 UTC`): the bounded pass stayed above the nuclear-space layer. The producer / finite-net stack remains complete enough for theorem 3; the live obstruction is now entirely local to the shell-side Banach-Steinhaus packaging in `OSToWightmanPositivity.lean`.

Fresh bounded theorem-3 source/doc/Lean correction on the live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T12:45:00Z`):

1. `finite_net_of_complex_schwartz_seminorm_of_isVonNBounded` remains the correct bounded-set consumer above the producer stack;
2. the tested next theorem was still the shell-local common finite-seminorm bound, not a new nuclear-space lemma;
3. the attempted proof route through
   `SchwartzMap.tempered_uniform_schwartz_bound`
   failed before the finite-net theorem is even invoked, on the local scalar-packaging seam needed to reinterpret the `ℂ`-linear shell family as an `ℝ`-linear family;
4. exact missing local prerequisites at that shell insertion surface:
   a compile-clean `IsScalarTower ℝ ℂ (SchwartzNPoint d (n + m))`
   / `LinearMap.CompatibleSMul (SchwartzNPoint d (n + m)) ℂ ℝ ℂ`
   path, or an equivalent local wrapper that does real scalar restriction without reopening the route;
5. this does not lower the mathematical frontier beneath the common-seminorm theorem;
6. bounded-pass Lean verdict:
   no production Lean edit was kept.

Supervision correction (`2026-04-15 23:59 UTC`): the nuclear-space route is no longer the active shell blocker, but the direct shell-local finite-net consumer is not yet the next theorem either. One genuinely smaller shell-side theorem still has to land first in `OSToWightmanPositivity.lean`: a uniform finite-seminorm bound for `section43_fixedTimeShellRawCLM` on `0 < ε < 1`.

Fresh bounded theorem-3 source/doc/Lean correction on the live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:59:59Z`):

1. `finite_net_of_complex_schwartz_seminorm_of_isVonNBounded` remains the live complex bounded-set finite-net bridge;
2. the direct consumer above it still lacks one shell-local hypothesis package:
   a theorem giving a single finite Schwartz seminorm and constant controlling
   `section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε`
   uniformly for all `0 < ε < 1`;
3. the exact intended theorem surface is:

```lean
∃ s : Finset (ℕ × ℕ), ∃ C_sem : ℝ, 0 ≤ C_sem ∧
  ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hε_lt : ε < 1,
  ∀ φ : SchwartzNPoint d (n + m),
    ‖section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε φ‖ ≤
      C_sem *
        (s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)) φ
```

4. cleanest insertion surface:
   immediately above
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
5. exact downstream chain once it lands:
   shell uniform seminorm bound
   -> complex bounded-set finite nets
   -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   on the real-restricted shell family
   -> strong-topology basis / `eventually_nhds_zero_mapsTo`
   -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
6. why no smaller honest shell theorem exists:
   the complex finite-net bridge is already complete,
   and the pointwise limit package is already complete;
   only the common shell seminorm bound remains before the direct bounded-set application can honestly be written;
7. bounded-pass Lean verdict:
   no production Lean edit was honestly made in this pass.

Supervision correction (`2026-04-15 23:59 UTC`): the live nuclear-space route is already past the Schwartz specialization seam. `OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean` contains the compile-clean theorem `finite_net_of_schwartz_seminorm_of_isVonNBounded`, so there is no remaining honest theorem-sized bridge below that specialization on the theorem-3 route. The next real frontier is the shell-side strong-dual existence theorem `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`.

Fresh bounded theorem-3 source/doc/Lean correction on the live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:59:59Z`):

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorem remains
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. live `NuclearSpace.lean` already contains both
   `finite_net_of_nuclear_seminorm_of_q_bounded`
   and
   `finite_net_of_schwartz_seminorm_of_isVonNBounded`
   with compile-clean proofs;
4. unsupported residue was found and removed in the route description:
   the claim that the Schwartz specialization was still the next missing theorem;
5. no production Lean edit was honestly made in this bounded pass;
6. no genuinely smaller compile-clean theorem/local lemma landed in this bounded pass;
7. no smaller bridge remains beneath the specialization:
   the boundedness-to-`q`-boundedness transfer and final specialization call are already packaged in the live theorem;
8. the exact best Lean-ready theorem now required on the theorem-3 route is
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
9. minimal hypotheses for that next theorem:
   `OS : OsterwalderSchraderAxioms d`,
   `lgc : OSLinearGrowthCondition d OS`,
   `{n m : ℕ}`,
   `hm : 0 < m`,
   `t : ℝ`,
   `ht : 0 < t`;
10. codomain object:
    keep the witness existentially packaged as
    `T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ`;
11. the exact first internal proof obligation beneath that next theorem is:
    construct the strong-dual limit / convergence package for the family
    `ε ↦ section43_fixedTimeShellRawCLM ... ε`
    by combining the live bounded-set finite-net theorem,
    the shell finite-net `MapsTo` consumer,
    strong-topology neighbourhood basis facts for `ContinuousLinearMap`,
    and pointwise shell convergence/Cauchy on each ambient Schwartz test;
12. that is now the honest minimal blocker because all producer-side and Schwartz-side precompactness theorems are already complete;
13. exact downstream chain is now:
    `finite_net_of_schwartz_seminorm_of_isVonNBounded`
    -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
    -> strong-topology basis / `eventually_nhds_zero_mapsTo`
    -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
    -> `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
14. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only.

Supervision correction (`2026-04-15 23:59 UTC`): the live producer-side frontier is now above the full generic theorem. `OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean` already contains the compile-clean theorem `finite_net_of_nuclear_seminorm_of_q_bounded`, so the next honest missing result is the Schwartz specialization that turns bounded `SchwartzNPoint` sets into finite nets for a fixed finite supremum seminorm, not another theorem beneath the generic nuclear-seminorm assembly.

Fresh bounded theorem-3 source/doc/Lean correction on the live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:59:59Z`):

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorem remains
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. live `NuclearSpace.lean` already contains the full compile-clean producer stack through
   `finite_net_of_nuclear_seminorm_of_q_bounded`;
4. unsupported residue was found and removed in the route description:
   the claim that the generic nuclear-seminorm finite-net theorem itself was still the missing landing;
5. no production Lean edit was honestly made in this bounded pass;
6. no genuinely smaller compile-clean theorem/local lemma landed in this bounded pass;
7. the full generic nuclear-seminorm theorem has already lowered one more step:
   it is complete and compile-clean live;
8. the exact first internal proof obligation still beneath that theorem is:
   none on the producer seam;
   the tail, head-net, and final assembly obligations are already discharged;
9. therefore there is no below-generic blocker to classify as smaller or as a restatement;
10. the exact best Lean-ready theorem now required is the Schwartz finite-net specialization

```lean
∀ {d n m : ℕ} (s : Finset (ℕ × ℕ))
    (B : Set (SchwartzNPoint d (n + m))),
    Bornology.IsVonNBounded ℂ B ->
      ∀ ε > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
        ∀ h ∈ B, ∃ g ∈ t,
          (s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ))
            (h - g) < ε
```

11. minimal hypotheses for that next theorem:
    fixed `d n m`,
    finite `s`,
    bounded set `B : Set (SchwartzNPoint d (n + m))`,
    and `Bornology.IsVonNBounded ℂ B`;
12. codomain objects:
    no quotient codomain is needed in the immediate theorem surface;
13. the cleanest intended insertion surface is now the Schwartz-shell specialization layer,
    immediately above the generic producer theorem and immediately below the shell consumer theorem;
14. the exact first internal proof obligation beneath that next theorem is:
    obtain `q`-boundedness of `B` for the nuclear-dominating seminorm `q`
    produced by nuclear dominance, then invoke the already-landed generic theorem;
15. that new obligation is genuinely smaller than the former producer theorem because it is only
    boundedness transfer plus specialization, not a new truncation/assembly proof;
16. exact downstream chain is now:
    Schwartz finite-net theorem
    -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
    -> strong-topology basis / `eventually_nhds_zero_mapsTo`
    -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
    -> `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
17. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only.

Supervision correction (`2026-04-15 11:08 UTC`): the live producer-side chain has advanced one honest theorem surface beyond the stale docs verdict. `OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean` now contains the compile-clean local theorem `finite_net_of_nuclear_head_tail`, which is the exact direct head-plus-tail assembly theorem beneath the full generic nuclear-seminorm finite-net / precompactness theorem. The next producer seam is therefore the full generic theorem immediately above that local assembly lemma, not the question whether such an assembly theorem exists at all.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, current bounded pass, `2026-04-15T23:59:59Z`) re-checked
whether the generic nuclear-seminorm finite-net theorem itself honestly lowers
one theorem-sized step.

Verdict:

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorem remains
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. `NuclearSpace.lean` still already contains
   `uniform_nuclear_tail_lt_of_q_bounded`,
   `finite_coordinate_image_totallyBounded_of_q_bounded`,
   and
   `finite_weighted_coordinate_net_of_q_bounded`
   with compile-clean proofs;
4. `lake env lean OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean`
   exited `0`;
   only the pre-existing unrelated theorem-level `sorry` warnings remained at
   `gauge_dominates_on_subspace_of_convex_nhd`
   and
   `product_seminorm_dominated`;
5. `lake env lean OSReconstruction/SCV/SchwartzComplete.lean`
   exited `0`;
   only pre-existing `push_neg` deprecation warnings remained;
6. unsupported residue was found in the route description:
   the claim that the generic nuclear-seminorm finite-net theorem still
   decomposes to a distinct theorem-sized local lemma was not supported by the
   live theorem statements;
7. no production Lean edit was honestly made in this bounded pass;
8. the active generic theorem does **not** presently decompose one honest step
   smaller;
9. the exact first internal proof obligation beneath it is:
   for fixed `ε > 0`,
   choose `N`,
   obtain a finite net for the truncated weighted seminorm,
   then prove smallness of `p (x - y)` by splitting the nuclear `tsum` at `N`
   and bounding the tail through
   `q (x - y) ≤ q x + q y`
   plus a finite `q`-bound on the chosen net centers;
10. that obligation is not a genuinely smaller theorem surface;
    it is the same precompactness blocker in proof form;
11. the exact best Lean-ready theorem now required is still the generic
    nuclear-seminorm finite-net theorem:

```lean
(∀ n, 0 ≤ c n) ->
Summable c ->
(∀ n x, ‖f n x‖ ≤ q x) ->
(∀ x, p x ≤ ∑' n, ‖f n x‖ * c n) ->
(∃ M > 0, ∀ x ∈ B, q x < M) ->
∀ ε > 0, ∃ t : Finset V,
  ∀ x ∈ B, ∃ y ∈ t, p (x - y) < ε
```

12. minimal hypotheses for that theorem:
    fixed seminorms `p q`,
    scalar-valued continuous linear maps `f n`,
    nonnegative summable coefficients `c`,
    the nuclear-dominance inequality for `p`,
    and `q`-boundedness of `B`;
13. codomain objects:
    no quotient is needed;
    internally only a finite scalar-coordinate product and the scalar tail
    function are used;
14. the cleanest intended insertion surface is
    `OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean`,
    immediately below
    `finite_weighted_coordinate_net_of_q_bounded`;
15. exact downstream chain is:
    generic nuclear-seminorm finite-net theorem
    -> Schwartz finite-net theorem
    -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
    -> strong-topology basis / `eventually_nhds_zero_mapsTo`
    -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
    -> `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
16. source-backed ingredients:
    OS II Theorem `4.3`,
    formulas `(5.2)` `(5.3)` `(5.4)`,
    Section `V.2`, formulas `(5.20)` `(5.21)`, Lemma `5.2`,
    witness existence / pointwise convergence,
    shell finite-seminorm control,
    and local nuclear-dominance packaging;
17. already-landed new ingredients:
    the assembled uniform nuclear-tail truncation lemma,
    finite-coordinate-image total boundedness,
    and the finite-family weighted-coordinate net theorem;
18. genuinely new ingredients now required:
    only the full generic nuclear-seminorm finite-net theorem,
    then the Schwartz specialization;
19. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, current bounded pass, `2026-04-15T23:59:59Z`) re-checked the
generic nuclear-seminorm finite-net theorem against the current finite-family
theorem interface.

Verdict:

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorem remains
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. `NuclearSpace.lean` still contains
   `uniform_nuclear_tail_lt_of_q_bounded`,
   `finite_coordinate_image_totallyBounded_of_q_bounded`,
   and
   `finite_weighted_coordinate_net_of_q_bounded`
   with compile-clean proofs;
4. `lake env lean OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean`
   exited `0`;
   only the pre-existing unrelated theorem-level `sorry` warnings remained at
   `gauge_dominates_on_subspace_of_convex_nhd`
   and
   `product_seminorm_dominated`;
5. unsupported residue was found in the decomposition notes:
   the smaller-candidate description treated
   `finite_weighted_coordinate_net_of_q_bounded`
   as if it already exposed net centres in `B`;
   the current theorem statement does not record that information;
6. no production Lean edit was honestly made in this bounded pass;
7. the generic nuclear-seminorm finite-net theorem still **does** decompose one
   honest step smaller in theorem shape;
8. the exact first internal proof obligation beneath it is:
   combine a truncation index `N`,
   a finite head net whose centres are explicitly in `B`,
   and a uniform tail estimate on differences `x - y` with `x, y ∈ B`,
   then split the nuclear series with
   `Summable.sum_add_tsum_nat_add`
   and conclude from
   `p z ≤ ∑' n, ‖f n z‖ * c n`;
9. that obligation is genuinely smaller as a theorem shape, but not yet an
   honest black-box consumer of the current finite-family theorem surface,
   because the present theorem drops the representative-in-`B` witness needed
   for the tail-on-differences bound;
10. therefore no genuinely smaller compile-clean theorem/local lemma honestly
    landed in this pass;
11. the exact best Lean-ready theorem now required is still the full generic
    nuclear-seminorm finite-net theorem in `NuclearSpace.lean`;
12. the smallest honest local statement below it is the head-plus-tail
    assembly theorem:

```lean
∀ ε_head ε_tail > 0, ∀ N : ℕ,
  (∃ t : Finset V, (∀ y ∈ t, y ∈ B) ∧
    ∀ x ∈ B, ∃ y ∈ t, ∑ i : Fin N, ‖f i (x - y)‖ * c i < ε_head) ->
  (∀ x ∈ B, ∀ y ∈ B,
    ∑' n, ‖f (n + N) (x - y)‖ * c (n + N) < ε_tail) ->
  ∃ t : Finset V, ∀ x ∈ B, ∃ y ∈ t, p (x - y) < ε_head + ε_tail
```

13. minimal hypotheses for that local theorem:
    fixed seminorm `p`,
    scalar-valued continuous linear maps `f n`,
    coefficients `c`,
    the nuclear-dominance inequality for `p`,
    one finite head net with centres in `B`,
    and one uniform tail estimate on differences of points of `B`;
14. codomain objects:
    no quotient is needed;
    internally only a finite head-coordinate product `Fin N → ℝ`
    and the scalar tail series are used;
15. the cleanest intended insertion surface remains
    `OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean`,
    immediately below
    `finite_weighted_coordinate_net_of_q_bounded`,
    but the finite-family interface must first retain the representative-in-`B`
    data or that data must be rederived locally in the generic proof;
16. exact downstream chain is:
    generic nuclear-seminorm finite-net theorem
    -> Schwartz finite-net theorem
    -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
    -> strong-topology basis / `eventually_nhds_zero_mapsTo`
    -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
    -> `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
17. source-backed ingredients:
    OS II Theorem `4.3`,
    formulas `(5.2)` `(5.3)` `(5.4)`,
    Section `V.2`, formulas `(5.20)` `(5.21)`, Lemma `5.2`,
    witness existence / pointwise convergence,
    shell finite-seminorm control,
    and strong-topology bounded-set convergence targets;
18. already-landed new ingredients:
    the assembled uniform nuclear-tail truncation lemma,
    finite-coordinate-image total boundedness,
    and the finite-family weighted-coordinate net theorem;
19. genuinely new ingredients now required:
    the difference-tail plus head-net assembly into the generic
    nuclear-seminorm finite-net theorem,
    then the Schwartz specialization;
20. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only.

## 0. Theorem-3 route status

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, current bounded pass, `2026-04-15T23:59:59Z`) re-checked
whether `finite_weighted_coordinate_net_of_q_bounded` is still unfinished.

Verdict:

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorem remains
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. `NuclearSpace.lean` already contains
   `uniform_nuclear_tail_lt_of_q_bounded`,
   `finite_coordinate_image_totallyBounded_of_q_bounded`,
   and
   `finite_weighted_coordinate_net_of_q_bounded`
   with compile-clean proofs;
4. `lake env lean OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean`
   exited `0`;
   only the pre-existing unrelated theorem-level `sorry` warnings remained at
   `gauge_dominates_on_subspace_of_convex_nhd`
   and
   `product_seminorm_dominated`;
5. unsupported residue was found in the route description:
   the claim that
   `finite_weighted_coordinate_net_of_q_bounded`
   was still the active unfinished producer surface was not supported by live
   Lean;
   that residue is removed here;
6. no production Lean edit was honestly made in this bounded pass;
7. the finite-family scalar-coordinate theorem still **does** decompose one
   honest step smaller;
8. the exact first internal proof obligation beneath it is:
   given a finite `δ`-net in the coordinate image
   `coord '' B ⊆ (ι → ℝ)`,
   choose representatives in `B` and convert
   coordinatewise `δ`-closeness into
   `∑ i, ‖g i (x - y)‖ * a i < ε`;
9. that obligation is genuinely smaller as a theorem shape, but not an active
   blocker anymore because it is already discharged inline in the live proof of
   `finite_weighted_coordinate_net_of_q_bounded`;
10. therefore the finite-family theorem is no longer the first genuinely new
    theorem surface on the route;
11. the exact best Lean-ready theorem now required is the generic
    nuclear-seminorm finite-net theorem:

```lean
(∀ n, 0 ≤ c n) ->
Summable c ->
(∀ n x, ‖f n x‖ ≤ q x) ->
(∀ x, p x ≤ ∑' n, ‖f n x‖ * c n) ->
(∃ M > 0, ∀ x ∈ B, q x < M) ->
∀ ε > 0, ∃ t : Finset V,
  ∀ x ∈ B, ∃ y ∈ t, p (x - y) < ε
```

12. minimal hypotheses for that theorem:
    fixed seminorms `p q`,
    scalar-valued continuous linear maps `f n`,
    nonnegative summable coefficients `c`,
    the nuclear-dominance inequality for `p`,
    and `q`-boundedness of `B`;
13. codomain objects:
    no quotient is needed;
    internally only a finite scalar-coordinate product is used;
14. the cleanest intended insertion surface is
    `OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean`,
    immediately below
    `finite_weighted_coordinate_net_of_q_bounded`;
15. exact downstream chain is:
    generic nuclear-seminorm finite-net theorem
    -> Schwartz finite-net theorem
    -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
    -> strong-topology basis / `eventually_nhds_zero_mapsTo`
    -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
    -> `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
16. source-backed ingredients:
    OS II Theorem `4.3`,
    formulas `(5.2)` `(5.3)` `(5.4)`,
    Section `V.2`, formulas `(5.20)` `(5.21)`, Lemma `5.2`,
    witness existence / pointwise convergence,
    shell finite-seminorm control,
    and local nuclear-dominance packaging;
17. already-landed new ingredients:
    the assembled uniform nuclear-tail truncation lemma,
    finite-coordinate-image total boundedness,
    and the finite-family weighted-coordinate net theorem;
18. genuinely new ingredients now required:
    the generic nuclear-seminorm finite-net theorem,
    then the Schwartz specialization;
19. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, current bounded pass, `2026-04-15T23:59:59Z`) checked the
finite-family scalar-coordinate theorem source-first against live Lean.

Verdict:

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorem remains
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. `NuclearSpace.lean` already contains all three internal ingredients now:
   `uniform_nuclear_tail_lt_of_q_bounded`,
   `finite_coordinate_image_totallyBounded_of_q_bounded`,
   and
   `finite_weighted_coordinate_net_of_q_bounded`;
4. `lake env lean OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean`
   exited `0`;
   only the pre-existing unrelated theorem-level `sorry` warnings remained at
   `gauge_dominates_on_subspace_of_convex_nhd`
   and
   `product_seminorm_dominated`;
5. no production Lean edit was honestly made in this bounded pass;
6. the finite-family scalar-coordinate theorem **does** decompose one honest
   step smaller;
7. the exact first internal proof obligation beneath it is:
   given a finite `δ`-net in the coordinate image
   `coord '' B ⊆ (ι → ℝ)`,
   pull that net back to a finite subset of `B` and convert
   coordinatewise `δ`-closeness into
   `∑ i, ‖g i (x - y)‖ * a i < ε`;
8. that obligation is genuinely smaller as a theorem shape, but not an active
   blocker anymore because it is already discharged inline in the live proof of
   `finite_weighted_coordinate_net_of_q_bounded`;
9. therefore the finite-family theorem is no longer the first genuinely new
   theorem surface on the route;
10. the exact best Lean-ready theorem now required is the generic
    nuclear-seminorm finite-net theorem:

```lean
(∀ n, 0 ≤ c n) ->
Summable c ->
(∀ n x, ‖f n x‖ ≤ q x) ->
(∀ x, p x ≤ ∑' n, ‖f n x‖ * c n) ->
(∃ M > 0, ∀ x ∈ B, q x < M) ->
∀ ε > 0, ∃ t : Finset V,
  ∀ x ∈ B, ∃ y ∈ t, p (x - y) < ε
```

11. minimal hypotheses for that theorem:
    fixed seminorms `p q`,
    scalar-valued continuous linear maps `f n`,
    nonnegative summable coefficients `c`,
    the nuclear-dominance inequality for `p`,
    and `q`-boundedness of `B`;
12. codomain objects:
    no quotient is needed;
    internally only a finite scalar-coordinate product is used;
13. the cleanest intended insertion surface is now
    `OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean`,
    immediately below
    `finite_weighted_coordinate_net_of_q_bounded`;
14. exact downstream chain is:
    generic nuclear-seminorm finite-net theorem
    -> Schwartz finite-net theorem
    -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
    -> strong-topology basis / `eventually_nhds_zero_mapsTo`
    -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
    -> `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
15. source-backed ingredients:
    OS II Theorem `4.3`,
    formulas `(5.2)` `(5.3)` `(5.4)`,
    Section `V.2`, formulas `(5.20)` `(5.21)`, Lemma `5.2`,
    witness existence / pointwise convergence,
    shell finite-seminorm control,
    and local nuclear-dominance packaging;
16. already-landed new ingredients:
    the assembled uniform nuclear-tail truncation lemma,
    finite-coordinate-image total boundedness,
    and the finite-family weighted-coordinate net theorem;
17. genuinely new ingredients now required:
    the generic nuclear-seminorm finite-net theorem,
    then the Schwartz specialization;
18. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only;
19. unsupported residue verdict:
    none found and none removed.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, current bounded pass, `2026-04-15T23:59:00Z`) checked whether
the uniform nuclear-tail truncation lemma itself still lowers one honest step.

Verdict:

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorem remains
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. no production Lean edit was honestly made in this bounded pass;
4. the smaller scalar-tail ingredients are already present compile-clean in
   `OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean` as
   `nuclear_tail_le_of_q_bounded`
   and
   `mul_tsum_nat_add_lt_of_summable_nonneg`;
5. therefore the uniform nuclear-tail truncation lemma lowers one step smaller
   only to already-landed infrastructure; the first genuinely new theorem
   surface is now the assembled uniform tail lemma itself;
6. the exact first new internal proof obligation remains:

```lean
(∃ M > 0, ∀ x ∈ B, q x < M) ->
(∀ n, 0 ≤ c n) ->
Summable c ->
(∀ n x, ‖f n x‖ ≤ q x) ->
∀ ε > 0, ∃ N : ℕ,
  ∀ x ∈ B, ∑' n, ‖f (n + N) x‖ * c (n + N) < ε
```

7. the already-landed strictly smaller pieces are:
   pointwise tail domination on `B`
   and
   scalar smallness of `M * ∑' n, c (n + N)`;
8. no further honest smaller new theorem remains beneath them, because the next
   proof step is exactly to assemble those two ingredients into the uniform
   statement above;
9. the exact next obligation after the uniform tail lemma stays:
   a finite-family scalar-coordinate finite-net theorem for seminorms
   `x ↦ ∑ i ∈ F, ‖g i x‖ * a i`
   on `q`-bounded sets;
10. the full generic theorem is then assembled from:
    uniform tail truncation
    + finite-family coordinate nets
    + the nuclear-dominance inequality for `p`;
11. minimal hypotheses for the first genuinely new theorem:
    fixed seminorm `q`,
    scalar-valued continuous linear maps `f n`,
    nonnegative summable `c`,
    and `q`-boundedness of `B`;
12. codomain objects:
    none for the uniform tail lemma;
    the later finite-family theorem still uses only a finite scalar-coordinate
    product, not a seminorm quotient;
13. the cleanest intended insertion surface remains
    `OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean`,
    immediately after the already-landed scalar-tail helper block;
14. exact downstream chain is:
    uniform nuclear-tail truncation
    -> finite-family scalar-coordinate net theorem
    -> generic nuclear-seminorm precompactness
    -> Schwartz finite-net theorem
    -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
    -> strong-topology basis / `eventually_nhds_zero_mapsTo`
    -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
    -> `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
15. source-backed ingredients:
    OS II Theorem `4.3`,
    formulas `(5.2)` `(5.3)` `(5.4)`,
    Section `V.2`, formulas `(5.20)` `(5.21)`, Lemma `5.2`,
    witness existence / pointwise convergence,
    shell finite-seminorm control,
    `WithSeminorms.isVonNBounded_iff_seminorm_bounded`,
    and local nuclear-dominance packaging;
16. genuinely new ingredients now required:
    the assembled uniform nuclear-tail truncation lemma,
    the finite-family scalar-coordinate net theorem,
    then the full generic nuclear-seminorm precompactness theorem;
17. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only;
18. unsupported residue verdict:
    none found and none removed.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, current bounded pass, `2026-04-15T23:30:00Z`) tested whether
the generic nuclear-seminorm precompactness theorem itself lowers one honest
step further.

Verdict:

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorem remains
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. no production Lean edit was honestly made in this bounded pass;
4. the generic nuclear-seminorm precompactness theorem **does** decompose one
   theorem-sized step smaller;
5. the exact first internal proof obligation beneath it is the uniform
   nuclear-tail truncation lemma on a `q`-bounded set:

```lean
(∃ M > 0, ∀ x ∈ B, q x < M) ->
(∀ n, 0 ≤ c n) ->
Summable c ->
(∀ n x, ‖f n x‖ ≤ q x) ->
∀ ε > 0, ∃ N : ℕ,
  ∀ x ∈ B, ∑' n, ‖f (n + N) x‖ * c (n + N) < ε
```

6. this is genuinely smaller than the full precompactness theorem because it
   only handles the uniform tail estimate and leaves the finite-dimensional
   net construction untouched;
7. the exact next internal obligation after the tail lemma is a finite-family
   scalar-coordinate finite-net theorem for seminorms
   `x ↦ ∑ i ∈ F, ‖g i x‖ * a i`
   on `q`-bounded sets;
8. the full generic theorem is then assembled from:
   tail truncation
   + finite-family coordinate nets
   + the nuclear-dominance inequality for `p`;
9. minimal hypotheses for the first new lemma:
   fixed seminorm `q`,
   scalar-valued continuous linear maps `f n`,
   nonnegative summable `c`,
   and `q`-boundedness of `B`;
10. codomain objects:
    none for the tail lemma;
    the later finite-family theorem uses only a finite scalar-coordinate
    product, not a seminorm quotient;
11. the cleanest intended insertion surface remains
    `OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean`;
12. exact downstream chain is now:
    uniform nuclear-tail truncation
    -> finite-family scalar-coordinate net theorem
    -> generic nuclear-seminorm precompactness
    -> Schwartz finite-net theorem
    -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
    -> strong-topology basis / `eventually_nhds_zero_mapsTo`
    -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
    -> `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
13. source-backed ingredients:
    OS II Theorem `4.3`,
    formulas `(5.2)` `(5.3)` `(5.4)`,
    Section `V.2`, formulas `(5.20)` `(5.21)`, Lemma `5.2`,
    witness existence / pointwise convergence,
    shell finite-seminorm control,
    `WithSeminorms.isVonNBounded_iff_seminorm_bounded`,
    and local nuclear-dominance packaging;
14. genuinely new ingredients now required:
    uniform nuclear-tail truncation,
    finite-family scalar-coordinate nets,
    then the full generic nuclear-seminorm precompactness theorem;
15. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only;
16. unsupported residue verdict:
    none found and none removed.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, current bounded pass, `2026-04-15T20:30:00Z`) refined the
producer seam using the existing nuclear and `WithSeminorms` infrastructure.

Verdict:

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorem remains
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. no production Lean edit was honestly made in this bounded pass;
4. the old Montel / compact-closure candidate is no longer the nearest honest
   internal seam, because
   `WithSeminorms.isVonNBounded_iff_seminorm_bounded`
   already gives boundedness of a Schwartz bounded set in any fixed continuous
   seminorm `q`;
5. the exact first internal proof obligation beneath the shell producer theorem
   is now the generic nuclear-space theorem:

```lean
q`-bounded B
  + nuclear decomposition of p dominated by q
  -> finite p-ε nets on B
```

   for one fixed continuous seminorm `p`;
6. this is genuinely smaller than the full Schwartz theorem because it removes
   the Schwartz-specific bornology step and isolates the new mathematics in a
   reusable nuclear-space package;
7. the exact best Lean-ready statement to target next is a theorem in
   `NuclearSpace.lean` asserting:

```lean
Continuous p ->
Continuous q ->
(∃ (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ),
  (∀ n, 0 ≤ c n) ∧
  Summable c ∧
  (∀ n x, ‖f n x‖ ≤ q x) ∧
  (∀ x, p x ≤ ∑' n, ‖f n x‖ * c n)) ->
(∃ M > 0, ∀ x ∈ B, q x < M) ->
∀ ε > 0, ∃ t : Finset E, ∀ x ∈ B, ∃ y ∈ t, p (x - y) < ε
```

8. minimal hypotheses:
   fixed `p q`,
   continuity of both seminorms,
   nuclear decomposition data for `p`,
   and `q`-boundedness of `B`;
9. codomain objects:
   no quotient or pseudometric codomain is needed at this first landing;
   the proof should run through finitely many scalar coordinate functionals and
   finite-dimensional compactness there;
10. no smaller reusable ingredient is currently known beneath this generic
    theorem that is both compile-clean and immediately consumable by the shell
    route;
11. the cleanest intended insertion surface is now:
    generic theorem in `NuclearSpace.lean`,
    then Schwartz specialization in `SchwartzComplete.lean`,
    then direct use in
    `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
12. exact downstream chain:
    generic nuclear-seminorm precompactness
    -> Schwartz finite-net theorem for
       `p := s.sup (schwartzSeminormFamily ...)`
    -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
    -> strong-topology basis / `eventually_nhds_zero_mapsTo`
    -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
    -> `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
13. source-backed ingredients:
    OS II Theorem `4.3`,
    formulas `(5.2)` `(5.3)` `(5.4)`,
    Section `V.2`, formulas `(5.20)` `(5.21)`, Lemma `5.2`,
    witness existence / pointwise convergence,
    shell finite-seminorm control,
    and the strong-topology basis API;
14. genuinely new ingredient still required:
    generic nuclear-seminorm precompactness,
    then its Schwartz specialization;
15. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only;
16. unsupported residue verdict:
    none found and none removed.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, current bounded pass, `2026-04-15T16:00:00Z`) re-checked the
nuclear/Montel infrastructure only to pin the exact shell producer theorem, not
to change route.

Verdict:

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorem remains
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. no production Lean edit was honestly made in this bounded pass;
4. the exact best producer theorem required at the shell seam is the direct
   finite-net statement

```lean
Bornology.IsVonNBounded ℂ B ->
  ∀ ε > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
    ∀ h ∈ B, ∃ g ∈ t, p (h - g) < ε
```

   for
   `p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`;
5. the quotient-language form

```lean
Bornology.IsVonNBounded ℂ B ->
  TotallyBounded ((q_p) '' B)
```

   is mathematically equivalent but not the cleanest first landing because the
   live shell consumer already expects `hnet` rather than quotient data;
6. minimal hypotheses remain only:
   fixed finite `s`,
   fixed `d n m`,
   set `B : Set (SchwartzNPoint d (n + m))`,
   and boundedness `Bornology.IsVonNBounded ℂ B`;
7. the exact first internal proof obligation beneath that theorem, if one
   insists on a genuinely smaller theorem-sized step, has not surfaced;
   every honest reformulation is still the same fixed-seminorm precompactness
   blocker;
8. therefore no smaller reusable ingredient is currently known beneath it that
   is both compile-clean and immediately consumable by the shell route;
9. the Montel / compact-closure lane is stronger rather than smaller because
   its first missing statement is

```lean
Bornology.IsVonNBounded ℂ B -> IsCompact (closure B)
```

   which is a full Heine-Borel theorem for Schwartz space;
10. the cleanest intended insertion surface remains:
    producer theorem in `SchwartzComplete.lean` or a compactness companion file,
    then direct specialization inside
    `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
11. exact downstream chain:
    producer theorem
    -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
    -> strong-topology basis / `eventually_nhds_zero_mapsTo`
    -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
    -> `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
12. source-backed ingredients:
    OS II Theorem `4.3`,
    formulas `(5.2)` `(5.3)` `(5.4)`,
    Section `V.2`, formulas `(5.20)` `(5.21)`, Lemma `5.2`,
    witness existence / pointwise convergence,
    and the strong-topology basis API;
13. genuinely new ingredient still required:
    bounded-set finite `p`-nets / fixed-seminorm precompactness for Schwartz
    sets;
14. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only;
15. unsupported residue verdict:
    none found and none removed.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, current bounded pass, `2026-04-15T12:00:00Z`) tested whether
the repo's existing nuclear/Montel lane already yields the fixed-seminorm
producer theorem by

`bounded B`
-> `bounded (closure B)`
-> `compact (closure B)`
-> compact image in the `p`-quotient
-> total boundedness / finite `p`-nets.

Verdict:

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorems remain
   `SchwartzMap.tempered_tendstoUniformlyOn_of_finite_seminorm_net`
   and
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. no production Lean edit was honestly made in this bounded pass;
4. the tested route fails with current infrastructure;
5. the closure step is genuinely available:
   mathlib provides `Bornology.IsVonNBounded.closure`;
6. the exact first missing proof obligation on that route is a Schwartz-space
   Montel / compact-closure theorem:

```lean
Bornology.IsVonNBounded ℂ B -> IsCompact (closure B)
```

   for `B : Set (SchwartzNPoint d (n + m))`;
7. that obligation is not an honest smaller theorem below the producer seam;
   it is stronger than the actual fixed-seminorm producer theorem we need;
8. the exact best producer theorem still required is:

```lean
Bornology.IsVonNBounded ℂ B ->
  ∀ ε > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
    ∀ h ∈ B, ∃ g ∈ t, p (h - g) < ε
```

   equivalently

```lean
Bornology.IsVonNBounded ℂ B ->
  TotallyBounded ((q_p) '' B)
```

   for the fixed finite controlling seminorm
   `p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`;
9. even if compact closure were available, the route would still require a
   continuous seminorm quotient / pseudometric map `q_p` with enough API to
   read compact image as finite `p`-nets;
   this was not found in the inspected infrastructure, but it is not the first
   blocker on the tested route;
10. the cleanest intended insertion surface remains:
    producer theorem in `SchwartzComplete.lean` or a compactness companion file,
    then direct specialization inside
    `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
11. exact downstream chain:
    producer theorem
    -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
    -> strong-topology basis / `eventually_nhds_zero_mapsTo`
    -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
12. source-backed ingredients:
    OS II Theorem `4.3`,
    formulas `(5.2)` `(5.3)` `(5.4)`,
    Section `V.2`, formulas `(5.20)` `(5.21)`, Lemma `5.2`,
    witness existence / pointwise convergence,
    and the strong-topology basis API;
13. genuinely new ingredient still required:
    the fixed-seminorm bounded-set finite-net / quotient-total-boundedness
    theorem;
14. stronger-than-needed and absent on the failed tested route:
    a Schwartz-space Montel / compact-closure theorem;
15. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only;
16. unsupported residue verdict:
    none found and none removed.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, current bounded pass, `2026-04-15T00:00:00Z`) checked whether
the repo's nuclear/Montel lane now lowers the producer compactness seam by one
honest theorem-sized step.

Verdict:

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the compile-clean shell-facing consumer theorems remain
   `SchwartzMap.tempered_tendstoUniformlyOn_of_finite_seminorm_net`
   and
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. no production Lean edit was honestly made in this bounded pass;
4. the exact best producer theorem still required is:

```lean
Bornology.IsVonNBounded ℂ B ->
  ∀ ε > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
    ∀ h ∈ B, ∃ g ∈ t, p (h - g) < ε
```

   equivalently

```lean
Bornology.IsVonNBounded ℂ B ->
  TotallyBounded ((q_p) '' B)
```

   for the fixed finite controlling seminorm
   `p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`;
5. this does not truly lower to a smaller reusable ingredient:
   every honest reformulation is the same blocker in fixed-seminorm
   finite-net / quotient-total-boundedness language;
6. the exact first missing proof obligation is still:
   bounded Schwartz sets admit finite `p`-nets for that fixed seminorm `p`;
7. the cleanest intended insertion surface remains:
   producer theorem in `SchwartzComplete.lean` or a compactness companion file,
   then direct specialization inside
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
8. exact downstream chain:
   producer theorem
   -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   -> strong-topology basis / `eventually_nhds_zero_mapsTo`
   -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
9. source-backed ingredients:
   OS II Theorem `4.3`,
   formulas `(5.2)` `(5.3)` `(5.4)`,
   Section `V.2`, formulas `(5.20)` `(5.21)`, Lemma `5.2`,
   witness existence / pointwise convergence,
   and the strong-topology basis API;
10. genuinely new ingredient:
    the fixed-seminorm bounded-set finite-net / quotient-total-boundedness
    theorem;
11. why the nuclear/Montel lane does not yet lower the blocker:
    current repo/mathlib infrastructure gives seminorm domination, nuclearity,
    and consequences of already-known total boundedness or compactness, but not
    the missing boundedness `->` fixed-seminorm total boundedness step;
12. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction remains wrapper drift only;
13. unsupported residue verdict:
    none found and none removed.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, current bounded pass) re-checked the exact shell-facing
consumer status after the new finite-net uniformization theorem.

Verdict:

1. `section43_fixedTimeShellRawCLM` is still immediately followed by
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, and the only live
   theorem-level `sorry`s on this route remain
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
   and
   `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
2. the exact shell-facing consumer theorem now available compile-clean is
   `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   in `OSReconstruction/SCV/SchwartzComplete.lean`;
3. its exact role is:
   finite `p`-nets on `B`
   +
   common `p`-control
   +
   pointwise convergence
   +
   a target zero-neighbourhood `U`
   imply eventual bounded-set `MapsTo`;
4. minimal hypotheses are only:
   a seminorm `p`,
   a constant `C ≥ 0`,
   a filter `l`,
   a bounded-set candidate `B`,
   codomain any normed real vector space `G`,
   the eventual bound,
   pointwise convergence,
   and finite `p`-nets on `B`;
5. this theorem genuinely sits below the producer theorem because it assumes
   `hnet` instead of proving it;
6. the exact producer theorem still missing is unchanged:

```lean
Bornology.IsVonNBounded ℂ B ->
  ∀ ε > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
    ∀ φ ∈ B, ∃ ψ ∈ t, p (φ - ψ) < ε
```

   equivalently

```lean
Bornology.IsVonNBounded ℂ B ->
  TotallyBounded ((q_p) '' B)
```

   for the fixed finite controlling seminorm `p`;
7. clean insertion surface:
   no further abstract consumer theorem is needed;
   the next insertion remains inside
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
8. exact downstream chain is now:
   packaged witness `T_t`
   -> common finite controlling seminorm `p`
   -> producer finite-net theorem
   -> `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
   -> strong-topology basis / `eventually_nhds_zero_mapsTo`
   -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
9. source-backed ingredients:
   paper Section `V`, Theorem `4.3`, formulas `(5.2)` `(5.3)` `(5.4)`,
   formulas `(5.20)` `(5.21)`, Lemma `5.2`,
   witness existence / pointwise convergence,
   and mathlib strong-topology basis lemmas;
10. genuinely new ingredients:
    the finite-net uniformization theorem,
    its `MapsTo` shell-facing corollary,
    and the still-missing producer finite-net theorem;
11. witness packaging decision stays fixed:
    keep `T_t` existentially packaged;
    early extraction is still wrapper drift only.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`, `2026-04-15T08:09:20Z`) refined the decomposition below the
fixed-seminorm compactness seam.

Verdict:

1. no compile-clean abstract theorem, skeleton, local lemma, or instance was
   honestly inserted;
2. the best exact **producer** theorem statement still required is:

```lean
Bornology.IsVonNBounded ℂ B ->
  TotallyBounded ((q_p) '' B)
```

for
`p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`,
with `q_p` the canonical quotient / pseudometric map induced by `p`;
3. minimal hypotheses for that theorem remain only:
   fixed finite seminorm data `s`,
   induced seminorm `p`,
   set `B : Set (SchwartzNPoint d (n + m))`,
   and `Bornology.IsVonNBounded ℂ B`;
4. a genuinely smaller **downstream consumer** does exist beneath that
   producer theorem:
   finite `p`-nets on `B`
   +
   common `p`-Lipschitz control on the shell family
   +
   pointwise convergence
   imply `TendstoUniformlyOn`, hence bounded-set `MapsTo`;
5. however this does not reduce the producer-side blocker:
   the first exact proof obligation is still to produce those finite `p`-nets /
   quotient total boundedness for bounded Schwartz sets;
6. exact specialization path is now best viewed as:
   packaged witness `T_t`
   -> common finite controlling seminorm `p`
   -> bounded-set quotient total boundedness / finite `p`-nets
   -> finite-net uniformization consumer
   -> bounded-set `MapsTo`
   -> `TendstoUniformlyOn`
   -> strong convergence
   -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
7. source-backed ingredients:
   paper Section `V`, Theorem `4.3`, formulas `(5.2)` `(5.3)` `(5.4)`,
   boundary-value witness existence, pointwise convergence,
   `distributional_limit_of_equicontinuous`,
   `SchwartzMap.tempered_uniform_schwartz_bound`,
   and the strong-topology / Montel API surface;
8. genuinely new ingredients:
   first, the producer theorem turning bounded sets into totally bounded sets in
   the quotient induced by a fixed finite Schwartz seminorm;
   second, source-free but downstream, the finite-net uniformization consumer;
9. witness packaging decision stays fixed:
   keep `T_t` existentially packaged;
   early extraction is still wrapper drift only;
10. unsupported residue verdict:
    none found and none removed.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`) re-checked whether the exact fixed-seminorm total-boundedness
surface now honestly lands one theorem statement or skeleton below the shell
bounded-set seam.

Verdict:

1. no compile-clean abstract theorem, skeleton, local lemma, or instance was
   honestly inserted;
2. the best exact abstract theorem statement surface remains:

```lean
Bornology.IsVonNBounded ℂ B ->
  TotallyBounded ((q_p) '' B)
```

for
`p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`,
equivalently bounded sets admit finite `p`-`ε` nets;
3. that statement is not a genuinely smaller theorem than the shell bounded-set
   `MapsTo` upgrade;
   it is the same compactness step rewritten in quotient / pseudometric
   language;
4. first exact proof obligation beneath that theorem surface:
   prove bounded subsets of Schwartz space are totally bounded in the quotient
   induced by the fixed controlling seminorm `p`;
5. why that is not smaller:
   once finite `p`-nets are available, the shell route gets bounded-set
   `MapsTo`, then `TendstoUniformlyOn`, then
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` immediately;
6. exact specialization path remains:
   packaged witness `T_t`
   -> common finite controlling seminorm `p`
   -> bounded-set `MapsTo`
   via finite `p`-nets / quotient total boundedness
   -> `TendstoUniformlyOn`
   -> strong convergence
   -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
7. source-backed ingredients:
   paper Section `V`, Theorem `4.3`, formulas `(5.2)` `(5.3)` `(5.4)`,
   boundary-value witness existence, pointwise convergence,
   `distributional_limit_of_equicontinuous`,
   `SchwartzMap.tempered_uniform_schwartz_bound`,
   and the strong-topology / Montel API surface;
8. genuinely new ingredient:
   the fixed-seminorm quotient-total-boundedness theorem itself;
9. witness packaging decision stays fixed:
   keep `T_t` existentially packaged;
   early extraction is still wrapper drift only;
10. unsupported residue verdict:
    none found and none removed.

Fresh bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`) re-checked whether the exact fixed-seminorm total-boundedness
surface can now be inserted as one honest compile-clean theorem in
`SchwartzComplete.lean`.

Verdict:

1. no compile-clean abstract theorem, skeleton, local lemma, or instance was
   honestly inserted;
2. the best exact abstract theorem statement surface remains:

```lean
Bornology.IsVonNBounded ℂ B ->
  TotallyBounded ((q_p) '' B)
```

for
`p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`,
equivalently bounded sets admit finite `p`-`ε` nets;
3. that statement is not a genuinely smaller theorem than the shell bounded-set
   `MapsTo` upgrade;
   it is the same compactness step rewritten in quotient / pseudometric
   language;
4. first exact proof obligation beneath that theorem surface:
   prove bounded subsets of Schwartz space are totally bounded in the quotient
   induced by the fixed controlling seminorm `p`;
5. why that is not smaller:
   once finite `p`-nets are available, the shell route gets eventual `MapsTo`,
   then `TendstoUniformlyOn`, then
   `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` immediately;
6. exact specialization path remains:
   packaged witness `T_t`
   -> common finite controlling seminorm `p`
   -> bounded-set finite `p`-nets / quotient total boundedness
   -> eventual `MapsTo`
   -> `TendstoUniformlyOn`
   -> strong convergence
   -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
7. source-backed ingredients:
   paper Section `V`, Theorem `4.3`, formulas `(5.2)` `(5.3)` `(5.4)`,
   boundary-value witness existence, pointwise convergence,
   `distributional_limit_of_equicontinuous`,
   `SchwartzMap.tempered_uniform_schwartz_bound`,
   and the strong-topology / Montel API surface;
8. genuinely new ingredient:
   the fixed-seminorm quotient-total-boundedness theorem itself;
9. witness packaging decision stays fixed:
   keep `T_t` existentially packaged;
   early extraction is still wrapper drift only;
10. unsupported residue verdict:
    none found and none removed.

Bounded theorem-3 source/doc/Lean pass on the live actual-shell route
(`2026-04-15`) checked whether the nuclear/Montel lane already contains an
honest theorem smaller than the current shell bounded-set compactness seam.

Verdict:

1. no such theorem is currently present in repo code or checked mathlib APIs;
2. the strongest abstract theorem worth naming for theorem 3 is still:

```lean
Bornology.IsVonNBounded ℂ B ->
  ∀ εp > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
    ∀ h ∈ B, ∃ g ∈ t, p (h - g) < εp
```

for
`p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`,
equivalently

```lean
Bornology.IsVonNBounded ℂ B ->
  TotallyBounded ((q_p) '' B)
```

3. that theorem is **not** genuinely smaller than the shell bounded-set
   `MapsTo` theorem; on the live route it is only the same compactness upgrade
   rewritten in quotient / pseudometric language;
4. exact specialization path for theorem 3 remains:
   packaged witness `T_t`
   -> common finite controlling seminorm `p`
   -> bounded-set finite `p`-nets / quotient total boundedness
   -> eventual `MapsTo`
   -> `TendstoUniformlyOn`
   -> strong convergence
   -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
5. source-backed ingredients:
   paper Section `V`, boundary-value witness existence, pointwise convergence,
   `distributional_limit_of_equicontinuous`,
   `SchwartzMap.tempered_uniform_schwartz_bound`,
   and the strong-topology/Montel API surface;
6. genuinely new ingredient:
   a Schwartz-specific theorem turning bounded sets into totally bounded sets in
   the quotient induced by a fixed finite Schwartz seminorm;
7. early extraction of `T_t` is still wrapper drift only, because the witness is
   already packaged by `forwardTube_boundaryValueData_of_polyGrowth` and the
   missing input is entirely the compactness upgrade;
8. first exact proof obligation still blocking even this abstract
   nuclear/Montel landing:
   neither repo nor mathlib currently supplies a Schwartz `MontelSpace`
   instance or the quoted fixed-seminorm total-boundedness theorem, and
   `OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean` still has live
   theorem-level `sorry`s at
   `gauge_dominates_on_subspace_of_convex_nhd`
   and `product_seminorm_dominated`.

It should be read together with:
- `docs/gns_pipeline_blueprint.md`,
- `docs/gns-pipeline-sorries.md`,
- `docs/r_to_e_blueprint.md`.

## 1. Live frontier surfaces

The relevant current open theorem surfaces are:

1. `subspace_seminorm_dominated` and `product_seminorm_dominated` in
   `Wightman/NuclearSpaces/NuclearSpace.lean`,
2. the Bochner-Minlos sorries in
   `Wightman/NuclearSpaces/BochnerMinlos.lean`,
3. the axioms
   `schwartz_nuclear_extension` and
   `exists_continuousMultilinear_ofSeparatelyContinuous`
   in `Wightman/WightmanAxioms.lean`.

These are not independent. They form one package:

1. nuclearity of the relevant Schwartz/Frechet spaces,
2. separately continuous multilinear maps become jointly continuous,
3. joint continuity feeds the Schwartz kernel theorem,
4. the kernel theorem feeds GNS cyclicity and Wightman packaging,
5. Bochner-Minlos feeds the measure-based Euclidean examples.

## 2. What is already available

The docs should treat the following as clean inputs:

1. `GaussianFieldBridge.lean` provides sorry-free Hermite and Gaussian
   infrastructure,
2. `ComplexSchwartz.lean` already transports nuclearity across complexification,
3. the basic `NuclearSpace` API exists and only two dominance theorems remain
   sorry-backed.

So the later implementation should not start from “what is a nuclear space?”
It should start from the two remaining dominance lemmas and the kernel-theorem
consumer interfaces.

## 3. Package A: Nuclearity infrastructure

The current explicit blockers in `NuclearSpace.lean` are:

1. `gauge_dominates_on_subspace_of_convex_nhd`,
2. `product_seminorm_dominated`.

These feed:

1. `subspace_seminorm_dominated`,
2. `subspace_nuclear`,
3. `product_nuclear`.

Documentation-standard theorem slots:

```lean
lemma gauge_dominates_on_subspace_of_convex_nhd
theorem subspace_seminorm_dominated
theorem subspace_nuclear

lemma product_coordinate_seminorm_control
theorem product_seminorm_dominated
theorem product_nuclear
```

The proof discipline should be:

1. prove subspace domination geometrically from convex neighborhoods and the
   gauge construction,
2. prove product domination from countable seminorm bookkeeping,
3. only then apply the generic nuclear-space closure lemmas already in the file.

### 3.1. Exact proof transcript for subspace domination

The later Lean file should prove `gauge_dominates_on_subspace_of_convex_nhd`
by the standard gauge argument, not by guessing constants.

Exact route:

1. let `i : S →L[ℝ] E` be the continuous inclusion,
2. for a given continuous seminorm `p` on `S`, choose a balanced convex
   neighborhood `V` of `0` in `S` such that `p x ≤ 1` on `V`,
3. use continuity of `i` at `0` to find a balanced convex neighborhood `U` in
   `E` with `i ⁻¹' U ⊆ V`,
4. define the Minkowski gauge `μ_U` on `E`,
5. show `p x ≤ μ_U (i x)` for all `x : S`,
6. package `μ_U` as the dominating ambient seminorm.

So the proof should be split as:

```lean
lemma subspace_preimage_of_convex_balanced_nhd
lemma minkowskiGauge_continuousSeminorm_of_convex_balanced_nhd
lemma seminorm_le_minkowskiGauge_on_preimage
lemma gauge_dominates_on_subspace_of_convex_nhd
theorem subspace_seminorm_dominated
```

The important point is that the constant should be `1` after the gauge choice;
the whole purpose of the Minkowski functional is to avoid a later rescaling
fight.

### 3.2. Exact proof transcript for countable-product domination

The later Lean proof of `product_seminorm_dominated` should proceed as:

1. let `p` be a continuous seminorm on `∀ i, E i`,
2. continuity of `p` at `0` gives a product neighborhood
   `∏ i, U_i` on which `p ≤ 1`,
3. by the product-topology basis, all but finitely many `U_i` are the whole
   space,
4. extract the finite support set `F`,
5. for each `i ∈ F`, replace `U_i` by a balanced convex neighborhood and form
   the corresponding coordinate gauge `q_i`,
6. prove
   `p x ≤ ∑ i in F, q_i (x i)`,
7. package the finite weighted sum as the dominating product seminorm.

The theorem-slot inventory should therefore include:

```lean
lemma continuousSeminorm_has_finite_coordinate_control
lemma product_coordinate_gauge_family
lemma product_coordinate_sum_dominates
theorem product_seminorm_dominated
```

This is the point where the countability/finiteness bookkeeping belongs. It
should not be postponed to `product_nuclear`.

## 4. Package B: Separate continuity to joint continuity

The axiom

```lean
exists_continuousMultilinear_ofSeparatelyContinuous
```

should eventually be replaced by a theorem package with exact slots:

```lean
lemma schwartz_isFrechet
lemma separatelyContinuous_multilinear_on_frechet
theorem exists_continuousMultilinear_ofSeparatelyContinuous
```

This is the Banach-Steinhaus / Frechet-space package. The docs should keep it
separate from the nuclear theorem itself.

### 4.1. Primary route and fallback route

The honest implementation choice should be:

1. **Primary route**: import the already-proved theorem from the local
   `gaussian-field` dependency and wrap it in the repo’s theorem surface,
2. **Fallback route**: prove the Frechet-space multilinear theorem locally by
   Banach-Steinhaus / barrelled-space arguments.

The primary route should be the default because the mathematical content is
already settled externally and the repo gap is mostly integration.

### 4.2. Exact proof transcript for the fallback route

If the import route is unavailable, the local proof should be organized as:

1. prove each Schwartz test space is a Frechet space,
2. prove the target scalar space is complete,
3. convert separate continuity into hypocontinuity on bounded sets,
4. apply the multilinear Banach-Steinhaus theorem on Frechet spaces,
5. package the resulting jointly continuous multilinear map.

The theorem slots should be:

```lean
lemma schwartzSpace_isFrechet
lemma separatelyContinuous_multilinear_is_hypocontinuous
lemma frechet_multilinear_banach_steinhaus
theorem exists_continuousMultilinear_ofSeparatelyContinuous
```

## 5. Package C: Schwartz kernel / nuclear theorem

The axiom

```lean
schwartz_nuclear_extension
```

is the next package and should be treated as the main direct consumer of
Packages A and B.

Documentation-standard theorem slots:

```lean
lemma schwartz_productTensor_dense
lemma schwartz_joint_space_nuclear
lemma multilinear_to_linear_kernel_candidate
lemma kernel_candidate_agrees_on_productTensor
theorem schwartz_nuclear_extension
```

This package is what later closes:

1. `wightmanDistribution_extends`,
2. `gns_cyclicity`,
3. any “product tests are dense” statements in the GNS uniqueness lane.

### 5.1. Primary route and exact consumer theorem

Again the honest primary route is:

1. import the Schwartz nuclearity instance / theorem from the local
   `gaussian-field` work,
2. derive the exact consumer theorem
   `schwartz_nuclear_extension`
   on the repo’s `SchwartzMap` / `SchwartzNPoint` surfaces,
3. immediately use that theorem to close the GNS and Wightman consumer files.

The local fallback route should only be used if the import/integration fails.

### 5.2. Exact proof transcript for the fallback route

The local proof should be decomposed as:

1. prove the algebraic product-tensor span is dense in the projective tensor
   product model of the joint Schwartz space,
2. use nuclearity to identify projective and injective tensor topologies,
3. convert the separately continuous multilinear functional into a continuous
   linear functional on the completed tensor product,
4. transport that functional to the concrete joint Schwartz space,
5. prove uniqueness by agreement on the dense product-tensor image.

So the theorem slots should be read as:

```lean
lemma schwartz_projectiveTensor_dense
lemma schwartz_projective_eq_jointSpace
lemma separatelyContinuous_to_projectiveTensor_linear
lemma projectiveTensor_linear_to_jointSpace_linear
lemma kernel_candidate_agrees_on_productTensor
theorem schwartz_nuclear_extension
```

The later implementation should not compress steps 2-4 into one opaque import
wrapper. Those are the exact places where the topology model has to match the
repo’s concrete `SchwartzMap` surface.

### 5.3. Exact intermediate extension package used by GNS consumers

The GNS and Wightman consumer files will be easier to implement if the kernel
theorem route is split into the exact “multilinear -> tensor -> joint space”
intermediate steps instead of jumping directly to
`schwartz_nuclear_extension`.

The later Lean file should therefore isolate:

```lean
lemma separatelyContinuous_multilinear_to_projectiveTensorMap
lemma projectiveTensorMap_continuous
lemma projectiveTensorMap_descends_to_jointSchwartz
lemma jointSchwartz_extension_agrees_on_productTensors
theorem schwartz_nuclear_extension
```

with the intended proof order:

1. build the algebraic multilinear-to-tensor linear map on pure tensors,
2. use separate-to-joint continuity plus nuclearity to extend it continuously
   to the completed projective tensor product,
3. identify that completed tensor product with the concrete joint Schwartz
   space,
4. transport the extension to the joint Schwartz space,
5. prove agreement on product tensors,
6. prove uniqueness from density.

That is the exact intermediate infrastructure a later `wightmanDistribution`
or `gns_cyclicity` implementation will need. The docs should no longer leave
that layer implicit.

## 6. Package D: Bochner finite-dimensional existence

The first open finite-dimensional theorem is:

```lean
private theorem bochner_tightness_and_limit
```

The later implementation should decompose it into:

1. approximate finite measures from mollified/compactly truncated data,
2. tightness,
3. weak-limit extraction,
4. characteristic-function recovery.

Documentation-standard theorem slots:

```lean
lemma bochner_approximate_measures_exist
lemma bochner_approximate_measures_tight
lemma bochner_weak_limit_exists
lemma bochner_limit_has_correct_characteristic_function
theorem bochner_tightness_and_limit
theorem bochner_existence
theorem bochner_theorem
```

### 6.1. Exact proof transcript

The later Lean file should prove the private tightness theorem by the following
literal sequence:

1. regularize the target characteristic function by compact cutoffs /
   mollification so Bochner’s classical finite-dimensional theorem applies to
   each approximant,
2. obtain a family of probability measures `μ_k` with characteristic functions
   `φ_k`,
3. prove tightness of `μ_k` from the uniform control inherited from the
   positive-definite normalized characteristic functions,
4. apply Prokhorov to obtain a weakly convergent subsequence,
5. use weak convergence plus continuity of bounded exponentials to identify the
   limit characteristic function with `φ`,
6. package the limit measure as the output of
   `bochner_tightness_and_limit`.

The theorem slots should therefore include:

```lean
lemma bochner_regularized_charfun
lemma bochner_regularized_measure_exists
lemma bochner_regularized_family_tight
lemma prokhorov_subsequence_of_tight
lemma weakLimit_charfun_eq_limit
theorem bochner_tightness_and_limit
```

## 7. Package E: Minlos projective family and uniqueness

The open Minlos-side theorems are:

1. `minlos_projective_consistency`,
2. `minlos_nuclearity_tightness`,
3. `eval_maps_generate_sigma_algebra`,
4. `eval_charfun_implies_fd_distributions`,
5. the downstream `minlos_theorem` / `minlos_unique` consumers.

The implementation order should be:

1. finite-dimensional projection measures,
2. projective consistency,
3. nuclearity-driven tightness,
4. Kolmogorov/projective extension,
5. uniqueness from evaluation-characteristic functions.

Documentation-standard theorem slots:

```lean
lemma minlos_finite_dim_projection
lemma minlos_projective_consistency
lemma minlos_nuclearity_tightness
lemma minlos_kolmogorov_extension
theorem minlos_theorem

lemma eval_maps_generate_sigma_algebra
lemma eval_charfun_implies_fd_distributions
theorem measures_eq_of_eval_charfun_eq
theorem minlos_unique
```

### 7.1. Exact proof transcript

The later Lean implementation should split Minlos into two separate chains.

Existence chain:

1. define finite-dimensional projection measures by Bochner on each finite set
   of test directions,
2. prove projective consistency under coordinate restriction,
3. use nuclearity to prove tightness / cylindrical Radon control,
4. apply the projective-extension theorem to get a measure on the dual,
5. prove its characteristic functional equals the original one.

Uniqueness chain:

1. prove evaluation maps generate the relevant sigma-algebra,
2. prove equality of characteristic functionals implies equality of every
   finite-dimensional marginal,
3. conclude equality of measures from equality on the generating cylinder
   sigma-algebra.

So the theorem slots should be read as:

```lean
lemma eval_projection_charfun
lemma projection_family_projectively_consistent
lemma nuclearity_implies_cylindrical_tightness
lemma projective_family_extension_exists
theorem minlos_theorem

lemma cylinder_sets_generate_sigma
lemma charfun_eq_implies_projection_eq
lemma measures_eq_of_projection_eq
theorem minlos_unique
```

## 8. Exact dependency graph

The later implementation should proceed in this order:

1. finish `NuclearSpace.lean` dominance lemmas,
2. replace separate-continuity axiom,
3. replace Schwartz nuclear-extension axiom,
4. close `gns_cyclicity`,
5. separately finish the Bochner finite-dimensional existence package,
6. then the Minlos projective/tightness/uniqueness package.

The docs should not present Bochner-Minlos as if it were required before the
GNS/kernel theorem. They are parallel consumers of overlapping nuclear-space
infrastructure.

## 9. Lean-style pseudocode for the kernel-theorem consumer side

```lean
theorem wightmanDistribution_extends (qft : WightmanQFT d) (n : ℕ) :
    ∃ W_n : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ,
      ∀ fs, W_n (SchwartzMap.productTensor fs) =
        qft.vacuumExpectation n fs := by
  obtain ⟨PhiCont, hPhiCont⟩ :=
    exists_continuousMultilinear_ofSeparatelyContinuous
      (d := d) (n := n) (wightman_separately_continuous qft n)
  obtain ⟨W_n, hW_n, _⟩ := schwartz_nuclear_extension (d := d) (n := n) PhiCont
  exact ⟨W_n, hW_n⟩
```

## 10. Do not do this

1. Do not mix the Frechet separate-continuity theorem with the kernel theorem.
2. Do not treat Bochner and Minlos as one undifferentiated measure theorem.
3. Do not reopen the sorry-free GaussianFieldBridge package.
4. Do not let GNS cyclicity smuggle in the nuclear theorem implicitly.

## 11. What counts as implementation-ready

This blueprint should be considered ready only when:

1. the two open `NuclearSpace.lean` dominance lemmas are isolated,
2. the two current axioms are split into theorem packages,
3. the Bochner and Minlos packages are separated into finite-dimensional,
   projective, tightness, and uniqueness layers,
4. the dependency from these packages to GNS cyclicity is explicit.

## 12. Recommended implementation order and size

The later implementation should treat these as five separate work packages:

1. `NuclearSpace.lean` domination lemmas: 180-260 lines,
2. separate-to-joint continuity import/wrapper or fallback proof:
   80-160 lines,
3. kernel-theorem consumer package:
   140-220 lines,
4. Bochner finite-dimensional existence:
   180-260 lines,
5. Minlos existence/uniqueness:
   220-320 lines.

The whole package is ready for implementation once these five items are read as
literal construction units with the stated order, not as a single “nuclear
spaces” blob.
