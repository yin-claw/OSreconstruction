Supervision correction (`2026-04-17`, ambient shell-zero supplier audit after the local-annihilation negative result):
this head note supersedes the repeated same-day seam notes immediately below.

- exact wrapper verdict:
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  is currently just a dominated-convergence wrapper over
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`,
  so the first honest supplier seam strictly beneath the ambient shell-zero
  theorem is still the coefficient-side explicit trace-data package;
- exact live consumer:
  `section43_fixedTimeShellRaw_flat_coefficient_tendsto_zero_of_localTraceData`
  is the first checked consumer beneath
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`;
- exact consumer contract:
  `DifferentiableOn`,
  `HasFourierLaplaceReprTempered`,
  an explicit local trace object `B`,
  `ContinuousOn B Uflat`,
  local ray limits to `B`,
  and separate local annihilation of `hTempered.dist`;
- exact supplier comparison:
  the positivity-side supplier still gives only local `ContinuousWithinAt` on
  a complement-side open set `Uflat`,
  and `HasFourierLaplaceReprTempered` still lacks the regular continuity fields
  that appear only on `HasFourierLaplaceReprRegular`;
- exact verdict:
  candidate **(A)**, the explicit local trace-object supplier package on
  `Uflat`, is the first honest unresolved seam;
  candidate **(B)**, a trace-to-`ContinuousWithinAt` bridge, is now only the
  older continuity-lane formulation and is downstream/historical for the live
  branch;
- exact theorem-contract gap:
  no source theorem currently constructs the explicit `B`, proves
  `ContinuousOn B Uflat`, supplies the local ray-limit package on `Uflat`, and
  packages the needed local annihilation statement
  `∀ f, tsupport f ⊆ Uflat → hTempered.dist f = 0`;
- exact packaging decision:
  for the natural trace `B₀ := fun xflat => G_t (SCV.realEmbed xflat)`, the
  sharper first theorem-sized target is
  `∀ xflat ∈ Uflat, ContinuousAt B₀ xflat`;
  because `Uflat` is already open in the live supplier package, Mathlib
  `IsOpen.continuousOn_iff` repackages this exactly as `ContinuousOn B₀ Uflat`
  for the consumer that asks for `ContinuousOn`;
- exact boundary-vs-tube obstruction:
  the generic route from the available tube-side
  `ContinuousWithinAt G_t ... (SCV.realEmbed xflat)` data to boundary-side
  `ContinuousOn B₀ Uflat` for `B₀ := fun xflat => G_t (SCV.realEmbed xflat)`
  is not available, because `SCV.realEmbed xflat` lies on the real boundary,
  not in `SCV.TubeDomain (ForwardConeFlat ...)`; this is an upstream source
  theorem gap, not a local topology-helper omission;
- exact judgment:
  the ambient shell-zero wrapper adds no new mathematical supplier surface on
  the current branch; the remaining blocker is still an upstream boundary-trace
  continuity theorem for the definitional edge trace, best stated first as the
  pointwise `ContinuousAt` contract for `B₀` on `Uflat` and only then packaged
  as `ContinuousOn B₀ Uflat`, not a further proof-doc specification gap.

Supervision correction (`2026-04-17`, bounded reread immediately above the shifted real `consecutiveDiff` gap: the first substantive consumer is the shell coefficient-limit theorem, and no Jost-only rewrite is yet honest):
this pass is docs-only.

- reread only the exact checked source around
  `consecutiveDiff_xiShift_zero_ofReal_eq_add`,
  `consecutiveDiff_xiShift_zero_ofReal_eq_of_ne`,
  the missing continuity supplier
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`,
  its transport wrappers
  `section43_fixedTimeShellRaw_pointwiseContinuity_on_section43PositiveEnergyRegion_compl`,
  `section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl`,
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`,
  the first non-wrapper consumer
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`,
  and the exact SCV local-recovery theorem surfaces
  `fourierLaplace_schwartz_integral_convergence_local_of_trace` and
  `fourierLaplace_boundary_recovery_on_open_of_tempered`;
- exact bounded result:
  no Lean theorem was added;
  the first honest consumer above the shifted-`ForwardJostSet` gap is the
  shell coefficient-limit theorem, not the transport wrappers;
  no theorem rewrite from `hy` directly to shifted-`ForwardJostSet` input is
  source-supported yet;
- source check:
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  is the first theorem above the gap whose content is larger than pure
  continuity transport;
- source check:
  the exact checked consumer-side package it should depend on, if split, is the
  local flat continuity package currently packaged by
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`;
- source check:
  the missing supplier beneath that package remains
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`;
- source check:
  the newly checked `consecutiveDiff` family pins down the missing shifted
  geometric inequalities honestly, but checked ET/Jost theorems still do not
  turn those inequalities into the boundary continuity required by the SCV
  recovery route;
- source check:
  therefore the first honest split is “consumer theorem from explicit local
  continuity package” plus “separate missing continuity supplier”, not
  “consumer theorem from shifted-`ForwardJostSet` alone”.

- reading conclusion:
  the first consumer surface above the shifted-Jost gap is
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`;
  any Lean-facing rewrite should isolate the local continuity package there,
  while keeping the shifted-`ForwardJostSet` package recorded only as a still-
  missing geometric ingredient beneath the continuity supplier.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, bounded reread immediately above the repaired pure-coordinate real `consecutiveDiff` block: the checked lower landing now sits in consecutive-difference language itself):
this pass is docs-only.

- reread only the exact checked source around
  `toDiffFlat_ofReal_apply_eq_consecutiveDiff`,
  `consecutiveDiff_xiShift_zero_ofReal_eq_update`,
  `consecutiveDiff_xiShift_zero_ofReal_eq_add`,
  `consecutiveDiff_xiShift_zero_ofReal_eq_of_ne`,
  the exact seam
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`,
  and the exact Jost/ET consumers
  `ForwardJostSet`, `forwardJostSet_subset_extendedTube`,
  `extendF_eq_boundary_value_ET_of_continuousWithinAt`;
- exact bounded result:
  no Lean theorem was added;
  no smaller checked theorem/interface below the new family was found;
  the lower landing is now the checked real `consecutiveDiff` theorem family,
  not merely `toDiffFlat_xiShift_eq_update`;
- source check:
  `toDiffFlat_ofReal_apply_eq_consecutiveDiff` already bridges the flat update
  theorem to real consecutive differences;
- source check:
  `consecutiveDiff_xiShift_zero_ofReal_eq_add` gives the updated slot
  `BHW.consecutiveDiff y j 0 + t` at
  `j := ⟨n, Nat.lt_add_of_pos_right hm⟩`;
- source check:
  `consecutiveDiff_xiShift_zero_ofReal_eq_of_ne` gives exact off-slot
  invariance for every `(i, μ) ≠ (j, 0)`;
- source check:
  the exact remaining missing geometric object is the theorem/interface or
  stronger hypothesis that upgrades those checked formulas to the full
  `ForwardJostSet` inequalities for the shifted real configuration:
  unchanged strict inequalities for `k ≠ j`, and
  `|BHW.consecutiveDiff y j 0 + t| <
    BHW.consecutiveDiff y j ⟨1, by omega⟩`
  at `k = j`;
- source check:
  the immediate geometric consumer is
  `forwardJostSet_subset_extendedTube`;
  downstream, `extendF_eq_boundary_value_ET_of_continuousWithinAt` would still
  require the present continuity seam as an extra input, so ET geometry alone
  does not close
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`.

- reading conclusion:
  the docs should now record the real consecutive-difference family as the
  current lower landing, and the remaining blocker as the full shifted-point
  `ForwardJostSet` inequality package.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, bounded reread immediately below Entry #1006: the exact lower landing is only the one-coordinate difference update for `xiShift`):
this pass reread only the exact source surfaces cited in Entry #1006: `section43PositiveEnergyRegion`, `xiShift`, `toDiffFlat_xiShift_eq_update`, `fromDiffFlat_update_eq_xiShift`, `diffCoordEquiv_apply`, `consecutiveDiff`, `ForwardJostSet`, `forwardJostSet_subset_extendedTube`, and the exact continuity seam around `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`.

Exact bounded result:

- no Lean theorem was landed on this pass;
- the lowest checked surface below the current ET/Jost fallback seam is only
  `toDiffFlat_xiShift_eq_update`;
- the missing object is therefore the explicit comparison from the weak Section
  4.3 complement hypothesis to the shifted-point consecutive-difference/Jost
  inequalities.

Exact source-first verdict:

- the complement of `section43PositiveEnergyRegion` still gives only that some
  cumulative time coordinate is negative;
- the checked `xiShift`/difference-coordinate theorems identify only which one
  consecutive difference is updated;
- `ForwardJostSet` still needs a full family of stronger spacelike inequalities;
- no checked theorem on the reread surfaces bridges those two levels.

Verification status:

- docs-only pass;
- no Lean verification command was run.

Supervision correction (`2026-04-17`, bounded reread immediately below Entry `#1006`: the missing geometry is the one-slot updated Jost inequality family, not an unspecified ET theorem):
this pass is docs-only.

- reread only the exact seam
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`,
  the exact wrapper
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`,
  the exact coordinate surfaces
  `section43PositiveEnergyRegion`, `xiShift`,
  `toDiffFlat_xiShift_eq_update`, `fromDiffFlat_update_eq_xiShift`,
  `diffCoordEquiv_apply`, `consecutiveDiff`,
  and the exact Jost/ET surfaces
  `ForwardJostSet`, `forwardJostSet_subset_extendedTube`,
  `extendF_eq_boundary_value_ET_of_continuousWithinAt`,
  `extendF_eq_boundary_value_ET`;
- exact bounded result:
  no Lean theorem was added;
  no checked smaller comparison theorem was missed, but the missing interface
  is now sharper;
- source check:
  `hy` still means only `∃ i, y i 0 < 0`;
- source check:
  `toDiffFlat_xiShift_eq_update` says only the difference-coordinate slot
  `(j, 0)` changes, with `j := ⟨n, Nat.lt_add_of_pos_right hm⟩`;
- source check:
  via the source-near comparison `diffCoordEquiv_apply` / `consecutiveDiff`,
  this means only the consecutive time difference at `k = j` changes, by `+ t`,
  while all other consecutive differences stay fixed;
- source check:
  therefore the exact missing theorem/interface/hypothesis is the full Jost
  inequality package for the shifted real configuration:
  unchanged inequalities for `k ≠ j`, and
  `|consecutiveDiff y j 0 + t| < consecutiveDiff y j ⟨1, by omega⟩`
  at the updated slot;
- source check:
  ET membership would still not by itself prove the current continuity seam,
  because the ET boundary-value theorems assume, rather than derive, the
  needed `ContinuousWithinAt`;

- reading conclusion:
  the frontier under Entry `#1006` is now precise:
  the route is blocked by missing one-slot updated Jost inequalities for the
  shifted real configuration, while the actual complement hypothesis is much
  too weak.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, bounded reread on the exact extended-tube / Jost fallback below the raw shifted-point continuity seam):
this pass is docs-only.

- reread only the exact shifted-point continuity surfaces in
  `OSToWightmanPositivity.lean`,
  the exact `xiShift` / `section43PositiveEnergyRegion` declarations,
  the exact JostPoints surfaces
  `forwardJostSet_subset_extendedTube`,
  `extendF_holomorphicOn`,
  `extendF_eq_boundary_value`,
  `extendF_eq_boundary_value_ET_of_continuousWithinAt`,
  and `extendF_eq_boundary_value_ET`,
  and the exact nearby `bvt_F` holomorphic/Lorentz/extension source objects;
- exact bounded result:
  no Lean theorem was added;
  the extended-tube route still does not land from the actual complement-side
  hypothesis;
- source check:
  the ET boundary-equality theorems do not help because they still assume the
  missing `ContinuousWithinAt`;
- source check:
  below that, the analytic continuation inputs for `bvt_F` are already checked;
- source check:
  the missing lower interface is geometric:
  no checked theorem upgrades
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  to `ForwardJostSet` or `ExtendedTube` membership for the exact shifted real
  point;
- source check:
  `section43PositiveEnergyRegion` complement only records a negative time
  coordinate, while `xiShift_mem_forwardTube_of_real` only preserves forward-
  tube interior membership.

- reading conclusion:
  the exact Jost/extended-tube fallback is blocked by missing shifted-point
  ET/Jost geometry, not by missing `bvt_F` invariance machinery;
  unless such geometry is proved or added as hypothesis, the frontier remains
  the new boundary-regularity theorem itself.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, frontier drop from the unflattened real-boundary zero seam to the raw shifted-point continuity seam):
this pass is docs-only.

- the latest source-first rereads (Entries #1001-#1002) closed off the unflattened equality itself as a lower-search target:
  there is no checked lower landing beneath
  `bvt_F OS lgc (n + m) (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 (fun k μ => (y k μ : ℂ)) (t : ℂ)) = 0`,
  and no smaller source-supported theorem/interface sits below it;
- therefore the honest implementation frontier drops one seam lower to
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`;
- next bounded question:
  whether that raw shifted-point `ContinuousWithinAt` theorem already has an
  exact checked lower landing, or whether one still smaller theorem/interface
  sits immediately beneath it.

Supervision correction (`2026-04-17`, bounded reread at the raw shifted-point continuity seam):
this pass is docs-only.

- reread only the fresh docs/chat entries from the last pass;
- reread only the exact fixed-time source surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4641](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4641)
  and
  [4999](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4999)
  through
  [5213](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5213);
- reread only the exact `xiShift` definition/geometry at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean:653](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean:653)
  through
  [712](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean:712);
- reread only the exact SCV package definitions at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  through
  [155](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:155);
- reread only the exact local tempered recovery / uniqueness surfaces at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179)
  through
  [248](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:248)
  and
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1954](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1954)
  through
  [1979](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1979).

- exact bounded result:
  no Lean theorem was added;
  this pass sharpens the frontier at the newly exposed seam:
  there is no checked lower landing beneath
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`.

- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  is checked, but it assumes exactly the target shifted-point continuity and
  only transports it along the affine `xiShift` map;
- source check:
  the later unflattened/flat/local-open continuity theorems are therefore
  wrappers above the same seam;
- source check:
  `section43_fixedTimeShellRaw_temperedRepr_fixedTime` still gives only a
  tempered FL package;
- source check:
  the SCV field `tube_continuousWithinAt` exists only for
  `HasFourierLaplaceReprRegular`, while `HasFourierLaplaceReprTempered`
  deliberately omits boundary continuity;
- source check:
  the local tempered recovery and uniqueness theorems explicitly require the
  missing `ContinuousWithinAt` / boundary-limit input rather than producing it;
- source check:
  `xiShift` and `xiShift_mem_forwardTube_of_real` provide only affine real
  transport and interior tube-membership preservation.

- reading conclusion:
  the raw shifted-point continuity theorem is itself the honest bottom seam in
  the current checked source;
  no smaller checked theorem/interface beneath it was missed.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, bounded reread immediately beneath the unflattened real-boundary zero seam):
this pass is docs-only.

- reread only the fresh docs/chat entries from the last pass;
- reread only the exact fixed-time source surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224),
  [4641](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4641),
  [5068](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5068),
  and
  [5221](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5221);
- reread only the exact nearby checked vanishing surface at
  [9617](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9617)
  through
  [9640](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9640);
- reread only the exact SCV theorem surfaces at
  [OSReconstruction/SCV/TubeDistributions.lean:83](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeDistributions.lean:83),
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232),
  and
  [OSReconstruction/SCV/LaplaceSchwartz.lean:143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143).

- exact bounded result:
  no Lean theorem was added;
  the reread sharpens the frontier one notch:
  even the nearest generic SCV zero-trace theorem does not provide a checked
  landing beneath the unflattened equality.

- source check:
  `section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime`
  still gives only `∃ T_t, ...`;
- source check:
  `section43_fixedTimeShellRaw_temperedRepr_fixedTime`
  still gives only
  `SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d (n + m)) G_t`;
- source check:
  `SCV.boundary_trace_zero_of_tempered_of_trace` additionally needs a separate
  continuous trace `G`, a raywise trace theorem to `G`, and a zero theorem for
  the stored boundary distribution, none of which the fixed-time source
  currently supplies in checked form;
- source check:
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` still assumes
  local `ContinuousWithinAt` and only identifies the boundary distribution with
  an integral against `F (realEmbed x)`;
- source check:
  the nearby checked zero theorem at [9617]-[9640] still concerns ambient
  tensor weights on the positive-energy region, not this complement-side
  boundary value of `bvt_F`;
- source check:
  the matching continuity and raywise-zero fixed-time theorem surfaces remain
  `sorry`.

- reading conclusion:
  there is no smaller source-supported theorem/interface beneath the
  unflattened real-boundary equality;
  the honest seam still stops there.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, bounded reread immediately beneath the real-boundary zero seam for `G_t`):
this pass is docs-only.

- reread only the fresh docs/chat entries from the last pass;
- reread only the exact fixed-time source surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224),
  [4641](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4641),
  [5115](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5115),
  [5171](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5171),
  and
  [5221](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5221);
- reread only the exact nearby checked vanishing surface at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9617](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9617)
  through
  [9640](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9640);
- reread only the exact definition of
  `section43PositiveEnergyRegion` at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:16](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:16);
- reread only the exact `realEmbed` / flatten source objects at
  [OSReconstruction/SCV/TubeDomainExtension.lean:110](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeDomainExtension.lean:110),
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:348](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:348),
  and
  [354](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:354).

- exact bounded result:
  no Lean theorem was added;
  this pass sharpens the frontier one notch lower:
  there is no smaller checked vanishing theorem beneath the proposed
  complement-side boundary equality
  `G_t (SCV.realEmbed xflat) = 0`;
  only a definitional unflattening identity sits below it.

- source check:
  from the exact definition of `G_t`,
  `G_t (SCV.realEmbed xflat)` unfolds to
  `bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      ((flattenCLEquiv (n + m) (d + 1)).symm (SCV.realEmbed xflat)) (t : ℂ))`;
- source check:
  by `SCV.realEmbed`, `flattenCLEquiv_symm_apply`, and
  `flattenCLEquivReal_symm_apply`, if
  `y := (flattenCLEquivReal (n + m) (d + 1)).symm xflat`,
  this is exactly
  `bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ => (y k μ : ℂ)) (t : ℂ))`;
- source check:
  `section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl`
  and
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  still provide only continuity/open-neighborhood packaging;
- source check:
  the nearby checked zero theorem at [9617]-[9640] still concerns ambient
  tensor weights on the positive-energy region, not `bvt_F` at complement-side
  real boundary points;
- source check:
  the only directly matching theorem surface asserting zero along the canonical
  boundary approach remains
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`,
  and it is still `sorry`.

- reading conclusion:
  no checked theorem-sized landing beneath the real-boundary equality was
  missed;
  the honest bottom seam is the equality
  `G_t (SCV.realEmbed xflat) = 0` itself.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, bounded reread immediately beneath the flat pointwise zero-trace supplier):
this pass is docs-only.

- reread only the fresh docs/chat entries from the last pass;
- reread only the exact coefficient theorem surface at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5221](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5221)
  through
  [5238](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5238);
- reread only the exact complement-side flat continuity package at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5115](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5115)
  through
  [5213](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5213);
- reread only the exact canonical path lemmas at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:2947](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:2947),
  [3118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3118),
  and
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean:96](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean:96);
- reread only the exact definition of
  `section43PositiveEnergyRegion` at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:16](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:16);
- reread only the exact nearby checked vanishing surface at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9617](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9617)
  through
  [9640](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9640).

- exact bounded result:
  no Lean theorem was added;
  this pass sharpens the frontier one notch lower:
  beneath the flat pointwise trace-to-zero statement, the actual smaller seam
  is the boundary-point vanishing theorem
  `G_t (SCV.realEmbed xflat) = 0`.

- source check:
  `section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl`
  already gives `ContinuousWithinAt G_t ... (SCV.realEmbed xflat)`;
- source check:
  `canonicalForwardConeDirection_mem`,
  `canonicalXiShift_mem_forwardTube`,
  and the checked flatten transport via `flattenCLEquiv_mem_tubeDomain_image`
  already place the canonical flattened shell path inside the flat tube;
- source check:
  from those checked ingredients, the flat trace-to-zero theorem would follow
  immediately once the real-boundary value itself is known to be zero;
- source check:
  the reread nearby zero theorem
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`
  does not apply, because it concerns tensor weights on the positive-energy
  region rather than `bvt_F` / `G_t` on the complement side;
- source check:
  no checked theorem in the reread source gives
  `G_t (SCV.realEmbed xflat) = 0`.

- reading conclusion:
  no already-checked theorem-sized landing beneath the flat supplier was
  missed;
  the honest next lower object is the complement-side real-boundary zero
  theorem for the flattened fixed-time continuation.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, bounded reread at the exact local-trace supplier seam):
this pass is docs-only.

- reread only the fresh docs/chat entries from the last pass;
- reread only the exact local-trace theorem surface at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179)
  through
  [219](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:219);
- reread only the exact fixed-time positivity-side theorem surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224),
  [4641](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4641),
  [5068](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5068),
  [5171](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5171),
  and
  [5221](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5221);
- reread only the exact package boundary at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143)
  through
  [162](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:162).

- exact bounded result:
  no Lean theorem was added;
  this pass sharpens the supplier frontier:
  the missing object is not a local construction of `B_t`, because on the
  complement side one can honestly take `B_t := fun _ => 0`;
  the first honest missing precursor is the pointwise flattened trace-to-zero
  theorem `htraceUflat`.

- source check:
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace`
  still asks for a separate `G`, `ContinuousOn G U`, one direction `η ∈ C`,
  and pointwise `htraceU`;
- source check:
  `section43_fixedTimeShellRaw_temperedRepr_fixedTime` still gives only
  `SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d (n + m)) G_t`;
- source check:
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  already gives an open `Uflat` inside the flattened complement image;
- source check:
  with that `Uflat`, the local trace function can be set to `0`, so
  `ContinuousOn B_t Uflat` is immediate;
- source check:
  the exact missing pointwise supplier is the flattened/canonical-direction
  theorem
  `∀ xflat ∈ Uflat, Tendsto
    (fun ε => G_t (fun i => ↑(xflat i) + ↑ε * ↑(ηflat i) * Complex.I))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds 0)`;
- source check:
  the only directly matching positivity-side pointwise theorem surface is
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`,
  and it is still a `sorry`.

- reading conclusion:
  no checked theorem-sized supplier producing `htraceUflat` was missed;
  the frontier is sharper than before:
  the real missing supplier is the complement-side pointwise zero-trace theorem.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, bounded reread immediately beneath the unavailable flat local-trace bridge):
this pass is docs-only.

- reread only the fresh docs/chat entries from the last four passes;
- reread the exact fixed-time theorem surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224),
  [4641](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4641),
  [4999](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4999),
  [5068](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5068),
  and
  [5171](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5171);
- reread only the exact local-trace / local-open recovery surfaces at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179)
  through
  [248](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:248);
- reread only the exact package boundary at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  through
  [159](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:159).

- exact bounded result:
  no Lean theorem was added;
  this pass isolates one precise source-level obstruction:
  the current checked source still stops before precursor `(a)`, the
  construction of a local trace function `B_t`.

- source check:
  `section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime`
  still gives only
  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ, ...`;
- source check:
  `section43_fixedTimeShellRaw_temperedRepr_fixedTime` still gives only
  `SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d (n + m)) G_t`;
- source check:
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace`
  still asks for a separate trace function `G`, together with
  `ContinuousOn G U` and pointwise `htraceU`;
- source check:
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` still asks for
  local `ContinuousWithinAt`;
- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  remains the first live `sorry`;
- source check:
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  shows the complement-side open-set geometry is already landed.

- reading conclusion:
  no precursor among `(a) B_t`, `(b) ContinuousOn B_t Uflat`, or
  `(c) htraceUflat` is source-ready now;
- plain reason:
  the current source layer has only a Schwartz-dual boundary functional and a
  tempered FL package for `G_t`, but no theorem producing a pointwise local
  boundary function on the complement side, so the chain stops before even the
  first precursor becomes honest.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, shifted-point continuity seam reread against the last four passes):
this pass is docs-only.

- reread only the fresh docs/chat entries from the last four passes;
- reread the exact fixed-time theorem surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4999](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4999),
  [5068](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5068),
  [5115](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5115),
  and
  [5171](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5171);
- reread only the exact local-recovery theorem surfaces at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:134](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:134)
  through
  [248](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:248);
- reread only the exact package boundary at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  through
  [159](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:159);
- reread only the exact tempered supplier at
  [OSReconstruction/SCV/VladimirovTillmann.lean:672](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:672)
  through
  [692](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:672);
- reread only the exact complement-open geometry packaged in
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5188](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5188)
  through
  [5213](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5213).

- exact bounded result:
  no Lean theorem was added;
  this pass isolates exactly one smaller real theorem-sized lower object
  directly beneath the missing shifted-point continuity theorem:
  the direct local-trace-to-`ContinuousWithinAt` bridge for flat fixed-time
  continuation `G_t`.

- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  still only transports an already-supplied shifted-point continuity proof;
- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  remains a bare `sorry`;
- source check:
  `section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl`
  and
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  are downstream flattening/open-set package theorems;
- source check:
  the exact lower object is still the unlanded theorem interface
  `section43_fixedTimeShellRaw_flatContinuousWithinAt_on_compl_of_trace_fixedTime`
  with local trace inputs
  `B_t`, `ContinuousOn B_t Uflat`, `η ∈ ForwardConeFlat d (n + m)`, and
  `htraceUflat`;
- source check:
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace`
  still concludes only local integral convergence;
- source check:
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` still requires
  `hcontU : ∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)`;
- source check:
  `section43_fixedTimeShellRaw_temperedRepr_fixedTime` still concludes only
  `SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d (n + m)) G_t`.

- reading conclusion:
  the shifted theorem is still not source-ready;
- plain reason:
  the checked SCV layer still has no theorem converting honest local trace data
  into the pointwise `ContinuousWithinAt` statement needed at the complement
  side, even though the local complement-open geometry below it is already in
  place.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, complement-side local-trace supplier seam rechecked after the tempered package):
this pass is docs-only.

- reread only the fresh docs/chat entries from the last three passes;
- reread the exact fixed-time theorem surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224),
  [4641](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4641),
  [4999](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4999),
  and
  [5068](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5068);
- reread only the exact local-trace theorem surfaces at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179)
  through
  [257](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:257);
- reread only the exact package boundary at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143)
  through
  [162](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:162);
- reread only the exact flattening / shift transports at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4999](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4999)
  through
  [5178](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5178).

- exact bounded result:
  no Lean theorem was added;
  this pass isolates exactly one smaller real theorem-sized lower object under
  the missing supplier:
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace`.

- source check:
  `section43_fixedTimeShellRaw_temperedRepr_fixedTime` still concludes only
  `SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d (n + m)) G_t`;
- source check:
  `section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime`
  still concludes only
  `∃ T_t, ... ∀ η ∈ ForwardConeAbs d (n + m), ∀ h,
    Tendsto (fun ε => ∫ x, F_analytic (...) * h x) ...`;
- source check:
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace`
  still asks for exactly
  `(_hG_contOn : ContinuousOn G U)` and
  `htraceU : ∀ x ∈ U, Tendsto ... (nhds (G x))`;
- source check:
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` still asks for
  separate
  `hcontU : ∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)`;
- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  remains the first live theorem above the supplier layer, while
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  still only transports an already-supplied continuity hypothesis.

- reading conclusion:
  the supplier theorem itself is still not source-ready;
- plain reason:
  current source still does not produce a local complement-side function `B_t`,
  `ContinuousOn B_t Uflat`, or pointwise `htraceUflat`, so the present
  distributional boundary-value data cannot honestly serve as the missing
  local-trace supplier.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, exact smaller theorem-sized object isolated under the complement-side local-trace supplier seam):
this pass is docs-only.

- reread only the fresh docs/chat entries from the last three passes;
- reread the exact fixed-time theorem surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224),
  [4641](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4641),
  [4913](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4913),
  and
  [4982](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4982);
- reread only the exact local-trace theorem surface at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179)
  through
  [219](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:219);
- reread only the exact package boundary at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143)
  through
  [162](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:162);
- reread only the exact ray-to-boundary transport theorem at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3627](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3627).

- exact bounded result:
  no Lean theorem was added;
  this pass isolates exactly one smaller real theorem-sized lower object under
  the missing supplier:
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace`;
- exact contract now pinned:
  beneath the direct continuity bridge, the local-trace supplier must provide a
  separate boundary function `B_t`, `ContinuousOn B_t Uflat`, one interior cone
  direction `η ∈ ForwardConeFlat d (n + m)`, and pointwise
  `htraceUflat : ∀ xflat ∈ Uflat, Tendsto ... (nhds (B_t xflat))`.

- source check:
  `section43_fixedTimeShellRaw_temperedRepr_fixedTime` still concludes only
  `SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d (n + m)) G_t`;
- source check:
  `section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime`
  still concludes only
  `∃ T_t, ... ∀ η ∈ ForwardConeAbs d (n + m), ∀ h,
    Tendsto (fun ε => ∫ x, F_analytic (...) * h x) ...`;
- source check:
  the isolated smaller theorem
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace`
  asks for exactly
  `(_hG_contOn : ContinuousOn G U)` and
  `htraceU : ∀ x ∈ U, Tendsto ... (nhds (G x))`;
- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  remains the first live theorem above the supplier layer, and no checked
  theorem in the reread source upgrades the present tempered/distributional data
  to that pointwise trace package.

- reading conclusion:
  the supplier theorem itself is still not source-ready;
- plain reason:
  current source has the tempered package for `G_t` and test-function boundary
  limits, but still lacks the local function `B_t`, its `ContinuousOn` proof on
  a complement-side open set, and the pointwise limit statement `htraceUflat`.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, one smaller source-ready lower object landed beneath the still-missing local-trace bridge):
this pass reread only the fresh docs/chat entries from the last three passes,
the exact fixed-time theorem surfaces at
[OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224),
[4474](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4474),
[4641](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4641),
[4913](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4913),
and
[4982](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4982);
- reread only the exact package boundary at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  through
  [162](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:162);
- reread only the exact local-trace / local-open recovery interfaces at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179)
  through
  [257](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:257);
- reread only the exact tempered supplier at
  [OSReconstruction/SCV/VladimirovTillmann.lean:672](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:672).

- exact bounded result:
  landed
  `section43_fixedTimeShellRaw_temperedRepr_fixedTime`
  in
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4641](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4641),
  with exact target
  `let G_t := ...; SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d (n + m)) G_t`;
- exact source check:
  this new theorem is an honest specialization of
  `SCV.vladimirov_tillmann_hasFourierLaplaceReprTempered` fed by the landed
  all-directions distributional BV theorem and the fixed-time global growth
  theorem;
- exact non-claim:
  it does not provide a local trace object `B_t`, does not provide
  `ContinuousOn B_t Uflat`, and does not provide pointwise `htraceUflat`.

- reading conclusion:
  the local-trace supplier itself is still too high;
- refined verdict:
  the best newly available lower object is the tempered package for `G_t`,
  while the still-missing direct supplier remains a theorem turning separate
  local trace data into the complement-side `ContinuousWithinAt` conclusion
  needed by
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`.

- verification note:
  `lake env lean ...OSToWightmanPositivity.lean` and then
  `lake build OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanPositivity`
  were both attempted;
- exact blocker:
  `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
  currently contains unresolved merge markers at lines 7-10, so the build
  stops there before checking the edited theorem.

Supervision correction (`2026-04-17`, reread note now pins the exact local-trace continuity theorem still missing on the complement side):
this pass is docs-only.

- reread the fresh docs/chat entries from the last two passes;
- reread the exact fixed-time theorem surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4474](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4474),
  [4982](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4982),
  [5029](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5029),
  [5085](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5085),
  and
  [5135](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5135);
- reread only the exact package boundary at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  through
  [162](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:162);
- reread only the exact local-trace / local-open recovery interfaces at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179)
  through
  [257](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:257);
- reread only the exact tempered supplier at
  [OSReconstruction/SCV/VladimirovTillmann.lean:672](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:672);
- reread only the exact checked forward-tube regular consumers at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881)
  and
  [914](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:914).

- source check:
  `section43_fixedTimeShellRawCLM_fl_representation_fixedTime` still lands only
  the tube identity for the flattened continuation
  `G_t zflat = bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))`;
- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  is still only the `xiShift` transport of an already-supplied shifted-point
  `ContinuousWithinAt` hypothesis;
- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  is still the first live theorem immediately above that landed FL
  specialization;
- source check:
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace` already
  uses the honest local trace vocabulary
  `G`, `ContinuousOn G U`, and `htraceU`;
- source check:
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` still requires
  `hcontU : ∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)`;
- source check:
  `SCV.HasFourierLaplaceReprRegular` still stores
  `boundary_continuous` and `tube_continuousWithinAt`;
- source check:
  no checked theorem upgrades the weaker local trace contract to those
  continuity fields.

- sharpened missing theorem statement:
  `private theorem
      section43_fixedTimeShellRaw_flatContinuousWithinAt_on_compl_of_trace_fixedTime
      (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
      {n m : ℕ} (hm : 0 < m) (t : ℝ)
      (Uflat : Set (Fin ((n + m) * (d + 1)) → ℝ))
      (hUflat_open : IsOpen Uflat)
      (hUflat_sub :
        Uflat ⊆ (flattenCLEquivReal (n + m) (d + 1)) ''
          ((section43PositiveEnergyRegion d (n + m))ᶜ))
      {B_t : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ}
      (hB_t_contOn : ContinuousOn B_t Uflat)
      (η : Fin ((n + m) * (d + 1)) → ℝ)
      (hη : η ∈ ForwardConeFlat d (n + m))
      (htraceUflat : ∀ xflat ∈ Uflat,
        Filter.Tendsto
          (fun ε : ℝ =>
            G_t (fun i => ↑(xflat i) + ↑ε * ↑(η i) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (B_t xflat))) :
      ∀ xflat ∈ Uflat,
        ContinuousWithinAt G_t
          (SCV.TubeDomain (ForwardConeFlat d (n + m)))
          (SCV.realEmbed xflat)`;
- sharpened minimal additional input:
  a local trace function `B_t`, continuous on an open complement-side set
  `Uflat`, plus the trace identification `htraceUflat` along one cone
  direction `η`;
- sharpened minimal consumer chain:
  direct local-open flat continuity
  →
  `section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl`
  →
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  →
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  →
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  →
  `hlimit_os`.

- reading conclusion:
  the missing source object is specifically a direct local-trace-to-
  `ContinuousWithinAt` bridge for `G_t` on a complement-side open set;
- refined verdict:
  the audited SCV layer already knows how to use such a trace for local
  integral/distributional recovery, but it still does not know how to turn that
  trace into the pointwise boundary continuity needed by the live fixed-time
  branch.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, reread note sharpened to the exact local-trace-to-`ContinuousWithinAt` theorem now missing on the complement side):
this pass is docs-only.

- reread the fresh docs/chat entries from the last two passes;
- reread the exact fixed-time theorem surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4474](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4474),
  [4913](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4913),
  [4982](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4982),
  [5029](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5029),
  [5085](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5085),
  [5135](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5135),
  and
  [5160](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5160);
- reread only the exact regular/tempered package boundary at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  through
  [190](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:190);
- reread only the exact local-trace interfaces at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179)
  through
  [266](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:266);
- reread only the exact tempered supplier at
  [OSReconstruction/SCV/VladimirovTillmann.lean:672](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:672);
- reread only the exact flat-regular forward-tube consumers at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881)
  and
  [914](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:914).

- source check:
  `section43_fixedTimeShellRawCLM_fl_representation_fixedTime` is landed and
  fixes the flattened continuation
  `G_t zflat = bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))`;
- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  is still only the `xiShift` transport of an already-supplied shifted-point
  continuity hypothesis;
- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  remains the first live theorem immediately above the landed FL theorem;
- source check:
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace` already
  uses the honest local trace vocabulary
  `G`, `ContinuousOn G U`, and `htraceU`;
- source check:
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` still asks for
  local `ContinuousWithinAt` directly and only concludes support-restricted
  distributional recovery;
- source check:
  `SCV.HasFourierLaplaceReprRegular` still carries the unavailable fields
  `boundary_continuous` and `tube_continuousWithinAt`;
- source check:
  no checked theorem upgrades either the tempered package or the local trace
  contract to those continuity fields.

- sharpened missing theorem statement:
  `private theorem
      section43_fixedTimeShellRaw_flatContinuousWithinAt_on_compl_of_trace_fixedTime
      (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
      {n m : ℕ} (hm : 0 < m) (t : ℝ)
      (Uflat : Set (Fin ((n + m) * (d + 1)) → ℝ))
      (hUflat_open : IsOpen Uflat)
      (hUflat_sub :
        Uflat ⊆ (flattenCLEquivReal (n + m) (d + 1)) ''
          ((section43PositiveEnergyRegion d (n + m))ᶜ))
      {B_t : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ}
      (hB_t_contOn : ContinuousOn B_t Uflat)
      (η : Fin ((n + m) * (d + 1)) → ℝ)
      (hη : η ∈ ForwardConeFlat d (n + m))
      (htraceUflat : ∀ xflat ∈ Uflat,
        Filter.Tendsto
          (fun ε : ℝ =>
            G_t (fun i => ↑(xflat i) + ↑ε * ↑(η i) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (B_t xflat))) :
      ∀ xflat ∈ Uflat,
        ContinuousWithinAt G_t
          (SCV.TubeDomain (ForwardConeFlat d (n + m)))
          (SCV.realEmbed xflat)`;
- sharpened minimal additional input:
  a local trace function `B_t` continuous on an open complement-side set
  `Uflat`, plus the pointwise trace identification `htraceUflat` along one
  interior cone direction `η`;
- sharpened minimal consumer chain:
  direct local-open flat continuity
  →
  `section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl`
  →
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  →
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  →
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  →
  `hlimit_os`.

- reading conclusion:
  the missing source object is specifically a direct local-trace-to-
  `ContinuousWithinAt` bridge for `G_t` on a complement-side open set;
- refined verdict:
  the audited SCV layer already knows how to use such a trace for
  distributional recovery, but it does not yet know how to turn it into the
  pointwise boundary continuity needed by the live fixed-time branch.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, reread note sharpened to the exact unavailable local-trace continuity bridge on the complement side):
this pass is docs-only.

- reread the fresh docs/chat entries from the last two passes;
- reread the exact fixed-time theorem surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4474](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4474),
  [4913](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4913),
  [4982](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4982),
  [5085](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5085),
  and
  [5135](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5135);
- reread only the exact regular/tempered package boundary at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  through
  [186](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:186),
  and the exact regular consumers at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:380](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:380)
  and
  [461](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:461);
- reread only the exact local-trace interfaces at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179)
  and
  [232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232);
- reread only the exact tempered supplier at
  [OSReconstruction/SCV/VladimirovTillmann.lean:672](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:672);
- reread only the exact flat-regular forward-tube consumers at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881)
  and
  [914](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:914).

- source check:
  `section43_fixedTimeShellRawCLM_fl_representation_fixedTime` is landed and
  fixes the flattened continuation
  `G_t zflat = bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))`;
- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  is still only the `xiShift` transport of a raw shifted-point continuity
  hypothesis;
- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  remains the first live theorem immediately above the landed FL theorem;
- source check:
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace` already
  uses the honest local trace vocabulary
  `G`, `ContinuousOn G U`, and pointwise trace data `htraceU`;
- source check:
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` still asks for
  local `ContinuousWithinAt` directly and only concludes distributional
  recovery on compactly supported tests;
- source check:
  `SCV.HasFourierLaplaceReprRegular` still carries the unavailable fields
  `boundary_continuous` and `tube_continuousWithinAt`;
- source check:
  no checked theorem upgrades either the tempered package or the local trace
  contract to those continuity fields.

- sharpened missing theorem statement:
  `private theorem
      section43_fixedTimeShellRaw_flatContinuousWithinAt_on_compl_of_trace_fixedTime
      (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
      {n m : ℕ} (hm : 0 < m) (t : ℝ)
      (Uflat : Set (Fin ((n + m) * (d + 1)) → ℝ))
      (hUflat_open : IsOpen Uflat)
      (hUflat_sub :
        Uflat ⊆ (flattenCLEquivReal (n + m) (d + 1)) ''
          ((section43PositiveEnergyRegion d (n + m))ᶜ))
      {B_t : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ}
      (hB_t_contOn : ContinuousOn B_t Uflat)
      (η : Fin ((n + m) * (d + 1)) → ℝ)
      (hη : η ∈ ForwardConeFlat d (n + m))
      (htraceUflat : ∀ xflat ∈ Uflat,
        Filter.Tendsto
          (fun ε : ℝ =>
            G_t (fun i => ↑(xflat i) + ↑ε * ↑(η i) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (B_t xflat))) :
      ∀ xflat ∈ Uflat,
        ContinuousWithinAt G_t
          (SCV.TubeDomain (ForwardConeFlat d (n + m)))
          (SCV.realEmbed xflat)`;
- sharpened minimal consumer chain:
  direct local-open flat continuity
  →
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  →
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  →
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  →
  `hlimit_os`.

- reading conclusion:
  the missing source object is specifically a direct local-trace-to-
  `ContinuousWithinAt` bridge for `G_t` on a complement-side open set;
- refined verdict:
  the audited SCV layer already knows how to use such a trace for
  distributional recovery, but it does not yet know how to turn it into the
  pointwise boundary continuity needed by the live fixed-time branch.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, reread note sharpened to the exact weak-to-regular upgrade now missing above the fixed-time FL theorem):
this pass is docs-only.

- reread the fresh docs/chat entries from the last two passes;
- reread the exact fixed-time theorem surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4474](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4474),
  [4913](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4913),
  and
  [4982](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4982);
- reread only the exact interface declarations at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118),
  [OSReconstruction/SCV/LaplaceSchwartz.lean:181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:181),
  [380](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:380),
  and
  [461](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:461);
- reread only the exact tempered-local consumer at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232);
- reread only the exact tempered supplier at
  [OSReconstruction/SCV/VladimirovTillmann.lean:672](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:672);
- reread only the exact flat-regular forward-tube consumers at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881)
  and
  [914](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:914).

- source check:
  `section43_fixedTimeShellRawCLM_fl_representation_fixedTime` is landed and
  already fixes the flattened continuation `G_t` and its FL identity on the
  tube;
- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  is a transport lemma only; it does not create continuity;
- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  is still the first live theorem above that landed FL theorem;
- source check:
  `SCV.HasFourierLaplaceReprRegular` carries the missing fields
  `boundary_continuous` and `tube_continuousWithinAt`;
- source check:
  `SCV.vladimirov_tillmann_hasFourierLaplaceReprTempered` stops one level short
  at `HasFourierLaplaceReprTempered`;
- source check:
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` still requires
  `hcontU : ∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)`;
- source check:
  the checked forward-tube consumers above a future flat regular package are
  `boundary_function_continuous_forwardTube_of_flatRegular` and
  `boundary_value_recovery_forwardTube_of_flatRegular`.

- sharpened missing theorem statements:
  strong interface candidate:
  `private theorem
      section43_fixedTimeShellRaw_regularFourierLaplaceRepr_fixedTime
      (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
      {n m : ℕ} (hm : 0 < m) (t : ℝ) :
      let G_t : (Fin ((n + m) * (d + 1)) → ℂ) → ℂ := fun zflat =>
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))
      SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d (n + m)) G_t`;
- weaker branch-local candidate:
  `private theorem
      section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl
      (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
      {n m : ℕ} (hm : 0 < m)
      (t : ℝ)
      (y : NPointDomain d (n + m))
      (hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ) :
      ContinuousWithinAt
        (bvt_F OS lgc (n + m))
        (ForwardTube d (n + m))
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ => (y k μ : ℂ)) (t : ℂ))`.

- reading conclusion:
  the missing source object is specifically the weak-to-regular upgrade from
  the landed fixed-time FL/spectral-support/growth package, with the direct
  shifted-point continuity theorem as the minimal weaker fallback;
- refined verdict:
  neither theorem is available in the audited layer for the exact source-first
  reasons above.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, reread note after locating the first live seam above the fixed-time FL representation):
this pass is docs-only.

- reread the fresh docs/chat entries from the last two passes;
- reread the exact fixed-time theorem surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4474](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4474),
  [4913](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4913),
  [4982](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4982),
  and
  [5085](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5085);
- reread only the exact SCV continuity/boundary-recovery interfaces at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118),
  [380](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:380),
  [461](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:461),
  and
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232);
- reread only the exact tempered supplier surface at
  [OSReconstruction/SCV/VladimirovTillmann.lean:680](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:680);
- reread only the exact flat-regular consumer surfaces at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:884](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:884)
  and
  [917](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:917)
  insofar as needed to name the continuity seam honestly.

- source check:
  `section43_fixedTimeShellRawCLM_fl_representation_fixedTime` is landed and
  already gives the flattened tube identity for
  `G_t zflat = bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))`;
- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  is only a transport lemma; its entire mathematical input is continuity of raw
  `bvt_F` at the shifted real boundary point;
- source check:
  the first live theorem above the landed FL specialization is exactly
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`;
- source check:
  `SCV.vladimirov_tillmann_hasFourierLaplaceReprTempered` can package the
  landed FL/growth/BV data only as `HasFourierLaplaceReprTempered`;
- source check:
  `LaplaceSchwartz.lean` exposes `boundary_continuous` and
  `tube_continuousWithinAt` only as fields of
  `HasFourierLaplaceReprRegular`, and the file explicitly says the regular
  upgrade theorem is not yet formalized;
- source check:
  `LocalBoundaryRecovery.lean` does not manufacture continuity from tempered
  data; its theorem `fourierLaplace_boundary_recovery_on_open_of_tempered`
  still assumes local continuity `hcontU`.

- sharpened missing theorem statement:
  `private theorem
      section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl
      (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
      {n m : ℕ} (hm : 0 < m)
      (t : ℝ)
      (y : NPointDomain d (n + m))
      (hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ) :
      ContinuousWithinAt
        (bvt_F OS lgc (n + m))
        (ForwardTube d (n + m))
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ => (y k μ : ℂ)) (t : ℂ))`.

- reading conclusion:
  no honest theorem-sized Lean landing is source-ready on this pass;
- refined verdict:
  the exact live gap above the fixed-time FL representation is the missing
  regularity/continuity upgrade needed to prove the shifted complement-side
  `ContinuousWithinAt` theorem.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-17`, reread note after landing the fixed-time spectral-support supplier):
this pass is theorem-sized source work plus docs sync.

- reread the fresh docs/chat entries from the last two passes;
- reread the exact fixed-time theorem surfaces at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224),
  [4372](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4372),
  and the adjacent local `G_t` sites at
  [4870](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4870)
  and
  [4925](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4925);
- reread the exact SCV axiom surfaces at
  [OSReconstruction/SCV/VladimirovTillmann.lean:148](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:148)
  and
  [392](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:392);
- reread the exact `schwartz_bv_to_flat_repr` declaration at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:1263](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:1263);
- reread only the nearby flattening/cone declarations at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:336](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:336),
  [456](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:456),
  and
  [460](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:460).

- source check:
  the new theorem
  `section43_fixedTimeShellRawCLM_bv_implies_fourier_support_fixedTime`
  now specializes `SCV.bv_implies_fourier_support` on the exact fixed-time
  seam;
- source check:
  its analytic input is still exactly
  `F_analytic z = bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))`;
- source check:
  it returns `Tflat` with support in
  `ForwardConeFlat d (n + m) =
    (flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)`;
- source check:
  it also returns the exact pairing identity
  `T_t.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (flattenCLEquivReal (n + m) (d + 1))) φ =
    Tflat (physicsFourierFlatCLM φ)`;
- source check:
  this is the precise consumer theorem immediately above the landed
  all-directions BV result;
- source check:
  `schwartz_bv_to_flat_repr` is not the first live consumer on this route
  segment, because it produces a `HasFourierLaplaceRepr` witness rather than
  the SCV frequency-side supplier object currently needed by theorem-3.

- reading conclusion:
  the fixed-time spectral-support supplier specialization was source-ready and
  is now landed;
- refined verdict:
  the next live seam is the fixed-time specialization of
  `SCV.fl_representation_from_bv` for the flattened continuation `G_t`.

- verification note:
  `timeout 60s lake env lean
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
  failed on an existing import/environment duplication, not a local theorem
  error;
  `lake build OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanPositivity`
  failed before the target module could be rebuilt, at
  `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:7`
  because that file currently contains merge markers (`<<<`), so no complete
  target build is claimed.

Supervision correction (`2026-04-17`, reread note after landing the fixed-time `fl_representation_from_bv` specialization):
this pass is theorem-sized source work plus docs sync.

- reread the fresh docs/chat entries from the last two passes;
- reread the exact fixed-time theorem surface at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224)
  through
  [4468](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4468),
  including the new consumer theorem immediately above the supplier layer;
- reread the exact SCV axiom surfaces at
  [OSReconstruction/SCV/VladimirovTillmann.lean:148](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:148)
  and
  [392](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:392),
  plus the flattened-salience proof pattern at
  [495](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:495);
- reread only the nearby flattening / cone declarations at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:336](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:336),
  [456](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:456),
  [460](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:460),
  and
  [629](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:629).

- source check:
  `section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime`
  is no longer the live seam;
- source check:
  the supplier specialization
  `section43_fixedTimeShellRawCLM_bv_implies_fourier_support_fixedTime`
  was already present immediately above it;
- source check:
  the first missing consumer was the fixed-time specialization of
  `SCV.fl_representation_from_bv`, and it is now landed as
  `section43_fixedTimeShellRawCLM_fl_representation_fixedTime`;
- source check:
  the theorem uses the same shifted continuation
  `F_analytic z = bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))`,
  the same shell boundary functional `T_t`,
  and a `Tflat` supported in `ForwardConeFlat d (n + m)`;
- source check:
  the only extra flat-cone ingredient needed above the supplier theorem was
  `IsSalientCone (ForwardConeFlat d (n + m))`, and the source already contained
  the exact proof pattern for that transport in `SCV.VladimirovTillmann`.

- reading conclusion:
  the first live consumer seam above the new all-directions BV theorem was
  source-ready and is now landed;
- refined verdict:
  the theorem-3 frontier has moved above the fixed-time FL representation
  specialization.

- verification note:
  attempted
  `timeout 60s lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`;
  it failed immediately because
  `OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValueLimits.olean`
  is missing, so no completed Lean build is claimed.

Supervision correction (`2026-04-17`, reread note after landing the fixed-time all-directions boundary-value theorem):
this pass is theorem-sized source work plus docs sync.

- reread the fresh docs/chat entries from the last two passes;
- reread the exact fixed-time theorem surface now at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4224)
  through
  [4361](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4361);
- reread the exact SCV axiom surfaces at
  [OSReconstruction/SCV/VladimirovTillmann.lean:148](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:148)
  and
  [392](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:392);
- reread only the nearby cone/flattening declarations at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:57](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:57),
  [336](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:336),
  [456](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:456),
  and
  [1263](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:1263);
- reread the exact canonical-direction declaration at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean:93](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean:93).

- source check:
  the new theorem
  `section43_fixedTimeShellRawCLM_boundaryValueData_allDirections_fixedTime`
  now preserves the full all-directions boundary-value package from
  `SCV.tube_boundaryValueData_of_polyGrowth`;
- source check:
  its `F_analytic` is exactly
  `fun z => bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))`;
- source check:
  the old theorem
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`
  is now just the canonical-ray corollary extracted from that stronger result;
- source check:
  this repairs the exact missing hypothesis surface
  `∀ η ∈ ForwardConeAbs d (n + m), ∀ φ, Tendsto ... (nhds (T_t φ))`
  on the fixed-time seam itself.

- reading conclusion:
  the formerly missing all-directions theorem statement was source-ready and is
  now landed;
- refined verdict:
  the fixed-time seam now honestly matches the SCV all-directions BV input
  surface, so the next live obstruction is above this theorem.

- verification note:
  attempted
  `timeout 20s lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`;
  it timed out with exit code `124` and no diagnostics, so no completed Lean
  build is claimed.

Supervision correction (`2026-04-16`, reread note on the exact missing all-directions boundary-value theorem statement on the fixed-time seam):
this pass is docs-only.

- reread the fresh docs/chat entries from the last two passes;
- reread the exact fixed-time theorem surface at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4221](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4221),
  together with the adjacent local fixed-time `G_t` site at
  [4727](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4727);
- reread the exact SCV axiom surfaces at
  [OSReconstruction/SCV/VladimirovTillmann.lean:148](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:148)
  and
  [392](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:392);
- reread only the nearby cone/flattening declarations at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:57](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:57),
  [336](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:336),
  and
  [456](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:456);
- reread the exact canonical-direction declaration at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean:93](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean:93).

- source check:
  the fixed-time theorem currently produces
  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ, ...`;
- source check:
  in that proof the continuation is named
  `F_analytic z = bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))`;
- source check:
  the only boundary-value limit actually extracted there is along
  `canonicalForwardConeDirection (d := d) (n + m)`;
- source check:
  `SCV.bv_implies_fourier_support` and `SCV.fl_representation_from_bv` both
  require the stronger hypothesis
  `∀ η ∈ ForwardConeAbs d (n + m), ∀ φ, Tendsto ... (nhds (T_t φ))`;
- source check:
  no nearby checked theorem upgrades the one-ray limit to that all-directions
  package;
- source check:
  `schwartz_bv_to_flat_repr` only transports an already available
  all-directions Pi-type BV witness to flat coordinates.

- sharpened missing theorem statement:
  the theorem now missing between the fixed-time source theorem and the SCV
  axioms is:
  for the same `T_t` and `F_analytic`,
  `∀ (η : Fin (n + m) → Fin (d + 1) → ℝ), η ∈ ForwardConeAbs d (n + m) →
      ∀ φ : SchwartzNPoint d (n + m),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin (n + m) → Fin (d + 1) → ℝ,
            F_analytic (fun k μ =>
              (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) * φ x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (T_t φ))`.

- reading conclusion:
  there is no honest theorem-sized source landing on this pass;
- refined verdict:
  the exact live gap is the fixed-time all-directions boundary-value
  strengthening itself.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the physics-side supplier specialization probe for the fixed-time flattened seam):
this pass is docs-only.

- reread the fresh docs/chat entries from the last pass;
- reread the exact fixed-time declarations at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4221](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4221),
  [4727](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4727),
  and
  [4782](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4782);
- reread the exact physics-side supplier/comparison declarations at
  [OSReconstruction/SCV/VladimirovTillmann.lean:148](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:148)
  and
  [392](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:392);
- reread the exact primitive FL/Fourier declarations at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052),
  [3471](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3471),
  [3491](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3491),
  and
  [3500](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3500);
- reread the exact flattening transport declarations at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:336](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:336),
  [365](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:365),
  and
  [378](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:378).

- source check:
  `SCV.bv_implies_fourier_support` already packages the supplier in the
  physics Fourier convention, so the inverse-Fourier supplier theorem is not
  the first obstruction on this pass;
- source check:
  that axiom still requires the full Pi-type boundary-value hypothesis
  `∀ η ∈ C, ∀ φ, Tendsto ... (nhds (W φ))`;
- source check:
  the exact fixed-time theorem
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`
  constructs `T_t`, but only with the boundary limit along
  `canonicalForwardConeDirection (d := d) (n + m)`;
- source check:
  no checked flattening or transport theorem nearby upgrades that one-ray
  boundary datum into the all-directions hypothesis required before either
  `SCV.bv_implies_fourier_support` or `SCV.fl_representation_from_bv` can be
  specialized;
- source check:
  flattening only transports an already-available Pi-type statement to the flat
  seam; it does not manufacture the missing all-`η` boundary-value package.

- reading conclusion:
  there is no honest theorem-sized source landing through the physics-side
  supplier axiom on this pass;
- refined verdict:
  the exact obstruction is now the boundary-value specialization layer for the
  fixed-time shifted continuation, not the inverse-vs-physics Fourier bridge.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact fixed-time comparison contract after collapsing the duplicate inverse-Fourier name mismatch):
this pass is docs-only.

- reread the fresh docs/chat entries from the last pass;
- reread the exact fixed-time declarations at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4221](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4221),
  [4727](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4727),
  and
  [4782](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4782);
- reread the exact inverse/physics Fourier declarations at
  [OSReconstruction/SCV/FourierSupportCone.lean:132](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:132),
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3471](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3471),
  [3491](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3491),
  and
  [3500](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3500);
- reread the exact supplier/comparison declarations at
  [OSReconstruction/SCV/FourierSupportCone.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:232)
  and
  [OSReconstruction/SCV/VladimirovTillmann.lean:392](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:392).

- source check:
  `SCV.inverseFourierFlatSupportCLM` and
  `SCV.inverseFourierFlatCLM` are defined by the same transport
  `fromEuc.comp (ft.comp toEuc)`;
- source check:
  the exact supplier theorem
  `SCV.fourierSupportInDualCone_of_tube_boundaryValue`
  therefore already lands, up to definitional equality, in the same
  Mathlib-convention inverse Fourier transform as
  `SCV.inverseFourierFlatCLM`;
- source check:
  the remaining normalization mismatch is exactly
  `SCV.physicsFourierFlatCLM_apply`,
  `physicsFourierFlatCLM f ξ =
    inverseFourierFlatCLM f ((-(1 / (2 * Real.pi) : ℝ)) • ξ)`;
- source check:
  no checked theorem transports a dual-cone-supported frequency-side
  distribution through that negative rescaling to the physics convention;
- source check:
  the exact function-level comparison theorem still exists in source only as
  the axiom `SCV.fl_representation_from_bv`;
- source check:
  its boundary identity remains
  `Wflat_t φ = Tflat_t (physicsFourierFlatCLM φ)`.

- reading conclusion:
  the exact candidate comparison theorem is unchanged, but the obstruction is
  now sharper than before:
  the blocker is not a separate mismatch between
  `inverseFourierFlatSupportCLM` and `inverseFourierFlatCLM`;
  it is the absent transport across the negative `1 / (2π)` scaling into
  `physicsFourierFlatCLM`, together with the fact that the comparison theorem
  itself is axiom-backed;
- refined verdict:
  the route remains docs-only on this seam.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact Fourier-normalization bridge layer on the fixed-time seam):
this pass is docs-only.

- reread the fresh docs/chat entries from the last pass;
- reread the exact normalization definitions at
  [OSReconstruction/SCV/FourierSupportCone.lean:132](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:132),
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3471](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3471),
  [3491](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3491),
  and
  [3500](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3500);
- reread the exact supplier/comparison declarations at
  [OSReconstruction/SCV/FourierSupportCone.lean:195](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:195),
  [232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:232),
  [OSReconstruction/SCV/VladimirovTillmann.lean:148](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:148),
  and
  [392](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:392);
- reread only the exact fixed-time declarations needed to state the theorem-3
  specialization at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4221](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4221),
  [4604](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4604),
  and
  [4673](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4673).

- source check:
  `SCV.inverseFourierFlatSupportCLM` is the Mathlib-convention Fourier
  transform transported to `Fin m → ℝ`;
- source check:
  `SCV.physicsFourierFlatCLM` is defined as
  `(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg).comp
    inverseFourierFlatCLM`
  with `scaleNeg` the negative scaling by `1 / (2 * π)`;
- source check:
  the exact checked formula is
  `physicsFourierFlatCLM f ξ =
    inverseFourierFlatCLM f ((-(1 / (2 * Real.pi) : ℝ)) • ξ)`;
- source check:
  the supplier theorem
  `SCV.fourierSupportInDualCone_of_tube_boundaryValue`
  still concludes
  `W φ = T (inverseFourierFlatSupportCLM φ)`;
- source check:
  the comparison axiom `SCV.fl_representation_from_bv` still requires
  `Wflat φ = Tflat (physicsFourierFlatCLM φ)`;
- source check:
  source also contains the separate supplier axiom
  `SCV.bv_implies_fourier_support`, already in the physics convention, but it
  is not a checked bridge theorem from the inverse-Fourier supplier layer;
- source check:
  no checked theorem in source relates
  `inverseFourierFlatSupportCLM` and `physicsFourierFlatCLM` strongly enough to
  convert one boundary identity into the other while keeping the same
  dual-cone support conclusion.

- reading conclusion:
  the needed bridge is not present as an honest theorem and not even as one
  checked source-ready normalization statement;
- refined verdict:
  the route remains docs-only on this layer because the normalization mismatch
  is substantive and both usable bridge directions in source are axiom-backed.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact post-supplier function-level FL comparison seam for the fixed-time shifted continuation):
this pass is docs-only.

- reread the fresh docs/chat entries from the last pass;
- reread the exact fixed-time cluster at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4221](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4221),
  [4604](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4604),
  and
  [4673](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4673);
- reread the exact primitive FL definition/evaluation surface at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052),
  [3061](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3061),
  and the primitive BV theorem at
  [4405](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4405);
- reread the exact dual-cone supplier layer at
  [OSReconstruction/SCV/FourierSupportCone.lean:132](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:132),
  [195](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:195),
  and
  [232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:232);
- reread the exact comparison-layer declaration at
  [OSReconstruction/SCV/VladimirovTillmann.lean:392](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:392);
- reread the exact weak/regular note at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  and
  [181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:181).

- source check:
  the exact flattened fixed-time continuation is still
  `G_t zflat = bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))`;
- source check:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` still gives only
  the fixed-time boundary functional `T_t`;
- source check:
  the exact next layer above that supplier is a function-level comparison with
  the primitive extension `fourierLaplaceExtMultiDim ... Tflat_t`;
- source check:
  checked source contains exactly that comparison layer only as the axiom
  `SCV.fl_representation_from_bv`;
- source check:
  its exact input boundary identity is
  `Wflat_t φ = Tflat_t (physicsFourierFlatCLM φ)`;
- source check:
  the nearest checked supplier theorem below,
  `SCV.fourierSupportInDualCone_of_tube_boundaryValue`,
  instead yields
  `Wflat_t φ = Tflat_t (inverseFourierFlatSupportCLM φ)`;
- source check:
  no checked bridge on this layer converts the inverse-Fourier supplier
  equality into the physics-Fourier equality required by
  `SCV.fl_representation_from_bv`;
- source check:
  both sides of the seam are therefore still blocked:
  the supplier theorem remains axiom-backed through
  `SCV.tube_boundaryValue_realizes_dualCone_distribution`, and the comparison
  theorem itself is also an axiom.

- reading conclusion:
  the weakest honest comparison theorem is the fixed-time specialization of
  `SCV.fl_representation_from_bv`, with hypotheses
  dual-cone support for `Tflat_t` plus the flattened boundary identity in the
  `physicsFourierFlatCLM` convention;
- refined verdict:
  there is no honest theorem-sized Lean landing on this seam in checked source.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact source layer immediately below the weak-to-regular contract for the fixed-time shifted continuation):
this pass is docs-only.

- reread the fresh docs/chat entries from the last pass;
- reread the exact fixed-time blocker cluster at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3825](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3825),
  [3900](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3900),
  [4221](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4221),
  [4604](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4604),
  and
  [4673](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4673);
- reread the exact weak/regular package note at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118),
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143),
  and
  [181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:181);
- reread the exact dual-cone supplier layer at
  [OSReconstruction/SCV/FourierSupportCone.lean:195](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:195)
  and
  [232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:232);
- reread the exact primitive FL growth/boundary declarations at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3342](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3342),
  [3388](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3388),
  [3435](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3435),
  and
  [3627](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3627);
- reread the exact flattened tempered supplier at
  [OSReconstruction/SCV/VladimirovTillmann.lean:672](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:672);
- reread the exact local continuity consumer at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232).

- source check:
  the exact fixed-time continuation is still
  `G_t zflat = bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))`;
- source check:
  the weak fixed-time feeder still gives only the boundary functional `T_t`
  plus growth/ray estimates, not a genuine frequency-side witness;
- source check:
  the exact weakest honest supplier theorem is
  `∃ Tflat_t,
      HasFourierSupportInDualCone (ForwardConeFlat d (n + m)) Tflat_t ∧
      ∀ φ, T_t φ = Tflat_t (inverseFourierFlatSupportCLM φ)`;
- source check:
  the nearest theorem surface for that is
  `SCV.fourierSupportInDualCone_of_tube_boundaryValue`;
- source check:
  that theorem still rests on the axiom
  `SCV.tube_boundaryValue_realizes_dualCone_distribution`;
- source check:
  `SCV.vladimirov_tillmann_hasFourierLaplaceReprTempered` only lands the weak
  flattened package, not the genuine dual-cone-supported FL witness and not
  any regular continuity field;
- source check:
  `SCV/LaplaceSchwartz.lean` still explicitly marks the strong-to-regular
  upgrade theorem as missing.

- reading conclusion:
  there is no honest theorem-sized Lean landing on the checked source layer;
- refined verdict:
  the route remains docs-only because the exact supplier theorem is still
  axiom-backed and the next bridge from genuine FL input to
  `HasFourierLaplaceReprRegular` is also still absent.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact dual-cone FL supplier theorem for the fixed-time shifted continuation):
this pass is docs-only.

- reread the fresh docs/chat entries from the last pass;
- reread the exact theorem cluster at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3822](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3822),
  [3894](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3894),
  [4601](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4601),
  [4669](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4669),
  and
  [4687](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4687);
- reread the exact weak/regular SCV package note at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118),
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143),
  [181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:181),
  and the weak constructor at
  [976](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:976);
- reread the exact dual-cone support source surface at
  [OSReconstruction/SCV/FourierSupportCone.lean:195](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:195)
  and
  [232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:232);
- reread the exact strong FL growth/BV declarations at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3342](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3342)
  and
  [4405](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4405);
- reread the exact flattened supplier packaging at
  [OSReconstruction/SCV/VladimirovTillmann.lean:672](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:672);
- reread the exact local continuity consumer at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232).

- source check:
  the exact fixed-time weak feeder still stops at tempered boundary-value data
  and growth;
- source check:
  the exact honest theorem immediately below the weak-to-regular contract is:
  identify the fixed-time boundary functional `T_t` for `G_t` with a genuine
  dual-cone-supported frequency-side distribution
  `Tflat_t`, i.e.
  `HasFourierSupportInDualCone (ForwardConeFlat d (n + m)) Tflat_t` together
  with
  `T_t φ = Tflat_t (inverseFourierFlatSupportCLM φ)`;
- source check:
  the nearest theorem surface for that is
  `SCV.fourierSupportInDualCone_of_tube_boundaryValue`;
- source check:
  that theorem still depends on the axiom
  `SCV.tube_boundaryValue_realizes_dualCone_distribution`, so it is not an
  honest source-ready landing;
- source check:
  `SCV/PaleyWienerSchwartz.lean` does provide strong FL growth and boundary
  value theorems for `fourierLaplaceExtMultiDim`, but checked source still does
  not identify `G_t` with that extension nor upgrade the strong FL input to
  `HasFourierLaplaceReprRegular`;
- source check:
  `SCV/LaplaceSchwartz.lean` still explicitly marks that upgrade as missing.

- reading conclusion:
  the exact supplier theorem one layer below the weak/regular contract is now
  pinned down more sharply than before: it is the genuine dual-cone FL
  realization of the fixed-time boundary functional, not yet the continuity
  theorem itself;
- refined verdict:
  the route remains docs-only because even that supplier theorem is still
  axiom-backed/unformalized in checked source, and the next strong-to-regular
  bridge is also still absent.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact weak-to-regular boundary-regularity contract beneath the shifted-point blocker):
this pass is docs-only.

- reread the fresh docs/chat entries from the last pass;
- reread the exact theorem cluster at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4209](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4209),
  [4601](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4601),
  [4669](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4669),
  [4687](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4687),
  and
  [4720](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4720);
- reread the exact weak/regular SCV package declarations and note at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118),
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143),
  [181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:181),
  [380](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:380),
  and
  [976](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:976);
- reread the exact local continuity consumer at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232);
- reread the exact flattened geometry declarations at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:456](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:456),
  [638](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:638),
  and
  [378](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:378);
- reread the exact dual-cone support theorem surface at
  [OSReconstruction/SCV/FourierSupportCone.lean:188](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:188).

- source check:
  the live blocker is still
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`;
- source check:
  the immediate theorem above it is still transport only;
- source check:
  `HasFourierLaplaceReprTempered` still does not contain any continuity field;
- source check:
  `HasFourierLaplaceReprRegular` is exactly where
  `tube_continuousWithinAt` first appears;
- source check:
  the local consumer already wants exactly local `ContinuousWithinAt`;
- source check:
  the fixed-time feeder still gives only weak BV data and growth;
- source check:
  the source note still says the genuine upgrade from strong FL input to
  `HasFourierLaplaceReprRegular` is not formalized.

- reading conclusion:
  the weakest honest bridge theorem is not a wrapper from regular input to
  continuity and not a theorem from tempered input alone;
- reading conclusion:
  it must add genuinely stronger missing mathematics, namely a dual-cone-
  supported Fourier-Laplace representation for `G_t`, and from that conclude
  either
  `SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d (n + m)) G_t`
  or directly
  `∀ xflat ∈ (flattenCLEquivReal (n + m) (d + 1)) ''
      ((section43PositiveEnergyRegion d (n + m))ᶜ),
      ContinuousWithinAt G_t
        (SCV.TubeDomain (ForwardConeFlat d (n + m)))
        (SCV.realEmbed xflat)`;
- refined verdict:
  no such theorem is source-ready now on the checked route layer.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact shifted-point continuity supplier seam):
this pass is docs-only.

- reread the fresh docs/chat entries recording that the regular-package /
  `tube_continuousWithinAt` constructor story was one layer too high;
- reread the exact theorem cluster at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4601](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4601),
  [4669](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4669),
  [4687](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4687),
  [4720](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4720),
  and
  [4776](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4776);
- reread the fixed-time feeder and growth suppliers at
  [3822](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3822),
  [3894](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3894),
  and
  [4209](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4209);
- reread the exact SCV package fields and the weak-to-regular note at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118),
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143),
  [181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:181),
  and the tempered package constructor at
  [976](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:976);
- reread the exact local continuity consumer at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232).

- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  is again the exact minimal blocker;
- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  only transports a supplied
  `hcont_shifted` and does not construct it;
- source check:
  the exact candidate theorem immediately beneath the blocker is the direct
  fixed-time shifted-point continuity theorem for the flattened continuation
  `G_t`, not a higher-level regular-package wrapper;
- source check:
  the raw equivalent statement is continuity of `bvt_F` at
  `xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
    (fun k μ => (y k μ : ℂ)) (t : ℂ)`
  for all
  `y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`;
- source check:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` still gives only
  the weak boundary-value functional `T_t`,
  while the shifted growth theorems only give polynomial and ray bounds;
- source check:
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` already shows the
  next consumer needs exactly local `ContinuousWithinAt`;
- source check:
  `HasFourierLaplaceReprTempered` still has no continuity field, and the real
  upgrade to `HasFourierLaplaceReprRegular` is still explicitly unformalized.

- reading conclusion:
  the exact smallest honest theorem statement to target now is
  `∀ xflat ∈ (flattenCLEquivReal (n + m) (d + 1)) ''
      ((section43PositiveEnergyRegion d (n + m))ᶜ),
      ContinuousWithinAt G_t
        (SCV.TubeDomain (ForwardConeFlat d (n + m)))
        (SCV.realEmbed xflat)`;
- refined verdict:
  there is still no theorem-sized Lean landing from already-landed source,
  because the missing mathematical object is the shifted real-boundary
  continuity theorem itself.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact fixed-time regular-package constructor seam):
this pass is docs-only.

- reread the exact fixed-time feeder and shifted continuation cluster at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131),
  [4514](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514),
  [4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4635](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4635),
  and
  [4682](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4682);
- reread the fixed-time growth suppliers at
  [3714](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3714),
  [3735](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3735),
  and
  [3810](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:3810);
- reread the exact SCV package fields and upgrade note at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118),
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143),
  [166](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:166),
  and
  [181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:181);
- reread the exact local tempered recovery consumer at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232);
- reread the regular flattened consumers at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881)
  and
  [914](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:914).

- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  is still the exact live blocker;
- source check:
  the exact fixed-time candidate beneath it is the flattened shifted
  continuation `G_t` already defined by `let` in the flat continuity theorems;
- source check:
  the fixed-time feeder already provides holomorphy, weak boundary-value data,
  and growth/ray estimates for that continuation route;
- source check:
  `HasFourierLaplaceReprTempered` still has no continuity field;
- source check:
  the first checked continuity-bearing interface is
  `HasFourierLaplaceReprRegular.tube_continuousWithinAt`;
- source check:
  the local recovery and forward-tube theorems only consume that continuity or
  regular package; none constructs it on this layer.

- reading conclusion:
  the exact smallest honest theorem to target beneath the blocker is a
  fixed-time theorem for `G_t` yielding either
  `SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d (n + m)) G_t`
  or directly the equivalent real-locus statement
  `∀ xflat` in the flattened complement image,
  `ContinuousWithinAt G_t (SCV.TubeDomain (ForwardConeFlat d (n + m))) (SCV.realEmbed xflat)`;
- refined verdict:
  no such theorem is source-ready now, because the missing mathematical step is
  the boundary-regularity upgrade itself from weak FL data to pointwise
  continuity.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact first regularity supplier beneath the shifted-point theorem):
this pass is docs-only.

- reread the exact theorem cluster at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131),
  [4514](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514),
  [4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  and
  [4601](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4601);
- reread the exact SCV package fields and upgrade note at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118),
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143),
  [181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:181),
  and the tempered constructor note at
  [976](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:976);
- reread the exact local consumer at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232);
- reread the regular flattened forward-tube consumers at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:881),
  [914](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:914),
  and
  [1066](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:1066).

- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  is still the exact minimal blocker;
- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  remains purely a transport lemma above that seam;
- source check:
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` still consumes
  local `ContinuousWithinAt` directly and does not force a lower explicit trace
  wrapper;
- source check:
  the first continuity-bearing interface already in checked source is
  `HasFourierLaplaceReprRegular.tube_continuousWithinAt`;
- source check:
  the checked forward-tube theorems confirm that regular flattened input is
  only consumed, never constructed, on this layer;
- source check:
  `HasFourierLaplaceReprTempered` still stops short of any continuity field,
  and `SCV/LaplaceSchwartz.lean` still says the weak-to-regular upgrade theorem
  has not been formalized.

- reading conclusion:
  the exact smallest honest theorem/interface beneath the shifted-point theorem
  is a regular flattened FL package for the fixed-time shifted continuation
  `G_t`, or equivalently a theorem directly supplying its
  `tube_continuousWithinAt`;
- refined verdict:
  no such supplier theorem is source-ready now, so the result is docs-only
  again.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact shifted-point continuity seam after checking the theorem statements themselves):
this pass is docs-only.

- reread the exact theorem cluster at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514),
  [4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4601](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4601),
  and
  [4736](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4736);
- reread the fixed-time feeder at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131);
- reread the exact local continuity-consuming theorem at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232)
  together with the explicit-trace variant at
  [179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179);
- reread the exact package fields and the checked upgrade note at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118),
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143),
  and
  [181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:181).

- source check:
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  is still the exact minimal next theorem on this route slice;
- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  is purely a transport lemma and contributes no new regularity;
- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_on_section43PositiveEnergyRegion_compl`
  simply consumes that transport plus the raw shifted-point continuity theorem;
- source check:
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  is downstream of that transported continuity and does not lower the seam;
- source check:
  the checked SCV local-recovery theorem already consumes exactly
  `hcontU : ∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)`;
- source check:
  the fixed-time positivity feeder still gives only a distributional boundary
  functional;
- source check:
  `HasFourierLaplaceReprTempered` still has no continuity field, whereas
  `HasFourierLaplaceReprRegular` does;
- source check:
  the note in `SCV/LaplaceSchwartz.lean` still says the weak-to-regular upgrade
  theorem has not been formalized;
- source check:
  no reread theorem on this exact layer upgrades the fixed-time source data to
  the needed raw shifted-point `ContinuousWithinAt`.

- reading conclusion:
  the honest verdict is still docs-only;
- refined verdict:
  the current theorem cannot be honestly landed from already-landed source;
- exact smaller interface only if one is named:
  not an explicit trace wrapper, but a boundary-regularity theorem for raw
  `bvt_F` at the shifted complement-side real point, or an equivalent regular
  Fourier-Laplace package for the shifted continuation.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact shifted-point continuity theorem and its true source-level obstruction):
this pass is docs-only.

- reread the exact theorem cluster at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514),
  [4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4601](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4601),
  and
  [4736](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4736);
- reread the fixed-time feeder at
  [4131](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131);
- reread the exact local tempered recovery theorem at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:236](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:236)
  together with its local DCT seam at
  [138](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:138);
- reread the exact package fields in
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  and
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143);
- reread the regular-uniqueness consumer at
  [OSReconstruction/SCV/TubeDistributions.lean:141](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeDistributions.lean:141)
  and the continuity-only uniqueness theorem at
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1658](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1658).

- source check:
  the exact minimal next theorem is indeed the already-present private theorem
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`;
- source check:
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  is only a transport lemma and contributes no new boundary regularity;
- source check:
  `LocalBoundaryRecovery.lean` already has a local tempered recovery theorem
  whose extra hypothesis is exactly
  `ContinuousWithinAt F (TubeDomain C) (realEmbed x)` on the relevant open set;
- source check:
  this means the earlier docs/chat demand for a separate explicit trace object
  beneath the current theorem was too low;
- source check:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` still gives only
  the distributional boundary functional;
- source check:
  `HasFourierLaplaceReprTempered` still does not contain
  `tube_continuousWithinAt`, while `HasFourierLaplaceReprRegular` does;
- source check:
  `SCV/LaplaceSchwartz.lean` still explicitly states that the upgrade to the
  regular package has not been formalized;
- source check:
  no reread theorem constructs that regular package for `bvt_F` or directly
  proves the needed shifted-point `ContinuousWithinAt`.

- reading conclusion:
  the honest verdict is still docs-only;
- refined verdict:
  the present theorem cannot be proved from already-landed source;
- exact smaller interface only if forced:
  not an explicit trace wrapper, but a boundary-regularity theorem supplying
  `ContinuousWithinAt` / `tube_continuousWithinAt` for raw `bvt_F` on the
  relevant shifted real complement points, or an equivalent regular FL package
  for the shifted continuation.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact theorem directly consumed by the outside-region branch under `hlimit_os`):
this pass is docs-only.

- reread the live outside-region branch in
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9923](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9923),
  especially the local blocker sketch near
  [10074](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:10074),
  [10154](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:10154),
  and
  [10177](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:10177);
- reread the exact lower outside-region shell chain at
  [4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4736](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4736),
  and
  [4756](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4756);
- reread the weight-transport input theorem at
  [9302](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9302);
- reread the theorem-3 consumer boundary in
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:5142](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:5142)
  and
  [5277](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:5277).

- source check:
  the theorem immediately under `hlimit_os` is already present in source as
  the generic statement
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`;
- source check:
  this is the right theorem category for the outside-region branch because it
  asks only for a test `h` with vanishing
  `section43PositiveEnergyQuotientMap`, exactly matching the branch need after
  taking
  `h = (φ.conjTensorProduct ψ) - (f.conjTensorProduct g)`;
- source check:
  `section43PositiveEnergyQuotientMap_conjTensorProduct_eq_of_repr_eq_transport`
  is the already-landed feeder that supplies the needed quotient equality for
  that specialization;
- source check:
  therefore a new pair-specific shell-comparison theorem would be wrapper
  drift;
- source check:
  the actual unresolved lower proof seam stays beneath that theorem, at
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  and ultimately
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`.

- reading conclusion:
  the exact minimal theorem beneath `hlimit_os` should stay as the existing
  descended shell functional theorem in `OSToWightmanPositivity.lean`;
- refined verdict:
  no Lean landing is source-ready from the checked layer, because the direct
  theorem under `hlimit_os` still rests on the older complement-side
  coefficient/continuity blocker;
- no-wrapper design note:
  keep the branch-specific fixed-pair use as a specialization of the generic
  `h`/`hq` theorem, not as a new theorem surface.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on exact theorem ownership and the minimal no-wrapper input surface):
this pass is docs-only.

- reread the exact supplier theorem at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131);
- reread the immediate complement-side seam at
  [4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4686](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686),
  and
  [4736](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4736);
- reread the exact generic local-trace consumer at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179);
- reread the exact tempered package constructor surface at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:976](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:976);
- reread the exact weak boundary-value existence theorem at
  [OSReconstruction/SCV/TubeBoundaryValues.lean:745](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeBoundaryValues.lean:745).

- source check:
  `TubeBoundaryValues.lean` stops at the weak distributional theorem and does
  not own any pointwise local trace upgrade;
- source check:
  `LaplaceSchwartz.lean` packages the same data into
  `HasFourierLaplaceReprTempered`, but that structure still contains no
  pointwise boundary trace field;
- source check:
  `LocalBoundaryRecovery.lean` already has the exact consumer contract wanted
  downstream:
  explicit trace `G`,
  `ContinuousOn G U`,
  and
  the raywise limit theorem on `U`;
- source check:
  the only branch-specific missing object is therefore a positivity-local
  supplier theorem producing that trace package for the fixed-time flattened
  shell continuation itself.

- reading conclusion:
  the next honest theorem belongs in
  `OSToWightmanPositivity.lean`, not in the generic SCV files;
- refined verdict:
  its minimal hypotheses should be only the existing branch data
  `(OS, lgc, hm, t)`;
  the earlier notes saying "for each fixed `t > 0`" were too strong at the
  theorem-design level, because the immediate complement-side consumers below
  the seam are stated for arbitrary `t : ℝ`;
- exact sufficient output:
  existence of a branch-specific trace
  `B_t : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ`
  with `ContinuousOn B_t Uflat` and the exact raywise boundary-limit theorem on
  `Uflat`;
- no-wrapper design note:
  do not make a separately passed `HasFourierLaplaceReprTempered` argument part
  of the new theorem statement; that is derived from the same fixed-time source
  data and belongs only in the downstream SCV application step.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact minimal new theorem now required below the complement-side continuity seam):
this pass is docs-only.

- reread the exact supplier theorem at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131);
- reread the immediate complement-side consumers at
  [4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4620](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4620),
  [4686](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686),
  and
  [4736](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4736);
- reread the exact local trace consumers at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:105](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:105),
  [179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179),
  and
  [232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232);
- reread the actual tempered package surface at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:66](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:66)
  and
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143);
- reread the exact SCV existence theorem used underneath at
  [OSReconstruction/SCV/TubeBoundaryValues.lean:745](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeBoundaryValues.lean:745).

- source check:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` is built from
  `SCV.tube_boundaryValueData_of_polyGrowth`;
- source check:
  that theorem gives only a Schwartz functional `W` with boundary-value
  convergence of pairings;
- source check:
  `HasFourierLaplaceReprTempered` likewise contains no explicit pointwise
  boundary trace on an open real set;
- source check:
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace` still
  requires an explicit trace `G`, `ContinuousOn G U`, and pointwise raywise
  convergence to `G`.

- reading conclusion:
  the honest verdict is still docs-only;
- refined verdict:
  the exact minimal new theorem now required is:
  for fixed `t > 0`, if
  `Uflat := (flattenCLEquivReal (n + m) (d + 1)) ''
    ((section43PositiveEnergyRegion d (n + m))ᶜ)`,
  and
  `G_t zflat := bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))`,
  then produce some
  `B_t : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ`
  with
  `ContinuousOn B_t Uflat`
  and
  `∀ xflat ∈ Uflat, Filter.Tendsto
    (fun ε : ℝ =>
      G_t (SCV.realEmbed xflat +
        ε • (fun i =>
          (canonicalForwardConeDirectionFlat (d := d) (n + m) i : ℂ)) *
          Complex.I))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (B_t xflat))`;
- why present source still stops short:
  the available source object is only the distributional functional `T_t`,
  while the local boundary-recovery theorem still consumes an already-given
  pointwise trace on `Uflat`.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact complement-side source object still missing under the outside-region fixed-time branch):
this pass is docs-only.

- reread the fixed-time boundary-functional supplier at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131);
- reread the exact complement-side theorem cluster at
  [4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4620](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4620),
  and
  [4736](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4736);
- reread the live outside-region use inside
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9923](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9923);
- reread the exact local-recovery contracts at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:105](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:105),
  [179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179),
  and
  [232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232).

- source check:
  the outside-region branch still feeds through
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  before the coefficient-limit theorem;
- source check:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` still gives only
  a distributional boundary functional `T_t`;
- source check:
  the available separate-trace SCV theorem still expects a separate pointwise
  trace object `G` on an open real set, with `ContinuousOn G U` and a raywise
  convergence hypothesis `htraceU`;
- source check:
  no theorem was found in the reread cluster that upgrades `T_t` to that
  explicit pointwise complement-side trace for the flattened shifted shell on
  `Uflat = (flattenCLEquivReal ...) '' ((section43PositiveEnergyRegion ...)ᶜ)`.

- reading conclusion:
  the honest verdict is still docs-only;
- refined verdict:
  the first exact missing source object is an explicit complement-side trace
  `B_t` on `Uflat` with `ContinuousOn B_t Uflat` and the exact raywise limit
  contract, or an equivalent local boundary theorem producing those data;
- why the current seam does not close:
  the local SCV recovery layer consumes that pointwise trace object, while the
  current positivity-side source only supplies the weaker distributional
  boundary functional `T_t`.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the live `hHlimit` consumer versus the actual first missing outside-region source object):
this pass is docs-only.

- reread the fixed-time outside-region branch in
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9923](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9923),
  especially the local blocker comment near
  [10125](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:10125),
  [10158](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:10158),
  and
  [10177](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:10177);
- reread the exact lower outside-region chain at
  [4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4601](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4601),
  [4736](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4736),
  and
  [4761](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4761);
- reread the scalar-trace supplier / consumer objects in
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:4901](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:4901),
  [5142](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:5142),
  and
  [5277](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:5277);
- reread the positivity-side feeder theorem that converts the fixed-time value
  equality into the theorem-3 kernel identity at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5623](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5623).

- source check:
  `BoundaryValueLimits.lean` is not missing a lower theorem here;
  it already reduces the public `hHlimit` consumer to proving the fixed-time
  positive-real equality `hreal`;
- source check:
  the live fixed-time theorem
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`
  is exactly the local supplier of that `hreal`;
- source check:
  however the outside-region branch of that theorem still bottoms out in the
  older complement-side chain through
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`;
- source check:
  that chain is first blocked by
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`,
  which remains unproved;
- source check:
  the only nearby lower source object is still
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`, a
  distributional boundary functional, not the pointwise local trace /
  boundary-continuity theorem needed on the complement side.

- reading conclusion:
  the honest verdict is still docs-only;
- refined verdict:
  the shell-comparison theorem sketched near `hlimit_os` is not yet the first
  source-ready theorem-sized landing, because it presupposes the unresolved
  lower complement-side trace / continuity contract;
- exact first missing object:
  the outside-region boundary-trace / `ContinuousWithinAt` supplier for shifted
  raw `bvt_F`, currently surfaced as
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on why the separate-trace local recovery route is not yet landable on the outside-region seam):
this pass is docs-only.

- reread the live outside-region theorem cluster at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4601](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4601),
  [4686](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686),
  and
  [4736](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4736);
- reread the fixed-time shell boundary-functional supplier at
  [4131](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131);
- reread the exact separate-trace local recovery contracts at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:105](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:105),
  [179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179),
  and
  [232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232).

- source check:
  the repaired SCV contract does allow a separate real-edge trace object `G`,
  not only `F ∘ realEmbed`;
- source check:
  however the local theorem still requires that `G` and the raywise limit data
  `htraceU` be provided as inputs;
- source check:
  the live fixed-time shell source only provides the boundary functional
  `T_t` via `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`;
- source check:
  no earlier theorem was found producing the exact needed complement-side
  trace object for the flattened shifted shell continuation on the open set
  `Uflat = (flattenCLEquivReal ...) '' ((section43PositiveEnergyRegion ...)ᶜ)`,
  together with `ContinuousOn` and pointwise ray-trace convergence there.

- reading conclusion:
  the honest verdict is still docs-only;
- refined verdict:
  the exact first missing source object is this explicit local boundary trace
  `B_t` on `Uflat`, not merely another wrapper around
  `ContinuousWithinAt (bvt_F ...)`;
- why the SCV trace theorems still do not close the branch:
  they consume `B_t` and `htraceU`, while the current outside-region shell code
  only has the weaker distributional boundary functional `T_t`.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note on the exact source obstruction for the first complement-side theorem):
this pass is docs-only.

- reread the live outside-region supplier at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583);
- reread the fixed-time shell boundary-value existence package at
  [4124](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4124);
- reread the raw `bvt_F` holomorphy source at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean:355](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean:355);
- reread the local SCV recovery contract at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232).

- source check:
  `bvt_F_holomorphic` gives interior continuity only after the point is already
  known to lie in `ForwardTube`;
- source check:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` packages only a
  boundary-value functional for the shifted shell family;
- source check:
  the local SCV recovery theorem still assumes
  `ContinuousWithinAt F (TubeDomain C) (realEmbed x)` on the open set, so it is
  a consumer of the missing continuity, not a supplier;
- source check:
  no earlier theorem was found that upgrades the current source package to
  complement-side real-edge continuity of raw `bvt_F` at the shifted point.

- reading conclusion:
  the first honest theorem-sized target remains exactly
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`;
- refined verdict:
  this theorem cannot yet be proved from current source because the needed
  boundary regularity of `bvt_F` on the outside-region real edge is not present
  in the live import layer.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, reread note for the live outside-region shell seam under `hlimit_os`):
this pass is docs-only.

- reread the full proof body of
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9923](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9923);
- reread the complement-side outside-region suppliers at
  [4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4736](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4736),
  and
  [4761](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4761);
- grep-checked the live route files for any earlier theorem already supplying
  complement-side `ContinuousWithinAt` for `bvt_F` at the shifted real point.

- source check:
  the live `hlimit_os` body already clears the source-support branch and the
  positive-energy/outside-source branch using landed transport and weight
  comparison lemmas;
- source check:
  the remaining outside-region path is the declared complement-side chain
  starting with
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`;
- source check:
  that continuity theorem is the first actual `sorry` on the live chain;
- source check:
  no earlier theorem was found in the current source files that already gives
  this complement-side boundary continuity of `bvt_F`.

- reading conclusion:
  the smallest honest theorem-sized step is now the exact existing theorem
  surface
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`;
- refined verdict:
  the outside-region shell contribution is blocked first by boundary
  regularity of `bvt_F` at the shifted real boundary point, not yet by the
  later shell-integral limit theorem.

- verification note:
  docs-only pass; no Lean build was run.

Supervision correction (`2026-04-16`, theorem-3 reread after the primitive-FL target removal):
this pass is docs-only.

- reread the contract-repair note in
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3236](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3236);
- reread the theorem-3 limit packaging around
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:4892](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:4892),
  [5277](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:5277),
  and
  [5408](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:5408);
- reread the fixed-time Stage-5 shell comments and the exact blocker note in
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5456](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5456),
  [5843](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5843),
  and
  [9962](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9962).

- source check:
  the removed primitive-FL theorem is explicitly marked stale because it would
  speak about the zero extension off the tube, not the true boundary value;
- source check:
  the live theorem-3 boundary object is the chosen scalar trace
  `bvt_singleSplit_xiShiftHolomorphicValue`;
- source check:
  the public theorem-3 consumers now expose only the Wightman-side limit
  hypothesis `hHlimit` for that trace;
- source check:
  `section43_fixedPair_upperHalfPlaneScalarization` is already present, so the
  next missing theorem is lower in the fixed-time shell limit, not in witness
  construction.

- reading conclusion:
  the theorem-3 frontier has been rebound from a false primitive-FL real-edge
  continuity target to a genuine boundary-trace identification problem;
- refined verdict:
  the smallest honest next theorem-sized step now exposed is the limit-level
  ambient-vs-source shell comparison beneath `hlimit_os`, specifically the
  outside-region contribution on the actual canonical shell.

Supervision correction (`2026-04-16`, reread note after the narrow post-relocation consumer probe):
this pass is docs-only after reverting the temporary probe theorem.

- reread the upstream source location of
  `forwardConeAbs_salient`
  in
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:488](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:488);
- then ran the exact consumer-side probe compile on
  `OSReconstruction/SCV/VladimirovTillmann.lean`.

- source check:
  the salientness theorem text is now in the upstream forward-tube file;
- source check:
  nevertheless the live consumer-side probe still fails to resolve the name
  `forwardConeAbs_salient`;
- verification note:
  `lake env lean OSReconstruction/SCV/VladimirovTillmann.lean`
  on `2026-04-16` exited `1` with decisive error
  `unknown identifier 'forwardConeAbs_salient'`.

- reading conclusion:
  the salientness relocation did not yet unblock the seam at the name-resolution
  level;
- refined verdict:
  the current blocker is theorem visibility / export on the live import path,
  not a new analytic or trace theorem gap.

Supervision correction (`2026-04-16`, 20:32 UTC, live seam clarification):
- confirmed by source reread that the direct VT -> forward-consumer step already exists as
  `distributional_uniqueness_forwardTube_of_trace_from_vt_bvZero`
  in `OSReconstruction/SCV/VladimirovTillmann.lean`;
- therefore the corrected live frontier is no longer a missing theorem near
  `distributional_uniqueness_forwardTube_of_flatTempered_of_trace`;
- the exact remaining theorem-sized blocker is upstream availability of
  `forwardConeAbs_salient`, whose current home in
  `WickRotation/ForwardTubeLorentz.lean`
  is too downstream / cyclic for the live seam;
- next honest bounded step: move or reproved
  `IsSalientCone (ForwardConeAbs d n)`
  in a non-cyclic upstream layer, then retry the VT supplier -> consumer discharge if needed.

Supervision correction (`2026-04-16`, reread note for the live forward-tube consumer seam rather than the stale theorem-1 seam):
this pass is docs-only.

- reread
  `vladimirov_tillmann_hasFourierLaplaceReprTempered`
  and
  `distributional_uniqueness_forwardTube_of_trace_from_vt_bvZero`
  in
  [OSReconstruction/SCV/VladimirovTillmann.lean:672](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:672)
  and
  [902](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:902);
- reread the first actual flattened consumer in
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:821](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:821)
  and its `_from_bvZero` wrapper at
  [1373](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:1373);
- reread the import headers of
  [OSReconstruction/SCV/VladimirovTillmann.lean:1](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:1)
  and
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:1](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:1).

- source check:
  the direct VT-to-consumer theorem already exists in the tree;
- source check:
  it builds the flattened tempered package from genuine forward-tube VT
  hypotheses and feeds it directly to the first real consumer;
- source check:
  the reason the same theorem is not housed in
  `ForwardTubeDistributions.lean`
  is import layering, not a missing proof.

- reading conclusion:
  there is no remaining theorem-sized mathematical blocker on the corrected
  forward-tube seam;
- refined verdict:
  the next honest task, if this theorem must move nearer the consumer, is a
  shared seam file / import refactor between
  `ForwardTubeDistributions`
  and
  `VladimirovTillmann`,
  not another wrapper theorem.

Supervision correction (`2026-04-16`, reread note after the failed direct VT-to-consumer theorem attempt):
this pass is docs-only.

- reread
  `SCV.vladimirov_tillmann_hasFourierLaplaceReprTempered`
  in
  [OSReconstruction/SCV/VladimirovTillmann.lean:672](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:672);
- reread the first live forward-tube consumer
  `distributional_uniqueness_forwardTube_of_flatTempered_of_trace`
  and its zero-BV variant in
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:821](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:821)
  and
  [1373](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:1373);
- reread the forward-cone geometry available in the same file, especially
  `forwardConeAbs_isOpen`,
  `forwardConeAbs_convex`,
  and
  `forwardConeAbs_smul`;
- source check:
  the direct theorem attempt only failed at the missing salientness witness for
  `ForwardConeAbs d n`;
- source check:
  the needed theorem exists, but only downstream in
  `WickRotation/ForwardTubeLorentz.lean`, which imports
  `SCV/VladimirovTillmann.lean`, so it cannot be reused here without a cycle.

- reading conclusion:
  the exact first forward-tube theorem-sized blocker is now
  upstream availability of
  `IsSalientCone (ForwardConeAbs d n)`;
- refined verdict:
  once `forwardConeAbs_salient` is moved/proved in
  `ForwardTubeDistributions.lean` or an earlier import layer, the direct
  VT-tempered supplier can feed the first forward-tube consumer with no further
  theorem-sized seam change.

- verification note:
  `lake env lean OSReconstruction/SCV/VladimirovTillmann.lean`
  on `2026-04-16` failed on the attempted theorem with
  `unknown identifier 'forwardConeAbs_salient'`;
  the theorem attempt was then reverted.

Supervision correction (`2026-04-16`, reread note after identifying the honest stronger theorem-1 input on the OS route):
this pass is no longer docs-only.

- reread
  `HasFourierLaplaceReprTempered`,
  `HasFourierLaplaceReprRegular`,
  and the `uniform_bound` commentary in
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118),
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143),
  and
  [181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:181);
- reread the live theorem-1 surface at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3440](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3440);
- reread the VT upstream growth hypotheses in
  [OSReconstruction/SCV/VladimirovTillmann.lean:149](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:149)
  and
  [461](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/VladimirovTillmann.lean:461).

- source check:
  theorem 1 cannot be a bare-support theorem after the half-line example;
- source check:
  the actual OS/Vladimirov route already assumes stronger input,
  namely a global polynomial bound on the whole tube;
- source check:
  that stronger input directly gives the needed raywise `uniform_bound`, and
  this has now been added as
  `SCV.uniform_bound_near_boundary_of_global_poly_growth`
  in `LaplaceSchwartz.lean`.

- reading conclusion:
  the smallest honest stronger theorem-1 seam is
  `global tube growth ⇒ uniform_bound`;
- refined verdict:
  the OS route should derive `hunif` from that stronger input and then package
  it into `HasFourierLaplaceReprTempered`, rather than continue trying to prove
  theorem 1 from bare `HasFourierSupportInDualCone`.

Supervision correction (`2026-04-16`, reread note after checking theorem 1 against the half-line support example):
this pass is docs-only.

- reread
  `HasFourierSupportInDualCone`
  and
  `tflat_pairing_eq_of_eqOn_dualCone`
  in
  [OSReconstruction/SCV/FourierSupportCone.lean:73](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:73)
  and
  [113](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:113);
- reread the theorem-1 caller and its current hypotheses in
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3440](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3440);
- reread the package contract where `uniform_bound` is treated as extra
  regularity in
  [OSReconstruction/SCV/LaplaceSchwartz.lean:104](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:104)
  and
  [263](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:263).

- source check:
  bare dual-cone support only gives qualitative localization;
- source check:
  for the standard one-dimensional cone, the supported tempered distribution
  `1_[0,∞)` produces the Fourier-Laplace transform `1 / (ε - i x)`, so the
  theorem-1 style `ε`-uniform bound fails already at `x = 0`;
- source check:
  this means the sought “support-adapted continuity from bare support” theorem
  cannot exist in the needed strength.

- reading conclusion:
  the first honest blocker is earlier than the previously recorded continuity
  seam;
- refined verdict:
  before theorem 1 can progress, source must identify and add the extra
  regularity hypothesis beyond bare `HasFourierSupportInDualCone` that rules
  out the half-line counterexample and only then seek a support-adapted
  continuity estimate under that stronger input.

- verification note:
  `lake env lean OSReconstruction/SCV/PaleyWienerSchwartz.lean` was launched on
  `2026-04-16`, but this note does not claim compile-clean output from that
  still-running probe.

Supervision correction (`2026-04-16`, reread note after checking the theorem-1 caller against the actual support predicate):
this pass is docs-only.

- reread
  `multiDimPsiZR_eval_eq_of_support`,
  `schwartz_clm_bound_by_finset_sup`,
  and
  `fourierLaplaceExtMultiDim_uniform_bound_near_boundary`
  in
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:2990](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:2990)
  and
  [3440](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3440);
- reread
  `HasFourierSupportInDualCone`,
  `hasFourierSupportIn_eqOn`,
  and
  `tflat_pairing_eq_of_eqOn_dualCone`
  in
  [OSReconstruction/SCV/FourierSupportCone.lean:73](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/FourierSupportCone.lean:73);
- source check: the support hypothesis currently gives only qualitative
  vanishing/equality-on-`C*` transport, not a quantitative estimate for
  `|T f|`;
- source check: theorem 1 still begins by invoking the generic finite-sup
  continuity bound for Schwartz space, so any kernel-side improvement still has
  to pass through a support-blind family of full Schwartz seminorms.

- reading conclusion:
  the first honest blocker is earlier than the radius-explicit seminorm package;
- refined verdict:
  source first needs a support-adapted continuity estimate for
  Fourier-supported functionals, not another theorem that only improves
  `multiDimPsiZR` while leaving the same `schwartz_clm_bound_by_finset_sup`
  consumer unchanged.

- verification note:
  `lake env lean OSReconstruction/SCV/PaleyWienerSchwartz.lean`
  on `2026-04-16` exited `0` and still reports the live `sorry` warning at
  line `3440`.

Supervision correction (`2026-04-16`, reread note after checking the candidate raywise seminorm statement against the actual kernel):
this pass is no longer docs-only.

- reread
  `schwartz_clm_bound_by_finset_sup`,
  `multiDimPsiZR_eval_eq_of_support`,
  and
  `fourierLaplaceExtMultiDim_uniform_bound_near_boundary`
  in
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:2990)
  and
  [3440](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3440);
- reread
  `psiZRaw_eq_on_dualCone`
  and
  `cexp_bound_on_support`
  in
  [OSReconstruction/SCV/ConeCutoffSchwartz.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/ConeCutoffSchwartz.lean:153)
  and
  [504](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/ConeCutoffSchwartz.lean:504);
- source check: for `R = ε⁻¹` and `z = x + i ε η`, the cutoff is exactly `1`
  on `DualConeFlat C`, so along any dual-cone ray the kernel is just
  `exp(i x·ξ - ε η·ξ)`;
- source check: therefore the weighted zeroth-derivative seminorm profile is
  already `t^k exp(-ε a t)`, which blows like `ε⁻k` for every `k > 0`.

- reading conclusion:
  the previously targeted “uniform full-Schwartz seminorm supplier” is false;
- refined verdict:
  the first honest blocker sits one step earlier, in the use of
  `schwartz_clm_bound_by_finset_sup`;
- what current source really lacks is a support-sensitive continuity estimate
  for Fourier-supported functionals that avoids demanding uniform control of
  the positive-weight Schwartz seminorms of the boundary-ray kernel family.

Supervision correction (`2026-04-16`, reread note after checking the actual general-radius kernel estimates):
this pass is no longer docs-only.

- reread
  `cexp_bound_on_support`,
  `psiZRaw_iteratedFDeriv_decay`,
  and
  `psiZRSchwartz`
  in
  [OSReconstruction/SCV/ConeCutoffSchwartz.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/ConeCutoffSchwartz.lean:504);
- reread the dynamic quantitative package and the live target at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:562](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:562)
  and
  [3440](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3440);
- source check: the exponential support estimate already carries explicit
  `R`-dependence, so after fixing `η ∈ C`, choosing coercivity
  `c = ε * cη` for `εη`, and setting `R = ε⁻¹`, the factor
  `exp(((c + K * ‖Im z‖) * R))` becomes `ε`-uniform;
- source check: the actual missing piece is the theorem that packages the
  remaining derivative scaling of `χ(·/R)` and the exponent map into a full
  seminorm estimate for `multiDimPsiZR` on that ray.

- reading conclusion:
  the first blocker is more precise than the previous broad “kernel-side
  estimate” label;
- refined verdict:
  what current source lacks is a radius-explicit quantitative upgrade of the
  qualitative general-radius decay theorem, specialized uniformly to
  `R = ε⁻¹` and `z = x + i ε η`;
- once that theorem exists, the live FL theorem should close directly from the
  already-proved
  `multiDimPsiZR_eval_eq_of_support`
  and
  `schwartz_clm_bound_by_finset_sup`.

Supervision correction (`2026-04-16`, reread note for the live SCV boundary-ray uniform bound theorem):
this pass is no longer docs-only.

- reread the live target
  `fourierLaplaceExtMultiDim_uniform_bound_near_boundary` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3440](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3440):
  it is still the live production `sorry`;
- reread
  `fourierLaplaceExtMultiDim_vladimirov_growth`,
  `fourierLaplaceExtMultiDim_poly_growth_on_compact`,
  and
  `multiDimPsiZDynamic_finset_sup_bound`:
  all current quantitative routes factor through
  `(1 + infDist (Im z, Cᶜ)⁻¹)^M`;
- along the boundary ray `Im z = ε • η`, this becomes a genuine small-`ε`
  blowup and therefore cannot by itself prove the target theorem;
- reread
  `multiDimPsiZR_eval_eq_of_support`:
  this already gives the honest support-based bridge needed to replace the
  radius-`1` kernel by an `ε`-dependent radius choice before applying any
  seminorm estimate.

- reading conclusion:
  the theorem is not blocked by a downstream boundary-value interface;
  it is blocked one step earlier by missing quantitative control of the
  general-radius kernel itself on the small-`ε` ray;
- refined verdict:
  the first honest supplier is a theorem giving, for fixed `η ∈ C`,
  `ε`-uniform Schwartz seminorm bounds for
  `multiDimPsiZR ... R(ε) ... (x + i ε η)` with a suitable radius
  choice such as `R(ε) = ε⁻¹`;
- once that supplier exists, the current source already has the two remaining
  ingredients needed to close the live theorem:
  `multiDimPsiZR_eval_eq_of_support`
  and
  `schwartz_clm_bound_by_finset_sup`.

- verification note:
  `lake env lean OSReconstruction/SCV/PaleyWienerSchwartz.lean`
  on `2026-04-16` succeeded and still reports the live `sorry` warning at
  line `3440`.

Supervision correction (`2026-04-16`, reread note after verifying the current live SCV seam in source):
this pass is no longer docs-only.

- reread the primitive definition
  `fourierLaplaceExtMultiDim` in
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052):
  it is explicitly `if hz : z ∈ TubeDomain C then ... else 0`;
- reread the seam note at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3236](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3236):
  the stale theorem
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` has been removed;
- reread the BV package around
  `hχf`, `hΦ_eq_hε`, `hTΦ_lim_to_cutoff`, and `hThχf_eq`:
  the real primitive boundary object is the tempered functional carried by
  `T (physicsFourierFlatCLM f)`, with the cutoff Schwartz representative
  `hχf := χ · physicsFourierFlatCLM f` appearing in the damping proof;
- reread the forward-tube consumer at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  it now takes an explicit flattened-side `htrace_boundary` hypothesis and no
  longer points back to the removed stale theorem.

- reading conclusion:
  the exact live answer at this seam is that the old theorem surface was
  unnecessary and has already been demoted/removed;
- refined verdict:
  no new primitive pointwise continuity theorem should be added here unless a
  separate boundary trace object is explicitly introduced;
- verification note:
  current-tree probes on `2026-04-16`
  `lake env lean OSReconstruction/SCV/PaleyWienerSchwartz.lean`
  and
  `lake env lean OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`
  both succeeded, with only the known unrelated warnings remaining.

Supervision correction (`2026-04-16`, reread note after removing the stale primitive real-edge continuity theorem surface):
this pass is no longer docs-only.

- reread `fourierLaplaceExtMultiDim` and the deleted
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` surface in
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052)
  and
  [3235](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3235):
  the zero-extension continuity target was stale and has now been removed;
- reread the BV-limit package near
  `regularizedKernel_pointwise` and `hχf = χ · physicsFourierFlatCLM f`:
  the primitive source already packages the honest tempered boundary object,
  not a pointwise real-edge value of the zero extension;
- the repaired forward-tube seam no longer consumes this stale theorem surface,
  because it now takes an explicit `htrace_boundary`.

- reading conclusion:
  the honest primitive interface at this seam is distributional/tempered only;
- refined verdict:
  no primitive pointwise `ContinuousWithinAt` theorem for
  `fourierLaplaceExtMultiDim` should remain in production under the current
  hypotheses.

- verification note:
  `lake env lean OSReconstruction/SCV/PaleyWienerSchwartz.lean`
  on `2026-04-16` succeeded and reports only pre-existing warnings, including
  the existing `sorry` warning at line `3440`.

Supervision correction (`2026-04-16`, reread note after repairing the live flat-FL point boundary theorem contract):
this pass is no longer docs-only.

- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point`
  at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  the old `hrepr_boundary` hypothesis was the wrong object, because it matched
  the forward-tube boundary value to the zero-extended primitive FL function at
  the real point;
- the theorem now instead consumes the honest flattened-side boundary
  `nhdsWithin` trace to `F(real x)`;
- with that input, the proof is just flatten/unflatten transport plus
  `hrepr_tube`.

- reading conclusion:
  the live seam was a contract problem, not an unresolved SCV continuity proof;
- refined verdict:
  the correct first missing mathematics, if a stronger downstream theorem later
  wants to discharge this hypothesis automatically, is a theorem producing the
  flattened-side boundary trace limit to a separate boundary value, not
  continuity of the zero-extended `fourierLaplaceExtMultiDim` at `realEmbed x`;
- verification note:
  `lake env lean OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`
  on `2026-04-16` now reports only the known deprecation warning at line `177`.

Supervision correction (`2026-04-16`, reread note after the source-first replay of the live flat-FL boundary continuity seam):
this pass is docs-only.

- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point`
  at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  the theorem surface is exactly a transport shell around flat SCV boundary
  continuity;
- reread
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed`
  at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  this remains the first unresolved supplier theorem;
- reread
  `fourierLaplace_boundary_recovery_on_open_of_tempered`
  and
  `eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`:
  both remain downstream consumers of already-available boundary continuity on
  an open real set, so neither can create the needed pointwise
  `ContinuousWithinAt` statement.

- reading conclusion:
  the live forward-tube theorem is still not the first missing mathematics;
- refined verdict:
  the first missing theorem remains FL-side boundary continuity of
  `fourierLaplaceExtMultiDim` at the real boundary point;
- verification note:
  `lake env lean OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`
  on `2026-04-16` still reports only the known deprecation warning at line
  `177` and the live `sorry` warning at line `688`.

Supervision correction (`2026-04-16`, reread note for the remaining flat-FL point boundary continuity seam):
this pass is docs-only.

- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point`
  at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  the theorem surface already contains exactly the data needed for a transport
  proof once the flat FL extension is known continuous at the corresponding
  real point;
- reread
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  this is the matching SCV supplier theorem, and it is still the unresolved
  theorem-level `sorry`;
- reread
  `fourierLaplace_boundary_recovery_on_open_of_tempered` and
  `eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`:
  both operate on open real neighborhoods after continuity is already present
  there, so they cannot create the needed single-point `ContinuousWithinAt`
  statement from the present theorem surface.

- reading conclusion:
  the current forward-tube theorem is not the first missing mathematics;
  it is a consumer of the unresolved SCV pointwise boundary continuity theorem;
- refined verdict:
  the exact first missing theorem remains FL-side boundary continuity of
  `fourierLaplaceExtMultiDim` at `realEmbed x`.

Supervision correction (`2026-04-16`, reread note after switching the old regular BV-zero caller in place):
this pass records the closure of the previously isolated caller-side trace transport seam.

- reread `distributional_uniqueness_forwardTube_of_flatRegular_from_bvZero` in
  `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`:
  it no longer closes through
  `distributional_uniqueness_forwardTube_of_flatRegular`;
- the theorem now keeps its old public surface but internally reroutes through
  `distributional_uniqueness_forwardTube_of_flatTempered_of_trace`;
- the proof uses the regular package only as supplier data:
  `boundary_function_continuous_forwardTube_of_flatRegular` for the real trace
  `B`,
  `tube_continuousWithinAt` transported to the full boundary `nhdsWithin`
  trace,
  and direct field reuse to build the tempered package on the same flattened
  difference.

- reread conclusion:
  the exact obstruction noted in the previous docs is now resolved without a
  new theorem surface;
- the transport really was just flatten/unflatten bookkeeping plus definitional
  reuse of the boundary functional field.

Supervision correction (`2026-04-16`, reading note after landing the public forward-tube trace BV-zero caller):
this pass records the next exact seam.

- `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean` now contains the compile-clean theorem
  `distributional_uniqueness_forwardTube_of_flatTempered_of_trace_from_bvZero`
  at line `1263`;
- reread its proof route:
  it builds the zero BV flattened representation from `h_agree`,
  identifies its boundary functional with the given flattened tempered package via
  `fourierLaplace_repr_dist_unique`,
  proves the flattened tempered boundary functional vanishes,
  and then invokes
  `distributional_uniqueness_forwardTube_of_flatTempered_of_trace`;
- this is the smallest honest public forward-tube consumer step opened by
  `distributional_uniqueness_tube_of_tempered_of_trace`.

- reread the neighboring old theorem
  `distributional_uniqueness_forwardTube_of_flatRegular_from_bvZero`:
  it still closes through the regular package and therefore is no longer the
  first downstream seam;
- reading conclusion:
  the frontier has moved one step further downstream;
- refined verdict:
  the next exact missing caller-side theorem is a full boundary
  `nhdsWithin` trace supplier for a separate forward-tube boundary object `B`.

Supervision correction (`2026-04-16`, reading note after landing the first downstream trace-based uniqueness theorem):
this pass records the new exact consumer seam.

- `OSReconstruction/SCV/DistributionalUniqueness.lean` now contains the
  compile-clean theorem
  `distributional_uniqueness_tube_of_tempered_of_trace`
  at line `1954`;
- reread its proof route: it first uses
  `boundary_trace_zero_of_tempered_of_trace` to kill the separate real trace
  `B`, then rewrites the full boundary-limit hypothesis
  `F → B` to `F → 0`, and finally applies
  `uniqueness_of_boundary_trace_zero`;
- this is the first exact downstream consumer of the new trace-zero bridge, and
  it sits at the right seam: adjacent to regular uniqueness, but without
  redesigning `HasFourierLaplaceReprRegular`.

- reread the forward-tube consumers in
  `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`:
  the file still calls the regular uniqueness theorem at line `816`, and the
  public derived theorem
  `distributional_uniqueness_forwardTube_of_flatRegular_from_bvZero`
  at line `1158` still depends on that route;
- reading conclusion:
  the new obstruction is no longer "no consumer theorem exists", but the exact
  missing caller hypothesis that would let forward-tube uniqueness switch over;
- refined verdict:
  the forward-tube side still lacks a theorem supplying full flattened boundary
  `nhdsWithin` convergence to a separate trace object.

Supervision correction (`2026-04-16`, reading note after landing the first trace-zero consumer bridge):
this pass records the new live seam.

- `OSReconstruction/SCV/TubeDistributions.lean` now contains the compile-clean theorem
  `boundary_trace_zero_of_tempered_of_trace`;
- the theorem uses the honest split boundary interface already exposed by
  `LocalBoundaryRecovery`: tempered package for the interior holomorphic object,
  separate continuous real trace `G`, and one-direction interior convergence to
  `G`;
- the conclusion is pointwise vanishing of `G` from vanishing of the tempered
  boundary functional, so this is the first actual downstream consumer bridge
  above the local seam;
- the next seam is no longer "does a separate-trace consumer theorem exist?"
  but "which exact first downstream caller should consume that theorem?";
- likely candidates remain the first regular/forward-tube consumers, but the next
  pass should stay theorem-sized and avoid redesigning `HasFourierLaplaceReprRegular`.

Supervision correction (`2026-04-16`, reading note for the first downstream boundary-interface consumer above the primitive FL seam):
this pass is docs-only.

- reread `HasFourierLaplaceReprRegular` / `HasFourierLaplaceReprTempered` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  and
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143):
  the regular package adds global boundary continuity fields for the same function `F`, while the tempered package stops short of any pointwise boundary object claim;
- reread `fourierLaplace_schwartz_integral_convergence_local` and
  `fourierLaplace_boundary_recovery_on_open_of_tempered` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:105](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:105)
  and
  [156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156):
  source already uses the honest split interface
  `HasFourierLaplaceReprTempered` + explicit local `hcontU`, so this file is not the first wrong-object consumer;
- reread `boundary_value_zero_of_regular` / `distributional_uniqueness_tube_of_regular` at
  [OSReconstruction/SCV/TubeDistributions.lean:78](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeDistributions.lean:78)
  and
  [95](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeDistributions.lean:95):
  these are the first explicit downstream regular consumers of the global boundary fields;
- reread the forward-tube regular transport at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:722](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:722):
  it also consumes `HasFourierLaplaceReprRegular` for the same flattened function.

- reading conclusion:
  the zero-extension discovery does not force a new local theorem in `LocalBoundaryRecovery`; it forces an upstream interface redesign above the primitive FL witness and before the regular-package consumers;
- refined verdict:
  the first wrong-object interface is `HasFourierLaplaceReprRegular F` itself when `F` is taken to be `fourierLaplaceExtMultiDim ... T`;
- exact next contract decision:
  introduce a separate boundary-trace representative `G` with interior agreement and put any regular package on `G`, or stay on the local-tempered route until that representative is defined.

Supervision correction (`2026-04-16`, reading note for the exact pointwise ray-limit probe):
this pass is docs-only.

- reread the exact extension definitions at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:279](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:279)
  and
  [3052](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052):
  both `multiDimPsiZExt` and `fourierLaplaceExtMultiDim` are extended by `0`
  outside `TubeDomain C`;
- reread
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  the live placeholder still asks for continuity of that exact outside-tube
  extension at `realEmbed x`;
- reread
  `realPlusIEpsEta_mem_tubeDomain` at
  [3616](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3616)
  and
  `realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [3631](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3631):
  the ray really approaches the boundary from inside the tube;
- reread
  `regularizedKernel_pointwise` at
  [3737](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3737)
  through
  [3827](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3827):
  its damping factor is exactly the same one obtained by directly unfolding the
  interior ray kernel
  `ξ ↦ χ(ξ) * exp(-(ε : ℂ) * ⟪η, ξ⟫) * exp(I * ⟪x, ξ⟫)`.

- reading conclusion:
  as `ε → 0+`, the primitive interior kernel tends to the nonzero cutoff
  oscillatory Schwartz function `ξ ↦ χ(ξ) * exp(I * ⟪x, ξ⟫)`;
- refined verdict:
  this does not match the current target
  `fourierLaplaceExtMultiDim ... (realEmbed x)`, because the exact extension is
  `0` at the boundary by definition;
- landing conclusion:
  no honest compile-clean Lean helper landed, because the seam has become a
  target-object contract problem rather than a missing local limit proof.

Supervision correction (`2026-04-16`, reread note for theorem-1 internal-proof-fragment probe):
this pass is docs-only.

- reread the theorem-1 skeleton at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3444](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3444)
  through
  [3455](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3455):
  the target is still exactly the `hunif` field shape with constants
  independent of `ε` for all `0 < ε < δ`;
- reread the upstream growth theorem at
  [3304](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304)
  and the ray-membership lemma at
  [3616](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3616):
  the first internal proof step is straightforward specialization of
  Vladimirov growth to `z = x + i ε η`;
- reread the cone-scaling lemma at
  [OSReconstruction/SCV/ConeCutoffSchwartz.lean:60](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/ConeCutoffSchwartz.lean:60):
  it gives the exact scaling
  `Metric.infDist (ε • η) Cᶜ = ε * Metric.infDist η Cᶜ`;
- reread the older slice theorem at
  [OSReconstruction/SCV/TubeBoundaryValueExistence.lean:220](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeBoundaryValueExistence.lean:220):
  that file already formalizes the fixed-`ε` conclusion honestly, namely
  polynomial growth of `x ↦ F(x + i ε η)` with a constant depending on `ε`;
- mutool extraction of
  `references/reconstruction theorem II.pdf`, printed pages `302`-`303`,
  confirms again that `(6.21)`, `(6.28)`, `(6.30)`, `(6.31)` speak about the
  renormalized `S_{k,\varepsilon}` family and the final temperedness estimate,
  not about a primitive theorem already matching the live Lean seam.

- reading conclusion:
  the only immediate internal fragment available below theorem 1 is the
  specialized Vladimirov ray estimate with an `ε`-dependent coefficient;
- refined verdict:
  that fragment is not an honest landing because it does not reduce the real
  blocker and would only package the wrong asymptotic behavior for the
  `uniform_bound` contract;
- next missing theorem-contract gap:
  replace the factor
  `(1 + (Metric.infDist (ε • η) Cᶜ)⁻¹)^M`
  by a bound uniform for `0 < ε < δ` on the primitive
  `fourierLaplaceExtMultiDim ... T` route.

Supervision correction (`2026-04-16`, reading note for the theorem-1 first-blocking-obligation probe):
this pass is docs-only.

- reread the focused primitive seam:
  `fourierLaplaceExtMultiDim_vladimirov_growth` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304),
  `fourierLaplaceExtMultiDim_poly_growth_on_compact` at
  [3342](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3342),
  theorem-1 skeleton
  `fourierLaplaceExtMultiDim_uniform_bound_near_boundary` at
  [3444](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3444),
  `realPlusIEpsEta_mem_tubeDomain` at
  [3616](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3616),
  `realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [3631](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3631),
  and the BV warning comment at
  [4425](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4425);
- reread the exact `hunif` consumer at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:921](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:921)
  through
  [924](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:924):
  the package still asks for the full theorem-1 raywise `ε`-uniform bound
  verbatim.

- paper reread by local extraction:
  `references/reconstruction theorem II.pdf`,
  PDF page `22` / printed page `302` gives `(6.21)` and `(6.28)`,
  and PDF page `23` / printed page `303` gives the maximum-principle step,
  `(6.30)`, and `(6.31)`;
- reading conclusion:
  those equations still belong to the renormalized `S_{k,\varepsilon}` family,
  not to an already formalized primitive sublemma for
  `fourierLaplaceExtMultiDim ... T`.

- refined blocker conclusion:
  the first honest missing obligation is still to prove theorem 1 itself;
- exact reason:
  after substituting `z = x + i ε η` into Vladimirov growth, the unresolved task
  is to eliminate the inverse-distance factor
  `(1 + (Metric.infDist (ε • η) Cᶜ)⁻¹)^M` uniformly as `ε → 0+`;
- nearby proved facts do not shrink that task:
  compact-slice growth needs fixed compact `K ⊆ C`,
  tube-membership/path lemmas give only approach geometry,
  and the boundary-value theorem is only distributional and explicitly allows
  pointwise blowup.

- landing conclusion:
  no honest compile-clean Lean lemma landed on this pass;
  the next insertion seam remains the existing theorem-1 skeleton in
  `PaleyWienerSchwartz.lean`.

Supervision correction (`2026-04-16`, reading note after the local OS II dependency probe beneath theorem 1):
this pass is docs-only.

- reread the exact `hunif` consumer at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:921](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:921)
  through
  [924](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:924):
  theorem 1 is still precisely the raywise bound
  `‖F(x+iεη)‖ ≤ C_bd * (1 + ‖x‖)^N` for all `0 < ε < δ`;
- reread the local primitive seam in
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241)
  through
  [3352](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3352):
  the live source still consists of the blocked boundary-continuity theorem, the
  proved Vladimirov growth theorem, and the proved compact-slice `hpoly`
  corollary;
- reread the ray-path theorem at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3612](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3612)
  through
  [3646](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3646):
  it gives only the approach map
  `ε ↦ x + i ε η` into `nhdsWithin (realEmbed x) (TubeDomain C)`;
- reread the nearby warning comment at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:4405](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4405)
  through
  [4408](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4408):
  source itself still warns that `F(x+iεη)` may blow up as `ε → 0+`;
- reread `references/reconstruction theorem II.pdf`, PDF page `22` / printed
  page `302`:
  OS II defines the renormalized family `S_{k,ε}` in `(6.21)` and proves the
  inductive Banach-valued estimate `(6.28)`;
- reread `references/reconstruction theorem II.pdf`, PDF page `23` / printed
  page `303`:
  the proof uses the maximum principle to propagate `(6.28)`, then picks
  `N = N(ζ)` by `(6.30)`, and finishes with the temperedness estimate `(6.31)`.

- reading conclusion:
  the only smaller source-visible ingredient beneath theorem 1 is OS II’s
  renormalized-family estimate `(6.28)` plus the pointwise `N(ζ)` step;
- refined verdict:
  that ingredient is not a genuine smaller theorem on the current primitive Lean
  route, because the live seam formalizes `fourierLaplaceExtMultiDim ... T`
  directly and does not currently contain the renormalized `S_{k,ε}` family;
- landing conclusion:
  no honest compile-clean non-wrapper Lean theorem emerged, so theorem 1 itself
  remains the first honest missing analytic package and this pass stays docs-only.

Supervision correction (`2026-04-16`, bounded reread on theorem 1 after the tempered-supplier blocker):
this pass is docs-only.

- reread
  `HasFourierLaplaceReprTempered.uniform_bound` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:151](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:151)
  through
  [154](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:154):
  the exact theorem-1 target is still the live `hunif` field shape
  `∀ η ∈ C, ∃ C_bd N δ, ... ‖F(x+iεη)‖ ≤ C_bd * (1 + ‖x‖)^N`;
- reread
  `exists_fourierLaplaceReprTempered` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:907](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:907):
  the first primitive supplier theorem still needs exactly four real inputs,
  namely:
  the composite continuity witness,
  `fourierLaplaceExtMultiDim_boundaryValue`,
  `fourierLaplaceExtMultiDim_poly_growth_on_compact`,
  and theorem 1 as `hunif`;
- reread
  `fourierLaplaceExtMultiDim_boundaryValue` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288):
  the currently proved boundary theorem is still distributional only;
- reread
  `fourierLaplaceExtMultiDim_poly_growth_on_compact` at
  [3342](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3342):
  the compact-slice `hpoly` input remains fully live;
- reread
  `realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [3510](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510):
  the path-to-boundary theorem is proved, but it is not itself theorem 1;
- reread
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  it is still `sorry`, so it is not an available ingredient for the present
  bounded task;
- reread
  `fourierLaplaceExtMultiDim_vladimirov_growth` at
  [3304](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304):
  after substituting `z = x + i ε η`, the estimate still carries the inverse
  boundary-distance factor, so it does not match the `hunif` field shape;
- reread the nearby source comment at
  [4303](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4303):
  source itself still warns that `F(x+iεη)` may blow up as `ε → 0+`;
- reread the cited OS II page by local extraction:
  file page `23` / printed page `303`, equation `(6.31)`, still reads as a
  temperedness estimate with boundary-variable dependence, not theorem-1’s
  `ε`-uniform ray bound in `x`.

- reading conclusion:
  the exact theorem-1 statement is now fixed at the `hunif` field shape and the
  available primitive FL inputs are exactly the distributional BV theorem, the
  compact-slice `hpoly` theorem, and the ray-path theorem;
- refined verdict:
  no honest compile-clean non-wrapper theorem-sized Lean step surfaced at the
  checked `PaleyWienerSchwartz.lean` seam, so this pass stays docs-only;
- placement conclusion:
  keep theorem 1 at the `PaleyWienerSchwartz.lean` near-boundary frontier, while
  the first primitive `HasFourierLaplaceReprTempered` supplier in
  `LaplaceSchwartz.lean` remains blocked exactly by that missing input.

Supervision correction (`2026-04-16`, reread note after the live compact-slice `hpoly` landing):
this pass is docs-only.

- reread
  `fourierLaplaceExtMultiDim_poly_growth_on_compact` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3342](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3342):
  the compact-slice `hpoly` input for the tempered package is now already in
  source, so it is no longer the blocker at the supplier seam;
- reread
  `exists_fourierLaplaceReprTempered` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:907](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:907):
  the exact remaining supplier theorem right after this definition must package
  the primitive function
  `fourierLaplaceExtMultiDim ... T`
  with boundary functional
  `fun f => T (physicsFourierFlatCLM f)`;
- reread
  `fourierLaplaceExtMultiDim_boundaryValue` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:4390](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4390):
  this gives exactly the boundary-value input needed for that supplier, landing
  in `nhds (T (physicsFourierFlatCLM f))`;
- reread
  `physicsFourierFlatCLM` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3476](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3476):
  together with `T.continuous`, it gives the exact continuity witness
  `hT_cont` for the supplier as the continuous composite
  `fun f => T (physicsFourierFlatCLM f)`;
- reread the `hunif` field shape at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:921](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:921)
  through
  [924](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:924):
  theorem 1 is still the exact missing input preventing the first primitive
  `HasFourierLaplaceReprTempered` theorem from being hypothesis-free.

- reading conclusion:
  the exact remaining supplier theorem is now fully determined from source;
- refined verdict:
  without theorem 1, the only compile-clean Lean step left is a conditional
  repackaging theorem through `exists_fourierLaplaceReprTempered`, which is
  wrapper-only and therefore not an honest landing for this pass;
- insertion seam conclusion:
  keep the supplier seam immediately after
  `exists_fourierLaplaceReprTempered` in `LaplaceSchwartz.lean`.

Supervision correction (`2026-04-16`, reread note on the exact theorem-1 source/probe loop):
this pass is docs-only.

Supervision correction (`2026-04-16`, reread note on the exact downstream chain immediately after theorem 1):
this pass is docs-only.

Supervision correction (`2026-04-16`, reread note for the theorem-1 statement-or-skeleton probe):
this pass is docs-only.

- reread the primitive FL seam at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3438](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3438)
  through
  [3455](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3455):
  the exact theorem-1 statement is already present there as the theorem/skeleton
  `fourierLaplaceExtMultiDim_uniform_bound_near_boundary`;
- reread the package consumer at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:921](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:921)
  through
  [924](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:924):
  the skeleton matches the `hunif` field exactly, with no wrapper drift;
- reread printed pages `302`-`303` of
  `references/reconstruction theorem II.pdf`:
  `(6.21)`, `(6.28)`, `(6.30)`, `(6.31)` still support only the renormalized
  OS II proof route and do not reveal a smaller primitive helper theorem on the
  live Lean seam.

- reading conclusion:
  the single honest theorem-sized landing at package level already exists;
- refined verdict:
  no new Lean edit is honest on this bounded pass, because duplicating the
  theorem-1 skeleton would add no mathematics and no smaller source-backed
  helper surfaced;
- next obligation:
  prove the existing theorem-1 skeleton honestly, or keep the frontier recorded
  as blocked exactly there.

- reread
  `exists_fourierLaplaceReprTempered` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:907](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:907):
  the would-be primitive theorem yielding `HasFourierLaplaceReprTempered`
  cannot honestly land before theorem 1, because the constructor still asks
  for explicit `hunif` at
  [921](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:921)
  through
  [924](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:924);
- reread
  `fourierLaplace_schwartz_integral_convergence_local` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:105](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:105):
  the first local DCT recovery step immediately unpacks
  `hTempered.uniform_bound` at
  [120](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:120);
- reread
  `fourierLaplace_boundary_recovery_on_open_of_tempered` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156):
  it depends directly on that convergence theorem at
  [172](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:172);
- reread
  `fourierLaplaceExtMultiDim_vladimirov_growth` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304):
  after theorem 1, the next genuinely source-backed theorem is the compact-slice
  `poly_growth` corollary obtained by bounding the boundary-distance factor on
  compact `K ⊆ C`;
- reread
  `HasFourierLaplaceReprTempered.poly_growth` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:146](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:146):
  this shows why that compact-slice corollary is the sharp smaller theorem
  strictly between theorem 1 and the first honest package theorem;
- reread the regular placeholder comment at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:180](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:180):
  the first honest boundary-continuity theorem after the tempered package is
  still a boundary-valued representative theorem yielding some `G` with
  `HasFourierLaplaceReprRegular C G`, not the current zero-extension continuity
  target in `PaleyWienerSchwartz.lean`.

- reading conclusion:
  the sharp next theorem after theorem 1 is option `B(3)`, the compact-slice
  primitive `poly_growth` theorem;
- refined chain:
  theorem 1
  `->` compact-slice `poly_growth`
  `->` first honest primitive theorem yielding `HasFourierLaplaceReprTempered`
  `->` first honest boundary-valued regular representative theorem;
- placement conclusion:
  the compact-slice corollary belongs right after Vladimirov growth in
  `PaleyWienerSchwartz.lean`,
  the tempered-package supplier belongs right after
  `exists_fourierLaplaceReprTempered` in `LaplaceSchwartz.lean`,
  and the first regular-representative theorem belongs at the placeholder
  starting at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:180](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:180).

- reread
  `HasFourierLaplaceReprRegular.uniform_bound` and
  `HasFourierLaplaceReprTempered.uniform_bound` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:126](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:126)
  and
  [151](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:151):
  theorem 1 is exactly the already-live field shape
  `‖F(x+iεη)‖ ≤ C_bd * (1 + ‖x‖)^N`
  for all `0 < ε < δ`;
- reread
  `fourierLaplace_uniform_bound_near_boundary` at
  [263](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:263):
  it is only a field projection from `HasFourierLaplaceReprRegular`;
- reread
  `fourierLaplaceExtMultiDim_vladimirov_growth` and
  `fourierLaplaceExtMultiDim_boundaryValue` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304)
  and
  [4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288):
  source still gives only Vladimirov growth plus distributional boundary values;
- reread the nearby comments at
  [3865](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3865)
  and
  [4303](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4303):
  source itself says the boundary value is not pointwise in general and
  `F(x+iεη)` may blow up as `ε → 0+`;
- reread the cited OS II page:
  local extraction of printed page `303` / equation `(6.31)` is OCR-poor, but
  still matches the supervision reading that the estimate carries a
  boundary-distance factor through the real-part variables, i.e. a standard
  temperedness estimate rather than an `ε`-uniform ray bound in `x`;
- reread `references/Zinoviev_1995.pdf`:
  the local file is an unrelated conifold paper, so it contributes nothing to
  this theorem-1 seam.

- reading conclusion:
  the current source/reference package gives distance-to-boundary growth and
  distributional boundary values, not theorem-1's `ε`-uniform bound in `x`;
- refined verdict:
  theorem 1 itself is the first honest missing analytic theorem here;
- landing conclusion:
  no non-wrapper Lean helper surfaced, so this pass remains docs-only.

Supervision correction (`2026-04-16`, reread note after checking whether a weaker primitive FL package theorem already lands):
this pass is docs-only.

- reread
  `HasFourierLaplaceReprRegular` and `HasFourierLaplaceReprTempered` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  and
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143):
  the extra-hypothesis interface already exists in source;
- reread
  `exists_fourierLaplaceRepr` and `exists_fourierLaplaceReprTempered` at
  [883](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:883)
  and
  [907](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:907):
  the transparent package constructors already exist too, so there is no
  missing tiny constructor theorem worth landing;
- reread
  `fourierLaplaceExtMultiDim_boundaryValue` and its nearby comments at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288)
  and
  [4303](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4303):
  source itself still says `F(x+iεη)` may blow up as `ε → 0+`;
- reading conclusion:
  the candidate smaller theorem
  “primitive FL data gives `HasFourierLaplaceReprTempered`”
  is not source-backed, because that package still requires a uniform
  small-`ε` ray bound;
- refined reading conclusion:
  there is still no honest smaller Lean landing between the current docs and
  the full primitive boundary-regularity theorem;
  the existing regularity structure is already the extra-hypothesis interface,
  and the next real progress must be analytic, not administrative.

Supervision correction (`2026-04-16`, reread note after unfolding the primitive FL target to its definition):
this pass is docs-only.

- reread
  `fourierLaplaceExtMultiDim` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052):
  it is the zero extension outside `SCV.TubeDomain C`;
- reread
  `fourierLaplaceExtMultiDim_eq_ext` at
  [3070](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3070):
  this rewrites the FL extension everywhere as
  `T (multiDimPsiZExt ... z)`;
- reread
  `multiDimPsiZExt` at
  [279](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:279):
  it is also extended by `0` off the tube, so a continuity theorem for
  `multiDimPsiZExt` at a real boundary point would force convergence to the
  zero-extension value there;
- reread
  `HasFourierLaplaceReprRegular` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118):
  source already treats real-boundary continuity as extra structure, not as a
  theorem currently derivable from the weak FL package;
- reread
  `fourierLaplaceExtMultiDim_boundaryValue` at
  [4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288):
  its comments again confirm that the available theorem is distributional-only.

- reading conclusion:
  the previous “maybe a tiny topology helper proves the target” hope fails at
  the statement level;
- refined reading conclusion:
  the first honest smaller gap is a **boundary-valued FL regularity upgrade**,
  not a generic topology lemma and not the same scalar ray-limit theorem under
  a new name;
- placement conclusion:
  that missing upgrade belongs with the upstream Paley-Wiener/Fourier-Laplace
  machinery, using the existing regularity interface in `LaplaceSchwartz.lean`,
  not in the shifted-side caller.

Supervision correction (`2026-04-16`, reread note on the primitive FL scalar ray-limit seam):
this pass is docs-only.

- reread
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  this is exactly the theorem that would convert the canonical ray path into
  the desired scalar limit, but it is still `sorry`;
- reread
  `SCV.realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510):
  the path theorem itself is already fully proved and has the exact filter
  target `nhdsWithin (realEmbed x) (TubeDomain C)`;
- reread
  `SCV.fourierLaplaceExtMultiDim_boundaryValue` and its proof comments at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288)
  and
  [3828](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3828):
  source explicitly says the limit theorem there is distributional-only and
  rejects a pointwise-in-`x` reading;
- reread
  `HasFourierLaplaceReprRegular`,
  `fourierLaplace_schwartz_integral_convergence`,
  and the local analogue in `LocalBoundaryRecovery.lean`:
  every nearby scalar boundary-limit theorem already assumes the same boundary
  continuity field that this seam is trying to prove;
- reading conclusion:
  there is no honest nearby proof of the scalar ray-limit theorem from current
  proved source;
- refined reading conclusion:
  the smallest honest missing lemma is the primitive FL boundary regularity
  statement
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed`,
  and that belongs in `PaleyWienerSchwartz.lean`;
- reading conclusion on edits:
  no honest Lean helper surfaced, so this pass remains docs-only.

Supervision correction (`2026-04-16`, reread note after exact Mathlib/repo check of the real-trace continuity bridge):
this pass is docs-only.

- reread
  `IsOpen.continuousOn_iff` at
  [Mathlib/Topology/ContinuousOn.lean:333](/home/claw/.openclaw/workspace/OSreconstruction/.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:333):
  it only packages
  `ContinuousOn f U ↔ ∀ x ∈ U, ContinuousAt f x`
  for open `U`;
- reread
  `Topology.IsInducing.continuousOn_image_iff` and
  `Topology.IsEmbedding.continuousOn_iff` at
  [Mathlib/Topology/ContinuousOn.lean:823](/home/claw/.openclaw/workspace/OSreconstruction/.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:823)
  and
  [827](/home/claw/.openclaw/workspace/OSreconstruction/.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:827):
  they compare continuity on a set with continuity after composition along an
  embedding/image map, but they do not manufacture boundary-trace continuity
  from ambient `ContinuousWithinAt`;
- reread the seam geometry:
  the available input is
  `ContinuousWithinAt G_t (SCV.TubeDomain ...) (SCV.realEmbed xflat)`,
  where `SCV.realEmbed xflat` is a tube-boundary point;
- reading conclusion:
  there is still no existing source bridge from that boundary statement to
  `ContinuousOn (fun xflat => G_t (SCV.realEmbed xflat)) Uflat`;
- refined reading conclusion:
  the smallest honest missing theorem is not a generic composition lemma, but a
  local trace-continuity theorem on the exact shifted open set `Uflat`;
- failed weaker alternative:
  `refine (hUflat.continuousOn_iff).2 ?_` only repackages the missing pointwise
  `ContinuousAt` theorem for the trace;
- failed wrong-generic alternative:
  embedding/image continuity lemmas do not apply because the trace is taken on
  the boundary of the tube, not along an interior image set where the ambient
  function is already continuous;
- reading conclusion on edits:
  no honest tiny Lean helper surfaced, so this pass remains docs-only.

Supervision correction (`2026-04-16`, reread note on the exact bridge from local-open ambient continuity to the uniqueness consumer):
this pass is docs-only.

- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156):
  it still consumes only
  `∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)`;
- reread
  `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` at
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1507](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1507):
  its continuity inputs are about the real trace functions on `U`, not the
  ambient tube function;
- reread nearby repo uses of `hU.continuousOn_iff`:
  source already has the generic open-set packaging from pointwise
  `ContinuousAt` to `ContinuousOn`, but nothing stronger;
- reading conclusion:
  there is no existing source bridge
  from open-set pointwise ambient `ContinuousWithinAt`
  to `ContinuousOn (fun x => F (realEmbed x)) U`;
- refined reading conclusion on the seam:
  the smallest honest missing theorem is a local boundary-trace continuity
  theorem on the exact shifted `Uflat`, not a wrapper around
  `ContinuousWithinAt` and not a demand for stronger external FL input;
- failed weaker alternative:
  `refine (hUflat.continuousOn_iff).2 ?_` only repackages the obligation and
  leaves the substantive pointwise trace `ContinuousAt` theorem untouched;
- reading conclusion on edits:
  no honest tiny Lean helper surfaced, so this pass remains docs-only.

Supervision correction (`2026-04-16`, reread note on the exact theorem-sized shifted consumer above theorem-(1)`):
this pass is docs-only.

- reread
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`,
  `section43_fixedTimeShellRaw_pointwiseContinuity_on_section43PositiveEnergyRegion_compl`,
  `section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl`,
  and
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  at
  [OSToWightmanPositivity.lean:4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4601](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4601),
  [4630](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4630),
  and
  [4686](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686):
  the current source stops at an open `Uflat` plus pointwise
  `ContinuousWithinAt` there;
- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point` at
  [ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  theorem-(1) still wants only one boundary equality at one point;
- reread the SCV local-open pair:
  `fourierLaplace_boundary_recovery_on_open_of_tempered` and
  `eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` at
  [LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156)
  and
  [DistributionalUniqueness.lean:1507](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1507):
  source is organized to produce local-open equality first and only then
  specialize to a basepoint;
- reading conclusion:
  the exact shifted-side theorem that should exist next is not pointwise but a
  local-open `Set.EqOn` theorem on `Uflat`;
- refined reading conclusion on the FL antecedent:
  the first honest missing SCV input beneath that theorem is still only the
  local-open `ContinuousWithinAt` field for the exact flattened FL witness;
- failed weaker alternative:
  proving only `hrepr_boundary_shifted` at the basepoint would skip the
  existing SCV local-open mechanism rather than using it honestly;
- reading conclusion on edits:
  no honest tiny helper surfaced, so this pass remains docs-only.

Supervision correction (`2026-04-16`, reread note on the shifted local-open consumer above theorem-(1)`):
this pass is docs-only.

- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point` at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  theorem-(1) still only wants the pointwise hypothesis
  `hrepr_boundary`;
- reread the raw shifted-side caller chain at
  [OSToWightmanPositivity.lean:4601](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4601),
  [4630](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4630),
  and
  [4686](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686):
  the shifted raw shell is already organized around an open `Uflat` with
  basepoint membership and
  `∀ xflat ∈ Uflat, ContinuousWithinAt ...`;
- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156):
  the recovery theorem uses exactly that open-set pointwise
  `ContinuousWithinAt` field, not full `ContinuousOn`;
- reread
  `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` at
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1507](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1507):
  the pointwise equality upgrade is genuinely local-open;
- reading conclusion:
  the honest shifted-side theorem above `hrepr_boundary_shifted` is an
  open-neighborhood equality theorem on `Uflat`, not a single-point theorem;
- refined reading conclusion on the FL-side contract:
  the minimal supplier statement remains the local-open
  `ContinuousWithinAt` field for the flattened FL witness on `Uflat`;
  any `ContinuousOn` upgrade should stay internal to the caller proof rather
  than becoming the public SCV-side supplier surface;
- failed weaker alternative:
  a theorem returning only the basepoint identity
  `hrepr_boundary_shifted`
  would skip the open-set mechanism the source is already organized to use;
- reading conclusion on edits:
  no honest Lean helper surfaced, so this pass remains docs-only.

Supervision correction (`2026-04-16`, reread note after checking the proved local/global recovery proofs on the primitive FL seam):

this pass is docs-only.

- reread the exact package fields in
  `HasFourierLaplaceReprRegular` and `HasFourierLaplaceReprTempered` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  and
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143):
  the weaker tempered package still needs `uniform_bound`, and the stronger
  regular package additionally needs `boundary_continuous` and
  `tube_continuousWithinAt`;
- reread the primitive source theorems
  `fourierLaplaceExtMultiDim_holomorphic`,
  `fourierLaplaceExtMultiDim_vladimirov_growth`,
  and
  `fourierLaplaceExtMultiDim_boundaryValue` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3256](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3256),
  [3304](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304),
  and
  [4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288):
  current proved source still stops at holomorphicity, Vladimirov growth, and
  distributional BV;
- reread the primitive comments at
  [3865](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3865)
  and
  [4303](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4303):
  source itself still says the boundary value is not pointwise and
  `F(x+iεη)` may blow up as `ε → 0+`;
- reading conclusion:
  the exact next primitive gap is not a continuity-only theorem and not a
  one-shot regularity theorem for the current zero extension;
- refined reading conclusion:
  the next honest theorem-sized target is a two-step chain:
  first
  `fourierLaplaceExtMultiDim_uniform_bound_near_boundary`
  with the exact `uniform_bound` field shape,
  then
  `fourierLaplaceExtMultiDim_exists_regular_boundary_repr`
  producing `HasFourierLaplaceReprRegular C G` for a representative `G`
  agreeing with `fourierLaplaceExtMultiDim ...` on the tube;
- why this order is forced:
  without the first theorem even `HasFourierLaplaceReprTempered` is not
  source-backed, while the second theorem is the minimal non-wrapper way to
  supply the downstream boundary continuity package without pretending the zero
  extension itself already has the correct boundary trace;
- reading conclusion on edits:
  no honest tiny compile-clean Lean theorem statement surfaced;
  this pass stays docs-only.
this pass is docs-only.

- reread
  `SCV.fourierLaplace_schwartz_integral_convergence` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:305](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:305):
  its pointwise step is exactly the canonical ray composed with
  `hRegular.tube_continuousWithinAt`;
- reread
  `fourierLaplace_schwartz_integral_convergence_local` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:105](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:105):
  the local DCT proof likewise needs
  `hcontU : ∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)`
  for the scalar pointwise limit;
- reread
  `HasFourierLaplaceReprRegular` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118):
  this package was introduced exactly because the weaker FL boundary-value data
  does not imply boundary continuity;
- reread the comments at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3865](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3865)
  and
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:4303](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4303):
  source itself says the boundary value is distributional, not pointwise in
  general;
- reading conclusion:
  the exact raywise scalar limit is still not derivable from current source,
  but the reason is now sharper than before:
  every existing scalar-limit theorem already assumes the same continuity field,
  and the universal pointwise theorem looks source-suspect at this generality;
- refined reading conclusion on the live seam:
  the honest missing analytic ingredient is extra boundary regularity for the
  specific FL witness on the shifted open set, not a generic evaluator from
  weak boundary-value data;
- reading conclusion on edits:
  no honest Lean landing surfaced, so this pass remains docs-only.

Supervision correction (`2026-04-16`, source-first reread note for the primitive FL raywise limit seam):
this pass is docs-only.

- reread
  `SCV.realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510):
  this is the exact path theorem for the canonical ray `x + i ε η`;
- reread
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  if proved, it would immediately give the desired scalar ray limit by
  `Filter.Tendsto.comp`;
- reread
  `SCV.fourierLaplaceExtMultiDim_boundaryValue` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288):
  it still gives only distributional convergence of pairings and explicitly
  warns that the boundary value is not pointwise in general;
- reread
  `SCV.fourierLaplace_schwartz_integral_convergence` and
  `HasFourierLaplaceReprRegular` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:309](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:309)
  and
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118):
  the only nearby scalar convergence theorem is circular here because the
  regular package already assumes `tube_continuousWithinAt`;
- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` and
  `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`:
  they only turn local pairing equality into pointwise equality after the same
  continuity input is already present;
- reading conclusion:
  the exact proof attempt is still just
  path theorem + missing `ContinuousWithinAt`,
  and no non-circular scalar-limit substitute exists in the nearby source;
- refined reading conclusion:
  the exact smaller missing analytic ingredient remains the direct pointwise
  boundary-regularity theorem for the exact FL extension,
  equivalently the scalar ray-limit theorem itself;
- reading conclusion on edits:
  no honest Lean helper surfaced, so this pass remains docs-only.

Supervision correction (`2026-04-16`, reread note after exact source composition check of the primitive FL raywise limit):
this pass is docs-only.

- reread
  `SCV.realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510):
  this is exactly the path theorem needed for the ray `x + i ε η`;
- reread
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  if proved, it would immediately give the raywise scalar limit by
  `Filter.Tendsto.comp`;
- reread
  `SCV.fourierLaplaceExtMultiDim_boundaryValue` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288):
  it still gives only distributional convergence of the pairings, not a
  pointwise scalar limit in `x`;
- reread
  `SCV.fourierLaplace_schwartz_integral_convergence` and
  `HasFourierLaplaceReprRegular` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:309](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:309)
  and
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118):
  the only nearby scalar-limit theorem is circular because the regular package
  already assumes `tube_continuousWithinAt`;
- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` and
  `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`:
  they only upgrade local pairing equality to pointwise equality after the same
  continuity input is already present on the open set;
- reading conclusion:
  the exact proof attempt is just
  path theorem + missing `ContinuousWithinAt`,
  and no non-circular substitute theorem surfaced;
- refined reading conclusion:
  the smallest honest missing analytic ingredient remains the direct pointwise
  boundary regularity theorem for the exact FL extension, equivalently the
  raywise limit theorem itself;
- reading conclusion on edits:
  no honest Lean helper surfaced, so this pass remains docs-only.

Supervision correction (`2026-04-16`, reread note after direct source check of the primitive FL continuity theorem):
this pass is docs-only.

Supervision correction (`2026-04-16`, reread note after exact raywise FL boundary-limit check):
this pass is docs-only.

- reread
  `SCV.realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510):
  this is the honest path theorem for the canonical ray
  `x + i ε η`;
- reread
  `SCV.fourierLaplaceExtMultiDim_boundaryValue` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288):
  it still gives only distributional boundary convergence of the test-function
  pairings, not a pointwise scalar limit in `x`;
- reread
  `SCV.fourierLaplace_schwartz_integral_convergence` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:309](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:309):
  the only nearby scalar convergence theorem is an integral theorem under
  `HasFourierLaplaceReprRegular`;
- reread
  `HasFourierLaplaceReprRegular` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118):
  that package already assumes
  `tube_continuousWithinAt`,
  so it cannot be used to prove the live primitive theorem without circularity;
- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` and
  `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156)
  and
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1506](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1506):
  they can upgrade local pairing equality to pointwise equality only after the
  same continuity input is already available;
- reading conclusion:
  the attempted direct proof of the raywise scalar limit is exactly
  path theorem + missing `ContinuousWithinAt`;
  no other existing theorem bypasses that;
- refined reading conclusion on blocker size:
  the smallest honest missing analytic ingredient is the direct pointwise
  boundary regularity theorem for the exact FL extension itself,
  equivalently the raywise limit theorem along `x + i ε η`;
- reading conclusion on edits:
  no honest Lean helper surfaced, so this pass remains docs-only.

- reread
  `SCV.fourierLaplaceExtMultiDim_continuousOn` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3204](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3204):
  it is only an interior theorem on `SCV.TubeDomain C`;
- reread
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  this is still the exact missing primitive source theorem for the FL side;
- reread
  `SCV.TubeDomain` and `SCV.realEmbed` at
  [OSReconstruction/SCV/TubeDomainExtension.lean:64](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeDomainExtension.lean:64)
  and
  [OSReconstruction/SCV/TubeDomainExtension.lean:110](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeDomainExtension.lean:110):
  the real point has imaginary part `0`, so it is generally on the boundary of
  `SCV.TubeDomain C`, not in the set itself unless `0 ∈ C`;
- reading conclusion:
  the tempting direct proof
  `fourierLaplaceExtMultiDim_continuousOn` + standard topology
  does **not** go through;
- reading conclusion on blocker size:
  the missing theorem is genuinely analytic boundary regularity from
  dual-cone support, not a hidden pure-topology lemma and not a missing
  membership fact;
- reading conclusion on edits:
  no honest tiny helper surfaced, so this pass remains docs-only.

Supervision correction (`2026-04-16`, reread note on the exact adjacent antecedent under theorem-(1)`):
this pass is docs-only.

- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point` at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  theorem-(1) takes the witness package, one real point `x`, interior equality
  `hrepr_tube`, and one pointwise boundary identity `hrepr_boundary`;
- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156):
  this theorem still only yields compact-support pairing equality on an open
  set, and only after one already has
  `∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)`;
- reread
  `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` at
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1507](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1507):
  this is the actual pointwise-equality upgrade step, but it still demands
  `ContinuousOn` of both traces on the same open `U`;
- reread
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  this is the exact primitive source theorem that should feed the immediate
  caller on the FL side, and it is still `sorry`;
- reading conclusion:
  theorem-(1) is formally blocked by the raw pointwise equality
  `hrepr_boundary_shifted`,
  but the first honest missing adjacent SCV antecedent is stronger:
  open-neighborhood FL boundary continuity for the same `Tflat`;
- reading conclusion on helper shape:
  no honest tiny Lean helper surfaced;
  any declaration that merely restated
  `hrepr_boundary_shifted`
  or theorem-(1)'s input list would be wrapper drift rather than blocker
  shrinkage.

Supervision correction (`2026-04-16`, reading note after exact source re-extraction of retained and omitted binders):
this pass is docs-only.

- reread
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr` at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233):
  the theorem inputs are only `OS`, `lgc`, `n`, and its returned witness data
  are exactly
  `Tflat`,
  `hCflat_open`,
  `hCflat_conv`,
  `hCflat_cone`,
  `hCflat_salient`,
  `hTflat_support`,
  `hTflat_W`,
  `hrepr_tube`;
- reread
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686):
  its exact surface already matches the future shifted-side supplier shape:
  open `Uflat`, basepoint membership, complement-image inclusion, and pointwise
  `ContinuousWithinAt`;
- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` and
  `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156)
  and
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1506](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1506):
  the former wants pointwise `ContinuousWithinAt` on an open set, while the
  latter wants `ContinuousOn`; so the `ContinuousOn` upgrade belongs inside the
  caller proof, not in the shifted-side supplier signature;
- reread
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  this is exactly why `hTflat_support` and the cone geometry first belong in
  the immediate caller above `hrepr_boundary_shifted`;
- reread
  `exists_fourierLaplaceReprTempered` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:907](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:907):
  the tempered package should stay proof-local and should not become a new
  theorem binder on this seam;
- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point` at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  `hrepr_tube` still belongs only at theorem-(1), not in the local-open caller
  above `hrepr_boundary_shifted`;
- reading conclusion:
  no honest Lean helper surfaced here;
  any declaration added now would merely restate the source-forced interface
  without shrinking the live blocker, so this pass remains docs-only.

Supervision correction (`2026-04-16`, reading note on omitted local-open caller binders):
this pass is docs-only.

- reread
  `exists_fourierLaplaceReprTempered` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:907](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:907):
  the local-open caller above `hrepr_boundary_shifted` does not need a new
  theorem parameter for a tempered package; that package can be assembled
  internally once the FL-side boundary-value and growth inputs are available;
- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156):
  this theorem is the local pairing supplier for the FL-side trace and is why
  the caller needs `Tflat`, cone geometry, and `hTflat_support`, but not a
  separately quantified `hTempered`;
- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point` at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  `hrepr_tube` is still consumed only at theorem-(1), so it should remain out
  of the open-neighborhood boundary-agreement theorem above
  `hrepr_boundary_shifted`;
- reading conclusion:
  the exact caller interface is now fixed:
  witness-free shifted-side supplier first,
  then a witness-local open-neighborhood `Set.EqOn` theorem carrying only
  `Tflat`, cone geometry, `hTflat_support`, and `hTflat_W`,
  with cone nonemptiness and tempered packaging left proof-local.

Supervision correction (`2026-04-16`, reading note on the exact shifted-side binder split):
this pass is docs-only.

- reread
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr` at
  [OSToWightmanBoundaryValueLimits.lean:233](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233):
  it packages four witness fields,
  `Tflat`, `hTflat_support`, `hTflat_W`, and `hrepr_tube`;
- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point` at
  [ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  theorem-(1) later needs `hTflat_support`, `hrepr_tube`, and one pointwise
  boundary equality, but not the whole local-open neighborhood theorem;
- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` and
  `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` at
  [LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156)
  and
  [DistributionalUniqueness.lean:1506](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1506):
  the local-open SCV route wants
  an open `Uflat`,
  pointwise `ContinuousWithinAt` on `Uflat`,
  and compact-support Schwartz pairing equality on `Uflat`;
- reading conclusion:
  the future insertion-site shifted-side theorem should carry **no** witness
  binders at all;
  it should only produce the open neighborhood and pointwise shifted-side
  continuity;
- reading conclusion on the next caller:
  the witness fields first re-enter in the boundary-agreement theorem above
  `hrepr_boundary_shifted`, and even there the only genuine witness binders are
  `Tflat`, cone geometry, `hTflat_support`, and `hTflat_W`;
  `hrepr_tube` should stay out of that theorem and re-enter only at the final
  theorem-(1) handoff;
- reading conclusion on the basepoint:
  the open set should be centered at
  `flattenCLEquivReal (n + m) (d + 1) y`,
  not at a separately flattened shifted point, because the comparison function
  already applies `xiShift ... t` internally.

Supervision correction (`2026-04-16`, reread note on the exact local-open seam above `hrepr_boundary_shifted`):
this pass is docs-only.

- reread
  `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` at
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1506](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1506):
  this is the exact open-set equality endpoint;
  it turns local compactly supported Schwartz pairing equality into
  `Set.EqOn g h U`, but only after one has `ContinuousOn` of both traces on
  the whole open set `U`;
- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156):
  it is still only the pairing supplier and still needs
  `∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)`;
- reread
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686):
  the shifted complement branch already has the right open-neighborhood
  continuity theorem surface for the flattened fixed-time shell continuation;
- reread its proof source:
  that theorem is only a thin open-set packaging of
  `section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl`,
  which itself packages the live theorem-(1) `sorry`
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  at positivity line `4583`;
- reread
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  the exact FL side still lacks proved boundary continuity even pointwise;
- reading conclusion on the smallest honest local-open theorem:
  the next theorem should assert open-neighborhood boundary agreement
  `Set.EqOn` between the shifted flattened `bvt_F` trace and the exact
  `fourierLaplaceExtMultiDim ... Tflat` trace on some open `Uflat`
  containing the distinguished shifted point;
- reading conclusion on continuity:
  current source does not already supply the needed open-neighborhood
  continuity package as a trustworthy proved fact;
  the right theorem surface exists on the shifted complement branch, but only
  downstream of theorem-(1)'s missing continuity proof.

Supervision correction (`2026-04-16`, reread note on the exact SCV boundary-agreement interfaces):
this pass is docs-only.

- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156):
  it is genuinely local but still only says
  `dist f = ∫ F(realEmbed x) * f x`
  for tests supported in an open set `U`, assuming
  `∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)`;
- reread
  `SCV.eq_zero_on_open_of_compactSupport_schwartz_integral_zero` at
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1353](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1353):
  this is the theorem that turns local Schwartz-pairing equality into
  pointwise equality, but only on an open set and only after one already has a
  continuous real-side function there;
- reread
  `SCV.uniqueness_of_boundary_zero` and
  `SCV.distributional_uniqueness_tube_of_zero_bv` at
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1659](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1659)
  and
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1958](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1958):
  they control tube-interior equality/vanishing, not the raw assigned value at
  one real boundary point;
- reread
  `SCV.boundary_value_zero_of_regular` /
  `SCV.distributional_uniqueness_tube_of_regular` at
  [OSReconstruction/SCV/TubeDistributions.lean:78](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeDistributions.lean:78)
  and
  [OSReconstruction/SCV/TubeDistributions.lean:95](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeDistributions.lean:95):
  they do reach pointwise real-boundary conclusions, but only from the stronger
  regular package, so they do not almost solve the live seam;
- reading conclusion on the missing theorem surface:
  the smallest honest theorem is still the witness-local shifted equality
  `bvt_F OS lgc q z0 =
    fourierLaplaceExtMultiDim ... Tflat ((flattenCLEquiv q (d + 1)) z0)`;
- continuity conclusion on reread:
  existing proved SCV packaging would require an open neighborhood theorem, not
  just one-point continuity, before it can turn shared distributional data into
  pointwise equality;
- insertion conclusion on reread:
  if reopened, prove this immediately below
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`,
  then feed it into
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point`,
  then into the theorem-(1) caller at positivity line `4583`.

Supervision correction (`2026-04-16`, reading note after the exact shifted-boundary source audit):
this pass is docs-only.

- reread `bvt_boundary_values` at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean:360](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean:360):
  it gives only convergence of shell integrals against Schwartz tests to
  `bvt_W`, never a raw formula for `bvt_F` on the real boundary;
- reread
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr` at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233):
  this is the exact trustworthy witness package,
  with
  `hTflat_W` on Schwartz tests and
  `hrepr_tube` on tube interior points;
- reread
  `boundary_value_recovery_forwardTube_of_flatRegular` /
  `..._from_bv` and the SCV recovery theorems:
  every one of them concludes an equality of the form
  `distribution applied to f = ∫ boundary-trace * f`,
  not a pointwise identity at one real point;
- reread
  `fourierLaplace_boundary_recovery_on_open_of_tempered` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156):
  it still requires local
  `ContinuousWithinAt F (TubeDomain C) (realEmbed x)` on the open set, so it is
  downstream of the missing boundary trace rather than a proof of it;
- reread
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  it is still `sorry`, so the only theorem shape that could bridge interior FL
  representation to raw boundary evaluation is not yet available as proved
  source;
- reading conclusion:
  `hrepr_boundary_shifted` is not derivable from existing proved source;
  the first honest missing ingredient is still a witness-local boundary
  trace/evaluation theorem upgrading distributional recovery to the shifted
  real-point equality for that same `Tflat`.

Supervision correction (`2026-04-16`, corrected reading note for the live theorem-(1) seam):
this pass is docs-only.

- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point` at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  its only non-witness input beyond the interior identity is the raw
  real-point equality `hrepr_boundary`;
- reread
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr` at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233):
  it already fixes the exact same `Tflat` and supplies the interior
  Fourier-Laplace identity `hrepr_tube`;
- reread
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583):
  theorem-(1) is still the full `ContinuousWithinAt` consumer on the current
  branch and should not be demoted to a weaker raywise theorem surface here;
- at the live shifted point
  `q := n + m`,
  `j := ⟨n, Nat.lt_add_of_pos_right hm⟩`,
  `x0 := xiShift j 0 y t`,
  `z0 := xiShift j 0 (fun k μ => (y k μ : ℂ)) (t : ℂ)`,
  the positivity-local proof target reduces to feeding that forward-tube theorem
  the exact missing boundary equality
  `bvt_F OS lgc q z0 =
    fourierLaplaceExtMultiDim ... Tflat
      (SCV.realEmbed (flattenCLEquivReal q (d + 1) x0))`;
- no extra positivity-local neighborhood theorem appeared on reread;
  the only remaining regularity theorem is the already-separated SCV exact-FL
  continuity theorem, and it lives upstream inside the forward-tube theorem
  surface rather than below it;
- both continuity theorems still end in `sorry`, so this is a source-shape
  reduction, not a usable proved route yet;
- smallest missing ingredient on reread:
  the raw shifted witness-local boundary agreement `hrepr_boundary_shifted`.

Supervision correction (`2026-04-16`, reread note for the exact theorem-(1) seam after the boundary-agreement probe):
this pass is docs-only.

- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point` at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  its only non-witness input beyond the interior identity is the raw
  real-point equality `hrepr_boundary`;
- reread
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr` at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233):
  it already fixes the exact same `Tflat` and supplies the interior
  Fourier-Laplace identity `hrepr_tube`;
- reread
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583):
  at the live shifted point
  `q := n + m`,
  `j := ⟨n, Nat.lt_add_of_pos_right hm⟩`,
  `x0 := xiShift j 0 y t`,
  `z0 := xiShift j 0 (fun k μ => (y k μ : ℂ)) (t : ℂ)`,
  the local proof target now reduces to feeding that forward-tube theorem the
  exact missing boundary equality
  `bvt_F OS lgc q z0 =
    fourierLaplaceExtMultiDim ... Tflat
      (SCV.realEmbed (flattenCLEquivReal q (d + 1) x0))`;
- no extra positivity-local neighborhood theorem appeared on reread;
  the only remaining regularity theorem is the already-separated SCV exact-FL
  continuity theorem, and it lives upstream inside the forward-tube theorem
  surface rather than below it;
- both continuity theorems still end in `sorry`, so this is a source-shape
  reduction, not a usable proved route yet;
- smallest missing ingredient on reread:
  the raw shifted witness-local boundary agreement `hrepr_boundary_shifted`.

Supervision correction (`2026-04-16`, reread note for the canonical-ray consumer on theorem-(1)):
this pass is docs-only.

- reread the exact complement-side chain in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583):
  the unresolved theorem at `4583` is only used to build wrappers at
  `4601`, `4630`, and `4686`, and the first actual downstream use is the
  coefficient limit at `4736`;
- that coefficient theorem consumes only the canonical shell ray
  `ε ↦ xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ =>
        ↑(y k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
            Complex.I)
      (t : ℂ)`;
- so on the exact current branch the consumer can be weakened below full
  `ContinuousWithinAt`;
- the newly landed SCV theorem
  `realPlusIEpsEta_tendsto_nhdsWithin_realEmbed`
  is the right geometry for this smaller target after flattening;
- the next honest missing ingredient is therefore a witness-local boundary
  trace theorem along that single canonical ray, together with the already
  tracked shifted boundary-value at
  `z0 = xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ => (y k μ : ℂ)) (t : ℂ)`;
- do not reopen the larger neighborhood-continuity packaging unless another
  branch actually consumes it.

Supervision correction (`2026-04-16`, bounded reread note on the SCV supplier decomposition):
this pass is not docs-only: one tiny compile-clean SCV geometry theorem was
landed.

- reread `fourierLaplaceExtMultiDim_continuousOn`,
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed`,
  `fourierLaplaceExtMultiDim_holomorphic`, and `SCV.tubeDomain_isOpen`;
- source verdict:
  the only smaller nearby ingredient already visible in the code was the
  geometry of the canonical approach ray `ε ↦ x + i ε η`;
- landed
  `realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510),
  which packages that ray as a theorem
  `Tendsto ... (nhdsWithin (SCV.realEmbed x) (SCV.TubeDomain C))`;
- this is genuinely useful and weaker than full boundary continuity, but it
  does not by itself bridge the supplier theorem because it controls only one
  chosen ray, not arbitrary tube approaches;
- smallest missing SCV theorem remains
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed`.

Supervision correction (`2026-04-16`, source-pinned reread note on the nearest SCV theorem surface):
this pass is docs-only.

- reread
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241)
  together with its immediate neighbors
  `fourierLaplaceExtMultiDim_continuousOn` at line `3204`
  and
  `fourierLaplaceExtMultiDim_holomorphic` at line `3256`;
- this is the nearest SCV boundary-regularity theorem surface to the live seam:
  it gives continuity of `fourierLaplaceExtMultiDim ... T` at
  `SCV.realEmbed x`, not continuity of `bvt_F`;
- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point` at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688):
  after unpacking the private witness theorem, every binder already matches
  except the explicit boundary equality at the chosen real point;
- for the live shifted point
  `q := n + m`,
  `j := ⟨n, Nat.lt_add_of_pos_right hm⟩`,
  `x0 := xiShift j 0 y t`,
  `z0 := xiShift j 0 (fun k μ => (y k μ : ℂ)) (t : ℂ)`,
  the exact remaining antecedent is
  `bvt_F OS lgc q z0 =
    fourierLaplaceExtMultiDim ... Tflat
      (SCV.realEmbed (flattenCLEquivReal q (d + 1) x0))`,
  equivalently
  `bvt_F OS lgc q z0 =
    fourierLaplaceExtMultiDim ... Tflat ((flattenCLEquiv q (d + 1)) z0)`;
- no Lean skeleton was added:
  any local theorem below the private witness would still just restate that same
  missing boundary equality.

Supervision correction (`2026-04-16`, reread note after the witness-local surface recheck):
this pass is docs-only.

- if this seam is reopened, still insert immediately below
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr` in
  [OSToWightmanBoundaryValueLimits.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233),
  before `sum_over_flat_timeSlots`;
- the future theorem should inherit the ambient file context
  `variable {d : ℕ} [NeZero d]`;
- keep the same explicit witness-local package:
  `Tflat`, cone geometry, `hTflat_support`, `hTflat_W`, `hrepr_tube`;
- the conclusion should still be only the raw shifted equality for
  `z0 = xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ => (y k μ : ℂ)) (t : ℂ)`;
- do not add a Lean theorem statement or local alias now:
  at that exact surface the only compile-clean additions are administrative and
  would not reduce the blocker;
- first proof obligation on reread:
  upgrade weak BV convergence to the raw shifted-point equality for the same
  witness `Tflat`, using the boundary distribution identification `hTflat_W`
  together with the interior FL identity `hrepr_tube`.

Supervision correction (`2026-04-16`, reread note for the exact witness-local insertion surface):
this pass is docs-only.

- if this seam is reopened, insert immediately below
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr` in
  [OSToWightmanBoundaryValueLimits.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233),
  before `sum_over_flat_timeSlots`;
- the theorem should keep the private flattened witness explicit:
  `Tflat`, cone geometry, dual-cone support, `hTflat_W`, `hrepr_tube`;
- its conclusion should be only the raw shifted-point equality for
  `z0 = xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ => (y k μ : ℂ)) (t : ℂ)`;
- do not add a Lean statement now unless there is a proof route for the actual
  boundary-trace upgrade, because the statement itself is the blocker;
- first proof obligation on reread:
  derive raw `bvt_F(real point)` from weak BV convergence plus the same-witness
  interior FL representation.

Supervision correction (`2026-04-16`, bounded reading note on the minimal blocker-A supplier):
this pass is docs-only.

- reread
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point` at
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688)
  together with the adjacent recovery theorems at lines `752`, `799`, and
  `1105`;
- source verdict:
  the forward-tube file already contains the right consumer theorem, but the
  neighboring theorems still recover only boundary distributions after pairing
  with Schwartz tests;
- the minimal missing supplier is therefore not another wrapper in
  `ForwardTubeDistributions.lean`, but the witness-local raw boundary equality
  for the same `Tflat` at the shifted real point
  `z0 = xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ => (y k μ : ℂ)) (t : ℂ)`;
- exact target shape:
  `bvt_F OS lgc (n + m) z0 =
    fourierLaplaceExtMultiDim ... Tflat
      ((flattenCLEquiv (n + m) (d + 1)) z0)`;
- minimal package as currently understood:
  unpack the private witness theorem, keep the same cone/support/interior
  representation data, use the exact flattening identity at `z0`, and add only
  the missing boundary-trace upgrade theorem for that same witness-local setup;
- practical reading consequence:
  when this seam is revisited, open
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`
  before searching for any new forward-tube wrapper theorem.

Supervision correction (`2026-04-16`, bounded reread note for the exact upstream obstruction above the private witness):
this pass is docs-only.

- reread `bvt_boundary_values` as weak BV data only:
  it converges shell integrals against Schwartz tests to `bvt_W`;
- reread `bv_zero_point_is_evaluation` only as the degree-`0` normalization
  bridge:
  it identifies `W_0` with evaluation on `Fin 0`, not `bvt_F(real point)` for
  the live shifted `q = n + m` seam;
- reread
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr` as
  the exact same-witness interior FL theorem:
  it fixes `Tflat` and proves the identity only on `TubeDomainSetPi C`;
- reread
  `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` only as paired
  boundary recovery:
  it recovers `T f`, not `F x0`;
- therefore no current theorem honestly yields the raw shifted equality
  `bvt_F OS lgc q z0 =
    fourierLaplaceExtMultiDim ... Tflat ((flattenCLEquiv q (d + 1)) z0)`;
- exact obstruction:
  the source has no boundary-trace theorem upgrading weak BV data for `bvt_F`
  to raw point evaluation at the shifted real point.

Supervision correction (`2026-04-16`, bounded reread note for the exact boundary-value obstruction at the live seam):
this pass is docs-only.

- reread `bvt_boundary_values` first:
  it gives only raywise distributional convergence against a Schwartz test,
  not any equality of raw values of `bvt_F` at a real boundary point;
- reread
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`
  next:
  it gives the same exact `Tflat` and the interior identity on
  `TubeDomainSetPi C`, but still nothing at the real boundary point;
- reread
  `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` only as a
  distributional recovery theorem:
  it identifies `T f` with the boundary integral `∫ F(x) f(x)`,
  not `F(x0)` with a Fourier-Laplace trace at one point;
- therefore no current theorem honestly yields
  `bvt_F OS lgc q z0 =
    fourierLaplaceExtMultiDim ... Tflat ((flattenCLEquiv q (d + 1)) z0)`;
- exact obstruction:
  the current source stops at weak boundary-value data and test-function-level
  recovery, while the live seam needs raw pointwise boundary agreement for the
  already-fixed witness `Tflat`.

Supervision correction (`2026-04-16`, exact reread note for the two unresolved theorem surfaces at the live seam):
this pass is docs-only.

- reread these four anchors together:
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233),
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688),
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241);
- the forward-tube theorem is already the exact raw-boundary consumer:
  same `Tflat`, same interior FL representation on `ForwardTube d n`, plus one
  real-point boundary equality, imply `ContinuousWithinAt`;
- the SCV theorem is already the exact exact-FL supplier:
  dual-cone support implies `ContinuousWithinAt` of
  `fourierLaplaceExtMultiDim ... T` at `SCV.realEmbed x`;
- both theorem surfaces still end in `sorry`, so neither may be treated as
  landed mathematics;
- at the live shifted point set
  `q := n + m`,
  `j := ⟨n, Nat.lt_add_of_pos_right hm⟩`,
  `x0 := xiShift j 0 y t`,
  `z0 := xiShift j 0 (fun k μ => (y k μ : ℂ)) (t : ℂ)`;
- the exact bridge identities needed by the consumer are
  `(fun k μ => (x0 k μ : ℂ)) = z0`
  and
  `SCV.realEmbed (flattenCLEquivReal q (d + 1) x0) =
    (flattenCLEquiv q (d + 1)) z0`;
- the private witness theorem already gives the same `Tflat` and the interior
  identity `hrepr_tube`;
- the only extra mathematical input still needed after the witness theorem and
  the SCV continuity theorem is the raw boundary equality
  `bvt_F OS lgc q z0 =
    fourierLaplaceExtMultiDim ... Tflat ((flattenCLEquiv q (d + 1)) z0)`.

Supervision correction (`2026-04-16`, exact reread note for the theorem-3 complement seam):
this pass is docs-only.

- reread these four source anchors together when the seam is revisited:
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:233),
  [OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean:688),
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241);
- both theorem surfaces still end in `sorry`, so neither continuity theorem may
  be treated as already landed mathematics;
- the private witness theorem already gives the exact interior identity for one
  witness `Tflat`:
  `∀ z ∈ ForwardTube d q,
      bvt_F OS lgc q z =
        fourierLaplaceExtMultiDim ... Tflat ((flattenCLEquiv q (d + 1)) z)`;
- at the live shifted point set
  `q := n + m`,
  `j := ⟨n, Nat.lt_add_of_pos_right hm⟩`,
  `x0 := xiShift j 0 y t`,
  `z0 := xiShift j 0 (fun k μ => (y k μ : ℂ)) (t : ℂ)`;
- the exact flattening match to feed the consumer theorem is
  `SCV.realEmbed (flattenCLEquivReal q (d + 1) x0) =
    (flattenCLEquiv q (d + 1)) z0`;
- the only extra mathematical input still needed after the witness theorem and
  the SCV continuity theorem is the raw boundary equality
  `bvt_F OS lgc q z0 =
    fourierLaplaceExtMultiDim ... Tflat ((flattenCLEquiv q (d + 1)) z0)`;
- do not drift into wrappers, regularity packaging, local recovery, or theorem
  (2): the seam is exactly this shifted-point boundary identification plus the
  two unresolved theorem surfaces above.

Supervision correction (`2026-04-16`, bounded source-pinned reread note for the theorem-3 complement seam):
this pass is docs-only.

- exact source statements to reread together:
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` and
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point`;
- the second theorem does not ask for any regularity wrapper: it asks directly
  for one witness `Tflat`, one interior identity on `ForwardTube d n`, and one
  exact boundary equality at one real point;
- for the live theorem set
  `q := n + m`,
  `j := ⟨n, Nat.lt_add_of_pos_right hm⟩`,
  `x0 := xiShift j 0 y t`,
  `z0 := xiShift j 0 (fun k μ => (y k μ : ℂ)) (t : ℂ)`;
- the flattening match at that point is exact:
  `SCV.realEmbed (flattenCLEquivReal q (d + 1) x0) =
    (flattenCLEquiv q (d + 1)) z0`;
- the private witness theorem already gives the same `Tflat` and the interior
  identity needed for the consumer theorem;
- the only extra mathematical input still needed is the raw equality
  `bvt_F OS lgc q z0 =
    fourierLaplaceExtMultiDim ... Tflat ((flattenCLEquiv q (d + 1)) z0)`;
- do not let future passes drift back into wrappers, regularity packaging, or
  theorem-(2): the seam is exactly this shifted boundary equality plus the two
  still-unproved source theorem surfaces above.

Supervision correction (`2026-04-16`, bounded shifted-boundary theorem-sizing pass):
the next honest source target is now pinned at theorem granularity, but no Lean
artifact was added.

- when revisiting this seam, open
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`
  and work directly below it in
  `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`;
- the intended missing theorem name is
  `section43_shifted_boundary_agreement_of_flattened_bvt_F_witness`;
- the intended statement is the raw shifted-point equality
  `bvt_F OS lgc (n + m) z0 =
    fourierLaplaceExtMultiDim ... Tflat
      ((flattenCLEquiv (n + m) (d + 1)) z0)`
  for
  `z0 = xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ => (y k μ : ℂ)) (t : ℂ)`;
- do not try to state that theorem in `OSToWightmanPositivity.lean`:
  the needed `Tflat` witness is private upstream and unavailable there;
- do not add a proposition-only Lean alias unless it is consumed immediately:
  the consumer theorem in `ForwardTubeDistributions.lean` already exposes the
  exact boundary hypothesis, so extra unproved scaffolding adds nothing.

Supervision correction (`2026-04-16`, bounded source verification of the shifted raw boundary-point seam):
the next honest source target is now pinned exactly.

- reread confirms the shifted point in the live seam is
  `z0 = xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ => (y k μ : ℂ)) (t : ℂ)`;
- the private witness theorem in
  `OSToWightmanBoundaryValueLimits.lean` already gives the interior exact
  Fourier-Laplace representation of `bvt_F` on the forward tube for one fixed
  `Tflat`;
- source search still finds no theorem giving the matching boundary-point
  equality at `z0` for that same `Tflat`;
- `bvt_boundary_values` remains only a weak boundary-value theorem and must not
  be read as pointwise boundary identification;
- `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` and
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point`
  are both still unresolved theorem surfaces in current source.

Practical reading consequence:

- when this seam is revisited, open these three items together and in this
  order:
  1. `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  2. `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`
  3. `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point`
- then target exactly the missing statement
  `bvt_F OS lgc (n + m) z0 =
    fourierLaplaceExtMultiDim ... Tflat
      ((flattenCLEquiv (n + m) (d + 1)) z0)`
  in `OSToWightmanBoundaryValueLimits.lean` or a nearby forward-tube consumer
  file.

Supervision correction (`2026-04-16`, bounded source-first check of the raw shifted-point consumer):
the next honest source target is now pinned more tightly.

- do not reread the local tempered recovery layer looking for pointwise
  continuity; that route is exhausted;
- the exact transfer theorem already exists:
  `ForwardTubeDistributions.boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point`;
- the private witness theorem already gives the flattened dual-cone witness and
  interior exact FL representation;
- the remaining missing ingredient is a theorem identifying raw `bvt_F` at the
  shifted real point with the boundary trace of that same exact FL extension;
- weak boundary-value theorems such as `bvt_boundary_values` do not provide
  that pointwise equality.

Practical reading consequence:

- when revisiting this seam, read the private witness theorem together with
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point`;
- then search only for a source theorem that upgrades weak boundary-value data
  to the needed boundary-point equality at the shifted real point, or prove
  that theorem itself.

Supervision correction (`2026-04-16`, bounded source-first check of the exact FL consumer layer):
the next honest reread target is now fully pinned.

- there are exactly two theorem-sized source surfaces on the live seam:
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` in
  `OSReconstruction/SCV/PaleyWienerSchwartz.lean`, and
  `boundary_function_continuousWithinAt_forwardTube_of_flatFLRepr_at_point` in
  `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`;
- the second theorem is the precise raw-boundary consumer:
  from exact interior FL representation plus boundary-point equality with the
  same FL extension, conclude `ContinuousWithinAt` for the raw forward-tube
  function;
- source-first caveat:
  both theorem surfaces are still unresolved, so neither may be consumed as an
  already-landed result.

Practical reading consequence:

- when revisiting this seam, start with those two theorem statements before
  rereading broader local-recovery infrastructure;
- do not search for another wrapper theorem around the private flattened witness
  package until one of these exact surfaces is genuinely proved.

Supervision correction (`2026-04-16`, bounded exact-FL boundary-continuity skeleton landing):
the next honest source target is now sharper and partly landed.

- new theorem-sized Lean skeleton:
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` in
  `OSReconstruction/SCV/PaleyWienerSchwartz.lean`;
- this is the correct source surface for continuity coming directly from the
  exact dual-cone Fourier-Laplace witness.

Reading consequence:

- when revisiting the seam, do not ask the private flattened witness theorem to
  prove continuity of `bvt_F` directly without checking boundary-value
  agreement;
- first check whether the exact FL extension has been shown continuous within at
  `realEmbed x`, then separately check whether `bvt_F (real point)` is already
  identified with that boundary trace.

Supervision correction (`2026-04-16`, bounded raw-`bvt_F` shifted-point source refinement):
the next honest source search is now pinned more tightly.

- do not keep searching for a continuity theorem that only consumes the current
  tempered shell package; that path is exhausted;
- the relevant strong input already exists privately in
  `OSToWightmanBoundaryValueLimits.lean` as
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`;
- the first missing theorem is therefore the consumer of that strong input:
  an SCV/forward-tube theorem turning flattened dual-cone Fourier-Laplace
  representation data into `HasFourierLaplaceReprRegular`, or directly into the
  boundary conclusion `ContinuousWithinAt`.

Practical reading consequence:

- when this seam is revisited, read
  `OSToWightmanBoundaryValueLimits.lean` for the exact private `Tflat`/support/
  `fourierLaplaceExtMultiDim` witness before designing more local shell lemmas;
- the mathematically honest new source surface is not theorem (2) and not a new
  local-recovery theorem, but a forward-tube/SCV regularity theorem consuming
  that already-built representation.

Supervision correction (`2026-04-16`, bounded raw-`bvt_F` shifted-point skeleton landing):
the live theorem-(1) seam is now source-pinned one notch lower in Lean.

Reading consequence:

- stop treating
  `section43_fixedTimeShellRaw_pointwiseContinuity_on_section43PositiveEnergyRegion_compl`
  as the live `sorry`; it is now a proved reduction step;
- the actual missing theorem is
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`,
  i.e. raw `bvt_F` continuity within `ForwardTube d (n + m)` at the shifted
  real boundary point;
- the next honest source search should target either an exact SCV theorem that
  yields that `ContinuousWithinAt` conclusion from real Fourier-Laplace support
  data, or a proof of that theorem itself.

Verification note:

- a bounded `timeout 30s lake env lean
  OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
  run produced no diagnostics before the harness stopped yielding, so this pass
  does not certify a completed file check.

Supervision correction (`2026-04-16`, bounded shifted-point reduction landing):
the live theorem-(1) seam has been tightened again. The shell continuation no
longer carries its own separate `xiShift` continuity burden: a new helper now
reduces it to continuity of raw `bvt_F` at the shifted real boundary point.

Reading consequence:

- do not spend more time on affine `xiShift` transport for this seam;
- the next honest source search is for continuity of raw `bvt_F` at shifted
  complement-side real points, or for the smallest SCV theorem that would imply
  exactly that.

Supervision correction (`2026-04-16`, bounded pointwise-supplier transport landing):
the flattening layer under theorem (1) is now discharged in Lean. The source
blocker moved one step lower:

- `section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl`
  is now a proved transport theorem;
- the only remaining `sorry` at this seam is the new unflattened statement
  `section43_fixedTimeShellRaw_pointwiseContinuity_on_section43PositiveEnergyRegion_compl`,
  i.e. pointwise `ContinuousWithinAt` on `ForwardTube d (n + m)` at a fixed
  complement-side real point.

Reading consequence:

- do not spend more time on flat-coordinate transport for this seam;
- the next honest source search is for unflattened boundary continuity input,
  or for the smallest SCV theorem that would imply it.

Supervision correction (`2026-04-16`, bounded theorem-(1) decomposition landing):
the source frontier moved down by one honest theorem-sized step. The local
`Uflat` package is no longer the real blocker: `OSToWightmanPositivity.lean`
now proves theorem (1)'s neighborhood half by taking the full flattened
complement image, and leaves only the pointwise boundary-continuity statement
as the live `sorry`:
`section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl`.

Reading consequence:

- the actual missing mathematics is now purely boundary regularity at a fixed
  flattened real point on the complement side;
- the open-set transport from
  `(section43PositiveEnergyRegion d (n + m))ᶜ`
  to flat coordinates is settled and should no longer be treated as part of the
  frontier.

Supervision correction (`2026-04-16`, bounded theorem-(1) skeleton landing):
the complement-side local continuity package is now named in Lean source as
`section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
in
`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`.
This does not advance the proof mathematically, but it fixes the live source
surface: the blocker is now one explicit theorem-level `sorry` with the exact
`Uflat` / `hcontUflat` contract, not an unlanded docs-only target.

Supervision correction (`2026-04-16`, bounded complement-side source reread):
no honest Lean edit survived; this pass was docs-only.

- reread of the live SCV/Wick-rotation source confirms that no existing theorem
  presently outputs
  `∀ xflat ∈ Uflat, ContinuousWithinAt G_t
    (SCV.TubeDomain (ForwardConeFlat d (n + m)))
    (SCV.realEmbed xflat)`;
- the only nearby exported continuity theorem is
  `ForwardTubeDistributions.boundary_function_continuous_forwardTube_of_flatRegular`,
  and it still requires a pre-existing
  `HasFourierLaplaceReprRegular` package;
- `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` and the private
  `SCV.LocalBoundaryRecovery.pointwise_convergence_local` proof are downstream
  consumers of local boundary continuity, not suppliers of it;
- `SCV.exists_fourierLaplaceReprTempered`,
  `SCV.tube_boundaryValueData_of_polyGrowth`,
  `SCV.tube_boundaryValueData_of_polyGrowth'`, and
  `SCV.tube_boundaryValue_of_vladimirov_growth` stop at distributional
  boundary-value existence and growth estimates;
- `TubeBoundaryValueExistence.continuous_tubeSlice_ray_deriv` is only a
  continuity theorem for the one-variable ray-slice integral on `τ > 0`, not a
  boundary theorem for `F`.

So the first missing theorem is most accurately a boundary-value continuity /
local boundary-regularity theorem in the SCV layer, rather than a recovery
theorem or a flatten-transport theorem.

Supervision correction (`2026-04-16`, bounded theorem-(1) reread): no honest
Lean edit survived; this pass was docs-only.

- theorem (1) still is not landed in source;
- the neighborhood half of theorem (1) is straightforward from
  `section43PositiveEnergyRegion` being the closed half-space intersection
  `{q | ∀ i, 0 ≤ q i 0}` and from
  `flattenCLEquivReal ... .toHomeomorph.isOpenMap`;
- the continuity half is the real blocker:
  the only source theorem directly giving boundary continuity on the flat side
  is
  `ForwardTubeDistributions.boundary_function_continuous_forwardTube_of_flatRegular`,
  which requires `HasFourierLaplaceReprRegular`;
- on the live seam, current source only builds
  `HasFourierLaplaceReprTempered` from
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`,
  `differentiableOn_flatten`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `section43_fixedTimeShellRaw_uniformPolyGrowth_fixedTime`,
  and `SCV.exists_fourierLaplaceReprTempered`;
- so theorem (1) currently fails because the needed continuity theorem is
  formulated through missing regularity, not because the complement-side
  neighborhood is unavailable.

Supervision correction (`2026-04-16`, bounded helper-source reread): no honest
Lean edit survived; this pass was docs-only.

- direct source search still finds no landed theorem (1) in
  `OSToWightmanPositivity.lean` producing `Uflat`, `hUflat_open`, and
  `hcontUflat`;
- the desired fixed-direction DCT helper is now pinned exactly as the compact-
  support bound on `tsupport (fflat : _ → ℂ)` stated in the blueprint/audit;
- the source lemmas closest to finishing it are
  `HasCompactSupport.isCompact`,
  `IsCompact.exists_bound_of_continuousOn`, and
  `forwardConeFlat_posScale_closed`;
- the last missing bridge is still a local theorem converting pointwise
  `ContinuousWithinAt` boundary traces into `ContinuousOn` for the strip map
  `(ε, xflat) ↦ G_t (xflat + i ε η0flat)` on a compact support neighborhood.

Supervision correction (`2026-04-16`, bounded theorem-(2) landing reread): the
source now fixes one more fidelity point.

- the current docs had been speaking as if theorem (1) already existed in Lean;
- direct reread of
  `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
  shows that no local theorem producing `Uflat` and `hcontUflat` is presently
  landed beneath
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`;
- so theorem (2) remains docs-only for now: its exact statement/proof chain is
  pinned, but its first hypothesis package is still missing in source.

Exact reread of the intended theorem-(2) proof:

- weak BV limit from
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`;
- flat rewrite through
  `ForwardTubeDistributions.schwartz_bv_to_flat_repr_dist_apply`;
- pointwise convergence by the local pattern of
  `SCV.LocalBoundaryRecovery.pointwise_convergence_local`;
- domination from a still-missing compact-support local-bound helper;
- conclude by DCT and limit uniqueness.

Exact reread blocker order:

- first missing object:
  theorem (1) itself, i.e. the local `Uflat`/`hcontUflat` continuity package;
- second missing object:
  the compact-support fixed-direction bound used in theorem (2)'s DCT step.

Supervision correction (`2026-04-16`, bounded theorem-(2) reread): the source
now forces a sharper reading than the older notes.

- theorem (2) is not a disguised call to the existing local tempered recovery
  theorem;
- it must instead be a flat, fixed-direction weak-BV recovery theorem for
  compactly supported tests, because the only available shell bound is along
  `η0flat := flattenCLEquivReal (n + m) (d + 1)
    (canonicalForwardConeDirection (d := d) (n + m))`.

Exact proof skeleton now pinned from source:

- define `G_t`, `T_t`, and `Tflat` exactly as in the live coefficient seam;
- consume theorem (1)'s `Uflat`/`hcontUflat`;
- for supported compact `fflat`, take the canonical-direction weak BV limit from
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`;
- prove pointwise convergence using the same local argument as
  `SCV.LocalBoundaryRecovery.pointwise_convergence_local`;
- prove domination on `tsupport fflat` from a compact-support local-bound lemma
  derived from `hcontUflat`;
- conclude
  `Tflat fflat = ∫ xflat, G_t (SCV.realEmbed xflat) * fflat xflat`
  by DCT and limit uniqueness.

Exact reread blocker:

- the missing ingredient is not another transport theorem and not all-directions
  growth;
- it is only the compact-support local-bound helper needed for the DCT step in
  theorem (2).

Supervision correction (`2026-04-16`, bounded source-first reread of the live
complement-side seam): the earlier reread entries claiming "still one theorem"
are stale/incomplete. The direct source reason is simple and decisive:

- `SCV.exists_fourierLaplaceReprTempered` needs
  `uniform_bound : ∀ η ∈ C, ...`;
- `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` consumes that
  tempered package;
- the fixed-time shell source below the live coefficient theorem only provides
  `section43_fixedTimeShellRaw_uniformPolyGrowth_fixedTime`, whose bound is
  tied to the single canonical shell direction and not to arbitrary
  `η ∈ ForwardConeFlat d (n + m)`.

So the missing live package is not already present, and it is not honestly just
one theorem if the current SCV consumer is kept. The source-backed minimal
cluster is:

1. a flat local continuity theorem for
   `G_t zflat := bvt_F OS lgc (n + m)
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        ((flattenCLEquiv (n + m) (d + 1)).symm zflat) (t : ℂ))`
   on some open `Uflat` around
   `flattenCLEquivReal (n + m) (d + 1) y`
   contained in the flattened complement image;
2. a flat local recovery theorem for the transported boundary functional
   `Tflat`, specialized to the canonical flat approach direction
   `flattenCLEquivReal (n + m) (d + 1)
      (canonicalForwardConeDirection (d := d) (n + m))`,
   concluding the supported-test identity
   `Tflat fflat = ∫ xflat, G_t (SCV.realEmbed xflat) * fflat xflat`.

This is why the old one-theorem diagnosis collapses: after local continuity is
supplied, there is still no existing source theorem that turns the transported
weak BV data plus only the canonical-direction shell bound into the required
local recovered integral formula.

Supervision correction (`2026-04-16 03:56 UTC`, bounded theorem-(2)
statement/proof-chain pin): the exact missing second theorem is now fixed more
sharply. After setting

- `T_t` to the CLM from
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`,
- `Tflat fflat := T_t ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (flattenCLEquivReal (n + m) (d + 1))) fflat)`,
- `η0flat := flattenCLEquivReal (n + m) (d + 1)
    (canonicalForwardConeDirection (d := d) (n + m))`,

the honest theorem-(2) surface should consume only:

- the open-set package `Uflat`, `IsOpen Uflat`,
  `flattenCLEquivReal (n + m) (d + 1) y ∈ Uflat`,
  `Uflat ⊆ (flattenCLEquivReal (n + m) (d + 1)) ''
    ((section43PositiveEnergyRegion d (n + m))ᶜ)`,
- the explicit local continuity hypothesis
  `hcontUflat : ∀ xflat ∈ Uflat, ContinuousWithinAt G_t
    (SCV.TubeDomain (ForwardConeFlat d (n + m)))
    (SCV.realEmbed xflat)`,
- the already existing weak flat BV witness transported from `T_t`.

It should conclude exactly:

- `∀ fflat, tsupport (fflat : _ → ℂ) ⊆ Uflat →
    HasCompactSupport (fflat : _ → ℂ) →
    Tflat fflat = ∫ xflat, G_t (SCV.realEmbed xflat) * fflat xflat`.

No extra fixed-time shell growth hypothesis should appear in theorem (2)
itself: those hypotheses are only needed by the abandoned tempered consumer
route, while the replacement theorem is supposed to bypass the unavailable
all-directions `uniform_bound` field entirely.

Exact consumer chain to keep honest:

- theorem (1) furnishes `hcontUflat`;
- theorem (2) supplies the supported-test identity on the flat side;
- `schwartz_bv_to_flat_repr_dist_apply` rewrites `Tflat` back to the product
  CLM `T_t`;
- the existing flatten change-of-variables/localizer bookkeeping returns to the
  product-coordinate shell functional used in the coefficient theorem;
- shrinking localizers centered at `y` then feed
  `section43_fixedTimeShellRaw_coefficient_tendsto_zero_on_section43PositiveEnergyRegion_compl`.

Why weaker candidates still fail:

- theorem (1) alone only gives local continuity and never connects the actual
  boundary functional `T_t` to local test integrals;
- a generic flatten-transport wrapper only repackages coordinates and does not
  produce the supported-test identity;
- any theorem phrased only for the single point `y` is too weak for shrinking
  localizers, which need an open neighborhood support statement.

Supervision correction (`2026-04-16`, bounded insertion-site reread): the
source reread now fixes the exact theorem home as well as the statement. The
missing theorem is still one local boundary-trace theorem for the flattened
fixed-time continuation, and the honest insertion site is local to
`OSToWightmanPositivity.lean`, immediately above the live coefficient theorem.
It should not be promoted to a generic flatten-transport theorem, because the
generic flatten machinery already exists:
`differentiableOn_flatten`,
`schwartz_bv_to_flat_repr`,
`schwartz_bv_to_flat_repr_dist_apply`,
and the flat constructor
`SCV.exists_fourierLaplaceReprTempered`.

So the exact remaining source object is still:

- for fixed complement witness `y`, an open
  `Uflat : Set (Fin ((n + m) * (d + 1)) → ℝ)` with
  `flattenCLEquivReal (n + m) (d + 1) y ∈ Uflat`,
  `Uflat ⊆ flattenCLEquivReal (n + m) (d + 1) ''
    ((section43PositiveEnergyRegion d (n + m))ᶜ)`,
  and
  `∀ xflat ∈ Uflat, ContinuousWithinAt G_t
    (SCV.TubeDomain (ForwardConeFlat d (n + m)))
    (SCV.realEmbed xflat)`.

That local `ContinuousWithinAt` package is still exactly what the existing SCV
consumer needs, and no smaller theorem avoids it.

Supervision correction (`2026-04-16`, bounded reread with flatten check): the
reread corrected one insertion-site detail in the previous notes. The missing
theorem is still just one local boundary-trace theorem, but the honest source
target is the flattened shell continuation, not the raw product-coordinate
`F_t`, because the only existing local recovery theorem is flat.

Concretely, after fixing

- `j := ⟨n, Nat.lt_add_of_pos_right hm⟩`,
- `e := flattenCLEquiv (n + m) (d + 1)`,
- `eR := flattenCLEquivReal (n + m) (d + 1)`,
- `G_t zflat := bvt_F OS lgc (n + m) (xiShift j 0 (e.symm zflat) (t : ℂ))`,

the current source already supplies everything except local boundary continuity:

- weak flat BV data from
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`
  through `ForwardTubeDistributions.schwartz_bv_to_flat_repr`;
- flat tempered packaging from the existing holomorphicity and growth bounds via
  `SCV.exists_fourierLaplaceReprTempered`.

So the only missing source object is:

- for fixed complement witness `y`,
  an open `Uflat` with `eR y ∈ Uflat` and
  `Uflat ⊆ eR '' ((section43PositiveEnergyRegion d (n + m))ᶜ)`,
  together with
  `∀ xflat ∈ Uflat, ContinuousWithinAt G_t
    (SCV.TubeDomain (ForwardConeFlat d (n + m)))
    (SCV.realEmbed xflat)`.

That is the exact input consumed by
`SCV.fourierLaplace_boundary_recovery_on_open_of_tempered`; no smaller theorem
avoids this, and no extra transport theorem is mathematically forced because
the flattening steps already exist inline in source.

Supervision correction (`2026-04-16 03:22 UTC`, bounded reread): the reread now
pins the live frontier at exact constructor level. The first missing theorem is
still the local boundary-trace theorem for the fixed-time shell continuation,
not a larger weak-to-regular upgrade package. Source reason: once

- `F_t z := bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))`

is fixed, current source already provides every ingredient needed for
`SCV.exists_fourierLaplaceReprTempered`:

- holomorphy of `F_t` is re-proved directly inside
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`;
- the boundary functional there is the required `T_t`;
- `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth` and
  `section43_fixedTimeShellRaw_uniformPolyGrowth_fixedTime` provide the
  tempered growth inputs.

So the only missing source object is still:

- near any fixed complement witness
  `y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  an open neighborhood `U` with
  `y ∈ U ⊆ (section43PositiveEnergyRegion d (n + m))ᶜ`
  and
  `∀ x ∈ U, ContinuousWithinAt F_t
    (TubeDomainSetPi (ForwardConeAbs d (n + m))) (SCV.realEmbed x)`.

That is exactly what `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered`
consumes after the tempered package is assembled, and every weaker-looking
candidate still reduces back to that same missing local trace.

Supervision correction (`2026-04-16 03:02 UTC`, bounded reread): the reread now
isolates the first genuinely new theorem surface that would make the
shrinking-localizer route honest. It is not a theorem about the localizer
family alone. It is a theorem giving a **continuous local boundary trace** for
the fixed-time shell continuation
`F_t z := bvt_F OS lgc (n + m) (xiShift ... z (t : ℂ))`
on an open real neighborhood of the shell point determined by the complement
witness `y`. This is exactly the missing hypothesis `hcontU` required by the
already existing local recovery theorem
`fourierLaplace_boundary_recovery_on_open_of_tempered`. Without that trace
package, the weak CLM `T_t` still has no source-backed identification with any
local function or measure near `y`, so neither a shrinking bump family nor a
pointwise `boundaryPointwise` limit can discharge the coefficient theorem.

Supervision correction (`2026-04-16 04:05 UTC`, bounded reread): the reread now
pins the first missing theorem as a single exact local-trace statement, not a
cluster. Existing source already lets the fixed-time shell continuation be
packaged as a tempered Fourier-Laplace object once the CLM `T_t` is known:
`exists_fourierLaplaceReprTempered` is only a constructor, and the needed
holomorphicity and growth inputs for
`F_t z := bvt_F OS lgc (n + m) (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))`
are already present. So the only missing source object is:

- for a fixed complement witness
  `y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  some open neighborhood `U` with
  `y ∈ U ⊆ (section43PositiveEnergyRegion d (n + m))ᶜ`
  together with
  `∀ x ∈ U, ContinuousWithinAt F_t
    (TubeDomainSetPi (ForwardConeAbs d (n + m))) (SCV.realEmbed x)`.

That is exactly the `hcontU` input consumed by
`fourierLaplace_boundary_recovery_on_open_of_tempered`, and after that current
source can identify the fixed-time boundary functional with integration against
the concrete local boundary trace on tests supported in `U`. Every weaker
candidate still collapses back to this same absent bridge.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T03:02Z`):

- direct reread of the first missing package:
  local `ContinuousWithinAt` data for the fixed-time shell continuation near the
  complement-side shell point;
- direct reread of the consumer chain:
  that local trace is what lets current source invoke
  `fourierLaplace_boundary_recovery_on_open_of_tempered`, after which the
  shrinking-localizer step becomes ordinary continuous-function evaluation;
- direct reread of why smaller candidates still fail:
  no theorem only about `T_t (φ_N)`, uniqueness, or existential pointwise
  limits can avoid first representing `T_t` by an honest local boundary trace.

Supervision correction (`2026-04-16 03:20 UTC`, bounded reread): the reread of
the exact regular/pointwise theorem surfaces confirms that no hidden
point-evaluation bridge exists below the live coefficient theorem.
`WightmanAnalyticity.boundaryPointwise` only records existence of a pointwise
boundary limit; it does not connect that limit to the chosen boundary
distribution or to the fixed-time CLM `T_t`. The SCV side only turns a
boundary-value functional into evaluation against a concrete boundary trace
after additional continuity input: globally via
`HasFourierLaplaceReprRegular.boundary_continuous` and
`tube_continuousWithinAt`, or locally via the open-set hypothesis `hcontU` in
`fourierLaplace_boundary_recovery_on_open_of_tempered`. The fixed-time shell
package reaches none of those surfaces. So the missing ingredient is still
regular/local boundary continuity near the shell point determined by the fixed
complement witness `y`.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T03:20Z`):

- direct reread of `boundaryPointwise`:
  existence of some scalar limit at fixed real `x` and cone direction `η`,
  with no identification of that limit with the weak boundary functional;
- direct reread of the only recovery surfaces:
  `fourierLaplace_boundary_recovery` needs
  `HasFourierLaplaceReprRegular`;
  `fourierLaplace_boundary_recovery_on_open_of_tempered` still needs a local
  continuous trace hypothesis `hcontU`;
  `boundary_value_zero_of_regular` then uses that regular recovery theorem;
- direct reread verdict:
  the coefficient-limit theorem remains the exact frontier, and the missing
  ingredient is continuous boundary trace at the fixed shell point or on an
  open neighborhood around it, not merely another distributional or uniqueness
  statement.

Supervision correction (`2026-04-16 02:41 UTC`, bounded reread): the reread now
closes the last plausible hidden-API possibility on the tempered side. The
remaining theorems in `SCV/LaplaceSchwartz.lean` about tempered boundary values
only say that the boundary functional is linear and uniquely determined on each
fixed Schwartz test; they do not turn it into an actual boundary function or
measure, and they do not say anything about a shrinking localizer family
`φ_N`. The OS-side theorem `boundary_values_tempered` and its exported form
`bvt_boundary_values` likewise stop at fixed-test convergence of a continuous
linear functional. OS II `(5.4)` explicitly keeps the other variables
distributional, so the paper matches the code on this point.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T02:41Z`):

- direct reread of the last checked tempered-side surfaces:
  `fourierLaplace_dist_map_add_tempered`,
  `fourierLaplace_dist_map_smul_tempered`,
  `fourierLaplace_dist_isLinearMap_tempered`,
  `fourierLaplace_repr_dist_unique`,
  `boundary_values_tempered`,
  `bvt_boundary_values`;
- direct reread of what they do not provide:
  no local function/measure realization of the fixed-time CLM `T_t`,
  no theorem on `T_t (φ_N)` for shrinking supported localizers near `y`,
  no theorem interchanging the localizer limit with the shell limit
  `ε → 0+`;
- direct reread verdict:
  the coefficient-limit theorem remains the exact frontier, and current source
  now rules out not only a missing regularity hypothesis but also any hidden
  fixed-test uniqueness/linearity theorem as a bridge to local shell
  evaluation.

Supervision correction (`2026-04-16 02:38 UTC`, bounded reread): the reread now
shows that the missing bridge is not merely absent for the specific fixed-time
supplier; it is absent as an explicit theorem surface in the SCV layer.
`SCV/LaplaceSchwartz.lean` distinguishes a weak tempered boundary-value package
from a stronger regular package with continuous real-boundary trace and
interior-to-boundary continuity. The file also says directly that the theorem
constructing the regular package from genuine Fourier-Laplace input is not yet
formalized. So the fixed-time shell supplier can only land in the weak package,
and none of the existing recovery/uniqueness theorems can upgrade it to local
shell evaluation on shrinking supported tests near the complement witness `y`.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T02:38Z`):

- direct reread of the SCV package split:
  `HasFourierLaplaceReprTempered` gives distributional boundary values plus
  growth bounds;
  `HasFourierLaplaceReprRegular` adds `boundary_continuous` and
  `tube_continuousWithinAt`;
- direct reread of the exact missing theorem surface:
  `SCV/LaplaceSchwartz.lean` explicitly says the weak-to-regular upgrade is not
  yet formalized, so downstream theorems take regularity as extra input rather
  than derive it;
- direct reread of the consequence for the live shell theorem:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` only reaches the
  weak side, hence there is still no source-backed theorem identifying
  `lim_N T_t (φ_N)` for shrinking localizers with shell evaluation at the
  complement point or allowing the needed limit interchange;
- direct reread verdict:
  the coefficient-limit theorem remains the exact frontier, and current source
  now documents that crossing it requires new mathematics producing the missing
  regular boundary-trace package, not a hidden existing API theorem.

Supervision correction (`2026-04-16 02:27 UTC`, bounded reread): the reread of
the SCV recovery layer sharpened the live obstruction. The repo does have a
local theorem turning a tempered boundary-value functional into integration
against an honest boundary trace on supported tests,
`SCV.fourierLaplace_boundary_recovery_on_open_of_tempered`, but it only applies
when the holomorphic tube function is already known to have a continuous
boundary trace on some open real set `U` (`hcontU`). Nothing in the fixed-time
shell package gives that near the complement witness `y`, so the weak
functional `T_t` still does not localize to shell evaluation.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T02:27Z`):

- direct reread of the missing upgrade theorem shape:
  local boundary recovery in `SCV/LocalBoundaryRecovery.lean` requires
  `hcontU`, i.e. a continuous boundary trace on an open real neighborhood;
- direct reread of the fixed-time gap:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` supplies only
  the weak CLM functional `T_t`, with no open-set boundary continuity near the
  complement shell point;
- direct reread of the failed localizer route:
  shrinking Schwartz bumps / approximate identities around `y`;
  these still fail because current source has no theorem identifying
  `T_t (φ_N)` with integration against a concrete local boundary trace;
- direct reread verdict:
  the coefficient-limit theorem remains the exact frontier, now with the
  sharper diagnosis that the missing ingredient is the absent `hcontU`-type
  local boundary trace hypothesis for the fixed-time shell continuation.

Supervision correction (`2026-04-16 03:07 UTC`, bounded reread): the reread now
ties the live obstruction to an explicit distinction already built into the
repo's abstract theorem surface. `WightmanAxioms.WightmanAnalyticity` separates
distributional boundary convergence (`boundaryValue`) from pointwise boundary
limits (`boundaryPointwise`). The current fixed-time shell theorem only yields
the first kind of object, namely a CLM `T_t` acting on fixed Schwartz tests.
So the natural localization attempt with a shrinking Schwartz bump /
approximate-identity family at the complement shell point `y` still has no
source-backed bridge to point evaluation.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T03:07Z`):

- direct reread of the abstract boundary-value split:
  `WightmanAxioms.lean:726-778` treats weak/distributional boundary values and
  honest pointwise boundary limits as separate inputs;
- direct reread of the fixed-time theorem shape:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` gives only
  `T_t h` for fixed Schwartz `h`, i.e. only the weak side of that split;
- direct reread of the failed localizer route:
  a shrinking Schwartz bump / approximate identity around `y`;
  this fails because no current theorem identifies `lim_N T_t (φ_N)` with shell
  evaluation or allows exchanging that limit with `ε → 0+`;
- direct reread verdict:
  the coefficient-limit theorem remains the exact frontier, because the missing
  theorem is a pointwise boundary-localization input of `boundaryPointwise`
  type, absent from the present OS II / SCV package.

Supervision correction (`2026-04-16 02:42 UTC`, bounded reread): the reread now
identifies the failed localization route more exactly. The fixed-time theorem
does not merely stop short of a continuity statement; it stops at a weak
boundary-value functional on Schwartz tests. A shrinking local Schwartz family
near the complement shell point `y` is the obvious candidate to recover
pointwise information, but the current package has no theorem for the second
limit on that family and no representation theorem for `T_t`. So the route from
weak boundary values to shell-point evaluation is absent in exactly the way the
coefficient-limit theorem needs.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T02:42Z`):

- direct reread of the blocking theorem shape:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` gives only
  `T_t h` for each fixed Schwartz test `h`;
- direct reread of the failed local family:
  a shrinking Schwartz bump / approximate-identity family centered at the real
  shell point of the complement witness `y`;
  this fails because current code contains no theorem identifying
  `lim_N T_t (φ_N)` with shell evaluation, and no interchange theorem between
  `N → ∞` and `ε → 0+`;
- direct reread of the only nearby evaluation theorem:
  `bv_zero_point_is_evaluation` is special to the `n = 0` normalization case and
  depends on a separate Euclidean restriction identity, not on generic boundary
  localization;
- direct reread verdict:
  the coefficient-limit theorem remains the exact frontier; the missing
  mathematics is a source-backed localization/representation theorem for the
  fixed-time boundary functional `T_t`, not further shell geometry.

Supervision correction (`2026-04-16 02:13 UTC`, bounded reread): the reread now isolates the exact reason the coefficient-limit stub does not reduce further. The natural candidate sub-lemma inside the theorem,
that the canonical shell input itself converges to the `ε = 0` real-shell point,
is true but useless for the live seam: `bvt_F` is only controlled as a
holomorphic function on the open forward tube plus a weak boundary-value
functional on Schwartz tests, not as a pointwise boundary-continuous function
on the shell. So the blocked next line is not shell geometry but pointwise
boundary localization of `bvt_F` at the complement-side shell point `y`.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T02:13Z`):

- direct reread of the missing source object:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` provides only a
  boundary-value functional `T_t` acting on Schwartz tests;
  it does not turn the coefficient at fixed `y` into a known boundary value;
- direct reread of the rejected smaller lemma:
  “`ε ↦ xiShift ...` tends to its `ε = 0` boundary point”;
  rejected because this says nothing about whether
  `bvt_F OS lgc (n + m)` admits the needed pointwise boundary limit there;
- direct reread verdict:
  the live frontier remains exactly the coefficient-limit theorem, now with the
  sharper diagnosis that the missing ingredient is pointwise boundary
  regularity/localization rather than any further shell rewrite.

Supervision correction (`2026-04-16 01:57 UTC`, bounded reread): the direct reread now supports one honest theorem-sized lowering of the seam. In the live complement branch, the first missing result is not the full
`bvt_F ... * h y` limit, but the coefficient-only canonical-shell limit at fixed
outside-region `y`; `h` and `hq` are inherited from the larger ambient theorem
and do not belong to the first missing statement itself. A private stub for that
coefficient limit is now placed directly above the ambient dominated-convergence
theorem, and the pointwise branch calls it. The reread still finds no smaller
source-backed feeder below that statement.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T01:57Z`):

- reread statement of the first missing theorem:
  fixed `y` with
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  prove
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- reread on essential versus inherited data:
  essential:
  the canonical shell data and the outside-region witness `hy`;
  inherited noise:
  `h`, `h y`, the indicator wrapper, and `hq`;
- reread on minimality:
  no fixed-time existence theorem, quotient lemma, shell realization lemma, or
  paper statement below this point already removes the outside-region
  contribution on the actual shell;
- reread on placement:
  the theorem belongs as a nearby private lemma in
  `OSToWightmanPositivity.lean`, not in `Section43Codomain.lean`, because it is
  a shell-coefficient limit theorem rather than a quotient-transport theorem.

Supervision correction (`2026-04-16 01:51 UTC`, bounded reread): re-read the live theorem body with the later `hlimit_os` case-`(3)` decomposition kept in view simultaneously, then rechecked the earlier fixed-time shell existence theorem, the immediately following dominated-convergence closure, the on-region shell realization / weight-comparison cluster, the nearest quotient lemmas, and OS II formula `(5.4)` on printed page `291`. No honest retained Lean step was found below the current complement branch. After `simp only [F, indicator_of_mem hy]`, the body still asks for the same fixed-`y` complement-side scalar shell limit; pulling out `h y` still only exposes the same canonical-shell coefficient limit; the earliest meaningful coefficient-limit theorem surface is still only that blocker restated; the generic dominated-convergence theorem still assumes exactly that pointwise limit as `hlim`; the fixed-time shell existence theorem gives only existence of some ambient limit functional; the shell realization / quotient transport lemmas still stop on `section43PositiveEnergyRegion`; the later `hlimit_os` case `(3)` failure is the same outside-region mathematics one level higher rather than a new lower feeder; and OS II `(5.4)` still gives only the fixed-time semigroup / one-variable analytic-continuation statement. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T01:51Z`):

- direct reread of the branch goal:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of why factoring out `h y` is not progress:
  the only natural local refactor is still to view `h y` as a constant scalar
  and reduce to the coefficient limit for the same shell family;
  that does not lower the route, because the complement witness `hy` gives no
  information about `h y`;
- direct reread of why the coefficient-limit theorem surface is not new:
  at the first meaningful insertion point, the coefficient-limit theorem is
  still just the same missing mathematics with `h y` removed, not a stricter
  source-backed lemma below the seam;
- direct reread of why the later case-`(3)` failure does not lower the route:
  the decomposition under `hlimit_os` already kills the source-support and
  on-region / outside-source branches, then fails exactly for
  `y ∉ section43PositiveEnergyRegion d (n + m)` at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9888);
  this is the same missing complement-side control seen one integral-comparison
  level higher, not a new fixed-`y` supplier below the current branch;
- direct reread of the nearest source objects:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131)
  supplies existence of some ambient limit functional only;
  the generic dominated-convergence closure at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4566)
  still requires the same pointwise limit as input `hlim`, so it is not a new
  source-backed seam-local lemma;
  the shell realization / weight-comparison lemmas at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:8916),
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9095),
  and [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9126)
  still stop on `section43PositiveEnergyRegion`;
  the quotient API lemmas at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still stop on-region;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only
  the fixed-time semigroup / one-variable analytic-continuation package with
  distributional dependence on the remaining variables;
- exact reading verdict:
  the first missing mathematics remains the complement-side coefficient limit for
  the canonical shell family;
  no reread source presently gives complement-localization, quotient-zero-on-
  complement, or a stricter fixed-`y` complement-shell vanishing theorem below
  this branch.

Supervision correction (`2026-04-16 01:41 UTC`, bounded reread): re-read the live theorem body with explicit focus on whether any stricter source-backed insertion point exists below the coefficient-limit restatement, then rechecked the earlier fixed-time shell existence theorem, the immediately following dominated-convergence closure, the on-region shell realization / weight-comparison cluster, the nearest quotient lemmas, and OS II formula `(5.4)` on printed page `291`. No honest retained Lean step was found below the current complement branch. After `simp only [F, indicator_of_mem hy]`, the body still asks for the same fixed-`y` complement-side scalar shell limit; pulling out `h y` still only exposes the same canonical-shell coefficient limit; the earliest meaningful coefficient-limit theorem surface is still only that blocker restated; the generic dominated-convergence theorem still assumes exactly that pointwise limit as `hlim`; the fixed-time shell existence theorem gives only existence of some ambient limit functional; the shell realization / quotient transport lemmas still stop on `section43PositiveEnergyRegion`; and OS II `(5.4)` still gives only the fixed-time semigroup / one-variable analytic-continuation statement. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T01:41Z`):

- direct reread of the branch goal:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of why factoring out `h y` is not progress:
  the only natural local refactor is still to view `h y` as a constant scalar
  and reduce to the coefficient limit for the same shell family;
  that does not lower the route, because the complement witness `hy` gives no
  information about `h y`;
- direct reread of why the coefficient-limit theorem surface is not new:
  at the first meaningful insertion point, the coefficient-limit theorem is
  still just the same missing mathematics with `h y` removed, not a stricter
  source-backed lemma below the seam;
- direct reread of the nearest source objects:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131)
  supplies existence of some ambient limit functional only;
  the generic dominated-convergence closure at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4566)
  still requires the same pointwise limit as input `hlim`, so it is not a new
  source-backed seam-local lemma;
  the shell realization / weight-comparison lemmas at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:8916),
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9095),
  and [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9126)
  still stop on `section43PositiveEnergyRegion`;
  the quotient API lemmas at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still stop on-region;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only
  the fixed-time semigroup / one-variable analytic-continuation package with
  distributional dependence on the remaining variables;
- exact reading verdict:
  the first missing mathematics remains the complement-side coefficient limit for
  the canonical shell family;
  no reread source presently gives complement-localization, quotient-zero-on-
  complement, or a stricter fixed-`y` complement-shell vanishing theorem below
  this branch.

Supervision correction (`2026-04-16 01:32 UTC`, bounded reread): re-read the live theorem body, the earlier fixed-time shell boundary-value existence theorem, the immediately following dominated-convergence closure, the on-region shell realization / weight-comparison cluster, the nearest quotient lemmas, and OS II formula `(5.4)` on printed page `291`. No honest retained Lean step was found below the current complement branch. After `simp only [F, indicator_of_mem hy]`, the body still asks for the same fixed-`y` complement-side scalar shell limit; pulling out `h y` still only exposes the same canonical-shell coefficient limit; the earliest meaningful coefficient-limit theorem surface is still only that blocker restated; the generic dominated-convergence theorem still assumes exactly that pointwise limit as `hlim`; the fixed-time shell existence theorem gives only existence of some ambient limit functional; the shell realization / quotient transport lemmas still stop on `section43PositiveEnergyRegion`; and OS II `(5.4)` still gives only the fixed-time semigroup / one-variable analytic-continuation statement. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T01:32Z`):

- direct reread of the branch goal:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of why factoring out `h y` is not progress:
  the only natural local refactor is still to view `h y` as a constant scalar
  and reduce to the coefficient limit for the same shell family;
  that does not lower the route, because the complement witness `hy` gives no
  information about `h y`;
- direct reread of why the coefficient-limit theorem surface is not new:
  at the first meaningful insertion point, the coefficient-limit theorem is
  still just the same missing mathematics with `h y` removed, not a stricter
  source-backed lemma below the seam;
- direct reread of the nearest source objects:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131)
  supplies existence of some ambient limit functional only;
  the complement-eventual-bound theorem at line `4430` still supplies domination only;
  the generic dominated-convergence closure at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4566)
  still requires the same pointwise limit as input `hlim`, so it is not a new
  source-backed seam-local lemma;
  the shell realization / weight-comparison lemmas at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:8916),
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9095),
  and [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9126)
  still stop on `section43PositiveEnergyRegion`;
  the quotient API lemmas at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still stop on-region;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only
  the fixed-time semigroup / one-variable analytic-continuation package with
  distributional dependence on the remaining variables;
- exact reading verdict:
  the first missing mathematics remains the complement-side coefficient limit for
  the canonical shell family;
  no reread source presently gives complement-localization, quotient-zero-on-
  complement, or fixed-`y` complement-shell vanishing below this branch.

Supervision correction (`2026-04-16 01:16 UTC`, bounded reread): re-read the live theorem body, the immediately following generic dominated-convergence closure, the nearest quotient lemmas, the downstream `hlimit_os` note, and OS II formula `(5.4)` on printed page `291`. No honest retained Lean step was found below the current complement branch. After `simp only [F, indicator_of_mem hy]`, the body still asks for the same fixed-`y` complement-side scalar shell limit; pulling out `h y` still only exposes the same canonical-shell coefficient limit; the generic dominated-convergence theorem still assumes exactly that pointwise limit as `hlim`; the quotient API still controls `h` only on `section43PositiveEnergyRegion`; and OS II `(5.4)` still gives only the fixed-time semigroup / one-variable analytic-continuation statement. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T01:16Z`):

- direct reread of the branch goal:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of why factoring out `h y` is not progress:
  the only natural local refactor is still to view `h y` as a constant scalar
  and reduce to the coefficient limit for the same shell family;
  that does not lower the route, because the complement witness `hy` gives no
  information about `h y`;
- direct reread of the nearest source objects:
  the complement-eventual-bound theorem at line `4430` still supplies domination only;
  the generic dominated-convergence closure at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4566)
  still requires the same pointwise limit as input `hlim`, so it is not a new
  source-backed seam-local lemma;
  the quotient API lemmas at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still stop on `section43PositiveEnergyRegion`;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only
  the fixed-time semigroup / one-variable analytic-continuation package with
  distributional dependence on the remaining variables;
- exact reading verdict:
  the first missing mathematics remains the complement-side coefficient limit for
  the canonical shell family;
  no reread source presently gives complement-localization, quotient-zero-on-
  complement, or fixed-`y` complement-shell vanishing below this branch.

Supervision correction (`2026-04-16 01:06 UTC`, bounded reread): re-read the live theorem body and nearest sources on the exact seam, then re-ran a targeted search in `OSToWightmanPositivity.lean` for any existing coefficient-limit theorem on the same canonical `xiShift` shell. No honest retained Lean step was found below the current complement branch. After `simp only [F, indicator_of_mem hy]`, the body still asks for the same fixed-`y` complement-side scalar shell limit; pulling out `h y` still only exposes the same canonical-shell coefficient limit; the quotient API still controls `h` only on `section43PositiveEnergyRegion`; the local search found no already-landed coefficient-limit supplier; and OS II `(5.4)` still gives only the fixed-time semigroup / one-variable analytic-continuation statement. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T01:06Z`):

- direct reread of the branch goal:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of why factoring out `h y` is not progress:
  the only natural local refactor is still to view `h y` as a constant scalar
  and reduce to the coefficient limit for the same shell family;
  that does not lower the route, because the complement witness `hy` gives no
  information about `h y`;
- direct reread of the nearest source objects:
  the complement-eventual-bound theorem at line `4430` still supplies domination only;
  the quotient API lemmas at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still stop on `section43PositiveEnergyRegion`;
  the targeted local search found no theorem already proving the missing
  complement-side coefficient limit for this exact `xiShift` shell;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only
  the fixed-time semigroup / one-variable analytic-continuation package with
  distributional dependence on the remaining variables;
- exact reading verdict:
  the first missing mathematics remains the complement-side coefficient limit for
  the canonical shell family;
  no reread source presently gives complement-localization, quotient-zero-on-
  complement, or fixed-`y` complement-shell vanishing below this branch.

Supervision correction (`2026-04-16 01:01 UTC`, bounded reread): re-read the live theorem body and nearest sources on the exact seam and again found no honest retained Lean step below the current complement branch. After `simp only [F, indicator_of_mem hy]`, the body still asks for the same fixed-`y` complement-side scalar shell limit; pulling out `h y` still only exposes the same canonical-shell coefficient limit; the quotient API still controls `h` only on `section43PositiveEnergyRegion`; and OS II `(5.4)` still gives only the fixed-time semigroup / one-variable analytic-continuation statement. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T01:01Z`):

- direct reread of the branch goal:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of why factoring out `h y` is not progress:
  the only natural local refactor is to view `h y` as a constant scalar and reduce to the coefficient limit for the same shell family;
  that does not lower the route, because the complement witness `hy` gives no information about `h y`;
- direct reread of the nearest source objects:
  the complement-eventual-bound theorem at line `4430` still supplies domination only;
  the quotient API lemmas at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still stop on `section43PositiveEnergyRegion`;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package with distributional dependence on the remaining variables;
- exact reading verdict:
  the first missing mathematics remains the complement-side coefficient limit for the canonical shell family;
  no reread source presently gives complement-localization, quotient-zero-on-complement, or fixed-`y` complement-shell vanishing below this branch.

Supervision correction (`2026-04-16 00:56 UTC`, bounded reread): re-read the live theorem body and nearest sources on the exact seam and again found no honest retained Lean step below the current complement branch. After `simp only [F, indicator_of_mem hy]`, the body still asks for the same fixed-`y` complement-side scalar shell limit; pulling out `h y` still only exposes the same canonical-shell coefficient limit; the quotient API still controls `h` only on `section43PositiveEnergyRegion`; and OS II `(5.4)` still gives only the fixed-time semigroup / one-variable analytic-continuation statement. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T00:56Z`):

- direct reread of the branch goal:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of why factoring out `h y` is not progress:
  the only natural local refactor is to view `h y` as a constant scalar and reduce to the coefficient limit for the same shell family;
  that does not lower the route, because the complement witness `hy` gives no information about `h y`;
- direct reread of the nearest source objects:
  the complement-eventual-bound theorem at line `4430` still supplies domination only;
  the quotient API lemmas at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still stop on `section43PositiveEnergyRegion`;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package with distributional dependence on the remaining variables;
- exact reading verdict:
  the first missing mathematics remains the complement-side coefficient limit for the canonical shell family;
  no reread source presently gives complement-localization, quotient-zero-on-complement, or fixed-`y` complement-shell vanishing below this branch.

Supervision correction (`2026-04-16 00:51 UTC`, bounded reread): one more bounded reread of the exact live seam again found no honest retained Lean step below the current complement branch. After `simp only [F, indicator_of_mem hy]`, the body still asks for the same fixed-`y` complement-side scalar shell limit; pulling out the constant `h y` still only exposes the same missing canonical-shell coefficient limit; the quotient API still controls `h` only on `section43PositiveEnergyRegion`; and OS II `(5.4)` still gives only the fixed-time semigroup / one-variable analytic continuation statement. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T00:51Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of why factoring out `h y` is not progress:
  the natural local factorization through the constant scalar `h y` is mathematically equivalent here and does not lower the route;
  it simply renames the blocker as the coefficient limit for the same canonical shell family;
- direct reread of the nearest source objects:
  the complement-eventual-bound theorem at line `4430` still supplies domination only;
  the quotient API lemmas at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still stop on `section43PositiveEnergyRegion`;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package with distributional dependence on the remaining variables;
- exact reading verdict:
  the first missing mathematics remains the complement-side coefficient limit for the canonical shell family;
  no reread source presently gives complement-localization, quotient-zero-on-complement, or fixed-`y` complement-shell vanishing below this branch.

Supervision correction (`2026-04-16 00:31 UTC`, bounded reread): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II printed page `291`, formula `(5.4)`, via local `python3`/`PyPDF2`. The live source still confirms that there is no honest retained Lean step below the current `hy` branch: after `simp only [F, indicator_of_mem hy]`, the first remaining content is still the fixed-`y` complement-side scalar shell limit; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made; the recorded worker `rapid-falcon` has completed and there is currently no live Codex worker.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T00:31Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
  even an explicit local `have` for the regionwise quotient consequence is not retainable as progress, because it does not interact with the complement witness `hy`;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9893)
  still identifies the first live failure as the outside-region case;
  direct `PyPDF2` extraction still shows that printed page `291`, formula `(5.4)`, is PDF page `11` in the local file and gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-16`, bounded reread): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II printed page `291`, formula `(5.4)`. The live source still confirms that there is no honest retained Lean step below the current `hy` branch: after `simp only [F, indicator_of_mem hy]`, the first remaining content is still the fixed-`y` complement-side scalar shell limit; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made; the recorded worker `young-harbor` has completed and there is currently no live Codex worker.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
  a local `have` for the regionwise quotient consequence is similarly not retainable as progress, because it does not interact with the complement witness `hy`;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9893)
  still identifies the first live failure as the outside-region case;
  direct `PyPDF2` extraction still shows that printed page `291`, formula `(5.4)`, is PDF page `11` in the local file and gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-16 00:44 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II printed page `291`, formula `(5.4)`, via local `python3`/`PyPDF2`. The live source still confirms that there is no honest retained Lean step below the current `hy` branch: after `simp only [F, indicator_of_mem hy]`, the first remaining content is still the fixed-`y` complement-side scalar shell limit; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made; the recorded worker `wild-cloud` has completed and there is currently no live Codex worker.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T00:44Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
  a local `have` for the regionwise quotient consequence is similarly not retainable as progress, because it does not interact with the complement witness `hy`;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9893)
  still identifies the first live failure as the outside-region case;
  direct `PyPDF2` extraction shows that printed page `291`, formula `(5.4)`, is PDF page `11` in the local file and still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-16 00:26 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II printed page `291`, formula `(5.4)`, via local `python3`/`PyPDF2`. The live source still confirms that there is no honest retained Lean step below the current `hy` branch: after `simp only [F, indicator_of_mem hy]`, the first remaining content is still the fixed-`y` complement-side scalar shell limit; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made; the recorded worker `wild-cloud` has completed and there is currently no live Codex worker.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T00:26Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
  a local `have` for the regionwise quotient consequence is similarly not retainable as progress, because it does not interact with the complement witness `hy`;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-16 00:11 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II printed page `291`, formula `(5.4)`, via local `python3`/`PyPDF2`. The live source still confirms that there is no honest retained Lean step below the current `hy` branch: after `simp only [F, indicator_of_mem hy]`, the first remaining content is still the fixed-`y` complement-side scalar shell limit; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made; the recorded worker `nimble-crustacean` has completed and there is currently no live Codex worker.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T00:11Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
  a local `have` for the regionwise quotient consequence is similarly not retainable as progress, because it does not interact with the complement witness `hy`;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-16 00:00 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II printed page `291`, formula `(5.4)`. The live source still confirms that there is no honest retained Lean step below the current `hy` branch: after `simp only [F, indicator_of_mem hy]`, the first remaining content is still the fixed-`y` complement-side scalar shell limit; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made; `fast-seaslug` is no longer live and there is currently no active Codex worker.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
  a local `have` for the regionwise quotient consequence is similarly not retainable as progress, because it does not interact with the complement witness `hy`;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9893)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 23:49 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II printed page `291`, formula `(5.4)`, via local `python3`/`PyPDF2`. The live source still confirms that there is no honest retained Lean step below the current `hy` branch: after `simp only [F, indicator_of_mem hy]`, the first remaining content is still the fixed-`y` complement-side scalar shell limit; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:49:00Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9893)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 23:36 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II `(5.4)`. The live source still confirms that there is no honest retained Lean step below the current `hy` branch: after `simp only [F, indicator_of_mem hy]`, the first remaining content is still the fixed-`y` complement-side scalar shell limit; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. The earlier worker `crisp-mist` has exited; there is currently no live Codex worker. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:36:31Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 23:31 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II `(5.4)`, and reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. The route is idle; there is currently no live productive worker. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:31:42Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 23:21 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II `(5.4)`, and reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. There is currently no live Codex worker. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:21:04Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9893)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 23:11 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II `(5.4)`, and reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. There is currently no live Codex worker. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:11:38Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9893)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 23:02 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II `(5.4)`, and reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:02:58Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9893)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 22:56 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and a direct extract of OS II `(5.4)`, and reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T22:56:28Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9893)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 22:46 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and OS II `(5.4)`, and reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. The just-finished worker `mild-claw` was docs-only after a source-first reread, and there is currently no live Codex worker. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T22:46Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 22:41 UTC`): one bounded reread of the exact live seam rechecked the theorem body itself, the direct quotient API, the exact `hlimit_os` consumer branch, and OS II `(5.4)`, and reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T22:41Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 22:36 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables; and the just-finished worker `young-pine` completed docs-only after a source-first reread, with no live Codex worker now. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T22:36Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 22:31 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables; and the just-finished worker `nimble-claw` was docs-only, with no live Codex worker now. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T22:31Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 22:26 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables; and by `2026-04-15 22:26 UTC` there is no live Codex worker. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T22:26:21Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9893)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 22:21 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables; and by `2026-04-15 22:20 UTC` there is again no live Codex worker. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T22:21:36Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 22:16 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; the direct `hlimit_os` consumer still fails first in outside-region case `(3)`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T22:16:59Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 22:06 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T22:06:40Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 22:02 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The exact first remaining content is still the fixed-`y` complement-side scalar shell limit after `simp only [F, indicator_of_mem hy]`; the quotient API still only controls `h` on `section43PositiveEnergyRegion`; and OS II `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the remaining variables. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T22:02:03Z`):

- direct reread of the first remaining local branch:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of the nearest definitions/consumers:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the quotient API lemma
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  still turns `hq` only into
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`,
  not into any statement at the complement point `y`;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
- exact reading verdict:
  no in-body refactor survives honestly;
  even the natural factorization through the constant `h y` is not retainable, because it leaves the same missing fixed-`y` complement-side shell coefficient limit and therefore does not lower the route;
- exact insertion surface and paper status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current downstream note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9890)
  still identifies the first live failure as the outside-region case;
  OS II printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / one-variable analytic-continuation package and no separate fixed-`y` complement-shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 21:56 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. The only genuinely sharper reading point beyond the `21:42 UTC` pass is that the local quotient-zero hypothesis only says `h` vanishes on `section43PositiveEnergyRegion`, not at a complement point `y`; and OS II formula `(5.4)` still reads only as a one-variable analytic continuation statement with distributional dependence on the other variables, not as a fixed-`y` complement-shell vanishing theorem. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T21:56:57Z`):

- direct reading of the theorem hypothesis:
  from
  `hq : section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0`,
  the only available local consequence is
  `Set.EqOn (h : NPointDomain d (n + m) → ℂ) 0 (section43PositiveEnergyRegion d (n + m))`
  through
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`
  at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106);
  this cannot rewrite `h y` in the live complement case
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`;
- direct reading of OS II page `291`, formula `(5.4)`:
  the extracted text still says the right-hand side is analytic only in the single variable
  `z = x⁰ + x⁰' + τ` for `Re z > 0`,
  while still being a distribution in all the remaining variables;
  so the source still does not descend to a pointwise statement at one ambient `y`, and in particular gives no theorem that the complement-side shell coefficient at that `y` tends to `0`;
- reading verdict at the insertion surface:
  after the complement indicator is removed by
  `simp only [F, indicator_of_mem hy]`,
  the branch remains exactly the same fixed-`y` scalar shell limit, with `h y` still unconstrained and no honest smaller retained target below it.

Supervision correction (`2026-04-15 21:42 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit; the quotient API still only controls equality on `section43PositiveEnergyRegion`; and OS II formula `(5.4)` still offers no complement-shell vanishing input. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T21:42:00Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current theorem comment block at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9813)
  still identifies the first live failure as the outside-region case;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 21:31 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the only plausible local calculation, factoring out the constant `h y`, still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T21:31:37Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current theorem comment block at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9813)
  already identifies the first live failure as the outside-region case;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 21:26 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the only plausible local calculation, factoring out the constant `h y`, still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T21:26:43Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  the current theorem comment block at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9813)
  already identifies the first live failure as the outside-region case;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 21:21 UTC`): one bounded reread of the exact live seam confirmed again that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the only plausible local calculation, factoring out the constant `h y`, still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T21:21:25Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 21:16 UTC`): one bounded reread of the exact live seam confirmed again that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the natural local factorization through the constant `h y` still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T21:16:27Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 21:06 UTC`): one bounded reread of the exact live seam confirmed again that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the natural local factorization through the constant `h y` still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T21:06:37Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 20:46 UTC`): one bounded reread of the exact live seam confirmed again that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the natural local factorization through the constant `h y` still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:46:42Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 20:42 UTC`): one bounded reread of the exact live seam confirmed again that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the natural local factorization through the constant `h y` still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:41:57Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 20:36 UTC`): one bounded reread of the exact live seam confirmed again that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the natural local factorization through the constant `h y` still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:36:52Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 20:32 UTC`): one bounded reread of the exact live seam confirmed again that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the natural local factorization through the constant `h y` still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:32:23Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.

Supervision correction (`2026-04-15 20:26 UTC`): one bounded reread of the exact live seam confirmed again that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and the live source still provides no quotient-side or shell-side theorem that annihilates that scalar on the complement. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:26:39Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization “coefficient limit, then multiply by the constant `h y`” is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell theorem below this branch.

Supervision correction (`2026-04-15 20:22 UTC`): one bounded reread of the exact live seam confirms again that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and the current source still provides no quotient-side or shell-side theorem that annihilates that scalar on the complement. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:22:06Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  the theorem body now literally asks for
  `bvt_F OS lgc (n + m) (xiShift ...) * h y → 0`
  as `ε → 0+`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell theorem below this branch.

Supervision correction (`2026-04-15 20:12 UTC`): one bounded reread of the exact live complement branch confirms that the new in-body `hpointwise` contraction is real but does not create a further retained Lean step. After `simp only [F, indicator_of_mem hy]`, the branch is just the unmasked fixed-`y` complement-side shell limit, and that exact limit is still unsupported. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:12:33Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`;
- exact reread of the sharpened local branch:
  in the complement case
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  the theorem body now literally reduces to
  `bvt_F OS lgc (n + m) (xiShift ...) * h y → 0`
  as `ε → 0+`;
- exact reread of what supports it:
  the theorem-local definition `F` supplies the indicator-masked family,
  `indicator_of_mem hy` removes the mask on the complement branch,
  the complement-eventual-bound theorem supplies domination,
  and the generic DCT theorem remains only a pattern/consumer once the pointwise limit exists;
- exact reading verdict on why no Lean step survives:
  the quotient-side API from [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still says nothing on the complement, so there is no honest local rewrite to quotient-zero, no canonical-shell coefficient vanishing lemma, and no retained calculation beyond the current `simp`;
- exact insertion surface and source status:
  this remains the direct missing supplier for case (3) of `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the semigroup / analytic-continuation package and no separate complement-side shell theorem.

Supervision correction (`2026-04-15 20:02 UTC`): one bounded reread of the live source/theorem seam confirms again that no compile-clean theorem-sized contraction can be kept honestly. The complement theorem still has the same dominated-convergence body shape, but not as a direct use of the local generic theorem because the generic theorem is unmasked while the live complement statement integrates the indicator-masked family. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:02:32Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`;
- exact reread of the internal package:
  complement domination is already live,
  the generic dominated-convergence pattern is already live,
  but the local theorem
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  only covers the unmasked shell;
  the complement theorem still requires the same argument on the indicator-masked family;
- exact reread of the first still-missing obligation:
  for fixed
  `y ∉ section43PositiveEnergyRegion d (n + m)`,
  show
  `indicator ((section43PositiveEnergyRegion d (n + m))ᶜ)
      (fun y =>
        bvt_F OS lgc (n + m) (xiShift ...) * h y) y → 0`
  as `ε → 0+`,
  equivalently the outside-region unmasked shell scalar tends to `0`;
- exact reading verdict on contraction:
  this is enough to describe the theorem body mathematically, but not enough to keep an honest compile-clean Lean contraction,
  because the explicit pointwise complement limit is still open and cannot be hidden inside the body;
- exact reading verdict on theorem-size:
  no smaller theorem-sized step survives below the complement theorem,
  because any useful helper would already need to prove that same complement-side pointwise limit;
- exact insertion surface:
  the theorem stays at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514)
  and is consumed from case (3) of `hlimit_os` at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9678);
- exact source citation status:
  OS II page index `10` / printed page `291`, formula `(5.4)`,
  still gives only the fixed-time semigroup / analytic-continuation identity
  and no separate complement-side shell theorem below it;
- production Lean verdict:
  no production Lean edit was kept.

Supervision correction (`2026-04-15 20:02 UTC`): one bounded reread of the live source/theorem seam confirms again that the complement theorem has an explicit dominated-convergence route, but no compile-clean theorem-sized contraction smaller than the full complement theorem can be kept honestly because the first remaining content is still the outside-region pointwise shell limit itself. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:02:00Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`;
- exact reread of the internal package:
  complement domination is already live,
  the generic dominated-convergence supplier is already live,
  and the only missing content between them is the complement-side pointwise
  shell limit under quotient-zero on `h`;
- exact reread of the first still-missing obligation:
  for fixed
  `y ∉ section43PositiveEnergyRegion d (n + m)`,
  show
  `bvt_F OS lgc (n + m) (xiShift ...) * h y → 0`
  as `ε → 0+`;
- exact reading verdict on contraction:
  this is enough to describe the theorem body mathematically, but not enough to keep an honest compile-clean Lean contraction,
  because retaining such a contraction would still require hiding this same pointwise blocker inside the theorem body;
- exact reading verdict on theorem-size:
  no smaller theorem-sized step survives below the complement theorem,
  because any useful helper would already need to prove that same complement-side pointwise limit;
- exact insertion surface:
  the theorem stays at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514)
  and is consumed from case (3) of `hlimit_os` at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9678);
- exact source citation status:
  OS II page index `10` / printed page `291`, formula `(5.4)`,
  still gives only the fixed-time semigroup / analytic-continuation identity
  and no separate complement-side shell theorem below it;
- production Lean verdict:
  no production Lean edit was kept.

Supervision correction (`2026-04-15 19:40 UTC`): one bounded reread of the live source/theorem seam confirms that the complement theorem now has an explicit internal dominated-convergence route, but no compile-clean theorem-sized contraction smaller than the full complement theorem can be kept honestly because the first remaining content is still the outside-region pointwise shell limit itself. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T19:40:00Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`;
- exact reread of the internal package:
  complement domination is already live,
  the generic dominated-convergence supplier is already live,
  and the only missing content between them is the complement-side pointwise
  shell limit under quotient-zero on `h`;
- exact reread of the first still-missing obligation:
  for fixed
  `y ∉ section43PositiveEnergyRegion d (n + m)`,
  show
  `bvt_F OS lgc (n + m) (xiShift ...) * h y → 0`
  as `ε → 0+`;
- exact reading verdict on contraction:
  this is enough to describe the theorem body mathematically, but not enough to keep an honest compile-clean Lean contraction,
  because retaining such a contraction would still require hiding this same pointwise blocker inside the theorem body;
- exact reading verdict on theorem-size:
  no smaller theorem-sized step survives below the complement theorem,
  because any useful helper would already need to prove that same complement-side pointwise limit;
- exact insertion surface:
  the theorem stays at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514)
  and is consumed from case (3) of `hlimit_os` at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9678);
- exact source citation status:
  OS II page index `10` / printed page `291`, formula `(5.4)`,
  still gives only the fixed-time semigroup / analytic-continuation identity
  and no separate complement-side shell theorem below it;
- production Lean verdict:
  no production Lean edit was kept.

Supervision correction (`2026-04-15 19:31 UTC`): one bounded reread of the live source/theorem seam confirms again that the first missing mathematics under the complement theorem is the outside-region pointwise shell limit, but no compile-clean theorem-sized contraction smaller than the full complement theorem survives honestly. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T19:31:50Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`;
- exact reread of the strongest honest theorem package:
  complement domination is already live,
  the generic dominated-convergence supplier is already live,
  and the only missing content between them is the complement-side pointwise
  shell limit under quotient-zero on `h`;
- exact reread of the first genuinely new mathematics:
  for fixed
  `y ∉ section43PositiveEnergyRegion d (n + m)`,
  show
  `bvt_F OS lgc (n + m) (xiShift ...) * h y → 0`
  as `ε → 0+`;
- exact reading verdict on theorem-size:
  no smaller theorem-sized step survives below the complement theorem,
  because any useful local theorem or proof contraction would already need to
  prove that same complement-side pointwise limit;
- exact insertion surface:
  the theorem stays at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514)
  and is consumed from case (3) of `hlimit_os` at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9678);
- exact source citation status:
  OS II page index `10` / printed page `291`, formula `(5.4)`,
  still gives only the fixed-time semigroup / analytic-continuation identity
  and no separate complement-side shell theorem below it;
- production Lean verdict:
  no production Lean edit was kept.

Supervision correction (`2026-04-15 19:27 UTC`): one bounded reread of the live source/theorem seam confirms that the first missing mathematics under the complement theorem is the outside-region pointwise shell limit, but no theorem-sized step smaller than the full complement theorem survives honestly. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T19:27:37Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`;
- exact reread of the first genuinely new mathematics:
  for fixed
  `y ∉ section43PositiveEnergyRegion d (n + m)`,
  show
  `bvt_F OS lgc (n + m) (xiShift ...) * h y → 0`
  as `ε → 0+`;
- exact reading verdict on theorem-size:
  that pointwise statement is the first missing mathematical content, but it is
  not an honest smaller theorem-sized pass:
  the full complement theorem is already exactly the package
  pointwise complement limit
  + complement domination
  + dominated convergence;
- exact insertion surface:
  the theorem stays immediately above
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  and is consumed from case (3) of `hlimit_os`;
- exact source citation status:
  OS II page index `10` / printed page `291`, formula `(5.4)`,
  still gives only the fixed-time semigroup / analytic-continuation identity
  and no separate complement-side shell theorem below it;
- production Lean verdict:
  no production Lean edit was kept.

Supervision correction (`2026-04-15 19:24 UTC`): one bounded reread plus direct production attempt on `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl` confirmed that the domination half is now usable, but the theorem still stops exactly at the outside-region pointwise limit. The Lean attempt was fully reverted.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T19:24:49Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`;
- exact reread of the production attempt:
  the proof can now legitimately start by combining the new complement
  domination lemma with the generic dominated-convergence supplier;
- exact reread of the first still-missing obligation:
  for fixed
  `y ∉ section43PositiveEnergyRegion d (n + m)`,
  show
  `bvt_F OS lgc (n + m) (xiShift ...) * h y → 0`
  as `ε → 0+`;
- exact reading reason this is not already available:
  quotient-zero on `h` only identifies `h` with `0` on
  `section43PositiveEnergyRegion d (n + m)`,
  not on its complement;
- exact reading verdict on minimality:
  no smaller theorem-sized step survives below the complement theorem;
  a pointwise helper would already be the same complement-shell limit in
  repackaged form;
- source citation status rechecked:
  OS II page index `10` / printed page `291`, formula `(5.4)`,
  still matches only the fixed-time semigroup / analytic-continuation package
  and gives no separate theorem for complement-side shell vanishing below it;
- production Lean verdict:
  no production Lean edit was kept.

Supervision correction (`2026-04-15 19:12 UTC`): one bounded reread of the newly landed local domination lemma, the full complement theorem statement, the live `hlimit_os` consumer branch, the Section-4.3 quotient API, and the direct OS II page carrying formula `(5.4)` confirms that the domination half is now closed but the complement theorem itself is already the minimal remaining theorem surface. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T19:12:25Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`,
  consumed from case (3) of `hlimit_os`;
- exact reread of the new local progress:
  `section43_fixedTimeShellRaw_on_section43PositiveEnergyRegion_compl_eventually_bounded`
  now honestly provides the domination input for the complement-indicator shell
  integrand;
- exact reread of the internal decomposition:
  only one substantive input remains below the complement theorem,
  namely the pointwise complement-indicator limit under quotient-zero on `h`,
  after which the already-landed dominated-convergence theorem applies directly;
- exact reread of the first still-missing obligation:
  for fixed `y`,
  show the outside-region integrand tends to `0`;
  this is not supplied by the current quotient API because quotient-zero only
  controls `h` on the positive-energy region itself;
- exact reading verdict on minimality:
  no smaller theorem-sized step survives below the complement theorem;
  a pointwise/eventual-zero helper would already encode the same outside-region
  actual-shell control and so is not genuinely smaller;
- source citation status rechecked:
  OS II page index `10` / printed page `291`, formula `(5.4)`,
  still matches only the semigroup / analytic-continuation target and gives no
  separate complement theorem below this package;
- production Lean verdict:
  no production Lean edit was made.

Supervision correction (`2026-04-15 18:41 UTC`): one bounded reread of the exact live `hlimit_os` body, the outside-region complement branch, the true insertion surface, the Section-4.3 quotient API, and the direct OS II source page carrying formula `(5.4)` confirmed again that no theorem-sized step survives strictly below the outside-region complement-localization package. The only genuinely new mathematics still missing is the outside-region actual-shell complement limit itself. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T18:41:33Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact reread of the live failure:
  the proof still first fails only on the outside-region branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`
  for the actual-shell integrand
  `bvt_F OS lgc (n + m) (xiShift ...) * h y`
  under quotient-zero on `h`,
  with
  `h := (φ.conjTensorProduct ψ) - (f.conjTensorProduct g)`;
- exact reread of the theorem shape:
  the honest next statement is a limit-level outside-region
  complement-localization theorem for that actual shell integral under
  `section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0`;
- exact reason no smaller reading candidate survives:
  the localization identity is already written inside `hlimit_os`;
  the region-side vanishing information is already exhausted;
  the dominated-convergence supplier is already live;
  any coefficient-only, fixed-`ε`, or shell-functional quotient-descent
  candidate strong enough to help would already require the same outside-region
  shell control and therefore does not lower the mathematics;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  at lines `4424`-`4429`,
  then inside `hlimit_os` at lines `9564`-`9783`;
- source citation status rechecked:
  OS II page index `10` / printed page `291`, formula `(5.4)`, still matches
  only the semigroup / analytic-continuation target
  `(Ψ_n(x, ξ) | e^{-τH} Ψ_m(x', ξ'))`;
  no separate paper theorem was found for actual-shell outside-region
  complement-localization below that package;
- production Lean verdict:
  no production Lean edit was made.

Supervision correction (`2026-04-15 18:37 UTC`): one bounded reread of the exact live `hlimit_os` body, the outside-region complement branch, the dominated-convergence supplier at the true insertion surface, the Section-4.3 quotient API, and the direct OS II page-`291` source extract confirmed again that no theorem-sized step survives strictly below the outside-region complement-localization package. The only genuinely new mathematics still missing is the outside-region actual-shell complement limit itself. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T18:37:13Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact reread of the live failure:
  the proof still first fails only on the outside-region branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`
  for the actual-shell integrand
  `bvt_F OS lgc (n + m) (xiShift ...) * h y`
  under quotient-zero on `h`;
- exact reread of the theorem shape:
  the honest next statement is a limit-level outside-region
  complement-localization theorem for that actual shell integral under
  `section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0`;
- exact reason no smaller reading candidate survives:
  the localization identity is already written inside `hlimit_os`;
  the region-side vanishing information is already exhausted;
  the dominated-convergence supplier is already live;
  any coefficient-only, fixed-`ε`, or shell-functional quotient-descent
  candidate strong enough to help would already require the same outside-region
  shell control and therefore does not lower the mathematics;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  at lines `4424`-`4429`,
  then inside `hlimit_os` at lines `9564`-`9783`;
- source citation status rechecked:
  OS II printed page `291`, formula `(5.4)`, still matches only the semigroup /
  analytic-continuation target;
  no separate paper theorem was found for actual-shell outside-region
  complement-localization below that package;
- production Lean verdict:
  no production Lean edit was made.

Supervision correction (`2026-04-15 18:32 UTC`): one bounded reread of the exact live `hlimit_os` body, the full outside-region complement-localization package candidate, the landed source-region lemmas, the generic dominated-convergence supplier, the Section-4.3 quotient API, and OS II printed pages `289`-`293` confirmed again that no theorem-sized step survives strictly below that package. The only genuinely new mathematics still missing is the outside-region actual-shell complement limit itself. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T18:32:00Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact reread of the package shape:
  the honest next statement is a limit-level outside-region
  complement-localization theorem for the actual shell integral against
  `bvt_F OS lgc (n + m) (xiShift ...) * h y`
  under quotient-zero on `h`;
- exact reread of the internal decomposition:
  the three-way indicator split is already visible in `hlimit_os`;
  the source-support and in-region outside-source pieces are already killed by
  landed lemmas;
  the generic dominated-convergence theorem is already available;
  the only new content left is proving the complement piece tends to `0`;
- exact reason no smaller reading candidate survives:
  a localization identity alone is bookkeeping, not a new theorem;
  a pointwise zero lemma below the package already fails outside the region;
  a coefficient-only, fixed-`ε`, or quotient-descent theorem strong enough to
  help would already require the same outside-region control and therefore does
  not lower the mathematics;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  and then inside `hlimit_os`;
- source citation status rechecked:
  OS II printed pages `289`-`293`, especially printed page `291`, formula
  `(5.4)`, still match only the semigroup / analytic-continuation target;
  no separate paper theorem was found for actual-shell outside-region
  complement-localization below that package;
- production Lean verdict:
  no production Lean edit was made.

Supervision correction (`2026-04-15 18:27 UTC`): one bounded reread of the exact live `hlimit_os` body, the already-landed source-support and region-support lemmas, the shell-limit existence theorem, the Section-4.3 quotient lemmas, and OS II printed pages `289`-`293` confirmed again that the proof first fails only on the actual-shell outside-region branch and that no theorem-sized step sits strictly below an outside-region complement-localization package on the current source. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T18:27:00Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact reread of the live split:
  `hlimit_os` already decomposes the shell into source-support,
  in-region outside-source,
  and outside-region pieces;
- exact first unresolved reading obligation:
  the outside-region branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`
  for the actual-shell integrand
  `bvt_F OS lgc (n + m) (xiShift ...) * h y`
  under quotient-zero input on `h`;
- exact best next theorem shape from reading:
  a limit-level outside-region complement-localization theorem for that actual
  shell integral under
  `section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0`;
- exact reason no smaller reading candidate survives:
  quotient-zero only kills `h` on
  `section43PositiveEnergyRegion d (n + m)`,
  so any coefficient-only, fixed-`ε`, or shell-functional descent candidate
  strong enough to matter already requires the same outside-region shell
  control and therefore does not lower the mathematics;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  and then above the generic quotient-zero actual-shell limit branch used in
  `hlimit_os`;
- source citation status rechecked:
  OS II printed page `291`, formula `(5.4)`, re-extracted directly via
  `python3`/PyMuPDF, still matches only the semigroup /
  analytic-continuation target;
  pages `289`-`293` again showed no separate paper theorem for actual-shell
  outside-region complement-localization;
- production Lean verdict:
  no production Lean edit was made.

Supervision correction (`2026-04-15 18:21 UTC`): one bounded reread of the exact live `hlimit_os` body, the dominated-convergence supplier, and the Section-4.3 quotient lemmas confirmed again that the proof first fails only on the actual-shell outside-region branch and that no theorem-sized step sits strictly below an outside-region complement-localization package on the current source. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T18:21:42Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact reread of the live split:
  `hlimit_os` already decomposes the shell into source-support,
  in-region outside-source,
  and outside-region pieces;
- exact best next theorem shape from reading:
  a limit-level outside-region complement-localization theorem for the actual
  shell integral against
  `bvt_F OS lgc (n + m) (xiShift ...) * h y`
  under quotient-zero on `h`;
- exact reason no smaller reading candidate survives:
  quotient-zero only kills `h` on
  `section43PositiveEnergyRegion d (n + m)`,
  so any coefficient-only, fixed-`ε`, or shell-functional descent candidate
  strong enough to matter already requires the same outside-region shell
  control and therefore does not lower the mathematics;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above the future outside-region shell theorem and then above the
  generic quotient-zero actual-shell limit theorem used in `hlimit_os`;
- source citation status rechecked:
  OS II printed page `291`, formula `(5.4)`, still matches only the semigroup
  / analytic-continuation target;
  `mutool draw -F txt` again returned blank page text and no separate paper
  theorem was found for actual-shell outside-region complement-localization;
- production Lean verdict:
  no production Lean edit was made.

Supervision correction (`2026-04-15 18:24 UTC`): one more bounded reread of the exact live `hlimit_os` body confirmed again that the proof first fails only on the actual-shell outside-region branch and that no theorem-sized step sits strictly below an outside-region complement-localization package on the current source. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T18:24:00Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact reread of the live split:
  `hlimit_os` already decomposes the shell into source-support,
  in-region outside-source,
  and outside-region pieces;
- exact best next theorem shape from reading:
  a limit-level outside-region complement-localization theorem for the actual
  shell integral against
  `bvt_F OS lgc (n + m) (xiShift ...) * h y`
  under quotient-zero on `h`;
- exact reason no smaller reading candidate survives:
  quotient-zero only kills `h` on
  `section43PositiveEnergyRegion d (n + m)`,
  so any coefficient-only, fixed-`ε`, or shell-functional descent candidate
  strong enough to matter already requires the same outside-region shell
  control and therefore does not lower the mathematics;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above the future outside-region shell theorem and then above the
  generic quotient-zero actual-shell limit theorem used in `hlimit_os`;
- source citation status rechecked:
  OS II printed page `291`, formula `(5.4)`, still matches only the semigroup
  / analytic-continuation target;
  `mutool draw -F txt` again returned blank page text and no separate paper
  theorem was found for actual-shell outside-region complement-localization;
- production Lean verdict:
  no production Lean edit was made.

Supervision correction (`2026-04-15 18:24 UTC`): one bounded reread of the exact live `hlimit_os` body confirmed that the already-visible three-way shell decomposition still fails first only on the outside-region branch. Between the two candidate theorem shapes, the complement-localization package is closer to the true next mathematics; the shell-functional quotient-descent package remains too optimistic because it would only become true after that same outside-region branch is already solved.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T18:24:00Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact live split reread:
  `hlimit_os` already separates the shell into source support, in-region
  outside-source, and outside-region pieces;
- exact first unresolved reading obligation:
  the outside-region branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`
  for the actual-shell integrand
  `bvt_F OS lgc (n + m) (xiShift ...) * h y`
  under quotient-zero input on `h`;
- exact reading verdict on theorem shape:
  an actual-shell outside-region complement-localization theorem is closer to
  the real next mathematics because it matches the live remaining branch
  exactly;
  a descended-shell-functional statement is not genuinely smaller, because the
  shell functional cannot honestly descend to quotient data until the same
  outside-region contribution has been removed or controlled;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above the first future outside-region shell theorem and then
  above the generic quotient-zero actual-shell limit theorem used in
  `hlimit_os`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`, still matches only the
  semigroup-side target;
  `mutool draw -F txt` again returned blank page text and no separate paper
  theorem was found for the actual-shell outside-region branch;
- production Lean verdict:
  no production Lean edit was made in this pass.

Supervision correction (`2026-04-15 18:08 UTC`): one bounded reread of the exact live theorem body, the three-case decomposition inside `hlimit_os`, the raw-shell CLM definition, and the Section-4.3 quotient lemmas confirmed again that no honest compile-clean theorem sits strictly below the generic quotient-zero actual-shell limit in one pass. The live seam still first fails on the actual-shell outside-region branch.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T18:08:26Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact supplier chain reread:
  `hlimit_os`
  specializes the generic quotient-zero actual-shell limit to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  and that generic limit still feeds through
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact generic quotient-zero contract reread:
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- exact first internal proof obligation reread from the live decomposition:
  control the complement branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`
  for the actual-shell integrand
  `bvt_F OS lgc (n + m) (xiShift ...) * h y`
  under quotient-zero on `h`;
  the in-source and in-region-outside-source cases are already handled by the
  currently landed pointwise comparison / vanishing lemmas;
- exact theorem-shape verdict from reading:
  a shell-functional descent / annihilation package is only honest if it
  directly removes or controls that outside-region contribution;
  this pass again found no paper-backed or already-landed lower theorem of that
  kind, so the package remains too optimistic as the next production statement;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above the future generic quotient-zero actual-shell limit theorem
  and then above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches only the semigroup-side target;
  `mutool draw -F txt` again returned blank page text and `pdftotext` is not
  installed in this harness;
  no separate paper theorem removing the actual-shell complement contribution
  was found;
- production Lean verdict:
  no production Lean edit was made in this pass.

Supervision correction (`2026-04-15 17:57 UTC`): one bounded reread of the exact live theorem body, the raw-shell CLM definition, the dominated-convergence supplier, and the Section-4.3 quotient lemmas confirmed again that no honest compile-clean theorem sits strictly below the generic quotient-zero actual-shell limit in one pass. The live seam still first fails on the actual-shell outside-region branch.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:57:02Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact supplier chain reread:
  `hlimit_os`
  specializes the generic quotient-zero actual-shell limit to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  and that generic limit still feeds through
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact generic quotient-zero contract reread:
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- exact rejected fixed-`ε` candidate reread:
  `∀ ε : ℝ, ∀ hε : 0 < ε, ∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h = 0`;
- why that candidate is not genuinely smaller:
  the live definition of `section43_fixedTimeShellRawCLM` is already the full
  actual-shell integral, so fixed-`ε` descent would already require whole-shell
  quotient descent / annihilation;
- exact first internal proof obligation reread:
  control the complement branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`
  for the actual-shell integrand
  `bvt_F OS lgc (n + m) (xiShift ...) * h y`
  under quotient-zero on `h`;
- exact theorem-shape verdict from reading:
  a shell-functional descent / annihilation package is only honest if it
  directly removes or controls that outside-region contribution;
  this pass again found no paper-backed or already-landed lower theorem of that
  kind, so the package remains too optimistic as the next production statement;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above the future generic quotient-zero actual-shell limit theorem
  and then above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches only the semigroup-side target;
  `mutool draw -F txt` again returned blank page text and `pdftotext` is not
  installed in this harness;
  no separate paper theorem removing the actual-shell complement contribution
  was found;
- production Lean verdict:
  no production Lean edit was made in this pass.

Supervision correction (`2026-04-15 17:52 UTC`): one bounded reread of the exact live theorem body, supplier chain, raw-shell CLM definition, and Section-4.3 quotient lemmas confirmed again that the first honest new lower statement is already the generic quotient-zero actual-shell limit theorem. No compile-clean smaller production theorem is visible in one pass: the fixed-`ε` candidate is not genuinely smaller, and no separate source-backed actual-shell complement-localization theorem was found between it and the `hlimit_os` specialization.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:52:01Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact supplier chain reread:
  `hlimit_os`
  specializes the generic quotient-zero actual-shell limit to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  and that generic limit still feeds through
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact rejected candidate reread:
  `∀ ε : ℝ, ∀ hε : 0 < ε, ∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h = 0`;
- why that candidate is not genuinely smaller:
  the live definition of `section43_fixedTimeShellRawCLM` is already the full
  shell integral, so fixed-`ε` descent would force the same whole-shell kernel
  control still missing at the limit level;
- exact next honest contract reread:
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- exact decision on theorem size:
  this generic quotient-zero actual-shell limit theorem is itself the first
  honest new contract;
  a weaker actual-shell localization theorem would only count if it directly
  controlled the live complement branch, and no such source-backed theorem was
  visible in this pass;
- exact reading blocker:
  quotient-zero kills `h` only on
  `section43PositiveEnergyRegion d (n + m)`,
  but the CLM integrates over every
  `y : NPointDomain d (n + m)`;
  there is still no source-backed theorem controlling the branch
  `y ∉ section43PositiveEnergyRegion d (n + m)` for the actual canonical shell;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above the future generic quotient-zero actual-shell limit theorem
  and then above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches only the semigroup-side target;
  `mutool draw -F txt` again returned blank page text and `pdftotext` is
  unavailable in this harness;
  this pass again found no separate paper theorem removing the actual-shell
  complement contribution;
- production Lean verdict:
  no production Lean edit was made in this pass;
  only notes/audit/chat docs were tightened.

Supervision correction (`2026-04-15 17:41 UTC`): one bounded reread of the exact live theorem body, raw-shell CLM definition, and dominated-convergence supplier chain confirmed again that the direct quotient-zero actual-shell limit theorem remains the first honest lower statement. No compile-clean smaller production theorem is visible in one pass: the natural fixed-`ε` quotient-descent candidate already asks for whole-shell kernel annihilation and still fails first on the complement branch outside `section43PositiveEnergyRegion d (n + m)`.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:41:44Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact supplier chain reread:
  `hlimit_os`
  specializes the generic quotient-zero shell limit to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  and that generic limit still feeds through
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact lower theorem statement confirmed again:
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- exact candidate theorem statement reread:
  `∀ ε : ℝ, ∀ hε : 0 < ε, ∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h = 0`;
- why that candidate is not genuinely smaller:
  the live definition of `section43_fixedTimeShellRawCLM` is already the
  full-shell integral, so fixed-`ε` descent would force the same whole-shell
  kernel control that the quotient-zero limit theorem still lacks;
- exact reading blocker:
  quotient-zero kills `h` only on
  `section43PositiveEnergyRegion d (n + m)`,
  but the CLM integrates over every
  `y : NPointDomain d (n + m)`;
  there is still no source-backed theorem controlling the branch
  `y ∉ section43PositiveEnergyRegion d (n + m)` for the actual canonical shell;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above the future generic quotient-zero shell limit theorem and
  then above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches only the semigroup-side target;
  `pdftotext` is unavailable in this harness, and this pass again found no
  separate paper theorem removing the actual-shell complement contribution;
- exact stale-comment status:
  the current Lean comment points one step too high, but should still be
  updated only after the real lower theorem exists.

Supervision correction (`2026-04-15 17:37 UTC`): one bounded reread of the live theorem body, the dominated-convergence supplier, and the raw-shell CLM definition confirmed again that the direct quotient-zero actual-shell limit theorem remains the first honest lower statement. No compile-clean smaller production theorem is visible in one pass: the natural fixed-`ε` quotient-descent candidate for `section43_fixedTimeShellRawCLM` already asks for whole-shell kernel annihilation and still fails first on the complement branch outside the Section-4.3 positive-energy region.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:37:04Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact supplier chain reread:
  `hlimit_os`
  specializes the generic quotient-zero shell limit to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  and that generic limit still feeds through
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact lower theorem statement confirmed again:
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- exact candidate theorem statement reread:
  `∀ ε : ℝ, ∀ hε : 0 < ε, ∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h = 0`;
- why that candidate is not genuinely smaller:
  the live definition of `section43_fixedTimeShellRawCLM` is already the
  actual full-shell integral, so fixed-`ε` descent would force the same whole-
  shell kernel control that the limit theorem still lacks;
- exact reading blocker:
  quotient-zero kills `h` only on
  `section43PositiveEnergyRegion d (n + m)`,
  but the CLM integrates over every
  `y : NPointDomain d (n + m)`;
  there is still no source-backed theorem controlling the branch
  `y ∉ section43PositiveEnergyRegion d (n + m)` for the actual canonical shell;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above the future generic quotient-zero shell limit theorem and
  then above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches only the semigroup-side target;
  this pass again found no separate paper theorem removing the actual-shell
  complement contribution;
- exact stale-comment status:
  the current Lean comment points one step too high, but should still be
  updated only after the real lower theorem exists.

Supervision correction (`2026-04-15 17:31 UTC`): one bounded reread of the exact live theorem body, the dominated-convergence supplier, and the quotient transport lemmas confirmed again that the direct quotient-zero actual-shell limit theorem remains the first honest lower statement. No compile-clean smaller production theorem is visible in one pass, because the actual canonical-shell complement branch is still the first uncontrolled branch. The current Lean comment is stale, but should only be updated later once a real production theorem exists at that lower surface.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:31:55Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact supplier chain reread:
  `hlimit_os`
  specializes the generic quotient-zero shell limit to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  and that generic limit still feeds through
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact lower theorem statement confirmed again:
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- why it is still first:
  the needed quotient-zero hypothesis for the shell difference is already
  supplied by the current Section-4.3 quotient transport lemmas, so the
  ambient-vs-source shell limit is only a specialization of this generic
  statement;
- exact reading blocker:
  the region branch is already killed by quotient-zero-on-region, but there is
  still no source-backed theorem controlling
  `y ∉ section43PositiveEnergyRegion d (n + m)` on the actual canonical shell;
- exact reading verdict on theorem size:
  no smaller honest compile-clean theorem was visible in one pass beneath that
  quotient-zero shell-limit statement;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  with downstream use inside `hlimit_os` after
  `hshellToSlice`,
  `hsliceTransport`,
  and
  `hweightEqOnSource`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches only the semigroup-side target;
  this pass again found no separate paper theorem removing the actual-shell
  complement contribution;
- exact stale-comment status:
  the current Lean comment points one step too high, but should be updated only
  after the real lower theorem exists.

Supervision correction (`2026-04-15 17:28 UTC`): one bounded reread of the exact live `hlimit_os` body against the current `sorry` comment confirmed again that the direct quotient-zero actual-shell limit theorem remains the first honest lower statement. The current Lean comment below `hlimit_os` is stale because it still points to the ambient-vs-source specialization rather than the generic quotient-zero theorem one step below it.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:28:33Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact supplier theorem body rechecked:
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact lower theorem statement confirmed again:
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- why it is still first:
  the live ambient-vs-source shell limit is exactly that theorem specialized to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  with the needed quotient-zero input already supplied by the current
  Section-4.3 transport and quotient lemmas;
- exact reading blocker:
  the only current route still runs through full-shell dominated convergence,
  and there is still no source-backed theorem controlling the branch
  `y ∉ section43PositiveEnergyRegion d (n + m)` on the actual canonical shell;
- exact reading verdict on theorem size:
  no smaller honest compile-clean theorem was visible in one pass beneath that
  quotient-zero shell-limit statement;
- exact stale-comment correction:
  the live note above the `sorry` still points to the ambient-vs-source shell
  comparison limit, but that statement is already only the quotient-zero
  theorem specialized to the shell difference test;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  with downstream use inside `hlimit_os` after
  `hshellToSlice`,
  `hsliceTransport`,
  and
  `hweightEqOnSource`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches only the semigroup-side target;
  this bounded pass again found no separate paper theorem removing the
  actual-shell complement contribution.

Supervision correction (`2026-04-15 18:02 UTC`): one bounded reread of the exact live `hlimit_os` body corrected the 17:12 package split. The direct quotient-zero actual-shell limit theorem remains the first honest lower statement. The full-shell dominated-convergence input package is only internal proof data for that theorem, not a standalone theorem-sized step below it.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T18:02:00Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact supplier theorem body rechecked:
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact lower theorem statement confirmed again:
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- why it is still first:
  the live ambient-vs-source shell limit is exactly that theorem applied to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  with the needed quotient-zero input already supplied by the current
  Section-4.3 transport and quotient lemmas;
- exact reading blocker:
  the only current route still runs through full-shell dominated convergence,
  and there is still no source-backed theorem controlling the branch
  `y ∉ section43PositiveEnergyRegion d (n + m)` on the actual canonical shell;
- exact correction to the 17:12 package split:
  the `hbound` / `hbound_int` / `hlim` package is not a separate production
  theorem surface;
  it only restates the internal data needed to call the generic supplier, so
  it does not lower the live blocker beyond the outside-region shell-control
  gap;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  with downstream use inside `hlimit_os` after
  `hshellToSlice`,
  `hsliceTransport`,
  and
  `hweightEqOnSource`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches only the semigroup-side target;
  this bounded pass again found no separate paper theorem removing the
  actual-shell complement contribution.

Supervision correction (`2026-04-15 17:12 UTC`): one bounded reread of the exact dominated-convergence hypotheses sharpened the next missing package above the quotient-zero actual-shell limit theorem. The package is the full-shell dominated-convergence data for quotient-zero `h`, and it decomposes one theorem smaller into an already-available region-zero branch plus one genuinely new complement-branch shell-control component.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:12:09Z`):

- exact supplier reread:
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact next package above the quotient-zero shell-limit statement:
  produce global `hbound`, `hbound_int`, and `hlim` for the actual-shell
  integrand under
  `section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0`;
- why it is immediately next:
  that supplier theorem consumes exactly those data, so the quotient-zero shell
  limit cannot be proved on the current route without this package;
- exact decomposition verdict:
  yes, one theorem smaller;
  on
  `section43PositiveEnergyRegion d (n + m)`,
  quotient-zero already forces
  `h = 0`,
  so the region branch is not the new work;
  the genuinely new smaller step is control of the true complement branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- exact source citation / lack:
  OS II printed page `291`, formula `(5.4)`,
  still matches only the semigroup-side target;
  this bounded pass again found no separate paper theorem removing the actual-
  shell complement contribution;
- exact insertion surface and consumer chain:
  `OSToWightmanPositivity.lean`,
  above the future quotient-zero shell-limit theorem;
  complement-branch shell control
  + region-zero consequence
  -> full-shell dominated-convergence package
  -> quotient-zero shell limit
  -> specialization in `hlimit_os`.

Supervision correction (`2026-04-15 17:07 UTC`): one bounded reread of the exact dominated-convergence body and the live actual-shell integrand confirmed that the first honest lower theorem beneath `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime` is still the direct quotient-zero actual-shell limit theorem. The outside-region complement branch does not honestly lower to a separate fixed-`ε` or pointwise theorem in one pass.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:07:07Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact supplier theorem body rechecked:
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact actual-shell integrand rechecked there:
  `fun y : NPointDomain d (n + m) =>
    bvt_F OS lgc (n + m)
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ)) *
      h y`;
- exact lower theorem statement remains:
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- why it is still first:
  the live ambient-vs-source shell limit is exactly that theorem applied to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  and the quotient-zero hypothesis for that input is already supplied by the
  current Section-4.3 transport and quotient-zero lemmas;
- exact reading blocker:
  the only current route still runs through dominated convergence on the full
  shell integrand, but current source only gives equality on
  `section43PositiveEnergyRegion d (n + m)`;
  there is still no source-backed theorem controlling the branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- exact reading verdict on theorem size:
  no smaller honest compile-clean theorem was visible in one pass beneath that
  quotient-zero shell-limit statement;
  the isolated outside-region branch is not yet its own honest theorem surface;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  with downstream use inside `hlimit_os` after
  `hshellToSlice`,
  `hsliceTransport`,
  and
  `hweightEqOnSource`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches the semigroup-side target,
  but this bounded pass again found no separate paper-level elimination of the
  actual-shell complement branch;
  local `mutool draw -F txt` still returned blank page text in this harness;
- production Lean verdict:
  keep production Lean unchanged in this pass;
  tighten only the reading notes.

Supervision correction (`2026-04-15 17:01 UTC`): one bounded reread of the exact live body confirmed that the first honest lower theorem beneath `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime` is still the direct quotient-zero actual-shell limit theorem. No honest compile-clean production step lands there in one pass, because the dominated-convergence route still first fails on the complement branch `y ∉ section43PositiveEnergyRegion d (n + m)`.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:01:42Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact lower theorem statement confirmed from the body:
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- why it is still first:
  the live ambient-vs-source shell limit is exactly that theorem applied to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  and the needed quotient-zero input is already supplied by the current
  Section-4.3 transport and quotient lemmas;
- exact reading blocker:
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence` is still
  the only honest supplier route, and it still lacks shell-side control for
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- exact reading verdict on theorem size:
  no smaller honest compile-clean theorem was visible in one pass beneath that
  quotient-zero shell-limit statement;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  with downstream use inside `hlimit_os` after
  `hshellToSlice`,
  `hsliceTransport`,
  and
  `hweightEqOnSource`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches the semigroup-side target,
  but this bounded pass found no separate paper-level elimination of the
  actual-shell complement branch;
  local `mutool draw -F txt` extraction again returned blank page text in this
  harness;
- production Lean verdict:
  keep production Lean unchanged in this pass;
  tighten only the reading notes.

Supervision correction (`2026-04-15 16:52 UTC`): one bounded reread of the exact live body confirmed that the first honest lower theorem beneath `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime` is still the direct quotient-zero actual-shell limit theorem. No honest compile-clean production step lands there in one pass, because the dominated-convergence route still first fails on the complement branch `y ∉ section43PositiveEnergyRegion d (n + m)`.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T16:52:31Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact lower theorem statement confirmed from the body:
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- why it is still first:
  the live ambient-vs-source shell limit is exactly that theorem applied to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  and the needed quotient-zero input is already supplied by the current
  Section-4.3 transport and quotient lemmas;
- exact reading blocker:
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence` is still
  the only honest supplier route, and it still lacks shell-side control for
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- exact reading verdict on theorem size:
  no smaller honest compile-clean theorem was visible in one pass beneath that
  quotient-zero shell-limit statement;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  with downstream use inside `hlimit_os` after
  `hshellToSlice`,
  `hsliceTransport`,
  and
  `hweightEqOnSource`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches the semigroup-side target,
  but this bounded pass found no separate paper-level elimination of the
  actual-shell complement branch.

Supervision correction (`2026-04-15 16:47 UTC`): one bounded reread of the exact `hlimit_os` body sharpened the lower theorem classification. The first honest lower statement is the direct quotient-zero shell-limit theorem on the actual canonical shell; the ambient-vs-source shell-difference limit is its specialization. That smaller theorem still does not land in one pass, because no current source theorem controls the complement branch `y ∉ section43PositiveEnergyRegion d (n + m)`.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T16:47:00Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact full shell contract rechecked from the body:
  the local missing limit in `hlimit_os` is still
  `ε ↦ ∫ y, bvt_F ... (xiShift ... (t : ℂ)) *
    (((φ.conjTensorProduct ψ) - (f.conjTensorProduct g)) y)`
  tending to `0` as `ε → 0+`;
- sharpened lower theorem statement:
  the first honest lower theorem is the quotient-zero shell-limit theorem
  `∀ h : SchwartzNPoint d (n + m),
      section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
      Filter.Tendsto
        (fun ε : ℝ =>
          if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;
- why it is first:
  the live shell-difference limit is exactly that theorem applied to
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  whose quotient-zero hypothesis is already source-backed by the existing
  Section-4.3 transport and quotient-zero lemmas;
- exact reading blocker:
  the complement branch
  `y ∉ section43PositiveEnergyRegion d (n + m)` is still uncontrolled on the
  actual shell, so the dominated-convergence supplier cannot yet be fed honest
  `hbound` and `hlim` data;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  immediately above
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  with downstream use in `hlimit_os`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches the semigroup-side target,
  but this bounded reread found no separate paper-level elimination of the
  actual-shell complement branch;
- production Lean verdict:
  keep production Lean unchanged in this pass;
  tighten only the reading notes.

Supervision correction (`2026-04-15 17:45 UTC`): one bounded reread of the exact `hlimit_os` body confirmed that this pass should again stay docs-only. The route still lowers to the full ambient-vs-source shell limit inside `hlimit_os`, but not to a separate compile-clean theorem for the isolated outside-region branch.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:45:00Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact lower statement rechecked from the body:
  the first honest theorem below it is still the shell-difference limit
  `ε ↦ ∫ y, bvt_F ... (xiShift ... (t : ℂ)) *
    (((φ.conjTensorProduct ψ) - (f.conjTensorProduct g)) y)`
  tending to `0` as `ε → 0+`;
- exact branch statement rechecked:
  the first uncontrolled branch is still
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- exact reading verdict on theorem size:
  no smaller honest compile-clean theorem was visible in one pass beneath that limit statement,
  because the outside-region branch still lacks its own annihilation/control theorem on the ambient shell;
- why this branch is first:
  on-source and positive-energy-outside-source cases are already grounded by the live local theorems in the body of `hlimit_os`;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  in `hlimit_os`,
  after
  `hshellToSlice`,
  `hsliceTransport`,
  and
  `hweightEqOnSource`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches the semigroup-side target,
  but this bounded reread found no separate paper-level elimination of the ambient-shell outside-region contribution;
- production Lean verdict:
  keep production Lean unchanged in this pass;
  tighten only the reading notes.

Supervision correction (`2026-04-15 16:32 UTC`): one more bounded reread of the live theorem body confirmed that this pass should stay docs-only. The route still lowers to the full ambient-vs-source shell limit inside `hlimit_os`, but not to a separate compile-clean theorem for the isolated outside-region branch.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T16:32:08Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact lower statement rechecked from the body:
  the first honest theorem below it is still the shell-difference limit
  `ε ↦ ∫ y, bvt_F ... (xiShift ... (t : ℂ)) *
    (((φ.conjTensorProduct ψ) - (f.conjTensorProduct g)) y)`
  tending to `0` as `ε → 0+`;
- exact branch statement rechecked:
  the first uncontrolled branch is
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- exact reading verdict on theorem size:
  no smaller honest compile-clean theorem was visible in one pass beneath that limit statement,
  because the outside-region branch still lacks its own annihilation/control theorem on the ambient shell;
- why this branch is first:
  on-source and positive-energy-outside-source cases are already grounded by the live local theorems in the body of `hlimit_os`;
- exact insertion surface:
  `OSToWightmanPositivity.lean`,
  in `hlimit_os`,
  after
  `hshellToSlice`,
  `hsliceTransport`,
  and
  `hweightEqOnSource`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches the semigroup-side target,
  but this bounded reread found no separate paper-level elimination of the ambient-shell outside-region contribution;
- production Lean verdict:
  keep production Lean unchanged in this pass;
  tighten only the reading notes.

Supervision correction (`2026-04-15 16:27 UTC`): one more bounded reread of the live theorem body confirmed that the route still stops first at the outside-`section43PositiveEnergyRegion` branch of the ambient shell comparison inside `hlimit_os`. No smaller source-backed compile-clean theorem sits below that comparison seam in one pass.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T16:27:00Z`):

- direct reading consequence:
  the next live theorem remains
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact first unread/ungrounded branch:
  `y ∉ section43PositiveEnergyRegion d (n + m)` for the canonical-shell integrand
  multiplying
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g)) y`;
- exact smaller theorem statement if lowered one step:
  the honest lower target is the limit theorem asserting the above shell difference integral tends to `0` as `ε → 0+`;
- why it is first:
  on-source and positive-energy-outside-source branches are already grounded by existing theorems,
  so the route cannot honestly move to a direct `psiZ` scalar comparison before the outside-region ambient contribution is controlled;
- exact insertion surface:
  in `OSToWightmanPositivity.lean`,
  inside `hlimit_os`,
  after
  `hshellToSlice`,
  `hsliceTransport`,
  and
  `hweightEqOnSource`;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`,
  still matches the semigroup-side analytic continuation target,
  but not the missing outside-region shell elimination;
- production Lean verdict:
  keep production Lean unchanged in this pass;
  tighten only reading notes.

Supervision correction (`2026-04-15 17:25 UTC`): direct rereading now places the live frontier at `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`. The previous shell-CLM limit theorem above it is already complete in source; the next open work is the internal `hlimit_os` comparison seam, and this bounded pass did not find a smaller honest compile-clean cut beneath it.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:25:00Z`):

- direct reading consequence:
  the next live theorem is the fixed-time value equality
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact local source shape:
  the proof already contains the canonical-shell realization on
  `section43PositiveEnergyRegion`,
  the region-level fixed-time transport to the mixed-order source slice,
  and the source-support weight equality;
- exact first unread/ungrounded branch:
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- exact reading verdict on theorem size:
  the route does lower one theorem-sized step smaller than the current theorem statement,
  namely to the limit-level ambient-vs-source shell comparison inside `hlimit_os`,
  but it does not lower smaller than that in an honest one-pass way;
- source citation rechecked:
  OS II printed page `291`, formula `(5.4)`, still matches the semigroup-side analytic continuation target, but the bounded reread found no separate paper-level identity that directly kills the outside-positive-energy branch of the actual ambient shell integral;
- production Lean verdict:
  keep production Lean unchanged;
  tighten only the reading notes.

Supervision correction (`2026-04-15 17:10 UTC`): a direct reread of the live theorem body shows that the source frontier has already moved past the last basis-conversion seam. `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` now contains the explicit `ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff` argument and the final add-back of `T0R`; the old note that still left a theorem-local `sorry` there is stale. In this bounded pass, the only unresolved item was time-bounded verification of the whole file compile.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T17:10:00Z`):

- direct reading consequence:
  the theorem-local strong-topology conversion is already written in source;
- exact verified source point:
  the live tail reads
  `rw [ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff]`,
  `intro SV hSV`,
  `rcases hSV with ⟨hB, hU⟩`,
  `simpa [Set.MapsTo] using (hMapsTo (hB.extend_scalars ℂ) hU)`,
  then
  `have hadd := hzero.const_add T0R`;
- exact correction to the old reading:
  the active theorem-sized seam is no longer an internal `hMapsTo -> Tendsto` design problem on paper;
  the remaining bounded issue in this pass was only full-file acceptance confirmation;
- bounded verification result:
  the whole-file check under
  `timeout 120s lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
  timed out with exit `124`;
- reading verdict:
  keep production Lean unchanged;
  update the route notes to reflect that the theorem body itself is already source-complete, while bounded compile re-certification was not obtained in this pass.

Supervision correction (`2026-04-15 16:35 UTC`): source-first re-reading now places the frontier exactly at the last strong-topology conversion inside `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`. The existing body is already compile-clean through `hMapsTo`; the remaining issue is Lean’s basis/elimination step for the complex-linear strong topology.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T16:35:00Z`):

- direct reading consequence:
  the finite-net producer and direct shell consumer are no longer the active seam in this theorem body;
- exact verified source point:
  the current insertion reaches the statement
  `hMapsTo :
    ∀ {B} {U}, Bornology.IsVonNBounded ℂ B → U ∈ nhds (0 : ℂ) →
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), Set.MapsTo ... B U`
  with no earlier compile failure;
- exact first unresolved local move after that:
  convert `hMapsTo` into the final
  `Filter.Tendsto ... (nhds T_t)`
  via the strong-topology neighbourhood description on
  `SchwartzNPoint d (n + m) →L[ℂ] ℂ`;
- exact local blocker recorded by the bounded attempt:
  `ContinuousLinearMap.nhds_zero_eq` followed by `le_iInf` leaves Lean with
  `CompleteLattice ?m`,
  so the remaining issue is theorem-application/basis elimination rather than new mathematics;
- reading verdict:
  keep the frontier at the final strong-topology conversion immediately above the live `sorry`.

Supervision correction (`2026-04-15 16:05 UTC`): the shell-domain nuclearity candidate is now source-backed and import-surface-verified. The missing piece was not a new transport theorem but an actual rebuild of the module exporting the new instance.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T16:05:00Z`):

- direct reading consequence:
  `OSToWightmanPositivity.lean` already imported
  `OSReconstruction.SCV.PartialFourierSpatial`,
  so the old downstream failure was not caused by a missing import line at the theorem surface;
- exact seam correction:
  before rebuilding,
  the imported environment still did not expose
  `OSReconstruction.instNuclearSpaceComplexNPointDomain`;
  after
  `lake build OSReconstruction.SCV.PartialFourierSpatial`,
  the same downstream import does expose it and synthesizes both shell-domain `NuclearSpace` goals;
- exact route consequence:
  the call
  `NuclearSpace.finite_net_of_complex_schwartz_seminorm_of_isVonNBounded
    (E := NPointDomain d (n + m)) ...`
  is now genuinely available from the theorem-3 import surface;
- reading verdict:
  the first remaining blocker is no longer the shell-domain nuclearity / finite-net transport seam;
  the frontier returns to the actual bounded-set / strong-topology assembly inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- production Lean verdict:
  no further Lean edit was made in this bounded pass.

Supervision correction (`2026-04-15 15:05 UTC`): the candidate `instNuclearSpaceComplexNPointDomain` has been source-checked and does not yet clear the theorem-3 shell obstruction. The transport proof compiles in its own file, but downstream typeclass synthesis still cannot see `NuclearSpace (SchwartzMap (NPointDomain d (n + m)) ℂ)`.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T15:05:00Z`):

- direct reading consequence:
  the first honest next step above the candidate is still not inside the body of
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- exact reason:
  the candidate currently certifies only that a transport proof was written compile-clean in
  `PartialFourierSpatial.lean`,
  not that the resulting nuclearity instance is available to downstream instance search on the raw shell test-space type;
- direct probe consequence:
  even after rebuilding the source file, a scratch check still fails on
  `infer_instance : NuclearSpace (SchwartzMap (NPointDomain d (n + m)) ℂ)`,
  so the finite-net call still cannot be written honestly at the theorem-3 insertion surface;
- reading verdict:
  no theorem-3 proof fragment should be landed before the export / instance-search seam is resolved.

Supervision correction (`2026-04-15 14:05 UTC`): the first honest obstruction inside the current theorem-3 shell limit theorem is now sharper. The route still sits at `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, but the first failing local step is not the final strong-topology basis call.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T14:05:00Z`):

- direct reading consequence:
  the next theorem is still
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- exact internal decomposition now source-tested:
  boundary-value pointwise limit data,
  common finite seminorm control,
  complex bounded-set finite nets,
  finite-net-to-`MapsTo`,
  strong-topology neighborhood basis;
- exact first obstruction found by the live insertion attempt:
  the complex bounded-set finite-net step is not yet callable on
  `SchwartzMap (NPointDomain d (n + m)) ℂ`
  because Lean does not have
  `NuclearSpace (SchwartzMap (NPointDomain d (n + m)) ℂ)` in scope there;
- reading verdict:
  blocker classification is `(d)` another exact source-backed sub-obligation,
  namely a local nuclearity / finite-net transport to the actual shell test-space domain;
- route consequence:
  the old coarse label `(a) bounded-set finite-net to eventual-MapsTo assembly`
  is too imprecise now;
  the first missing bridge is before `MapsTo`, at the finite-net theorem application itself.

Supervision correction (`2026-04-15 14:08 UTC`): source-first reading plus a direct `lake env lean` check corrected the live shell status again. The common finite-seminorm theorem is already written in source, but it is not compile-clean because the shell CLM family still does not pass through `.restrictScalars ℝ`.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T14:08:00Z`):

- direct reading correction:
  `section43_fixedTimeShellRawCLM_uniformSeminormBound_fixedTime`
  is already present in the live file immediately above
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- exact live obstruction from the compile check:
  line `4247` still fails on
  `.restrictScalars ℝ`
  with missing
  `LinearMap.CompatibleSMul (SchwartzNPoint d (n + m)) ℂ ℝ ℂ`;
- reading verdict:
  the remaining blocker at this theorem surface is only real/complex scalar packaging for the shell family,
  not a fresh theorem between the pointwise-bounded theorem and the common finite-seminorm theorem,
  and not a missing shell-side inequality;
- exact already-available inputs remain:
  `section43_fixedTimeShellRaw_uniformPolyGrowth_fixedTime`,
  `section43_fixedTimeShellRawCLM_pointwiseBounded_fixedTime`,
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`,
  `finite_net_of_complex_schwartz_seminorm_of_isVonNBounded`,
  and
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`;
- route status after that correction:
  once the scalar seam is resolved,
  the next honest theorem remains
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`.

Supervision correction (`2026-04-15 13:50 UTC`): source-first reading of the live shell file, the finite-net consumer, the strong-topology basis, and OS II Section V leaves the route unchanged. There is still no smaller theorem above `section43_fixedTimeShellRawCLM_pointwiseBounded_fixedTime`; the next honest theorem is still the common finite-seminorm bound.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T13:50:00Z`):

- direct reading consequence:
  the next honest mathematical theorem is still the shell-local common finite-seminorm bound;
- exact source-backed reason:
  formula `(5.4)` in `reconstruction theorem II.pdf` matches the already-live shell family / fixed-test-function route and does not expose a smaller theorem between fixed-test-function boundedness and one common seminorm;
- consumer-side reading consequence:
  the first bounded-set shell consumer remains
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`,
  so the route still needs:
  one common finite seminorm,
  then finite nets,
  then strong-topology `MapsTo`;
- reading verdict:
  any candidate below the common-seminorm theorem is either wrapper drift around the same Banach-Steinhaus upgrade or generic scalar-restriction packaging, not a new theorem-3 bridge;
- insertion surface, minimal hypotheses, and downstream chain remain unchanged.

Supervision correction (`2026-04-15 13:40 UTC`): the live route was re-read again at the insertion surface and then tested by a direct Lean scalar-probe. The result is unchanged mathematically: there is still no smaller theorem above `section43_fixedTimeShellRawCLM_pointwiseBounded_fixedTime`; the next honest theorem is still the common finite-seminorm bound.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T13:40:00Z`):

- direct reading consequence:
  the next honest mathematical theorem is still the shell-local common finite-seminorm bound;
- exact live obstruction now verified by probe rather than only by insertion failure:
  Lean does not synthesize
  `IsScalarTower ℝ ℂ (SchwartzMap (NPointDomain d (n + m)) ℂ)`,
  and therefore cannot synthesize
  `LinearMap.CompatibleSMul (SchwartzMap (NPointDomain d (n + m)) ℂ) ℂ ℝ ℂ`
  needed by `ContinuousLinearMap.restrictScalars`;
- reading verdict:
  this remains generic scalar packaging,
  not a smaller theorem between the landed pointwise-bounded theorem and the missing common finite-seminorm theorem;
- insertion surface, minimal hypotheses, and downstream chain remain unchanged.

Supervision correction (`2026-04-15 13:30 UTC`): source-first reading plus live type probes confirm that the route still does not drop to a smaller theorem above `section43_fixedTimeShellRawCLM_pointwiseBounded_fixedTime`. The newly pinned blocker is purely the generic real/complex scalar-restriction seam for `SchwartzMap`, not a new theorem-3 bridge.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T13:30:00Z`):

- direct reading consequence:
  the next honest mathematical theorem is still the shell-local common finite-seminorm bound;
- exact live obstruction:
  even after unfolding
  `SchwartzNPoint d (n + m) = SchwartzMap (NPointDomain d (n + m)) ℂ`,
  Lean still cannot synthesize
  `LinearMap.CompatibleSMul (SchwartzMap (NPointDomain d (n + m)) ℂ) ℂ ℝ ℂ`,
  so the family cannot yet be fed directly into
  `ContinuousLinearMap.restrictScalars ℝ`;
- reading verdict:
  this obstruction is generic packaging, not a smaller theorem between the landed pointwise-bounded theorem and the missing common finite-seminorm theorem;
- insertion surface, minimal hypotheses, and downstream chain remain unchanged.

Supervision correction (`2026-04-15 12:45 UTC`): the next shell theorem has now been tested directly rather than only inferred from route structure. The result is still docs-only: the common finite-seminorm bound is mathematically still the right next theorem, but the first local attempt to derive it from `tempered_uniform_schwartz_bound` runs into a live scalar-packaging seam on `SchwartzNPoint`.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T12:45:00Z`):

- direct route test:
  the file already has the needed pointwise boundedness theorem,
  so the natural next move is to package the family
  `ε ↦ section43_fixedTimeShellRawCLM ... ε`
  as a real-linear family and apply Banach-Steinhaus;
- exact live obstruction:
  at this insertion surface the alias
  `SchwartzNPoint d (n + m)`
  does not currently expose the `IsScalarTower ℝ ℂ ...` / `CompatibleSMul` path needed for a clean `.restrictScalars ℝ` call on the shell CLMs;
- reading consequence:
  the route does **not** drop to a smaller new theorem;
  it stays at the common finite-seminorm theorem,
  now with one explicit local packaging prerequisite recorded;
- insertion surface and minimal hypotheses remain unchanged.

Supervision correction (`2026-04-15 12:25 UTC`): the shell-side producer stack has advanced by one honest bounded Lean step. The new private theorem `section43_fixedTimeShellRaw_uniformPolyGrowth_fixedTime` now supplies the raw-shell uniform polynomial-growth bridge, so the next open shell seam is the finite-seminorm upgrade above that theorem: either one genuinely smaller immediately consumable theorem between raw polynomial growth and the full CLM seminorm bound, or else the fixed-time uniform finite-seminorm bound for `section43_fixedTimeShellRawCLM` on `0 < ε < 1` itself.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:59:59Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- shell-frontier correction:
  the next honest theorem is not yet the direct eventual-`MapsTo` application;
  the lower missing theorem is the shell-family common seminorm bound;
- exact next shell-side theorem now required:
  `section43_fixedTimeShellRawCLM_uniformSeminormBound_fixedTime`
  with hypotheses
  `OS`, `lgc`, `hm`, `t`
  and conclusion
  `∃ s C_sem, 0 ≤ C_sem ∧
    ∀ ε, 0 < ε → ε < 1 → ∀ φ,
      ‖section43_fixedTimeShellRawCLM ... ε ... φ‖ ≤
        C_sem * (s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)) φ`;
- exact insertion surface:
  immediately below
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`
  and immediately above
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- why this is smaller than the eventual `MapsTo` theorem:
  it supplies one missing consumer hypothesis only;
  it does not yet combine bounded sets, finite nets, pointwise convergence, or strong-topology neighbourhoods;
- why there is no smaller honest bridge under it:
  finite nets and pointwise convergence are already landed on this route;
  the remaining missing datum is exactly the common seminorm control for the shell family;
- bounded-pass Lean verdict:
  no production Lean edit occurred;
- reason:
  the reusable SCV uniform-bound proof currently lives as private tube-slice infrastructure, so there was no short honest local specialization available in this bounded pass without broadening the work.

Supervision correction (`2026-04-15 23:59 UTC`): the source-first reading frontier is now above the Schwartz specialization. Live `NuclearSpace.lean` already contains the compile-clean theorem `finite_net_of_schwartz_seminorm_of_isVonNBounded`, so the next honest theorem surface on the theorem-3 route is `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, not a smaller or fuller Schwartz finite-net bridge.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:59:59Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean route correction:
  both the generic producer theorem
  `finite_net_of_nuclear_seminorm_of_q_bounded`
  and the shell-facing Schwartz specialization
  `finite_net_of_schwartz_seminorm_of_isVonNBounded`
  are already landed live;
- unsupported residue:
  yes;
  the old reading that still placed the frontier at the Schwartz specialization was unsupported by the live file and is corrected here;
- bounded-pass Lean verdict:
  no production Lean edit occurred;
- theorem-sized decision:
  there is no genuinely smaller bridge left beneath the specialization;
  the next honest missing surface is already the fixed-time shell limit theorem itself;
- exact first internal obligation beneath that next theorem:
  produce strong-dual convergence of
  `ε ↦ section43_fixedTimeShellRawCLM ... ε`
  along `nhdsWithin 0 (Set.Ioi 0)` using the now-live finite-net theorem on bounded Schwartz sets, the shell finite-net consumer in `SchwartzComplete.lean`, strong-topology `MapsTo` neighbourhood control, and pointwise shell convergence/Cauchy on each test function;
- downstream chain now:
  `finite_net_of_schwartz_seminorm_of_isVonNBounded`
  ->
  `tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  ->
  strong-topology basis inside the proof of
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only;

Supervision correction (`2026-04-15 23:59 UTC`): the live producer route is one theorem surface further along than the stale frontier supplied to this pass. `NuclearSpace.lean` already contains the full compile-clean generic producer theorem `finite_net_of_nuclear_seminorm_of_q_bounded`. The next honest theorem surface is therefore not another producer lemma below it, but the Schwartz shell-facing specialization that converts `Bornology.IsVonNBounded ℂ B` into finite nets for a fixed finite supremum Schwartz seminorm.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T23:59:59Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean consumer status:
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  remains present compile-clean in `SchwartzComplete.lean`;
- live-reading correction:
  the full generic nuclear-seminorm finite-net theorem is already present compile-clean as
  `finite_net_of_nuclear_seminorm_of_q_bounded`;
- unsupported residue:
  yes;
  the old reading that still placed the frontier at the generic theorem itself was unsupported by the live file and is corrected here;
- bounded-pass Lean verdict:
  no production Lean edit occurred;
  no new below-generic theorem could honestly land because the targeted theorem is already live;
- exact first internal proof obligation still beneath the full generic theorem:
  none;
  that proof has already been discharged in live Lean;
- exact best Lean-ready theorem now required:

  `Bornology.IsVonNBounded ℂ B ->
    ∀ ε > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
      ∀ h ∈ B, ∃ g ∈ t,
        (s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ))
          (h - g) < ε`;
- minimal hypotheses:
  fixed `d n m`,
  finite `s : Finset (ℕ × ℕ)`,
  bounded `B : Set (SchwartzNPoint d (n + m))`,
  and `Bornology.IsVonNBounded ℂ B`;
- why this is the first honest missing surface:
  everything below it is now already present:
  pairwise-difference tail control,
  finite weighted head nets with centres in `B`,
  the head-plus-tail assembly lemma,
  and the generic nuclear-seminorm finite-net theorem;
  what remains is only the specialization from bounded Schwartz sets to those generic hypotheses;
- exact first internal obligation beneath that next theorem:
  obtain a bound for the nuclear-dominating seminorm `q` on `B` from Schwartz boundedness, then call the already-landed generic theorem for
  `p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`;
- downstream chain now:
  Schwartz finite-net theorem
  ->
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  ->
  strong-topology basis inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only.

Supervision correction (`2026-04-15 11:08 UTC`): live source now shows that the generic nuclear precompactness surface really did shrink one theorem-sized step further in Lean. `NuclearSpace.lean` contains the compile-clean local theorem `finite_net_of_nuclear_head_tail`, which is exactly the direct head-plus-tail assembly theorem beneath the full generic nuclear-seminorm finite-net theorem. Fresh supervision re-checks confirmed the unchanged raw-shell insertion surface and `sorry` pair in `OSToWightmanPositivity.lean`, and `lake env lean OSReconstruction/Wightman/NuclearSpaces/NuclearSpace.lean` exits `0` with only the two pre-existing unrelated theorem-level `sorry` warnings. The live next step is therefore the full generic nuclear-seminorm finite-net / precompactness theorem above this new assembly lemma and below the Schwartz specialization.

Bounded theorem-3 reading note on the same live actual-shell route, after
testing the generic nuclear-seminorm finite-net theorem itself for one more
honest theorem-sized decomposition (`2026-04-15`, current bounded pass,
`2026-04-15T23:59:59Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean consumer status:
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  remains present compile-clean in `SchwartzComplete.lean`;
- live-reading conclusion:
  the active generic nuclear-seminorm precompactness theorem does not lower to
  a distinct new theorem surface below itself;
- exact first internal obligation beneath it:
  choose a truncation index `N`,
  net the truncated weighted seminorm,
  and then control the tail on differences `x - y` by combining
  `q (x - y) ≤ q x + q y`
  with a finite `q`-bound on the chosen net centers;
- why this is not a genuinely smaller theorem:
  every candidate smaller statement inspected in this pass either just
  repackages that same truncation-plus-net assembly,
  or depends on strengthened output data from the already-landed finite-family
  theorem rather than isolating a new mathematical blocker;
- exact best Lean-ready theorem now required:
  the full generic nuclear-seminorm finite-net theorem on `q`-bounded sets from
  the nuclear-dominance inequality for `p`;
- minimal hypotheses:
  fixed seminorms `p q`,
  scalar-valued `f`,
  nonnegative summable `c`,
  `‖f n x‖ ≤ q x`,
  `p x ≤ ∑' n, ‖f n x‖ * c n`,
  and `q`-boundedness of `B`;
- what remains immediately after that:
  the Schwartz specialization, then
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`,
  then the strong-topology basis inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- why no compile-clean Lean landing occurred:
  no theorem-sized statement strictly below the generic theorem stayed honest
  after checking the live hypotheses actually exposed by the landed inputs;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  the unsupported residue removed in this pass is the claim that the generic
  theorem itself still decomposes one theorem-sized step smaller.

Bounded theorem-3 reading note on the same live actual-shell route, after
re-checking directly in live Lean whether
`finite_weighted_coordinate_net_of_q_bounded`
is still unfinished (`2026-04-15`, current bounded pass,
`2026-04-15T23:59:59Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean consumer status:
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  remains present compile-clean in `SchwartzComplete.lean`;
- live-reading correction:
  `finite_weighted_coordinate_net_of_q_bounded`
  is already proved compile-clean in `NuclearSpace.lean`;
- unsupported residue:
  the prior frontier claim treating that theorem as still unfinished was not
  supported by the live source and is removed here;
- decomposition result:
  that theorem still splits one honest step smaller to:
  finite-coordinate-image total boundedness
  +
  representative selection / pullback from the coordinate net
  +
  coordinatewise `δ`-control implying small weighted `ℓ¹` sum;
- exact first internal obligation beneath it:
  the pullback/conversion step described above;
- why this is not the active blocker anymore:
  the live proof already contains that step, so promoting it now would only
  repackage solved mathematics;
- exact best Lean-ready theorem now required above it:
  the generic nuclear-seminorm finite-net theorem on `q`-bounded sets from the
  nuclear-dominance inequality for `p`;
- minimal hypotheses:
  fixed seminorms `p q`,
  scalar-valued `f`,
  nonnegative summable `c`,
  `‖f n x‖ ≤ q x`,
  `p x ≤ ∑' n, ‖f n x‖ * c n`,
  and `q`-boundedness of `B`;
- what remains immediately after that:
  the Schwartz specialization, then
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`,
  then the strong-topology basis inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- why no compile-clean Lean landing occurred:
  the finite-family theorem under inspection is already landed, and no new
  smaller theorem below it remained honestly available without wrapper drift;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported code residue was found or removed beyond the corrected route
  description.

Bounded theorem-3 reading note on the same live actual-shell route, after
re-checking the finite-family scalar-coordinate net theorem directly in live
Lean (`2026-04-15`, current bounded pass, `2026-04-15T23:59:59Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean consumer status:
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  remains present compile-clean in `SchwartzComplete.lean`;
- live-reading correction:
  the finite-family weighted-coordinate theorem is already present compile-clean
  in `NuclearSpace.lean` as
  `finite_weighted_coordinate_net_of_q_bounded`;
- decomposition result:
  that theorem does split one honest step smaller to:
  finite-coordinate-image total boundedness
  +
  the pullback/conversion from coordinatewise `δ`-closeness to small weighted
  `ℓ¹`-seminorm;
- exact first internal obligation beneath it:
  the pullback/conversion step described above;
- why this is not the active blocker anymore:
  the live proof already contains that step, so promoting it to a separate
  theorem now would only repackage solved mathematics;
- exact best Lean-ready theorem now required above it:
  the generic nuclear-seminorm finite-net theorem on `q`-bounded sets from the
  nuclear-dominance inequality for `p`;
- minimal hypotheses:
  fixed seminorms `p q`,
  scalar-valued `f`,
  nonnegative summable `c`,
  `‖f n x‖ ≤ q x`,
  `p x ≤ ∑' n, ‖f n x‖ * c n`,
  and `q`-boundedness of `B`;
- what remains immediately after that:
  the Schwartz specialization, then
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`,
  then the strong-topology basis inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- why no compile-clean Lean landing occurred:
  the finite-family theorem under inspection is already landed, and no new
  smaller theorem below it remained honestly available without wrapper drift;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after
checking whether the uniform nuclear-tail truncation lemma itself lowers
further (`2026-04-15`, current bounded pass, `2026-04-15T23:59:00Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean consumer status:
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  remains present compile-clean in `SchwartzComplete.lean`;
- reading conclusion:
  the tail lemma does lower one step smaller in principle, but those smaller
  scalar ingredients are already present compile-clean in `NuclearSpace.lean` as
  `nuclear_tail_le_of_q_bounded`
  and
  `mul_tsum_nat_add_lt_of_summable_nonneg`;
- exact first genuinely new internal proof obligation:
  the assembled uniform tail truncation theorem on a `q`-bounded set;
- why this is now the honest minimal new surface:
  once the pointwise tail domination and scalar summable-tail estimates are
  already landed, the remaining work is exactly to combine them into the
  uniform-in-`x` tail bound;
  that assembly is not a smaller distinct blocker;
- exact best Lean-ready statement now required:
  the `q`-bounded uniform tail lemma recorded in
  `docs/theorem3_os_route_blueprint.md`;
- what remains immediately after that:
  a finite-family scalar-coordinate finite-net theorem, then the full generic
  nuclear-seminorm precompactness theorem;
- why no compile-clean Lean landing occurred:
  the only smaller honest pieces were already in production, so there was no
  new theorem-sized landing below the uniform tail lemma itself;
- immediate downstream use once both internal pieces exist:
  uniform tail truncation
  + finite-family coordinate nets
  give generic nuclear-seminorm precompactness,
  then the Schwartz finite-net theorem,
  then
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`,
  then the strong-topology basis inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after
testing whether the generic nuclear-space precompactness theorem lowers one
step further (`2026-04-15`, current bounded pass, `2026-04-15T23:30:00Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean consumer status:
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  remains present compile-clean in `SchwartzComplete.lean`;
- reading conclusion:
  the generic nuclear-seminorm precompactness theorem does split once more;
- exact first internal proof obligation:
  uniform tail truncation of the nuclear series on `q`-bounded sets;
- why this is a real lowering:
  it isolates only the summable-tail argument and does not yet solve the
  finite-dimensional coordinate-cover part;
- exact best Lean-ready statement now required:
  the `q`-bounded uniform tail lemma recorded in
  `docs/theorem3_os_route_blueprint.md`;
- what remains immediately after that:
  a finite-family scalar-coordinate finite-net theorem, then the full generic
  precompactness theorem;
- why no compile-clean Lean landing occurred:
  the tail lemma looks honest, but this bounded pass did not finish the
  `NNReal`/`tsum` coercion plumbing cleanly enough for production;
- immediate downstream use once both internal pieces exist:
  tail truncation
  + finite-family coordinate nets
  give generic nuclear-seminorm precompactness,
  then the Schwartz finite-net theorem,
  then
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`,
  then the strong-topology basis inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  OS II witness existence, pointwise convergence, shell growth control, and
  existing nuclear-dominance packaging;
  genuinely new:
  uniform nuclear-tail truncation,
  finite-family coordinate nets,
  and the full generic nuclear-seminorm precompactness theorem;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after
isolating the first honest generic theorem beneath the shell producer statement
(`2026-04-15`, current bounded pass, `2026-04-15T20:30:00Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean consumer status:
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  remains present compile-clean in `SchwartzComplete.lean`;
- reading conclusion:
  the first honest internal obligation below the shell producer theorem is now
  visible as a generic nuclear-space statement:
  boundedness in a dominating seminorm `q` plus nuclear decomposition of a
  fixed seminorm `p` should imply finite `p`-nets;
- why this is a real lowering:
  mathlib already gives
  `WithSeminorms.isVonNBounded_iff_seminorm_bounded`,
  so the Schwartz-specific step
  `Bornology.IsVonNBounded ℂ B -> ∃ M, ∀ x ∈ B, q x < M`
  is not the blocker;
- exact best Lean-ready statement now required below the shell theorem:
  a generic theorem in `NuclearSpace.lean` proving finite `p`-nets on
  `q`-bounded sets from nuclear decomposition data for `p`;
- whether anything smaller reusable exists below that:
  no immediately shell-consumable theorem smaller than this surfaced;
  the remaining proof is exactly the tail truncation
  + finitely many coordinate functionals
  + finite-dimensional covering argument;
- why the Montel route is still not the right next target:
  compact closure remains stronger than required and no longer sits closest to
  the route once fixed-seminorm boundedness is already available;
- immediate downstream use once the generic theorem exists:
  specialize to
  `E := SchwartzNPoint d (n + m)` and
  `p := s.sup (schwartzSeminormFamily ...)`,
  obtain the `q`-bounded hypothesis from
  `WithSeminorms.isVonNBounded_iff_seminorm_bounded`,
  feed the resulting Schwartz finite-net theorem into
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`,
  then into the strong-topology basis inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  OS II witness existence, pointwise convergence, and shell growth control;
  genuinely new:
  the generic nuclear-seminorm precompactness theorem and its Schwartz
  specialization;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after
checking the exact shell-facing producer statement shape (`2026-04-15`, current
bounded pass, `2026-04-15T16:00:00Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean consumer status:
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  remains present compile-clean in `SchwartzComplete.lean`;
- exact best Lean-ready producer theorem is the finite-net form, not the
  quotient form:

  `Bornology.IsVonNBounded ℂ B ->
    ∀ ε > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
      ∀ h ∈ B, ∃ g ∈ t, p (h - g) < ε`,

  with
  `p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`;
- why this is the best immediate shell statement:
  the shell consumer already takes exactly `hnet`;
  the equivalent quotient-language statement
  `TotallyBounded ((q_p) '' B)` is not a cleaner first formal surface because
  no local quotient API is already sitting at the consumer seam;
- exact minimal hypotheses and codomain objects:
  only fixed `d n m`, fixed finite `s`, bounded `B`, and no codomain object in
  the immediate theorem;
  `q_p` only appears in the equivalent reformulation;
- exact first internal proof obligation beneath that theorem:
  no smaller immediate theorem-sized landing was found;
  every honest reformulation is still fixed-seminorm precompactness of bounded
  Schwartz sets;
- whether anything smaller reusable exists:
  no;
  weaker boundedness facts do not reach finite `p`-nets;
- why the Montel route is stronger:
  it asks first for compactness of `closure B`, which is a full Schwartz-space
  Heine-Borel theorem and therefore stronger than the shell need;
- immediate downstream use once available:
  feed the producer theorem into
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`,
  then into the strong-topology basis inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  OS II witness existence, pointwise convergence, and shell growth control;
  genuinely new:
  the fixed-seminorm finite-net / precompactness theorem;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of the producer seam beneath the now-landed shell
consumer (`2026-04-15`, current bounded pass, `2026-04-15T00:00:00Z`):

Bounded theorem-3 reading note on the same live actual-shell route, after
testing the Montel/closure/compact-image route directly
(`2026-04-15`, current bounded pass, `2026-04-15T12:00:00Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean consumer status:
  both
  `SchwartzMap.tempered_tendstoUniformlyOn_of_finite_seminorm_net`
  and
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  remain present compile-clean in `SchwartzComplete.lean`;
- reading conclusion on the tested route:
  the closure step is available because mathlib has
  `Bornology.IsVonNBounded.closure`,
  but the Montel/compact-image route still fails at the next step;
- exact first missing proof obligation on that route:

  `Bornology.IsVonNBounded ℂ B -> IsCompact (closure B)`

  for
  `B : Set (SchwartzNPoint d (n + m))`;
- whether that obligation is honestly smaller than the producer theorem:
  no;
  it is stronger than the fixed-seminorm producer theorem, so this route does
  not expose a smaller theorem-sized landing;
- exact best Lean-ready producer theorem remains:

  `Bornology.IsVonNBounded ℂ B ->
    ∀ ε > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
      ∀ h ∈ B, ∃ g ∈ t, p (h - g) < ε`,

  equivalently

  `Bornology.IsVonNBounded ℂ B ->
    TotallyBounded ((q_p) '' B)`;
- continuation status after hypothetical compactness:
  the route would still need a continuous seminorm quotient / pseudometric map
  `q_p`, but this is not the first blocker on the tested route;
- immediate downstream use once the producer theorem is available:
  feed it into
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`,
  then into the strong-topology basis inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  OS II witness existence, pointwise convergence, and shell growth control;
  genuinely new:
  the fixed-seminorm finite-net / quotient-precompactness theorem;
  stronger-than-needed and absent on the failed route:
  a Schwartz-space Montel / compact-closure theorem;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean consumer status:
  both
  `SchwartzMap.tempered_tendstoUniformlyOn_of_finite_seminorm_net`
  and
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  remain present compile-clean in `SchwartzComplete.lean`;
- reading conclusion:
  there is still no honest theorem-sized producer-side ingredient smaller than
  fixed-seminorm finite-net / quotient-total-boundedness;
- exact best Lean-ready producer theorem remains:

  `Bornology.IsVonNBounded ℂ B ->
    ∀ ε > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
      ∀ h ∈ B, ∃ g ∈ t, p (h - g) < ε`,

  equivalently

  `Bornology.IsVonNBounded ℂ B ->
    TotallyBounded ((q_p) '' B)`;
- whether it lowers further:
  no;
  every reformulation is the same blocker;
- exact first missing proof obligation:
  bounded Schwartz sets must admit finite `p`-nets for the fixed finite
  seminorm `p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`;
- immediate downstream use once available:
  feed that theorem into
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`,
  then into the strong-topology basis inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  OS II witness existence, pointwise convergence, and shell growth control;
  genuinely new:
  the fixed-seminorm finite-net / quotient-precompactness theorem;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after
checking the exact shell-facing strong-topology consumer now present compile-
clean in `SchwartzComplete.lean` (`2026-04-15`, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact shell-facing consumer now available:
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`;
- reading conclusion:
  the route now genuinely splits into
  producer:
  bounded `B` gives finite `p`-nets
  and
  consumer:
  finite `p`-nets + common `p`-control + pointwise convergence
  give eventual bounded-set `MapsTo`;
- exact best Lean-ready statement above the producer theorem:

  `hU : U ∈ nhds (0 : G)`
  ->
  `hbound : ∀ᶠ a in l, ∀ φ, ‖(T a - L) φ‖ ≤ C * p φ`
  ->
  `hpointwise : ∀ φ, Tendsto (fun a => T a φ) l (nhds (L φ))`
  ->
  `hnet : ∀ ε > 0, ∃ t : Finset _, ∀ φ ∈ B, ∃ ψ ∈ t, p (φ - ψ) < ε`
  ->
  `∀ᶠ a in l, Set.MapsTo (fun φ => (T a - L) φ) B U`;
- whether it sits below the producer theorem:
  yes;
  the only missing input is `hnet`;
- immediate downstream use:
  specialize it at the fixed-time shell family and the packaged limit witness
  `T_t`, then feed the resulting bounded-set `MapsTo` statement into the strong
  topology basis at
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential at this seam;
  early extraction is still wrapper drift only;
- bounded-pass verdict:
  no new production Lean landing was needed in this pass because the consumer
  theorem is already present compile-clean;
  the blocker remains the producer finite-net theorem below it.

Bounded theorem-3 reading note on the same live actual-shell route, refining
what actually sits below the fixed-seminorm compactness seam
(`2026-04-15`, current bounded pass, `2026-04-15T08:09:20Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact best new producer theorem statement remains:

  `Bornology.IsVonNBounded ℂ B ->
    TotallyBounded ((q_p) '' B)`,

  equivalently bounded sets admit finite `p`-`ε` nets, for
  `p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`;
- exact minimal quantified objects:
  fixed finite index set `s`,
  induced seminorm `p`,
  canonical quotient map `q_p`,
  and arbitrary bounded set `B : Set (SchwartzNPoint d (n + m))`;
- refined reading conclusion:
  there is a smaller downstream consumer beneath that theorem, namely:
  common `p`-control
  +
  pointwise convergence
  +
  finite `p`-nets on `B`
  =>
  uniform convergence on `B`;
- but the new producer-side blocker is unchanged:
  the first exact missing proof is still the finite-net / quotient-total-
  boundedness theorem for bounded Schwartz sets;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed;
- witness decision:
  keep `T_t` existential at this seam;
  early extraction is still wrapper drift only.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of whether the exact fixed-seminorm total-boundedness
surface now admits an honest compile-clean theorem statement or skeleton below
the shell seam (`2026-04-15`, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  printed pages `289`, `290-291`, `293-295`;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  `gauge_dominates_on_subspace_of_convex_nhd`,
  and `product_seminorm_dominated`;
  mathlib declarations
  `schwartzSeminormFamily`,
  `schwartzSeminormFamily_apply`,
  `MontelSpace.isCompact_of_isClosed_of_isVonNBounded`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`,
  `TotallyBounded.isVonNBounded`,
  and `isCompact_closure_of_totallyBounded_quasiComplete`;
- reading conclusion:
  no honest compile-clean infrastructure theorem has surfaced below the shell
  seam;
- exact strongest abstract theorem statement still required:

  `Bornology.IsVonNBounded ℂ B ->
    TotallyBounded ((q_p) '' B)`,

  equivalently bounded sets admit finite `p`-`ε` nets, for
  `p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`;
- whether it is genuinely smaller than the shell theorem:
  no;
  it is only the same missing bounded-set `MapsTo` upgrade in quotient
  language;
- first exact blocking proof obligation:
  prove bounded Schwartz sets are totally bounded in the quotient induced by the
  fixed controlling seminorm `p`;
  that is already the whole missing compactness step needed by the shell route;
- exact specialization path:
  packaged witness `T_t`
  +
  common finite `p`-control
  +
  finite `p`-nets on bounded `B`
  =>
  bounded-set `MapsTo`
  =>
  `TendstoUniformlyOn`
  =>
  strong convergence
  =>
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential at this seam;
  early extraction is still wrapper drift only;
- source-backed versus genuinely new:
  source-backed:
  holomorphy,
  growth,
  witness existence,
  pointwise convergence,
  common finite seminorm control,
  and the strong-topology / Montel API surface;
  genuinely new:
  the bounded-set finite-net / quotient-precompactness theorem;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of whether the exact fixed-seminorm total-boundedness
surface can honestly land compile-clean in `SchwartzComplete.lean`
(`2026-04-15`, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  printed pages `289`, `290-291`, `293-295`;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  `gauge_dominates_on_subspace_of_convex_nhd`,
  and `product_seminorm_dominated`;
  mathlib declarations
  `schwartzSeminormFamily`,
  `MontelSpace.isCompact_of_isClosed_of_isVonNBounded`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`,
  `TotallyBounded.isVonNBounded`,
  and `isCompact_closure_of_totallyBounded_quasiComplete`;
- reading conclusion:
  no honest compile-clean infrastructure theorem has surfaced below the shell
  seam;
- exact strongest abstract theorem statement still required:

  `Bornology.IsVonNBounded ℂ B ->
    TotallyBounded ((q_p) '' B)`,

  equivalently bounded sets admit finite `p`-`ε` nets, for
  `p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`;
- whether it is genuinely smaller than the shell theorem:
  no;
  it is only the same missing bounded-set `MapsTo` upgrade in quotient language;
- first exact blocking proof obligation:
  prove bounded Schwartz sets are totally bounded in the quotient induced by the
  fixed controlling seminorm `p`;
  that is already the whole missing compactness step needed by the shell route;
- exact specialization path:
  packaged witness `T_t`
  +
  common finite `p`-control
  +
  finite `p`-nets on bounded `B`
  =>
  eventual `MapsTo`
  =>
  `TendstoUniformlyOn`
  =>
  strong convergence
  =>
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential at this seam;
  early extraction is still wrapper drift only;
- source-backed versus genuinely new:
  source-backed:
  holomorphy,
  growth,
  witness existence,
  pointwise convergence,
  and common finite seminorm control;
  genuinely new:
  the bounded-set finite-net / quotient-precompactness theorem;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of whether the nuclear/Montel lane contains any honest
smaller theorem below the shell bounded-set compactness step
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  still sits immediately before
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  printed pages `289`, `290-291`, `293-295`;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  `gauge_dominates_on_subspace_of_convex_nhd`,
  and `product_seminorm_dominated`;
  mathlib declarations
  `schwartzSeminormFamily`,
  `MontelSpace.isCompact_of_isClosed_of_isVonNBounded`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`,
  `TotallyBounded.isVonNBounded`,
  and `isCompact_closure_of_totallyBounded_quasiComplete`;
- reading conclusion:
  no honest smaller infrastructure theorem has surfaced below the shell seam;
  the strongest abstract theorem still worth naming is fixed-seminorm total
  boundedness of bounded Schwartz sets;
- exact strongest abstract theorem statement now required:

  `Bornology.IsVonNBounded ℂ B ->
    ∀ εp > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
      ∀ h ∈ B, ∃ g ∈ t, p (h - g) < εp`

  for
  `p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`,
  equivalently
  `Bornology.IsVonNBounded ℂ B -> TotallyBounded ((q_p) '' B)`;
- whether it is genuinely smaller than the shell theorem:
  no;
  once `T_t` and the common `p`-bound are fixed, this is immediately the same
  eventual-`MapsTo` / uniform-convergence seam;
- exact specialization path:
  packaged witness `T_t` with pointwise convergence
  +
  common finite `p`-control
  +
  total boundedness of bounded sets in the `p`-quotient
  =>
  eventual `MapsTo`
  =>
  `TendstoUniformlyOn`
  =>
  strong convergence
  =>
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential at this seam;
  early extraction is still wrapper drift only;
- source-backed versus genuinely new:
  source-backed:
  holomorphy,
  growth,
  witness existence,
  pointwise convergence,
  common finite seminorm control,
  and the abstract strong-topology / Montel API surface;
  genuinely new:
  the bounded-set finite-net / quotient-precompactness theorem;
- first blocking proof obligation:
  no inspected theorem makes Schwartz space Montel or proves bounded-set total
  boundedness in a fixed seminorm quotient,
  and `NuclearSpace.lean` is itself still blocked lower down by its two theorem-
  level `sorry`s;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of whether the fixed controlling-seminorm
quotient/total-boundedness theorem is genuinely smaller than the shell
bounded-set theorem (2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  printed pages `289`, `290-291`, `293-295`;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`;
  mathlib declarations
  `schwartzSeminormFamily`,
  `MontelSpace.isCompact_of_isClosed_of_isVonNBounded`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`,
  `TotallyBounded.isVonNBounded`;
- reading conclusion:
  no honest smaller infrastructure theorem has surfaced below the shell seam;
  the only abstract theorem left is fixed-seminorm quotient total boundedness of
  bounded Schwartz sets, equivalently finite `p`-ε-nets for bounded sets;
- exact smallest abstract theorem statement now required:

  `Bornology.IsVonNBounded ℂ B ->
    TotallyBounded ((q_p) '' B)`;

  equivalently
  `Bornology.IsVonNBounded ℂ B ->
    ∀ εp > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
      ∀ h ∈ B, ∃ g ∈ t, p (h - g) < εp`;
- whether it is genuinely smaller than the shell theorem:
  no;
  once `T_t` and the common `p`-bound are fixed, this is immediately the same
  eventual-`MapsTo` / uniform-convergence seam;
- exact specialization path:
  packaged witness `T_t` with pointwise convergence
  +
  common finite `p`-control
  +
  total boundedness of bounded sets in the `p`-quotient
  =>
  eventual `MapsTo`
  =>
  `TendstoUniformlyOn`
  =>
  strong convergence
  =>
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential at this seam;
  early extraction is still wrapper drift only;
- source-backed versus genuinely new:
  source-backed:
  holomorphy,
  growth,
  witness existence,
  pointwise convergence,
  and common finite seminorm control;
  genuinely new:
  the bounded-set finite-net / quotient-precompactness theorem;
- first blocking proof obligation:
  neither repo nor mathlib currently supplies a Schwartz `MontelSpace`
  instance, any usable nuclear-to-Montel theorem, or the fixed-seminorm
  quotient-total-boundedness theorem itself;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of whether the best fixed-seminorm Montel theorem is
actually a smaller seam than the shell bounded-set theorem (2026-04-15,
current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  printed pages `289`, `290-291`, `293-295`;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`;
  mathlib declarations
  `schwartzSeminormFamily`,
  `MontelSpace.isCompact_of_isClosed_of_isVonNBounded`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`;
- reading conclusion:
  no honest smaller infrastructure theorem has surfaced below the shell seam;
  the only abstract theorem left is fixed-seminorm total boundedness of bounded
  Schwartz sets;
- exact smallest abstract theorem statement now required:

  `Bornology.IsVonNBounded ℂ B ->
    ∀ εp > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
      ∀ h ∈ B, ∃ g ∈ t, p (h - g) < εp`

  equivalently
  `Bornology.IsVonNBounded ℂ B -> TotallyBounded ((q_p) '' B)`;
- whether it is genuinely smaller than the shell theorem:
  no;
  once `T_t` and the common `p`-bound are fixed, this is immediately the same
  eventual-`MapsTo` / uniform-convergence seam;
- exact specialization path:
  packaged witness `T_t` with pointwise convergence
  +
  common finite `p`-control
  +
  finite `p`-nets on bounded `B`
  =>
  eventual `MapsTo`
  =>
  `TendstoUniformlyOn`
  =>
  strong convergence
  =>
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential at this seam;
  early extraction is still wrapper drift only;
- source-backed versus genuinely new:
  source-backed:
  holomorphy,
  growth,
  witness existence,
  pointwise convergence,
  and common finite seminorm control;
  genuinely new:
  the bounded-set finite-net / quotient-precompactness theorem;
- first blocking proof obligation:
  neither repo nor mathlib currently supplies a Schwartz `MontelSpace`
  instance or any theorem proving total boundedness in the quotient induced by
  a fixed finite Schwartz seminorm;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of whether the finite controlling seminorm can be
reduced to finite coordinates rather than to the same precompactness seam
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  still sits immediately before
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `bvt_F_holomorphic`,
  `SCV.tubeSlice_uniformPolyGrowth_of_polyGrowth`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  and mathlib
  `schwartzSeminormFamily`,
  `schwartzSeminormFamily_apply`,
  `MontelSpace.isCompact_of_isClosed_of_isVonNBounded`,
  `ContinuousLinearMap.hasBasis_nhds_zero`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`;
- reading conclusion:
  the hoped-for finite-dimensional coordinate reduction does not exist on the
  current formal surface;
  a fixed Schwartz seminorm is already a global sup over all `x`, so the only
  honest lower package is bounded-set total boundedness in the pseudometric /
  quotient induced by that seminorm;
- exact coordinate/quotient statement now required:
  for fixed controlling `p`, prove
  `Bornology.IsVonNBounded ℂ B ->
    ∀ εp > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
      ∀ h ∈ B, ∃ g ∈ t, p (h - g) < εp`;
- whether it is smaller than the shell theorem:
  no;
  it is the same bounded-set theorem in quotient/precompactness form;
- exact specialization path:
  pointwise convergence of the shell family to packaged witness `T_t`
  +
  common finite `p`-bound on `shell_ε - T_t`
  +
  finite `p`-ε-nets for bounded `s`
  =>
  eventual `MapsTo`
  =>
  bounded-set uniform convergence
  =>
  strong-topology convergence
  =>
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential at this seam;
  extracting it early is still wrapper drift only;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, growth, witness existence, pointwise convergence, common finite
  seminorm control, and the abstract Montel API surface;
  genuinely new:
  a Schwartz-specific Montel consequence usable for the controlling seminorm
  quotient;
- first blocking proof obligation:
  no inspected theorem instantiates Schwartz space as Montel or gives total
  boundedness of bounded sets in the quotient/pseudometric induced by a fixed
  Schwartz seminorm;
  without that, no honest compile-clean finite-coordinate reduction lemma can
  land;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of the exact finite-seminorm compactness bridge now
required below `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  still sits immediately before
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `bvt_F_holomorphic`,
  `SCV.tubeSlice_uniformPolyGrowth_of_polyGrowth`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  and mathlib
  `ContinuousLinearMap.hasBasis_nhds_zero`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`;
- reading conclusion:
  the route now needs a Schwartz/Montel statement:
  bounded subsets of Schwartz space are totally bounded for the pseudometric of
  the finite controlling seminorm `p`;
  equivalently, every bounded set has finite `p`-ε-nets;
- whether it is smaller than the shell theorem:
  no;
  this is the same bounded-set theorem in different clothes, because the
  downstream deduction from finite nets to eventual `MapsTo` is immediate;
- exact specialization path:
  pointwise convergence of the shell family to packaged witness `T_t`
  +
  common finite `p`-bound on `shell_ε - T_t`
  +
  finite `p`-ε-nets for bounded `s`
  =>
  eventual `MapsTo`
  =>
  bounded-set uniform convergence
  =>
  strong-topology convergence
  =>
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential at this seam;
  extracting it early is still wrapper drift only;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, growth, witness existence, pointwise convergence, and common
  finite seminorm control;
  genuinely new:
  the bounded-set finite-net / total-boundedness bridge;
- first blocking proof obligation:
  no inspected repo/mathlib theorem turns bounded sets in Schwartz space into
  finite nets for an arbitrary finite Schwartz seminorm;
  without that, no honest compile-clean lemma or theorem-skeleton can be added
  that actually shrinks the seam;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of the exact bounded-set theorem surface now exposed
immediately beneath `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTime_xiShift_zero_eq_add_indicator`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `bvt_F_holomorphic`,
  `SCV.tubeSlice_uniformPolyGrowth_of_polyGrowth`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  and mathlib
  `ContinuousLinearMap.hasBasis_nhds_zero`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`;
- reading conclusion:
  there is still no smaller honest theorem surface below the full bounded-set
  theorem;
  the neighborhood-basis / `MapsTo` form is the same theorem, not a new lower
  lemma;
- exact theorem shape now required:

  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      (∀ h, Filter.Tendsto (...) (nhds (T_t h))) ∧
      ∀ s, Bornology.IsVonNBounded ℂ s →
        TendstoUniformlyOn (...) (fun h => T_t h)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) s`;

  exact internal package:

  `∀ s, Bornology.IsVonNBounded ℂ s → ∀ U ∈ 𝓝 (0 : ℂ),
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      MapsTo
        (fun h =>
          (if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0) - T_t h)
        s U`;
- witness decision:
  keep `T_t` existential at this seam;
  extracting it early is still wrapper drift only;
- insertion placement and consumer chain:
  insert immediately above
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
  translated-shell growth
  ->
  boundary-value witness with pointwise convergence
  ->
  bounded-set / `MapsTo` upgrade
  ->
  bounded-set strong convergence
  ->
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  ->
  quotient/factorization
  ->
  later `hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, translated-shell growth, slice growth, witness existence,
  pointwise boundary convergence, distributional-limit packaging, and common
  finite seminorm control;
  genuinely new:
  bounded-set eventual smallness of the shell-difference family;
- first blocking proof obligation:
  from the finite seminorm delivered by Banach-Steinhaus and a bounded set
  `s ⊆ SchwartzNPoint d (n + m)`, derive the finite-`p`-net / eventual-`MapsTo`
  bridge needed to upgrade pointwise convergence to uniform convergence on `s`;
  no current source object provides that step;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of whether the best abstract strong-topology theorem
really lowers the fixed-time shell seam (2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `bvt_F_holomorphic`,
  `SCV.tubeSlice_uniformPolyGrowth_of_polyGrowth`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  and mathlib
  `ContinuousLinearMap.hasBasis_nhds_zero`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`;
- reading conclusion:
  the reusable abstraction only becomes genuinely smaller if one already has a
  theorem that bounded subsets of Schwartz space are totally bounded for the
  finite controlling seminorm furnished by Banach-Steinhaus;
  no such theorem was found in the inspected repo/mathlib objects during this
  pass;
- exact theorem shape now required on the route:
  after obtaining `T_t`, prove strong convergence of the shell family from
  pointwise convergence plus common finite-seminorm control plus a new bounded
  set compactness bridge for Schwartz space;
- exact internal package:
  for every bounded `s` and `U ∈ 𝓝 (0 : ℂ)`, eventually
  `MapsTo (fun h => shell_ε h - T_t h) s U`;
- witness decision:
  keep `T_t` existential at this seam;
  extracting it early is still wrapper drift only;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, growth, witness existence, pointwise convergence, and common
  finite seminorm control;
  genuinely new:
  the Schwartz bounded-set compactness / total-boundedness theorem needed for
  the final strong-topology upgrade;
- first blocking proof obligation:
  given the finite seminorm `p` from Banach-Steinhaus and a bounded set
  `s ⊆ SchwartzNPoint d (n + m)`, produce finite `p`-ε-nets for `s` strongly
  enough to upgrade pointwise convergence to eventual `MapsTo`;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of the exact bounded-set eventual-`MapsTo` seam now
exposed beneath `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  still sits immediately before
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `bvt_F_holomorphic`,
  `SCV.tubeSlice_uniformPolyGrowth_of_polyGrowth`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  and mathlib
  `ContinuousLinearMap.hasBasis_nhds_zero`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`;
- exact lowest honest interface:
  still the full bounded-set uniform-convergence theorem for the fixed-time
  shell family;
  the neighborhood-basis / `MapsTo` rewrite is the same theorem in the strong
  topology, not a smaller one;
- exact theorem shape now required:

  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      (∀ h, Filter.Tendsto (...) (nhds (T_t h))) ∧
      ∀ s, Bornology.IsVonNBounded ℂ s →
        TendstoUniformlyOn (...) (fun h => T_t h)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) s`;

  exact internal package:

  `∀ s, Bornology.IsVonNBounded ℂ s → ∀ U ∈ 𝓝 (0 : ℂ),
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      MapsTo
        (fun h =>
          (if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0) - T_t h)
        s U`;
- witness decision:
  keep `T_t` existential at this seam;
  the witness already comes packaged from
  `forwardTube_boundaryValueData_of_polyGrowth`,
  so early extraction is only wrapper drift;
- insertion placement and consumer chain:
  insert immediately above
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
  translated-shell growth
  ->
  boundary-value witness with pointwise convergence
  ->
  bounded-set / `MapsTo` upgrade
  ->
  bounded-set uniform convergence
  ->
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  ->
  quotient/factorization
  ->
  later `hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, global growth, slice growth, witness existence, pointwise
  boundary convergence, and common finite seminorm control;
  genuinely new:
  bounded-set eventual smallness of the shell-difference family;
- first blocking proof obligation:
  no current source object upgrades common finite-seminorm control plus
  pointwise convergence on each fixed test into eventual `MapsTo` on an
  arbitrary von Neumann bounded set;
  because of that, even a theorem statement/proof skeleton inserted now would
  not honestly shrink the seam;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of the fixed-time shell seam against the paper, the
boundary-value witness, and the strong-topology declarations
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  still sits immediately before
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact lowest honest interface:
  still the full bounded-set uniform-convergence theorem for the fixed-time
  shell family;
  there is no smaller honest theorem or local lemma below it on the live route;
- exact theorem shape now required:

  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      (∀ h, Filter.Tendsto (...) (nhds (T_t h))) ∧
      ∀ s, Bornology.IsVonNBounded ℂ s →
        TendstoUniformlyOn (...) (fun h => T_t h)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) s`;
- exact internal package:
  the theorem must be proved through the equivalent neighborhood-basis
  statement that for every bounded `s` and every `U ∈ 𝓝 (0 : ℂ)`, the shell
  difference family is eventually `MapsTo s U`;
- witness decision:
  keep `T_t` existential at this seam;
  `forwardTube_boundaryValueData_of_polyGrowth`
  already gives the correct witness package, and naming it earlier is only
  wrapper drift;
- insertion placement and consumer chain:
  insert immediately above
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
  translated-shell growth
  ->
  boundary-value witness with pointwise convergence
  ->
  bounded-set / `MapsTo` upgrade
  ->
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  ->
  quotient/factorization
  ->
  later `hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, global growth, slice growth, witness existence, pointwise
  boundary convergence, and common finite seminorm control;
  genuinely new:
  bounded-set eventual smallness of the shell-difference family;
- first blocking proof obligation:
  no current source object upgrades common finite-seminorm control plus
  pointwise convergence on each fixed test into eventual `MapsTo` on an
  arbitrary von Neumann bounded set;
  because of that, even a theorem skeleton inserted now would not honestly
  shrink the seam.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of whether the full bounded-set shell theorem can now
land at the first insertion surface without merely restating the blocker
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only live theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `bvt_F_holomorphic`,
  `SCV.tubeSlice_uniformPolyGrowth_of_polyGrowth`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  and mathlib
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`,
  `ContinuousLinearMap.hasBasis_nhds_zero`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`;
- exact lowest honest interface now exposed:
  still the full bounded-set uniform-convergence theorem for the fixed-time
  shell family;
  there is no smaller honest theorem below it on the live route;
- exact theorem shape and internal package:
  the route requires

  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      (∀ h, Tendsto (...) (nhds (T_t h))) ∧
      ∀ s, Bornology.IsVonNBounded ℂ s →
        TendstoUniformlyOn (...) (fun h => T_t h)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) s`;

  and the same content must be proved internally via the neighborhood-basis
  statement

  `∀ s, Bornology.IsVonNBounded ℂ s → ∀ U ∈ 𝓝 (0 : ℂ),
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      MapsTo
        (fun h =>
          (if hε : 0 < ε then
            section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
          else
            0) - T_t h)
        s U`;
- witness decision:
  keep `T_t` existential at this seam;
  the natural witness is already the one returned by
  `forwardTube_boundaryValueData_of_polyGrowth`,
  and extracting it early is only wrapper drift;
- consumer chain:
  translated-shell growth
  -> raw shell CLM family
  -> existential witness `T_t` with pointwise convergence
  -> internal neighborhood-basis / `MapsTo` package
  -> bounded-set uniform convergence
  -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, global growth, slice growth, pointwise boundary values,
  witness existence, and common finite seminorm control;
  genuinely new:
  eventual bounded-set smallness of the shell difference family;
- first blocking proof obligation:
  no current source object yields the upgrade from common seminorm control plus
  pointwise convergence to eventual `MapsTo` on an arbitrary von Neumann
  bounded set;
  for that reason, even a theorem skeleton inserted now would not honestly
  shrink the seam;
- verification result:
  no production Lean edit was attempted in this pass;

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first audit of the bounded-set shell seam against the paper, the
boundary-value package, and the strong-topology declarations
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only live theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `bvt_F_holomorphic`,
  `SCV.tubeSlice_uniformPolyGrowth_of_polyGrowth`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  and mathlib
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`,
  `ContinuousLinearMap.hasBasis_nhds_zero`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`;
- exact lowest honest interface now exposed:
  still the full bounded-set uniform-convergence theorem for the fixed-time
  shell family;
  there is no smaller honest theorem below it on the live route;
- exact first internal package:
  the theorem must be executed through the equivalent neighborhood-basis /
  `MapsTo` form for the shell-difference family;
  this is not smaller mathematics, only the exact strong-topology obligation;
- exact eventual-smallness obligation on bounded sets:
  after choosing the existential witness `T_t`, prove that for every bounded
  `s : Set (SchwartzNPoint d (n + m))` and every neighborhood `U` of `0` in
  `ℂ`, the shell difference
  `h ↦ (if hε : 0 < ε then section43_fixedTimeShellRawCLM ... ε hε h else 0) - T_t h`
  is eventually `MapsTo s U` along `nhdsWithin (0 : ℝ) (Set.Ioi 0)`;
- witness decision:
  keep `T_t` existential at this seam;
  the natural witness is the one already produced existentially by
  `forwardTube_boundaryValueData_of_polyGrowth`;
- consumer chain:
  translated-shell growth
  -> raw shell CLM family
  -> existential witness `T_t` with pointwise convergence
  -> internal neighborhood-basis / `MapsTo` package
  -> bounded-set uniform convergence
  -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, global growth, pointwise boundary values, witness existence, and
  common finite Schwartz-seminorm control;
  genuinely new:
  eventual bounded-set smallness of the shell difference family;
- first blocking proof obligation:
  no current source object yields the upgrade from common seminorm control plus
  pointwise convergence to the eventual `MapsTo` conclusion on an arbitrary
  von Neumann bounded set;
- verification result:
  no production Lean edit was attempted in this pass;
  verification commands were
  `rg -n "section43_fixedTimeShellRawCLM|section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime|section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime|sorry" OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
  and
  `mutool draw -F txt -o - references/'reconstruction theorem II.pdf' 9-15`.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of whether any compile-clean local theorem packaging
can honestly land beneath the fixed-time shell existence seam
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only live theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `bvt_F_holomorphic`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  and mathlib
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.hasBasis_nhds_zero`;
- exact lowest honest interface now exposed:
  still the full bounded-set uniform-convergence theorem for the fixed-time
  shell family;
  there is no smaller honest theorem or local lemma below it on the live route;
- exact theorem statement:

  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      (∀ h : SchwartzNPoint d (n + m),
        Filter.Tendsto
          (fun ε : ℝ =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (T_t h))) ∧
      ∀ s : Set (SchwartzNPoint d (n + m)),
        Bornology.IsVonNBounded ℂ s →
        TendstoUniformlyOn
          (fun ε h =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
          (fun h => T_t h)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          s`;
- witness decision:
  keep `T_t` existential at this seam;
  the natural witness is the one already produced existentially by
  `forwardTube_boundaryValueData_of_polyGrowth`;
- consumer chain:
  translated-shell growth
  -> raw shell CLM family
  -> existential witness `T_t` with pointwise convergence
  -> bounded-set uniform convergence
  -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, global growth, pointwise boundary values, and equicontinuity /
  common seminorm control;
  genuinely new:
  uniform convergence on each von Neumann bounded test set;
- first blocking proof obligation:
  show the shell difference tends to `0` uniformly on every bounded set;
  equivalently, prove the eventual `MapsTo s U` statement for every bounded
  `s` and every neighborhood `U` of `0`;
- verification result:
  no production Lean edit was attempted in this pass.

Bounded theorem-3 reading note on the same live actual-shell route, fixing the
exact proof decomposition at the strong-topology seam below the fixed-time
shell limit theorem (2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only live theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `bvt_F_holomorphic`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `section43_fixedTimeShellRawCLM`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  `distributional_limit_of_equicontinuous`,
  and mathlib
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.hasBasis_nhds_zero`;
- exact lowest honest interface now exposed:
  still the full bounded-set uniform-convergence theorem;
  there is no smaller honest theorem below it on the live route;
- exact internal execution package at the same surface:
  yes;
  the theorem should be attempted through the neighborhood-basis / `MapsTo`
  form for the shell difference, because that is the exact obligation exposed
  by the strong topology on continuous linear maps;
  this does not lower the theorem surface;
- strongest honest theorem statement and witness handling:
  keep `T_t` existentially packaged, with
  pointwise convergence on each fixed test and
  bounded-set uniform convergence on every von Neumann bounded set;
  do not introduce a wrapper witness extracted by `Classical.choose` unless a
  later theorem truly requires a named witness;
- consumer chain:
  translated-shell growth
  -> raw shell CLM family
  -> existential witness `T_t` with pointwise convergence
  -> internal neighborhood-basis / `MapsTo` package
  -> bounded-set uniform convergence
  -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, global growth, slice growth, and pointwise boundary values;
  genuinely new:
  the strong-dual upgrade from those data to eventual bounded-set smallness of
  the shell difference family;
- first blocking proof obligation:
  show the shell difference tends to `0` uniformly on every bounded set;
  equivalently, prove the eventual `MapsTo s U` statement for every bounded
  `s` and every neighborhood `U` of `0`;
- verification result:
  no production Lean edit was attempted in this pass.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first check of whether the pinned bounded-set `MapsTo` obligation
lowers to one smaller theorem beneath the fixed-time shell limit theorem
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only live theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `bvt_F_holomorphic`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `section43_fixedTimeShellRawCLM`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  `distributional_limit_of_equicontinuous`,
  and mathlib
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`;
- exact lowest honest interface now exposed:
  still the full bounded-set uniform-convergence theorem;
  there is no smaller honest intermediate theorem on the live route;
- exact reason:
  the paper and the current Lean boundary-value package only force
  pointwise convergence on each fixed test function;
  the current Banach-Steinhaus lemmas only force equicontinuity / common
  seminorm control;
  neither source-backed package yields the missing eventual uniform smallness on
  arbitrary von Neumann bounded test sets;
- strongest honest intermediate theorem statement:
  none strictly smaller;
  any theorem asserting that those existing hypotheses already imply bounded-set
  eventual `MapsTo` would itself be the new missing strong-topology theorem;
- consumer chain:
  translated-shell growth
  -> raw shell CLM family
  -> existential witness `T_t` with pointwise convergence
  -> bounded-set eventual `MapsTo` / `TendstoUniformlyOn`
  -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, global growth, slice growth, and pointwise boundary values;
  genuinely new:
  uniform convergence on each von Neumann bounded test set;
- first blocking proof obligation:
  show the shell difference tends to `0` uniformly on every bounded set, not
  just on each fixed test function;
- verification result:
  no production Lean edit was attempted in this pass.

Bounded theorem-3 reading note on the same live actual-shell route, clarifying
the exact next theorem interface and witness choice below the fixed-time shell
existence theorem (2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only live theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  `distributional_limit_of_equicontinuous`,
  and mathlib
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`;
- exact next honest interface:
  still one theorem, not a smaller packaging lemma:

  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      (∀ h : SchwartzNPoint d (n + m),
        Filter.Tendsto
          (fun ε : ℝ =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (T_t h))) ∧
      ∀ s : Set (SchwartzNPoint d (n + m)),
        Bornology.IsVonNBounded ℂ s →
        TendstoUniformlyOn
          (fun ε h =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
          (fun h => T_t h)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          s`;
- witness decision:
  keep `T_t` existential at this seam;
  the paper/Lean source gives an existential boundary-value functional, and
  forcing an explicit extracted witness earlier would only rename that data;
- consumer chain:
  translated-shell growth
  -> raw shell CLM family
  -> existential witness `T_t` with pointwise convergence
  -> bounded-set uniform convergence
  -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  holomorphy, global growth, and pointwise ray boundary values;
  genuinely new:
  uniform convergence on each von Neumann bounded test set;
- first blocking proof obligation:
  show the shell difference tends to `0` uniformly on bounded sets, not just on
  each fixed test function;
- verification result:
  no production Lean edit was attempted in this pass.

Bounded theorem-3 reading note on the same live actual-shell route, after a
fresh source-first re-check of the topology seam below
`section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only live theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `section43_fixedTimeShellRawCLM`,
  `SCV.tubeSlice_uniformPolyGrowth_of_polyGrowth`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  `distributional_limit_of_equicontinuous`,
  and mathlib
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`;
- exact lowest honest interface now exposed:
  still the full bounded-set uniform-convergence theorem;
  there is no smaller reusable theorem/local lemma between the current CLM
  witness package and `Tendsto ... (nhds T_t)` on the Schwartz dual;
- exact statement surface:
  for fixed `t > 0`,

  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      ∀ s : Set (SchwartzNPoint d (n + m)),
        Bornology.IsVonNBounded ℂ s →
        TendstoUniformlyOn
          (fun ε h =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
          (fun h => T_t h)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          s`;
- consumer chain:
  translated-shell growth
  -> local holomorphy by composition
  -> `forwardTube_boundaryValueData_of_polyGrowth`
  -> CLM witness `T_t` + scalar convergence
  -> bounded-set uniform convergence theorem
  -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  the forward-tube scalar boundary-value package,
  slice growth on fixed rays,
  and Banach-Steinhaus/equicontinuity control for Schwartz dual families;
  genuinely new:
  the passage from those data to uniform convergence on arbitrary von Neumann
  bounded test sets;
- why the direct topology upgrade still fails:
  pointwise shell convergence plus a common finite seminorm bound only gives
  equicontinuity and a CLM witness;
  strong convergence of CLMs is bounded convergence, and no inspected theorem
  derives that bounded-set uniformity from the current source-backed package;
- verification result:
  no production Lean edit was attempted in this pass, because the exact first
  missing step is unchanged.

Bounded theorem-3 reading note on the same live actual-shell route, after
checking whether Banach-Steinhaus/equicontinuity infrastructure lowers the
strong-topology seam below the full bounded-set uniform-convergence theorem
(2026-04-15, later bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only live theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF pages 10-11 / printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `section43_fixedTimeShellRawCLM`,
  `SCV.tubeSlice_uniformPolyGrowth_of_polyGrowth`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_of_tendsto_filter`,
  `distributional_limit_of_equicontinuous`,
  and mathlib
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`;
- exact lowest honest interface now exposed:
  still the full bounded-set uniform-convergence theorem;
  the candidate smaller bridge through Banach-Steinhaus gives only a common
  seminorm bound / equicontinuity, not the missing uniform convergence on
  bounded subsets of the Schwartz space;
- exact statement surface:
  for fixed `t > 0`,

  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      ∀ s : Set (SchwartzNPoint d (n + m)),
        Bornology.IsVonNBounded ℂ s →
        TendstoUniformlyOn
          (fun ε h =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
          (fun h => T_t h)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          s`;
- consumer chain:
  translated-shell growth
  -> local holomorphy by composition
  -> `forwardTube_boundaryValueData_of_polyGrowth`
  -> CLM witness `T_t` + scalar convergence
  -> bounded-set uniform convergence theorem
  -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  the forward-tube scalar boundary-value package and the local slice/equicontinuity
  infrastructure;
  genuinely new:
  the passage from pointwise/equicontinuous CLM data to the strong dual
  topology on `SchwartzNPoint d (n + m) →L[ℂ] ℂ`;
- verification result:
  no production Lean edit was attempted in this pass, because the candidate
  smaller bridge was inspected and found insufficient.

Bounded theorem-3 reading note on the same live actual-shell route, after
re-checking whether the translated-shell analytic package now already closes
`section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
(2026-04-15, latest bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only live theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF page 10 / printed page 290 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `xiShift`,
  `norm_xiShift_le`,
  `xiShift_mem_forwardTube_of_real`,
  `bvt_F_holomorphic`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  plus mathlib
  `ContinuousLinearMap.topologicalSpace`
  and
  `UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn`;
- exact lowest honest interface now exposed:
  not another analytic growth theorem;
  the next genuinely missing local theorem is still the strong-topology
  upgrade from the boundary-value theorem's pointwise convergence to bounded-set
  uniform convergence of the shell CLM family on
  `SchwartzNPoint d (n + m)`;
- exact statement surface:
  for fixed `t > 0`,

  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      ∀ s : Set (SchwartzNPoint d (n + m)),
        Bornology.IsVonNBounded ℂ s →
        TendstoUniformlyOn
          (fun ε h =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
          (fun h => T_t h)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          s`;
- consumer chain:
  translated-shell growth
  -> local holomorphy by composition
  -> `forwardTube_boundaryValueData_of_polyGrowth`
  -> CLM witness `T_t` + scalar convergence
  -> bounded-set uniform convergence upgrade
  -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  the forward-tube scalar/CLM boundary-value package;
  genuinely new:
  the passage to the bounded-convergence topology on the Schwartz dual;
- verification result:
  no production Lean edit was attempted in this pass, because the missing step
  is now a topology upgrade, not another translated-shell analytic estimate.

Bounded theorem-3 reading note on the same live actual-shell route, after
re-checking whether the current translated-shell analytic package already closes
`section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
(2026-04-15, current bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only live theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  PDF page 9 / printed page 289 / Theorem 4.3;
  PDF page 10 / printed page 290 / `(5.2)` `(5.3)` `(5.4)`;
  PDF pages 13-15 / printed pages 293-295 / Section V.2 `(AN)` `(PN)`,
  `(5.20)` `(5.21)`, Lemma 5.2;
  Lean declarations
  `xiShift`,
  `norm_xiShift_le`,
  `xiShift_mem_forwardTube_of_real`,
  `bvt_F_holomorphic`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- exact lowest honest interface now exposed:
  not another analytic growth theorem;
  the next genuinely missing local theorem is the strong-topology upgrade from
  scalar boundary values to bounded-set uniform convergence of the shell CLM
  family on
  `SchwartzNPoint d (n + m)`;
- exact statement surface:
  for fixed `t > 0`,

  `∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
      ∀ s : Set (SchwartzNPoint d (n + m)),
        Bornology.IsVonNBounded ℂ s →
        TendstoUniformlyOn
          (fun ε h =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε h
            else
              0)
          (fun h => T_t h)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          s`;
- consumer chain:
  translated-shell growth
  -> local holomorphy by composition
  -> `forwardTube_boundaryValueData_of_polyGrowth`
  -> scalar witness `T_t`
  -> bounded-set uniform convergence upgrade
  -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  the forward-tube scalar boundary-value package;
  genuinely new:
  the passage to the strong dual topology on the Schwartz space;
- verification result:
  no production Lean edit was attempted in this pass, because the missing step
  is no longer a direct analytic proof but the absent CLM-topology upgrade.

Bounded theorem-3 reading note on the same live actual-shell route, after a
second direct translated-growth insertion attempt was removed
(2026-04-15, current latest bounded pass):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only live theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  printed page 289 / Theorem 4.3;
  printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  printed pages 293-295 / Section V.2 `(AN)` `(PN)`, `(5.20)` `(5.21)`,
  Lemma 5.2;
  Lean declarations
  `xiShift`,
  `bvt_F_hasGlobalForwardTubeGrowth`,
  `bvt_F_holomorphic`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- exact lowest honest compile-clean interface now exposed:
  not yet the full translated-shell growth theorem itself, but the smaller
  local `xiShift` branch-normalization estimate:
  real `xiShift` preserves the imaginary-part map and admits the explicit
  affine decomposition `xiShift = z + shift`;
- consumer chain:
  branch-normalization estimate
  -> translated-shell growth theorem
  -> translated-shell holomorphy
  -> `forwardTube_boundaryValueData_of_polyGrowth`
  -> rewrite to `section43_fixedTimeShellRawCLM`
  -> `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- source-backed versus genuinely new:
  source-backed:
  the forward-tube growth and boundary-value package;
  genuinely new:
  the concrete `xiShift` branch normalization for the fixed-time translated
  shell;
- verification result:
  `lake build OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanPositivity`
  failed on the attempted insertion with unresolved local branch goals only;
  the attempted theorem was removed, so no production Lean edit remains.

Bounded theorem-3 reading note on the same live actual-shell route, after a
direct attempt to land the translated-shell growth theorem
(2026-04-15, latest bounded pass):

- re-checked first:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the only theorem-level `sorry`s at this frontier remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- arbitrary-forward-tube `xiShift` geometry:
  now fully closed in source;
- exact lowest honest interface:
  the translated-shell global-growth statement for
  `z ↦ bvt_F OS lgc (n + m)
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))`
  on `ForwardTube d (n + m)`;
- local hypotheses / names:
  `OS`, `lgc`, `{n m}`, `hm : 0 < m`, `t : ℝ`,
  local `r : Fin (n + m)`,
  local `F_t : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ`,
  later witness `T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ`;
- source-backed versus genuinely new:
  source-backed:
  Theorem 4.3, Section V/V.2 growth-and-boundary-value material, Lean
  `bvt_F_hasGlobalForwardTubeGrowth`,
  `bvt_F_holomorphic`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  and the closed `xiShift` geometry seam;
  genuinely new:
  the translated-shell growth transfer itself;
- bounded-pass outcome:
  a direct Lean attempt at that theorem did not verify cleanly and was removed;
  therefore no compile-clean theorem/local lemma statement or skeleton landed
  in production Lean this pass.

Bounded theorem-3 reading note on the live fixed-time raw-shell existence seam,
re-checking whether the existing ambient-limit theorem surface itself needs any
statement repair before proof work (2026-04-15, later bounded pass):

Bounded theorem-3 reading note on the live fixed-time raw-shell existence seam,
now pinning the exact proof-route package for the existing theorem
(2026-04-15, current bounded pass):

- `(A0)` was re-run first and the first live insertion surface remains
  `section43_fixedTimeShellRawCLM`
  immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- exact paper objects inspected:
  `reconstruction theorem II.pdf`
  printed page 289 / Theorem 4.3;
  printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  printed pages 293-295 / Section V.2 `(AN)` `(PN)`, `(5.20)` `(5.21)`,
  Lemma 5.2;
- exact local declarations rechecked:
  `xiShift`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `bvt_boundary_values`,
  `bvt_F_translationInvariant`,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `bvt_F_canonicalXiShift_hasPolynomialGrowth`,
  `canonicalXiShift_mem_forwardTube`,
  `contDiff_canonicalXiShift`,
  `section43PositiveEnergyQuotientMap`,
  `Section43PositiveEnergyComponent`,
  `evalAtZeroDescendsToSection43PositiveEnergyComponent`,
  and `hlimit_os`;
- unsupported-residue verdict:
  live source still has theorem-level `sorry`s at
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
  none were removed in this pass;
- strongest source-backed package actually available:
  `forwardTube_boundaryValueData_of_polyGrowth`;
  this already constructs a CLM-valued boundary functional from a holomorphic,
  globally polynomially bounded continuation on `ForwardTube`;
- exact proof-route decomposition:
  define
  `F_t z := bvt_F OS lgc (n + m)
    (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))`,
  prove holomorphy and global growth for `F_t`,
  apply `forwardTube_boundaryValueData_of_polyGrowth`,
  specialize to
  `canonicalForwardConeDirection (d := d) (n + m)`,
  rewrite the scalar boundary-value family as
  `section43_fixedTimeShellRawCLM`,
  and conclude the existing theorem without changing its statement;
- exact first genuinely new theorem-sized sub-obligation:
  the fixed-time shifted global-growth theorem for `F_t`,
  with statement

  `∃ C_bd : ℝ, ∃ N : ℕ, 0 < C_bd ∧
      ∀ z ∈ ForwardTube d (n + m),
        ‖bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0 z (t : ℂ))‖
          ≤ C_bd * (1 + ‖z‖) ^ N`;

  no separate ambient Cauchy/extraction theorem is first needed on this route;
- exact local hypotheses / new object names:
  `OS`, `lgc`, `{n m}`, `hm : 0 < m`, `t : ℝ`, `ht : 0 < t`,
  `r : Fin (n + m)`,
  `F_t : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ`,
  `T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ`;
- insertion-surface and consumer verdict:
  the existing theorem still belongs directly after
  `section43_fixedTimeShellRawCLM`;
  once proved, the consumer chain remains
  CLM limit existence
  -> quotient-kernel / factorization
  -> full shell boundary-distribution package
  -> outside-region coefficient corollary
  -> `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> `hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  Theorem 4.3, Section V / V.2 continuation-and-growth material, and Lean
  `forwardTube_boundaryValueData_of_polyGrowth`;
  genuinely new:
  the concrete global-growth theorem for the fixed-time shifted continuation,
  then the specialization back to the live shell CLM family;
- no production Lean edit was made in this pass, and no compile-clean skeleton
  was landed.

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` remain clean; the second still contains
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence` and
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- exact paper objects inspected:
  `reconstruction theorem II.pdf`
  printed page 289 / Theorem 4.3;
  printed pages 293-295 / Section V.2 `(AN)` `(PN)`, `(5.20)` `(5.21)`,
  Lemma 5.2;
- exact local declarations rechecked:
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_shellToSlice_limit_fixedTime`,
  `section43PositiveEnergyQuotientMap`,
  `Section43PositiveEnergyComponent`,
  `evalAtZeroDescendsToSection43PositiveEnergyComponent`,
  and `hlimit_os`;
- unsupported-residue verdict:
  live source still has theorem-level `sorry`s at
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
  none were removed in this pass;
- statement verdict:
  the existing theorem statement is still honest as written, with the correct
  witness type
  `T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ`
  and the correct one-sided limit filter
  `nhdsWithin (0 : ℝ) (Set.Ioi 0)`;
- insertion-surface and consumer verdict:
  this theorem still belongs directly after
  `section43_fixedTimeShellRawCLM`;
  downstream chain remains
  CLM limit existence
  -> quotient-kernel / factorization
  -> full shell boundary-distribution package
  -> outside-region coefficient corollary
  -> `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> `hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  Theorem 4.3, Section V.2 `(AN)` `(PN)`, `(5.20)` `(5.21)`, Lemma 5.2, and
  the local ambient-shell / quotient packaging;
  genuinely new:
  the convergence proof for the concrete fixed-time shell family, then the
  quotient descent of the resulting `T_t`;
- no production Lean edit was made in this pass, because the theorem surface is
  already correct and no smaller honest skeleton exists beneath it yet.

Bounded theorem-3 reading note on the fixed-time ambient-shell limit-existence
theorem surface (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` remain clean; the second still contains
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact paper objects inspected:
  `reconstruction theorem II.pdf`
  printed pages 288-289 / Theorem 4.1-4.3;
  printed pages 290-291 / Section V `(5.2)` `(5.3)` `(5.4)`;
  printed pages 294-295 / Section V.2 `(AN)` `(PN)`, `(5.20)` `(5.21)`,
  Lemma 5.2;
- exact local declarations rechecked:
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43PositiveEnergyQuotientMap`,
  `Section43PositiveEnergyComponent`,
  `evalAtZeroDescendsToSection43PositiveEnergyComponent`,
  and `hlimit_os`;
- unsupported-residue verdict:
  live source still has theorem-level `sorry`s at
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
  none were removed in this pass;
- statement verdict:
  the existing theorem statement is honest as written:

  `∀ t : ℝ, 0 < t →
      ∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
        Filter.Tendsto
          (fun ε : ℝ =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε
            else
              0)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds T_t)`;

- exact local hypotheses genuinely required:
  `OS`, `lgc`, `{n m}`, `hm : 0 < m`, `t : ℝ`, `ht : 0 < t`;
- exact next proof-shape split:
  keep this theorem surface unchanged;
  the next honest work item is its proof route, not a statement repair;
  only after a witness `T_t` exists should the route add the stronger descended
  interface
  `T̄_t : Section43PositiveEnergyComponent (d := d) (n + m) →L[ℂ] ℂ`
  with
  `T_t = T̄_t.comp (section43PositiveEnergyQuotientMap (d := d) (n + m))`;
- exact insertion-surface location and consumer chain:
  this theorem belongs, and already sits, directly after
  `section43_fixedTimeShellRawCLM`;
  downstream chain remains
  CLM limit existence
  -> quotient-kernel / factorization
  -> full shell boundary-distribution package
  -> outside-region coefficient corollary
  -> `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> `hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  the paper continuation/existence package and the local ambient-shell CLM
  packaging;
  genuinely new:
  the proof of the actual shell-family convergence at fixed `t > 0`, and then
  the quotient descent of `T_t`;
- no production Lean edit was made in this pass, because no honest compile-clean
  helper skeleton smaller than the existing theorem surface was available.

Bounded theorem-3 reading note on the live fixed-time shell package split
(2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` remain clean; the second still contains
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact paper objects inspected:
  `reconstruction theorem II.pdf`
  printed pages 288-289 / Theorem 4.1-4.3;
  printed pages 290-291 / Section V `(5.2)` `(5.3)` `(5.4)`;
  printed pages 294-295 / Section V.2 `(5.20)` `(5.21)`, Lemma 5.2, `(AN)`,
  `(PN)`;
- exact local declarations rechecked:
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `differentiableAt_bvt_F_restrictScalars`,
  `hasFDerivAt_bvt_F_canonicalXiShift`,
  `section43PositiveEnergyQuotientMap`,
  `evalAtZeroDescendsToSection43PositiveEnergyComponent`,
  and `hlimit_os`;
- unsupported-residue verdict:
  live source inspection shows two current theorem-level `sorry`s in
  `OSToWightmanPositivity.lean`, at
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
  none were removed in this pass;
- split verdict:
  yes; the fixed-time shell boundary-distribution package already splits into
  an object-introduction step plus a later quotient-support/factorization step;
- exact lowest honest theorem/object interface now exposed:

  `∀ t : ℝ, 0 < t →
      ∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
        Filter.Tendsto
          (fun ε : ℝ =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε
            else
              0)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds T_t)`;

- exact local hypotheses genuinely required:
  `OS`, `lgc`, `{n m}`, `hm : 0 < m`, `t : ℝ`, `ht : 0 < t`;
- exact next theorem-sized interface:
  after choosing `T_t`, prove either
  `∀ h, section43PositiveEnergyQuotientMap ... h = 0 -> T_t h = 0`
  or, more strongly and more honestly for the codomain route,
  introduce a descended functional
  `T̄_t : Section43PositiveEnergyComponent (d := d) (n + m) →L[ℂ] ℂ`
  with
  `T_t = T̄_t.comp (section43PositiveEnergyQuotientMap (d := d) (n + m))`;
- exact new object names/types required:
  no new type for the lowest step beyond
  `T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ`;
  one new descended-object type at the next step:
  `T̄_t : Section43PositiveEnergyComponent (d := d) (n + m) →L[ℂ] ℂ`;
- exact insertion-surface location:
  the existence theorem belongs, and already sits, directly after
  `section43_fixedTimeShellRawCLM`;
  the later coefficient corollary still belongs after
  `hasFDerivAt_bvt_F_canonicalXiShift`;
- exact immediate downstream consumer chain:
  CLM limit existence
  -> quotient-kernel / factorization
  -> full shell boundary-distribution package
  -> outside-region coefficient corollary
  -> product-level pointwise `hlim`
  -> `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> `hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  the paper continuation/existence package and the local quotient codomain API;
  genuinely new:
  the proof that the shell-limit functional descends through the
  positive-energy quotient, and then the outside-region coefficient limit;
- no production Lean edit was made in this pass, because the lowest honest
  statement is already present in live source rather than merely doc-extracted.

Bounded theorem-3 reading note on the live shell complement branch, checking
whether OS II first needs a shell boundary-distribution package below the bare
coefficient theorem (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact paper objects inspected:
  `reconstruction theorem II.pdf`
  printed pages 288-289 / Theorem 4.1 `(4.4)` `(4.5)`, Theorem 4.2 `(4.6)`,
  Theorem 4.3;
  printed pages 290-295 / `(5.2)` `(5.3)` `(5.4)`, Section V.2 `(5.20)`
  `(5.21)`, Lemma 5.2, `(AN)`, `(PN)`;
- exact local declarations rechecked:
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `differentiableAt_bvt_F_restrictScalars`,
  `hasFDerivAt_bvt_F_canonicalXiShift`,
  `section43_fixedPair_canonicalShell_sliceRealization`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_mixedOrderSlice_descendedScalar_eq_directPsiIntegral_fixedTime`,
  `section43_iteratedSlice_descendedPairing`,
  and `hlimit_os`;
- implication verdict:
  yes: before the outside-region pointwise coefficient limit can be justified,
  the live route first needs a fixed-time shell boundary-distribution /
  quotient-support package;
- exact reason:
  the paper support theorem acts only on descended `W_k`, while the present
  shell/slice realization only reaches an actual-shell frozen-slice object on
  `section43PositiveEnergyRegion d (n + m)`;
  outside that region there is not yet a shell-side descended object whose
  support can be read from Theorem 4.3;
- exact next genuinely new package:
  for fixed `t > 0`, produce a limiting shell functional `T_t` on
  `SchwartzNPoint d (n + m)` such that
  `ε ↦ ∫ y, bvt_F ... (xiShift ...) * h y` tends to `T_t h` and `T_t`
  annihilates every `h` with
  `section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0`;
- exact full theorem shape:

  `∀ t : ℝ, 0 < t →
      ∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
        (∀ h : SchwartzNPoint d (n + m),
          Filter.Tendsto
            (fun ε : ℝ =>
              ∫ y : NPointDomain d (n + m),
                bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun k μ =>
                      ↑(y k μ) +
                        ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                          Complex.I)
                    (t : ℂ)) *
                  h y)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (T_t h))) ∧
        (∀ h : SchwartzNPoint d (n + m),
          section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 →
            T_t h = 0)`;
- exact local hypotheses genuinely required:
  `OS`, `lgc`, `{n m}`, `hm : 0 < m`, `t : ℝ`, `ht : 0 < t`;
- exact insertion-surface location:
  first after `section43_fixedTimeShellRawCLM`, then later the pointwise
  outside-region corollary after `hasFDerivAt_bvt_F_canonicalXiShift`;
- exact immediate downstream consumer chain:
  shell boundary-distribution package
  -> pointwise outside-region coefficient limit
  -> product-level outside-region pointwise `hlim`
  -> full pointwise `hlim` for
     `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> shell-integral limit `0`
  -> `hlimit_os`
  -> `tendsto_nhds_unique hlimit_w hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  continuation / support for descended objects plus region-local shell/slice
  transport;
  genuinely new:
  the shell-family descent to a fixed-time boundary functional supported on the
  Section-4.3 positive-energy region;
- no unsupported residue was found or removed;
- this package is one bounded mathematical unit, but not yet an honest
  compile-clean theorem/local-lemma skeleton at the current pointwise insertion
  surface, so no production Lean edits were made.

Bounded theorem-3 reading note on the live coefficient-only outside-region seam,
checking whether OS II already implies it on the actual shell (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact paper objects inspected:
  `reconstruction theorem II.pdf`
  printed pages 288-289 / Theorem 4.1 `(4.4)` `(4.5)`, Theorem 4.2 `(4.6)`,
  Theorem 4.3;
  printed pages 293-295 / Section V.2, formulas `(5.20)` `(5.21)`, Lemma 5.2,
  and the `(AN)` `(PN)` continuation package;
- exact local declarations rechecked:
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `differentiableAt_bvt_F_restrictScalars`,
  `hasFDerivAt_bvt_F_canonicalXiShift`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  and `hlimit_os`;
- implication verdict:
  no, the inspected OS II objects do not already imply the coefficient-only
  theorem on the live actual shell;
- exact reason:
  the paper gives support only for descended `W_k` after continuation, while the
  local Lean route only has region-local shell/slice transport;
  the branch
  `y ∉ section43PositiveEnergyRegion d (n + m)` still lacks an honest theorem
  turning that support information into vanishing of the actual shell
  coefficient;
- exact next genuinely new theorem package:
  for every `y : NPointDomain d (n + m)` with
  `y ∉ section43PositiveEnergyRegion d (n + m)`, prove
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds 0)`;
- exact local hypotheses genuinely required:
  `OS`, `lgc`, `{n m}`, `hm : 0 < m`, `t : ℝ`, and the branch data `y`, `hy`;
- exact insertion-surface location:
  the second live shell-local insertion point in
  `OSToWightmanPositivity.lean`, immediately after
  `hasFDerivAt_bvt_F_canonicalXiShift` and before
  `tendsto_bvt_F_canonical_conjTensorProduct_timeShift_boundaryValue`;
- exact immediate downstream consumer chain:
  coefficient-only complement-side pointwise `hlim`
  -> product-level complement-side pointwise `hlim`
  -> full pointwise `hlim` for
     `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> shell-integral limit `0`
  -> `hlimit_os`
  -> `tendsto_nhds_unique hlimit_w hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  continuation and descended positive-energy support, plus region-local fixed-
  time transport;
  genuinely new:
  the actual-shell complement-control bridge, exposed by the coefficient-only
  theorem above;
- no unsupported residue was found or removed;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 reading note on the fixed-seminorm Montel/quotient seam
below `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
(2026-04-15):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- exact source objects inspected:
  `reconstruction theorem II.pdf`
  printed page 289 / Theorem 4.3;
  printed pages 290-291 / `(5.2)` `(5.3)` `(5.4)`;
  printed pages 293-295 / Section V.2 `(AN)` `(PN)`, `(5.20)` `(5.21)`,
  Lemma 5.2;
  Lean declarations
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `forwardTube_boundaryValueData_of_polyGrowth`,
  `distributional_limit_of_equicontinuous`,
  `SchwartzMap.tempered_uniform_schwartz_bound`,
  `SchwartzMap.tempered_apply_tendsto_zero_of_tendsto`;
  mathlib declarations
  `schwartzSeminormFamily`,
  `ContinuousLinearMap.eventually_nhds_zero_mapsTo`,
  `ContinuousLinearMap.tendsto_iff_tendstoUniformlyOn`,
  `MontelSpace.isCompact_of_isClosed_of_isVonNBounded`;
- reading conclusion:
  the route now needs a bounded-set finite-net / precompactness theorem for the
  fixed controlling seminorm returned by Banach-Steinhaus;
- exact smallest abstract theorem statement now required:

  `Bornology.IsVonNBounded ℂ B ->
    ∀ εp > 0, ∃ t : Finset (SchwartzNPoint d (n + m)),
      ∀ h ∈ B, ∃ g ∈ t, p (h - g) < εp`

  for
  `p := s.sup (schwartzSeminormFamily ℂ (NPointDomain d (n + m)) ℂ)`,
  equivalently

  `Bornology.IsVonNBounded ℂ B ->
    TotallyBounded ((q_p) '' B)`;
- whether it is smaller than the shell theorem:
  no;
  it is merely the same bounded-set shell theorem in quotient/precompactness
  language, because finite `p`-nets immediately yield eventual `MapsTo`, then
  `TendstoUniformlyOn`, then strong convergence;
- exact specialization path:
  pointwise convergence of the shell family to packaged witness `T_t`
  +
  common finite `p`-control on `shell_ε - T_t`
  +
  finite `p`-ε-nets on bounded `B`
  =>
  eventual `MapsTo`
  =>
  `TendstoUniformlyOn`
  =>
  strong-topology convergence
  =>
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- witness decision:
  keep `T_t` existential at this seam;
  extracting it early is still wrapper drift only;
- source-backed versus genuinely new:
  source-backed:
  holomorphy,
  growth,
  witness existence,
  pointwise convergence,
  common finite seminorm control,
  and the abstract Montel / strong-topology APIs;
  genuinely new:
  the Schwartz-specific precompactness theorem for bounded sets and a fixed
  finite seminorm;
- first blocking proof obligation:
  prove the fixed-seminorm bounded-set total-boundedness theorem itself;
  neither repo nor mathlib currently instantiates Schwartz space as Montel or
  supplies the needed quotient/pseudometric consequence directly;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  no unsupported residue was found or removed.

Bounded theorem-3 reading note on the raw fixed-time shell package decomposition
(2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` remain clean; the second still contains
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact local declarations rechecked:
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `differentiableAt_bvt_F_restrictScalars`,
  `hasFDerivAt_bvt_F_canonicalXiShift`,
  `section43_iteratedSlice_descendedPairing`,
  `section43_fixedPair_mixedOrderSlice_descendedScalar_eq_directPsiIntegral_fixedTime`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  and `hlimit_os`;
- exact paper objects rechecked:
  the same OS II slots already pinned for this seam in the docs:
  printed pages 288-289 / Theorem 4.1-4.3;
  printed pages 290-295 / Section V, Section V.2, Lemma 5.2, `(AN)`, `(PN)`;
- source-first verdict:
  yes, the raw-family boundary-distribution package lowers one theorem-sized
  step smaller;
  the first smaller unit is just existence of a limiting ambient-shell
  functional `T_t`, before any quotient-kernel statement;
- exact weaker theorem shape:

  `∀ t : ℝ, 0 < t →
      ∃ T_t : SchwartzNPoint d (n + m) →L[ℂ] ℂ,
        Filter.Tendsto
          (fun ε : ℝ =>
            if hε : 0 < ε then
              section43_fixedTimeShellRawCLM (d := d) OS lgc hm t ε hε
            else
              0)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds T_t)`;

- exact local hypotheses genuinely required:
  `OS`, `lgc`, `{n m}`, `hm : 0 < m`, `t : ℝ`, `ht : 0 < t`;
- exact next downstream theorem shape:
  for such a limiting `T_t`, prove
  `section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0 -> T_t h = 0`;
  only after that does the route reach the outside-region pointwise coefficient
  corollary;
- exact reason this is the first honest smaller unit:
  `section43_fixedTimeShellRawCLM` already packages the raw family itself;
  the next missing fact is that the family has a limit in the ambient Schwartz
  dual;
  quotient-kernel annihilation and pointwise outside-region vanishing both need
  extra mathematics beyond that first topological limit step;
- exact insertion-surface placement:
  first after `section43_fixedTimeShellRawCLM`, then later the coefficient
  corollary after `hasFDerivAt_bvt_F_canonicalXiShift`;
- exact immediate downstream consumer chain:
  raw-shell CLM limit existence
  -> quotient-kernel annihilation / factorization
  -> full shell boundary-distribution package
  -> outside-region coefficient corollary
  -> product-level pointwise `hlim`
  -> `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> `hlimit_os`;
- unsupported-residue note:
  live source inspection now shows two `sorry`s in
  `OSToWightmanPositivity.lean`, at
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime` and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
  none were removed in this doc-only pass;
- no theorem/local lemma statement or skeleton landed compile-clean in this
  pass.

Bounded theorem-3 reading note on the live outside-region shell seam, checking
minimality of the coefficient-only theorem (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact paper objects inspected:
  `reconstruction theorem II.pdf`
  printed pages 288-289 / Theorem 4.1 `(4.4)` `(4.5)`, Theorem 4.2 `(4.6)`,
  Theorem 4.3;
  printed pages 293-295 / Section V.2, formulas `(5.20)` `(5.21)`, Lemma 5.2,
  and the `(AN)` `(PN)` continuation package;
- exact local declarations rechecked:
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `hasFDerivAt_bvt_F_canonicalXiShift`,
  `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  and `hlimit_os`;
- minimality verdict:
  the coefficient-only outside-region theorem is already the first genuinely new
  theorem-sized surface below the current live branch;
- exact minimal theorem shape:
  for every `y : NPointDomain d (n + m)` with
  `y ∉ section43PositiveEnergyRegion d (n + m)`, prove
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
            (t : ℂ)))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds 0)`;
- exact local hypotheses genuinely required:
  `OS`, `lgc`, `{n m}`, `hm : 0 < m`, `t : ℝ`, and the branch data `y`, `hy`;
- exact reason no smaller honest seam remains:
  the live dominated-convergence supplier still demands pointwise convergence of
  the shell integrand, and the existing region lemmas already dispose of every
  source-backed case where `y` lies inside `section43PositiveEnergyRegion`;
  after removing the `ε`-constant factor `h y`, the complement-side coefficient
  limit is the irreducible residue;
- exact insertion-surface location:
  the second live shell-local insertion point in
  `OSToWightmanPositivity.lean`, immediately after
  `hasFDerivAt_bvt_F_canonicalXiShift` and before
  `tendsto_bvt_F_canonical_conjTensorProduct_timeShift_boundaryValue`;
- exact immediate downstream consumer chain:
  coefficient-only complement-side pointwise `hlim`
  -> product-level complement-side pointwise `hlim`
  -> full pointwise `hlim` for
     `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> shell-integral limit `0`
  -> `hlimit_os`
  -> `tendsto_nhds_unique hlimit_w hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  continuation / support / region transport;
  genuinely new:
  actual-shell complement-side vanishing of the bare coefficient;
- no unsupported residue was found or removed;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 reading note on the live complement-side pointwise `hlim`
supplier seam, reduced to the bare coefficient question (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact paper objects inspected:
  `reconstruction theorem II.pdf`
  printed pages 288-289 / Theorem 4.1 `(4.4)` `(4.5)`, Theorem 4.2 `(4.6)`,
  Theorem 4.3;
  printed pages 291-295 / formulas `(5.2)` `(5.3)` `(5.4)`, Lemma 5.1, and
  the `(A0)` `(AN)` `(PN)` continuation package;
- exact local declarations rechecked:
  `section43PositiveEnergyRegion`,
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`,
  `section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `hasFDerivAt_bvt_F_canonicalXiShift`,
  `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  and `hlimit_os`;
- lowering verdict:
  yes, the pinned product-level supplier lowers one theorem-sized step to a
  coefficient-only outside-region limit theorem, since `h y` does not depend on
  `ε`;
- exact minimal weaker theorem shape at the live seam:
  for every `y : NPointDomain d (n + m)` with
  `y ∉ section43PositiveEnergyRegion d (n + m)`, prove
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
            (t : ℂ)))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds 0)`;
- exact local hypotheses genuinely required:
  `OS`, `lgc`, `{n m}`, `hm : 0 < m`, `t : ℝ`, and the branch data `y`, `hy`;
  the ambient test `h` and the surrounding kernel hypothesis `hker` only enter
  after this seam, when recovering the current product-level branch;
- exact insertion-surface location:
  the second live shell-local insertion point in
  `OSToWightmanPositivity.lean`, immediately after
  `hasFDerivAt_bvt_F_canonicalXiShift` and before
  `tendsto_bvt_F_canonical_conjTensorProduct_timeShift_boundaryValue`;
- exact immediate downstream consumer chain:
  coefficient-only complement-side pointwise `hlim`
  -> product-level complement-side pointwise `hlim`
  -> full pointwise `hlim` for
     `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> shell-integral limit `0`
  -> `hlimit_os`
  -> `tendsto_nhds_unique hlimit_w hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  positive-energy support / Fourier-Laplace reconstruction and region-local
  quotient transport only;
  genuinely new:
  actual-shell complement-side vanishing of the bare coefficient
  `ε ↦ bvt_F ... (xiShift ...)`;
- exact reason the weaker theorem is sufficient:
  multiplication by the constant scalar `h y` converts that coefficient limit
  directly into the currently demanded product-level supplier;
- no unsupported residue was found or removed;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 reading note on the live complement-side pointwise `hlim`
supplier seam, rechecked directly from source and the live shell consumer
(2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact paper objects inspected:
  `reconstruction theorem II.pdf`
  printed pages 288-289 / Theorem 4.1 `(4.4)` `(4.5)`, Theorem 4.2 `(4.6)`,
  Theorem 4.3;
  printed pages 291-295 / formulas `(5.2)` `(5.3)` `(5.4)`, Lemma 5.1, and
  the `(A0)` `(AN)` `(PN)` continuation package;
- exact local declarations rechecked:
  `section43PositiveEnergyRegion`,
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`,
  `section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `hasFDerivAt_bvt_F_canonicalXiShift`,
  `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  and `hlimit_os`;
- exact minimal theorem statement shape at the live seam:
  for every `y : NPointDomain d (n + m)` with
  `y ∉ section43PositiveEnergyRegion d (n + m)`, prove
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
            (t : ℂ)) *
        h y)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds 0)`;
- exact local hypotheses genuinely required:
  `OS`, `lgc`, `{n m}`, `hm : 0 < m`, `t : ℝ`,
  `h : SchwartzNPoint d (n + m)`, and the branch data `y`, `hy`;
  the surrounding `hlimit_os` proof also carries
  `hker : section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0`, but that
  only kills the inside-region branch;
- exact insertion-surface location:
  the second live shell-local insertion point in
  `OSToWightmanPositivity.lean`, immediately after
  `hasFDerivAt_bvt_F_canonicalXiShift` and before
  `tendsto_bvt_F_canonical_conjTensorProduct_timeShift_boundaryValue`;
- exact immediate downstream consumer chain:
  complement-side pointwise `hlim`
  -> full pointwise `hlim` for
     `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> shell-integral limit `0`
  -> `hlimit_os`
  -> `tendsto_nhds_unique hlimit_w hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  positive-energy support / Fourier-Laplace reconstruction and region-local
  quotient transport only;
  genuinely new:
  actual-shell complement-side vanishing of
  `ε ↦ bvt_F ... (xiShift ...) * h y`;
- no unsupported residue was found or removed;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 reading note on the live complement-side pointwise `hlim`
supplier seam (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact paper objects inspected:
  `reconstruction theorem II.pdf`
  printed pages 288-289 / Theorem 4.1 `(4.4)` `(4.5)`, Theorem 4.2 `(4.6)`,
  Theorem 4.3;
  printed pages 291-292 / formulas `(5.2)` `(5.3)` `(5.4)`;
  printed page 292 / Lemma 5.1;
- exact local declarations rechecked:
  `section43PositiveEnergyRegion`,
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`,
  `section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `hasFDerivAt_bvt_F_canonicalXiShift`,
  `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`,
  and `hlimit_os`;
- exact minimal theorem statement shape at the live seam:
  for every `y : NPointDomain d (n + m)` with
  `y ∉ section43PositiveEnergyRegion d (n + m)`, prove
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
            (t : ℂ)) *
        h y)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds 0)`;
- exact local hypotheses genuinely required:
  `OS`, `lgc`, `{n m}`, `hm : 0 < m`, `t : ℝ`,
  `h : SchwartzNPoint d (n + m)`, and the branch data `y`, `hy`;
  the surrounding `hlimit_os` proof also carries
  `hker : section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0`, but that
  only kills the inside-region branch;
- exact insertion-surface location:
  the second live shell-local insertion point in
  `OSToWightmanPositivity.lean`, immediately after
  `hasFDerivAt_bvt_F_canonicalXiShift` and before
  `tendsto_bvt_F_canonical_conjTensorProduct_timeShift_boundaryValue`;
- exact immediate downstream consumer chain:
  complement-side pointwise `hlim`
  -> full pointwise `hlim` for
     `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> shell-integral limit `0`
  -> `hlimit_os`
  -> `tendsto_nhds_unique hlimit_w hlimit_os`;
- source-backed versus genuinely new:
  source-backed:
  positive-energy support / Fourier-Laplace reconstruction and region-local
  quotient transport only;
  genuinely new:
  actual-shell complement-side vanishing of
  `ε ↦ bvt_F ... (xiShift ...) * h y`;
- no unsupported residue was found or removed;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 source/doc reading note on the live actual-shell route (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `differentiableAt_bvt_F_restrictScalars`, and
  `hasFDerivAt_bvt_F_canonicalXiShift`;
- exact paper objects inspected in `reconstruction theorem II.pdf`:
  PDF pages 13-15 / printed pages 288-294:
  Theorem 4.1 `(4.4)` `(4.5)`, Theorem 4.2 `(4.6)`, Theorem 4.3,
  formulas `(5.2)` `(5.3)` `(5.4)`, and Lemma 5.1;
- exact local declarations rechecked:
  `section43PositiveEnergyRegion`,
  `section43PositiveEnergyQuotientMap_eq_of_eqOn_region`,
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`,
  `section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region`,
  `section43PositiveEnergyQuotientMap_conjTensorProduct_eq_of_repr_eq_transport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_section43Region`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_source_tsupport`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `hasFDerivAt_bvt_F_canonicalXiShift`,
  and `hlimit_os`;
- decomposition verdict:
  the current minimal complement-side pointwise `hlim` supplier does not split
  into one smaller honest source-backed theorem/local lemma on the live route;
- strongest honest weaker source-backed shape:
  OS II Theorem 4.3 plus the current local source support only region-local
  positive-energy quotient control and fixed-time slice transport on
  `section43PositiveEnergyRegion d (n + m)`;
- insertion-surface verdict:
  not insertion-surface-ready; it is still too weak because it gives no
  complement-side pointwise limit theorem for the canonical shell coefficient;
- why the supplier is already the first genuinely new mathematics here:
  the missing dominated-convergence branch is the true complement
  `y ∉ section43PositiveEnergyRegion d (n + m)`, while quotient-zero says
  nothing about `h y` there, and the inspected OS II theorems do not force the
  actual-shell coefficient to vanish on that complement;
- no unsupported residue was found or removed;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 insertion-surface source note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `differentiableAt_bvt_F_restrictScalars`, and
  `hasFDerivAt_bvt_F_canonicalXiShift`;
- exact paper objects inspected in `reconstruction theorem II.pdf`:
  Theorem 4.1 `(4.4)` `(4.5)` and Theorem 4.2 `(4.6)` on printed page 288,
  Theorem 4.3 on printed page 289,
  and Chapter V formulas `(5.2)` `(5.3)` `(5.4)` plus Lemma 5.1 on printed
  pages 291-294;
- exact local declarations rechecked:
  `section43PositiveEnergyRegion`,
  `section43PositiveEnergyQuotientMap_eq_of_eqOn_region`,
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`,
  `section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region`,
  `section43PositiveEnergyQuotientMap_conjTensorProduct_eq_of_repr_eq_transport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_section43Region`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_source_tsupport`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `hasFDerivAt_bvt_F_canonicalXiShift`,
  and `hlimit_os`;
- strongest honest weaker source-backed shape:
  OS II Theorem 4.3 plus the current local source only support region-local
  positive-energy quotient control and fixed-time slice transport on
  `section43PositiveEnergyRegion d (n + m)`;
- insertion-surface verdict:
  not insertion-surface-ready; it is still too weak because it does not give
  complement-side boundary-value vanishing or even a complement-side pointwise
  limit theorem for the canonical shell coefficient;
- why it still fails under `hlimit_os`:
  the missing dominated-convergence branch is the true complement
  `y ∉ section43PositiveEnergyRegion d (n + m)`, while quotient-zero only says
  anything on the region. So neither the paper support theorem nor the local
  quotient/slice transport package supplies the complement-side pointwise
  `hlim` needed there;
- no unsupported residue was found or removed;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 source-backed coefficient-complement re-audit note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `differentiableAt_bvt_F_restrictScalars`, and
  `hasFDerivAt_bvt_F_canonicalXiShift`;
- exact paper objects inspected in `reconstruction theorem II.pdf`:
  Theorem 4.1 `(4.4)` `(4.5)` and Theorem 4.2 `(4.6)` on printed page 288,
  Theorem 4.3 on printed page 289,
  and Chapter V formulas `(5.2)` `(5.3)` `(5.4)` plus Lemma 5.1 on printed
  pages 291-294;
- exact local declarations rechecked:
  `section43PositiveEnergyRegion`,
  `section43PositiveEnergyQuotientMap_eq_of_eqOn_region`,
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`,
  `section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region`,
  `section43PositiveEnergyQuotientMap_conjTensorProduct_eq_of_repr_eq_transport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_section43Region`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_source_tsupport`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `differentiableAt_bvt_F_restrictScalars`,
  `hasFDerivAt_bvt_F_canonicalXiShift`,
  and `hlimit_os`;
- source-first verdict:
  the complement-vanishing theorem itself is not source-backed;
- strongest honest weaker source-backed shape:
  OS II Theorem 4.3 gives only positive-energy support of `W_k`, and the local
  faithful Lean shadow is only region-local quotient/equality control on
  `section43PositiveEnergyRegion d (n + m)`;
- exact negative conclusion from the rest of the inspected paper source:
  Theorem 4.1, Theorem 4.2, formulas `(5.2)` `(5.3)` `(5.4)`, and Lemma 5.1
  give analyticity, growth, semigroup continuation, and local radius control,
  but no complement-shell boundary vanishing theorem for
  `ε ↦ bvt_F OS lgc (n + m) (xiShift ... ε ... (t : ℂ))`;
- why that still fails on the live shell route:
  the current missing branch is the true complement
  `y ∉ section43PositiveEnergyRegion d (n + m)`, while quotient-zero only says
  anything on the region. So neither the paper support theorem nor the local
  quotient transport package supplies the complement-side pointwise `hlim`
  needed under `hlimit_os`;
- no unsupported residue was found or removed;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 OS-II/source audit note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact paper objects inspected in `reconstruction theorem II.pdf`:
  Theorem 4.1 on page 288, Theorem 4.2 and Theorem 4.3 on page 289, and
  Chapter V formulas `(5.2)` `(5.3)` `(5.4)` plus Lemma 5.1 on pages 291-293;
- exact local declarations rechecked:
  `section43PositiveEnergyRegion`,
  `section43PositiveEnergyQuotientMap_eq_of_eqOn_region`,
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`,
  `section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region`,
  `section43PositiveEnergyQuotientMap_conjTensorProduct_eq_of_repr_eq_transport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_section43Region`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_source_tsupport`,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  and `hlimit_os`;
- source-first verdict:
  the complement-vanishing theorem itself is not source-backed;
- strongest honest weaker source-backed shape:
  OS II Theorem 4.3 gives only positive-energy support of `W_k`, and the local
  faithful Lean surface is only region-local quotient/equality control on
  `section43PositiveEnergyRegion d (n + m)`;
- why that still fails on the live shell route:
  the current missing branch is the true complement
  `y ∉ section43PositiveEnergyRegion d (n + m)`, while quotient-zero only says
  anything on the region. So neither the paper support theorem nor the local
  quotient transport package supplies the complement-side pointwise `hlim`
  needed under `hlimit_os`;
- no unsupported residue was found or removed;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 coefficient-complement insertion-surface note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- source-first verdict:
  the first theorem-sized package above the current docs-only frontier is the
  coefficient-side complement boundary-vanishing theorem for the live
  canonical-shell coefficient;
- exact statement shape:
  for every `y : NPointDomain d (n + m)` with
  `y ∉ section43PositiveEnergyRegion d (n + m)`, prove
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds 0)`;
- exact insertion surface:
  `OSToWightmanPositivity.lean`, second live shell-local insertion point,
  immediately after `hasFDerivAt_bvt_F_canonicalXiShift`;
- exact downstream consumer chain:
  coefficient-side complement vanishing
  -> kernel complement-side `hlim`
  -> complement-sensitive `hbound`
  -> `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`
  -> limit-level kernel annihilation
  -> specialization to the actual tensor difference
  -> `hlimit_os`;
- exact weaker-statement insufficiency:
  any theorem confined to the Section-4.3 region, to source support, or to
  quotient transport remains too weak because the uncontrolled branch is the
  true complement, and kernel-zero gives no equation for `h y` there;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 complement-package-above-supplier note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- the exact local source objects rechecked were:
  both live insertion-point theorem clusters,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-pair region transport/tensor-equality theorems, and the
  Section-4.3 quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  the minimal exact package above the exposed complement-side pointwise `hlim`
  supplier is coefficient-side complement vanishing of the canonical-shell
  boundary value itself;
- exact statement shape:
  for `y ∉ section43PositiveEnergyRegion d (n + m)`, prove
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds 0)`;
- exact side classification: coefficient-side;
- exact source reason this is the smallest honest package above the supplier:
  the supplier is quantified over arbitrary kernel elements `h`, but the
  quotient/source toolkit only forces `h = 0` on the region, not on the
  complement. So source-side transport cannot produce the complement supplier.
  Coefficient-side vanishing would, because `h y` is then just a fixed scalar
  multiplier;
- exact source reason it still is not proved by current local toolkit:
  region equality does not constrain complement values, and the current shell
  package has no theorem giving zero boundary value of `bvt_F` on those
  complement shell points;
- exact next package order:
  1. coefficient-side complement pointwise coefficient vanishing;
  2. kernel complement-side pointwise `hlim`;
  3. complement-sensitive `hbound`;
  4. limit-level canonical-shell kernel annihilation;
  5. specialize to
     `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`;
  6. discharge `hlimit_os`;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 coefficient-package recheck note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- the exact local source objects rechecked were:
  both live insertion-point theorem clusters,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-pair region transport/tensor-equality theorems, and the
  Section-4.3 quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  the minimal exact package above the exposed complement-side supplier is still
  the coefficient-side complement vanishing theorem for the canonical-shell
  boundary value itself;
- exact side classification: coefficient-side;
- exact source reason this package is the smallest honest one:
  the supplier below it must hold for arbitrary kernel `h`, but the quotient
  toolkit only forces `h` to vanish on
  `section43PositiveEnergyRegion d (n + m)`, not on the true complement. So
  only coefficient-side vanishing of the shell coefficient can imply that
  supplier uniformly;
- exact source reason it is still unsupported:
  the current shell toolkit has no theorem identifying a complement-side real
  boundary value of `bvt_F` with `0`, and the Section-4.3 quotient package is
  purely region-local;
- exact next package order:
  1. coefficient-side complement pointwise coefficient vanishing;
  2. kernel complement-side pointwise `hlim`;
  3. complement-sensitive `hbound`;
  4. limit-level canonical-shell kernel annihilation;
  5. specialize to
     `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`;
  6. discharge `hlimit_os`;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 actual-shell sub-complement-`hlim` note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- the exact local source objects rechecked were:
  both live insertion-point theorem clusters,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-pair region transport/tensor-equality theorems, and the
  Section-4.3 quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  no honest new theorem below the complement-side pointwise `hlim` supplier is
  currently supported by live source on the actual shell route;
- exact smallest shell-side package is therefore still that complement-side
  pointwise `hlim` supplier itself for kernel elements;
- exact input category:
  shell-level dominated-convergence input, not a new source-side quotient
  theorem and not an analytic-continuation comparison theorem;
- exact source reason:
  the kernel hypothesis already kills the region branch through quotient-zero,
  so the first uncontrolled branch is still the true complement
  `y ∉ section43PositiveEnergyRegion d (n + m)`, and there is still no local
  theorem controlling the live shell coefficient there;
- exact next package order:
  1. kernel complement-side pointwise `hlim`;
  2. complement-sensitive `hbound`;
  3. limit-level canonical-shell kernel annihilation;
  4. specialize to
     `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`;
  5. discharge `hlimit_os`;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 actual-shell kernel-complement-`hlim` note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- the exact local source objects rechecked were:
  both live insertion-point theorem clusters,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-pair region transport/tensor-equality theorems, and the
  Section-4.3 quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  strictly beneath the limit-level kernel-annihilation theorem, the smallest
  shell-side package is the complement-side pointwise `hlim` supplier for
  kernel elements;
- exact statement shape:
  if `h : SchwartzNPoint d (n + m)` satisfies
  `section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0`, then for every
  `y ∉ section43PositiveEnergyRegion d (n + m)` the pointwise shell integrand
  `ε ↦ bvt_F ... (xiShift ... ε ...) * h y`
  tends to `0` as `ε → 0+`;
- exact dominated-convergence input targeted: `hlim`;
- exact source reason this is smaller and more honest than the previously
  discussed options:
  the kernel hypothesis already kills `h` on the region, so the region-side
  `hlim` branch is trivial; the first live shell-side branch not already
  handled is the true complement;
- exact source reason it still is not proved by current local toolkit:
  region equality does not constrain complement values, and no current theorem
  makes the canonical shell coefficient vanish or limit to zero on the
  complement for a kernel element;
- exact next package order:
  1. kernel complement-side pointwise `hlim`;
  2. complement-sensitive `hbound`;
  3. limit-level canonical-shell kernel annihilation;
  4. specialize to
     `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`;
  5. discharge the ambient shell-comparison limit / `hlimit_os`;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 actual-shell kernel-annihilation note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- the exact local source objects rechecked were:
  both live insertion-point theorem clusters,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-pair region transport/tensor-equality theorems, and the
  Section-4.3 quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  the minimal honest next package beneath the ambient fixed-time shell-
  comparison limit is the limit-level canonical-shell quotient-kernel
  annihilation theorem;
- exact statement shape:
  if `h : SchwartzNPoint d (n + m)` satisfies
  `section43PositiveEnergyQuotientMap (d := d) (n + m) h = 0`, then the raw
  shell integral
  `ε ↦ section43_fixedTimeShellRawCLM OS lgc hm t ε hε h`
  tends to `0` as `ε → 0+`;
- exact source reason this is smaller and more honest than the previously
  discussed options:
  the live proof only needs limit annihilation on the Section-4.3 kernel, not
  fixed-`ε` equality of raw shell values and not a global complement-vanishing
  statement; the current transport package already provides kernel membership
  for the actual tensor difference, so this statement isolates exactly the
  shell-side missing mathematics;
- exact source reason it still is not proved by current local toolkit:
  region equality does not make the raw shell descend, and no current theorem
  controls the true complement branch
  `y ∉ section43PositiveEnergyRegion d (n + m)` enough to supply dominated-
  convergence hypotheses for a kernel element;
- exact next package order:
  1. limit-level canonical-shell kernel annihilation;
  2. specialize to
     `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`;
  3. discharge the ambient shell-comparison limit / `hlimit_os`;
  4. only then attempt any later direct-`psiZ` source-shell comparison;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 actual-shell minimal-contract note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- the exact local source objects rechecked were:
  both live insertion-point theorem clusters,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-pair region transport/tensor-equality theorems, and the
  Section-4.3 quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  the bare complement-side pointwise supplier remains the first explicit
  unsupported hypothesis under dominated convergence, but it is not the right
  next theorem surface to record;
- exact corrected theorem-sized frontier:
  the minimal honest next theorem is the ambient fixed-time shell-comparison
  limit for the actual shell difference, not a standalone wrapper around one
  `hlim` branch;
- exact source reason:
  the current quotient/support package only controls the source-support branch
  and the already-in-region outside-source branch. Since the raw shell
  functional still integrates over all `y`, region equality alone does not
  descend it, and no current theorem localizes or null-limits the true
  complement branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- exact next package order:
  1. ambient shell-comparison / complement-localization on the actual shell;
  2. discharge `hlimit_os`;
  3. only then any later direct-`psiZ` source-shell comparison;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.

Bounded theorem-3 actual-shell complement-supplier theorem-sized note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- the exact local source objects rechecked were:
  both live insertion-point theorem clusters,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-pair region transport/tensor-equality theorems, and the
  Section-4.3 quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  the complement-side pointwise supplier itself does not yet follow as one
  honest theorem/local lemma from current source;
- exact post-pass frontier:
  that complement-side pointwise supplier is now confirmed as the first
  theorem-sized new-math contract on the branch;
- exact source reason:
  the existing Section-4.3 quotient/support package only controls the
  source-support branch and the already-in-region outside-source branch; it has
  no theorem at all for the true complement branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`, so there is still no
  complement-side pointwise limit-to-zero supplier for the actual shell
  integrand;
- `hbound` is still open afterward, because no complement-sensitive ambient
  domination independent of `ε` is currently available either.

Bounded theorem-3 actual-shell complement-branch source note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- the exact local source objects rechecked were:
  both live insertion-point theorem clusters,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-pair region transport/tensor-equality theorems, and the
  Section-4.3 quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  no new honest theorem below the complement-side pointwise `hlim` branch is
  currently supported by live source for the actual shell difference;
- exact post-pass frontier:
  the first remaining honest theorem-sized contract is still the complement-
  side pointwise limit-to-zero supplier itself on
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- no equivalent still-smaller explicit hypothesis beneath that supplier was
  found in the current source/toolkit;
- `hbound` is still open afterward, because no complement-sensitive ambient
  domination independent of `ε` is currently available either.

Bounded theorem-3 actual-shell complement-`hlim` supplier note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- the exact local source objects rechecked were:
  both live insertion-point theorem clusters,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-pair region transport/tensor-equality theorems, and the
  Section-4.3 quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  no new honest theorem below the complement-side pointwise `hlim` branch is
  currently supported by live source for the actual shell difference;
- exact post-pass frontier:
  the first remaining honest theorem-sized contract is now the complement-side
  pointwise limit-to-zero supplier itself on
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- no equivalent still-smaller explicit hypothesis beneath that supplier was
  found in the current source/toolkit;
- `hbound` is still open afterward, because no complement-sensitive ambient
  domination independent of `ε` is currently available either.

Bounded theorem-3 actual-shell hypothesis-supplier note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- the exact local source objects rechecked were:
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-pair region transport/tensor-equality theorems, and the
  Section-4.3 quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  no new honest theorem below the already-landed dominated-convergence theorem
  is currently supported by live source for the actual shell difference;
- exact post-landing contract:
  the remaining obligations under `hlimit_os` are still the explicit
  hypotheses `hbound` and `hlim` for the shell integrand against
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`;
- sharper first unsupported item:
  the first missing branch is now a smaller explicit hypothesis beneath
  `hlim`, namely pointwise limit-to-zero on the true complement branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- `hbound` is still open afterward, because no complement-sensitive ambient
  domination independent of `ε` is currently available either.

Bounded theorem-3 actual-shell dominated-convergence note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM`;
- the exact local source objects rechecked were:
  `section43_fixedTimeShellRawCLM`,
  its unfolded coefficient `coeff`,
  the live shell parameters `xiShift`, `t`, and `ε`,
  the live shell difference
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-time region transport theorems, and the Section-4.3 quotient
  codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  the missing limit beneath `hlimit_os` already has an honest ambient theorem
  surface in source, namely
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact analytic contract now exposed is therefore the need to prove its two
  hypotheses for the actual test difference:
  an ambient integrable domination `hbound` uniform in `ε` near `0`, and a
  pointwise limit-to-zero statement `hlim`, both for the actual shell
  integrand
  `bvt_F OS lgc (n + m) (xiShift ... (t : ℂ)) *
    (((φ.conjTensorProduct ψ) - (f.conjTensorProduct g)) y)`;
- current Section-4.3 transport remains insufficient because it only kills the
  integrand on source support and on already-in-region outside-source points,
  while the outside-region branch still has no source-backed localization or
  domination.

Bounded theorem-3 `hlimit_os` note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM`;
- the exact local source objects rechecked were:
  `section43_fixedTimeShellRawCLM`,
  its unfolded coefficient `coeff`,
  the live shell parameters `xiShift`, `t`, and `ε`,
  the live shell difference
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-time region transport theorems, and the Section-4.3 quotient
  codomain theorems from `Section43Codomain.lean`;
- source-first verdict after re-unfolding the actual fixed-time shell:
  the missing object is still the ambient shell limit against the live test
  difference, with the failure now sharpened by the actual shell-domain split;
- exact analytic contract now exposed:

  `Filter.Tendsto
    (fun ε : ℝ =>
      section43_fixedTimeShellRawCLM OS lgc hm t ε hε
        (((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds 0))`;

- exact shell split now visible in source:
  1. source support is controlled;
  2. already-in-region outside-source points are controlled;
  3. outside-region points are not controlled at all;
- therefore any honest reduction below that seam still needs ambient, not
  merely region-local, control of the complement branch: either localization of
  the actual shell coefficient there, or an ambient dominated-convergence
  theorem for the actual shell integrand with domination uniform in `ε`.

Bounded theorem-3 coefficient-contract note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM`;
- the exact local source objects rechecked were:
  `section43_fixedTimeShellRawCLM`,
  its unfolded coefficient `coeff`,
  the live shell parameters `xiShift`, `t`, and `ε`,
  the live shell difference
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the current fixed-time region transport theorems, and the Section-4.3
  quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict after re-unfolding the actual fixed-time shell:
  the missing object is still the ambient shell limit against the live test
  difference, not a smaller quotient-side wrapper;
- exact analytic contract now exposed:

  `Filter.Tendsto
    (fun ε : ℝ =>
      section43_fixedTimeShellRawCLM OS lgc hm t ε hε
        (((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds 0))`;

- any honest reduction below that seam would still need ambient, not merely
  region-local, control: either localization of the actual shell coefficient
  off the true complement branch, or an ambient dominated-convergence theorem
  for the actual shell integrand with domination uniform in `ε`;
- current Section-4.3 transport remains insufficient because it only sees
  equality on `section43PositiveEnergyRegion d (n + m)`, while the live shell
  functional still integrates over all `y`.

Bounded theorem-3 actual-shell ambient-contract note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM`;
- the exact local source objects rechecked were:
  `section43_fixedTimeShellRawCLM`,
  its unfolded coefficient `coeff`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_source_tsupport`,
  `section43PositiveEnergyVanishingSubmodule`,
  `section43PositiveEnergyQuotientMap`,
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`, and
  `section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region`;
- source-first verdict after re-unfolding the actual fixed-time shell:
  the missing object is still the ambient limit of the shell integral against
  `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`;
- exact analytic contract now exposed:

  `Filter.Tendsto
    (fun ε : ℝ =>
      section43_fixedTimeShellRawCLM OS lgc hm t ε hε
        (((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds 0))`;

- any honest reduction below that seam would need ambient, not merely region-
  local, control: either the actual coefficient must localize off the true
  complement branch, or one must have an ambient dominated-convergence theorem
  for the actual shell integrand with domination uniform in `ε`;
- current Section-4.3 transport remains insufficient because it only sees
  equality on `section43PositiveEnergyRegion d (n + m)`, while the live shell
  functional still integrates over all `y`.

Bounded theorem-3 actual-shell live-source seam note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM`;
- the exact local source objects rechecked were:
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  `section43_fixedTimeShellRawCLM`,
  its unfolded coefficient `coeff`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_source_tsupport`,
  `section43PositiveEnergyVanishingSubmodule`,
  `section43PositiveEnergyQuotientMap`,
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`, and
  `section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region`;
- source-first verdict after re-unfolding the actual shell functional:
  `section43_fixedTimeShellRawCLM` is an ambient CLM
  `h ↦ ∫ y, coeff y * h y`, so equality only on
  `section43PositiveEnergyRegion d (n + m)` does not determine its value;
- therefore region-local shell/slice transport remains insufficient, and the
  exact first missing honest theorem-sized item is still the direct raw-CLM
  comparison limit for the actual shell difference;
- all smaller candidate formulations reduce to the same obstruction because
  they still need complement-sensitive control of the outside-region branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`.

Bounded theorem-3 actual-shell OS-paper seam note (2026-04-14):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM`;
- the exact local source objects rechecked were:
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_source_tsupport`,
  `section43PositiveEnergyVanishingSubmodule`,
  `section43PositiveEnergyQuotientMap`,
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`, and
  `section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region`;
- the exact paper sections/pages checked against that seam were:
  OS I Section 4.1 `(4.10)`-`(4.11)` on pp. 92-93,
  OS I Lemmas `8.5`-`8.8` on pp. 108-110,
  OS II Theorems `4.1`-`4.3` on pp. 288-289,
  OS II Section V with `(5.2)`-`(5.4)` on pp. 290-291,
  OS II Section V.1 on pp. 291-294,
  and OS II Section VI.1 on pp. 297-300;
- source-first verdict after that paper check:
  the papers stay at semigroup matrix elements, iterated one-variable
  continuation, Fourier-Laplace support, and temperedness estimates;
  they do not supply a theorem descending the actual ambient fixed-time shell
  functional over all `y` from equality only on
  `section43PositiveEnergyRegion d (n + m)`;
- therefore the first missing honest theorem-sized item is still the direct
  raw-CLM comparison limit for the actual shell difference, and that contract
  remains beyond the currently extracted paper/local package.

Bounded theorem-3 actual-shell recheck note (2026-04-14):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM`;
- the exact source objects rechecked were:
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  `section43_fixedTimeShellRawCLM`,
  `section43_fixedPair_canonicalShell_sliceRealization_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_canonicalSlice_eq_of_repr_eq_fixedTime_on_section43PositiveEnergyRegion`,
  `section43_fixedPair_conjTensorProduct_eq_zero_of_repr_eq_on_section43Region_outside_source_tsupport`,
  `section43_fixedPair_conjTensorProduct_eq_of_repr_eq_on_source_tsupport`,
  `section43PositiveEnergyVanishingSubmodule`,
  `section43PositiveEnergyQuotientMap`,
  `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`, and
  `section43PositiveEnergyQuotientMap_sub_eq_zero_of_eqOn_region`;
- source-first verdict stayed unchanged:
  region-local shell/slice realization and quotient equality do not control
  the true complement branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`, while
  `section43_fixedTimeShellRawCLM` still integrates an ambient coefficient
  over all `y`;
- therefore the first missing honest theorem-sized item is still the direct
  raw-CLM comparison limit for the actual shell difference, not a smaller
  already-landed complement-sensitive theorem.

# OS Reconstruction Reading Notes

These notes summarize the parts of Osterwalder-Schrader I and II that are
actually relevant to the current Lean development, with emphasis on the
`E -> R` direction and the current blocker surface.

Primary local references:

- `references/Reconstruction theorem I.pdf`
- `references/reconstruction theorem II.pdf`

This note is intentionally theorem-focused. It is not a full paper summary.

## 1. High-level picture

The OS reconstruction papers do not proceed by solving the two-point case and
then inferring all `k`-point functions by a formal induction on `k`.

Instead, the core analytic mechanism is:

1. pass to difference-variable Schwinger functions,
2. construct a Hilbert space and a positive self-adjoint semigroup from OS
   positivity,
3. continue in one time variable at a time using semigroup matrix elements,
4. treat all remaining variables as parameters,
5. then iterate this one-variable continuation mechanism.

That is the key conceptual bridge from the current `k = 2` work to the general
base-step theorem.

## 1.1. Paper notation dictionary

The papers use several notation layers that are easy to blur together. The
following dictionary is the one we actually need in Lean work.

- `𝒮_n`
  Euclidean `n`-point Green's functions in the original point variables
  `(x₁, ..., x_n)`.

- `S_n`
  difference-variable Euclidean Green's functions. These are obtained from
  translation invariance by passing from point variables to successive
  differences. In current Lean language, this is the natural world of
  admissible time-ordered / difference-variable shells.

- `W_n`
  difference-variable Wightman distributions, obtained after Fourier-Laplace
  continuation and support control.

- `Ψ_n(x, ξ)`
  Hilbert-space-valued distributions built from the OS form. These are the
  bridge between Schwinger functions and the semigroup.

- `T_t = e^{-tH}`
  the self-adjoint contraction semigroup on the OS Hilbert space.

- `T_τ`
  the holomorphic extension of the semigroup for `Re τ > 0`.

- `S^(m)(t,s | h_m)`
  the key parameterized one-gap continuation object in OS I. The point is:
  the variable being analytically continued is isolated, while all other
  variables are packaged into the parameter `h_m`.

- `C_+^k`
  product right half-plane in the time variables. OS II emphasizes that this
  full domain is reached only after an inductive continuation procedure, not
  from a naive one-shot argument.

## 1.2. Growth assumptions in OS II

OS II distinguishes three levels of distribution/growth control, and this
distinction matters for how the proof is organized.

- `E0`
  the original temperedness assumption from OS I. This is enough to build the
  semigroup and to obtain one-variable analytic continuation.

- `E0'`
  the linear-growth condition. Roughly, the Euclidean Green's functions are not
  merely tempered distributions, but their order is controlled linearly in the
  number of variables by seminorms of the form `|f|_{ns}` up to a factorially
  growing sequence.

- `E0"`
  a stronger pointwise/distributional growth condition. OS II remarks several
  times that if one were willing to assume `E0"` instead of `E0'`, the later
  temperedness arguments would become much shorter.

The important strategic point is:

- OS II does **not** use `E0'` to produce the analytic continuation itself;
- it uses `E0'` later to prove the polynomial growth / temperedness estimates
  needed for boundary values.

So there is a conceptual split:

- Chapter V:
  continuation, using `E0`, `E1`, `E2`;
- Chapter VI:
  temperedness estimates, using `E0'`.

This is exactly the right mental model for our file split:

- `OSToWightmanSemigroup.lean` and the core continuation side are about the
  analogue of Chapter V;
- `OSToWightmanBoundaryValues.lean` and later growth control are about the
  analogue of Chapter VI.

## 2. OS I: the original `E -> R` mechanism

In OS I, the `E -> R` proof is described in Section 4.

The essential steps are:

1. Construct the pre-Hilbert space from the OS form.
2. Build a one-parameter semigroup `T_t = e^{-tH}` of self-adjoint
   contractions.
3. Extend it to a holomorphic semigroup `T_τ` for `Re τ >= 0`.
4. Use matrix elements of `T_τ` to analytically continue Schwinger functions.
5. Show the continued functions are Fourier-Laplace transforms of
   distributions with the correct support.

This is the origin of the current Lean split:

- `WickRotation/OSToWightmanSemigroup.lean`
- `WickRotation/OSToWightman.lean`
- `WickRotation/OSToWightmanBoundaryValues.lean`

### 2.1. Difference variables come first

OS I does not construct Wightman distributions directly from the raw
point-variable Schwinger functions. The first step is to pass to
difference-variable Schwinger functions `S_n`; see their `(4.1)`.

This matters for us because many of the current Lean difficulties are exactly
about representing the correct difference-variable shell, not about the raw
point-variable objects.

In project terms:

- the current center/difference infrastructure is not accidental extra
  scaffolding;
- it is the Lean reflection of the paper’s decision to do the analytic work in
  difference variables.

### 2.2. The OS Hilbert space and semigroup

The core Hilbert-space construction in OS I is organized around:

- the OS sesquilinear form `(4.3)`,
- the quotient / completion `(4.4)`,
- spatial translation operators `(4.5)`,
- the time-translation semigroup `(4.6)`,
- and the bounds `(4.7)`-`(4.9)` showing this gives a positive symmetric
  contraction semigroup.

The important conceptual point is:

- positivity gives the Hilbert space,
- Euclidean invariance gives the semigroup,
- and the semigroup is the real source of analytic continuation.

This is exactly why `OSToWightmanSemigroup.lean` is the right upstream file for
the whole `E -> R` lane.

### 2.3. One-variable continuation via semigroup matrix elements

OS I then uses matrix elements of the holomorphic semigroup to continue one
time variable. The crucial formulas are `(4.10)` and `(4.11)`.

The structure is:

1. take two positive-time test families `f_m`, `g_n`,
2. form the matrix element
   `⟨ v(f_m), T_{t+is} v(g_n) ⟩`,
3. identify it with a distributional continuation of a Schwinger function,
4. then repackage the remaining variables into the parameter `h_m`.

This is the exact ancestor of the semigroup matrix-element theorems in our
current `OSToWightman*` files.

### The key OS I formula

OS I writes the continuation in one chosen time variable as a semigroup matrix
element. In the text around formula `(4.11)`, they then package the remaining
variables into a parameter `h_m` and define a distribution

- `S^(m)(t, s | h_m)`

for `t > 0`.

For fixed `h_m`, this object:

- is a distribution in the time variables,
- satisfies the Cauchy-Riemann equations,
- and hence is the Fourier-Laplace transform of a distribution in the dual
  cone variable.

This is the part of OS I that most closely matches the current Lean target.

The strongest practical reading of this for our code is:

- the correct target is not just “some holomorphic continuation”;
- it is a continuation produced from a semigroup matrix element after the other
  variables have been packaged as parameters.

That is why our present `k = 2` work is converging toward a factorization
statement rather than yet another shell-specific identity.

### 2.4. The technical lemmas actually used in OS I

The semigroup-to-Fourier-Laplace chain in OS I is mediated by the technical
lemmas in Section 8, and these are worth keeping in mind because they explain
what the proof is *really* using.

- Lemma 8.5:
  a distribution in `(t, s)` satisfying the Cauchy-Riemann equations on
  `t > 0` comes from a holomorphic function `G(τ)` on `Re τ > 0`.

- Lemma 8.6:
  a holomorphic function on `Re τ > 0` with a polynomial bound of the form
  `|G(τ)| ≤ M (1 + |τ|^α) / (Re τ)^β`
  is the Fourier-Laplace transform of a distribution supported in `[0, ∞)`.

- Lemma 8.7:
  combines the previous two statements: a CR distribution on the half-plane is
  already the Fourier-Laplace transform of some positive-support distribution.

- Lemma 8.8:
  this is the problematic multi-variable extension step in OS I. It tries to
  deduce the full many-variable Fourier-Laplace structure from separate
  one-variable statements.

This makes the OS I proof skeleton much more concrete:

1. construct a semigroup matrix element,
2. verify CR equations in one chosen time variable,
3. invoke the one-variable Fourier-Laplace theorem,
4. try to bootstrap to many variables.

The first three steps are robust. The fourth is where OS I overreached.

### 2.5. What exactly went wrong in OS I

The issue is not with the semigroup matrix element itself, nor with the
one-variable holomorphic extension. The issue is that OS I tried to infer the
existence of a joint continuation on the full product half-plane from separate
continuations in each variable.

So when reading OS I operationally, the safe takeaway is:

- one-gap continuation:
  trustworthy;
- joint many-gap continuation from that alone:
  not trustworthy without the extra OS II machinery.

### Important caveat: the famous OS I gap

OS II explicitly states that OS I incorrectly used Lemma 8.8 to continue
simultaneously in all time variables to the full product of right half-planes.

That means the safe reading of OS I is:

- one-variable continuation from semigroup matrix elements is sound,
- simultaneous all-variable continuation requires extra work.

This is why our current base-step should be thought of as a one-gap /
one-variable theorem first, not a full many-variable continuation all at once.

This is the single most important historical warning for current development:

- if a proof sketch seems to jump from one semigroup variable to a full
  `C_+^k` continuation in one move, it is probably recapitulating the old OS I
  gap.

## 3. OS II: the corrected continuation strategy

OS II revisits the `E -> R` direction in Chapters IV and V.

The most important correction is conceptual and explicit:

- continue only in the time variables,
- treat the spatial variables as parameters,
- and build the analytic continuation inductively.

OS II states this very clearly in Chapter V:

- `S_k(ξ) = S_k(ξ^0 | ξ_)`
- the time variables are the analytic variables,
- the spatial variables play the role of parameters.

This matters directly for the current Lean blocker. The public theorem
`schwinger_continuation_base_step` in
[OSToWightman.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean)
has now been corrected to the safe OS II base-step reading:

- time-difference holomorphicity,
- spatial variables treated as parameters,
- Euclidean reproduction on the Schwinger test side.

The old full-`ACR(1)` holomorphic surface still exists only as a private legacy
upgrade theorem used by the current downstream restriction chain. So the root
blocker is no longer "what should the public base-step statement be?" but
rather:

- close the honest time-parametric theorem, and
- either justify or eventually eliminate the private legacy upgrade step.

This is the part of the papers we should be pattern-matching in Lean.

### Theorems 4.1, 4.2, 4.3 in OS II

OS II organizes the continuation into a ladder:

- Theorem 4.1 `(A0)`: real analyticity in a complex neighborhood of real time
  variables, plus temperedness estimates.
- Theorem 4.2 `(A_r)`: continuation to larger open subsets `C_k^(r)` of the
  time-variable domain.
- Theorem 4.3: full continuation on the product right half-plane `C_+^k`,
  still with spatial variables treated parametrically.

Then standard Fourier-Laplace arguments produce the Wightman distributions.

The practical lesson for us is:

- the genuine engine is a one-variable continuation theorem with parameters,
- not an ad hoc many-variable identity theorem on the whole shell.

### 3.1. The inductive structure in OS II

OS II is explicit that the continuation is built inductively.

Their sequence is:

- Theorem 4.1 `(A0)`:
  establish real analyticity near the real domain, together with a temperedness
  estimate.
- Theorem 4.2 `(A_r)`:
  continue to larger open subsets `C_k^(r)`.
- Theorem 4.3:
  obtain analytic continuation on the whole product right half-plane in the
  time variables.

So the actual architecture is:

- local analyticity / one-variable continuation,
- inductive domain enlargement,
- then global Fourier-Laplace extraction.

That should be the default sanity check for our own file structure.

### 3.2. The corrected semigroup formula in OS II

Chapter V of OS II restates the semigroup part in a corrected notation. The
key formulas are `(5.2)`-`(5.4)`.

The conceptual content is:

- `Ψ_n(x, ξ)` packages the parameter variables,
- `e^{-tH}` shifts one time variable,
- the semigroup matrix element defines analytic continuation in the `n`-th
  time variable,
- but only one variable at a time.

The paper then says explicitly that OS I went wrong when it tried to continue
all time variables simultaneously at that stage.

This is very close to the current role of:

- `OSToWightmanSemigroup.lean` for the semigroup matrix element,
- `OSToWightmanTwoPoint.lean` for the first nontrivial parameterized shell
  where we are trying to identify the correct descended parameter object.

### 3.3. How OS II proves real analyticity in practice

OS II, Chapter V, is more concrete than the theorem ladder alone might suggest.
The proof of `(A0)` has several technical ingredients:

1. Rewrite the Green's functions in difference variables and preserve the OS
   positivity form.
2. Build Hilbert-space-valued distributions `Ψ_n(x, ξ)` so that the scalar
   product identity `(5.2)` holds.
3. Use the self-adjoint contraction semigroup `e^{-tH}` to shift one time
   variable, giving `(5.3)`.
4. Use the matrix element formula `(5.4)` to continue in a single time
   variable while keeping all remaining variables distributional/parametric.
5. Use Euclidean covariance plus carefully chosen cones to convert these
   one-variable continuations into genuine local analyticity in all time
   variables near the real domain.

The geometric part is the key refinement over the naive OS I picture.

#### 3.3.1. Cone geometry and rotated continuation

OS II chooses cones `R_+^k(y)` and dual-cone vectors `e_1, ..., e_4` so that:

- the original real configuration lies in a cone stable under small rotations,
- the chosen `e_μ` point into directions compatible with one-variable semigroup
  continuation,
- and the analytically continued function can be parameterized by variables
  `u_i^μ ≥ 0` in the directions `e_μ`.

Then the argument proceeds by taking logs `s_i^μ = ln u_i^μ`, getting separate
flat tubes in the `s`-variables, and applying the Malgrange-Zerner / tube
theorem to pass from separate flat-tube analyticity to analyticity on the
convex envelope of the union.

This is one of the most important proof ideas in OS II:

- separate one-variable semigroup analyticity
  `+`
- Euclidean covariance / cone geometry
  `+`
- a tube theorem
  `=`
- genuine local analyticity in several time variables.

#### 3.3.2. Why Lemma 5.1 matters

Lemma 5.1 is not just a convenience estimate. It gives an explicit polydisc of
analyticity around each real point `ξ`, with radius controlled by

- the size of the time coordinates,
- and the ratio `ξ_i^0 / |ξ_i|`.

This is exactly the kind of local quantitative analyticity one later needs in
Chapter VI when turning distributional information into polynomial estimates on
the resulting analytic functions.

#### 3.3.3. What `(AN)` and `(PN)` are really doing

The induction in Chapter V alternates between two statements:

- `(AN)`:
  scalar-valued analytic continuation on larger time domains `C_k^(N)`;
- `(PN)`:
  Hilbert-space-valued vectors `Ψ_n(x, ζ)` on larger mixed domains `D_n^(N)`
  whose scalar products reproduce the analytically continued Green's functions.

This alternation is structurally important.

`(PN)` gives the semigroup/Hilbert-space control needed to define the next
analytic continuation step, and `(AN)` packages the outcome as a scalar
analytic function on a larger domain. Then the process repeats.

So the real engine is not just “analyticity by semigroup.” It is:

- vector-valued semigroup control
  `->`
- scalar analytic continuation
  `->`
- bigger vector-valued domain
  `->`
- bigger scalar domain.

That is a useful model for our own general one-gap theorem design.

#### 3.3.4. Lemma 5.2 and Corollary 5.3

Lemma 5.2 is the combinatorial/domain-growth heart of the OS II induction.
It shows that the recursively defined domains `D_n^(N)` and `C_k^(N)` contain
explicit regions whose opening increases with `N`.

Corollary 5.3 then gives a quantitative lower bound on how much of the time
domain is covered at stage `N`. This is what ultimately lets OS II conclude
that the union of all `C_k^(N)` is the whole product right half-plane `C_+^k`.

So there are two distinct technical burdens in OS II:

- Chapter V:
  prove the continuation exists on bigger and bigger domains;
- Chapter VI:
  prove the resulting functions satisfy usable polynomial bounds on those
  domains.

## 4. Method A vs Method B in OS II

OS II distinguishes two ways to handle spatial variables.

### Method A

Treat spatial variables distributionally throughout.

Pros:

- simpler,
- closer to the semigroup formulas.

Cons:

- needs a stronger growth assumption, roughly the stronger `E0"`-type input.

### Method B

Use Euclidean invariance and a Glaser-type geometric argument to show the
relevant functions are honest continuous / analytic functions of spatial
variables, not merely distributions in them.

Pros:

- works under the weaker corrected OS growth assumption.

Cons:

- much more geometric,
- more technically demanding.

For our current Lean state, the semigroup-side two-point work is closer to
Method A in flavor, while the eventual `boundary_values_tempered` and some of
the Euclidean analyticity work are closer to Method B.

An important practical reading of this split:

- if we are trying to close the immediate `schwinger_continuation_base_step`
  blocker, Method A style semigroup/parameter work is probably the right local
  target;
- if we are trying to close the full growth / temperedness / boundary-value
  chain, then Method B style analyticity and geometry will inevitably come
  back.

### 4.1. Exactly where the linear growth condition is used

OS II is explicit on this point: the linear growth condition `E0'` is used for
the **temperedness estimates**, not for the bare existence of analytic
continuation.

The proof logic is:

- Chapter V:
  construct `S_k(ζ)` and `S_k(ζ^0 | ξ)` using semigroup continuation and
  Euclidean covariance, with only `E0`, `E1`, `E2`;
- Chapter VI:
  use `E0'` to derive the bounds `(4.5)` and `(4.6)` that make the
  Fourier-Laplace/boundary-value step rigorous in the tempered category.

That is why OS II says the linear growth condition is only needed at “this
stage,” namely the temperedness-estimate stage.

### 4.2. Chapter VI.1: from distributions to actual functions

This is one of the most technical parts of OS II, and it is worth summarizing
carefully because it explains what “linear growth” is really buying them.

The problem is:

- even if `S_k(ξ)` is known to be real analytic,
- and even if it arises from a distribution satisfying `E0'`,
- it does **not** follow formally that the resulting analytic function is
  polynomially bounded.

OS II therefore does not estimate `S_k` directly. Instead it:

1. uses the local analyticity radius from Lemma 5.1,
2. performs a carefully chosen regularization of `S_k` in complex directions,
3. obtains a smoother auxiliary object `T_k`,
4. estimates `T_k`,
5. then recovers bounds on `S_k` via a mean-value / maximum-principle argument.

#### 4.2.1. The regularization step

OS II chooses:

- a compactly supported radial mollifier in complex directions,
- a kernel `k_ρ`,
- and a compactly supported bump `g_ρ`.

Using the local polydisc analyticity from Lemma 5.1 and the mean-value theorem
for harmonic functions, they rewrite `S_k(ξ + ζ)` as an average of a regularized
object `T_k` over a small complex neighborhood.

The key lesson is:

- they do not estimate the raw analytic function head-on;
- they first move to a regularized object that still remembers positivity.

#### 4.2.2. Why positivity matters for the estimate

The regularized `T_k` still satisfies a positivity structure inherited from the
OS form. This allows OS II to write `T_k` as a scalar product of two vectors in
the OS Hilbert space.

That is the bridge back to semigroup methods:

- once `T_k` is a scalar product `(Ψ_1, Ψ_2)`,
- the shifted quantity `(Ψ_1, e^{-zH} Ψ_2)` gives analytic continuation in one
  complex variable,
- and its absolute value is bounded by `||Ψ_1|| * ||Ψ_2||`.

So the linear growth estimate is *channeled through Hilbert-space norms*.
That is a very useful structural point.

#### 4.2.3. Where `E0'` actually enters

The hard analytic estimate in VI.1 is the bound on the norms of those vectors,
schematically of the form

- `||Ψ_1|| ≤ σ_n * (...)^s`,
- `||Ψ_2|| ≤ σ_{k-n+1} * (...)^s`,

with factorial-growth sequences and polynomial dependence on the parameters.

This is precisely where the linear growth condition is used.

In other words:

- `E0'` is not used to show the semigroup exists;
- `E0'` is not used to show one-variable continuation exists;
- `E0'` is used to control the **size** of the vectors that arise after
  regularization, so the semigroup matrix elements satisfy quantitative
  polynomial bounds.

#### 4.2.4. Why four directions appear

OS II analytically continues the regularized object in `4k` linearly
independent directions. This is a specifically Euclidean four-dimensional
feature of the proof as written: they choose four independent vectors `e_μ`
coming from the cone geometry and continue in each associated direction.

Then they use the Malgrange-Zerner theorem on the union of the corresponding
tubes and the maximum principle to control the analytic continuation on the
full local complex neighborhood.

So the logic is:

- directional semigroup continuation in enough independent directions
  `+`
- envelope of holomorphy / tube theorem
  `+`
- maximum principle
  `=`
- polynomial bound on the full local analytic function.

#### 4.2.5. Output of VI.1

The output is the real-domain temperedness estimate `(4.5)`.

This is already a significant strengthening over mere analyticity: it says the
real-analytic functions `S_k(ξ)` satisfy a polynomial bound of the exact type
needed to later treat them as tempered boundary values after further analytic
continuation.

### 4.3. Chapter VI.2: continuing the estimates

Once `(4.5)` is proved on the real domain, OS II carries those estimates through
the inductive analytic continuation domains `C_k^(N)`.

The key move is to regard `S_k(ζ^0 | ·)` as taking values in a Banach space of
continuous functions of the spatial variables with polynomial weights. Then:

- the real-domain bound gives a Banach-space norm estimate,
- the Chapter V induction gives analyticity on larger domains,
- the maximum principle transports the estimate from one stage to the next,
- and Corollary 5.3 provides quantitative control that eventually covers all of
  `C_+^k`.

So Chapter VI.2 is not re-proving analyticity. It is transporting the **bounds**
along the analytic continuation ladder already built in Chapter V.

### 4.4. Why this matters for our Lean plan

The distinction between Chapters V and VI suggests a very concrete division of
labor for our `E -> R` development:

- first prove the OS-style one-gap semigroup continuation/factorization
  theorem;
- only after that, attack the growth estimates needed for
  `boundary_values_tempered`.

If we blur those two stages, we risk mixing the Chapter V and Chapter VI
burdens and making both harder.

## 5. Exact correspondence with the current Lean files

### `OSToWightmanSemigroup.lean`

This file corresponds to the clean semigroup/Hilbert-space part of OS I and OS
II:

- construction and use of the holomorphic semigroup,
- spectral/Laplace bridge,
- one-variable holomorphic matrix elements.

This is the Lean home of the semigroup object itself.

Paper correspondence:

- OS I `(4.6)`-`(4.11)`
- OS II `(5.3)`-`(5.4)`

### `OSToWightman.lean`

This file is the base-step analytic continuation core.

Its main remaining blocker

- `schwinger_continuation_base_step`

is the Lean version of: turn the semigroup continuation mechanism into the
actual Schwinger-shell continuation statement needed by reconstruction.

This file should remain the place where the general one-gap continuation
machinery lives, not the place where all specialized shell reductions get
accumulated.

### `OSToWightmanTwoPoint.lean`

This file is not a separate OS theorem in the papers. It is our controlled
model case for the first genuinely nontrivial continuation mechanism.

Its role is:

- isolate the center/difference-variable issue,
- expose the semigroup-side product-shell vs admissible-shell mismatch,
- reduce the missing input to a precise factorization / annihilation statement.

So this file is a Lean-specific staging ground for the OS one-gap mechanism.

Its real value is diagnostic:

- if we can make the semigroup scalar depend only on the descended
  difference-variable parameter here,
- then we have identified the theorem shape the general OS-style parameter
  theorem must satisfy.

### `OSToWightmanBoundaryValues.lean`

This file corresponds to the downstream Fourier-Laplace / boundary-value stage:

- temperedness of boundary values,
- transfer of the continued objects to Wightman distributions,
- support/growth transport.

This is downstream of the current blocker, not upstream of it.

## 6. What the current `k = 2` work means in OS language

Our current two-point descent infrastructure does the following.

On center/difference coordinates `(u, ξ)`:

- `twoPointCenterDescent` integrates out the center block `u`,
- `twoPointCenterShearDescent` produces the descended difference-variable test
  from the semigroup/product shell,
- `twoPointCenterShearResidual` is the kernel element measuring the mismatch
  between the product shell `χ(u) g(u + ξ)` and its canonical admissible
  representative `χ(u) h(ξ)`.

Recent progress:

- the residual has zero descent,
- the descent operator is now covariant under right translations on the
  product shell.

Translated into OS language, this means:

- we are trying to prove that the relevant semigroup matrix element depends
  only on the descended difference-variable parameter,
- i.e. that the semigroup continuation factors through the correct one-gap
  parameter object.

That is exactly the kind of statement OS encode by fixing `h_m` and running the
semigroup/Laplace argument only in one time variable.

### 6.1. Why the current descent language is not alien to OS

The papers do not literally define our `twoPointCenterDescent`, but conceptually
it is doing the same job as OS’s parameter packaging:

- remove the dummy center variable,
- isolate the true difference-variable content,
- and force the scalar continuation problem to depend only on that content.

So the descent language is a Lean-specific implementation of an OS-style
parameterization step, not a deviation from the paper’s method.

### 6.2. Production realization of the center-integration step

The current production files now contain a fairly clean realization of the
“integrate out the dummy center variable” step.

At the block-integration level:

- `integrateHeadBlock_tensorProduct`
  in [BlockIntegral.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/BlockIntegral.lean)
  says that integrating out the head block of a tensor-product Schwartz test
  gives exactly “integral of the head factor” times the tail factor.

- `integrateHeadBlock_translateSchwartz_tail`
  and
  `integrateHeadBlock_translateSchwartz_head`
  say that block integration is compatible with translating the surviving block
  and invariant under translating the block that gets integrated out.

At the two-point descent level:

- `twoPointCenterDescent_twoPointDifferenceLift_eq_integral_smul`
  in [TwoPointDescent.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/TwoPointDescent.lean)
  is the exact admissible-shell formula:
  `twoPointCenterDescent (twoPointDifferenceLift χ h) = (∫ χ) • h`.

- `twoPointCenterDescent_twoPointProductLift_eq_differenceRepresentative`
  says that the semigroup/product shell and its canonical admissible
  representative have the same descent.

- `twoPointCenterDescent_twoPointCenterShearResidual_eq_zero`
  isolates the kernel element measuring the mismatch between those two shells
  and proves that its descent is zero.

- `twoPointCenterShearDescent_translate_right`
  and
  `twoPointCenterShearDescent_translate_left`
  show that the descended parameter behaves correctly under translation of
  either the right factor or the center cutoff on the product shell.

There is an important update to the interpretation of this package.

The admissible-shell center-collapse step is no longer the live blocker. It is
already closed in production, both on the Schwinger side and on the witness
side:

- `OsterwalderSchraderAxioms.exists_const_twoPointDifferenceLift_eq_integral`
  and
  `OsterwalderSchraderAxioms.twoPointDifferenceLift_eq_centerValue`
  in [SchwingerOS.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean)
  say that for admissible shells `χ(u) h(ξ)`, the two-point Schwinger value
  depends on the center cutoff only through `∫ χ`.

- `schwinger_twoPoint_flatCenterDiffWitness_exists_const`
  and its corollaries in
  [OSToWightman.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean)
  give the corresponding center-collapse statement for explicit flat witnesses.

This is already quite close to what the OS papers need conceptually:

- identify the dummy center variable,
- integrate it out,
- get a parameter object in the true difference variable,
- and prove the analytic continuation depends only on that parameter object.

So the current production descent package should be read as:

- a successful Lean implementation of the OS parameter-packaging step on the
  admissible shell, and
- a diagnostic package for the remaining semigroup-side mismatch.

What still remains unresolved is **not** the statement that admissible shells
factor through the center integral. What remains is the comparison between:

- the natural semigroup/product shell `χ(u) g(u + ξ)`, and
- the admissible shell `χ(u) h(ξ)` obtained after descent.

This distinction matters because OS do not face it in the same form: they pass
to difference variables from the start, so the dummy center variable has
already disappeared before the semigroup continuation step is stated.

### 6.3. Direct `k = 2` semigroup specialization

For `k = 2`, the semigroup/spectral picture becomes much simpler than the
general multi-gap story.

There is only one genuine time-difference variable, so we do **not** need any
joint spectral-measure story. The relevant scalar is already an ordinary
two-vector semigroup matrix element.

The key current production statements are:

- `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`
  in [OSToWightmanSemigroup.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSemigroup.lean),
  which identifies the holomorphic semigroup matrix element with the spectral
  Laplace off-diagonal form.

- `selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift`
  in [OSToWightmanTwoPoint.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanTwoPoint.lean),
  which identifies that spectral object with the explicit `ξ`-shift Euclidean
  integral for one-point test pairs.

- `twoPointDifferenceLift_timeShift_holomorphicValue_semigroupMatrix_centerShear_centerValue`
  in [OSToWightmanTwoPoint.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanTwoPoint.lean),
  which packages the two-point continuation directly in terms of the semigroup
  matrix element after the center-shear reduction.

- the spatial-translation chain in
  [OSToWightmanSemigroup.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanSemigroup.lean):
  `translateSchwartzNPoint_timeShiftSchwartzNPoint`,
  `timeShiftBorchers_translateBorchers`,
  `OSInnerProduct_translate_eq_of_spatial`,
  `OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single_translate_spatial`,
  and
  `OSInnerProductTimeShiftHolomorphicValue_single_translate_spatial`.
  Together, these now show that the one-point semigroup pairing is already
  spatially translation invariant on the full right half-plane, not just on the
  positive real axis.

This is the precise OS-style reading of the current two-point file:

- the live issue is not a missing spectral theorem,
- and not a missing holomorphic-extension theorem in abstract form,
- but the mismatch between the semigroup-side center-shear shell
  `χ(u) g(u + ξ)` and the admissible difference shell `χ(u) h(ξ)`.

The descent package explains how these shells are related, but it does not by
itself prove that every semigroup-side scalar pairing depends only on the
descended parameter. So the current gap is better described as:

- either a factorization theorem for the specific semigroup/witness scalar
  functional,
- or an honest difference-variable bridge that removes the center-shear shell
  before the semigroup step is stated.

At the current production state, the first option has become more precise.
The spatial-translation part is no longer the blocker. What remains is the
fixed-time extension theorem behind the private `headBlockExtension` surface in
[OSToWightmanTwoPoint.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanTwoPoint.lean):

- for each `t > 0`, construct a continuous head-block-translation-invariant
  Schwartz functional on the flattened center/difference space;
- make it recover the semigroup/product-shell value on
  `twoPointProductLift χ₀ g`;
- and make it also evaluate the canonical admissible shell built from
  `twoPointCenterShearDescent χ₀ g`.

So the remaining issue is now an extension/continuity theorem, not more
translation algebra.

## 7. The current `E -> R` blocker in OS terms

The current blocker is not:

- “find some holomorphic function.”

It is:

- construct the correct one-gap parameterized semigroup object directly in
  difference variables,
- or prove that the current semigroup/product-shell scalar functional agrees
  with the admissible-shell scalar functional determined by the same descended
  parameter.

Historically, the two-point file exposed this as a residual-annihilation /
factorization problem. That was useful diagnostically, but it should no longer
be treated as the final theorem surface. The public production surface is now
cleaner: the residual-annihilation wrapper is gone, and the real gap is the
product-shell vs admissible-shell identification itself.

That is the correct OS-style next step.

### 7.1. What a truly OS-shaped missing theorem would look like

The missing theorem should have one of these two flavors:

 - input:
  the semigroup-side product shell together with its descended parameter
  object;
 - claim:
  the semigroup matrix element agrees with the scalar functional defined from
  the admissible shell carrying the same descended parameter;
 - output:
  the resulting scalar function is the correct holomorphic continuation in the
  chosen time variable.

In other words, the theorem should eliminate the shell mismatch structurally,
not by postulating an accidental equality of two unrelated shells.

### 7.2. The precise factorization route suggested by the current code

The current code suggests a very concrete theorem chain for `k = 2`, but it
should now be read a little more cautiously than before.

Fix a normalized cutoff `χ₀` with `∫ χ₀ = 1`, and let

- `g`
  be the product-shell one-point test,
- `twoPointCenterShearDescent χ₀ g`
  be the canonical descended admissible representative,
- `twoPointCenterShearResidual χ₀ g`
  be the difference between the original product shell and its canonical
  descended representative.

We already know:

- `twoPointCenterDescent (twoPointCenterShearResidual χ₀ g) = 0`.

One possible missing theorem would say:

- if `L` is the relevant semigroup/witness scalar functional on two-point
  center/difference Schwartz space,
- and `L` is invariant under center translation,
- then `L` factors through `twoPointCenterDescent`.

Formally, the desired pattern is:

- `L (translate_in_center a F) = L(F)` for all center translations `a`,
- therefore there exists `L'` on difference-variable Schwartz space such that
  `L = L' ∘ twoPointCenterDescent`.

Once such a factorization theorem is available, the residual is killed for the
right structural reason:

- `twoPointCenterDescent residual = 0`,
- so `L(residual) = L'(0) = 0`.

Then the remaining chain is immediate:

1. product shell and canonical admissible shell have equal scalar pairings,
2. the semigroup/spectral object already computes the product-shell pairing,
3. therefore the same semigroup/spectral object computes the admissible shell,
4. hence the admissible shell has the required holomorphic continuation.

However, the current production stance is that this factorization theorem is
only **one candidate route**. The more OS-faithful route may be to remove the
product-shell mismatch earlier by working directly with the correct
difference-variable parameter object, rather than proving a large abstract
factorization theorem over the residual kernel.

The current code suggests an intermediate stance between these two pictures:

- use the now-proved semigroup-side spatial translation invariance to eliminate
  all purely translational ambiguity;
- then prove the extension theorem that lets this invariance act on the full
  flattened center/difference Schwartz space.

### 7.2.1. Why the extension theorem is genuinely nontrivial

It is tempting to try to define the fixed-time extension functional simply by:

- taking a Schwartz function on the flattened center/difference space,
- undoing the flattening and center/difference change of variables,
- and applying `OS.S 2`.

At the current formalization surface, that does **not** solve the problem.

The reason is structural:

- `OS.S 2` is defined on `ZeroDiagonalSchwartz d 2`,
- while the desired extension functional must act on **all**
  Schwartz functions on the flattened center/difference space.

So the missing content is not just a reindexing or change-of-variables lemma.
One must still prove an actual extension statement from the zero-diagonal
subspace to the ambient Schwartz space, together with the required
head-block-translation invariance.

This is exactly why the present blocker should be read as an
extension/continuity theorem, not as leftover shell algebra.

So the remaining mathematical gap is still small in statement size but deep in
content:

- not another shell identity,
- not a disguised matching hypothesis,
- but either a true factorization theorem for the semigroup-side scalar
  functional, or a cleaner difference-variable reformulation that makes the
  mismatch disappear.

### 7.3. Why this is the right OS-shaped next theorem

This factorization route is one defensible OS-shaped route, but only if it is
used to remove the mismatch structurally. It should not be turned into a tower
of conditional shell-matching lemmas.

OS do not proceed by proving accidental shell identities. They:

- package the non-analytic variables into a parameter object,
- show the analytic continuation depends on that parameter,
- and then study the resulting one-variable function.

Our descent language is the Lean equivalent of that move on the admissible
side. The present challenge is to make the semigroup/product-shell side meet
that same parameter object without smuggling the missing identification as a
hypothesis.

So, from the perspective of the papers, the right next theorem is:

- not “a better shell-comparison lemma,”
- and not “assume the product shell already matches the admissible shell,”
- but “remove the center-shear mismatch for the semigroup scalar by an honest
  parameter theorem.”

## 8. Path from `k = 2` to general `k`

The papers suggest the following route.

1. Solve one-gap continuation with all other variables treated as parameters.
2. Package the parameter space in a Schwartz-compatible way.
3. Show the resulting continued object satisfies the needed growth estimates.
4. Iterate this one-gap mechanism across the ordered time differences.

So the role of the current two-point development is not to serve as a final
base case for induction on `k`.

Its role is to identify, in the simplest nontrivial case, the exact theorem
shape the general parameterized continuation must satisfy.

### 8.1. The real generalization step

The real jump from `k = 2` to general `k` is therefore:

- not “do the same proof with bigger indices,”
- but “replace the two-point descended difference-variable test by the general
  parameter object `h_m`.”

Once that parameterized theorem exists, the rest of the OS chain is the same in
spirit:

- semigroup matrix element,
- one-gap continuation,
- inductive enlargement of the analytic domain,
- Fourier-Laplace extraction,
- boundary values.

## 9. Practical takeaway for future Lean work

When deciding whether a new theorem is on the right path, the best test is:

- does it move us toward a one-gap semigroup continuation theorem with the
  remaining variables as parameters?

Good signs:

- factorization through a descent operator, when it removes a real mismatch
  rather than rephrasing it,
- explicit semigroup matrix-element formulas,
- parameterized one-variable holomorphic continuation,
- Fourier-Laplace packaging with support/growth control.
- proofs that a semigroup/witness scalar functional factors through
  `integrateHeadBlock` / `twoPointCenterDescent`.
- direct difference-variable formulations that bypass dummy center variables.

Bad signs:

- adding more shell-specific wrapper theorems with no new factorization content,
- treating `k = 2` as if it were itself the whole OS method,
- trying to continue all time variables simultaneously before the one-gap
  parameter mechanism is settled.
- treating the residual-annihilation criterion as a final theorem rather than
  as a signal that a deeper factorization theorem is still missing.
- treating the admissible-shell center-collapse theorem as if it solved the
  semigroup/product-shell mismatch.

## 10. Concrete current reading of the project

The current file split is consistent with the papers if we interpret it as:

- `OSToWightmanSemigroup.lean`
  = OS semigroup and one-variable matrix-element engine;
- `OSToWightman.lean`
  = intended home of the general one-gap continuation theorem;
- `OSToWightmanTwoPoint.lean`
  = first nontrivial laboratory for identifying the right parameter object;
- `OSToWightmanBoundaryValues.lean`
  = downstream Fourier-Laplace / growth / boundary-value layer.

The current risk is not mathematical unsoundness in the two-point ladder.
It is theorem-surface drift:

- if we keep adding shell-specific criteria, the file may grow while the real
  product-shell/admissible-shell identification stays untouched.

Conversely, the current opportunity is good:

- the descent package in
  [BlockIntegral.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/BlockIntegral.lean)
  and
  [TwoPointDescent.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/TwoPointDescent.lean)
  has already exposed the kernel element and the correct covariance properties;
- the admissible-shell center-collapse theorem is already in production;
- so the remaining step is now concentrated on the semigroup-side shell
  comparison rather than on general center-factorization.

Finally, some older local Bernstein-Widder / center-shear scratch notes are now
partly superseded by the production descent infrastructure. They may still be
useful for ideas, but they should no longer be treated as the current theorem
surface. The current production surface is the descent/factorization one.
The risk is staying too long in the laboratory file and never extracting the
general parameter theorem that OS II actually wants.

So the main remaining conceptual jump is:

- make the semigroup-side one-gap object land on the same difference-variable
  parameter object as the admissible shell,
- then generalize that identification from the two-point model to the general
  one-gap parameterized continuation mechanism.

One useful refinement from the latest semigroup-side attempts:

- asking immediately for invariance under the **full** center block
  `(center time + center space)` is probably too strong as the first
  production theorem surface;
- the spatial part is natural and now largely formalized from OS translation
  invariance;
- the time part interacts with the semigroup parameter itself and is better
  treated as part of the one-variable continuation mechanism.

So a more OS-II-shaped next target is:

- integrate out the center **spatial** variables,
- keep the center **time** variable as the active analytic parameter,
- and compare that semigroup-side parameter object with the admissible
  difference-variable shell before trying to package full center-block
  invariance.

This is now reflected more directly in production than before.
The file
[CenterSpatialTranslationInvariant.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/CenterSpatialTranslationInvariant.lean)
contains the explicit descended CLM
`centerSpatialDescentCLM`, and now also the iterated factorization theorem
`map_eq_headTranslationDescentCLM_sliceIntegral_integrateCenterSpatial`.
That theorem says:

- first descend a center-spatial-translation-invariant functional by
  `integrateCenterSpatial`,
- then, if the reduced `(u_time, ξ)` functional is head-translation
  invariant, descend again by `sliceIntegral`.

So the production theorem surface now matches the OS-II narrative more closely:

- spatial parameters are peeled off first,
- the remaining center-time variable is treated by the one-variable
  translation/factorization mechanism,
- and the remaining gap is no longer generic center-factorization but the
  reduced fixed-time semigroup functional and the reduced-shell identity.

## 11. R -> E direction: BHW theorem and translation invariance

The `R -> E` direction (Wightman to OS) involves the Bargmann-Hall-Wightman
theorem and its consequences. The key references are Streater-Wightman
Chapter 2 and Jost's *PCT, Spin & Statistics, and All That*.

### 11.1. BHW theorem structure

The BHW theorem extends the Wightman functions from the forward tube to the
permuted extended tube (PET) by:

1. The complex Lorentz group `SL(2,C)` acts on the forward tube.
2. By analytic continuation (identity theorem), the Wightman function extends
   to the orbit of the forward tube under `SL(2,C)`.
3. Jost's theorem: this orbit equals the extended tube.
4. By permutation symmetry (Bose/Fermi), the function extends to the PET.

This is implemented in:
- `AnalyticContinuation/BHWExtension.lean` — `fullExtendF`
- `AnalyticContinuation/Extend.lean` — `complex_lorentz_invariance`

### 11.2. Translation invariance of the BHW extension

The live R→E blocker is `bhw_translation_invariant` in `BHWTranslation.lean`,
which reduces to `isPreconnected_baseFiber`.

The proof that the BHW extension `F_ext` is translation-invariant requires:
- On the forward tube: `F_ext(z+c) = F_ext(z)` by the original Wightman
  function's translation invariance.
- On the PET: extend by the identity theorem on connected components.

The blocker `isPreconnected_baseFiber` asks: for fixed tail variables, is the
fiber of the PET in the base variable (z₀) path-connected?

### 11.3. ForwardTube variable convention issue

This section records an earlier debugging concern and should be read as
historical / exploratory rather than as the current public contract.

Current settled reading of the repo:
- the public surfaces `WightmanQFT.wightmanFunction n` and
  `WightmanFunctions.W n` are literal `n`-point objects;
- the current public `ForwardTube d n` is an absolute-coordinate tube with
  the basepoint condition `Im(z₀) ∈ V⁺` and the successive-difference
  conditions `Im(z_k - z_{k-1}) ∈ V⁺` for `k ≥ 1`;
- this is slightly stronger than the minimal literal `n`-point tube often
  used in the standard literature;
- the reduced `(m + 1) -> m` difference-variable convention belongs to the
  internal Route 1 bridge, not to the public meaning of `W n`.

So the important present-day point is not that the public `ForwardTube d n`
was "wrong", but that the repo mixes:
- a public literal `n`-point API, and
- an internal reduced Route 1 descent from absolute arity `m + 1` to reduced
  arity `m`.

That distinction must be kept explicit when reading older debugging notes.

### 11.4. Relaxed tube bridge

`ForwardTubeRelaxed d n` (proved in `test/proofideas_diff_var_bridge.lean`)
drops the k=0 condition. Key results:
- `pet_subset_relaxed`: PET ⊆ PET_relaxed
- `petRelaxed_translation_invariant`: PET_relaxed is trivially
  translation-invariant (differences unchanged by uniform shift)
- `pet_eq_petRelaxed` is FALSE (the base condition is genuinely restrictive)

### 11.5. BEG path lemma (Cases 1 and 2)

The Bros-Epstein-Glaser path lemma shows that any complex Lorentz group
element can be connected to the identity by a path staying in the tube.
Two canonical forms:

**Case 1 (nilpotent/shear)**: The Lorentz boost is nilpotent. The path is a
straight line (convex combination), which stays in the tube because the
forward light cone is convex.
- Proved: `nilpotent_path_in_tube` in `test/proofideas_BEG_path_lemma.lean`

**Case 2 (semisimple/boost-rotation)**: The Lorentz transformation has
eigenvalues e^{±α±iβ}. The lightcone components follow g±(t) = e^{±αt}(q cos βt + p sin βt).
Positivity reduces to the sinusoidal factor.
- Proved: `sinusoidal_pos_of_endpoints_pos` in `test/proofideas_BEG_case2.lean`
  (extracted to `BEGTrigonometric.lean`)

Both cases combine to give the BEG path lemma → sector preconnectedness →
`isPreconnected_baseFiber` → `bhw_translation_invariant`.

## 12. Fiberwise antiderivative and E→R factorization chain

The fiberwise antiderivative provides the analytical backbone for the
center-factorization argument that kills the E→R shell mismatch.

### 12.1. The complete chain (all proved)

```
fiberwiseAntiderivRaw F v = ∫ t ∈ Iic(v₀), F(cons t (tail v))
  → contDiff_fiberwiseAntiderivRaw         [PROVED, SliceIntegral.lean + test]
  → decay_fiberwiseAntiderivRaw            [PROVED, test file, 0 sorrys]
  → fiberwiseAntideriv : SchwartzMap       [PROVED, test file]
  → lineDeriv_fiberwiseAntideriv: ∂₀g = F  [PROVED, test file]
```

This gives the Schwartz Poincaré lemma: if ∫ F(cons t y) dt = 0 for all y,
then F = ∂₀ g for some Schwartz g.

### 12.2. Connection to center factorization

The multi-D Poincaré lemma is already proved independently in production:
- `exists_eq_sum_lineDeriv_of_integral_eq_zero` in
  `TranslationInvariantSchwartz.lean`

Combined with translation invariance of the OS functional:
- `exists_eq_const_integralCLM_of_translationInvariant`: any
  translation-invariant CLM on Schwartz space equals c·∫

This means the OS functional on 2-point functions factors through center
descent (integrating out the center variable). The shell mismatch
(product shell χ(u)g(u+ξ) vs admissible shell χ(u)h(ξ)) is resolved because
the semigroup evaluation sees only the descended difference variable.

### 12.3. Infrastructure summary

| Component | File | Status |
|-----------|------|--------|
| `iicZeroSlice` chain | `SliceIntegral.lean` | 0 sorrys |
| `intervalPiece` chain | `SliceIntegral.lean` | 0 sorrys |
| `fiberwiseAntiderivRaw` decomposition | `SliceIntegral.lean` | 0 sorrys |
| `contDiff_fiberwiseAntiderivRaw` | test file | 0 sorrys |
| `decay_fiberwiseAntiderivRaw` | test file | 0 sorrys |
| `fiberwiseAntideriv` packaging | test file | 0 sorrys |
| Multi-D Poincaré lemma | `TranslationInvariantSchwartz.lean` | 0 sorrys |
| Translation factorization | `TranslationInvariantSchwartz.lean` | 0 sorrys |

## 13. Lean ↔ OS II formula dictionary for `schwinger_continuation_base_step`

The single remaining E→R sorry is `schwinger_continuation_base_step` at
`OSToWightman.lean:430`. Here is the precise mapping to OS II.

### 13.1. The sorry statement

```lean
∃ G : (Fin (k * (d + 1)) → ℂ) → ℂ,
  DifferentiableOn ℂ G (TubeDomain (FlatPositiveTimeDiffReal k d)) ∧
  ∀ f : ZeroDiagonalSchwartz d k,
    OS.S k f = ∫ x, G(toDiffFlat(wickRotate(x))) * f(x)
```

### 13.2. OS II correspondence

- `G` = OS II's `S_k(ζ)` in difference variables, equation (5.4)
- `TubeDomain(FlatPositiveTimeDiffReal k d)` = flattened product tube
  `{ζ ∈ ℂ^{k(d+1)} : Im(ζⱼ⁰) > 0 for all j}` in the time components
- The identity `OS.S k f = ∫ G(toDiffFlat(wickRotate(x))) * f(x)` =
  OS II's distributional identity (5.2) after Wick rotation
- `wickRotatePoint` implements `x → ix⁰ + x_spatial` (Wick rotation)
- `toDiffFlat` converts cumulative-sum variables to flattened differences

### 13.3. Construction for k=2

For `k=2`, `G` has one difference variable ζ ∈ ℂ^{d+1}:
```
G(ζ) = ⟨Ψ₁(ξ_spatial), T(ζ⁰) Ψ₁(ξ_spatial)⟩_OS
```
where `Ψ₁` embeds one-point test functions into the OS Hilbert space and
`T(z) = e^{-zH}` is the holomorphic semigroup for `Re z > 0`.

This is already partially implemented:
- `OSInnerProductTimeShiftHolomorphicValue` gives `⟨F, T(z) G⟩`
- `exists_twoPoint_xiShift_holomorphicValue` proves holomorphicity for
  compact-support test functions

### 13.4. Construction for general k

For general `k`, OS II's formula (5.3) gives:
```
G(ζ₁,...,ζ_{k-1}) = ⟨Ψ₁, T(ζ₁⁰) A₂ T(ζ₂⁰) ... T(ζ_{k-1}⁰) Ψ_{k-1}⟩
```
where `Aⱼ` are operator-valued distributions (smeared field operators) and
`Ψⱼ` are Hilbert-space-valued distributions.

This requires the GNS construction + operator domains, which is why the
general k case is harder than k=2.

### 13.5. What remains to close the sorry

For k=2:
1. Connect `OSInnerProductTimeShiftHolomorphicValue` to `G` via the
   difference-variable bridge
2. Show `G` is holomorphic on the product right half-plane (from semigroup)
3. Verify the distributional identity on the Euclidean section

For general k:
1. Define the interleaved operator product `T A T A ... T`
2. Show the resulting matrix element is holomorphic in each time variable
3. Use the OS II induction (AN/PN alternation) for simultaneous continuation

## 14. Current theorem-3 fixed-time obstruction

On the current theorem-3 actual-shell route, the first missing mathematical
contract is not a new quotient-side equality theorem. The live obstruction is
strictly lower and more concrete:

- in
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  the branch `hlimit_os` already kills the actual shell integrand on source
  support and on region points outside source support;
- the first failure is the complement branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
- `section43_fixedTimeShellRawCLM` still integrates an ambient coefficient over
  all `y`, so region equality alone does not descend it;
- the available Section-4.3 quotient API only supplies equality/vanishing on
  `section43PositiveEnergyRegion d (n + m)`;
- the current shell-to-slice realization theorem is explicitly region-local.

So the exact first missing contract beneath `hlimit_os` is still the direct
raw-CLM comparison limit for the actual fixed-time shell difference, not a
strictly smaller complement-sensitive theorem already present in source.
Bounded theorem-3 actual-shell complement-side pointwise-supplier note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- the exact local source objects rechecked were:
  both live insertion-point theorem clusters,
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`,
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`,
  `hlimit_os`,
  the fixed-pair region transport/tensor-equality theorems, and the
  Section-4.3 quotient codomain theorems from `Section43Codomain.lean`;
- source-first verdict:
  no new honest theorem below the complement-side pointwise supplier itself is
  currently supported by live source for the actual shell difference;
- exact contract now exposed:

  `∀ y : NPointDomain d (n + m),
      y ∉ section43PositiveEnergyRegion d (n + m) →
      Filter.Tendsto
        (fun ε : ℝ =>
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (((φ.conjTensorProduct ψ) - (f.conjTensorProduct g)) y))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)`;

- why no smaller source-backed supplier exists:
  current source only controls the integrand on source support and on
  already-in-region outside-source points, while every quotient-side theorem
  still stops at `section43PositiveEnergyRegion d (n + m)`;
- no equivalent still-smaller explicit hypothesis beneath that supplier was
  found in the current source/toolkit;
- `hbound` is still open afterward, because no complement-sensitive ambient
  domination independent of `ε` is currently available either.
Bounded theorem-3 coefficient-package decomposition note (2026-04-15):

- `(A0)` was re-run first and both live insertion surfaces in
  `OSToWightmanPositivity.lean` are still clean; the second still contains
  `section43_fixedTimeShellRawCLM` and
  `section43_fixedTimeShellRaw_tendsto_zero_of_dominated_convergence`;
- exact source-first verdict:
  the coefficient-side complement vanishing theorem for the canonical-shell
  boundary value does not decompose one honest theorem/local-lemma step smaller
  on the current actual-shell route;
- exact source reason:
  smaller current-source-backed facts are only source-side or region-gated,
  hence they do not control the ambient shell coefficient on
  `y ∉ section43PositiveEnergyRegion d (n + m)`;
  the weaker kernel/fixed-pair complement suppliers are downstream consumers of
  this coefficient-side vanishing, not feeders beneath it;
- exact OS-I/OS-II citation status:
  the rechecked paper slots
  OS I Section 4.3 Lemma 4.1, Lemma 4.2, `(4.27)`, `(4.28)`,
  OS II Theorems 4.1-4.3,
  and OS II Chapter V `(5.2)`-`(5.4)`
  stay on semigroup continuation, positive-energy comparison, and
  Fourier-Laplace support / boundary-value extraction;
  they do not already state complement-side vanishing of the live canonical
  shell coefficient;
- exact present-source / paper status:
  the package is the first genuinely new mathematical package on this route,
  not an already-present source/paper theorem awaiting extraction;
- exact package order:
  1. coefficient-side complement pointwise coefficient vanishing;
  2. complement-side pointwise `hlim`;
  3. complement-sensitive `hbound`;
  4. limit-level canonical-shell kernel/fixed-pair annihilation;
  5. specialization to
     `((φ.conjTensorProduct ψ) - (f.conjTensorProduct g))`;
  6. discharge `hlimit_os`;
- no production Lean edits were made and no new compile-clean theorem/local
  lemma landed in this pass.
Bounded theorem-3 reading note on the same live actual-shell route, after
checking the generic nuclear-seminorm finite-net theorem against the current
finite-family theorem interface (`2026-04-15`, current bounded pass,
`2026-04-15T23:59:59Z`):

- first re-check:
  `section43_fixedTimeShellRawCLM`
  is still immediately followed by
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`,
  and the live theorem-level `sorry`s remain
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`
  and
  `section43_fixedPair_bvtW_timeShift_eq_osHolomorphicValue_fixedTime`;
- compile-clean consumer status:
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`
  remains present compile-clean in `SchwartzComplete.lean`;
- compile-clean producer-input status:
  `uniform_nuclear_tail_lt_of_q_bounded`,
  `finite_coordinate_image_totallyBounded_of_q_bounded`,
  and
  `finite_weighted_coordinate_net_of_q_bounded`
  remain present compile-clean in `NuclearSpace.lean`;
- reading correction:
  the honest smaller candidate below the generic theorem is not just
  "tail truncation + finite-family theorem as black boxes";
  the proof also needs the finite-head net centres to stay visibly inside `B`,
  because the tail estimate is required on `x - y`, not merely on `x`;
- exact first internal obligation beneath the generic theorem:
  package a truncation index `N`,
  a finite head net with centres in `B`,
  and a uniform tail bound on all differences `x - y` with `x, y ∈ B`,
  then conclude `p (x - y) < ε` by splitting the series with
  `Summable.sum_add_tsum_nat_add`;
- why this is only conditionally smaller:
  it is smaller as a theorem shape,
  but it is not presently available from the current theorem surfaces without
  either strengthening
  `finite_weighted_coordinate_net_of_q_bounded`
  to record `t ⊆ B`
  or re-running that representative-selection argument inside the generic proof;
- exact best Lean-ready theorem now required:
  still the full generic nuclear-seminorm finite-net theorem in
  `NuclearSpace.lean`;
- minimal hypotheses for the smaller local assembly theorem:
  dominance inequality for `p`,
  head-net centres in `B`,
  and a uniform tail estimate on differences of points in `B`;
- what remains immediately after that:
  the Schwartz specialization, then
  `SchwartzMap.tempered_eventually_mapsTo_sub_of_finite_seminorm_net`,
  then the strong-topology basis inside
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- why no compile-clean Lean landing occurred:
  the only honest smaller theorem needs data that the current finite-family
  theorem statement does not expose, so landing it cleanly in this bounded pass
  would have required either statement surgery on the already-landed
  finite-family theorem or a disguised reproving of the same blocker;
- witness decision:
  keep `T_t` existential;
  early extraction is still wrapper drift only;
- bounded-pass verdict:
  no compile-clean Lean landing occurred;
  unsupported residue was found and removed from the route notes:
  the black-box use of the current finite-family theorem was too optimistic.
Supervision correction (`2026-04-15 14:05 UTC`): the first honest obstruction inside the current theorem-3 shell limit theorem is now sharper. The route still sits at `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`, but the first failing local step is not the final strong-topology basis call.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T14:05:00Z`):

- direct reading consequence:
  the next theorem is still
  `section43_fixedTimeShellRawCLM_tendsto_exists_fixedTime`;
- exact internal decomposition now source-tested:
  boundary-value pointwise limit data,
  common finite seminorm control,
  complex bounded-set finite nets,
  finite-net-to-`MapsTo`,
  strong-topology neighborhood basis;
- exact first obstruction found by the live insertion attempt:
  the complex bounded-set finite-net step is not yet callable on
  `SchwartzMap (NPointDomain d (n + m)) ℂ`
  because Lean does not have
  `NuclearSpace (SchwartzMap (NPointDomain d (n + m)) ℂ)` in scope there;
- reading verdict:
  blocker classification is `(d)` another exact source-backed sub-obligation,
  namely a local nuclearity / finite-net transport to the actual shell test-space domain;
- route consequence:
  the old coarse label `(a) bounded-set finite-net to eventual-MapsTo assembly`
  is too imprecise now;
  the first missing bridge is before `MapsTo`, at the finite-net theorem application itself.
Supervision correction (`2026-04-15 20:51 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the natural local factorization through the constant `h y` still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:51:28Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.
Supervision correction (`2026-04-15 20:51 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the natural local factorization through the constant `h y` still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:51:28Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.
Supervision correction (`2026-04-15 20:56 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the natural local factorization through the constant `h y` still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T20:56:29Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.
Supervision correction (`2026-04-15 21:01 UTC`): one bounded reread of the exact live seam reconfirmed that there is still no honest retained Lean step below the current `hy` branch. After the complement indicator is removed, the branch is exactly the unmasked fixed-`y` shell scalar limit, and even the natural local factorization through the constant `h y` still needs the same missing complement-side shell coefficient limit. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-15`, current bounded pass, `2026-04-15T21:01:23Z`):

- direct reading consequence:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
- exact reread of the first remaining local branch:
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4555),
  after
  `simp only [F, indicator_of_mem hy]`,
  the theorem body literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- exact reread of what still feeds that branch:
  theorem-local `F` and `indicator_of_mem hy` expose the unmasked scalar;
  the complement-eventual-bound theorem at line `4430` supplies domination only;
  the generic DCT theorem at line `4566` remains only a consumer once such pointwise limits already exist;
  the quotient API in [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still controls equality only on `section43PositiveEnergyRegion`, not on its complement;
- exact reading verdict:
  no further in-body refactor survives honestly;
  even the natural local factorization
  coefficient-limit `->` multiply by the constant `h y`
  is not retainable, because the coefficient-limit theorem is exactly the missing blocker and does not already exist in the live source or OS II formula `(5.4)`;
- exact insertion surface and source status:
  this remains the direct missing supplier for `hlimit_os` in
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9701);
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only the fixed-time semigroup / analytic-continuation package and no separate complement-side shell or coefficient theorem below this branch.
Supervision correction (`2026-04-16 01:21 UTC`, bounded reread): reread the mandated sources plus the live theorem body, the immediately following generic dominated-convergence closure, the earlier `hlimit_os` case-(3) decomposition note, the nearest quotient lemmas, and OS II formula `(5.4)` on printed page `291`. No honest retained Lean step was found below the current complement branch. After `simp only [F, indicator_of_mem hy]`, the body still asks for the same fixed-`y` complement-side scalar shell limit; pulling out `h y` still only exposes the same canonical-shell coefficient limit; the generic dominated-convergence theorem still assumes exactly that pointwise limit as `hlim`; the quotient API still controls `h` only on `section43PositiveEnergyRegion`; the later `hlimit_os` analysis still fails first in outside-region case `(3)`; and OS II `(5.4)` still gives only the fixed-time semigroup / one-variable analytic-continuation statement. No production Lean edit was made.

Bounded theorem-3 reading correction on the same live actual-shell route (`2026-04-16`, current bounded pass, `2026-04-16T01:21Z`):

- direct reread of the branch goal:
  the live theorem remains
  `section43_fixedTimeShellRaw_tendsto_zero_on_section43PositiveEnergyRegion_compl`
  at [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4514);
  in the branch
  `hy : y ∈ (section43PositiveEnergyRegion d (n + m))ᶜ`,
  after
  `simp only [F, indicator_of_mem hy]`,
  the body still literally asks for
  `Filter.Tendsto
    (fun ε : ℝ =>
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
      h y)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds 0)`;
- direct reread of why factoring out `h y` is not progress:
  the only natural local refactor is still to view `h y` as a constant scalar
  and reduce to the coefficient limit for the same shell family;
  that does not lower the route, because neither `hy` nor `hq` says anything
  about the complement value `h y`;
- direct reread of the nearest source objects:
  the complement-eventual-bound theorem at line `4430` still supplies domination only;
  the generic dominated-convergence closure at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4566)
  still requires the same pointwise limit as input `hlim`;
  the quotient API lemmas at [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:106)
  and [Section43Codomain.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/Section43Codomain.lean:121)
  still stop on `section43PositiveEnergyRegion`;
  the later `hlimit_os` note at
  [OSToWightmanPositivity.lean](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9813)
  still shows the first unresolved case is outside-region case `(3)`;
  OS II page index `10` / printed page `291`, formula `(5.4)`, still gives only
  the fixed-time semigroup / one-variable analytic-continuation package with
  distributional dependence on the remaining variables;
- exact reading verdict:
  the first missing mathematics remains the complement-side coefficient limit for
  the canonical shell family;
  equivalently, no reread source presently gives the actual-shell outside-region
  contribution any complement-localization or quotient-zero-on-complement
  control below this branch.

Supervision correction (`2026-04-16`, bounded theorem-(1) reread on the actual flattened seam): no honest Lean edit survived; this pass was docs-only.

- direct reread now fixes the exact near-source gap more sharply:
  theorem (1) is **not** blocked by missing flatten transport;
  it is blocked because the available flattened FL source only yields
  continuity on the open tube, not boundary continuity at real points;
- exact source chain reread:
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime`
  gives the fixed-time weak BV functional;
  `section43_fixedTime_xiShift_hasGlobalForwardTubeGrowth` gives the growth
  input;
  `schwartz_bv_to_flat_repr` and the flattened FL package in
  `OSToWightmanBoundaryValueLimits` move that data to the flat tube;
  `SCV.fourierLaplaceExtMultiDim_continuousOn` stops at interior continuity on
  `SCV.TubeDomain (ForwardConeFlat d (n + m))`;
- exact reread verdict:
  there is still no public theorem giving
  `ContinuousWithinAt G_t
    (SCV.TubeDomain (ForwardConeFlat d (n + m))) (SCV.realEmbed xflat)`
  on a real open set inside the flattened complement image;
- blocker classification after this reread:
  continuity formulation mismatch, not localizer transport and not the later
  DCT bound.
Supervision correction (`2026-04-16`, reading note on the exact local-open theorem shape and its continuity hypotheses):
this pass is docs-only.

- reread
  `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156):
  it supplies only compact-support Schwartz pairing recovery on an open `U`,
  and still assumes
  `∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)`;
- reread
  `SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn` at
  [OSReconstruction/SCV/DistributionalUniqueness.lean:1507](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/DistributionalUniqueness.lean:1507):
  this is the exact endpoint for the local-open route;
  it turns those pairings into `Set.EqOn`, but only once both real traces are
  `ContinuousOn` on the entire same open neighborhood;
- reread
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  the exact FL-side boundary continuity theorem is still `sorry`;
- reread
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686):
  the shifted branch already has the right open-neighborhood continuity theorem
  surface, but only as a wrapper over the live theorem-(1) `sorry`, so it does
  not count as current proved source;
- reading conclusion:
  the smallest honest theorem above `hrepr_boundary_shifted` is
  an open-neighborhood boundary-agreement theorem
  `∃ Uflat, IsOpen Uflat ∧ xflat0 ∈ Uflat ∧ Set.EqOn g h Uflat`,
  where `g` is the shifted flattened `bvt_F` trace and `h` is the exact
  `fourierLaplaceExtMultiDim ... Tflat` trace for the same witness;
- continuity conclusion:
  this route genuinely needs an open neighborhood plus continuity for both
  traces on that neighborhood;
  witness-local continuity at one point is not enough for the proved SCV route;
- insertion conclusion:
  if reopened, this theorem belongs immediately below
  `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`,
  and its value at `xflat0` is the direct supplier of
  `hrepr_boundary_shifted`.

Supervision correction (`2026-04-16`, reading note on the exact circularity of the shifted-side continuity package):
this pass is docs-only.

- reread the three exact positivity theorems at
  [OSToWightmanPositivity.lean:4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [OSToWightmanPositivity.lean:4630](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4630),
  and
  [OSToWightmanPositivity.lean:4686](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686);
- source fact:
  the open-neighborhood theorem at `4686` is only a packaging layer over the
  pointwise flattened theorem at `4630`, and that theorem in turn immediately
  calls the live theorem-(1) `sorry` at `4583`;
- exact circular chain on reread:
  `localFlatContinuity (4686)`
  → `pointwiseFlatContinuity (4630)`
  → `pointwiseContinuity (~4600)`
  → `section43_bvt_F_continuousWithinAt_shifted... (4583)`
  → theorem-(1) live `sorry`;
- reading correction:
  for the local-open SCV route, the smallest useful non-circular replacement is
  not the pointwise theorem at `4630`;
  the route genuinely needs the open-neighborhood statement with the same shape
  as `4686`, because `LocalBoundaryRecovery` plus
  `eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`
  need continuity on an open set, not only at one point;
- exact theorem surface to keep in mind:
  after fixing
  `q := n + m`,
  `j := ⟨n, Nat.lt_add_of_pos_right hm⟩`,
  and
  `G_t zflat :=
    bvt_F OS lgc q
      (xiShift j 0 ((flattenCLEquiv q (d + 1)).symm zflat) (t : ℂ))`,
  prove an honest
  `∃ Uflat, IsOpen Uflat ∧
      flattenCLEquivReal q (d + 1) y ∈ Uflat ∧
      Uflat ⊆ (flattenCLEquivReal q (d + 1)) ''
        ((section43PositiveEnergyRegion d q)ᶜ) ∧
      ∀ xflat ∈ Uflat, ContinuousWithinAt G_t
        (SCV.TubeDomain (ForwardConeFlat d q))
        (SCV.realEmbed xflat)`;
- reread verdict on upstream supply:
  no proved upstream theorem already gives this from the live witness package;
  the only nearby stronger source is the regular package
  `SCV.HasFourierLaplaceReprRegular`, which assumes the continuity rather than
  proving it from the current witness data;
- FL-side reread verdict:
  the corresponding exact FL theorem
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` is still `sorry`,
  so both sides of the local-open route still need trustworthy open-neighborhood
  continuity theorems.

Supervision correction (`2026-04-16`, reread note on the primitive FL real-boundary direct proof attempt):
this pass is docs-only.

- reread
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  exact target is
  `ContinuousWithinAt (fourierLaplaceExtMultiDim ...) (SCV.TubeDomain C) (SCV.realEmbed x)`;
- reread
  `SCV.realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510):
  this only gives the approach path
  `x + i ε η → realEmbed x` inside `nhdsWithin`;
- reread
  `SCV.fourierLaplaceExtMultiDim_boundaryValue` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288):
  this only gives distributional convergence of the pairings
  `∫ F(x+iεη) f(x) dx`;
- reread
  `SCV.HasFourierLaplaceReprRegular` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118):
  the needed fields
  `boundary_continuous` and `tube_continuousWithinAt` are present only as
  assumptions of the stronger regular package.

Reading conclusion:

- the direct proof attempt fails exactly because no existing source theorem says
  the scalar values
  `fourierLaplaceExtMultiDim(...)(x+iεη)` converge to the assigned real-boundary
  value `fourierLaplaceExtMultiDim(...)(realEmbed x)`;
- the smallest honest missing FL-side theorem is therefore a pointwise
  boundary-ray limit theorem for `fourierLaplaceExtMultiDim`, not the full
  regular-package upgrade and not a topology helper;
- once that raywise limit exists, the already-proved path theorem at line
  `3510` should compose directly to produce
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed`.

Supervision correction (`2026-04-16`, reread note after extracting the exact interior continuity helper below the primitive FL target):
this pass is docs-only.

- reread
  `SCV.fourierLaplaceExtMultiDim_continuousOn` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3204](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3204):
  it is only an interior theorem on `SCV.TubeDomain C`;
- reread
  `continuous_multiDimPsiZExt_comp_of_mem_tube` at
  [2739](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:2739):
  this is the only genuinely smaller continuity helper nearby, and it requires
  the parameter map to stay in the tube for every parameter value;
- reread
  `SCV.realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [3510](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510):
  the interior ray satisfies the helper only for `ε > 0`, not at the boundary
  endpoint `ε = 0`;
- reread
  the comments at
  [3865](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3865)
  and
  [4303](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4303):
  source still explicitly says the boundary value is distributional, not
  pointwise in general.

Reading conclusion:

- the direct `continuousOn` route fails because the real boundary point is not
  in the open tube where continuity is proved;
- the tiny-helper route also fails because the only nearby helper stops at maps
  landing entirely inside the tube and does not reach `realEmbed x`;
- the first honest missing item is therefore not a generic topology bridge but
  an upstream boundary-valued regularity theorem or extra hypothesis for the
  primitive Fourier-Laplace object;
- that theorem-sized gap belongs in
  `OSReconstruction/SCV/PaleyWienerSchwartz.lean`,
  not in the shifted-side positivity caller.

Supervision correction (`2026-04-16`, reread note after exact extraction of the primitive FL regularity fields and comments):
this pass is docs-only.

- reread
  `HasFourierLaplaceReprRegular` /
  `HasFourierLaplaceReprTempered` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:118](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:118)
  and
  [143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143):
  the exact extra fields are
  `poly_growth`, `uniform_bound`, `boundary_continuous`,
  `tube_continuousWithinAt` for the regular package, and only
  `poly_growth`, `uniform_bound` for the tempered package;
- reread
  `fourierLaplaceExtMultiDim_holomorphic`,
  `fourierLaplaceExtMultiDim_vladimirov_growth`,
  and
  `fourierLaplaceExtMultiDim_boundaryValue` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3256](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3256),
  [3304](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304),
  and
  [4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288):
  current primitive source supplies holomorphicity, Vladimirov growth, and
  only distributional boundary values;
- reread the proof comments at
  [3865](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3865)
  and
  [4303](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4303):
  they explicitly reject pointwise boundary-value convergence in general and
  explicitly allow `F(x+iεη)` to blow up like `ε⁻ᴹ`.

Reading conclusion:

- the next theorem-sized gap is not continuity-only and not a one-shot wrapper;
- the source forces a two-step chain:
  first a primitive theorem proving the exact `uniform_bound` field already
  demanded by the package interfaces, and only then a theorem producing a
  boundary-correct regular representative carrying
  `boundary_continuous` and `tube_continuousWithinAt`;
- this supersedes the earlier “ray-limit only” reading:
  the ray-limit theorem is not the first honest target, because the uniform
  boundary-ray estimate is already an exposed upstream missing field.

Supervision correction (`2026-04-16`, final theorem-1 reread note on exact source/reference scope):
this pass is docs-only.

- reread
  `HasFourierLaplaceReprRegular.uniform_bound` and
  `HasFourierLaplaceReprTempered.uniform_bound` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:126](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:126)
  and
  [151](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:151):
  the exact theorem-1 target is already fixed there as an `ε`-uniform bound
  along rays `x + i ε η`;
- reread
  `fourierLaplace_uniform_bound_near_boundary` and
  `exists_fourierLaplaceReprTempered` at
  [263](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:263)
  and
  [907](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:907):
  both confirm that current source treats this as already-supplied data, not as
  a primitive FL theorem;
- reread
  `fourierLaplaceExtMultiDim_vladimirov_growth`,
  `realPlusIEpsEta_mem_tubeDomain`,
  `realPlusIEpsEta_tendsto_nhdsWithin_realEmbed`,
  and
  `fourierLaplaceExtMultiDim_boundaryValue` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304),
  [3495](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3495),
  [3510](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3510),
  and
  [4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288):
  current primitive source gives only Vladimirov growth, ray geometry, and
  distributional boundary-value convergence;
- reread the comments at
  [4303](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4303):
  the file explicitly warns that `F(x+iεη)` may blow up as `ε → 0+`;
- reread the cited OS II estimate in the local offprint
  `references/reconstruction theorem II.pdf`:
  journal page 303 is local PDF page 24, and equation `(6.31)` still carries
  an inverse-power distance-to-boundary factor in `Re ζ`;
- reread `references/Zinoviev_1995.pdf`:
  the local file is the unrelated hep-th preprint
  “c = 1 String as the Topological Theory of the Conifold”, so it does not bear
  on theorem 1.

Reading conclusion:

- the current source/reference package gives distance-to-boundary growth and
  distributional boundary values, not theorem-1’s `ε`-uniform bound in `x`;
- theorem 1 itself is therefore the first honest missing analytic theorem on the
  present primitive FL seam;
- no honest tiny Lean helper surfaced, so this pass remained docs-only.
Supervision correction (`2026-04-16`, bounded reread on theorem-1 downstream chain):
this pass is docs-only.

- reread
  `exists_fourierLaplaceReprTempered` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:907](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:907):
  any honest theorem producing
  `HasFourierLaplaceReprTempered` for the primitive FL witness still needs
  four real inputs, and theorem 1 is exactly the missing `hunif` one;
- reread
  `fourierLaplace_schwartz_integral_convergence_local` and
  `fourierLaplace_boundary_recovery_on_open_of_tempered` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:105](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:105)
  and
  [156](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:156):
  the very first tempered-side consumer chain is
  `uniform_bound`
  -> local DCT
  -> local-open boundary recovery;
- reread
  `fourierLaplace_schwartz_integral_convergence` and
  `fourierLaplace_boundary_recovery` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:305](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:305)
  and
  [386](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:386):
  the regular route consumes the same theorem-1 field immediately through DCT,
  so there is no honest boundary-recovery theorem before theorem 1 either;
- reread
  `fourierLaplaceExtMultiDim_vladimirov_growth` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304):
  fixing compact `K ⊆ C` really does give the next smaller source-backed theorem
  after theorem 1, namely compact-slice polynomial growth for the primitive FL
  witness;
- reread
  `fourierLaplaceExtMultiDim_boundaryValue` at
  [4288](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4288):
  together with the compact-slice theorem and theorem 1, this is enough for the
  first honest primitive theorem yielding
  `HasFourierLaplaceReprTempered`, via the existing constructor surface in
  `LaplaceSchwartz.lean`;
- reread
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241)
  and the zero-extension definition nearby:
  this still cannot be the first honest boundary theorem, because it is about
  the zero extension rather than a genuine boundary-valued representative.

- refined reading conclusion:
  the sharp next theorem after theorem 1 is option `B(3)`, not the full
  tempered package yet and not the regular package yet;
- exact tightened chain:
  theorem 1
  -> primitive FL compact-slice `poly_growth`
  -> primitive FL tempered package supplier
  -> later boundary-valued regular representative theorem
  -> first honest `HasFourierLaplaceReprRegular` supplier;
- exact insertion seam:
  the future regular theorem belongs at the placeholder upgrade note in
  [OSReconstruction/SCV/LaplaceSchwartz.lean:181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:181),
  while the smaller compact-slice corollary belongs immediately after
  `fourierLaplaceExtMultiDim_vladimirov_growth` in
  `PaleyWienerSchwartz.lean`.

Supervision correction (`2026-04-16`, bounded reread on theorem-1 exact uniform-bound seam after the tempered-supplier blocker):
this pass is docs-only.

- reread
  `HasFourierLaplaceReprTempered.uniform_bound` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:151](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:151)
  through
  [154](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:154):
  theorem 1 is still exactly the live `hunif` shape
  `∀ η ∈ C, ∃ C_bd N δ, ... ‖F(x+iεη)‖ ≤ C_bd * (1 + ‖x‖)^N`;
- reread
  `exists_fourierLaplaceReprTempered` at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:907](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:907):
  the first primitive supplier theorem still needs exactly four real inputs,
  and theorem 1 is the remaining missing one;
- reread
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  it is still `sorry`, so it is not a genuine input for this bounded pass;
- reread
  `fourierLaplaceExtMultiDim_vladimirov_growth` and
  `fourierLaplaceExtMultiDim_poly_growth_on_compact` at
  [3304](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3304)
  and
  [3342](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3342):
  the compact-slice `hpoly` theorem is live, but the global growth theorem
  still leaves the inverse boundary-distance factor after substituting
  `z = x + i ε η`;
- reread
  `realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [3613](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3613):
  the ray-path theorem is proved, but it does not itself supply theorem 1;
- reread
  `fourierLaplaceExtMultiDim_boundaryValue` at
  [4398](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4398)
  through
  [4411](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4411):
  the boundary theorem remains distributional only;
- reread the nearby source comment at
  [4405](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4405)
  through
  [4408](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4408):
  the file still explicitly warns that `F(x+iεη)` may blow up as `ε → 0+`;
- reread the cited OS II page through local `PyPDF2` extraction:
  PDF page `23` / journal page `303`, equation `(6.31)`, still reads as a
  temperedness estimate with boundary dependence, not theorem-1's
  `ε`-uniform ray bound.

- reading conclusion:
  current source/reference still gives only distributional boundary values,
  compact-slice polynomial growth, and the ray path theorem;
- refined verdict:
  theorem 1 itself remains the first honest missing analytic theorem, and no
  honest theorem-sized Lean helper surfaced at the checked seam;
- placement conclusion:
  keep the theorem-1 insertion seam at
  `PaleyWienerSchwartz.lean` near
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` /
  `fourierLaplaceExtMultiDim_vladimirov_growth`.

Supervision correction (`2026-04-16`, reread note for the exact zero-extension boundary-contract seam):
this pass is docs-only.

- reread
  `fourierLaplaceExtMultiDim` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052):
  the primitive FL witness is definitionally `0` outside `TubeDomain C`;
- reread
  `fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` at
  [3241](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3241):
  the live stale target still asks for continuity of that exact zero-extended
  object at `realEmbed x`;
- reread
  `realPlusIEpsEta_mem_tubeDomain` /
  `realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` at
  [3616](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3616)
  and
  [3631](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3631):
  the canonical ray approaches the boundary from inside the tube, so it samples
  the interior branch, not the outside-tube branch;
- reread
  `regularizedKernel_pointwise` at
  [3712](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3712)
  through
  [3827](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3827)
  and the damping-limit block inside
  `fourierLaplace_boundaryValue_recovery` at
  [4331](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4331)
  through
  [4407](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:4407):
  the exact source object already present is the cutoff oscillatory Schwartz
  trace `χ · physicsFourierFlatCLM f`.

- reading conclusion:
  the current seam is a target-object mismatch, not a missing local limit
  tactic;
- refined verdict:
  no honest theorem/helper lands now, because any theorem about the live
  interior limit would target the cutoff boundary trace rather than the
  definitional outside-tube value `0`;
- downstream note:
  the tempered package still only needs theorem 1, while the stronger regular /
  local-boundary consumers are the ones that need a refined boundary-trace
  object or hypothesis.

Supervision correction (`2026-04-16`, reread note after checking the exact live primitive FL source surface):
this pass is docs-only.

- reread
  `fourierLaplaceExtMultiDim` at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3052)
  and the in-file note at
  [3236](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3236)
  through
  [3245](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3245):
  the stale theorem surface
  `SCV.fourierLaplaceExtMultiDim_continuousWithinAt_realEmbed` has already been
  removed from source, with the zero-extension mismatch recorded explicitly;
- reread
  `realPlusIEpsEta_tendsto_nhdsWithin_realEmbed` and
  `fourierLaplaceExtMultiDim_boundaryValue`:
  the live primitive outputs remain the interior-ray path theorem plus the
  distributional boundary-value theorem, not a pointwise continuity theorem for
  the ambient zero extension.

- reading conclusion:
  the smallest contract repair is already done in Lean;
- refined verdict:
  this bounded pass should update notes/docs only, not hunt for a theorem that
  is no longer present in the file;
- future work note:
  any next honest theorem-sized primitive FL step must introduce a separate
  boundary-trace object/interface if pointwise boundary data is needed.

Supervision correction (`2026-04-16`, reread note for the corrected post-contract-repair theorem-3 frontier):
this pass is docs-only.

- reread the primitive FL removal note at
  [OSReconstruction/SCV/PaleyWienerSchwartz.lean:3236](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3236)
  through
  [3247](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/PaleyWienerSchwartz.lean:3247);
- reread the live theorem-3 boundary object
  `bvt_singleSplit_xiShiftHolomorphicValue` at
  [OSToWightmanBoundaryValueLimits.lean:4901](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:4901);
- reread the actual consumer hypothesis `hHlimit` at
  [OSToWightmanBoundaryValueLimits.lean:5296](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:5296)
  through
  [5312](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean:5312);
- reread the fixed-time shell blocker proof at
  [OSToWightmanPositivity.lean:9923](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:9923)
  through
  [10181](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:10181).

- source check:
  the theorem-3 route is now bound to a genuine boundary-trace package, not to
  the removed zero-extension continuity theorem;
- source check:
  the first remaining consumer-side gap is beneath `hlimit_os`, not above it;
- source check:
  the failure is exactly the outside-region branch
  `y ∉ section43PositiveEnergyRegion d (n + m)`, where no theorem yet kills or
  rewrites the live canonical-shell integrand.

- reading conclusion:
  no honest theorem-sized Lean step is ready before that outside-region
  shell-limit theorem;
- refined verdict:
  the exact next target is the in-source ambient-vs-source shell comparison
  limit on the actual fixed-time canonical shell, and nothing smaller on the
  current theorem-3 route survives the source audit.

Supervision correction (`2026-04-16`, reread note on the exact minimal interface below the complement coefficient theorem):
this pass is docs-only.

- reread the exact source statements at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4131),
  [4583](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4583),
  [4686](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4686),
  and
  [4736](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4736);
- reread the exact local SCV consumers at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179)
  and
  [232](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:232);
- reread the exact tempered package surface at
  [OSReconstruction/SCV/LaplaceSchwartz.lean:143](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LaplaceSchwartz.lean:143)
  and the weak supplier theorem at
  [OSReconstruction/SCV/TubeBoundaryValues.lean:745](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/TubeBoundaryValues.lean:745).

- source check:
  the checked local SCV recovery theorem relevant to this branch is
  `fourierLaplace_boundary_recovery_on_open_of_tempered`, and it consumes only
  local `ContinuousWithinAt` data, not an explicit trace function;
- source check:
  the explicit-trace theorem
  `fourierLaplace_schwartz_integral_convergence_local_of_trace` exists, but it
  is not the minimal interface forced by the live positivity proof layer;
- source check:
  the positivity file already contains the shell-side local-open continuity
  theorem
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`,
  explicitly marked in-source as the exact seam beneath the coefficient limit;
- source check:
  the only remaining content below that theorem is the lower raw-`bvt_F`
  shifted-point boundary continuity statement
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`.

- reading conclusion:
  the earlier docs candidate “add an explicit pointwise trace supplier `B_t` on
  `Uflat`” was too high for the current source layer;
- refined verdict:
  the exact minimal next theorem/interface is already source-designed as the
  branch-specific shifted-point `ContinuousWithinAt` theorem in
  `OSToWightmanPositivity.lean`;
- no-wrapper feed:
  it should take only `OS`, `lgc`, `hm`, `t`, `y`, `hy`;
  the fixed-time boundary-value theorem
  `section43_fixedTimeShellRawCLM_boundaryValueData_fixedTime` remains only a
  later feeder for tempered recovery, not part of the next minimal theorem
  statement;
- verification note:
  docs-only pass; no Lean build was run.

## 2026-04-17 note — fixed-time all-directions BV package does not yet yield `htraceUflat`

Source comparison from the 01:15 UTC supervision pass:

- The landed fixed-time all-directions theorem produces `T_t` and all-direction boundary-value convergence on test integrals.
- The missing local continuity bridge for the flattened fixed-time continuation needs pointwise trace data on an open complement-side set.
- That mismatch is real and source-visible: distributional boundary values are weaker than the required pointwise `htraceUflat` hypothesis.
- So the next honest lower object is a separate local-trace supplier theorem, not a claim that the existing all-directions theorem already closes the seam by transport alone.

## 2026-04-17 note — reread of the transport layer confirms no hidden local-trace supplier

- reread
  `section43_fixedTimeShellRaw_pointwiseContinuity_of_bvt_F_at_shifted_point`
  at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4999](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:4999):
  it explicitly takes the shifted-point `ContinuousWithinAt` hypothesis as an
  input and only transports it through `xiShift`.
- reread
  `section43_bvt_F_continuousWithinAt_shifted_section43PositiveEnergyRegion_compl`
  at
  [OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5068](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5068):
  this remains the exact live missing theorem one layer below the flat/open
  continuity package.
- reread
  `section43_fixedTimeShellRaw_pointwiseFlatContinuity_on_section43PositiveEnergyRegion_compl`
  and
  `section43_fixedTimeShellRaw_localFlatContinuity_on_section43PositiveEnergyRegion_compl`
  at
  [5115](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5115)
  and
  [5171](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean:5171):
  they only transport/package `ContinuousWithinAt G_t` on a complement-side
  open set `Uflat`; they do not define a boundary function `B_t` or prove
  pointwise trace convergence.
- reread
  `SCV.fourierLaplace_schwartz_integral_convergence_local_of_trace` at
  [OSReconstruction/SCV/LocalBoundaryRecovery.lean:179](/home/claw/.openclaw/workspace/OSreconstruction/OSReconstruction/SCV/LocalBoundaryRecovery.lean:179):
  its stronger supplier contract is still separate trace `G`,
  `ContinuousOn G U`, and pointwise `htraceU`.

- reading conclusion:
  flattening and shift transport do not secretly close the seam beneath the
  complement-side local trace package;
- refined verdict:
  the honest smaller theorem-sized object remains the SCV local-of-trace
  theorem, while the actual supplier remains unready because the positivity
  file still lacks both the raw shifted-point continuity theorem and any
  function-level pointwise trace package on `Uflat`.
