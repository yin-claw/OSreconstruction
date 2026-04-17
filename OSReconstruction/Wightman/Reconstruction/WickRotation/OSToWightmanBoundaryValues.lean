/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesComparison
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValueLimits
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesCompactApprox
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesEuclidean
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanPositivityOnImage
import OSReconstruction.Wightman.Reconstruction.WightmanTwoPoint

/-!
# OS to Wightman Boundary Values and Transfers

Public frontier for the boundary-value transfer layer. The valid support
infrastructure now lives across `OSToWightmanBoundaryValuesBase.lean` and the
slimmed `OSToWightmanBoundaryValuesComparison.lean`.
-/

open scoped Classical NNReal
open BigOperators Finset
open OSReconstruction

noncomputable section

variable {d : ℕ} [NeZero d]

theorem bv_cluster_transfer_of_canonical_eventually (n m : ℕ)
    (W_nm : SchwartzNPoint d (n + m) → ℂ)
    (W_n : SchwartzNPoint d n → ℂ)
    (W_m : SchwartzNPoint d m → ℂ)
    (F_nm : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ)
    (hBV_canonical : ∀ h : SchwartzNPoint d (n + m),
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d (n + m),
          F_nm (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
            (h x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_nm h)))
    (hF_cluster :
      ∀ (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (ε : ℝ), 0 < ε →
        ∃ R : ℝ, R > 0 ∧
          ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
            ∀ (g_a : SchwartzNPoint d m),
              (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
              ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
                ‖(∫ x : NPointDomain d (n + m),
                    F_nm (fun k μ =>
                      ↑(x k μ) +
                        t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                          Complex.I) *
                      ((f.tensorProduct g_a) x)) - W_n f * W_m g‖ < ε) :
    ∀ (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖W_nm (f.tensorProduct g_a) - W_n f * W_m g‖ < ε := by
  intro f g ε hε
  obtain ⟨R, hR, hcluster⟩ := hF_cluster f g (ε / 2) (by linarith)
  refine ⟨R, hR, ?_⟩
  intro a ha0 ha_large g_a hg_a
  have hBV_fg := hBV_canonical (f.tensorProduct g_a)
  rw [Metric.tendsto_nhds] at hBV_fg
  have hnearW :
      ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        dist
          (∫ x : NPointDomain d (n + m),
            F_nm (fun k μ =>
              ↑(x k μ) +
                t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
              ((f.tensorProduct g_a) x))
          (W_nm (f.tensorProduct g_a)) < ε / 2 :=
    hBV_fg (ε / 2) (by linarith)
  have hnearProd := hcluster a ha0 ha_large g_a hg_a
  have hboth :
      ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        dist
            (∫ x : NPointDomain d (n + m),
              F_nm (fun k μ =>
                ↑(x k μ) +
                  t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
                ((f.tensorProduct g_a) x))
            (W_nm (f.tensorProduct g_a)) < ε / 2 ∧
          ‖(∫ x : NPointDomain d (n + m),
              F_nm (fun k μ =>
                ↑(x k μ) +
                  t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I) *
                ((f.tensorProduct g_a) x)) - W_n f * W_m g‖ < ε / 2 :=
    hnearW.and hnearProd
  haveI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := nhdsWithin_Ioi_neBot le_rfl
  rcases hboth.exists with ⟨t, htW, htProd⟩
  have htProd' :
      dist
        (∫ x : NPointDomain d (n + m),
          F_nm (fun k μ =>
            ↑(x k μ) +
              t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
            ((f.tensorProduct g_a) x))
        (W_n f * W_m g) < ε / 2 := by
    simpa [dist_eq_norm] using htProd
  have hdist :
      dist (W_nm (f.tensorProduct g_a)) (W_n f * W_m g) < ε := by
    calc
      dist (W_nm (f.tensorProduct g_a)) (W_n f * W_m g)
          ≤ dist (W_nm (f.tensorProduct g_a))
              (∫ x : NPointDomain d (n + m),
                F_nm (fun k μ =>
                  ↑(x k μ) +
                    t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I) *
                  ((f.tensorProduct g_a) x)) +
              dist
                (∫ x : NPointDomain d (n + m),
                  F_nm (fun k μ =>
                    ↑(x k μ) +
                      t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I) *
                    ((f.tensorProduct g_a) x))
                (W_n f * W_m g) := by
            simpa [dist_comm, add_comm] using
              (dist_triangle_right
                (W_nm (f.tensorProduct g_a))
                (W_n f * W_m g)
                (∫ x : NPointDomain d (n + m),
                  F_nm (fun k μ =>
                    ↑(x k μ) +
                      t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I) *
                    ((f.tensorProduct g_a) x)))
      _ < ε / 2 + ε / 2 := by
            have hadd : dist (W_nm (f.tensorProduct g_a))
                (∫ x : NPointDomain d (n + m),
                  F_nm (fun k μ =>
                    ↑(x k μ) +
                      t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I) *
                    ((f.tensorProduct g_a) x)) +
                dist
                  (∫ x : NPointDomain d (n + m),
                    F_nm (fun k μ =>
                      ↑(x k μ) +
                        t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                          Complex.I) *
                      ((f.tensorProduct g_a) x))
                  (W_n f * W_m g) <
              ε / 2 + ε / 2 := by
                exact add_lt_add (by simpa [dist_comm] using htW) htProd'
            exact hadd
      _ = ε := by ring
  simpa [dist_eq_norm] using hdist

theorem bvt_normalized (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsNormalized d (bvt_W OS lgc) := by
  intro f
  exact bv_zero_point_is_evaluation OS lgc
    (bvt_W OS lgc 0)
    (bvt_F OS lgc 0)
    (bvt_boundary_values OS lgc 0)
    (bvt_euclidean_restriction OS lgc 0)
    f

theorem bvt_translation_invariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsTranslationInvariantWeak d (bvt_W OS lgc) := by
  intro n a f g hfg
  have hF_inv :
      ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
        bvt_F OS lgc n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
          bvt_F OS lgc n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) := by
    intro a x η ε _hε
    let aNeg : Fin (d + 1) → ℂ := fun μ => -(a μ : ℂ)
    have hz :
        (fun j => (fun μ => ↑(x j μ) + ε * ↑(η j μ) * Complex.I) + aNeg) =
          (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) := by
      funext j μ
      simp [aNeg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    calc
      bvt_F OS lgc n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
          bvt_F OS lgc n (fun j => (fun μ => ↑(x j μ) + ε * ↑(η j μ) * Complex.I) + aNeg) := by
            rw [hz.symm]
      _ = bvt_F OS lgc n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) := by
            simpa [aNeg] using
              bvt_F_translationInvariant (d := d) OS lgc n
                (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) aNeg
  exact bv_translation_invariance_transfer (d := d) n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_boundary_values OS lgc n)
    hF_inv a f g hfg

private theorem bvt_F_reflectCanonical
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      starRingEnd ℂ
        (bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I))
      =
      bvt_F OS lgc n (fun k μ =>
        ↑(x (Fin.rev k) μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) := by
  intro n x ε hε
  let η := canonicalForwardConeDirection (d := d) n
  let a : Fin (d + 1) → ℂ := fun μ =>
    if μ = 0 then (((n : ℝ) + 1) * ε : ℂ) * Complex.I else 0
  let zrev : Fin n → Fin (d + 1) → ℂ := fun k μ =>
    ↑(x k μ) + ε * ↑(η (Fin.rev k) μ) * Complex.I
  have hshift :
      bvt_F OS lgc n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I) =
        bvt_F OS lgc n zrev := by
    have hzrev :
        (fun j => (fun k μ =>
          ↑(x k μ) - ε * ↑(η k μ) * Complex.I) j + a) = zrev := by
      funext k
      funext μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [a, zrev, η, canonicalForwardConeDirection, Fin.val_rev]
        ring_nf
      · simp [a, zrev, η, canonicalForwardConeDirection, hμ]
    calc
      bvt_F OS lgc n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I)
          =
        bvt_F OS lgc n
          (fun j => (fun k μ =>
            ↑(x k μ) - ε * ↑(η k μ) * Complex.I) j + a) := by
              symm
              exact bvt_F_translationInvariant OS lgc n _ a
      _ = bvt_F OS lgc n zrev := by rw [hzrev]
  have hperm :
      bvt_F OS lgc n zrev =
        bvt_F OS lgc n (fun k μ =>
          ↑(x (Fin.rev k) μ) +
            ε * ↑(η k μ) * Complex.I) := by
    simpa [zrev] using (bvt_F_perm OS lgc n Fin.revPerm zrev).symm
  calc
    starRingEnd ℂ
        (bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(η k μ) * Complex.I))
        =
      bvt_F OS lgc n (fun k μ =>
        ↑(x k μ) -
          ε * ↑(η k μ) * Complex.I) := bvt_F_negCanonical OS lgc n x ε hε
    _ = bvt_F OS lgc n zrev := hshift
    _ = bvt_F OS lgc n (fun k μ =>
          ↑(x (Fin.rev k) μ) +
            ε * ↑(η k μ) * Complex.I) := hperm

/-- Theorem 1 frontier: Lorentz covariance of the Wick-section pairing.

OS paper target:
- OS II Theorem 4.1, p. 288 (real analyticity from `E0`, `E1`, `E2`)
- OS II Chapter V.1, pp. 290-293, especially `(5.5)`-`(5.7)` on p. 291

This sorry is the Wick-section Lorentz-covariance step on the active OS route.
It is not a same-shell comparison between Euclidean and Minkowski functionals. -/
private theorem bvt_F_lorentz_ortho_wick
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (Λ : LorentzGroup d),
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              ∑ ν, (↑((Λ⁻¹).val μ ν) : ℂ) * wickRotatePoint (x k) ν) *
                (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x)
          =
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (x k)) *
              (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x) := by
  intro n Λ φ _hφ_compact hφ_tsupport
  have hφ_coeff :
      (ZeroDiagonalSchwartz.ofClassical φ).1 = φ :=
    ZeroDiagonalSchwartz.coe_ofClassical_of_tsupport_subset_wickForwardTubeSection
      (d := d) (n := n) φ hφ_tsupport
  let Γ := wightmanToLorentzGroup (Λ⁻¹)
  have hpoint :
      ∀ x : NPointDomain d n,
        x ∈ tsupport (φ : NPointDomain d n → ℂ) →
          bvt_F OS lgc n (fun k μ =>
            ∑ ν, (↑((Λ⁻¹).val μ ν) : ℂ) * wickRotatePoint (x k) ν) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
    intro x hx
    have hx_ft : (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n := hφ_tsupport hx
    have hF_holo_BHW :
        DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using bvt_F_holomorphic OS lgc n
    have hF_dist_BHW :
        ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
          (hdet : R.det = 1) (horth : R.transpose * R = 1)
          (ψ : SchwartzNPoint d n),
            HasCompactSupport (ψ : NPointDomain d n → ℂ) →
            tsupport (ψ : NPointDomain d n → ℂ) ⊆
              {x : NPointDomain d n |
                (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n ∧
                  BHW.complexLorentzAction
                    (ComplexLorentzGroup.ofEuclidean R hdet horth)
                    (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n} →
            ∫ x : NPointDomain d n,
                bvt_F OS lgc n
                  (BHW.complexLorentzAction
                    (ComplexLorentzGroup.ofEuclidean R hdet horth)
                    (fun k => wickRotatePoint (x k))) * ψ x
              =
            ∫ x : NPointDomain d n,
                bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * ψ x := by
      intro R hdet horth ψ hψ_compact hψ_tsupport
      refine bvt_F_ofEuclidean_wick_pairing (d := d) OS lgc n R hdet horth ψ hψ_compact ?_
      intro x hx
      rcases hψ_tsupport hx with ⟨hx0, hx1⟩
      constructor
      · simpa [BHW_forwardTube_eq (d := d) (n := n)] using hx0
      · simpa [BHW_forwardTube_eq (d := d) (n := n)] using hx1
    have hx_ft_BHW : (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
      simpa [BHW_forwardTube_eq (d := d) (n := n)] using hx_ft
    have hΓ :=
      BHW.Task5Bridge.real_lorentz_invariance_from_euclidean_distributional
        (d := d) n
        (bvt_F OS lgc n)
        hF_holo_BHW
        hF_dist_BHW
        Γ (fun k => wickRotatePoint (x k)) hx_ft_BHW
    simpa [Γ, wightmanToLorentzGroup, lorentzGroupEquiv_symm_val] using hΓ
  refine MeasureTheory.integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ tsupport (φ : NPointDomain d n → ℂ)
    · simp [hpoint x hx]
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hφ0 :
          (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x) = 0 := by
        simpa [hφ_coeff] using hφx
      simp [hφ0]

/-- Theorem 2 frontier: locality / swap symmetry for the canonical BV pairing.

OS paper target:
- OS I Section 4.5 "Locality", pp. 104-105
- OS II IV.2, p. 288, which says the remaining Wightman axioms are established
  as in Sections 4.2-4.5 of OS I

This sorry is the locality transfer step on the boundary-value route. -/
private theorem bvt_F_swapCanonical_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  sorry

/- Theorem 3 frontier: positivity of the reconstructed Wightman inner product.

OS paper target:
- OS I Section 4.3 "Positivity", pp. 102-103
- OS II IV.2, p. 288, reducing the remaining Wightman axioms to the OS I
  arguments after continuation

Current active substep on the repo's OS route:
- OS II Theorem 4.3, p. 289, together with Chapter VI.1, pp. 297-298

The transformed-image / on-image positivity package now lives upstream, and the
blueprint fixes the remaining theorem-3 seam as the prior VEV /
boundary-value identification into the fixed-surrogate theorem
`bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget` in
`OSToWightmanPositivityOnImage.lean`.

That consuming theorem already fixes the narrow honest supplier surface:
- ambient supplier data: `F₀`, `m`, `hF₀`, `hEq`,
- outer on-image closure consumer data there: `G`, `hG`, `hcomp`, `hcore`,
- but the first genuinely missing upstream fixed-surrogate seam is the
  stricter producer payload localized in
  `OSToWightmanPositivityOnImage.lean` and
  `OSToWightmanBoundaryValuesComparison.lean`:
  `∃ G, hG, hcomp, hprecompact, hambientCompact, hG0, hreal`.
So the missing theorem-3 work before `bvt_W_positive` is specifically the
upstream ambient fixed-surrogate identification feeding that existing on-image
consumer theorem, not any new local retuning theorem here.

So this file no longer contains an endorsed theorem-3 supplier surface. The
local retuning/surrogate chain below is retained only as private legacy graph
structure until that upstream identification package lands.

Route discipline here:
- no same-input `W = S` shortcut,
- no transformed-image-family supplier theorem in this file,
- no wrapper reduction theorem around the later on-image package. -/
/-- Algebraic vacuum-retuning expansion used only by the legacy local chain.

This is not itself a live theorem-3 seam. It is just the quadratic expansion
for adding a vacuum-sequence multiple, reused by the retained private retuning
block below. -/
private theorem bvt_W_selfPairing_re_add_vacuumSequence
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) (c : ℂ) :
    let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
    (WightmanInnerProduct d (bvt_W OS lgc) (F + c • V) (F + c • V)).re =
      (WightmanInnerProduct d (bvt_W OS lgc) F F
        + c * WightmanInnerProduct d (bvt_W OS lgc) F V
        + starRingEnd ℂ c * WightmanInnerProduct d (bvt_W OS lgc) V F
        + starRingEnd ℂ c * c *
            WightmanInnerProduct d (bvt_W OS lgc) V V).re := by
  let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
  change (WightmanInnerProduct d (bvt_W OS lgc) (F + c • V) (F + c • V)).re =
    (WightmanInnerProduct d (bvt_W OS lgc) F F
      + c * WightmanInnerProduct d (bvt_W OS lgc) F V
      + starRingEnd ℂ c * WightmanInnerProduct d (bvt_W OS lgc) V F
      + starRingEnd ℂ c * c *
          WightmanInnerProduct d (bvt_W OS lgc) V V).re
  rw [WightmanInnerProduct_add_left (d := d) (W := bvt_W OS lgc) (bvt_W_linear (d := d) OS lgc),
    WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc) (bvt_W_linear (d := d) OS lgc),
    WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc) (bvt_W_linear (d := d) OS lgc),
    WightmanInnerProduct_smul_right (d := d) (W := bvt_W OS lgc) (bvt_W_linear (d := d) OS lgc),
    WightmanInnerProduct_smul_left (d := d) (W := bvt_W OS lgc) (bvt_W_linear (d := d) OS lgc),
    WightmanInnerProduct_smul_left (d := d) (W := bvt_W OS lgc) (bvt_W_linear (d := d) OS lgc),
    WightmanInnerProduct_smul_right (d := d) (W := bvt_W OS lgc) (bvt_W_linear (d := d) OS lgc)]
  simp only [V]
  ring_nf

private theorem bvt_W_vacuumSequence_self
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
    WightmanInnerProduct d (bvt_W OS lgc) V V = 1 := by
  let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
  simp only [V, WightmanInnerProduct]
  rw [show (Reconstruction.vacuumSequence (d := d)).bound + 1 = 2 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hv1 : (Reconstruction.vacuumSequence (d := d)).funcs 1 = 0 := rfl
  simp only [hv1, SchwartzMap.conjTensorProduct_zero_left,
    SchwartzMap.conjTensorProduct_zero_right, (bvt_W_linear (d := d) OS lgc _).map_zero, add_zero]
  show bvt_W OS lgc 0
      (((Reconstruction.vacuumSequence (d := d)).funcs 0).conjTensorProduct
        ((Reconstruction.vacuumSequence (d := d)).funcs 0)) = 1
  rw [bvt_normalized (d := d) OS lgc]
  rw [SchwartzMap.conjTensorProduct_apply]
  change (starRingEnd ℂ (1 : ℂ)) * 1 = (1 : ℂ)
  simp

private theorem bvt_W_real_vacuumSequence_retuning_range
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) (r : ℝ)
    (hr :
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re -
          ((WightmanInnerProduct d (bvt_W OS lgc) F (Reconstruction.vacuumSequence (d := d)) +
              WightmanInnerProduct d (bvt_W OS lgc) (Reconstruction.vacuumSequence (d := d)) F).re) ^ 2 / 4
        ≤ r) :
    ∃ t : ℝ,
      (WightmanInnerProduct d (bvt_W OS lgc)
          (F + ((t : ℂ) • Reconstruction.vacuumSequence (d := d)))
          (F + ((t : ℂ) • Reconstruction.vacuumSequence (d := d)))).re = r := by
  let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
  let a : ℝ := (WightmanInnerProduct d (bvt_W OS lgc) F F).re
  let b : ℝ :=
    (WightmanInnerProduct d (bvt_W OS lgc) F V +
      WightmanInnerProduct d (bvt_W OS lgc) V F).re
  let lower : ℝ := a - b ^ 2 / 4
  have hlower : lower ≤ r := by
    simpa [V, a, b, lower] using hr
  have hgap : 0 ≤ r - lower := sub_nonneg.mpr hlower
  have hquad :
      ∀ t : ℝ,
        (WightmanInnerProduct d (bvt_W OS lgc)
            (F + ((t : ℂ) • V))
            (F + ((t : ℂ) • V))).re =
          a + b * t + t ^ 2 := by
    intro t
    have h :=
      bvt_W_selfPairing_re_add_vacuumSequence
        (d := d) OS lgc F (t : ℂ)
    have hVV : WightmanInnerProduct d (bvt_W OS lgc) V V = 1 := by
      simpa [V] using bvt_W_vacuumSequence_self (d := d) OS lgc
    calc
      (WightmanInnerProduct d (bvt_W OS lgc)
          (F + ((t : ℂ) • V))
          (F + ((t : ℂ) • V))).re
          =
        a +
          (WightmanInnerProduct d (bvt_W OS lgc) F V).re * t +
          (WightmanInnerProduct d (bvt_W OS lgc) V F).re * t +
          t * t := by
            simpa [V, a, hVV, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im, Complex.conj_ofReal, mul_comm, mul_left_comm, mul_assoc]
              using h
      _ = a + b * t + t ^ 2 := by
            simp [b]
            ring
  refine ⟨Real.sqrt (r - lower) - b / 2, ?_⟩
  rw [hquad]
  have hsqrt : (Real.sqrt (r - lower)) ^ 2 = r - lower := by
    rw [Real.sq_sqrt hgap]
  calc
    a + b * (Real.sqrt (r - lower) - b / 2) +
        (Real.sqrt (r - lower) - b / 2) ^ 2
        = lower + (Real.sqrt (r - lower)) ^ 2 := by
            simp [lower]
            ring
    _ = lower + (r - lower) := by rw [hsqrt]
    _ = r := by ring

private theorem bvt_W_real_vacuumSequence_retuning_lowerBound_of_exists
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) (r : ℝ)
    (hretune :
      ∃ t : ℝ,
        (WightmanInnerProduct d (bvt_W OS lgc)
            (F + ((t : ℂ) • Reconstruction.vacuumSequence (d := d)))
            (F + ((t : ℂ) • Reconstruction.vacuumSequence (d := d)))).re = r) :
    (WightmanInnerProduct d (bvt_W OS lgc) F F).re -
        ((WightmanInnerProduct d (bvt_W OS lgc) F
              (Reconstruction.vacuumSequence (d := d)) +
            WightmanInnerProduct d (bvt_W OS lgc)
              (Reconstruction.vacuumSequence (d := d)) F).re) ^ 2 / 4 ≤
      r := by
  let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
  let a : ℝ := (WightmanInnerProduct d (bvt_W OS lgc) F F).re
  let b : ℝ :=
    (WightmanInnerProduct d (bvt_W OS lgc) F V +
      WightmanInnerProduct d (bvt_W OS lgc) V F).re
  let lower : ℝ := a - b ^ 2 / 4
  have hquad :
      ∀ t : ℝ,
        (WightmanInnerProduct d (bvt_W OS lgc)
            (F + ((t : ℂ) • V))
            (F + ((t : ℂ) • V))).re =
          a + b * t + t ^ 2 := by
    intro t
    have h :=
      bvt_W_selfPairing_re_add_vacuumSequence
        (d := d) OS lgc F (t : ℂ)
    have hVV : WightmanInnerProduct d (bvt_W OS lgc) V V = 1 := by
      simpa [V] using bvt_W_vacuumSequence_self (d := d) OS lgc
    calc
      (WightmanInnerProduct d (bvt_W OS lgc)
          (F + ((t : ℂ) • V))
          (F + ((t : ℂ) • V))).re
          =
        a +
          (WightmanInnerProduct d (bvt_W OS lgc) F V).re * t +
          (WightmanInnerProduct d (bvt_W OS lgc) V F).re * t +
          t * t := by
            simpa [V, a, hVV, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im, Complex.conj_ofReal, mul_comm, mul_left_comm, mul_assoc]
              using h
      _ = a + b * t + t ^ 2 := by
            simp [b]
            ring
  rcases hretune with ⟨t, ht⟩
  have hsq : 0 ≤ (t + b / 2) ^ 2 := sq_nonneg (t + b / 2)
  have hlower :
      lower ≤ a + b * t + t ^ 2 := by
    calc
      lower ≤ lower + (t + b / 2) ^ 2 := by nlinarith
      _ = a + b * t + t ^ 2 := by
            simp [lower]
            ring
  calc
    (WightmanInnerProduct d (bvt_W OS lgc) F F).re -
        ((WightmanInnerProduct d (bvt_W OS lgc) F
              (Reconstruction.vacuumSequence (d := d)) +
            WightmanInnerProduct d (bvt_W OS lgc)
              (Reconstruction.vacuumSequence (d := d)) F).re) ^ 2 / 4
        = lower := by simp [V, a, b, lower]
    _ ≤ a + b * t + t ^ 2 := hlower
    _ = r := by simpa [V] using (hquad t).symm.trans ht

/-- Exact real-vacuum retuning attainment criterion on the ambient side.

This is honest reusable replacement-seam content: it characterizes precisely
which real values can be attained by retuning `F` with a real multiple of the
vacuum sequence, without claiming any boundary-vanishing surrogate theorem. -/
private theorem bvt_W_real_vacuumSequence_retuning_exists_iff
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) (r : ℝ) :
    (∃ t : ℝ,
      (WightmanInnerProduct d (bvt_W OS lgc)
          (F + ((t : ℂ) • Reconstruction.vacuumSequence (d := d)))
          (F + ((t : ℂ) • Reconstruction.vacuumSequence (d := d)))).re = r) ↔
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re -
          ((WightmanInnerProduct d (bvt_W OS lgc) F
                (Reconstruction.vacuumSequence (d := d)) +
              WightmanInnerProduct d (bvt_W OS lgc)
                (Reconstruction.vacuumSequence (d := d)) F).re) ^ 2 / 4 ≤
        r := by
  constructor
  · intro hretune
    exact bvt_W_real_vacuumSequence_retuning_lowerBound_of_exists
      (d := d) OS lgc F r hretune
  · intro hr
    exact bvt_W_real_vacuumSequence_retuning_range
      (d := d) OS lgc F r hr

private theorem bvt_W_killedTarget_removedComponent_retuningOptimalGap_eq_selfPairingGap_of_le_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {n : ℕ} (hn_pos : 0 < n)
    (hprev : ∀ k, 0 < k → k < n →
      ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0)
    (hn_bound : n ≤ F.bound) :
    let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
    let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
    let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
    let q : ℝ :=
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
        WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re
    (WightmanInnerProduct d (bvt_W OS lgc) F F).re -
        (WightmanInnerProduct d (bvt_W OS lgc)
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))).re
      =
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
          WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
          WightmanInnerProduct d (bvt_W OS lgc) S S).re +
        q ^ 2 / 4 := by
  let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
  let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
  let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
  let q : ℝ :=
    (WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
      WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re
  have h_expand :
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re := by
    have hF_funcs : ∀ k, F.funcs k = (Fkill + S).funcs k := by
      intro k
      simp [Fkill, S, sub_eq_add_neg, add_assoc]
    have hW :
        WightmanInnerProduct d (bvt_W OS lgc) F F =
          WightmanInnerProduct d (bvt_W OS lgc) (Fkill + S) (Fkill + S) := by
      exact
        (WightmanInnerProduct_congr_left (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) F (Fkill + S) F hF_funcs).trans
        (WightmanInnerProduct_congr_right (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) (Fkill + S) F (Fkill + S) hF_funcs)
    rw [congrArg Complex.re hW]
    rw [WightmanInnerProduct_add_left (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc),
      WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc),
      WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc)]
    ring_nf
  have hretuned :
      (WightmanInnerProduct d (bvt_W OS lgc)
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))).re =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re - q ^ 2 / 4 := by
    let r : ℝ := q * 2⁻¹
    have hpair :=
      bvt_W_selfPairing_re_add_vacuumSequence
        (d := d) OS lgc Fkill (-((r : ℝ) : ℂ))
    have hVV : WightmanInnerProduct d (bvt_W OS lgc) V V = 1 := by
      simpa [V] using bvt_W_vacuumSequence_self (d := d) OS lgc
    calc
      (WightmanInnerProduct d (bvt_W OS lgc)
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))).re
          =
        (WightmanInnerProduct d (bvt_W OS lgc)
          (Fkill + (-((r : ℝ) : ℂ)) • V)
          (Fkill + (-((r : ℝ) : ℂ)) • V)).re := by
            have hcoef : (((q / 2 : ℝ) : ℂ) • V) = (((r : ℝ) : ℂ) • V) := by
              simp [r]
              ring
            let A : BorchersSequence d := Fkill - (((q / 2 : ℝ) : ℂ) • V)
            let B : BorchersSequence d := Fkill + (-((r : ℝ) : ℂ)) • V
            have hAB_funcs : ∀ k, A.funcs k = B.funcs k := by
              intro k
              dsimp [A, B]
              change Fkill.funcs k + -((((q / 2 : ℝ) : ℂ) • V.funcs k)) =
                Fkill.funcs k + (-((r : ℝ) : ℂ)) • V.funcs k
              have hcoef_funcs :
                  (((q / 2 : ℝ) : ℂ) • V.funcs k) = (((r : ℝ) : ℂ) • V.funcs k) := by
                simpa using congrArg (fun X : BorchersSequence d => X.funcs k) hcoef
              have hneg_funcs :
                  -((((q / 2 : ℝ) : ℂ) • V.funcs k)) = (-((r : ℝ) : ℂ)) • V.funcs k := by
                simpa [neg_smul] using congrArg Neg.neg hcoef_funcs
              exact congrArg (fun z => Fkill.funcs k + z) hneg_funcs
            have hAB :
                WightmanInnerProduct d (bvt_W OS lgc) A A =
                  WightmanInnerProduct d (bvt_W OS lgc) B B := by
              exact
                (WightmanInnerProduct_congr_left (d := d) (W := bvt_W OS lgc)
                  (hlin := bvt_W_linear (d := d) OS lgc) A B A hAB_funcs).trans
                (WightmanInnerProduct_congr_right (d := d) (W := bvt_W OS lgc)
                  (hlin := bvt_W_linear (d := d) OS lgc) B A B hAB_funcs)
            exact congrArg Complex.re hAB
      _ =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill
          + (-((r : ℝ) : ℂ)) *
              WightmanInnerProduct d (bvt_W OS lgc) Fkill V
          + starRingEnd ℂ (-((r : ℝ) : ℂ)) *
              WightmanInnerProduct d (bvt_W OS lgc) V Fkill
          + starRingEnd ℂ (-((r : ℝ) : ℂ)) * (-((r : ℝ) : ℂ)) *
              WightmanInnerProduct d (bvt_W OS lgc) V V).re := by
            simpa [V] using hpair
      _ =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re -
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
              WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) * r +
          r ^ 2 := by
            simp [r, hVV, Complex.add_re, Complex.mul_re,
              Complex.ofReal_re, Complex.ofReal_im, Complex.conj_ofReal]
            ring
      _ = (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re - q ^ 2 / 4 := by
            simp [r, q]
            ring
  have hsplit :
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill +
          WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
          WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
          WightmanInnerProduct d (bvt_W OS lgc) S S).re =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re +
          (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
              WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
              WightmanInnerProduct d (bvt_W OS lgc) S S).re := by
    simp [Complex.add_re, add_assoc]
  calc
    (WightmanInnerProduct d (bvt_W OS lgc) F F).re -
        (WightmanInnerProduct d (bvt_W OS lgc)
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))).re
        =
      ((WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re) -
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re - q ^ 2 / 4) := by
            rw [h_expand, hretuned]
    _ =
      ((WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re +
          (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
              WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
              WightmanInnerProduct d (bvt_W OS lgc) S S).re) -
        ((WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re - q ^ 2 / 4) := by
          rw [hsplit]
    _ =
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
          WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
          WightmanInnerProduct d (bvt_W OS lgc) S S).re +
        q ^ 2 / 4 := by
          ring

private theorem bvt_W_killedTarget_removedComponent_retuningOptimalGap_nonneg_of_le_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {n : ℕ} (hn_pos : 0 < n)
    (hprev : ∀ k, 0 < k → k < n →
      ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0)
    (hn_bound : n ≤ F.bound) :
    let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
    let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
    let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
    let q : ℝ :=
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
        WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re
    0 ≤
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
          WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
          WightmanInnerProduct d (bvt_W OS lgc) S S).re +
        q ^ 2 / 4 := by
  /- Route-fidelity note:
  this theorem is part of the older intrinsic boundary-vanishing correction
  chain inside `OSToWightmanBoundaryValues.lean`. The theorem-3 blueprint no
  longer treats this as the live Package-I seam. The endorsed frontier is the
  prior ambient supplier that must first produce:
  1. a boundary-vanishing surrogate `F₀`,
  2. quadratic-form equality `Re ⟪F, F⟫ = Re ⟪F₀, F₀⟫`,
  3. the exact zero-right / positive-degree transformed-image kernel inputs
     consumed upstream in `OSToWightmanPositivityOnImage.lean`.

  So this local nonnegativity statement is retained only as legacy internal
  graph structure; it should not be mistaken for the endorsed missing theorem-3
  supplier surface. No honest local proof is currently available from the
  already-imported retuning algebra alone. -/
  let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
  let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
  let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
  let q : ℝ :=
    (WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
      WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re
  have hgap :
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re -
          (WightmanInnerProduct d (bvt_W OS lgc)
            (Fkill - (((q / 2 : ℝ) : ℂ) • V))
            (Fkill - (((q / 2 : ℝ) : ℂ) • V))).re
        =
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
          WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
          WightmanInnerProduct d (bvt_W OS lgc) S S).re +
        q ^ 2 / 4 := by
    simpa [Fkill, S, V, q] using
      bvt_W_killedTarget_removedComponent_retuningOptimalGap_eq_selfPairingGap_of_le_bound
        (d := d) OS lgc F (n := n) hn_pos hprev hn_bound
  -- Exact next blocker: prove the self-pairing comparison
  -- `Re ⟪Fkill - (q/2)V, Fkill - (q/2)V⟫ ≤ Re ⟪F, F⟫`,
  -- then transport it across `hgap`.
  sorry

/-!
Legacy intrinsic surrogate chain.

The theorem-3 blueprint and the on-image Stage-5 file now agree that the live
missing supplier is upstream of this block: one must first identify the target
quadratic form with a bounded boundary-vanishing surrogate and then feed that
surrogate into the transformed-image closure package. The theorems below are
therefore retained only as private legacy local graph structure; they are not
the endorsed theorem-3 supplier interface.

Exact source-backed status of this local block:
- genuinely reusable proved ambient-side content survives only up to the
  vacuum-retuning algebra and pairing-preservation identities above, namely
  `bvt_W_real_vacuumSequence_retuning_range`,
  `bvt_W_real_vacuumSequence_retuning_lowerBound_of_exists`, and
  `bvt_W_real_vacuumSequence_retuning_exists_iff`, together with
  `bvt_W_killedTarget_removedComponent_retuningOptimalGap_eq_selfPairingGap_of_le_bound`;
- the first theorem that tries to turn that algebra into the intrinsic
  boundary-vanishing correction route is still
  `bvt_W_killedTarget_removedComponent_retuningOptimalGap_nonneg_of_le_bound`,
  which remains a live `sorry`;
- every later intrinsic surrogate constructor in this file depends downstream
  on that unresolved nonnegativity step, so none of them can be treated as a
  currently available ambient supplier for
  `bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget`.

Relevant endorsed seam:
- `OSToWightmanPositivityOnImage.lean`
- `bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget`
-/

private theorem bvt_W_killedTarget_optimalRetuning_selfPairing_le_of_le_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {n : ℕ} (hn_pos : 0 < n)
    (hprev : ∀ k, 0 < k → k < n →
      ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0)
    (hn_bound : n ≤ F.bound) :
    let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
    let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
    let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
    let q : ℝ :=
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
        WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re
    (WightmanInnerProduct d (bvt_W OS lgc)
        (Fkill - (((q / 2 : ℝ) : ℂ) • V))
        (Fkill - (((q / 2 : ℝ) : ℂ) • V))).re ≤
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
  let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
  let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
  let q : ℝ :=
    (WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
      WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re
  have hquad :
      0 ≤
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re +
          q ^ 2 / 4 := by
    simpa [Fkill, S, V, q] using
      bvt_W_killedTarget_removedComponent_retuningOptimalGap_nonneg_of_le_bound
        (d := d) OS lgc F (n := n) hn_pos hprev hn_bound
  have h_expand :
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re := by
    have hF_funcs : ∀ k, F.funcs k = (Fkill + S).funcs k := by
      intro k
      simp [Fkill, S, sub_eq_add_neg, add_assoc]
    have hW :
        WightmanInnerProduct d (bvt_W OS lgc) F F =
          WightmanInnerProduct d (bvt_W OS lgc) (Fkill + S) (Fkill + S) := by
      exact
        (WightmanInnerProduct_congr_left (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) F (Fkill + S) F hF_funcs).trans
        (WightmanInnerProduct_congr_right (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) (Fkill + S) F (Fkill + S) hF_funcs)
    rw [congrArg Complex.re hW]
    rw [WightmanInnerProduct_add_left (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc),
      WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc),
      WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc)]
    ring_nf
  have hretuned :
      (WightmanInnerProduct d (bvt_W OS lgc)
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))).re =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re - q ^ 2 / 4 := by
    let r : ℝ := q * 2⁻¹
    have hpair :=
      bvt_W_selfPairing_re_add_vacuumSequence
        (d := d) OS lgc Fkill (-((r : ℝ) : ℂ))
    have hVV : WightmanInnerProduct d (bvt_W OS lgc) V V = 1 := by
      simpa [V] using bvt_W_vacuumSequence_self (d := d) OS lgc
    calc
      (WightmanInnerProduct d (bvt_W OS lgc)
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))).re
          =
        (WightmanInnerProduct d (bvt_W OS lgc)
          (Fkill + (-((r : ℝ) : ℂ)) • V)
          (Fkill + (-((r : ℝ) : ℂ)) • V)).re := by
            have hcoef : (((q / 2 : ℝ) : ℂ) • V) = (((r : ℝ) : ℂ) • V) := by
              simp [r]
              ring
            have hcoef' : (((q / 2 : ℝ) : ℂ)) = (((r : ℝ) : ℂ)) := by
              simp [r]
              ring
            let A : BorchersSequence d := Fkill - (((q / 2 : ℝ) : ℂ) • V)
            let B : BorchersSequence d := Fkill + (-((r : ℝ) : ℂ)) • V
            have hAB_funcs : ∀ k, A.funcs k = B.funcs k := by
              intro k
              dsimp [A, B]
              change Fkill.funcs k + -((((q / 2 : ℝ) : ℂ) • V.funcs k)) =
                Fkill.funcs k + (-((r : ℝ) : ℂ)) • V.funcs k
              have hcoef_funcs :
                  (((q / 2 : ℝ) : ℂ) • V.funcs k) = (((r : ℝ) : ℂ) • V.funcs k) := by
                simpa using congrArg (fun X : BorchersSequence d => X.funcs k) hcoef
              have hneg_funcs :
                  -((((q / 2 : ℝ) : ℂ) • V.funcs k)) = (-((r : ℝ) : ℂ)) • V.funcs k := by
                simpa [neg_smul] using congrArg Neg.neg hcoef_funcs
              exact congrArg (fun z => Fkill.funcs k + z) hneg_funcs
            have hAB :
                WightmanInnerProduct d (bvt_W OS lgc) A A =
                  WightmanInnerProduct d (bvt_W OS lgc) B B := by
              exact
                (WightmanInnerProduct_congr_left (d := d) (W := bvt_W OS lgc)
                  (hlin := bvt_W_linear (d := d) OS lgc) A B A hAB_funcs).trans
                (WightmanInnerProduct_congr_right (d := d) (W := bvt_W OS lgc)
                  (hlin := bvt_W_linear (d := d) OS lgc) B A B hAB_funcs)
            exact congrArg Complex.re hAB
      _ =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill
          + (-((r : ℝ) : ℂ)) *
              WightmanInnerProduct d (bvt_W OS lgc) Fkill V
          + starRingEnd ℂ (-((r : ℝ) : ℂ)) *
              WightmanInnerProduct d (bvt_W OS lgc) V Fkill
          + starRingEnd ℂ (-((r : ℝ) : ℂ)) * (-((r : ℝ) : ℂ)) *
              WightmanInnerProduct d (bvt_W OS lgc) V V).re := by
            simpa [V] using hpair
      _ =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re -
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
              WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) * r +
          r ^ 2 := by
            simp [r, hVV, Complex.add_re, Complex.mul_re,
              Complex.ofReal_re, Complex.ofReal_im, Complex.conj_ofReal]
            ring
      _ = (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re - q ^ 2 / 4 := by
            simp [r, q]
            ring
  have hsplit :
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill +
          WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
          WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
          WightmanInnerProduct d (bvt_W OS lgc) S S).re =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re +
          (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
              WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
              WightmanInnerProduct d (bvt_W OS lgc) S S).re := by
    simp [Complex.add_re, add_assoc]
  have hgoal :
      (WightmanInnerProduct d (bvt_W OS lgc)
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))
          (Fkill - (((q / 2 : ℝ) : ℂ) • V))).re ≤
        (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
    rw [h_expand, hsplit, hretuned]
    linarith
  simpa [Fkill, S, V, q] using hgoal

private theorem bvt_W_killedTarget_removedComponent_retuningQuadratic_nonneg_of_le_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {n : ℕ} (hn_pos : 0 < n)
    (hprev : ∀ k, 0 < k → k < n →
      ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0)
    (hn_bound : n ≤ F.bound) :
    let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
    let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
    let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
    0 ≤
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
          WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
          WightmanInnerProduct d (bvt_W OS lgc) S S).re +
        ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
              WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 := by
  simpa using
    bvt_W_killedTarget_removedComponent_retuningOptimalGap_nonneg_of_le_bound
      (d := d) OS lgc F (n := n) hn_pos hprev hn_bound

private theorem bvt_W_killedTarget_selfPairing_real_vacuumRetuning_lowerBound_of_le_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {n : ℕ} (hn_pos : 0 < n)
    (hprev : ∀ k, 0 < k → k < n →
      ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0)
    (hn_bound : n ≤ F.bound) :
    let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
    (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re -
        ((WightmanInnerProduct d (bvt_W OS lgc) Fkill
              (Reconstruction.vacuumSequence (d := d)) +
            WightmanInnerProduct d (bvt_W OS lgc)
              (Reconstruction.vacuumSequence (d := d)) Fkill).re) ^ 2 / 4 ≤
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
  let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
  let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
  have hquad :
      0 ≤
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re +
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
                WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 := by
    simpa [Fkill, S, V] using
      bvt_W_killedTarget_removedComponent_retuningQuadratic_nonneg_of_le_bound
        (d := d) OS lgc F (n := n) hn_pos hprev hn_bound
  have h_expand :
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re := by
    have hF_funcs : ∀ k, F.funcs k = (Fkill + S).funcs k := by
      intro k
      simp [Fkill, S, sub_eq_add_neg, add_assoc]
    have hW :
        WightmanInnerProduct d (bvt_W OS lgc) F F =
          WightmanInnerProduct d (bvt_W OS lgc) (Fkill + S) (Fkill + S) := by
      exact
        (WightmanInnerProduct_congr_left (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) F (Fkill + S) F hF_funcs).trans
        (WightmanInnerProduct_congr_right (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) (Fkill + S) F (Fkill + S) hF_funcs)
    rw [congrArg Complex.re hW]
    rw [WightmanInnerProduct_add_left (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc),
      WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc),
      WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc)]
    ring_nf
  have hgoal :
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re -
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
                WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 ≤
        (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
    have hsplit :
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re =
          (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re +
            (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
                WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
                WightmanInnerProduct d (bvt_W OS lgc) S S).re := by
      simp [Complex.add_re, add_assoc]
    rw [h_expand]
    rw [hsplit]
    linarith [hquad]
  simpa [Fkill, V] using hgoal

private theorem bvt_W_killedTarget_selfPairing_real_vacuumRetuning_exists_of_le_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {n : ℕ} (hn_pos : 0 < n)
    (hprev : ∀ k, 0 < k → k < n →
      ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0)
    (hn_bound : n ≤ F.bound) :
    let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
    let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
    ∃ t : ℝ,
      (WightmanInnerProduct d (bvt_W OS lgc)
          (Fkill + ((t : ℂ) • V))
          (Fkill + ((t : ℂ) • V))).re =
        (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  /- Exact live theorem-3 retuning attainment seam on the bounded ambient side.

  This is the narrow mathematical content still needed to discharge
  `h_intrinsicRetuning`: after removing the live degree-`n` component, a real
  vacuum retuning of `Fkill` should recover the original reconstructed
  self-pairing real part. The surrounding decomposition and lower-bound bridge
  are already in place and should stay downstream of this statement. -/
  let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
  have hinf :
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re -
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill
                (Reconstruction.vacuumSequence (d := d)) +
              WightmanInnerProduct d (bvt_W OS lgc)
                (Reconstruction.vacuumSequence (d := d)) Fkill).re) ^ 2 / 4 ≤
        (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
    simpa [Fkill] using
      bvt_W_killedTarget_selfPairing_real_vacuumRetuning_lowerBound_of_le_bound
        (d := d) OS lgc F (n := n) hn_pos hprev hn_bound
  simpa [Fkill] using
    bvt_W_real_vacuumSequence_retuning_range
      (d := d) OS lgc Fkill
      ((WightmanInnerProduct d (bvt_W OS lgc) F F).re) hinf

private theorem bvt_W_killedTarget_removedComponent_retuningLowerBound_of_le_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {n : ℕ} (hn_pos : 0 < n)
    (hprev : ∀ k, 0 < k → k < n →
      ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0)
    (hn_bound : n ≤ F.bound) :
    let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
    let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
    let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
    0 ≤
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
          WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
          WightmanInnerProduct d (bvt_W OS lgc) S S).re +
        ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
              WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 := by
  simpa using
    bvt_W_killedTarget_removedComponent_retuningQuadratic_nonneg_of_le_bound
      (d := d) OS lgc F (n := n) hn_pos hprev hn_bound

private theorem bvt_W_killedTarget_selfPairing_ge_vacuumRetuningInfimum_of_le_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {n : ℕ} (hn_pos : 0 < n)
    (hprev : ∀ k, 0 < k → k < n →
      ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0)
    (hn_bound : n ≤ F.bound) :
    let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
    let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
    (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re -
        ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
              WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 ≤
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
  let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
  let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
  have hquad :
      0 ≤
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re +
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
                WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 := by
    simpa [Fkill, S, V] using
      bvt_W_killedTarget_removedComponent_retuningLowerBound_of_le_bound
        (d := d) OS lgc F (n := n) hn_pos hprev hn_bound
  have h_expand :
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re := by
    have hF_funcs : ∀ k, F.funcs k = (Fkill + S).funcs k := by
      intro k
      simp [Fkill, S, sub_eq_add_neg, add_assoc]
    have hW :
        WightmanInnerProduct d (bvt_W OS lgc) F F =
          WightmanInnerProduct d (bvt_W OS lgc) (Fkill + S) (Fkill + S) := by
      exact
        (WightmanInnerProduct_congr_left (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) F (Fkill + S) F hF_funcs).trans
        (WightmanInnerProduct_congr_right (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) (Fkill + S) F (Fkill + S) hF_funcs)
    rw [congrArg Complex.re hW]
    rw [WightmanInnerProduct_add_left (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc),
      WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc),
      WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc)]
    ring_nf
  have hgoal :
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re -
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
                WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 ≤
        (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
    have hsplit :
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re =
          (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re +
            (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
                WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
                WightmanInnerProduct d (bvt_W OS lgc) S S).re := by
      simp [Complex.add_re, add_assoc]
    rw [h_expand]
    rw [hsplit]
    linarith [hquad]
  simpa [Fkill, V] using hgoal

private theorem bvt_W_killedTarget_removedComponent_retuningLowerBound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {n : ℕ} (hn_pos : 0 < n)
    (hprev : ∀ k, 0 < k → k < n →
      ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0) :
    let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
    let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
    let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
    0 ≤
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
          WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
          WightmanInnerProduct d (bvt_W OS lgc) S S).re +
        ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
              WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 := by
  by_cases hn_bound : n ≤ F.bound
  · simpa using
      bvt_W_killedTarget_removedComponent_retuningLowerBound_of_le_bound
        (d := d) OS lgc F (n := n) hn_pos hprev hn_bound
  · let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
    let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
    let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
    have hgt : F.bound < n := Nat.lt_of_not_ge hn_bound
    have hFn_zero : (F.funcs n : SchwartzNPoint d n) = 0 := F.bound_spec n hgt
    have hS_funcs : ∀ k, S.funcs k = 0 := by
      intro k
      by_cases hkn : k = n
      · subst hkn
        simp [S, hFn_zero]
      · simp [S, BorchersSequence.single_funcs_ne hkn (F.funcs n)]
    have hW_Fkill_S :
        WightmanInnerProduct d (bvt_W OS lgc) Fkill S = 0 := by
      rw [WightmanInnerProduct_congr_right (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) Fkill S 0 hS_funcs]
      exact WightmanInnerProduct_zero_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc) Fkill
    have hW_S_Fkill :
        WightmanInnerProduct d (bvt_W OS lgc) S Fkill = 0 := by
      rw [WightmanInnerProduct_congr_left (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) S 0 Fkill hS_funcs]
      exact WightmanInnerProduct_zero_left (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc) Fkill
    have hW_S_S :
        WightmanInnerProduct d (bvt_W OS lgc) S S = 0 := by
      rw [WightmanInnerProduct_congr_right (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) S S 0 hS_funcs]
      exact WightmanInnerProduct_zero_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc) S
    have hsq :
        0 ≤
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
                WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 := by
      nlinarith [sq_nonneg
        ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
            WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re)]
    have htarget :
        0 ≤
          (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
              WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
              WightmanInnerProduct d (bvt_W OS lgc) S S).re +
            ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
                  WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 := by
      rw [hW_Fkill_S, hW_S_Fkill, hW_S_S]
      simp
      exact hsq
    simpa [Fkill, S, V] using htarget

private theorem bvt_W_killedTarget_selfPairing_ge_vacuumRetuningInfimum
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {n : ℕ} (hn_pos : 0 < n)
    (hprev : ∀ k, 0 < k → k < n →
      ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0) :
    let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
    (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re -
        ((WightmanInnerProduct d (bvt_W OS lgc) Fkill
              (Reconstruction.vacuumSequence (d := d)) +
            WightmanInnerProduct d (bvt_W OS lgc)
              (Reconstruction.vacuumSequence (d := d)) Fkill).re) ^ 2 / 4 ≤
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
  let S : BorchersSequence d := BorchersSequence.single n (F.funcs n)
  let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
  have hquad :
      0 ≤
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re +
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
                WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 := by
    simpa [Fkill, S, V] using
      bvt_W_killedTarget_removedComponent_retuningLowerBound
        (d := d) OS lgc F (n := n) hn_pos hprev
  have h_expand :
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re =
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re := by
    have hF_funcs : ∀ k, F.funcs k = (Fkill + S).funcs k := by
      intro k
      simp [Fkill, S, sub_eq_add_neg, add_assoc]
    have hW :
        WightmanInnerProduct d (bvt_W OS lgc) F F =
          WightmanInnerProduct d (bvt_W OS lgc) (Fkill + S) (Fkill + S) := by
      exact
        (WightmanInnerProduct_congr_left (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) F (Fkill + S) F hF_funcs).trans
        (WightmanInnerProduct_congr_right (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) (Fkill + S) F (Fkill + S) hF_funcs)
    rw [congrArg Complex.re hW]
    rw [WightmanInnerProduct_add_left (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc),
      WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc),
      WightmanInnerProduct_add_right (d := d) (W := bvt_W OS lgc)
        (bvt_W_linear (d := d) OS lgc)]
    ring_nf
  have hgoal :
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re -
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill V +
                WightmanInnerProduct d (bvt_W OS lgc) V Fkill).re) ^ 2 / 4 ≤
        (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
    have hsplit :
        (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
            WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
            WightmanInnerProduct d (bvt_W OS lgc) S S).re =
          (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re +
            (WightmanInnerProduct d (bvt_W OS lgc) Fkill S +
                WightmanInnerProduct d (bvt_W OS lgc) S Fkill +
                WightmanInnerProduct d (bvt_W OS lgc) S S).re := by
      simp [Complex.add_re, add_assoc]
    rw [h_expand]
    rw [hsplit]
    linarith [hquad]
  simpa [Fkill, V]
    using hgoal

private theorem bvt_W_killedTarget_selfPairing_vacuumRetuning_exists
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {n : ℕ} (hn_pos : 0 < n)
    (hprev : ∀ k, 0 < k → k < n →
      ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0) :
    ∃ c : ℂ,
      (WightmanInnerProduct d (bvt_W OS lgc)
          ((F - BorchersSequence.single n (F.funcs n)) + c •
            Reconstruction.vacuumSequence (d := d))
          ((F - BorchersSequence.single n (F.funcs n)) + c •
            Reconstruction.vacuumSequence (d := d))).re =
        (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
  have hinf :
      (WightmanInnerProduct d (bvt_W OS lgc) Fkill Fkill).re -
          ((WightmanInnerProduct d (bvt_W OS lgc) Fkill
                (Reconstruction.vacuumSequence (d := d)) +
              WightmanInnerProduct d (bvt_W OS lgc)
                (Reconstruction.vacuumSequence (d := d)) Fkill).re) ^ 2 / 4 ≤
        (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
    simpa [Fkill] using
      bvt_W_killedTarget_selfPairing_ge_vacuumRetuningInfimum
        (d := d) OS lgc F (n := n) hn_pos hprev
  rcases bvt_W_real_vacuumSequence_retuning_range
      (d := d) OS lgc Fkill
      ((WightmanInnerProduct d (bvt_W OS lgc) F F).re) hinf with ⟨t, ht⟩
  refine ⟨(t : ℂ), ?_⟩
  simpa [Fkill] using ht

/-- Legacy private one-step correction inside the superseded intrinsic
boundary-vanishing route.

The theorem-3 blueprint no longer treats this theorem surface as the endorsed
supplier. The real missing input is an upstream VEV / boundary-value theorem
that directly supplies a fixed boundary-vanishing surrogate together with the
exact on-image closure data consumed in
`OSToWightmanPositivityOnImage.lean`. -/
private theorem bvt_W_component_boundaryVanishingCorrection
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (F : BorchersSequence d) {n : ℕ}, 0 < n → n ≤ F.bound →
      (∀ k, 0 < k → k < n →
        ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0) →
      ∃ F₁ : BorchersSequence d,
        F₁.bound ≤ F.bound ∧
        (∀ k, 0 < k → k ≤ n →
          ((F₁.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0) ∧
        (WightmanInnerProduct d (bvt_W OS lgc) F₁ F₁).re =
          (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  /- Legacy route note:
  this intrinsic correction theorem belongs to the pre-blueprint local attempt
  to manufacture the boundary-vanishing surrogate directly inside the boundary-
  values file. The current theorem-3 blueprint instead requires that surrogate,
  the quadratic-form equality, and the zero-right / transformed-image supplier
  data to come from an upstream VEV / boundary-value identification step. -/
  have hkill :
      ∀ (F : BorchersSequence d) {n : ℕ}, 0 < n → n ≤ F.bound →
        (∀ k, 0 < k → k < n →
          ((F.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0) →
        ∃ Fkill : BorchersSequence d,
          Fkill.bound ≤ F.bound ∧
          (∀ k, 0 < k → k ≤ n →
            ((Fkill.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0) := by
    intro F n hn_pos hn_bound hprev
    let Fkill : BorchersSequence d :=
      F - BorchersSequence.single n (F.funcs n)
    refine ⟨Fkill, ?_, ?_⟩
    · change max F.bound n ≤ F.bound
      simpa [max_eq_left hn_bound]
    · intro k hk_pos hk_le
      by_cases hkn : k = n
      · subst hkn
        simp [Fkill]
      · have hk_lt : k < n := by omega
        simp [Fkill, BorchersSequence.single_funcs_ne hkn (F.funcs n), hprev k hk_pos hk_lt]
  intro F n hn_pos hn_bound hprev
  let Fkill : BorchersSequence d := F - BorchersSequence.single n (F.funcs n)
  have hFkill_bound : Fkill.bound ≤ F.bound := by
    change max F.bound n ≤ F.bound
    simpa [max_eq_left hn_bound]
  have hFkill_vanish :
      ∀ k, 0 < k → k ≤ n →
        ((Fkill.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0 := by
    intro k hk_pos hk_le
    by_cases hkn : k = n
    · subst hkn
      simp [Fkill]
    · have hk_lt : k < n := by omega
      simp [Fkill, BorchersSequence.single_funcs_ne hkn (F.funcs n), hprev k hk_pos hk_lt]
  let V : BorchersSequence d := Reconstruction.vacuumSequence (d := d)
  have hscalar :
      ∃ c : ℂ,
        (WightmanInnerProduct d (bvt_W OS lgc) (Fkill + c • V) (Fkill + c • V)).re =
          (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
    simpa [Fkill, V] using
      bvt_W_killedTarget_selfPairing_vacuumRetuning_exists
        (d := d) OS lgc F (n := n) hn_pos hprev
  rcases hscalar with ⟨c, hc⟩
  refine ⟨Fkill + c • V, ?_, ?_, hc⟩
  · change max Fkill.bound V.bound ≤ F.bound
    refine max_le ?_ ?_
    · exact hFkill_bound
    · have h1 : 1 ≤ F.bound := le_trans (Nat.succ_le_of_lt hn_pos) hn_bound
      simpa [V, Reconstruction.vacuumSequence] using h1
  · intro k hk_pos hk_le
    have hkill_zero := hFkill_vanish k hk_pos hk_le
    have hV_zero :
        ((V.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) 0 = 0 := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk_pos)
      simp [V, Reconstruction.vacuumSequence]
    simp [hkill_zero, hV_zero, V]

/-- Legacy finite-stage surrogate constructor for the old intrinsic route.

This remains private compiled scaffolding only. It should not be read as the
endorsed theorem-3 supplier interface, which now lives upstream as the missing
fixed-surrogate identification feeding
`bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget`. -/
private theorem bvt_W_positive_boundaryVanishingSurrogateUpTo
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (F : BorchersSequence d) (m : ℕ), m ≤ F.bound →
      ∃ F₀ : BorchersSequence d,
        F₀.bound ≤ F.bound ∧
        (∀ n, 0 < n → n ≤ m →
          ((F₀.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0 = 0) ∧
        (WightmanInnerProduct d (bvt_W OS lgc) F F).re =
          (WightmanInnerProduct d (bvt_W OS lgc) F₀ F₀).re := by
  /- Legacy supplier note:
  this internal surrogate-construction chain is not the endorsed theorem-3
  route any more. The live route is the upstream supplier interface already
  isolated in `OSToWightmanPositivityOnImage.lean`, not an intrinsic retuning
  argument here. This theorem remains only as legacy compiled structure until
  that upstream identification package is landed. -/
  intro F m
  induction m generalizing F with
  | zero =>
      intro hm
      refine ⟨F, le_rfl, ?_, rfl⟩
      intro n hn hnm
      omega
  | succ m ihm =>
      intro hmF
      rcases ihm F (Nat.le_of_succ_le hmF) with ⟨F₀, hF₀_bound, hvanish, hEq⟩
      by_cases hstep : m + 1 ≤ F₀.bound
      · obtain ⟨F₁, hF₁_bound, hF₁_vanish, hEq_step⟩ :=
          bvt_W_component_boundaryVanishingCorrection
            (d := d) OS lgc F₀ (n := m + 1) (Nat.succ_pos m) hstep
            (by
              intro k hk_pos hk_lt
              exact hvanish k hk_pos (Nat.le_of_lt_succ hk_lt))
        refine ⟨F₁, le_trans hF₁_bound hF₀_bound, ?_, ?_⟩
        · intro n hn hnm
          exact hF₁_vanish n hn hnm
        · calc
            (WightmanInnerProduct d (bvt_W OS lgc) F F).re
                = (WightmanInnerProduct d (bvt_W OS lgc) F₀ F₀).re := hEq
            _ = (WightmanInnerProduct d (bvt_W OS lgc) F₁ F₁).re := hEq_step.symm
      · refine ⟨F₀, hF₀_bound, ?_, hEq⟩
        intro n hn hnm
        by_cases hnm1 : n = m + 1
        · subst hnm1
          have hgt : F₀.bound < m + 1 := Nat.lt_of_not_ge hstep
          have hzero : (F₀.funcs (m + 1) : SchwartzNPoint d (m + 1)) = 0 :=
            F₀.bound_spec (m + 1) hgt
          simpa [hzero]
        · have hnm' : n ≤ m := by omega
          exact hvanish n hn hnm'

/-- Legacy full-surrogate packaging for the superseded intrinsic route.

This theorem shape is stronger than the currently endorsed theorem-3 seam and
is kept only as private compiled scaffolding while the upstream fixed-surrogate
identification package feeding the existing on-image consumer theorem is not
yet implemented. -/
private theorem bvt_W_positive_boundaryVanishingSurrogate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      ∃ F₀ : BorchersSequence d,
        (∀ n, 0 < n →
          ((F₀.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0 = 0) ∧
        (WightmanInnerProduct d (bvt_W OS lgc) F F).re =
          (WightmanInnerProduct d (bvt_W OS lgc) F₀ F₀).re := by
  intro F
  rcases bvt_W_positive_boundaryVanishingSurrogateUpTo
      (d := d) OS lgc F F.bound le_rfl with
    ⟨F₀, hF₀_bound, hvanish, hEq⟩
  refine ⟨F₀, ?_, hEq⟩
  intro n hn
  by_cases hn_bound : n ≤ F.bound
  · exact hvanish n hn hn_bound
  · have hgt : F.bound < n := Nat.lt_of_not_ge hn_bound
    have hgt₀ : F₀.bound < n := lt_of_le_of_lt hF₀_bound hgt
    have hzero : (F₀.funcs n : SchwartzNPoint d n) = 0 := F₀.bound_spec n hgt₀
    simpa [hzero]

private theorem bvt_W_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re ≥ 0 := by
  /- Live-route note:
  the actual remaining theorem-3 supplier seam is no longer the intrinsic
  surrogate chain above. By the current blueprint and
  `OSToWightmanPositivityOnImage.lean`, the honest missing input is an upstream
  VEV / boundary-value identification feeding the existing fixed-surrogate
  consumer theorem
  `bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget`:
  `F₀`, `m`, `hF₀`, `hEq`, `G`, `hG`, `hcomp`, and `hcore`.
  Exact currently sourced refinement of that statement:
  in the present branch, the only file-local/on-image route that actually
  recovers this `hcore` payload is the fixed-surrogate supplier block in
  `OSToWightmanPositivityOnImage.lean`, and there the minimal extra ambient
  datum first required is
  `hF0 : ((F₀.funcs 0 : SchwartzNPoint d 0) = 0)`,
  together with the explicit family-side payload
  `hprecompact`, `hambientCompact`, `hG0`, and `hreal`.
  Source-backed obstruction at this exact caller surface:
  the retained local surrogate chain
  `bvt_W_positive_boundaryVanishingSurrogateUpTo` /
  `bvt_W_positive_boundaryVanishingSurrogate`
  only proves boundary-point vanishing for degrees `n > 0`; it does not
  construct or imply the additional degree-`0` datum
  `((F₀.funcs 0 : SchwartzNPoint d 0) = 0)` now required downstream by the
  corrected compact-family/on-image consumer package. So the present ambient
  theorem-3 caller in this file cannot honestly supply `hF0` from existing
  local source alone. More precisely, the only retained file-local correction
  algebra is the `0 < n` component-killing / vacuum-retuning chain
  `bvt_W_component_boundaryVanishingCorrection`, and its retuning direction is
  `Reconstruction.vacuumSequence`, whose degree-`0` component is nonzero.
  Concretely, the locally produced surrogate has the shape
  `F₀ = (F - BorchersSequence.single n (F.funcs n)) + c • vacuumSequence`,
  so its degree-`0` term is changed only by the vacuum direction, while the
  available retuning theorem
  `bvt_W_real_vacuumSequence_retuning_exists_iff`
  characterizes attainable **real quadratic values** under that one-parameter
  vacuum perturbation and does not solve the separate component equation
  `((F₀.funcs 0 : SchwartzNPoint d 0) = 0)`.
  Current source therefore contains no theorem here that simultaneously
  preserves the quadratic value and forces the ambient degree-`0` component to
  vanish. More sharply, after re-reading the current upstream files
  `OSToWightmanPositivityOnImage.lean`,
  `OSToWightmanBoundaryValuesCompactApprox.lean`, and
  `OSToWightmanBoundaryValuesBase.lean`, there is also no existing theorem that
  takes this fixed ambient surrogate `F₀` and honestly supplies the explicit
  family payload
  `G, hG, hcomp, hprecompact, hambientCompact, hG0`
  consumed by
  `bvt_wightmanInner_self_nonneg_of_fixed_boundaryVanishingSurrogate_onImage_supplier_of_timeShift_eq_on_positiveReals`.
  The only current explicit family constructor is the legacy compact positive-
  time package in `OSToWightmanPositivityOnImage.lean`, and every theorem on
  that surface starts from an honest `PositiveTimeBorchersSequence d` together
  with its own ambient degree-`0` zero datum. No theorem in the present
  boundary-value layer upgrades an arbitrary theorem-3 surrogate `F₀` to that
  positive-time surface or otherwise constructs the required on-image family.
  Source-first decomposition of the missing payload therefore stops even
  earlier than `hcomp`: once an honest positive-time/on-image family is in
  hand, the current compact-family cluster in
  `OSToWightmanPositivityOnImage.lean` already supplies the boundedness and
  convergence fields (`hG`, `hcomp`) via the explicit family
  `compactApproxPositiveTimeBorchers` together with
  `tendsto_compactApproxPositiveTimeBorchers_component`, and the same cluster
  also supplies `hprecompact`, `hambientCompact`, and `hG0`. The first
  genuinely missing producer piece is thus the upstream fixed-surrogate family
  constructor itself: a theorem that, for the specific bounded surrogate `F₀`,
  produces an honest `G : ℕ → BvtTransportImageSequence d` on the positive-time
  / transformed-image side. So the first missing upstream theorem surface is
  not yet another local
  `hF0`-recovery lemma here; it is an upstream fixed-surrogate supplier theorem
  producing exactly that family payload for the specific `F₀`, after which
  `component_zero_of_fixed_boundaryVanishingSurrogate_onImage_supplier` can
  recover `hF0` internally and the existing `hreal` consumer can run.
  This local theorem remains blocked only because that upstream supplier is not
  yet available; the retained private retuning chain is not the endorsed route
  to manufacture those inputs. -/
  sorry

/-- Theorem 4 frontier: cluster transfer for the canonical BV pairing.

OS paper target:
- OS I Section 4.4 "Cluster Property", p. 103
- OS II IV.2, p. 288, which delegates the remaining Wightman axioms to
  Sections 4.2-4.5 of OS I after the continuation step

This sorry is downstream of the continuation/boundary-value route and should be
proved by the OS cluster/isometry logic, not by any deleted same-shell
comparison route. -/
private theorem bvt_F_clusterCanonicalEventually_translate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
            ‖(∫ x : NPointDomain d (n + m),
                bvt_F OS lgc (n + m) (fun k μ =>
                  ↑(x k μ) +
                    t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I) *
                  ((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x)) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  sorry

private theorem bvt_F_clusterCanonicalEventually
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
              ‖(∫ x : NPointDomain d (n + m),
                  bvt_F OS lgc (n + m) (fun k μ =>
                    ↑(x k μ) +
                      t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I) *
                    ((f.tensorProduct g_a) x)) -
                bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  intro n m f g ε hε
  obtain ⟨R, hR, hcluster⟩ :=
    bvt_F_clusterCanonicalEventually_translate (d := d) OS lgc n m f g ε hε
  refine ⟨R, hR, ?_⟩
  intro a ha0 ha_large g_a hg_a
  have hga_eq :
      ∀ x : NPointDomain d m,
        g_a x = (translateSchwartzNPoint (d := d) a g) x := by
    intro x
    simpa [translateSchwartzNPoint_apply] using hg_a x
  have hfg_eq :
      ∀ x : NPointDomain d (n + m),
        (f.tensorProduct g_a) x =
          (f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x := by
    intro x
    simp [SchwartzMap.tensorProduct_apply, hga_eq (splitLast n m x)]
  filter_upwards [hcluster a ha0 ha_large] with t ht
  have hIntEq :
      ∫ x : NPointDomain d (n + m),
          bvt_F OS lgc (n + m) (fun k μ =>
            ↑(x k μ) +
              t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I) *
            ((f.tensorProduct g_a) x)
        =
      ∫ x : NPointDomain d (n + m),
          bvt_F OS lgc (n + m) (fun k μ =>
            ↑(x k μ) +
              t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I) *
            ((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x) := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall (fun x => by
      exact congrArg
        (fun z : ℂ =>
          bvt_F OS lgc (n + m) (fun k μ =>
            ↑(x k μ) +
              t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I) * z)
        (hfg_eq x))
  rw [hIntEq]
  exact ht

private theorem bvt_W_cluster
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖bvt_W OS lgc (n + m) (f.tensorProduct g_a) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  intro n m f g ε hε
  let η0 := canonicalForwardConeDirection (d := d) (n + m)
  have hη0 : InForwardCone d (n + m) η0 := canonicalForwardConeDirection_mem (d := d) (n + m)
  exact bv_cluster_transfer_of_canonical_eventually (d := d) n m
    (bvt_W OS lgc (n + m))
    (bvt_W OS lgc n)
    (bvt_W OS lgc m)
    (bvt_F OS lgc (n + m))
    (fun h => bvt_boundary_values (d := d) OS lgc (n + m) h η0 hη0)
    (bvt_F_clusterCanonicalEventually (d := d) OS lgc n m)
    f g ε hε

private theorem bvt_F_lorentz_orthoCanonical
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (Λ : LorentzGroup d),
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        bvt_F OS lgc n (fun k μ =>
          ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε *
              ↑(canonicalForwardConeDirection (d := d) n k ν) * Complex.I)) =
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) := by
  intro n Λ x ε hε
  have hΛ : LorentzGroup.IsOrthochronous Λ := LorentzGroup.zero_zero_ge_one Λ
  let η := canonicalForwardConeDirection (d := d) n
  let ΛinvC : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun μ ν => ↑((Λ⁻¹).val μ ν)
  let ΛC : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun μ ν => ↑(Λ.val μ ν)
  let FInv : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z =>
    bvt_F OS lgc n (fun k => Matrix.mulVec ΛinvC (z k))
  have hFInv_hol : DifferentiableOn ℂ FInv (ForwardTube d n) := by
    apply DifferentiableOn.comp (bvt_F_holomorphic OS lgc n)
    · intro z _hz
      apply DifferentiableAt.differentiableWithinAt
      apply differentiableAt_pi.mpr
      intro k
      apply differentiableAt_pi.mpr
      intro μ
      have hcoord : ∀ (k : Fin n) (ν : Fin (d + 1)),
          DifferentiableAt ℂ (fun w : Fin n → Fin (d + 1) → ℂ => w k ν) z :=
        fun k' ν' =>
          differentiableAt_pi.mp (differentiableAt_pi.mp differentiableAt_id k') ν'
      suffices h :
          ∀ (s : Finset (Fin (d + 1))),
            DifferentiableAt ℂ
              (fun w : Fin n → Fin (d + 1) → ℂ =>
                ∑ ν ∈ s, ΛinvC μ ν * w k ν) z by
        simpa [FInv, ΛinvC, Matrix.mulVec, dotProduct] using h Finset.univ
      intro s
      induction s using Finset.induction with
      | empty =>
          simp [differentiableAt_const]
      | @insert ν s hν ih =>
          simp only [Finset.sum_insert hν]
          exact ((differentiableAt_const _).mul (hcoord k ν)).add ih
    · intro z hz
      exact orthochronous_preserves_forward_tube (d := d) Λ⁻¹
        (LorentzGroup.IsOrthochronous.inv hΛ) z hz
  have hint_inv :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            FInv (fun k => wickRotatePoint (x k)) *
              (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x)
          =
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (x k)) *
              (((ZeroDiagonalSchwartz.ofClassical φ).1 : NPointDomain d n → ℂ) x) := by
    intro φ hφ_compact hφ_tsupport
    simpa [FInv, ΛinvC, Matrix.mulVec, dotProduct] using
      bvt_F_lorentz_ortho_wick (d := d) OS lgc n Λ φ hφ_compact hφ_tsupport
  have hpoint :=
    forwardTube_orthochronousLorentz_point_eq_of_zeroDiagonal_distributional_wickSection_eq
      (d := d) (n := n) FInv (bvt_F OS lgc n)
      hFInv_hol (bvt_F_holomorphic OS lgc n) hint_inv
      Λ hΛ x η (canonicalForwardConeDirection_mem (d := d) n) ε hε
  have hmul : (Λ⁻¹).val * Λ.val = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
    have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hmulC : ΛinvC * ΛC = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    ext μ ρ
    have hentry :
        ((Λ⁻¹).val * Λ.val) μ ρ = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) μ ρ :=
      congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => M μ ρ) hmul
    calc
      (ΛinvC * ΛC) μ ρ
        = ↑(((Λ⁻¹).val * Λ.val) μ ρ) := by
            simp [ΛinvC, ΛC, Matrix.mul_apply]
      _ = ↑((1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) μ ρ) := by
            exact congrArg (fun r : ℝ => (r : ℂ)) hentry
      _ = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) μ ρ := by
            by_cases hμρ : μ = ρ <;> simp [Matrix.one_apply, hμρ]
  have hleft :
      FInv (fun k μ =>
        ∑ ν, (↑(Λ.val μ ν) : ℂ) * (↑(x k ν) + ε * ↑(η k ν) * Complex.I))
        =
      bvt_F OS lgc n (fun k μ =>
        ↑(x k μ) + ε * ↑(η k μ) * Complex.I) := by
    unfold FInv
    congr 1
    ext k μ
    have hk :
        Matrix.mulVec ΛinvC
            (Matrix.mulVec ΛC (fun ν =>
              ↑(x k ν) + ε * ↑(η k ν) * Complex.I))
          =
        (fun ν => ↑(x k ν) + ε * ↑(η k ν) * Complex.I) := by
      rw [Matrix.mulVec_mulVec]
      rw [hmulC, Matrix.one_mulVec]
    simpa [ΛC, Matrix.mulVec, dotProduct] using congrFun hk μ
  exact hpoint.symm.trans hleft

theorem bvt_lorentz_covariant_restricted
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (Λ : LorentzGroup d)
      (f g : SchwartzNPoint d n),
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        bvt_W OS lgc n f = bvt_W OS lgc n g := by
  intro n Λ f g hfg
  exact bv_lorentz_covariance_transfer_orthochronous_of_tube_covariance (d := d) n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_boundary_values OS lgc n)
    (fun Γ _hΓ => bvt_F_lorentz_orthoCanonical (d := d) OS lgc n Γ)
    Λ (LorentzGroup.zero_zero_ge_one Λ) f g hfg

private theorem bvt_F_lorentz_restricted_wick
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (Λ : LorentzGroup d)
      (φ : SchwartzNPoint d n),
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆
          {x : NPointDomain d n | (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n} →
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              ∑ ν, (↑((Λ⁻¹).val μ ν) : ℂ) * wickRotatePoint (x k) ν) * (φ x)
          =
        ∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * (φ x) := by
  intro n Λ φ hφ_compact hφ_tsupport
  exact W_analytic_lorentz_wick_pairing_eq_of_restrictedCovariance
    (d := d) (n := n)
    (bvt_W OS lgc n)
    (bvt_W_linear OS lgc n)
    (bvt_W_continuous OS lgc n)
    (fun Γ f g hfg =>
      bvt_lorentz_covariant_restricted (d := d) OS lgc n Γ f g hfg)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.2.2.2.2
    (bvt_boundary_values OS lgc n)
    Λ φ hφ_compact hφ_tsupport

private theorem bvt_F_lorentz_restrictedCanonical
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (Λ : LorentzGroup d)
      (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        bvt_F OS lgc n (fun k μ =>
          ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k ν) * Complex.I)) =
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) := by
  intro n Λ x ε hε
  let z : Fin n → Fin (d + 1) → ℂ := fun k μ =>
    ↑(x k μ) + ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I
  have hη : InForwardCone d n (canonicalForwardConeDirection (d := d) n) :=
    canonicalForwardConeDirection_mem (d := d) n
  have hz : z ∈ ForwardTube d n := by
    have hη_abs :
        canonicalForwardConeDirection (d := d) n ∈ ForwardConeAbs d n :=
      (inForwardCone_iff_mem_forwardConeAbs
        (canonicalForwardConeDirection (d := d) n)).mp hη
    have hscaled_abs :
        ε • canonicalForwardConeDirection (d := d) n ∈ ForwardConeAbs d n :=
      forwardConeAbs_smul d n ε hε (canonicalForwardConeDirection (d := d) n) hη_abs
    rw [forwardTube_eq_imPreimage, Set.mem_setOf_eq]
    convert hscaled_abs using 1
    ext k μ
    simp [z, Pi.smul_apply, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im]
  exact W_analytic_lorentz_on_tube_of_restrictedCovariance
    (d := d) (n := n)
    (bvt_W OS lgc n)
    (bvt_W_linear OS lgc n)
    (bvt_W_continuous OS lgc n)
    (fun Γ f g hfg =>
      bvt_lorentz_covariant_restricted (d := d) OS lgc n Γ f g hfg)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.2.2.2.2
    (bvt_boundary_values OS lgc n)
    Λ z hz

/-- The reconstructed boundary-value witness already satisfies the abstract
absolute forward-tube input interface used by the reduced BHW route. This keeps
the connected Lorentz covariance lane theorem-based, rather than
special-casing the old spectrum-condition package. -/
noncomputable def bvt_absoluteForwardTubeInput
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (m : ℕ) :
    BHW.AbsoluteForwardTubeInput (d := d) m (bvt_W OS lgc (m + 1)) where
  toFun := bvt_F OS lgc (m + 1)
  holomorphic := by
    simpa [BHW_forwardTube_eq (d := d) (n := m + 1)] using
      (bvt_F_holomorphic OS lgc (m + 1))
  real_lorentz_invariant := by
    intro Λ z hz
    exact W_analytic_lorentz_on_tube_of_restrictedCovariance
      (d := d) (n := m + 1)
      (bvt_W OS lgc (m + 1))
      (bvt_W_linear OS lgc (m + 1))
      (bvt_W_continuous OS lgc (m + 1))
      (fun Λ f g hfg =>
        bvt_lorentz_covariant_restricted (d := d) OS lgc (m + 1) Λ f g hfg)
      (bvt_F OS lgc (m + 1))
      (bvt_F_holomorphic OS lgc (m + 1))
      (full_analytic_continuation_with_symmetry_growth OS lgc (m + 1)).choose_spec.2.2.2.2.2
      (bvt_boundary_values OS lgc (m + 1))
      Λ z ((BHW_forwardTube_eq (d := d) (n := m + 1)) ▸ hz)
  translation_invariant := by
    intro z c hz hzc
    exact bvt_F_translationInvariant OS lgc (m + 1) z c
  boundary_values := by
    intro f η hη
    simpa using bvt_boundary_values OS lgc (m + 1) f η hη

theorem bvt_lorentz_covariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLorentzCovariantWeak d (bvt_W OS lgc) := by
  exact bvt_lorentz_covariant_restricted (d := d) OS lgc

theorem bvt_locally_commutative (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (bvt_W OS lgc) := by
  intro n i j f g hsupp hswap
  exact bv_local_commutativity_transfer_of_swap_pairing (d := d) n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_F_swapCanonical_pairing (d := d) OS lgc n)
    i j f g hsupp hswap

theorem bvt_positive_definite (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  exact bvt_W_positive (d := d) OS lgc

theorem bvt_hermitian (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f) := by
  have hF_reflect_pairing :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            bvt_F OS lgc n (fun k μ =>
              ↑(x k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) := by
    intro n f g ε hε hfg
    exact boundary_ray_hermitian_pairing_of_F_negCanonical (d := d) n
      (bvt_F OS lgc n)
      (bvt_F_perm OS lgc n)
      (bvt_F_translationInvariant OS lgc n)
      (bvt_F_negCanonical OS lgc n)
      f g ε hε hfg
  intro n f g hfg
  exact bv_hermiticity_transfer (d := d) n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_boundary_values OS lgc n)
    (hF_reflect_pairing n)
    f g hfg

theorem bvt_positiveTime_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hWlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                  ((F : BorchersSequence d).funcs m)) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((F : BorchersSequence d).funcs m)))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  exact
    bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian
      (d := d) (OS := OS) (lgc := lgc) (bvt_hermitian (d := d) OS lgc) F hF_compact
      hWlimit

/-- Theorem 3 restated on the chosen scalar holomorphic `singleSplit_xiShift`
trace.

OS paper target:
- OS I Section 4.3 "Positivity", pp. 102-103
- OS II Theorem 4.3, p. 289
- OS II Chapter VI.1, pp. 297-298 for the current regularization / boundary-value
  substep

The OS/Schwinger side of this limit is already packaged in
`OSToWightmanBoundaryValueLimits`; the remaining content is the Wightman-side
boundary-value identification of that same scalar holomorphic function. -/
theorem bvt_positiveTime_self_nonneg_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hHlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm
              (((F : BorchersSequence d).funcs n))
              (F.ordered_tsupport n)
              (hF_compact n)
              (((F : BorchersSequence d).funcs m))
              (F.ordered_tsupport m)
              (hF_compact m) (t : ℂ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((F : BorchersSequence d).funcs m)))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  exact
    bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_hermitian
      (d := d) (OS := OS) (lgc := lgc) (bvt_hermitian (d := d) OS lgc) F hF_compact hHlimit

theorem bvt_positiveTime_self_nonneg_of_compactApprox_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hHlimit :
      ∀ N : ℕ,
        let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N
        ∀ n m (hm : 0 < m),
          Filter.Tendsto
            (fun t : ℝ =>
              bvt_singleSplit_xiShiftHolomorphicValue
                (d := d) OS lgc hm
                (((F_N : BorchersSequence d).funcs n))
                (F_N.ordered_tsupport n)
                (compactApproxPositiveTimeBorchers_component_compact F N n)
                (((F_N : BorchersSequence d).funcs m))
                (F_N.ordered_tsupport m)
                (compactApproxPositiveTimeBorchers_component_compact F N m) (t : ℂ))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds
              (bvt_W OS lgc (n + m)
                ((((F_N : BorchersSequence d).funcs n).conjTensorProduct
                  ((F_N : BorchersSequence d).funcs m)))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  exact
    bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_tendsto_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_hermitian
      (d := d) OS lgc (bvt_hermitian (d := d) OS lgc) F hHlimit

theorem bvt_positiveTime_self_nonneg_of_compactApprox_timeShift_eq_osInner
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hkernel :
      ∀ N (t : ℝ), 0 < t →
        let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N;
          WightmanInnerProduct d (bvt_W OS lgc)
            (F_N : BorchersSequence d)
            (timeShiftBorchers (d := d) t (F_N : BorchersSequence d))
          =
          OSInnerProduct d OS.S
            (F_N : BorchersSequence d)
            (timeShiftBorchers (d := d) t (F_N : BorchersSequence d))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  exact
    bvt_wightmanInner_self_nonneg_of_compactApprox_timeShift_eq_osInner
      (d := d) OS lgc F hkernel

theorem bvt_positiveTime_self_nonneg_of_compactApprox_componentwise_ofReal_eq_bvt_W_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (_hF0 : (((F : BorchersSequence d).funcs 0 : SchwartzNPoint d 0)) = 0)
    (hreal :
      ∀ N n m (hm : 0 < m) (t : ℝ), 0 < t →
        let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N;
          bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hm
            (((F_N : BorchersSequence d).funcs n))
            (F_N.ordered_tsupport n)
            (compactApproxPositiveTimeBorchers_component_compact F N n)
            (((F_N : BorchersSequence d).funcs m))
            (F_N.ordered_tsupport m)
            (compactApproxPositiveTimeBorchers_component_compact F N m) (t : ℂ)
          =
            (bvt_W OS lgc (n + m)
              (((F_N : BorchersSequence d).funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t
                  ((F_N : BorchersSequence d).funcs m))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  /-
  Source-backed surface repair (2026-04-12):
  the corrected compact-family on-image consumer exposed upstream in
  `OSToWightmanPositivityOnImage.lean`
  needs the ambient degree-`0` vanishing datum
  `(((F : BorchersSequence d).funcs 0 : SchwartzNPoint d 0)) = 0`.
  Current source does not honestly derive that datum from the legacy
  compact-shell positive-real family hypothesis `hreal` alone, so this theorem
  now exposes `hF0` explicitly at the public consumer surface rather than
  continuing to hide the exact extra input still required by the corrected OS
  route.
  -/
  exact
    bvt_wightmanInner_self_nonneg_of_compactApproxPositiveTime_onImage_of_component_zero_and_singleSplit_eq_bvt_W_on_positiveReals
      (d := d) OS lgc F _hF0 hreal

/-
Deprecated route note:

The hypothesis `hschw` below is mathematically false on the intended theorem
surface. The left-hand side is the Euclidean/OS time-shifted Schwinger pairing,
whose free-field momentum-space form carries the Laplace factor `e^{-ω_p t}`;
the right-hand side is the reconstructed Wightman boundary-value pairing
against a real Minkowski time translation, whose free-field momentum-space form
carries the oscillatory factor `e^{-i ω_p t}`.

So this theorem is a logically valid implication from a false premise. It
remains harmless compiled legacy infrastructure, but it is no longer part of
the endorsed theorem-3 route. -/
theorem bvt_positiveTime_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hschw :
      ∀ N n m (hm : 0 < m) (t : ℝ), 0 < t →
        let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers F N;
          OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            ((((F_N : BorchersSequence d).funcs n).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t
                ((F_N : BorchersSequence d).funcs m)))))
          =
            (bvt_W OS lgc (n + m)
              (((F_N : BorchersSequence d).funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t
                  ((F_N : BorchersSequence d).funcs m))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  exact
    bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian
      (d := d) OS lgc (bvt_hermitian (d := d) OS lgc) F hschw

theorem bvt_cluster (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖bvt_W OS lgc (n + m) (f.tensorProduct g_a) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  exact bvt_W_cluster (d := d) OS lgc

def constructWightmanFunctions (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    WightmanFunctions d where
  W := bvt_W OS lgc
  linear := bvt_W_linear OS lgc
  tempered := bvt_W_continuous OS lgc
  normalized := bvt_normalized OS lgc
  translation_invariant := bvt_translation_invariant OS lgc
  lorentz_covariant := bvt_lorentz_covariant OS lgc
  spectrum_condition := by
    intro n
    refine ⟨bvt_F OS lgc n, bvt_F_holomorphic OS lgc n, ?_, bvt_boundary_values OS lgc n⟩
    -- Global polynomial growth from full_analytic_continuation_with_symmetry_growth (ACR(1)).
    exact (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.2.2.2.2
  locally_commutative := bvt_locally_commutative OS lgc
  positive_definite := bvt_positive_definite OS lgc
  hermitian := bvt_hermitian OS lgc
  cluster := bvt_cluster OS lgc

/-- The OS pre-Hilbert space constructed from the Wightman functions obtained
    data. -/
def osPreHilbertSpace (OS : OsterwalderSchraderAxioms d) :=
  OSPreHilbertSpace OS

/-! ### The Bridge Theorems -/

theorem wightman_to_os_full (Wfn : WightmanFunctions d) :
    ∃ (S : SchwingerFunctions d),
      (∀ n, Continuous (S n)) ∧
      (∀ n, IsLinearMap ℂ (S n)) ∧
      IsWickRotationPair S Wfn.W := by
  refine ⟨constructZeroDiagonalSchwingerFunctions Wfn, ?_, ?_, ?_⟩
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedSchwinger_tempered_zeroDiagonal Wfn n
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedZeroDiagonalSchwinger_linear Wfn n
  intro n
  refine ⟨(W_analytic_BHW Wfn n).val,
    (W_analytic_BHW Wfn n).property.1.mono
      (ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)),
    ?_, fun _ => rfl⟩
  · intro f η hη
    exact bhw_distributional_boundary_values Wfn f η hη

theorem os_to_wightman_full (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      IsWickRotationPair OS.schwinger Wfn.W := by
  refine ⟨constructWightmanFunctions OS lgc, fun n => ?_⟩
  exact ⟨bvt_F OS lgc n,
    bvt_F_holomorphic OS lgc n,
    bvt_boundary_values OS lgc n,
    fun f => by
      simpa [OsterwalderSchraderAxioms.schwinger] using
        bvt_euclidean_restriction OS lgc n f⟩

end
