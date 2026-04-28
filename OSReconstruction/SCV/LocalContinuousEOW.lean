import OSReconstruction.SCV.TubeDomainExtension

/-!
# Local Continuous Edge-of-the-Wedge Geometry

This file contains the finite-dimensional local-wedge geometry needed to
extract a local continuous edge-of-the-wedge theorem from the checked global
tube-domain proof in `TubeDomainExtension.lean`.
-/

noncomputable section

open BigOperators Topology

namespace SCV

/-- The closed coefficient simplex in `Fin m -> ℝ`. -/
def localEOWCoefficientSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {a | (∀ j, a j ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ j, a j = 1}

/-- The compact set of cone directions obtained from convex combinations of a
chosen cone basis. -/
def localEOWSimplexDirections {m : ℕ}
    (ys : Fin m → Fin m → ℝ) : Set (Fin m → ℝ) :=
  (fun a : Fin m → ℝ => ∑ j, a j • ys j) ''
    localEOWCoefficientSimplex m

def localEOWRealChart {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ) :
    (Fin m → ℝ) → Fin m → ℝ :=
  fun u a => x0 a + ∑ j, u j * ys j a

def localEOWChart {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ) :
    (Fin m → ℂ) → Fin m → ℂ :=
  fun w a => (x0 a : ℂ) + ∑ j, w j * (ys j a : ℂ)

theorem continuous_localEOWRealChart {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ) :
    Continuous (localEOWRealChart x0 ys) := by
  change Continuous (fun u : Fin m → ℝ => fun a => x0 a + ∑ j, u j * ys j a)
  fun_prop

theorem isCompact_localEOWRealChart_image {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    {B : Set (Fin m → ℝ)}
    (hB_compact : IsCompact B) :
    IsCompact (localEOWRealChart x0 ys '' B) :=
  hB_compact.image (continuous_localEOWRealChart x0 ys)

theorem localEOWChart_real_imag {m : ℕ}
    (x0 : Fin m → ℝ) (ys : Fin m → Fin m → ℝ)
    (u v : Fin m → ℝ) :
    localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) =
      fun a => (localEOWRealChart x0 ys u a : ℂ) +
        (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I := by
  ext a
  simp only [localEOWChart, localEOWRealChart]
  have hsum :
      (∑ j : Fin m, ((u j : ℂ) + (v j : ℂ) * Complex.I) * (ys j a : ℂ)) =
        (∑ j : Fin m, (u j : ℂ) * (ys j a : ℂ)) +
          (∑ j : Fin m, (v j : ℂ) * (ys j a : ℂ)) * Complex.I := by
    calc
      (∑ j : Fin m, ((u j : ℂ) + (v j : ℂ) * Complex.I) * (ys j a : ℂ))
          = ∑ j : Fin m, ((u j : ℂ) * (ys j a : ℂ) +
              ((v j : ℂ) * (ys j a : ℂ)) * Complex.I) := by
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = (∑ j : Fin m, (u j : ℂ) * (ys j a : ℂ)) +
            ∑ j : Fin m, ((v j : ℂ) * (ys j a : ℂ)) * Complex.I := by
            rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin m, (u j : ℂ) * (ys j a : ℂ)) +
            (∑ j : Fin m, (v j : ℂ) * (ys j a : ℂ)) * Complex.I := by
            rw [Finset.sum_mul]
  rw [hsum]
  rw [Complex.ofReal_add, Complex.ofReal_sum]
  simp [Complex.ofReal_mul]
  ring

theorem isCompact_localEOWCoefficientSimplex (m : ℕ) :
    IsCompact (localEOWCoefficientSimplex m) := by
  let box : Set (Fin m → ℝ) :=
    Set.Icc (0 : Fin m → ℝ) 1
  have hbox : IsCompact box :=
    isCompact_Icc
  have hsum_cont : Continuous fun a : Fin m → ℝ => ∑ j, a j := by
    fun_prop
  have hsum_closed : IsClosed {a : Fin m → ℝ | ∑ j, a j = 1} :=
    isClosed_eq hsum_cont continuous_const
  have hsimplex :
      localEOWCoefficientSimplex m =
        box ∩ {a : Fin m → ℝ | ∑ j, a j = 1} := by
    ext a
    constructor
    · intro ha
      rcases ha with ⟨hcoords, hsum⟩
      refine ⟨?_, hsum⟩
      simpa [box, Set.mem_Icc, Pi.le_def] using
        (show (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≤ 1) from
          ⟨fun i => (hcoords i).1, fun i => (hcoords i).2⟩)
    · intro ha
      rcases ha with ⟨hboxa, hsum⟩
      have hcoords : (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≤ 1) := by
        simpa [box, Set.mem_Icc, Pi.le_def] using hboxa
      exact ⟨fun i => ⟨hcoords.1 i, hcoords.2 i⟩, hsum⟩
  rw [hsimplex]
  exact hbox.inter_right hsum_closed

theorem isCompact_localEOWSimplexDirections {m : ℕ}
    (ys : Fin m → Fin m → ℝ) :
    IsCompact (localEOWSimplexDirections ys) := by
  have hcont : Continuous fun a : Fin m → ℝ => ∑ j, a j • ys j := by
    fun_prop
  exact (isCompact_localEOWCoefficientSimplex m).image hcont

theorem localEOWSimplexDirections_subset_cone {m : ℕ}
    (C : Set (Fin m → ℝ))
    (hC_conv : Convex ℝ C)
    (ys : Fin m → Fin m → ℝ)
    (hys : ∀ j, ys j ∈ C) :
    localEOWSimplexDirections ys ⊆ C := by
  rintro y ⟨a, ha, rfl⟩
  exact hC_conv.sum_mem
    (t := Finset.univ)
    (w := a)
    (z := ys)
    (by
      intro j _hj
      exact (ha.1 j).1)
    (by simpa using ha.2)
    (by
      intro j _hj
      exact hys j)

theorem localEOW_positive_imag_normalized_mem_simplex {m : ℕ}
    {ys : Fin m → Fin m → ℝ}
    {v : Fin m → ℝ}
    (hv_nonneg : ∀ j, 0 ≤ v j)
    (hv_sum_pos : 0 < ∑ j, v j) :
    ((∑ j, v j)⁻¹) • (∑ j, v j • ys j) ∈
      localEOWSimplexDirections ys := by
  let s : ℝ := ∑ j, v j
  let a : Fin m → ℝ := fun j => s⁻¹ * v j
  have hs_pos : 0 < s := by
    simpa [s] using hv_sum_pos
  have ha_nonneg : ∀ j, 0 ≤ a j := by
    intro j
    exact mul_nonneg (inv_nonneg.mpr hs_pos.le) (hv_nonneg j)
  have hv_le_sum : ∀ j, v j ≤ s := by
    intro j
    simpa [s] using
      Finset.single_le_sum (fun i _hi => hv_nonneg i) (Finset.mem_univ j)
  have ha_le_one : ∀ j, a j ≤ 1 := by
    intro j
    have hmul := mul_le_mul_of_nonneg_left (hv_le_sum j) (inv_nonneg.mpr hs_pos.le)
    have hcancel : s⁻¹ * s = 1 := inv_mul_cancel₀ (ne_of_gt hs_pos)
    simpa [a, hcancel] using hmul
  have ha_sum : ∑ j, a j = 1 := by
    calc
      ∑ j, a j = s⁻¹ * ∑ j, v j := by
        simp [a, Finset.mul_sum]
      _ = s⁻¹ * s := by simp [s]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hs_pos)
  refine ⟨a, ?_, ?_⟩
  · exact ⟨fun j => ⟨ha_nonneg j, ha_le_one j⟩, ha_sum⟩
  · simp [a, s, Finset.smul_sum, smul_smul, mul_comm]

theorem localEOW_chart_positive_polywedge_mem {m : ℕ}
    (Ωplus : Set (Fin m → ℂ))
    (E C : Set (Fin m → ℝ))
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus)
    (hC_conv : Convex ℝ C)
    (ys : Fin m → Fin m → ℝ)
    (hys : ∀ j, ys j ∈ C)
    (B : Set (Fin m → ℝ))
    (hB_compact : IsCompact B)
    (hB_E : B ⊆ E) :
    ∃ r : ℝ, 0 < r ∧
      ∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) ∈ Ωplus := by
  have hKη_compact : IsCompact (localEOWSimplexDirections ys) :=
    isCompact_localEOWSimplexDirections ys
  have hKη_C : localEOWSimplexDirections ys ⊆ C :=
    localEOWSimplexDirections_subset_cone C hC_conv ys hys
  obtain ⟨r, hrpos, hrmem⟩ :=
    hlocal_wedge B hB_compact hB_E (localEOWSimplexDirections ys) hKη_compact hKη_C
  refine ⟨r, hrpos, ?_⟩
  intro u hu v hv_nonneg hv_sum_pos hv_sum_lt
  let s : ℝ := ∑ j, v j
  let η : Fin m → ℝ := s⁻¹ • (∑ j, v j • ys j)
  have hη : η ∈ localEOWSimplexDirections ys := by
    dsimp [η, s]
    exact localEOW_positive_imag_normalized_mem_simplex hv_nonneg hv_sum_pos
  have hmem :=
    hrmem u hu η hη s (by simpa [s] using hv_sum_pos) (by simpa [s] using hv_sum_lt)
  have hpoint_eq :
      (fun a => (u a : ℂ) + (s : ℂ) * (η a : ℂ) * Complex.I) =
        (fun a =>
          (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) := by
    ext a
    have hs_ne : s ≠ 0 := by
      dsimp [s]
      exact ne_of_gt hv_sum_pos
    have hηa : η a = s⁻¹ * (∑ j, v j * ys j a) := by
      simp [η, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hscale_real : s * η a = ∑ j, v j * ys j a := by
      rw [hηa, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
    have hscale : (s : ℂ) * (η a : ℂ) = ∑ j, (v j : ℂ) * (ys j a : ℂ) := by
      rw [← Complex.ofReal_mul, hscale_real]
      simp
    simp [hscale]
  rwa [← hpoint_eq]

theorem localEOW_chart_negative_polywedge_mem {m : ℕ}
    (Ωminus : Set (Fin m → ℂ))
    (E C : Set (Fin m → ℝ))
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (hC_conv : Convex ℝ C)
    (ys : Fin m → Fin m → ℝ)
    (hys : ∀ j, ys j ∈ C)
    (B : Set (Fin m → ℝ))
    (hB_compact : IsCompact B)
    (hB_E : B ⊆ E) :
    ∃ r : ℝ, 0 < r ∧
      ∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) ∈ Ωminus := by
  have hKη_compact : IsCompact (localEOWSimplexDirections ys) :=
    isCompact_localEOWSimplexDirections ys
  have hKη_C : localEOWSimplexDirections ys ⊆ C :=
    localEOWSimplexDirections_subset_cone C hC_conv ys hys
  obtain ⟨r, hrpos, hrmem⟩ :=
    hlocal_wedge B hB_compact hB_E (localEOWSimplexDirections ys) hKη_compact hKη_C
  refine ⟨r, hrpos, ?_⟩
  intro u hu v hv_nonpos hv_sum_pos hv_sum_lt
  let w : Fin m → ℝ := fun j => -v j
  let s : ℝ := ∑ j, w j
  let η : Fin m → ℝ := s⁻¹ • (∑ j, w j • ys j)
  have hw_nonneg : ∀ j, 0 ≤ w j := by
    intro j
    exact neg_nonneg.mpr (hv_nonpos j)
  have hw_sum_pos : 0 < ∑ j, w j := by
    simpa [w] using hv_sum_pos
  have hw_sum_lt : ∑ j, w j < r := by
    simpa [w] using hv_sum_lt
  have hη : η ∈ localEOWSimplexDirections ys := by
    dsimp [η, s]
    exact localEOW_positive_imag_normalized_mem_simplex hw_nonneg hw_sum_pos
  have hmem :=
    hrmem u hu η hη s (by simpa [s] using hw_sum_pos) (by simpa [s] using hw_sum_lt)
  have hpoint_eq :
      (fun a => (u a : ℂ) - (s : ℂ) * (η a : ℂ) * Complex.I) =
        (fun a =>
          (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) := by
    ext a
    have hs_ne : s ≠ 0 := by
      dsimp [s]
      exact ne_of_gt hw_sum_pos
    have hηa : η a = s⁻¹ * (∑ j, w j * ys j a) := by
      simp [η, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hscale_real : s * η a = ∑ j, w j * ys j a := by
      rw [hηa, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
    have hscale : (s : ℂ) * (η a : ℂ) = ∑ j, (w j : ℂ) * (ys j a : ℂ) := by
      rw [← Complex.ofReal_mul, hscale_real]
      simp
    simp [hscale, w]
  rwa [← hpoint_eq]

theorem localEOW_chart_twoSided_polywedge_mem {m : ℕ}
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E C : Set (Fin m → ℝ))
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (hC_conv : Convex ℝ C)
    (ys : Fin m → Fin m → ℝ)
    (hys : ∀ j, ys j ∈ C)
    (B : Set (Fin m → ℝ))
    (hB_compact : IsCompact B)
    (hB_E : B ⊆ E) :
    ∃ r : ℝ, 0 < r ∧
      (∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) ∈ Ωplus) ∧
      (∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) ∈ Ωminus) := by
  have hKη_compact : IsCompact (localEOWSimplexDirections ys) :=
    isCompact_localEOWSimplexDirections ys
  have hKη_C : localEOWSimplexDirections ys ⊆ C :=
    localEOWSimplexDirections_subset_cone C hC_conv ys hys
  obtain ⟨r, hrpos, hrmem⟩ :=
    hlocal_wedge B hB_compact hB_E (localEOWSimplexDirections ys) hKη_compact hKη_C
  refine ⟨r, hrpos, ?_, ?_⟩
  · intro u hu v hv_nonneg hv_sum_pos hv_sum_lt
    let s : ℝ := ∑ j, v j
    let η : Fin m → ℝ := s⁻¹ • (∑ j, v j • ys j)
    have hη : η ∈ localEOWSimplexDirections ys := by
      dsimp [η, s]
      exact localEOW_positive_imag_normalized_mem_simplex hv_nonneg hv_sum_pos
    have hmem :=
      (hrmem u hu η hη s (by simpa [s] using hv_sum_pos)
        (by simpa [s] using hv_sum_lt)).1
    have hpoint_eq :
        (fun a => (u a : ℂ) + (s : ℂ) * (η a : ℂ) * Complex.I) =
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) := by
      ext a
      have hs_ne : s ≠ 0 := by
        dsimp [s]
        exact ne_of_gt hv_sum_pos
      have hηa : η a = s⁻¹ * (∑ j, v j * ys j a) := by
        simp [η, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hscale_real : s * η a = ∑ j, v j * ys j a := by
        rw [hηa, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
      have hscale : (s : ℂ) * (η a : ℂ) = ∑ j, (v j : ℂ) * (ys j a : ℂ) := by
        rw [← Complex.ofReal_mul, hscale_real]
        simp
      simp [hscale]
    rwa [← hpoint_eq]
  · intro u hu v hv_nonpos hv_sum_pos hv_sum_lt
    let w : Fin m → ℝ := fun j => -v j
    let s : ℝ := ∑ j, w j
    let η : Fin m → ℝ := s⁻¹ • (∑ j, w j • ys j)
    have hw_nonneg : ∀ j, 0 ≤ w j := by
      intro j
      exact neg_nonneg.mpr (hv_nonpos j)
    have hw_sum_pos : 0 < ∑ j, w j := by
      simpa [w] using hv_sum_pos
    have hw_sum_lt : ∑ j, w j < r := by
      simpa [w] using hv_sum_lt
    have hη : η ∈ localEOWSimplexDirections ys := by
      dsimp [η, s]
      exact localEOW_positive_imag_normalized_mem_simplex hw_nonneg hw_sum_pos
    have hmem :=
      (hrmem u hu η hη s (by simpa [s] using hw_sum_pos)
        (by simpa [s] using hw_sum_lt)).2
    have hpoint_eq :
        (fun a => (u a : ℂ) - (s : ℂ) * (η a : ℂ) * Complex.I) =
          (fun a =>
            (u a : ℂ) + (∑ j, (v j : ℂ) * (ys j a : ℂ)) * Complex.I) := by
      ext a
      have hs_ne : s ≠ 0 := by
        dsimp [s]
        exact ne_of_gt hw_sum_pos
      have hηa : η a = s⁻¹ * (∑ j, w j * ys j a) := by
        simp [η, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hscale_real : s * η a = ∑ j, w j * ys j a := by
        rw [hηa, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
      have hscale : (s : ℂ) * (η a : ℂ) = ∑ j, (w j : ℂ) * (ys j a : ℂ) := by
        rw [← Complex.ofReal_mul, hscale_real]
        simp
      simp [hscale, w]
    rwa [← hpoint_eq]

theorem localEOWChart_twoSided_polywedge_mem {m : ℕ}
    (Ωplus Ωminus : Set (Fin m → ℂ))
    (E C : Set (Fin m → ℝ))
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (hC_conv : Convex ℝ C)
    (x0 : Fin m → ℝ)
    (ys : Fin m → Fin m → ℝ)
    (hys : ∀ j, ys j ∈ C)
    (B : Set (Fin m → ℝ))
    (hB_compact : IsCompact B)
    (hB_E : localEOWRealChart x0 ys '' B ⊆ E) :
    ∃ r : ℝ, 0 < r ∧
      (∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus) ∧
      (∀ u ∈ B, ∀ v : Fin m → ℝ,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus) := by
  have hBimg_compact : IsCompact (localEOWRealChart x0 ys '' B) :=
    isCompact_localEOWRealChart_image x0 ys hB_compact
  obtain ⟨r, hrpos, hplus, hminus⟩ :=
    localEOW_chart_twoSided_polywedge_mem Ωplus Ωminus E C hlocal_wedge hC_conv ys hys
      (localEOWRealChart x0 ys '' B) hBimg_compact hB_E
  refine ⟨r, hrpos, ?_, ?_⟩
  · intro u hu v hv_nonneg hv_sum_pos hv_sum_lt
    have hmem := hplus (localEOWRealChart x0 ys u) ⟨u, hu, rfl⟩ v
      hv_nonneg hv_sum_pos hv_sum_lt
    rwa [localEOWChart_real_imag]
  · intro u hu v hv_nonpos hv_sum_pos hv_sum_lt
    have hmem := hminus (localEOWRealChart x0 ys u) ⟨u, hu, rfl⟩ v
      hv_nonpos hv_sum_pos hv_sum_lt
    rwa [localEOWChart_real_imag]

end SCV
