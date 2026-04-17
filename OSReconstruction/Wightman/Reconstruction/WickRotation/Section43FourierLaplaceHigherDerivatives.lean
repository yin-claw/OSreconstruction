import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceWitness

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

/-- A single derivative slot in the Section 4.3 Fourier-Laplace integrand.

`time k` means the derivative hits the Laplace exponential and contributes the
time-coordinate scalar from the direction.  `spatial i` means the derivative
hits the spatial Fourier argument and contributes the `i`th spatial-coordinate
scalar from the direction. -/
inductive Section43DerivativeAtom (d n : ℕ) where
  | time (k : Fin n)
  | spatial (i : Fin n × Fin d)
  deriving DecidableEq, Fintype

/-- A length-`r` derivative word records which factor each derivative slot hits.
The slot order follows `iteratedFDeriv_succ_apply_left`: index `0` is the
newest derivative direction when passing from `r` to `r + 1`. -/
abbrev Section43DerivativeWord (d n r : ℕ) :=
  Fin r → Section43DerivativeAtom d n

/-- The derivative atom type is the finite disjoint union of time-coordinate
atoms and spatial-coordinate atoms. -/
def section43DerivativeAtomEquivSum (d n : ℕ) :
    Section43DerivativeAtom d n ≃ (Fin n) ⊕ (Fin n × Fin d) where
  toFun
    | Section43DerivativeAtom.time k => Sum.inl k
    | Section43DerivativeAtom.spatial i => Sum.inr i
  invFun
    | Sum.inl k => Section43DerivativeAtom.time k
    | Sum.inr i => Section43DerivativeAtom.spatial i
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by
    intro a
    cases a <;> rfl

/-- Split a finite sum over derivative atoms into its time and spatial pieces. -/
theorem section43DerivativeAtom_sum
    (d n : ℕ) {M : Type*} [AddCommMonoid M]
    (f : Fin n → M) (g : Fin n × Fin d → M) :
    (∑ a : Section43DerivativeAtom d n,
      match a with
      | Section43DerivativeAtom.time k => f k
      | Section43DerivativeAtom.spatial i => g i) =
    (∑ k : Fin n, f k) + ∑ i : Fin n × Fin d, g i := by
  classical
  let e := section43DerivativeAtomEquivSum d n
  calc
    (∑ a : Section43DerivativeAtom d n,
      match a with
      | Section43DerivativeAtom.time k => f k
      | Section43DerivativeAtom.spatial i => g i) =
        ∑ s : (Fin n) ⊕ (Fin n × Fin d),
          match s with
          | Sum.inl k => f k
          | Sum.inr i => g i := by
          refine Fintype.sum_equiv e _ _ ?_
          intro a
          cases a <;> rfl
    _ = (∑ k : Fin n, f k) + ∑ i : Fin n × Fin d, g i := by
          rw [Fintype.sum_sum_type]

/-- Prepend one derivative atom to a word. -/
def section43DerivativeWordCons
    (d n r : ℕ)
    (head : Section43DerivativeAtom d n)
    (tail : Section43DerivativeWord d n r) :
    Section43DerivativeWord d n (r + 1) :=
  Fin.cons head tail

@[simp] theorem section43DerivativeWordCons_zero
    (d n r : ℕ)
    (head : Section43DerivativeAtom d n)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordCons d n r head tail 0 = head := by
  rfl

@[simp] theorem section43DerivativeWordCons_succ
    (d n r : ℕ)
    (head : Section43DerivativeAtom d n)
    (tail : Section43DerivativeWord d n r)
    (j : Fin r) :
    section43DerivativeWordCons d n r head tail j.succ = tail j := by
  rfl

/-- A nonempty derivative word is equivalently its newest atom together with
the remaining tail word. -/
def section43DerivativeWordEquivCons (d n r : ℕ) :
    Section43DerivativeWord d n (r + 1) ≃
      Section43DerivativeAtom d n × Section43DerivativeWord d n r where
  toFun a := (a 0, fun j => a j.succ)
  invFun p := section43DerivativeWordCons d n r p.1 p.2
  left_inv := by
    intro a
    funext j
    refine Fin.cases ?zero ?succ j
    · rfl
    · intro i
      rfl
  right_inv := by
    intro p
    cases p with
    | mk head tail =>
        rfl

/-- Reindex a finite sum over nonempty derivative words by newest atom and
tail word. -/
theorem section43DerivativeWord_sum_cons
    (d n r : ℕ) {M : Type*} [AddCommMonoid M]
    (f : Section43DerivativeWord d n (r + 1) → M) :
    (∑ a : Section43DerivativeWord d n (r + 1), f a) =
      ∑ head : Section43DerivativeAtom d n,
        ∑ tail : Section43DerivativeWord d n r,
          f (section43DerivativeWordCons d n r head tail) := by
  classical
  let e := section43DerivativeWordEquivCons d n r
  calc
    (∑ a : Section43DerivativeWord d n (r + 1), f a) =
        ∑ p : Section43DerivativeAtom d n × Section43DerivativeWord d n r,
          f (section43DerivativeWordCons d n r p.1 p.2) := by
          refine Fintype.sum_equiv e _ _ ?_
          intro a
          exact congrArg f (e.left_inv a).symm
    _ = ∑ head : Section43DerivativeAtom d n,
        ∑ tail : Section43DerivativeWord d n r,
          f (section43DerivativeWordCons d n r head tail) := by
          rw [Fintype.sum_prod_type]

/-- Drop the newest derivative slot from a nonempty derivative word. -/
def section43DerivativeWordTail
    (d n r : ℕ)
    (a : Section43DerivativeWord d n (r + 1)) :
    Section43DerivativeWord d n r :=
  fun j => a j.succ

@[simp] theorem section43DerivativeWordTail_cons
    (d n r : ℕ)
    (head : Section43DerivativeAtom d n)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordTail d n r
      (section43DerivativeWordCons d n r head tail) = tail := by
  rfl

/-- Drop the newest direction from a nonempty direction tuple. -/
def section43DirectionTail
    (d n r : ℕ) [NeZero d]
    (m : Fin (r + 1) → NPointDomain d n) :
    Fin r → NPointDomain d n :=
  fun j => m j.succ

@[simp] theorem section43DirectionTail_cons
    (d n r : ℕ) [NeZero d]
    (head : NPointDomain d n)
    (tail : Fin r → NPointDomain d n) :
    section43DirectionTail d n r (Fin.cons head tail) = tail := by
  rfl

/-- Number of time atoms in a derivative word.  This is the exponent of the
time-moment weight `‖τ‖ ^ K` consumed by the partial-Fourier rapid theorem. -/
def section43DerivativeWordTimeCount
    (d n : ℕ) : (r : ℕ) → Section43DerivativeWord d n r → ℕ
  | 0, _ => 0
  | r + 1, a =>
      let old := section43DerivativeWordTimeCount d n r
        (section43DerivativeWordTail d n r a)
      match a 0 with
      | Section43DerivativeAtom.time _ => old + 1
      | Section43DerivativeAtom.spatial _ => old

@[simp] theorem section43DerivativeWordTimeCount_cons_time
    (d n r : ℕ) (k : Fin n)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordTimeCount d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.time k) tail) =
      section43DerivativeWordTimeCount d n r tail + 1 := by
  rfl

@[simp] theorem section43DerivativeWordTimeCount_cons_spatial
    (d n r : ℕ) (i : Fin n × Fin d)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordTimeCount d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.spatial i) tail) =
      section43DerivativeWordTimeCount d n r tail := by
  rfl

/-- The transported Schwartz input attached to a derivative word.  Spatial atoms
apply the already compiled coordinate multiplier transport; time atoms leave the
input unchanged. -/
noncomputable def section43DerivativeWordInput
    (d n : ℕ) [NeZero d] :
    (r : ℕ) → SchwartzNPoint d n → Section43DerivativeWord d n r → SchwartzNPoint d n
  | 0, F, _ => F
  | r + 1, F, a =>
      let old := section43DerivativeWordInput d n r F
        (section43DerivativeWordTail d n r a)
      match a 0 with
      | Section43DerivativeAtom.time _ => old
      | Section43DerivativeAtom.spatial i =>
          section43SpatialMultiplierTransport d n old i

@[simp] theorem section43DerivativeWordInput_cons_time
    (d n r : ℕ) [NeZero d]
    (F : SchwartzNPoint d n) (k : Fin n)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordInput d n (r + 1) F
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.time k) tail) =
      section43DerivativeWordInput d n r F tail := by
  rfl

@[simp] theorem section43DerivativeWordInput_cons_spatial
    (d n r : ℕ) [NeZero d]
    (F : SchwartzNPoint d n) (i : Fin n × Fin d)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordInput d n (r + 1) F
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.spatial i) tail) =
      section43SpatialMultiplierTransport d n
        (section43DerivativeWordInput d n r F tail) i := by
  rfl

/-- Nonnegative scalar coefficient controlling the coordinate factors in a
derivative word. -/
noncomputable def section43DerivativeWordCoeff
    (d n : ℕ) [NeZero d] :
    (r : ℕ) → Section43DerivativeWord d n r → ℝ
  | 0, _ => 1
  | r + 1, a =>
      let old := section43DerivativeWordCoeff d n r
        (section43DerivativeWordTail d n r a)
      match a 0 with
      | Section43DerivativeAtom.time k =>
          section43QTimeCoordOpNorm d n k * old
      | Section43DerivativeAtom.spatial i =>
          section43QSpatialCoordOpNorm d n i * old

@[simp] theorem section43DerivativeWordCoeff_cons_time
    (d n r : ℕ) [NeZero d] (k : Fin n)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordCoeff d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.time k) tail) =
      section43QTimeCoordOpNorm d n k *
        section43DerivativeWordCoeff d n r tail := by
  rfl

@[simp] theorem section43DerivativeWordCoeff_cons_spatial
    (d n r : ℕ) [NeZero d] (i : Fin n × Fin d)
    (tail : Section43DerivativeWord d n r) :
    section43DerivativeWordCoeff d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.spatial i) tail) =
      section43QSpatialCoordOpNorm d n i *
        section43DerivativeWordCoeff d n r tail := by
  rfl

/-- Scalar factor carried by a derivative word after evaluating it on the
direction tuple `m`. -/
noncomputable def section43DerivativeWordScalar
    (d n : ℕ) [NeZero d] :
    (r : ℕ) → Section43DerivativeWord d n r →
      (Fin n → ℝ) → (Fin r → NPointDomain d n) → ℂ
  | 0, _a, _τ, _m => 1
  | r + 1, a, τ, m =>
      let old := section43DerivativeWordScalar d n r
        (section43DerivativeWordTail d n r a) τ
        (section43DirectionTail d n r m)
      match a 0 with
      | Section43DerivativeAtom.time k =>
          (-((τ k : ℂ) *
            (section43QTime (d := d) (n := n) (m 0) k : ℂ))) * old
      | Section43DerivativeAtom.spatial i =>
          ((section43QSpatial (d := d) (n := n) (m 0) i : ℝ) : ℂ) * old

@[simp] theorem section43DerivativeWordScalar_cons_time
    (d n r : ℕ) [NeZero d]
    (k : Fin n) (tail : Section43DerivativeWord d n r)
    (τ : Fin n → ℝ) (head : NPointDomain d n)
    (directions : Fin r → NPointDomain d n) :
    section43DerivativeWordScalar d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.time k) tail)
      τ (Fin.cons head directions) =
      (-((τ k : ℂ) *
        (section43QTime (d := d) (n := n) head k : ℂ))) *
        section43DerivativeWordScalar d n r tail τ directions := by
  rfl

@[simp] theorem section43DerivativeWordScalar_cons_spatial
    (d n r : ℕ) [NeZero d]
    (i : Fin n × Fin d) (tail : Section43DerivativeWord d n r)
    (τ : Fin n → ℝ) (head : NPointDomain d n)
    (directions : Fin r → NPointDomain d n) :
    section43DerivativeWordScalar d n (r + 1)
      (section43DerivativeWordCons d n r
        (Section43DerivativeAtom.spatial i) tail)
      τ (Fin.cons head directions) =
      ((section43QSpatial (d := d) (n := n) head i : ℝ) : ℂ) *
        section43DerivativeWordScalar d n r tail τ directions := by
  rfl

theorem section43DerivativeWordCoeff_nonneg
    (d n r : ℕ) [NeZero d]
    (a : Section43DerivativeWord d n r) :
    0 ≤ section43DerivativeWordCoeff d n r a := by
  induction r with
  | zero =>
      simp [section43DerivativeWordCoeff]
  | succ r ih =>
      cases h : a 0 with
      | time k =>
          have hold :
              0 ≤ section43DerivativeWordCoeff d n r
                (section43DerivativeWordTail d n r a) :=
            ih (section43DerivativeWordTail d n r a)
          simp [section43DerivativeWordCoeff, h,
            section43QTimeCoordOpNorm,
            mul_nonneg (norm_nonneg _) hold]
      | spatial i =>
          have hold :
              0 ≤ section43DerivativeWordCoeff d n r
                (section43DerivativeWordTail d n r a) :=
            ih (section43DerivativeWordTail d n r a)
          simp [section43DerivativeWordCoeff, h,
            section43QSpatialCoordOpNorm,
            mul_nonneg (norm_nonneg _) hold]

/-- Norm bound for the scalar carried by a derivative word.  Time atoms
contribute one power of `‖τ‖`; every atom contributes the corresponding
coordinate-projection operator norm and one direction norm. -/
theorem section43DerivativeWordScalar_norm_le
    (d n r : ℕ) [NeZero d]
    (a : Section43DerivativeWord d n r)
    (τ : Fin n → ℝ) (m : Fin r → NPointDomain d n) :
    ‖section43DerivativeWordScalar d n r a τ m‖ ≤
      section43DerivativeWordCoeff d n r a *
        ‖τ‖ ^ section43DerivativeWordTimeCount d n r a *
          ∏ j : Fin r, ‖m j‖ := by
  induction r with
  | zero =>
      simp [section43DerivativeWordScalar, section43DerivativeWordCoeff,
        section43DerivativeWordTimeCount]
  | succ r ih =>
      cases h : a 0 with
      | time k =>
          let oldWord : Section43DerivativeWord d n r :=
            section43DerivativeWordTail d n r a
          let oldDirections : Fin r → NPointDomain d n :=
            section43DirectionTail d n r m
          let head : ℂ :=
            -((τ k : ℂ) *
              (section43QTime (d := d) (n := n) (m 0) k : ℂ))
          let oldScalar : ℂ :=
            section43DerivativeWordScalar d n r oldWord τ oldDirections
          have hhead :
              ‖head‖ ≤ section43QTimeCoordOpNorm d n k * ‖τ‖ * ‖m 0‖ := by
            have hm := abs_section43QTime_coord_le_opNorm d n (m 0) k
            have hτk : |τ k| ≤ ‖τ‖ := by
              simpa [Real.norm_eq_abs] using norm_le_pi_norm τ k
            calc
              ‖head‖ =
                  |τ k| * |section43QTime (d := d) (n := n) (m 0) k| := by
                    simp [head, Complex.norm_real, Real.norm_eq_abs]
              _ ≤ ‖τ‖ *
                    (section43QTimeCoordOpNorm d n k * ‖m 0‖) := by
                    exact mul_le_mul hτk hm (abs_nonneg _)
                      (norm_nonneg _)
              _ = section43QTimeCoordOpNorm d n k * ‖τ‖ * ‖m 0‖ := by
                    ring
          have hold :
              ‖oldScalar‖ ≤
                section43DerivativeWordCoeff d n r oldWord *
                  ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                    ∏ j : Fin r, ‖oldDirections j‖ := by
            simpa [oldScalar, oldWord, oldDirections] using
              ih oldWord oldDirections
          have hhead_nonneg :
              0 ≤ section43QTimeCoordOpNorm d n k * ‖τ‖ * ‖m 0‖ := by
            exact mul_nonneg
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              (norm_nonneg _)
          have hmul :
              ‖head‖ * ‖oldScalar‖ ≤
                (section43QTimeCoordOpNorm d n k * ‖τ‖ * ‖m 0‖) *
                  (section43DerivativeWordCoeff d n r oldWord *
                    ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                      ∏ j : Fin r, ‖oldDirections j‖) := by
            exact mul_le_mul hhead hold (norm_nonneg _) hhead_nonneg
          calc
            ‖section43DerivativeWordScalar d n (r + 1) a τ m‖ =
                ‖head‖ * ‖oldScalar‖ := by
                  simp [section43DerivativeWordScalar, h, head, oldScalar,
                    oldWord, oldDirections]
            _ ≤
                (section43QTimeCoordOpNorm d n k * ‖τ‖ * ‖m 0‖) *
                  (section43DerivativeWordCoeff d n r oldWord *
                    ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                      ∏ j : Fin r, ‖oldDirections j‖) := hmul
            _ =
                section43DerivativeWordCoeff d n (r + 1) a *
                  ‖τ‖ ^ section43DerivativeWordTimeCount d n (r + 1) a *
                    ∏ j : Fin (r + 1), ‖m j‖ := by
                  simp [section43DerivativeWordCoeff,
                    section43DerivativeWordTimeCount, h, oldWord,
                    oldDirections, section43DirectionTail,
                    Fin.prod_univ_succ, pow_succ]
                  ring
      | spatial i =>
          let oldWord : Section43DerivativeWord d n r :=
            section43DerivativeWordTail d n r a
          let oldDirections : Fin r → NPointDomain d n :=
            section43DirectionTail d n r m
          let head : ℂ :=
            ((section43QSpatial (d := d) (n := n) (m 0) i : ℝ) : ℂ)
          let oldScalar : ℂ :=
            section43DerivativeWordScalar d n r oldWord τ oldDirections
          have hhead :
              ‖head‖ ≤ section43QSpatialCoordOpNorm d n i * ‖m 0‖ := by
            have hm := abs_section43QSpatial_coord_le_opNorm d n (m 0) i
            simpa [head, Complex.norm_real, Real.norm_eq_abs] using hm
          have hold :
              ‖oldScalar‖ ≤
                section43DerivativeWordCoeff d n r oldWord *
                  ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                    ∏ j : Fin r, ‖oldDirections j‖ := by
            simpa [oldScalar, oldWord, oldDirections] using
              ih oldWord oldDirections
          have hhead_nonneg :
              0 ≤ section43QSpatialCoordOpNorm d n i * ‖m 0‖ := by
            exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
          have hmul :
              ‖head‖ * ‖oldScalar‖ ≤
                (section43QSpatialCoordOpNorm d n i * ‖m 0‖) *
                  (section43DerivativeWordCoeff d n r oldWord *
                    ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                      ∏ j : Fin r, ‖oldDirections j‖) := by
            exact mul_le_mul hhead hold (norm_nonneg _) hhead_nonneg
          calc
            ‖section43DerivativeWordScalar d n (r + 1) a τ m‖ =
                ‖head‖ * ‖oldScalar‖ := by
                  simp [section43DerivativeWordScalar, h, head, oldScalar,
                    oldWord, oldDirections]
            _ ≤
                (section43QSpatialCoordOpNorm d n i * ‖m 0‖) *
                  (section43DerivativeWordCoeff d n r oldWord *
                    ‖τ‖ ^ section43DerivativeWordTimeCount d n r oldWord *
                      ∏ j : Fin r, ‖oldDirections j‖) := hmul
            _ =
                section43DerivativeWordCoeff d n (r + 1) a *
                  ‖τ‖ ^ section43DerivativeWordTimeCount d n (r + 1) a *
                    ∏ j : Fin (r + 1), ‖m j‖ := by
                  simp [section43DerivativeWordCoeff,
                    section43DerivativeWordTimeCount, h, oldWord,
                    oldDirections, section43DirectionTail,
                    Fin.prod_univ_succ]
                  ring

/-- The first derivative is the one-letter instance of the finite word
expansion: time atoms come from differentiating the exponential, and spatial
atoms come from differentiating the spatial Fourier argument. -/
theorem section43FourierLaplace_timeIntegrandFDerivCLM_apply_eq_sum_atoms
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q m : NPointDomain d n)
    (τ : Fin n → ℝ) :
    section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ m =
      ∑ a : Section43DerivativeAtom d n,
        match a with
        | Section43DerivativeAtom.time k =>
            (-((τ k : ℂ) *
              (section43QTime (d := d) (n := n) m k : ℂ))) *
              Complex.exp
                (-(∑ j : Fin n,
                  (τ j : ℂ) *
                    (section43QTime (d := d) (n := n) q j : ℂ))) *
                partialFourierSpatial_fun (d := d) (n := n) F
                  (τ, section43QSpatial (d := d) (n := n) q)
        | Section43DerivativeAtom.spatial i =>
            ((section43QSpatial (d := d) (n := n) m i : ℝ) : ℂ) *
              Complex.exp
                (-(∑ j : Fin n,
                  (τ j : ℂ) *
                    (section43QTime (d := d) (n := n) q j : ℂ))) *
                partialFourierSpatial_fun (d := d) (n := n)
                  (section43SpatialMultiplierTransport d n F i)
                  (τ, section43QSpatial (d := d) (n := n) q) := by
  classical
  let E : ℂ :=
    Complex.exp
      (-(∑ j : Fin n,
        (τ j : ℂ) * (section43QTime (d := d) (n := n) q j : ℂ)))
  let ξ : EuclideanSpace ℝ (Fin n × Fin d) :=
    section43QSpatial (d := d) (n := n) q
  let P : ℂ :=
    partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ)
  let timeTerm : Fin n → ℂ := fun k =>
    (-((τ k : ℂ) *
      (section43QTime (d := d) (n := n) m k : ℂ))) * E * P
  let spatialTerm : Fin n × Fin d → ℂ := fun i =>
    ((section43QSpatial (d := d) (n := n) m i : ℝ) : ℂ) * E *
      partialFourierSpatial_fun (d := d) (n := n)
        (section43SpatialMultiplierTransport d n F i) (τ, ξ)
  have hspatial :
      (fderiv ℝ
        (fun ξ' : EuclideanSpace ℝ (Fin n × Fin d) =>
          partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ'))
        ξ)
        (section43QSpatial (d := d) (n := n) m) =
        ∑ i : Fin n × Fin d,
          ((section43QSpatial (d := d) (n := n) m i : ℝ) : ℂ) *
            partialFourierSpatial_fun (d := d) (n := n)
              (section43SpatialMultiplierTransport d n F i) (τ, ξ) := by
    simpa [ξ] using
      fderiv_partialFourierSpatial_fun_spatial_apply_eq_sum_multiplierTransport
        d n F τ ξ (section43QSpatial (d := d) (n := n) m)
  have hsplit :
      (∑ a : Section43DerivativeAtom d n,
        match a with
        | Section43DerivativeAtom.time k => timeTerm k
        | Section43DerivativeAtom.spatial i => spatialTerm i) =
      (∑ k : Fin n, timeTerm k) + ∑ i : Fin n × Fin d, spatialTerm i := by
    exact section43DerivativeAtom_sum d n timeTerm spatialTerm
  calc
    section43FourierLaplace_timeIntegrandFDerivCLM d n F q τ m =
        (∑ k : Fin n,
          (section43QTime (d := d) (n := n) m k : ℝ) •
            (-(τ k : ℂ) * E * P)) +
          E •
            (fderiv ℝ
              (fun ξ' : EuclideanSpace ℝ (Fin n × Fin d) =>
                partialFourierSpatial_fun (d := d) (n := n) F (τ, ξ'))
              ξ)
              (section43QSpatial (d := d) (n := n) m) := by
          simp [section43FourierLaplace_timeIntegrandFDerivCLM_apply, E, P, ξ]
    _ = (∑ k : Fin n, timeTerm k) + ∑ i : Fin n × Fin d, spatialTerm i := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro k _hk
            simp [timeTerm, Complex.real_smul, mul_assoc, mul_left_comm]
          · rw [hspatial]
            simp [spatialTerm, smul_eq_mul, Finset.mul_sum,
              mul_assoc, mul_left_comm]
    _ =
        ∑ a : Section43DerivativeAtom d n,
          match a with
          | Section43DerivativeAtom.time k =>
              (-((τ k : ℂ) *
                (section43QTime (d := d) (n := n) m k : ℂ))) *
                Complex.exp
                  (-(∑ j : Fin n,
                    (τ j : ℂ) *
                      (section43QTime (d := d) (n := n) q j : ℂ))) *
                  partialFourierSpatial_fun (d := d) (n := n) F
                    (τ, section43QSpatial (d := d) (n := n) q)
          | Section43DerivativeAtom.spatial i =>
              ((section43QSpatial (d := d) (n := n) m i : ℝ) : ℂ) *
                Complex.exp
                  (-(∑ j : Fin n,
                    (τ j : ℂ) *
                      (section43QTime (d := d) (n := n) q j : ℂ))) *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43SpatialMultiplierTransport d n F i)
                    (τ, section43QSpatial (d := d) (n := n) q) := by
          rw [← hsplit]

/-- The pointwise Section 4.3 Fourier-Laplace time integrand is smooth in the
positive-energy variable `q`, for fixed real time parameter `τ`.  This is the
regularity input needed to pass from the CLM-valued `iteratedFDeriv` recursion
to an applied scalar derivative after freezing the old directions. -/
theorem contDiff_section43FourierLaplace_timeIntegrand_q
    (d n : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (τ : Fin n → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q' : NPointDomain d n =>
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) *
              (section43QTime (d := d) (n := n) q' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q')) := by
  classical
  have hEarg : ContDiff ℝ (⊤ : ℕ∞) (fun q' : NPointDomain d n =>
      -(∑ k : Fin n,
        (τ k : ℂ) *
          (section43QTime (d := d) (n := n) q' k : ℂ))) := by
    apply ContDiff.neg
    apply ContDiff.sum
    intro k _hk
    have hreal : ContDiff ℝ (⊤ : ℕ∞) (fun q' : NPointDomain d n =>
        section43QTime (d := d) (n := n) q' k) := by
      let L : NPointDomain d n →L[ℝ] ℝ :=
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ => ℝ) k).comp
          (section43QTimeCLM d n)
      simpa [L] using L.contDiff
    have hcomplex : ContDiff ℝ (⊤ : ℕ∞) (fun q' : NPointDomain d n =>
        (section43QTime (d := d) (n := n) q' k : ℂ)) := by
      exact Complex.ofRealCLM.contDiff.comp hreal
    exact contDiff_const.mul hcomplex
  have hE : ContDiff ℝ (⊤ : ℕ∞) (fun q' : NPointDomain d n =>
      Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) *
            (section43QTime (d := d) (n := n) q' k : ℂ)))) :=
    Complex.contDiff_exp.comp hEarg
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun q' : NPointDomain d n =>
      partialFourierSpatial_fun (d := d) (n := n) F
        (τ, section43QSpatial (d := d) (n := n) q')) := by
    let hbase : ContDiff ℝ (⊤ : ℕ∞)
        (partialFourierSpatial_fun (d := d) (n := n) F) :=
      contDiff_partialFourierSpatial_fun_joint (d := d) (n := n) F
    have hspatial : ContDiff ℝ (⊤ : ℕ∞) (fun q' : NPointDomain d n =>
        section43QSpatial (d := d) (n := n) q') := by
      simpa using (section43QSpatialCLM d n).contDiff
    let hpath : ContDiff ℝ (⊤ : ℕ∞) (fun q' : NPointDomain d n =>
        (τ, section43QSpatial (d := d) (n := n) q')) :=
      (contDiff_const :
        ContDiff ℝ (⊤ : ℕ∞) (fun _ : NPointDomain d n => τ)).prodMk hspatial
    simpa using hbase.comp hpath
  exact hE.mul hP

/-- Differentiating a fixed old-word summand only differentiates the basic
Fourier-Laplace integrand; the old word scalar is constant in `q`. -/
private theorem hasFDerivAt_section43FourierLaplace_timeIntegrand_wordTerm
    (d n r : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (a : Section43DerivativeWord d n r)
    (τ : Fin n → ℝ)
    (m : Fin r → NPointDomain d n)
    (q : NPointDomain d n) :
    HasFDerivAt
      (fun q' : NPointDomain d n =>
        section43DerivativeWordScalar d n r a τ m *
          Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) *
                (section43QTime (d := d) (n := n) q' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n)
            (section43DerivativeWordInput d n r F a)
            (τ, section43QSpatial (d := d) (n := n) q'))
      (section43DerivativeWordScalar d n r a τ m •
        section43FourierLaplace_timeIntegrandFDerivCLM d n
          (section43DerivativeWordInput d n r F a) q τ)
      q := by
  let c : ℂ := section43DerivativeWordScalar d n r a τ m
  let F' : SchwartzNPoint d n := section43DerivativeWordInput d n r F a
  simpa [c, F', mul_assoc] using
    (hasFDerivAt_section43FourierLaplace_timeIntegrand d n F' q τ).const_mul c

/-- Expanding the first derivative of every old-word summand and reindexing by
prepending the new derivative atom gives the next word layer. -/
theorem section43FourierLaplace_sum_words_fderivCLM_apply_eq_sum_cons
    (d n r : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q v : NPointDomain d n)
    (τ : Fin n → ℝ)
    (mtail : Fin r → NPointDomain d n) :
    (∑ a : Section43DerivativeWord d n r,
      section43DerivativeWordScalar d n r a τ mtail *
        section43FourierLaplace_timeIntegrandFDerivCLM d n
          (section43DerivativeWordInput d n r F a) q τ v) =
    ∑ a : Section43DerivativeWord d n (r + 1),
      section43DerivativeWordScalar d n (r + 1) a τ (Fin.cons v mtail) *
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) *
              (section43QTime (d := d) (n := n) q k : ℂ))) *
        partialFourierSpatial_fun (d := d) (n := n)
          (section43DerivativeWordInput d n (r + 1) F a)
          (τ, section43QSpatial (d := d) (n := n) q) := by
  classical
  let E : ℂ :=
    Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
  calc
    (∑ a : Section43DerivativeWord d n r,
      section43DerivativeWordScalar d n r a τ mtail *
        section43FourierLaplace_timeIntegrandFDerivCLM d n
          (section43DerivativeWordInput d n r F a) q τ v) =
      ∑ a : Section43DerivativeWord d n r,
        section43DerivativeWordScalar d n r a τ mtail *
          (∑ head : Section43DerivativeAtom d n,
            match head with
            | Section43DerivativeAtom.time k =>
                (-((τ k : ℂ) *
                  (section43QTime (d := d) (n := n) v k : ℂ))) * E *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43DerivativeWordInput d n r F a)
                    (τ, section43QSpatial (d := d) (n := n) q)
            | Section43DerivativeAtom.spatial i =>
                ((section43QSpatial (d := d) (n := n) v i : ℝ) : ℂ) * E *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43SpatialMultiplierTransport d n
                      (section43DerivativeWordInput d n r F a) i)
                    (τ, section43QSpatial (d := d) (n := n) q)) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        rw [section43FourierLaplace_timeIntegrandFDerivCLM_apply_eq_sum_atoms]
    _ = ∑ a : Section43DerivativeWord d n r,
        ∑ head : Section43DerivativeAtom d n,
          section43DerivativeWordScalar d n r a τ mtail *
            (match head with
            | Section43DerivativeAtom.time k =>
                (-((τ k : ℂ) *
                  (section43QTime (d := d) (n := n) v k : ℂ))) * E *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43DerivativeWordInput d n r F a)
                    (τ, section43QSpatial (d := d) (n := n) q)
            | Section43DerivativeAtom.spatial i =>
                ((section43QSpatial (d := d) (n := n) v i : ℝ) : ℂ) * E *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43SpatialMultiplierTransport d n
                      (section43DerivativeWordInput d n r F a) i)
                    (τ, section43QSpatial (d := d) (n := n) q)) := by
        simp [Finset.mul_sum]
    _ = ∑ head : Section43DerivativeAtom d n,
        ∑ a : Section43DerivativeWord d n r,
          section43DerivativeWordScalar d n r a τ mtail *
            (match head with
            | Section43DerivativeAtom.time k =>
                (-((τ k : ℂ) *
                  (section43QTime (d := d) (n := n) v k : ℂ))) * E *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43DerivativeWordInput d n r F a)
                    (τ, section43QSpatial (d := d) (n := n) q)
            | Section43DerivativeAtom.spatial i =>
                ((section43QSpatial (d := d) (n := n) v i : ℝ) : ℂ) * E *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43SpatialMultiplierTransport d n
                      (section43DerivativeWordInput d n r F a) i)
                    (τ, section43QSpatial (d := d) (n := n) q)) := by
        rw [Finset.sum_comm]
    _ = ∑ head : Section43DerivativeAtom d n,
        ∑ a : Section43DerivativeWord d n r,
          section43DerivativeWordScalar d n (r + 1)
            (section43DerivativeWordCons d n r head a) τ (Fin.cons v mtail) *
            E *
            partialFourierSpatial_fun (d := d) (n := n)
              (section43DerivativeWordInput d n (r + 1) F
                (section43DerivativeWordCons d n r head a))
              (τ, section43QSpatial (d := d) (n := n) q) := by
        refine Finset.sum_congr rfl ?_
        intro head _hhead
        refine Finset.sum_congr rfl ?_
        intro a _ha
        cases head with
        | time k =>
            simp [E, mul_assoc, mul_left_comm, mul_comm]
        | spatial i =>
            simp [E, mul_assoc, mul_comm]
    _ = ∑ a : Section43DerivativeWord d n (r + 1),
      section43DerivativeWordScalar d n (r + 1) a τ (Fin.cons v mtail) *
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) *
              (section43QTime (d := d) (n := n) q k : ℂ))) *
        partialFourierSpatial_fun (d := d) (n := n)
          (section43DerivativeWordInput d n (r + 1) F a)
          (τ, section43QSpatial (d := d) (n := n) q) := by
        rw [section43DerivativeWord_sum_cons]

/-- Pointwise all-order finite-word expansion for the Section 4.3
Fourier-Laplace time integrand.  Each derivative slot either differentiates the
Laplace exponential, producing a `time` atom, or differentiates the spatial
Fourier argument, producing a `spatial` atom and transporting the input
Schwartz function by the corresponding coordinate multiplier. -/
theorem section43FourierLaplace_timeIntegrand_iteratedFDeriv_apply_eq_sum_words
    (d n r : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    (q : NPointDomain d n)
    (τ : Fin n → ℝ)
    (m : Fin r → NPointDomain d n) :
    iteratedFDeriv ℝ r
      (fun q' : NPointDomain d n =>
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) *
              (section43QTime (d := d) (n := n) q' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q'))
      q m =
      ∑ a : Section43DerivativeWord d n r,
        section43DerivativeWordScalar d n r a τ m *
          Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) *
                (section43QTime (d := d) (n := n) q k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n)
            (section43DerivativeWordInput d n r F a)
            (τ, section43QSpatial (d := d) (n := n) q) := by
  classical
  induction r generalizing q with
  | zero =>
      simp [section43DerivativeWordScalar, section43DerivativeWordInput]
  | succ r ih =>
      let G : NPointDomain d n → ℂ := fun q' =>
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) *
              (section43QTime (d := d) (n := n) q' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q')
      let v : NPointDomain d n := m 0
      let mtail : Fin r → NPointDomain d n := section43DirectionTail d n r m
      have hm : Fin.cons v mtail = m := by
        change Fin.cons (m 0) (Fin.tail m) = m
        exact Fin.cons_self_tail m
      have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) G := by
        simpa [G] using contDiff_section43FourierLaplace_timeIntegrand_q d n F τ
      have hGdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ r G) q := by
        exact hGsmooth.contDiffAt.differentiableAt_iteratedFDeriv
          (WithTop.coe_lt_coe.2 (ENat.coe_lt_top r))
      have happly :
          (fderiv ℝ (fun q' : NPointDomain d n => (iteratedFDeriv ℝ r G q') mtail) q) v =
            (fderiv ℝ (iteratedFDeriv ℝ r G) q) v mtail := by
        simpa using
          (fderiv_continuousMultilinear_apply_const_apply
            (𝕜 := ℝ) (c := fun q' : NPointDomain d n => iteratedFDeriv ℝ r G q')
            (x := q) hGdiff mtail v)
      have hfun :
          (fun q' : NPointDomain d n => (iteratedFDeriv ℝ r G q') mtail) =
            fun q' : NPointDomain d n =>
              ∑ a : Section43DerivativeWord d n r,
                section43DerivativeWordScalar d n r a τ mtail *
                  Complex.exp
                    (-(∑ k : Fin n,
                      (τ k : ℂ) *
                        (section43QTime (d := d) (n := n) q' k : ℂ))) *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43DerivativeWordInput d n r F a)
                    (τ, section43QSpatial (d := d) (n := n) q') := by
        funext q'
        simpa [G] using ih q' mtail
      have hsumDeriv :
          HasFDerivAt
            (fun q' : NPointDomain d n =>
              ∑ a : Section43DerivativeWord d n r,
                section43DerivativeWordScalar d n r a τ mtail *
                  Complex.exp
                    (-(∑ k : Fin n,
                      (τ k : ℂ) *
                        (section43QTime (d := d) (n := n) q' k : ℂ))) *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43DerivativeWordInput d n r F a)
                    (τ, section43QSpatial (d := d) (n := n) q'))
            (∑ a : Section43DerivativeWord d n r,
              section43DerivativeWordScalar d n r a τ mtail •
                section43FourierLaplace_timeIntegrandFDerivCLM d n
                  (section43DerivativeWordInput d n r F a) q τ)
            q := by
        apply HasFDerivAt.fun_sum
        intro a _ha
        exact hasFDerivAt_section43FourierLaplace_timeIntegrand_wordTerm
          d n r F a τ mtail q
      have hfderiv_sum_apply :
          (fderiv ℝ
            (fun q' : NPointDomain d n =>
              ∑ a : Section43DerivativeWord d n r,
                section43DerivativeWordScalar d n r a τ mtail *
                  Complex.exp
                    (-(∑ k : Fin n,
                      (τ k : ℂ) *
                        (section43QTime (d := d) (n := n) q' k : ℂ))) *
                  partialFourierSpatial_fun (d := d) (n := n)
                    (section43DerivativeWordInput d n r F a)
                    (τ, section43QSpatial (d := d) (n := n) q')) q) v =
            ∑ a : Section43DerivativeWord d n r,
              section43DerivativeWordScalar d n r a τ mtail *
                section43FourierLaplace_timeIntegrandFDerivCLM d n
                  (section43DerivativeWordInput d n r F a) q τ v := by
        rw [hsumDeriv.fderiv]
        simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [← hm]
      calc
        iteratedFDeriv ℝ (r + 1) G q (Fin.cons v mtail) =
            (fderiv ℝ (iteratedFDeriv ℝ r G) q) v mtail := by
              rfl
        _ = (fderiv ℝ (fun q' : NPointDomain d n => (iteratedFDeriv ℝ r G q') mtail) q) v := by
              rw [← happly]
        _ = (fderiv ℝ
              (fun q' : NPointDomain d n =>
                ∑ a : Section43DerivativeWord d n r,
                  section43DerivativeWordScalar d n r a τ mtail *
                    Complex.exp
                      (-(∑ k : Fin n,
                        (τ k : ℂ) *
                          (section43QTime (d := d) (n := n) q' k : ℂ))) *
                    partialFourierSpatial_fun (d := d) (n := n)
                      (section43DerivativeWordInput d n r F a)
                      (τ, section43QSpatial (d := d) (n := n) q')) q) v := by
              rw [hfun]
        _ = ∑ a : Section43DerivativeWord d n r,
              section43DerivativeWordScalar d n r a τ mtail *
                section43FourierLaplace_timeIntegrandFDerivCLM d n
                  (section43DerivativeWordInput d n r F a) q τ v := hfderiv_sum_apply
        _ = ∑ a : Section43DerivativeWord d n (r + 1),
              section43DerivativeWordScalar d n (r + 1) a τ (Fin.cons v mtail) *
                Complex.exp
                  (-(∑ k : Fin n,
                    (τ k : ℂ) *
                      (section43QTime (d := d) (n := n) q k : ℂ))) *
                partialFourierSpatial_fun (d := d) (n := n)
                  (section43DerivativeWordInput d n (r + 1) F a)
                  (τ, section43QSpatial (d := d) (n := n) q) := by
              exact section43FourierLaplace_sum_words_fderivCLM_apply_eq_sum_cons
                d n r F q v τ mtail

/-- Positive-energy pointwise norm bound for the all-order finite-word
expansion, applied to a fixed tuple of derivative directions. -/
theorem norm_section43FourierLaplace_timeIntegrand_iteratedFDeriv_apply_le_sum_words
    (d n r : ℕ) [NeZero d]
    (F : SchwartzNPoint d n)
    {δ : ℝ}
    (q : NPointDomain d n) (hq : q ∈ section43PositiveEnergyRegion d n)
    (τ : Fin n → ℝ)
    (hτ_margin : ∀ k : Fin n, δ ≤ τ k)
    (m : Fin r → NPointDomain d n) :
    ‖iteratedFDeriv ℝ r
      (fun q' : NPointDomain d n =>
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) *
              (section43QTime (d := d) (n := n) q' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q'))
      q m‖ ≤
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k)) *
        (∑ a : Section43DerivativeWord d n r,
          section43DerivativeWordCoeff d n r a *
            ‖τ‖ ^ section43DerivativeWordTimeCount d n r a *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43DerivativeWordInput d n r F a)
              (τ, section43QSpatial (d := d) (n := n) q)‖) *
        ∏ j : Fin r, ‖m j‖ := by
  classical
  let E : ℂ :=
    Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
  let A : ℝ :=
    Real.exp (-(δ * ∑ k : Fin n, section43QTime (d := d) (n := n) q k))
  let dirProd : ℝ := ∏ j : Fin r, ‖m j‖
  let P : Section43DerivativeWord d n r → ℂ := fun a =>
    partialFourierSpatial_fun (d := d) (n := n)
      (section43DerivativeWordInput d n r F a)
      (τ, section43QSpatial (d := d) (n := n) q)
  have hEbound : ‖E‖ ≤ A := by
    simpa [E, A] using
      norm_exp_neg_section43_timePair_le_exp_neg_margin_sum
        d n q τ hq hτ_margin
  have hmain :
      ‖∑ a : Section43DerivativeWord d n r,
        section43DerivativeWordScalar d n r a τ m * E * P a‖ ≤
        ∑ a : Section43DerivativeWord d n r,
          A *
            (section43DerivativeWordCoeff d n r a *
              ‖τ‖ ^ section43DerivativeWordTimeCount d n r a * ‖P a‖) *
            dirProd := by
    calc
      ‖∑ a : Section43DerivativeWord d n r,
        section43DerivativeWordScalar d n r a τ m * E * P a‖ ≤
          ∑ a : Section43DerivativeWord d n r,
            ‖section43DerivativeWordScalar d n r a τ m * E * P a‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ a : Section43DerivativeWord d n r,
          A *
            (section43DerivativeWordCoeff d n r a *
              ‖τ‖ ^ section43DerivativeWordTimeCount d n r a * ‖P a‖) *
            dirProd := by
          refine Finset.sum_le_sum ?_
          intro a _ha
          have hscalar := section43DerivativeWordScalar_norm_le d n r a τ m
          have hupper_nonneg :
              0 ≤ section43DerivativeWordCoeff d n r a *
                ‖τ‖ ^ section43DerivativeWordTimeCount d n r a * dirProd := by
            exact mul_nonneg
              (mul_nonneg (section43DerivativeWordCoeff_nonneg d n r a)
                (pow_nonneg (norm_nonneg τ) _))
              (Finset.prod_nonneg fun j _hj => norm_nonneg (m j))
          have hSE :
              ‖section43DerivativeWordScalar d n r a τ m‖ * ‖E‖ ≤
                (section43DerivativeWordCoeff d n r a *
                  ‖τ‖ ^ section43DerivativeWordTimeCount d n r a * dirProd) * A := by
            exact mul_le_mul hscalar hEbound (norm_nonneg E) hupper_nonneg
          have hP_nonneg : 0 ≤ ‖P a‖ := norm_nonneg _
          calc
            ‖section43DerivativeWordScalar d n r a τ m * E * P a‖ =
                ‖section43DerivativeWordScalar d n r a τ m‖ * ‖E‖ * ‖P a‖ := by
                  simp [mul_assoc]
            _ ≤ ((section43DerivativeWordCoeff d n r a *
                  ‖τ‖ ^ section43DerivativeWordTimeCount d n r a * dirProd) * A) *
                  ‖P a‖ := by
                  exact mul_le_mul_of_nonneg_right hSE hP_nonneg
            _ = A *
                (section43DerivativeWordCoeff d n r a *
                  ‖τ‖ ^ section43DerivativeWordTimeCount d n r a * ‖P a‖) *
                dirProd := by
                  ring
  calc
    ‖iteratedFDeriv ℝ r
      (fun q' : NPointDomain d n =>
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) *
              (section43QTime (d := d) (n := n) q' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n) F
            (τ, section43QSpatial (d := d) (n := n) q'))
      q m‖ =
        ‖∑ a : Section43DerivativeWord d n r,
          section43DerivativeWordScalar d n r a τ m * E * P a‖ := by
          rw [section43FourierLaplace_timeIntegrand_iteratedFDeriv_apply_eq_sum_words]
    _ ≤ ∑ a : Section43DerivativeWord d n r,
          A *
            (section43DerivativeWordCoeff d n r a *
              ‖τ‖ ^ section43DerivativeWordTimeCount d n r a * ‖P a‖) *
            dirProd := hmain
    _ = A *
        (∑ a : Section43DerivativeWord d n r,
          section43DerivativeWordCoeff d n r a *
            ‖τ‖ ^ section43DerivativeWordTimeCount d n r a * ‖P a‖) *
        dirProd := by
          rw [← Finset.sum_mul]
          congr 1
          rw [Finset.mul_sum]
    _ = Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k)) *
        (∑ a : Section43DerivativeWord d n r,
          section43DerivativeWordCoeff d n r a *
            ‖τ‖ ^ section43DerivativeWordTimeCount d n r a *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43DerivativeWordInput d n r F a)
              (τ, section43QSpatial (d := d) (n := n) q)‖) *
        ∏ j : Fin r, ‖m j‖ := by
          simp [A, P, dirProd]

/-- Below the ordered-support time margin, the pointwise Fourier-Laplace time
integrand for the OS-I difference-coordinate pullback is identically zero as a
function of the positive-energy variable `q`. -/
theorem section43FourierLaplace_timeIntegrand_eq_zero_of_exists_time_lt_margin
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (τ : Fin n → ℝ)
    (hτ : ∃ i : Fin n, τ i < δ) :
    (fun q' : NPointDomain d n =>
      Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) *
            (section43QTime (d := d) (n := n) q' k : ℂ))) *
      partialFourierSpatial_fun (d := d) (n := n)
        (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
        (τ, section43QSpatial (d := d) (n := n) q')) =
      fun _ => 0 := by
  funext q'
  have hP_zero :
      partialFourierSpatial_fun (d := d) (n := n)
        (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
        (τ, section43QSpatial (d := d) (n := n) q') = 0 := by
    exact partialFourierSpatial_section43DiffPullback_eq_zero_of_exists_time_lt_margin
      d n f hf_ord hδ_supp τ (section43QSpatial (d := d) (n := n) q') hτ
  simp [hP_zero]

/-- Below the ordered-support time margin, all pointwise iterated derivatives
of the Fourier-Laplace time integrand vanish.  The proof goes through the
zero-function identity for the original integrand, avoiding any transported-word
support claim. -/
theorem section43FourierLaplace_timeIntegrand_iteratedFDeriv_eq_zero_of_exists_time_lt_margin
    (d n r : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (τ : Fin n → ℝ)
    (hτ : ∃ i : Fin n, τ i < δ) :
    iteratedFDeriv ℝ r
      (fun q' : NPointDomain d n =>
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) *
              (section43QTime (d := d) (n := n) q' k : ℂ))) *
        partialFourierSpatial_fun (d := d) (n := n)
          (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
          (τ, section43QSpatial (d := d) (n := n) q')) =
      0 := by
  rw [section43FourierLaplace_timeIntegrand_eq_zero_of_exists_time_lt_margin
    d n f hf_ord hδ_supp τ hτ]
  simp

/-- Pointwise operator-norm bound for the all-order Fourier-Laplace integrand
derivative.  The proof splits on the lower-margin branch; above the margin it
packages the applied word bound with `ContinuousMultilinearMap.opNorm_le_bound`. -/
theorem norm_section43FourierLaplace_timeIntegrand_iteratedFDeriv_le_sum_words
    (d n r : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (hf_ord :
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    {δ : ℝ}
    (hδ_supp :
      tsupport (f : NPointDomain d n → ℂ) ⊆
        {x |
          (∀ i : Fin n, δ ≤ x i 0) ∧
          (∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)})
    (q : NPointDomain d n) (hq : q ∈ section43PositiveEnergyRegion d n)
    (τ : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ r
      (fun q' : NPointDomain d n =>
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) *
              (section43QTime (d := d) (n := n) q' k : ℂ))) *
          partialFourierSpatial_fun (d := d) (n := n)
            (section43DiffPullbackCLM d n ⟨f, hf_ord⟩)
            (τ, section43QSpatial (d := d) (n := n) q'))
      q‖ ≤
      Real.exp (-(δ * ∑ k : Fin n,
        section43QTime (d := d) (n := n) q k)) *
        ∑ a : Section43DerivativeWord d n r,
          section43DerivativeWordCoeff d n r a *
            ‖τ‖ ^ section43DerivativeWordTimeCount d n r a *
            ‖partialFourierSpatial_fun (d := d) (n := n)
              (section43DerivativeWordInput d n r
                (section43DiffPullbackCLM d n ⟨f, hf_ord⟩) a)
              (τ, section43QSpatial (d := d) (n := n) q)‖ := by
  classical
  let F : SchwartzNPoint d n := section43DiffPullbackCLM d n ⟨f, hf_ord⟩
  let A : ℝ :=
    Real.exp (-(δ * ∑ k : Fin n, section43QTime (d := d) (n := n) q k))
  let S : ℝ :=
    ∑ a : Section43DerivativeWord d n r,
      section43DerivativeWordCoeff d n r a *
        ‖τ‖ ^ section43DerivativeWordTimeCount d n r a *
        ‖partialFourierSpatial_fun (d := d) (n := n)
          (section43DerivativeWordInput d n r F a)
          (τ, section43QSpatial (d := d) (n := n) q)‖
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    refine Finset.sum_nonneg ?_
    intro a _ha
    exact mul_nonneg
      (mul_nonneg (section43DerivativeWordCoeff_nonneg d n r a)
        (pow_nonneg (norm_nonneg τ) _))
      (norm_nonneg _)
  have hM_nonneg : 0 ≤ A * S := mul_nonneg (Real.exp_pos _).le hS_nonneg
  by_cases hlow : ∃ i : Fin n, τ i < δ
  · have hzero :=
      section43FourierLaplace_timeIntegrand_iteratedFDeriv_eq_zero_of_exists_time_lt_margin
        d n r f hf_ord hδ_supp τ hlow
    rw [hzero]
    simpa [A, S, F] using hM_nonneg
  · have hτ_margin : ∀ i : Fin n, δ ≤ τ i := by
      intro i
      exact le_of_not_gt fun hi => hlow ⟨i, hi⟩
    have hop :
        ‖iteratedFDeriv ℝ r
          (fun q' : NPointDomain d n =>
            Complex.exp
              (-(∑ k : Fin n,
                (τ k : ℂ) *
                  (section43QTime (d := d) (n := n) q' k : ℂ))) *
              partialFourierSpatial_fun (d := d) (n := n) F
                (τ, section43QSpatial (d := d) (n := n) q'))
          q‖ ≤ A * S := by
      refine ContinuousMultilinearMap.opNorm_le_bound hM_nonneg ?_
      intro m
      have happly :=
        norm_section43FourierLaplace_timeIntegrand_iteratedFDeriv_apply_le_sum_words
          d n r F q hq τ hτ_margin m
      simpa [A, S, F] using happly
    simpa [A, S, F] using hop

end OSReconstruction
