import OSReconstruction.Wightman.Reconstruction.Core

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The Euclidean positive-time degree-`n` test space from OS I Section 4.3.

This is the paper's `S_+(ℝ^{4n})`: Schwartz `n`-point test functions whose
topological support lies in the ordered positive-time region. -/
def EuclideanPositiveTimeComponent (d n : ℕ) [NeZero d] :=
  {f : SchwartzNPoint d n //
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}

/-- The mixed-order total-arity source surface forced by
`SchwartzMap.conjTensorProduct_apply` on a fixed pair of positive-time inputs:
every time coordinate is nonnegative, the left block is strictly ordered in the
reverse direction, and the right block remains strictly ordered forward. -/
def FixedPairMixedOrderTimeRegion (d n m : ℕ) [NeZero d] :
    Set (NPointDomain d (n + m)) :=
  {y |
    (∀ i : Fin (n + m), 0 ≤ y i 0) ∧
      (∀ ⦃i j : Fin (n + m)⦄, i.1 < n → j.1 < n → i < j → y j 0 < y i 0) ∧
      (∀ ⦃i j : Fin (n + m)⦄, n ≤ i.1 → n ≤ j.1 → i < j → y i 0 < y j 0)}

/-- The explicit mixed-order total-arity source object matching the geometry of
`f.conjTensorProduct g` for a positive-time left factor `f` and right factor
`g`. This is strictly weaker than `EuclideanPositiveTimeComponent d (n + m)`:
the left block is reversed rather than globally ordered. -/
def FixedPairMixedOrderComponent (d n m : ℕ) [NeZero d] :=
  {F : SchwartzNPoint d (n + m) //
    tsupport (F : NPointDomain d (n + m) → ℂ) ⊆ FixedPairMixedOrderTimeRegion d n m}

/-- An equivalent submodule presentation of the Euclidean positive-time domain.

The Section-4.3 transport map is naturally a continuous linear map on this
submodule surface. -/
def euclideanPositiveTimeSubmodule (d n : ℕ) [NeZero d] :
    Submodule ℂ (SchwartzNPoint d n) where
  carrier := {f |
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}
  zero_mem' := by
    change tsupport (((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ)) ⊆
      OrderedPositiveTimeRegion d n
    rw [show (((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ)) = 0 by rfl]
    simpa using (empty_subset (OrderedPositiveTimeRegion d n) :
      (∅ : Set (NPointDomain d n)) ⊆ OrderedPositiveTimeRegion d n)
  add_mem' := by
    intro f g hf hg x hx
    have hx' := tsupport_add
      ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)
      ((g : SchwartzNPoint d n) : NPointDomain d n → ℂ) hx
    exact hx'.elim (hf ·) (hg ·)
  smul_mem' := by
    intro c f hf
    exact (tsupport_smul_subset_right
      (fun _ : NPointDomain d n => c)
      ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)).trans hf

@[simp] theorem mem_euclideanPositiveTimeSubmodule
    {n : ℕ} (f : SchwartzNPoint d n) :
    f ∈ euclideanPositiveTimeSubmodule (d := d) n ↔
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n := Iff.rfl

namespace EuclideanPositiveTimeComponent

variable {n : ℕ}

/-- Package a positive-time submodule element as the corresponding subtype
object. -/
def ofSubmodule
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    EuclideanPositiveTimeComponent d n :=
  ⟨f.1, f.2⟩

/- Exact constructor seam:
`euclideanPositiveTimeSubmodule` and `EuclideanPositiveTimeComponent.ofSubmodule`
only repackage support that is already proved. Current source still has no
theorem here upgrading an ambient Schwartz component from boundary-vanishing,
time-shift comparison, or fixed-surrogate hypotheses to
`tsupport ⊆ OrderedPositiveTimeRegion`. -/

end EuclideanPositiveTimeComponent

omit [NeZero d] in
private theorem tsupport_precomp_subset_local {X Y α : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero α]
    {f : Y → α} {h : X → Y} (hh : Continuous h) :
    tsupport (fun x => f (h x)) ⊆ h ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hh)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

/-- The explicit tensor of two ordered positive-time inputs lies in the honest
mixed-order total-arity source surface: nonnegative times everywhere, reversed
strict order on the left block, and forward strict order on the right block. -/
theorem conjTensorProduct_tsupport_subset_fixedPairMixedOrderTimeRegion
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m) :
    tsupport (((f.conjTensorProduct g : SchwartzNPoint d (n + m)) :
      NPointDomain d (n + m) → ℂ)) ⊆ FixedPairMixedOrderTimeRegion d n m := by
  intro y hy
  have hsplitFirstRev_cont :
      Continuous (fun z : NPointDomain d (n + m) =>
        fun i : Fin n => splitFirst n m z (Fin.rev i)) := by
    refine continuous_pi ?_
    intro i
    simpa [splitFirst] using
      (continuous_apply (Fin.castAdd m (Fin.rev i)) :
        Continuous fun z : NPointDomain d (n + m) => z (Fin.castAdd m (Fin.rev i)))
  have hyprod :
      y ∈ tsupport (fun z : NPointDomain d (n + m) =>
        starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i))) *
          g (splitLast n m z)) := by
    simpa [SchwartzMap.conjTensorProduct_apply] using hy
  have hleft :
      (fun i : Fin n => splitFirst n m y (Fin.rev i)) ∈
        tsupport (f : NPointDomain d n → ℂ) := by
    have hy_left :
        y ∈ tsupport (fun z : NPointDomain d (n + m) =>
          starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i)))) :=
      (tsupport_mul_subset_left
        (f := fun z : NPointDomain d (n + m) =>
          starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i))))
        (g := fun z : NPointDomain d (n + m) => g (splitLast n m z))) hyprod
    exact tsupport_precomp_subset_local
      (f := (f : NPointDomain d n → ℂ))
      (h := fun z : NPointDomain d (n + m) => fun i : Fin n =>
        splitFirst n m z (Fin.rev i))
      hsplitFirstRev_cont
      ((tsupport_comp_subset
        (g := starRingEnd ℂ)
        (map_zero _)
        (fun z : NPointDomain d (n + m) =>
          f (fun i : Fin n => splitFirst n m z (Fin.rev i)))) hy_left)
  have hright :
      splitLast n m y ∈ tsupport (g : NPointDomain d m → ℂ) := by
    exact tsupport_precomp_subset_local
      (f := (g : NPointDomain d m → ℂ))
      (h := splitLast n m)
      (splitLast_continuousLinear n m)
      ((tsupport_mul_subset_right
        (f := fun z : NPointDomain d (n + m) =>
          starRingEnd ℂ (f (fun i : Fin n => splitFirst n m z (Fin.rev i))))
        (g := fun z : NPointDomain d (n + m) => g (splitLast n m z))) hyprod)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.1 < n
    · have hpos :
          0 < ((fun j : Fin n => splitFirst n m y (Fin.rev j)) (Fin.rev ⟨i.1, hi⟩)) 0 :=
        (hf_ord hleft (Fin.rev ⟨i.1, hi⟩)).1
      simpa [splitFirst, hi] using le_of_lt hpos
    · have hi_ge : n ≤ i.1 := Nat.not_lt.mp hi
      let j : Fin m := ⟨i.1 - n, by omega⟩
      have hij : Fin.natAdd n j = i := by
        apply Fin.ext
        simp [j, hi_ge]
      have hpos : 0 < (splitLast n m y j) 0 := (hg_ord hright j).1
      simpa [splitLast, hij] using le_of_lt hpos
  · intro i j hi hj hij
    have hrev : Fin.rev ⟨j.1, hj⟩ < Fin.rev ⟨i.1, hi⟩ := by
      simpa using (Fin.rev_lt_rev.mpr hij)
    have htime :
        ((fun k : Fin n => splitFirst n m y (Fin.rev k)) (Fin.rev ⟨j.1, hj⟩)) 0 <
          ((fun k : Fin n => splitFirst n m y (Fin.rev k)) (Fin.rev ⟨i.1, hi⟩)) 0 :=
      (hf_ord hleft (Fin.rev ⟨j.1, hj⟩)).2 (Fin.rev ⟨i.1, hi⟩) hrev
    simpa [splitFirst] using htime
  · intro i j hi hj hij
    let ii : Fin m := ⟨i.1 - n, by omega⟩
    let jj : Fin m := ⟨j.1 - n, by omega⟩
    have hii : Fin.natAdd n ii = i := by
      apply Fin.ext
      simp [ii, hi]
    have hjj : Fin.natAdd n jj = j := by
      apply Fin.ext
      simp [jj, hj]
    have hij' : ii < jj := by
      apply Fin.lt_iff_val_lt_val.mpr
      dsimp [ii, jj]
      omega
    have htime : (splitLast n m y ii) 0 < (splitLast n m y jj) 0 :=
      (hg_ord hright ii).2 jj hij'
    simpa [splitLast, hii, hjj] using htime

namespace FixedPairMixedOrderComponent

variable {n m : ℕ}

/-- Package the explicit tensor `f.conjTensorProduct g` as an honest element of
the mixed-order total-arity source object. -/
def ofConjTensorProduct
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m) :
    FixedPairMixedOrderComponent d n m :=
  ⟨f.conjTensorProduct g,
    conjTensorProduct_tsupport_subset_fixedPairMixedOrderTimeRegion
      (d := d) f hf_ord g hg_ord⟩

end FixedPairMixedOrderComponent

end OSReconstruction
