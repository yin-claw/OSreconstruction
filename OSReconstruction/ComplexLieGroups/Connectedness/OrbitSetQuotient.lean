import OSReconstruction.ComplexLieGroups.Connectedness.OrbitSetBasic

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d : ℕ}

/-- Subgroup stabilizer of `w` for the complex Lorentz action. -/
abbrev stabilizerSubgroup {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    Subgroup (ComplexLorentzGroup d) :=
  MulAction.stabilizer (ComplexLorentzGroup d) w

/-- Orbit quotient points whose represented configuration lies in the forward tube. -/
abbrev orbitQuotTube {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    Set (ComplexLorentzGroup d ⧸ stabilizerSubgroup w) :=
  {q | MulAction.ofQuotientStabilizer (ComplexLorentzGroup d) w q ∈ ForwardTube d n}

/-- Restrict the quotient projection to `orbitSet w`, landing in `orbitQuotTube w`. -/
abbrev orbitSetToQuotTube {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    orbitSet w → orbitQuotTube w :=
  fun Λ =>
    ⟨(QuotientGroup.mk (Λ : ComplexLorentzGroup d) :
      ComplexLorentzGroup d ⧸ stabilizerSubgroup w), by
      simpa [orbitQuotTube, MulAction.ofQuotientStabilizer_mk] using
        (show complexLorentzAction (Λ : ComplexLorentzGroup d) w ∈ ForwardTube d n from
          Λ.property)⟩

/-- Continuity of `ofQuotientStabilizer` for the Lorentz action follows from the
    quotient-map characterization of `QuotientGroup.mk`. -/
theorem continuous_ofQuotientStabilizer {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) :
    Continuous (MulAction.ofQuotientStabilizer (ComplexLorentzGroup d) w) := by
  refine (QuotientGroup.isQuotientMap_mk (N := stabilizerSubgroup w)).continuous_iff.mpr ?_
  simpa [Function.comp, MulAction.ofQuotientStabilizer_mk] using
    (continuous_complexLorentzAction_fst w)

/-- The quotient-tube subset is open in `G ⧸ Stab(w)`. -/
theorem isOpen_orbitQuotTube {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) :
    IsOpen (orbitQuotTube w) := by
  exact isOpen_forwardTube.preimage (continuous_ofQuotientStabilizer (d := d) (n := n) w)

/-- The restricted quotient projection `orbitSet w → orbitQuotTube w` is a quotient map. -/
theorem orbitSetToQuotTube_isQuotient {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) :
    Topology.IsQuotientMap (orbitSetToQuotTube (d := d) (n := n) w) := by
  let mkq : ComplexLorentzGroup d → ComplexLorentzGroup d ⧸ stabilizerSubgroup w :=
    QuotientGroup.mk
  have hqmk : Topology.IsQuotientMap mkq :=
    QuotientGroup.isQuotientMap_mk (N := stabilizerSubgroup w)
  have hopen : IsOpen (orbitQuotTube (d := d) (n := n) w) :=
    isOpen_orbitQuotTube (d := d) (n := n) w
  have hq_restrict : Topology.IsQuotientMap ((orbitQuotTube w).restrictPreimage mkq) :=
    hqmk.restrictPreimage_isOpen hopen
  simpa [orbitSetToQuotTube, orbitSet, orbitQuotTube, mkq, stabilizerSubgroup,
    MulAction.ofQuotientStabilizer_mk] using hq_restrict

/-- The set-based stabilizer predicate agrees with the subgroup carrier. -/
lemma stabilizer_eq_subgroup_carrier {n : ℕ} (w : Fin n → Fin (d + 1) → ℂ) :
    stabilizer w = (stabilizerSubgroup w : Set (ComplexLorentzGroup d)) := by
  ext g
  rfl

/-- Quotient-tube reduction: connected stabilizer + preconnected quotient-tube codomain
    imply preconnectedness of `orbitSet w`. -/
theorem orbitSet_isPreconnected_of_stabilizer_connected_quotTube {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) (hw : w ∈ ForwardTube d n)
    (hstab_conn : IsConnected (stabilizer w))
    [PreconnectedSpace (orbitQuotTube w)] :
    IsPreconnected (orbitSet w) := by
  have hquot : Topology.IsQuotientMap (orbitSetToQuotTube (d := d) (n := n) w) :=
    orbitSetToQuotTube_isQuotient (d := d) (n := n) w
  have hFib : ∀ y : orbitQuotTube w,
      IsConnected ((orbitSetToQuotTube (d := d) (n := n) w) ⁻¹' ({y} : Set _)) := by
    intro y
    let Λy : ComplexLorentzGroup d := Quotient.out y.1
    have hΛy : (QuotientGroup.mk Λy : ComplexLorentzGroup d ⧸ stabilizerSubgroup w) = y.1 :=
      Quotient.out_eq y.1
    set A : Set (ComplexLorentzGroup d) :=
      {Λ | (QuotientGroup.mk Λ : ComplexLorentzGroup d ⧸ stabilizerSubgroup w) = y.1} with hA_def
    have hA_sub : A ⊆ orbitSet w := by
      intro Λ hΛA
      have hyFT : MulAction.ofQuotientStabilizer (ComplexLorentzGroup d) w y.1
          ∈ ForwardTube d n := y.2
      have hyFT_mk :
          MulAction.ofQuotientStabilizer (ComplexLorentzGroup d) w
            (QuotientGroup.mk Λ : ComplexLorentzGroup d ⧸ stabilizerSubgroup w)
            ∈ ForwardTube d n := by
        simpa [hΛA.symm] using hyFT
      simpa [orbitSet, MulAction.ofQuotientStabilizer_mk] using hyFT_mk
    have hA_eq_coset_image :
        A = (fun g : stabilizer w => Λy * g.1) '' Set.univ := by
      ext Λ
      constructor
      · intro hΛA
        have hmk : (QuotientGroup.mk Λy : ComplexLorentzGroup d ⧸ stabilizerSubgroup w) =
            (QuotientGroup.mk Λ : ComplexLorentzGroup d ⧸ stabilizerSubgroup w) := by
          simpa [hΛy] using hΛA.symm
        have hrel : Λy⁻¹ * Λ ∈ stabilizerSubgroup w :=
          (QuotientGroup.eq).mp hmk
        refine ⟨⟨Λy⁻¹ * Λ, ?_⟩, Set.mem_univ _, ?_⟩
        · simpa [stabilizer_eq_subgroup_carrier (d := d) (n := n) w] using hrel
        · simp
      · rintro ⟨g, -, rfl⟩
        have hg_sub : (g.1 : ComplexLorentzGroup d) ∈ stabilizerSubgroup w := by
          simp
        have hmk_eq :
            (QuotientGroup.mk (Λy * (g.1 : ComplexLorentzGroup d)) :
              ComplexLorentzGroup d ⧸ stabilizerSubgroup w) =
            QuotientGroup.mk Λy := by
          exact (QuotientGroup.eq).2 (by simp [hg_sub])
        simp [A, hΛy]
    have hA_conn : IsConnected A := by
      let f : stabilizer w → ComplexLorentzGroup d := fun g => Λy * g.1
      have hf_cont : Continuous f := by
        exact continuous_const.mul continuous_subtype_val
      have hIm_conn : IsConnected (f '' (Set.univ : Set (stabilizer w))) := by
        letI : ConnectedSpace (stabilizer w) := Subtype.connectedSpace hstab_conn
        simpa [f] using (isConnected_univ.image f hf_cont.continuousOn)
      simpa [hA_eq_coset_image, f] using hIm_conn
    let incl : A → orbitSet w := fun g => ⟨g.1, hA_sub g.2⟩
    have h_incl_cont : Continuous incl :=
      continuous_subtype_val.subtype_mk (fun g => hA_sub g.2)
    have h_range_conn : IsConnected (Set.range incl) := by
      letI : ConnectedSpace A := Subtype.connectedSpace hA_conn
      exact isConnected_range h_incl_cont
    have h_range_eq :
        Set.range incl =
          ((orbitSetToQuotTube (d := d) (n := n) w) ⁻¹' ({y} : Set _)) := by
      ext Λ
      constructor
      · rintro ⟨g, rfl⟩
        rcases g with ⟨g, hgA⟩
        apply Subtype.ext
        simpa [orbitSetToQuotTube, A] using hgA
      · intro hΛ
        have hmk :
            (QuotientGroup.mk (Λ : ComplexLorentzGroup d) :
              ComplexLorentzGroup d ⧸ stabilizerSubgroup w) = y.1 := by
          exact congrArg Subtype.val hΛ
        have hΛA : (Λ : ComplexLorentzGroup d) ∈ A := by
          simpa [A] using hmk
        refine ⟨⟨(Λ : ComplexLorentzGroup d), hΛA⟩, ?_⟩
        ext
        rfl
    simpa [h_range_eq] using h_range_conn
  haveI : Nonempty (orbitSet w) :=
    ⟨⟨1, by simpa [orbitSet, complexLorentzAction_one] using hw⟩⟩
  haveI : PreconnectedSpace (orbitSet w) :=
    IsQuotientMap.preconnectedSpace_of_connectedFibers
      (f := orbitSetToQuotTube (d := d) (n := n) w) hquot hFib
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

/-- If the stabilizer is connected and the restricted orbit map is quotient onto a
    preconnected image, then the orbit set is preconnected.

    This discharges the fiber-connectedness premise in
    `orbitSet_isPreconnected_of_quotientData` from stabilizer connectedness via
    the explicit coset description of orbit-map fibers. -/
theorem orbitSet_isPreconnected_of_stabilizer_connected {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) (hw : w ∈ ForwardTube d n)
    (hstab_conn : IsConnected (stabilizer w))
    (hquot : Topology.IsQuotientMap
      (fun Λ : orbitSet w =>
        (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ : orbitMap w '' orbitSet w)))
    [PreconnectedSpace (orbitMap w '' orbitSet w)] :
    IsPreconnected (orbitSet w) := by
  refine orbitSet_isPreconnected_of_quotientData (d := d) (n := n) w hw hquot ?_
  intro y
  rcases y with ⟨yval, hyim⟩
  rcases hyim with ⟨Λy, hΛy_orbit, rfl⟩
  set A : Set (ComplexLorentzGroup d) :=
    (orbitMap w) ⁻¹' ({orbitMap w Λy} : Set (Fin n → Fin (d + 1) → ℂ)) with hA_def
  have hyFT : orbitMap w Λy ∈ ForwardTube d n := by
    simpa [orbitSet, orbitMap] using hΛy_orbit
  have hA_sub : A ⊆ orbitSet w := by
    intro g hgA
    have hgEq : orbitMap w g = orbitMap w Λy := by
      simpa [A, Set.mem_preimage, Set.mem_singleton_iff] using hgA
    have hgEq' : complexLorentzAction g w = complexLorentzAction Λy w := by
      simpa [orbitMap] using hgEq
    change complexLorentzAction g w ∈ ForwardTube d n
    rw [hgEq']
    exact hyFT
  have hA_pre : IsPreconnected A := by
    have hA' := fiber_orbitMap_isPreconnected_of_stabilizer (d := d) (n := n) w
      hstab_conn.isPreconnected Λy
    simpa [A] using hA'
  have hA_nonempty : A.Nonempty := ⟨Λy, by simp [A]⟩
  have hA_conn : IsConnected A := ⟨hA_nonempty, hA_pre⟩
  let incl : A → orbitSet w := fun g => ⟨g.1, hA_sub g.2⟩
  have h_incl_cont : Continuous incl :=
    continuous_subtype_val.subtype_mk (fun g => hA_sub g.2)
  have h_range_conn : IsConnected (Set.range incl) := by
    letI : ConnectedSpace A := Subtype.connectedSpace hA_conn
    exact isConnected_range h_incl_cont
  let y0 : orbitMap w '' orbitSet w := ⟨orbitMap w Λy, ⟨Λy, hΛy_orbit, rfl⟩⟩
  have h_range_eq :
      Set.range incl =
        ((fun Λ : orbitSet w =>
            (⟨orbitMap w Λ, ⟨Λ, Λ.property, rfl⟩⟩ :
              orbitMap w '' orbitSet w)) ⁻¹' ({y0} : Set _)) := by
    ext Λ
    constructor
    · rintro ⟨g, rfl⟩
      rcases g with ⟨g, hg⟩
      apply Subtype.ext
      have hgEq : orbitMap w g = orbitMap w Λy := by
        simpa [A, Set.mem_preimage, Set.mem_singleton_iff] using hg
      simpa [incl] using hgEq
    · intro hΛ
      have hEq : orbitMap w (Λ : ComplexLorentzGroup d) = orbitMap w Λy := by
        exact congrArg Subtype.val hΛ
      have hΛA : (Λ : ComplexLorentzGroup d) ∈ A := by
        simpa [A, Set.mem_preimage, Set.mem_singleton_iff] using hEq
      refine ⟨⟨(Λ : ComplexLorentzGroup d), hΛA⟩, ?_⟩
      ext
      rfl
  simpa [h_range_eq, y0] using h_range_conn

/-- Combined reduction for orbit-set preconnectedness:
    connected stabilizer + preconnected orbit image + openness of the global orbit map. -/
theorem orbitSet_isPreconnected_of_stabilizer_connected_and_openOrbitMap {n : ℕ}
    (w : Fin n → Fin (d + 1) → ℂ) (hw : w ∈ ForwardTube d n)
    (hstab_conn : IsConnected (stabilizer w))
    (hopen : IsOpenMap (orbitMap w))
    [PreconnectedSpace (orbitMap w '' orbitSet w)] :
    IsPreconnected (orbitSet w) := by
  have hopen_restr :=
    orbitMap_restricted_isOpen_of_global (d := d) (n := n) w hopen
  have hquot :=
    orbitSet_restricted_orbitMap_isQuotient (d := d) (n := n) w
      (hopen_restr.subtype_mk (fun Λ => ⟨Λ, Λ.property, rfl⟩))
  exact orbitSet_isPreconnected_of_stabilizer_connected (d := d) (n := n) w hw hstab_conn hquot

end BHW
