/-
# Proof Ideas: Connectivity Analysis for BHW Blockers

## Date: 2026-03-06

## Summary of numerical tests (all scripts in /tmp/ and /private/tmp/)

All tests run with seed 20260306 unless stated.

### Test 1: FT ∩ PFT_{swap⁻¹} = ∅ (d=1, n=2)
Script: /tmp/connectivity_expanded_tests.py
Result: 0/5000 trials found z with z ∈ FT AND (z₁,z₀) ∈ FT.
STATUS: CONFIRMED ✓

Proof: Im(z₁-z₀) ∈ V⁺ (FT condition at k=1) and Im(z₀-z₁) = -Im(z₁-z₀) ∈ V⁺
(PFT_{swap} condition). But V⁺ is a strict cone: V⁺ ∩ (-V⁺) = {0}.
Since Im(z₁-z₀) ∈ V⁺ requires Im(z₁-z₀)[0] > 0 strictly, impossible to also have
-Im(z₁-z₀)[0] > 0. QED.

### Test 2: {z | (z₁,z₀) ∈ FT} ⊄ ET (pure CLG orbit, no permutations)
Script: /tmp/et_vs_pet_test.py
Result: 138/200 samples (69%) with (z₁,z₀) ∈ FT are NOT in ET.
STATUS: CONFIRMED ✓

This means permSeedSet = ET ∩ {z | z∘σ⁻¹ ∈ FT} is a PROPER subset of
{z | z∘σ⁻¹ ∈ FT} (which is convex). So the blocker is GENUINE.

### Test 3: permSeedSet(1, 2, swap) is connected
Script: /private/tmp/permseed_d1n2_refined.py
Result: 4 seeds × 4000 samples each, k ∈ {5,10,20,40,80}: ALL n_components=1.
STATUS: SUPPORTED ✓ (strongly)

Note: The sampler uses z = Λ·w (w ∈ FT) to get z ∈ ET, then checks (z₁,z₀) ∈ FT.
This is the correct definition of permSeedSet.

### Test 4: D = PET ∩ (PET - c) is connected (isConnected_permutedExtendedTube_inter_translate)
Scripts: /private/tmp/isConnected_PET_inter_translate_d1n2.py,
         /tmp/connectivity_expanded_tests.py
Result:
- c = 0: CONNECTED (sanity check)
- c real (1+0i, 0.5+0i): CONNECTED (since Im(z+c) = Im(z), PET-c = PET)
- c = (0.3i, 0): CONNECTED
- c = (0.5i, 0.3i): CONNECTED
- c = (0.5+0.3i, 0.2+0.1i): CONNECTED
- c = (-0.4+0.6i, 0.1-0.2i): CONNECTED
- c = (0.2+0.8i, -0.3+0.2i): CONNECTED
- c = (0.8i, 0): CONNECTED
- c = (0.5i, 0.4i): CONNECTED
Wick temporal shifts a0 ∈ {0.3, 0.5, 1.0, 2.0, 5.0}: ALL CONNECTED
STATUS: STRONGLY SUPPORTED ✓

---

## Definitions (Lean conventions)

### ExtendedTube (ET) — PURE CLG orbit, NO permutations
```
def ExtendedTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ (Λ : ComplexLorentzGroup d),
    { z | ∃ w ∈ ForwardTube d n, z = complexLorentzAction Λ w }
```
Note: ET ≠ PET. ET only uses boosts, NOT permutations.

### PermutedExtendedTube (PET) — includes permutations
PET = ∪_π permAct(π)(ET) = ∪_{Λ,π} {z | Λ·(z∘π) ∈ FT}

### permSeedSet
```
permSeedSet n σ = ExtendedTube d n ∩ {z | z∘σ⁻¹ ∈ FT}
               = ⋃_Λ (Λ·FT ∩ {z | z∘σ⁻¹ ∈ FT})  [by permSeedSet_eq_iUnion_seedSlice]
```
Each "slice" SeedSlice(Λ) = Λ·FT ∩ {z | z∘σ⁻¹ ∈ FT} is convex (intersection of
two convex sets). But the UNION is not trivially connected.

---

## Proof Strategy for blocker_isConnected_permSeedSet_nontrivial

### For d ≥ 2: Use JostWitnessGeneralSigma
JostWitnessGeneralSigma provides: for any σ ≠ 1 and n ≥ 2, there exists a "Jost point"
z_J ∈ JostSet ⊆ FT such that z_J ∘ σ ∈ FT (using spatial j=2 Wick rotation to flip
the time ordering). Moreover z_J is REAL, so it lies in every CLG-translate Λ·FT that
contains it.

This gives a base point z_J ∈ permSeedSet (via Λ=id, z_J ∈ FT and z_J∘σ⁻¹ ∈ FT).

From this base point:
1. Every other point p ∈ permSeedSet can be connected to z_J via a CLG path.
2. The CLG acts continuously on each Λ-slice, so the orbit of z_J under CLG covers
   a connected neighborhood of permSeedSet.

For d ≥ 2, this strategy works (JostWitnessGeneralSigma is proved for d ≥ 2).

### For d = 1: No real Jost witnesses → different approach needed

The d1n2_blocker_analysis.lean documents why real Jost witnesses fail for d=1.

#### Key constraint for d=1 permSeedSet(1, 2, swap):
permSeedSet = {Λ·w | w ∈ FT, (Λ·w)₁ := Λ·w₁ ∈ ET' and (Λ·(w₁,w₀))[1] = Λ·w₀ ∈ V⁺}
           = {z = Λ·w ∈ ET | Im(z₁) ∈ V⁺ and Im(z₀-z₁) ∈ V⁺}

For z = Λ(θ)·w with w ∈ FT (d=1, n=2):
- Im(w₀) ∈ V⁺ and Im(w₁-w₀) ∈ V⁺ (FT conditions)
- Need: Im(Λ·w₁) ∈ V⁺ and Im(Λ·(w₀-w₁)) ∈ V⁺

Since Im(w₀-w₁) = -Im(w₁-w₀) ∈ -V⁺, we need Λ to "flip" this into V⁺.
For θ = s + iτ with τ ∈ (π/2, 3π/2): Im(cosh(θ)) < 0, Im(sinh(θ)) < 0.
So Im(Λ·v) ≈ Im(cosh(θ))·v_t + Im(sinh(θ))·v_x can flip signs.

#### Potential connectivity proof for d=1:

Approach A: Direct path construction
For any two points z₀, z₁ ∈ permSeedSet, find a path θ(t) ∈ ℂ connecting the
boost parameters, such that Λ(θ(t))·w(t) remains in permSeedSet.

This requires the set of valid boost parameters θ (for a fixed w ∈ FT such that
Λ(θ)·w ∈ permSeedSet) to be connected. Numerical evidence suggests this set is
always connected (full range of τ ∈ (π/2, 3π/2) often works).

Approach B: Via permSeedSet_eq_iUnion_seedSlice + adjacent slices overlap
From SeedSlices.lean (proved): permSeedSet = ⋃_Λ seedSlice(Λ).
Each seedSlice is convex (hence preconnected).
If any two non-empty slices seedSlice(Λ₁) and seedSlice(Λ₂) share a point (overlap),
then they're in the same connected component.

For d=1: The CLG(1) is ℂ* (parametrized by θ ∈ ℂ), so the slices form a 2-parameter
family. Adjacent boosts θ → θ+ε give overlapping slices (by continuity of CLG action
and openness of FT). So all non-empty slices are connected to each other, making the
union connected.

Approach C: Via IndexSetD1.lean (may already have structure)
The IndexSetD1.lean in BHWPermutation may provide a finite decomposition (finite
index set for CLG orbits in the d=1 case) that makes the connectivity argument finite.

Approach D: Convexity of permSeedSet for d=1
CHECK: Is permSeedSet itself convex for d=1, n=2?
The set {z | z ∈ ET ∧ (z₁,z₀) ∈ FT} is intersection of ET (which is NOT convex:
ET = ⋃ Λ·FT, not an intersection) with a convex half-plane condition.
ET is a TUBE DOMAIN (intersection of halfspaces in Im direction), so it IS convex!

Wait: ET = {z | ∃ Λ: Λ·z ∈ FT}. Is this convex?
FT is defined by Im conditions: Im(z_k - z_{k-1}) ∈ V⁺. After applying Λ: Im(Λ·z_k - Λ·z_{k-1}) ∈ V⁺.
This is: Im(Λ·(z_k - z_{k-1})) ∈ V⁺ where Λ is a fixed complex matrix.

For fixed Λ, the set {z | Λ·z ∈ FT} IS convex (inverse image under linear map of
convex set). But ET = ⋃_Λ {z | Λ·z ∈ FT} is a UNION, so ET is generally NOT convex.

However, ET might still be convex for d=1! For d=1 the CLG is SO(1,1;ℂ) ≅ ℂ.
The union ⋃_{θ ∈ ℂ} Λ(θ)·FT... each Λ(θ)·FT is a convex set, and taking the union
over all θ might still yield a convex set. Numerical evidence (all 9 D_c tests connected)
suggests the geometry is nice.

APPROACH D CONCLUSION: Likely needs separate investigation. Not obviously convex.

---

## Proof Strategy for isConnected_permutedExtendedTube_inter_translate

### Case: c purely real (Im(c) = 0)
PET is defined purely by Im conditions. For real c, z + c has the same imaginary part
as z. So z ∈ PET iff z+c ∈ PET (since PET conditions only involve Im(z_k - z_{k-1})).
Hence D = PET ∩ (PET - c) = PET. PET is connected. QED.

This covers:
- Any real Minkowski shift c ∈ ℝ^{d+1}
- Wick rotation of purely spatial translations (a_0 = 0): wick(0, a_1) = (0, a_1) ∈ ℝ^{d+1}
- Translation by wick(a) with Im(wick(a)) = 0, i.e., a_0 = 0.

### Case: c = wick(a) with a_0 ≠ 0 (temporal component)
wick(a₀, a₁) = (i·a₀, a₁). This has Im(c) = (a₀, 0) ≠ 0 for a₀ ≠ 0.
D = PET ∩ {z | z + wick(a) ∈ PET} is a proper subset of PET.

Numerically CONNECTED for all tested a₀ ∈ {0.3, 0.5, 0.8, 1.0, 2.0, 5.0}.

#### Proof sketch (unfinished):
- PET is "tube-like" in the imaginary direction: PET is defined by Im(z_k - z_{k-1}) ∈ V⁺.
- Translation by wick(a): Im((z+c)_k - (z+c)_{k-1}) = Im(z_k - z_{k-1}) since c is added
  uniformly to all k. So PET condition for z+c is: Im(z_k - z_{k-1}) ∈ V⁺ (SAME as for z)!

Wait: the PET condition for z+c is: ∃ Λ, π: Λ·((z+c)∘π) ∈ FT.
(z+c)∘π = z∘π + c∘π. But c is a CONSTANT (same for all k), so (c∘π)_k = c for all k.
(z+c)∘π = z∘π + c (where c is broadcast to all positions).
Λ·(z∘π + c) = Λ·(z∘π) + Λ·c.

So z+c ∈ PET iff ∃ Λ, π: Λ·(z∘π) + Λ·c ∈ FT.

For c ≠ 0, Λ·c ≠ c in general (since Λ is a boost). So the condition IS nontrivial.

The FT condition for w = Λ·(z∘π) + Λ·c ∈ FT:
- Im(w_0) ∈ V⁺: Im(Λ·z∘π(0) + Λ·c) = Im(Λ·z∘π(0)) + Im(Λ·c) ∈ V⁺
- Im(w_k - w_{k-1}) = Im(Λ·(z∘π(k) - z∘π(k-1))) ∈ V⁺

Note: the DIFFERENCES w_k - w_{k-1} don't depend on c (it cancels)! Only the
FIRST term w_0 depends on c.

So z+c ∈ PET iff ∃ Λ, π: Im(Λ·z∘π(0) + Λ·c) ∈ V⁺ AND Im(Λ·(z∘π(k) - z∘π(k-1))) ∈ V⁺ ∀k≥1.

Compare: z ∈ PET iff ∃ Λ', π': Im(Λ'·z∘π'(0)) ∈ V⁺ AND Im(Λ'·differences) ∈ V⁺.

D = PET ∩ (PET - c) = {z ∈ PET | z+c ∈ PET}.

The difference conditions are the SAME for z and z+c (with the same Λ,π)! Only the
first-point condition changes.

This suggests D might be characterizable purely through the "difference" cone structure,
which is translation-invariant, plus constraints on the first point.

#### The standard physics approach (difference variables):
Standard Schwinger functions use DIFFERENCE variables: ζ_k = x_{k+1} - x_k ∈ Euclidean.
The analyticity domain in terms of differences is manifestly translation-invariant.
This is Streater-Wightman's approach.

In difference variables, the tube domain becomes {ζ | Im(ζ_k) ∈ V⁺}  (n-1 differences
for n+1 points), which is a CONVEX set, manifestly invariant under translation of the
original variables.

The formalization uses cumulative-sum variables rather than difference variables.
The connectivity of D in cumulative-sum variables should follow from:
1. The difference-variable description is invariant
2. Connectedness of the difference domain
3. The map between cumulative-sum and difference variables is a bijection

This gives a cleaner proof strategy but requires reformulating the FT/PET in difference
variables first.

---

## Next Steps

### For blocker_isConnected_permSeedSet_nontrivial:
1. Implement Approach B (adjacent slice overlap via CLG continuity) systematically
2. Check if IndexSetD1.lean provides needed finite decomposition
3. Try Approach A (direct path construction) for the d=1 case specifically

### For isConnected_permutedExtendedTube_inter_translate:
1. First prove the easy case: c purely real → D = PET → connected. This handles spatial
   Euclidean shifts and gives a partial sorry removal.
2. For general c: use the difference-variable characterization to reduce to convexity.

### Files to read next:
- /Users/xiyin/OSReconstruction/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/IndexSetD1.lean
- /Users/xiyin/OSReconstruction/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean
- /Users/xiyin/OSReconstruction/OSReconstruction/ComplexLieGroups/Connectedness/PermutedTubeConnected.lean
  (to understand how PET connectivity was proved — could be adapted)
-/

/-
## Derivative Approach (2026-03-08)

### Key Lemma: Translation Derivative Vanishes on PET

**Claim**: For each μ, the holomorphic function h_μ(z) = Σ_k ∂F_ext/∂z_{k,μ}(z) vanishes on PET.

**Proof sketch**:
1. h_μ is holomorphic on PET (F_ext is holomorphic, so its partial derivatives are holomorphic)
2. On FT: F_ext = W_analytic, and W_analytic is translation-invariant (proved:
   `W_analytic_translation_on_forwardTube`). So h_μ = 0 on FT.
3. FT ⊆ PET is open and nonempty. PET is connected (proved: `permutedExtendedTube_isPreconnected`).
4. By identity theorem: h_μ = 0 on all of PET. ∎

### Consequence: Telescoping in Difference Variables

In difference coordinates ζ₀ = z₀, ζ_k = z_k - z_{k-1} (k ≥ 1):
  Σ_k ∂/∂z_{k,μ} = ∂/∂ζ₀,μ  (telescoping!)

So h_μ = 0 means ∂F_ext/∂ζ₀ = 0 on PET — F_ext has ZERO derivative in the base-point direction.

### Gap: Fiber Connectivity

∂F_ext/∂ζ₀ = 0 on PET means F_ext is constant on each connected component of the fiber
F_ζ = {ζ₀ : (ζ₀, ζ₀+ζ₁, ζ₀+ζ₁+ζ₂, ...) ∈ PET} for fixed differences ζ₁,...,ζ_{n-1}.

For z, z+c ∈ PET with c constant: z₀ and z₀+c are both in F_ζ (same differences).
So F_ext(z) = F_ext(z+c) iff z₀ and z₀+c are in the SAME connected component of F_ζ.

**Fiber Connectivity Claim**: F_ζ is connected (for each valid ζ).

Proof sketch (not formalized):
- For each (π, Λ), the sector fiber F_ζ^{π,Λ} = {ζ₀ : Λ·config(ζ₀,ζ)∘π ∈ FT} is CONVEX
  (preimage of convex FT under affine map).
- F_ζ = ⋃_{π,Λ} F_ζ^{π,Λ} is a union of convex sets.
- Adjacent sector fibers overlap (via Jost witness arguments restricted to the fiber).
- By `iUnion_of_reflTransGen`: F_ζ is connected.

This fiber connectivity is SIMPLER than D = PET ∩ (PET-c) connectivity because:
(a) It's in ℂ^{d+1} (one base point) rather than ℂ^{n(d+1)}
(b) Each sector fiber is convex (not just preconnected)
(c) The adjacency argument is essentially the same as in PermutedTubeConnected.lean

### Alternative: Common Lorentz-Perm Witness

For z, z+c ∈ PET, if we can find (π, Λ) with BOTH Λ·(z∘π) ∈ FT AND Λ·((z+c)∘π) ∈ FT:

  F_ext(z+c) = F_ext((z+c)∘π) = F_ext(Λ·((z+c)∘π))       [perm+Lorentz inv]
            = W_an(Λ·((z+c)∘π))                             [BHW prop 2, FT membership]
            = W_an(Λ·(z∘π) + Λ·c)                           [linearity of Lorentz action]
            = W_an(Λ·(z∘π))                                  [translation inv on FT]
            = F_ext(Λ·(z∘π)) = F_ext(z∘π) = F_ext(z)        [BHW prop 2 + perm+Lorentz inv]

Key fact: Λ·((z+c)∘π) = Λ·(z∘π) + Λ·c because c is constant across particles.
So successive differences are unchanged; only k=0 base condition shifts.

For a.e. Euclidean x with Λ=1 (identity): works when min time > max(0, -a₀).
For general z ∈ PET: may need Λ ≠ 1 and scaling argument.

### Status

The derivative approach reduces `isConnected_permutedExtendedTube_inter_translate` to
fiber connectivity of F_ζ, which is a potentially simpler geometric question.
The common-witness approach gives a direct proof chain but requires existence of common witnesses.
Neither approach has been fully formalized. The sorry remains.

-/

-- Placeholder to make this a valid Lean file
section ConnectivityAnalysis
end ConnectivityAnalysis
