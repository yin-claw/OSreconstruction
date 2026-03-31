# Issue #48 local study report

Date: 2026-03-31
Repo state studied: local repo synced to `origin/main = upstream/main = 8a9031a`
Issue studied: GitHub issue #48, `Fix HasFourierLaplaceReprTempered.uniform_bound and unblock boundary_values_tempered`

## Executive summary

The issue is **real**.

The current abstraction

- `SCV.HasFourierLaplaceReprTempered.uniform_bound`

is too strong for singular Wightman boundary values if interpreted as a theorem that should follow from the OS continuation input. It asks for a ray-wise polynomial bound

- `‖F(x + i ε η)‖ ≤ C (1 + ‖x‖)^N`

uniformly for small `ε > 0`, with **no blow-up in `ε`**.

That is incompatible with the expected boundary singularities of Wightman-type holomorphic continuations. So if `full_analytic_continuation_flat_tempered_package` is supposed to produce `hunif` from honest OS data, there is a genuine mathematical problem.

At the same time, `uniform_bound` is not decorative. It is currently a load-bearing hypothesis for:

- `SCV.fourierLaplace_dist_map_add_tempered`
- `SCV.fourierLaplace_dist_map_smul_tempered`
- `SCV.fourierLaplace_boundary_recovery_on_open_of_tempered`
- and therefore for the linearity / local boundary recovery infrastructure used downstream by
  `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`.

So the issue is not just a typo in one theorem statement. It is an abstraction problem in the SCV interface.

My recommendation is:

1. **Do not try to prove the current `hunif` from OS input.**
2. **Do not immediately refactor the whole SCV layer on the main branch.**
3. First make a clear strategic choice between:
   - **Option A:** OS-local quarantine axiom at `full_analytic_continuation_flat_tempered_package`, or
   - **Option B:** full SCV refactor replacing `uniform_bound` by a Vladimirov-style global slow-growth condition and reworking the DCT-based proofs.
4. For near-term progress, the most effective move is **Option A** on a local test branch, so we can measure exactly how much of the E→R boundary-value pipeline clears once this obstruction is quarantined.

---

## 1. Exact source objects involved

### 1.1. The problematic structure field

File:
- `OSReconstruction/SCV/LaplaceSchwartz.lean`

Current structure:

```lean
structure HasFourierLaplaceReprTempered {m : ℕ} (C : Set (Fin m → ℝ))
    (F : (Fin m → ℂ) → ℂ) extends HasFourierLaplaceRepr C F where
  poly_growth : ...
  uniform_bound : ∀ (η : Fin m → ℝ), η ∈ C →
    ∃ (C_bd : ℝ) (N : ℕ) (δ : ℝ), C_bd > 0 ∧ δ > 0 ∧
      ∀ (x : Fin m → ℝ) (ε : ℝ), 0 < ε → ε < δ →
        ‖F (fun i => ↑(x i) + ↑ε * ↑(η i) * I)‖ ≤ C_bd * (1 + ‖x‖) ^ N
```

The issue’s diagnosis is exactly about this `uniform_bound` field.

### 1.2. Where the field is consumed

Also in `SCV/LaplaceSchwartz.lean`:

- `fourierLaplace_dist_map_add_tempered`
- `fourierLaplace_dist_map_smul_tempered`
- `fourierLaplace_dist_isLinearMap_tempered`
- `exists_fourierLaplaceReprTempered`

and in

- `OSReconstruction/SCV/LocalBoundaryRecovery.lean`
  - `fourierLaplace_boundary_recovery_on_open_of_tempered`

These uses are real and explicit. For example the additivity proof immediately does:

```lean
obtain ⟨C_bd, N, δ, _hC_bd_pos, hδ_pos, hbd⟩ := hTempered.uniform_bound η hη
```

and then uses `hbd` to get the DCT dominator.

### 1.3. Where the OS-side blocker sits

File:
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`

Current blocking theorem:

- `full_analytic_continuation_flat_tempered_package`

This theorem asks for:
- boundary-value functional `Tflat`,
- continuity of `Tflat`,
- boundary-value convergence,
- `hpoly`,
- `hunif`.

Then `boundary_values_tempered` packages these into:

```lean
SCV.exists_fourierLaplaceReprTempered ... hTflat_cont hBVflat hpoly hunif
```

So issue #48 is targeting the correct local source seam.

---

## 2. Why the issue is mathematically plausible

The current `uniform_bound` requires a bound that stays polynomial in `x` uniformly as `ε → 0+` along a fixed interior direction `η`.

For a singular boundary-value problem, this is too strong. Boundary values of Wightman-type holomorphic functions are tempered **distributions**, not honest boundary functions with uniform pointwise control near the edge.

The issue’s comparison with Vladimirov is plausible:
- one expects a global growth condition with additional blow-up in distance to the boundary, e.g. a factor like `Δ_C(y)^(-M)`.
- along a ray `y = ε η`, that becomes an `ε^{-M}` factor.

That is exactly the kind of singular behavior the current `uniform_bound` forbids.

I have not rederived Vladimirov’s theorem from scratch here, but the local code itself is already philosophically consistent with the issue’s criticism:

- `HasFourierLaplaceReprRegular` is for genuinely strong boundary-regular objects.
- `HasFourierLaplaceReprTempered` was introduced because singular Wightman boundary values do **not** extend continuously to the real boundary.

So it is suspicious that the tempered structure still demands a uniform pointwise boundary-ray estimate of the same qualitative type used for DCT in the regular case.

---

## 3. Exact dependency chain to boundary_values_tempered

The issue’s dependency claim is correct.

Current chain:

1. `full_analytic_continuation_flat_tempered_package`
2. `boundary_values_tempered`
3. extracted Wightman boundary package
4. downstream boundary transfer theorems:
   - `bv_translation_invariance_transfer`
   - `bv_lorentz_covariance_transfer`
   - `bv_local_commutativity_transfer`
   - `bv_positive_definiteness_transfer`
   - `bv_hermiticity_transfer`
   - `bvt_cluster`

So if the issue is right, then:
- `bvt_cluster` is downstream collateral,
- not the root problem.

---

## 4. Evaluation of the two fix strategies from the issue

## Option A — OS-local quarantine axiom

Meaning:
- leave `SCV/LaplaceSchwartz.lean` unchanged for now,
- put a local axiom/placeholder at
  `full_analytic_continuation_flat_tempered_package`,
- unblock `boundary_values_tempered` and the seven downstream boundary-value `sorry`s.

### Advantages
- small scope
- isolates the bug to the OS boundary-values lane
- does not pollute the generic SCV library with a false theorem
- immediately tests whether the downstream transfer layer is otherwise structurally sound

### Disadvantages
- does not fix the SCV abstraction
- postpones the real Fourier-Laplace representation theorem problem

### My assessment
This is the **best local test-work move** if the immediate goal is to understand how much of the E→R boundary-value pipeline can be cleared once this abstraction bug is quarantined.

It is also the safest short-term move.

---

## Option B — SCV refactor to a Vladimirov-style growth condition

Meaning:
- replace `uniform_bound` in `HasFourierLaplaceReprTempered` by a global slow-growth condition compatible with singular boundary behavior,
- rework all proofs currently using `uniform_bound` as an ε-independent DCT dominator,
- likely introduce a more sophisticated regularization/derivative argument in the style of Vladimirov.

### Advantages
- mathematically correct direction
- repairs the abstraction at the right level
- future-proofs the SCV layer for genuine singular boundary-value problems

### Disadvantages
- much larger scope
- several generic SCV theorems must be rewritten
- the new proofs are not just plumbing; they require a different analytic mechanism
- risky to attempt immediately on the main line unless we first test the downstream OS consequences

### My assessment
This is the **right long-term fix**, but **not** the best first move if the immediate question is “what actually unblocks E→R next?”

This should be done only after we have measured the payoff of the OS-local quarantine and confirmed that the downstream transfer lane is otherwise worth pushing.

---

## 5. Concrete recommendations

## Recommendation 1 — do an OS-local unblock experiment first

On a local test branch:

1. Add a temporary local axiom / placeholder for
   - `full_analytic_continuation_flat_tempered_package`
2. Build the repo and see exactly how many of the downstream seven boundary-value `sorry`s become directly attackable.
3. Record which of those are actually straightforward once `boundary_values_tempered` exists.

This will answer the practical question:
- is boundary-value extraction the real high-leverage bottleneck right now?

I expect the answer is yes, but we should verify it empirically.

## Recommendation 2 — do not try to prove the current `hunif` from OS input

I do **not** recommend spending local effort trying to prove the current `uniform_bound` for the OS continuation as it stands.

If the issue is right, that theorem is not merely hard — it is probably **false in the intended generality**.

## Recommendation 3 — prepare the SCV refactor as a separate project

If Xi wants the mathematically correct fix rather than the short-term unblock, then the refactor should be planned as a separate work package with explicit tasks:

1. design a new tempered FL structure with a Vladimirov-style global slow-growth field,
2. prove the correct integrability / linearity / recovery theorems for that structure,
3. port `boundary_values_tempered` to use the new structure,
4. only then remove the OS-local placeholder.

This is not a one-lemma patch.

## Recommendation 4 — keep the SCV and OS layers separated conceptually

The issue correctly suggests quarantining the current problem if we take the short-term route.

That is important.

We should avoid:
- hard-coding a false “generic SCV” theorem just because it holds for the one OS continuation we care about.

So:
- **generic SCV claims should stay honest**,
- **OS-local workaround should stay local**.

---

## 6. Suggested implementation plan

### Phase A — local experiment (recommended next)

Create a local branch, e.g.
- `issue48_boundary_values_local_test`

Then:

1. introduce a temporary local axiom replacing the `sorry` in
   - `full_analytic_continuation_flat_tempered_package`
2. build:
   - `OSToWightmanBoundaryValues`
   - then the full `Wightman.Reconstruction.WickRotation` subtree if feasible
3. record which of the downstream seven theorems remain genuinely hard

Deliverable:
- a short follow-up note saying exactly what this unblock clears.

### Phase B — if Phase A looks worthwhile

Attack the downstream transfer theorems in this order:

1. `bv_translation_invariance_transfer`
2. `bv_hermiticity_transfer`
3. `bv_positive_definiteness_transfer`
4. `bv_local_commutativity_transfer`
5. `bv_lorentz_covariance_transfer`
6. `bvt_cluster`

That order is only tentative, but the main point is:
- use the local placeholder to test whether these are truly mechanical or still hide major analytic gaps.

### Phase C — long-term SCV repair

Only after the above experiment:

1. redesign `HasFourierLaplaceReprTempered`
2. replace `uniform_bound`
3. rewrite the three main consumers
4. reconnect `boundary_values_tempered`

---

## 7. Final assessment

Issue #48 is not noise. It identifies a real mismatch between:
- singular tempered Wightman boundary values,
and
- the current SCV abstraction used to package them.

My final recommendation is:

### Immediate next step
**Take Option A locally**
- quarantine the problem at `full_analytic_continuation_flat_tempered_package`
- measure downstream payoff

### Strategic next step
**Plan Option B separately**
- real SCV refactor
- Vladimirov-style growth condition
- rewritten boundary-value arguments

That is the cleanest, safest, and most informative way forward.
