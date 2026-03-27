/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

# Adapter: HilleYosida → OSreconstruction

Replaces the `semigroupGroup_bochner` axiom with a proof via the
`semigroupGroupBochner` theorem from the HilleYosida project.

## Prerequisites

Add to `lakefile.toml`:
```toml
[[require]]
name = "HilleYosida"
git = "https://github.com/mrdouglasny/hille-yosida.git"
```

Both projects must be on the same Mathlib version.

## Axioms eliminated

- `semigroupGroup_bochner` — fully proved (0 axioms, 0 sorry's)

## Axioms remaining

- `laplaceFourier_measure_unique` — not yet proved in HilleYosida
  (used in OSToWightmanK2VI1Support.lean)
-/

import HilleYosida.SemigroupGroupExtension

open MeasureTheory Complex Set Filter Finset BigOperators
open scoped Topology

noncomputable section

namespace SCV

/-- The `IsSemigroupGroupPD` definitions are definitionally equal:
`starRingEnd ℂ` and `star` coincide on `ℂ`. -/
theorem isSemigroupGroupPD_iff (d : ℕ) (F : ℝ → (Fin d → ℝ) → ℂ) :
    IsSemigroupGroupPD d F ↔ _root_.IsSemigroupGroupPD d F :=
  Iff.rfl

/-- **Semigroup-group Bochner theorem** (BCR Theorem 4.1.13).

Eliminates the `semigroupGroup_bochner` axiom by applying the fully proved
`semigroupGroupBochner` theorem from the HilleYosida project.

Hypothesis adaptation:
- `Continuous` → `ContinuousOn` on `[0,∞) × ℝ^d` (via `.continuousOn`)
- Global bound → half-space bound (drop unused `0 ≤ t`)
- `starRingEnd ℂ` vs `star` — definitionally equal on `ℂ` -/
theorem semigroupGroup_bochner' (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : Continuous (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2))
    (hbdd : ∃ C : ℝ, ∀ t a, ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        F t a = ∫ p : ℝ × (Fin d → ℝ),
          Complex.exp (-(↑(t * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂μ :=
  semigroupGroupBochner d F
    hcont.continuousOn
    (hbdd.imp fun C hC t a _ => hC t a)
    hpd

end SCV
