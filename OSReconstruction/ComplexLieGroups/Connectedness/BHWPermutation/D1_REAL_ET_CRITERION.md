# d=1 Real ET Criterion (Working Note)

This note records an explicit `d=1` real-geometry criterion that is useful for
reasoning about the blocker in
`PermutationFlow.deferred_eventually_forward_eq_nhds_d1_holo`.

## 1. Setup

Fix `d=1`. For a real vector `v=(t,x) in R^(1+1)`, define lightcone
coordinates

- `u := t + x`
- `vbar := x - t`

(so `x>|t|` iff `u>0` and `vbar>0`; `x<-|t|` iff `u<0` and `vbar<0`).

For a complex rapidity `xi = a + i b`, the Lorentz matrix is

- `[[cosh xi, sinh xi], [sinh xi, cosh xi]]`.

If input is real, the imaginary part of transformed coordinates is controlled by
`sin b` and the two linear forms `u`, `vbar`.

## 2. Real-point FT criterion after complex boost

For real `v=(t,x)`, write `eta = Im(Lambda(xi) v)`. Then

- `eta_0 + eta_1 = sin(b) * exp(a) * u`
- `eta_0 - eta_1 = sin(b) * exp(-a) * vbar`

and `eta in V_+` is equivalent to

- `eta_0 + eta_1 > 0`
- `eta_0 - eta_1 > 0`.

Hence:

A real vector can be sent into `V_+` by a fixed complex boost iff `u` and
`vbar` have the same sign as `sin(b)`.

Equivalent geometric statement:

- either `x>|t|` (right spacelike cone), or
- `x<-|t|` (left spacelike cone),

with the same component choice for all vectors constrained by the same `b`.

The real rapidity `a` rescales by positive factors `exp(±a)` and does not
change signs.

## 3. Consecutive-difference consequence for real configurations

For a real configuration `y : Fin n -> R^(1+1)` viewed in the project FT model,
`realEmbed y in ET` in `d=1` requires existence of one complex boost parameter
`b` making every consecutive difference fit the same sign condition above.

So all consecutive differences must lie in one spacelike component (all right
or all left) after the same choice of sign of `sin b`.

## 4. Why this matters for the current blocker

This explains two practical facts already seen in code/work:

1. In `d=1`, a generic permutation does not admit a simple global real-anchor
   witness package (unlike `d>=2` constructions using extra spatial directions).
2. A local prepared complex anchor `(w0, Gamma)` with
   `w in FT` and `Gamma·(sigma·w) in FT` can exist without any local exact
   back-witness `Lambda·(sigma·w)=w`.

Therefore the remaining theorem
`deferred_eventually_forward_eq_nhds_d1_holo` needs a genuinely complex local
continuation mechanism, not a hidden real-anchor shortcut.

## 5. Route consequence for witness-based reductions

This criterion also explains why naive "pick one real Jost anchor and propagate"
arguments are fragile in `d=1`:

- `realEmbed y ∈ ET` requires one sign-compatible spacelike component choice
  for all consecutive differences of `y`,
- after permutation, consecutive differences are reoriented and can violate a
  common sign choice,
- so simultaneous real `ET` membership of `y` and `y ∘ σ` is not automatic.

Hence d>=2 witness constructions (which use an extra spatial direction) do not
port directly to d=1.
