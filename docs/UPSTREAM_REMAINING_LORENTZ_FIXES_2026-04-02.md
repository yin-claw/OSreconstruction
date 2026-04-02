# Upstream Remaining Lorentz/Poincaré Fixes After `5f36d35`

Date: 2026-04-02
Repo: `OSreconstruction`
Reference upstream commit: `5f36d35` — `refactor: complete connected Lorentz/Poincare migration`

## Purpose

This note records what still appears to remain after the upstream migration that changed the default meanings of:

- `LorentzGroup d` -> connected proper-orthochronous Lorentz group
- `PoincareGroup d` -> connected proper-orthochronous Poincaré group

The goal here is **not** to restate what upstream already fixed. The goal is to isolate the **residual issues** that still look conceptually or terminologically wrong after `5f36d35`.

## Main Conclusion

Upstream `5f36d35` already fixes the **big** semantic problem.

In particular, the following foundational issue is largely resolved:
- the default Wightman/reconstruction-facing meaning of “Lorentz group” is no longer the full disconnected `O(1,d)`
- the default Wightman/reconstruction-facing meaning of “Poincare group” is no longer the full disconnected `ISO(1,d)`

So the remaining work is **narrower** than before.

What still appears to remain is mostly:
1. **stale comments/documentation that still talk like the default symmetry is full `O(1,d)`**, and
2. **one theorem-level strengthening on the boundary-values side** that still upgrades connected covariance plus time reversal into a full-Lorentz covariance statement.

---

## Residual Issue 1: stale wording in `Reconstruction/Core.lean`

File:
- `OSReconstruction/Wightman/Reconstruction/Core.lean`

### What is still wrong

The definition
- `IsLorentzCovariantWeak`

now quantifies over `LorentzGroup d`, but its comments still say things like:
- “for all `Λ ∈ O(1,d)`”
- “Lorentz covariance ... for all `Λ ∈ O(1,d)`”

That wording is stale after `5f36d35`, because upstream’s migration note says `LorentzGroup d` now means the connected proper-orthochronous group.

### Why it matters

This is exactly the kind of wording that can reintroduce conceptual confusion even after the group-level migration is mathematically correct.

### Recommended fix

Update the docstring/comments for:
- `lorentzNPointFun`
- `IsLorentzCovariantWeak`
- any nearby reconstruction-level covariance comments

so that they refer to the connected Lorentz group, not full `O(1,d)`.

If a full-group notion is still desired anywhere, it should be stated explicitly in terms of `FullLorentzGroup d`, not by stale prose attached to `LorentzGroup d`.

---

## Residual Issue 2: theorem-level full-covariance upgrade in `OSToWightmanBoundaryValuesBase.lean`

File:
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`

### What is still present

There is still a theorem:
- `lorentz_covariance_of_orthochronous_and_timeReversal`

Its role is to obtain a full Lorentz covariance conclusion from:
- connected / orthochronous covariance, and
- time reversal.

### Why this is still potentially problematic

Even after the connected-group migration, this theorem keeps alive the idea that the main covariance statement should be strengthened to the full disconnected group when time reversal is available.

That may be mathematically legitimate as a derived theorem **under extra hypotheses**, but it should not silently redefine what ordinary Lorentz symmetry means.

### Recommended fix

Keep the theorem only if it is genuinely useful, but make its role explicit:
- this is a **stronger derived theorem** using extra discrete symmetry input
- not the default meaning of Lorentz covariance

In particular, its naming/comments should make clear that this is an augmentation beyond the connected default covariance group.

---

## Residual Issue 3: main boundary-value covariance theorem still routed through the stronger upgrade

File:
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`

### What is still present

The theorem:
- `bvt_lorentz_covariant`

is still obtained by combining:
- `bvt_lorentz_covariant_orthochronous`
- `bvt_W_timeReversal`
- `lorentz_covariance_of_orthochronous_and_timeReversal`

### Why this matters

After the connected-group migration, the natural default expectation is that the main theorem-level covariance surface should stop at the connected Lorentz group unless stronger symmetry is explicitly requested.

At the moment, the main public-looking statement still flows through a theorem that uses time reversal to recover a full-group covariance theorem.

### Recommended fix

Split the theorem surface more clearly:

1. **default theorem**
   - connected Lorentz covariance only
   - this should be the ordinary boundary-value output

2. **optional stronger theorem**
   - full covariance only under the additional time-reversal/discrete-symmetry hypothesis

This would bring the theorem-level API into better conceptual alignment with the upstream group migration.

---

## Residual Issue 4: old language may still survive in docs and generated summaries

Likely files to refresh:
- `DEFINITIONS.md`
- `README.md` (if it still summarizes Lorentz/Poincaré in the old way)
- old status/proof-outline notes that still describe the default symmetry using full `O(1,d)` / `ISO(1,d)` language

### Why this matters

The migration is mathematically meaningful only if collaborators no longer read stale public prose and infer the old convention.

### Recommended fix

Do a targeted wording pass for public-facing summaries so that:
- `LorentzGroup d` is described as connected/proper-orthochronous by default
- full disconnected groups are referenced only via `FullLorentzGroup d` / `FullPoincareGroup d`

---

## What does **not** seem to remain as a major issue

The following broad concerns are now largely addressed upstream by `5f36d35`:

- foundational use of full `O(1,d)` as the default Wightman-side Lorentz group
- foundational use of full `ISO(1,d)` as the default Wightman-side Poincaré group
- need for the older Wightman-side `Restricted` wrapper layer as the main public API

So the remaining work is **not** a whole-repo conceptual rewrite.
It is a narrower cleanup of:
- stale wording, and
- one theorem-level strengthening habit on the boundary-values side.

---

## Recommended next-step order

1. **Fix stale comments in `Reconstruction/Core.lean`.**
   - Small, clear, high-value.

2. **Audit `bvt_lorentz_covariant` and its base theorem path.**
   - Decide whether the main theorem should be connected-only by default.

3. **If needed, rename or annotate the time-reversal upgrade theorem** in `OSToWightmanBoundaryValuesBase.lean` so it is clearly a stronger derived result, not the default covariance meaning.

4. **Refresh public-facing docs / generated summaries** that still describe the old full-group convention.

---

## Bottom line

After upstream `5f36d35`, the major conceptual migration is already done.

What still appears to remain upstream is mainly:
- **stale `O(1,d)` wording in reconstruction-facing comments**, and
- **a remaining boundary-values theorem path that still promotes connected covariance + time reversal into a full-Lorentz covariance result**, which may be too strong as the default theorem surface.

So the remaining upstream fix surface is now **narrow and well-defined**.
