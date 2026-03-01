# d=1 n>=4 LP Reduction: Result Log (2026-03-01)

Companion files:

- `D1_NGE4_LINEAR_REDUCTION_NOTES.md`
- `scripts/d1_linear_witness_lp.py`

## Repro Commands

```bash
python3 scripts/d1_linear_witness_lp.py --n 4 --exhaustive
python3 scripts/d1_linear_witness_lp.py --n 5 --exhaustive
python3 scripts/d1_linear_witness_lp.py --n 4 --i 0 --sigma 0,2,3,1
```

## Exhaustive Results

- `n=4` nontrivial cases: `66 / 66` feasible on lambda grid.
- `n=5` nontrivial cases: `472 / 472` feasible on lambda grid.

## Sample Concrete Witness Output

Instance:

- `n=4`, `i=0`, `sigma=(0,2,3,1)`.

Script output:

- `lambda_tau = -2.0`
- `lambda_sigma = 0.25`
- `T = [2.0, 4.555555555555555, 5.555555555555555, 6.555555555555556]`
- `R = [0.0, 1.7777777777777777, -10.222222222222221, -10.222222222222223]`

This gives an explicit reduced-system witness (non-formal) for a previously
hard `n=4` case.

## Pattern Observations (Empirical)

With fixed `lambda_tau = 1`, exhaustive `n=4,5,6` runs still show feasibility
for all nontrivial cases when allowing `lambda_sigma` search on the same grid.

Observed solver-choice pattern in exhaustive data:

- only two `lambda_sigma` values were selected: `{3/2, -2}`.

Empirically, branch selection matches the order of `i` and `i+1` in `sigma^{-1}`:

- use `lambda_sigma = 3/2` when `(sigma^{-1} i).val > (sigma^{-1} (i+1)).val`,
- use `lambda_sigma = -2` otherwise.

This is not a formal theorem yet, but it is the best current proof-construction
target for closing `deferred_d1_forward_triple_nonempty_nge4`.
