# d=1, n=3 Forward-Triple Witness Table (Constructive Inputs)

This note records explicit constructive data for the `n=3` subproblem of

- `deferred_d1_forward_triple_nonempty_nontrivial`

in `PermutationFlow.lean`.

Goal shape (for fixed adjacent `tau = swap(i,i+1)` and nontrivial
`sigma ≠ 1, tau`):

- find `w` such that
  - `w ∈ FT(1,3)`,
  - `tau · w ∈ ET(1,3)`,
  - `sigma · w ∈ ET(1,3)`.

All witnesses below use integer coordinates and ET witnesses by explicit
2x2 complex Lorentz boosts of the form:

- `M(a,c,s) = [[a, s*i*c], [s*i*c, a]]`, with `a^2 + c^2 = 1`
- implemented via Pythagorean triples `(p,q,r)` with `a = p/r`, `c = q/r`,
  and sign `s ∈ {+1, -1}`.

## Conventions

- permutations in one-line notation on `Fin 3`:
  - `(1,0,2)` means swap(0,1),
  - `(0,2,1)` means swap(1,2), etc.
- `w = [w0, w1, w2]`, each `wk = (t_k, x_k) ∈ C^2`.
- For each case we list:
  - witness `w`,
  - one boost for `tau · w`,
  - one boost for `sigma · w`.

## Cases

### i = 0, tau = (1,0,2)

1. sigma = `(0,2,1)`
- `w0 = (0+6i, 0-1i)`
- `w1 = (-1+11i, 4-1i)`
- `w2 = (-2+13i, 0+0i)`
- tau boost: `(p,q,r,s) = (8,15,17,-1)`
- sigma boost: `(p,q,r,s) = (3,4,5,+1)`

2. sigma = `(1,2,0)`
- `w0 = (0+2i, 3-1i)`
- `w1 = (-1+7i, 0+1i)`
- `w2 = (-1+12i, 0+1i)`
- tau boost: `(5,12,13,+1)`
- sigma boost: `(9,40,41,+1)`

3. sigma = `(2,0,1)`
- `w0 = (0+5i, 1-1i)`
- `w1 = (0+8i, 2-1i)`
- `w2 = (-1+9i, -2-1i)`
- tau boost: `(7,24,25,-1)`
- sigma boost: `(5,12,13,+1)`

4. sigma = `(2,1,0)`
- `w0 = (-3+1i, -4+0i)`
- `w1 = (-3+3i, -3+0i)`
- `w2 = (-3+6i, -2+0i)`
- tau boost: `(5,12,13,-1)`
- sigma boost: `(7,24,25,-1)`

### i = 1, tau = (0,2,1)

1. sigma = `(1,0,2)`
- `w0 = (-1+4i, 1+1i)`
- `w1 = (-1+10i, -2+1i)`
- `w2 = (-2+14i, 4+1i)`
- tau boost: `(3,4,5,-1)`
- sigma boost: `(5,12,13,+1)`

2. sigma = `(1,2,0)`
- `w0 = (0+6i, -4+0i)`
- `w1 = (0+10i, 4+1i)`
- `w2 = (0+12i, 2+1i)`
- tau boost: `(3,4,5,+1)`
- sigma boost: `(3,4,5,-1)`

3. sigma = `(2,0,1)`
- `w0 = (1+2i, 1-1i)`
- `w1 = (-1+8i, 4+1i)`
- `w2 = (0+12i, -4+1i)`
- tau boost: `(3,4,5,+1)`
- sigma boost: `(5,12,13,+1)`

4. sigma = `(2,1,0)`
- `w0 = (1+3i, -4+1i)`
- `w1 = (1+8i, -2+0i)`
- `w2 = (1+13i, 2+0i)`
- tau boost: `(3,4,5,-1)`
- sigma boost: `(7,24,25,-1)`

## Validation status

- Each listed case was validated numerically by checking:
  - `w ∈ FT`,
  - boosted `tau · w ∈ FT` for the listed tau boost,
  - boosted `sigma · w ∈ FT` for the listed sigma boost.
- This gives ET membership witnesses by definition.

Formalization status:

- Production module:
  - `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/D1N3Witnesses.lean`
  - now contains four fully formal constructive packages:
    - `d1_n3_forward_triple_nonempty_i0_pairA`
      (covers `sigma=(1,2,0)` and `sigma=(2,1,0)`),
    - `d1_n3_forward_triple_nonempty_i0_pairB`
      (covers `sigma=(0,2,1)` and `sigma=(2,0,1)`),
    - `d1_n3_forward_triple_nonempty_i1_pairA`
      (covers `sigma=(1,0,2)` and `sigma=(1,2,0)` for `tau=(0,2,1)`).
    - `d1_n3_forward_triple_nonempty_i1_pairB`
      (covers `sigma=(2,1,0)` and `sigma=(2,0,1)` for `tau=(0,2,1)`).
  - these are wired into `PermutationFlow.lean`, so the full `n=3` branch of
    `deferred_d1_forward_triple_nonempty_nontrivial` is now constructive.

- Historical test artifact:
  - `test/d1_forward_triple_witness_n3.lean`
  - theorem `witness3_forward_triple_hard_case`
    (`i=0`, `tau=(1,0,2)`, `sigma=(2,1,0)`).

Recommended next step:

- proceed to the `n≥4` branch of
  `deferred_d1_forward_triple_nonempty_nontrivial` (the only remaining
  deferred branch inside that theorem).
