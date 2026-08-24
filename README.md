# LagTwoPositivity

Notice：I'm Japanese and not a native English speaker, so I'm using an LLM for translation!

A single, self-contained Lean 4 file about **lag-coupled quadratic forms over nonnegative
integer signals**: the exact block-decomposition (GD) identity, the fact that only lags `≥ 2`
can cross a block boundary, preservation of any pointwise denominator, and a Rayleigh
transfer stated entirely in `Int`.

**No Mathlib. No Batteries. Lean 4 core only — the file has zero `import` lines.**

| | |
|---|--:|
| source | `LagTwoPositivity.lean`, 954 lines |
| theorems | 60 |
| definitions | 19 |
| `example`s checked by `decide` | 34 |
| build-time exhaustive sweeps | 8 |
| clean build (`rm -rf .lake/build && lake build`) | ~2.8 s |
| dependencies to fetch | none |

## Definitions

For integer coefficients `a b c` and `x : List Int`,

```
Q a b c x = Σ_i a·x_i²  +  Σ_i b·x_i·x_{i+1}  +  Σ_i c·x_i·x_{i+2}
```

(all indices taken only inside range), with

```
blocks x  = the maximal runs of strictly positive entries of x
iso x     = Σ over i with x_i = 0, x_{i-1} > 0, x_{i+1} > 0  of  x_{i-1}·x_{i+1}
Nonneg x  = every entry of x is ≥ 0
sqnorm x  = Σ_i x_i²
D d x     = Σ_i d (x_i)
```

`blocks` is defined by structural recursion, so no well-founded recursion and no termination
obligation. `blocks_pos` and `blocks_mem_ne_nil` are the correctness witnesses for the phrase
"maximal run of strictly positive entries": every block is nonempty and every entry of every
block is `> 0`.

## Part 0 — lag 2

| theorem | statement |
|---|---|
| `gd_identity` | `Nonneg x → Q x = Σ_{B ∈ blocks x} Q B + c · iso x` |
| `isolated_zero_strict` | `Nonneg x → 0 < c → 0 < iso x → Σ_B Q B < Q x` |
| `sharpness_at_zero` | `Q a b 0 [1,1,0,1,1] = 2 · Q a b 0 [1,1]` |

`gd_identity'` and `isolated_zero_strict'` restate the first two with nonnegativity written
as `∀ v ∈ x, 0 ≤ v` and with the block sum spelled out as `((blocks x).map (Q a b c)).sum`.

### Why nonnegativity is required

`gd_identity` is **false** without it. For `x = [1,-1,1]` the positive runs are `[[1],[1]]`
and `iso x = 0`, so the right-hand side is `2a`, while `Q x = 3a − 2b + c`.
Nonnegativity forces every non-block entry to be exactly `0`; that is what kills the lag-1
cross-boundary term and turns the lag-2 cross-boundary term into `iso`.

## Part 1 — arbitrary lag-coefficient list

`Qgen coef x = Σ_{L < coef.length} coef[L] · Σ_i x_i · x_{i+L}`.

| theorem | statement |
|---|---|
| `Q_eq_Qgen` | `Q a b c x = Qgen [a,b,c] x` |
| `gd_identity_general` | `Nonneg x → Qgen coef x = Σ_B Qgen coef B + crossDefect coef x` |
| `straddle_lag_ge_two` | the lag-1 coefficient cancels identically out of `crossDefect` |
| `adjacent_same_block` | `0 < x_i`, `0 < x_{i+1}` → both lie in one and the same block |
| `crossDefect_abc` | `Nonneg x → crossDefect [a,b,c] x = c · iso x` |
| `gd_identity_is_specialization` | `gd_identity` re-derived from `gd_identity_general` |

`crossDefect coef x` is the cross-block pair sum
`Σ_i x_i · (Σ_{j>i, j ∉ block(i)} coef[j−i] · x_j)`, written in the Lean-friendly form
"all later partners minus the partners inside one's own block":
`dot (tl coef) rᵢ − dot (tl coef) (headBlock rᵢ)`.

`straddle_lag_ge_two` is the core of the general identity:

```
dot cs r − dot cs (headBlock r) = dot (tl cs) (tl r) − dot (tl cs) (tl (headBlock r))
```

The `cs[0]` coefficient — i.e. `coef[1]`, the lag-1 coefficient — drops out entirely, so the
cross term is supported on lags `≥ 2`. Lag 0 never appears in it by construction.
`adjacent_same_block` is the same fact in block-membership form.

## Part 2 — norm preservation and Rayleigh transfer

| theorem | statement |
|---|---|
| `blocks_sqnorm_preserved` | `Nonneg x → Σ_B sqnorm B = sqnorm x` |
| `rayleigh_transfer` | `Nonneg x → 0 < c → 0 < iso x → 0 < sqnorm x → ∃ B ∈ blocks x, 0 < sqnorm B ∧ Q B · sqnorm x < Q x · sqnorm B` |

`rayleigh_transfer` is stated by **cross multiplication**, so no division and no rationals:
everything stays in `Int`. The proof is the mediant argument — `Σ_B Q B < Q x` together with
`Σ_B sqnorm B = sqnorm x` forces some block to beat the average — carried out through the
helper `sum_mul_le` and the *decidable* finite search `list_forall_or_exists`.

## Part 3 — an arbitrary pointwise denominator

| theorem | statement |
|---|---|
| `blocks_D_preserved` | `d 0 = 0 → Nonneg x → Σ_B D d B = D d x` |
| `blocks_sqnorm_preserved_from_D` | Part 2's law as the `d = (· * ·)` instance |
| `rayleigh_transfer_general` | `d 0 = 0`, `0 < t → 0 < d t` → the transfer for `D d` |
| `rayleigh_transfer_from_general` | Part 2's transfer as the `d = (· * ·)` instance |
| `rayleigh_transfer_sum` | the `d = id` instance — denominator `Σ_i x_i` |

**`blocks_D_preserved` assumes only `d 0 = 0`.** No positivity, no monotonicity, no shape
condition at all. The proof never looks at `d` beyond that one value: under `Nonneg` every
entry outside every block is exactly `0`, so it contributes `d 0 = 0` to both sides.
Positivity of `d` is needed only in the *transfer*, to know that each block's denominator is
strictly positive.

`rayleigh_transfer_sum` is the shape an application with a mass denominator needs:

```lean
theorem rayleigh_transfer_sum (a b c : Int) {x : List Int}
    (hx : Nonneg x) (hc : 0 < c) (hiso : 0 < iso x) (hM : 0 < x.sum) :
    ∃ B ∈ blocks x, 0 < B.sum ∧ Q a b c B * x.sum < Q a b c x * B.sum
```

Part 2's two theorems keep their own direct proofs; the Part 3 versions are stated alongside
as instances rather than replacing them.

## Build

```
lake build
```

Requires only the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.33.0`).
Nothing is downloaded; there is no dependency to fetch.

The build runs **eight** executable exhaustive sweeps, each over every `x ∈ {0,1,2,3}^n` for
`n = 0 … 7` (21 845 lists per sweep), and prints one line each:

```
[0, 0, 0, 0, 0, 0, 0, 0]              lag-2 GD identity            (a=4369, b=-6314, c=2050)
[0, 0, 0, 0, 0, 0, 0, 0]              general GD identity at lag 4 (coef = [7,-3,5,11,-2])
[0, 0, 0, 0, 0, 0, 0, 0]              squared norm preserved by blocking
[0, 0, 0, 0, 0, 0, 0, 0]              pure lag 0 never straddles
[0, 0, 0, 0, 0, 0, 0, 0]              pure lag 1 never straddles   (straddle_lag_ge_two)
[0, 0, 0, 0, 63, 423, 2295, 10755]    lag 3 DOES straddle
[0, 0, 0, 0, 0, 0, 0, 0]              D-preserved for d t = 7t − 3t²  (d 0 = 0, not positive)
[0, 1, 7, 37, 175, 781, 3367, 14197]  D-preservation FAILS for d t = t + 1  (d 0 = 1 ≠ 0)
```

These are *checks*, not proofs — the theorems already cover every nonnegative list. They are
here for three reasons:

* **line 1** reproduces an independent Python sweep on identical data;
* **line 6** shows the cross term is not identically zero, so `straddle_lag_ge_two` is a real
  restriction and not a vacuous one;
* **lines 7–8** bracket the hypothesis of `blocks_D_preserved` from both sides — dropping
  positivity of `d` changes nothing, dropping `d 0 = 0` breaks it at `n = 1`.

## Trust

`#print axioms` on every theorem in the file reports exactly

```
[propext, Quot.sound]
```

(a few report just `[propext]`). No `Classical.choice`, no `sorryAx`, no `native_decide`.
The file contains no `sorry`, no `admit`, and declares no `axiom`.

The only place excluded middle would normally creep in is the existential in the
`rayleigh_transfer*` family. It is obtained constructively from `list_forall_or_exists`, a
`Decidable`-driven finite search over `blocks x`.

Squares are written `v * v` rather than `v ^ 2` so that `omega` sees them as atoms;
`Q_cons_sq` records that this agrees with the `^ 2` form.

## Numeric anchors (all `example`s in the file, checked by `decide`)

| expression | value |
|---|--:|
| `Q 4369 (-6314) 2050 [1,1,0,1,1]` | 6898 |
| `Q 4369 (-6314) 0 [1,1,0,1,1]` | 4848 |
| `2 * Q 4369 (-6314) 0 [1,1]` | 4848 |
| margin at `[1,0,1]`, `c = 2050` | +2050 |
| margin at `[1,0,1]`, `c = 0` | 0 |
| margin at `[3,0,3,0,3,0,3]`, `c = −100` | −2700 |
| `crossDefect [4369,-6314,2050] [1,1,0,1,1]` | 2050 |
| `Qgen [1,0,0,1] [1,0,0,1]` | 3 |
| `Σ_B Qgen [1,0,0,1] B` for the same `x` | 2 |
| `crossDefect [1,0,0,1] [1,0,0,1]` | 1 |
| `sqnorm [1,1,0,1,1]` and `Σ_B sqnorm B` | 4, 4 |
| `(blocks [1,1,0,1,1]).map (·.sum)` | `[2, 2]` |

("margin" = `Q − Σ_B Q B`, which `gd_identity` says is exactly `c · iso x`. The lag-3 rows
show a cross term that lag ≤ 2 cannot produce.)

## Scope

Deliberately **not** formalised here: the complete classification of the equality locus
(needs reals and measures), the sharp constant `α` (an algebraic number), and the
cyclic / stationary transfer. Those are cited from existing reports in the accompanying
Letter.
