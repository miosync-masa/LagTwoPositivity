# LagTwoPositivity

Notice：I'm Japanese and not a native English speaker, so I'm using an LLM for translation!

A single, self-contained Lean 4 file about **banded quadratic forms over nonnegative integer
signals**, with coefficients that depend on **position as well as lag**: the exact block
decomposition, the fact that only lags `≥ 2` can cross a block boundary, preservation of any
pointwise denominator, a Rayleigh transfer stated entirely in `Int`, and the consequences for
copositive matrices.

**No Mathlib. No Batteries. Lean 4 core only — the file has zero `import` lines.**

| | |
|---|--:|
| source | `LagTwoPositivity.lean`, 1 692 lines |
| theorems | 130 |
| definitions | 37 (+ 1 structure) |
| `example`s checked by `decide` | 52 |
| build-time exhaustive invariants | 18, across 8 traversals |
| clean build (`rm -rf .lake/build && lake build`) | ~4.4 s |
| dependencies to fetch | none |

## The point: blocks must preserve position

Coefficients are an arbitrary function of position **and** lag,

```
c : Nat → Nat → Int          -- c i L is the coefficient of x_i · x_{i+L}
Qf c x = Σ_L Σ_i c i L · x_i · x_{i+L}
```

`Bandwidth c K` says `c i L = 0` for every `L > K`.

`restr x` lists one list per maximal run of strictly positive entries of `x`. Each of them
has **the same length as `x`**: it agrees with `x` on its own run and is `0` everywhere else.

This is not cosmetic. If blocks are taken as *extracted sublists* — re-indexed from `0` — the
decomposition identity is **false** as soon as the coefficients depend on position. Already a
diagonal matrix breaks it. Take `c i 0 = (1, 1, 5)`, every other `c i L = 0`, and `x = [1,0,1]`:

| | |
|---|--:|
| `Qf c x` | 6 |
| `cross c 0 x` | 0 |
| `Σ` over position-preserving blocks: `Qf c [1,0,0] + Qf c [0,0,1]` | 1 + 5 = **6** |
| `Σ` over extracted blocks: `Qf c [1] + Qf c [1]` | 1 + 1 = **2** |

`extraction_breaks_position_dependence` pins this down, and the sweep `identityCounts`
measures how often it happens (13 104 of the 16 384 signals of length 7, for a generic
non-Toeplitz bandwidth-2 matrix).

## Definitions

```
Qf c x     = Σ_L Σ_i c i L · x_i · x_{i+L}        Qfrom c i x  = the same from position i
cdot c i L r = Σ_k c i (L+k) · r[k]               zeros x      = 0-list of x's length
restr x    = the position-preserving maximal positive runs of x
headRestr r = the restriction to the run containing r's head (all-zero if it has none)
cross c i x = Σ_k x_k · Σ_{l > k, l outside k's run} c (i+k) (l−k) · x_l
isoW c i x  = Σ_{isolated zeros k} c (i+k−1) 2 · x_{k−1} · x_{k+1}
Masked w u  = w is u with some entries zeroed (same length, same order)
Nonneg x    = every entry of x is ≥ 0
sqnorm x    = Σ_i x_i²                            D d x        = Σ_i d (x_i)
```

and, kept for the Toeplitz sections of the Letter,

```
Q a b c x = Σ_i a·x_i²  +  Σ_i b·x_i·x_{i+1}  +  Σ_i c·x_i·x_{i+2}
blocks x  = the *extracted* maximal runs of strictly positive entries of x
iso x     = Σ over i with x_i = 0, x_{i-1} > 0, x_{i+1} > 0  of  x_{i-1}·x_{i+1}
toep a b c i L = a, b, c, 0, 0, …   (independent of the position i)
```

Both `blocks` and `restr` are defined by structural recursion, so no well-founded recursion
and no termination obligation. `blocks_pos`, `blocks_mem_ne_nil`, `restr_masked` and
`restr_mem_pos` are the correctness witnesses for the phrase "maximal run of strictly
positive entries".

## Part 0 — the lag-2 Toeplitz form

| theorem | statement |
|---|---|
| `gd_identity` | `Nonneg x → Q x = Σ_{B ∈ blocks x} Q B + c · iso x` (Toeplitz only!) |
| `isolated_zero_strict` | `Nonneg x → 0 < c → 0 < iso x → Σ_B Q B < Q x` |
| `sharpness_at_zero` | `Q a b 0 [1,1,0,1,1] = 2 · Q a b 0 [1,1]` — criticality at `c = 0` |

## Part 1 — position-dependent coefficients

| theorem | statement |
|---|---|
| `gd_identity_posdep` | `Nonneg x → Qf c x = Σ_r Qf c (x^(r)) + cross c x` — **Theorem 2.1** |
| `straddle_lag_ge_two` | the lag-1 coefficient cancels identically out of `cross` — **Theorem 2.2** |
| `cross_eq_zero_of_band_one` | `Bandwidth c 1 → Nonneg x → cross c i x = 0` |
| `cross_eq_isoW` | `Bandwidth c 2 → Nonneg x → cross c i x = isoW c i x` — **Corollary 2.1** |
| `gd_identity_band_two` | the two combined: `Qf c x = Σ_r Qf c (x^(r)) + isoW c 0 x` |
| `adjacent_same_restr` | `0 < x_0`, `0 < x_1` → both sit in one and the same run |

`straddle_lag_ge_two` is the core of the identity:

```
cdot c i 1 r − cdot c i 1 (headRestr r) = cdot c i 2 (tl r) − cdot c i 2 (tl (headRestr r))
```

The lag-1 coefficient drops out entirely, so the cross term is supported on lags `≥ 2`.
Lag 0 never appears in it by construction. `adjacent_same_restr` is the same fact in
run-membership form.

**Corollary 2.1 is where position dependence shows up in the answer, not only in the
hypotheses:** every isolated zero `k` is charged its *own* coefficient `c (k−1) 2`, so the
defect is `Σ_k c (k−1) 2 · x_{k−1} · x_{k+1}`, not a single scalar times `iso x`.

## Part 2 — the Toeplitz specialisation

| theorem | statement |
|---|---|
| `Qf_toep` | `Qf (toep a b c) x = Q a b c x` |
| `isoW_toep` | `isoW (toep a b c) i x = c · iso x` |
| `gd_identity_restr` | Part 0's identity in position-preserving form, from `cross_eq_isoW` |
| `Qblocks_eq_Qrestr` | **extraction and masking agree exactly when `c` is Toeplitz** |

`Qblocks_eq_Qrestr` is the precise sense in which the original development was safe:
subtract `gd_identity` from `gd_identity_restr`, the `c · iso x` terms cancel, and the two
block sums must coincide for every nonnegative `x`. Off Toeplitz they do not.

## Part 3 — masking and support

| theorem | statement |
|---|---|
| `restr_masked` | every `x^(r)` is a masking of `x` |
| `restr_nonneg` | every `x^(r)` is nonnegative when `x` is |
| `restr_mem_pos` | every `x^(r)` carries at least one strictly positive mark |
| `masked_iff` | `Masked` agrees with its Boolean form `maskedB`, used by the sweeps |

## Part 4 — denominators and Rayleigh transfer

| theorem | statement |
|---|---|
| `restr_D_preserved` | `d 0 = 0 → Nonneg x → Σ_r D d (x^(r)) = D d x` — **Lemma 4.1** |
| `blocks_D_preserved` | the same for *extracted* blocks |
| `blocks_restr_D_agree` | consequently the two block sums of a denominator always agree |
| `isolated_zero_strict_posdep` | `Bandwidth c 2`, all `c i 2 > 0`, `0 < iso x` → `Σ_r Qf c (x^(r)) < Qf c x` |
| `rayleigh_transfer_posdep` | the transfer for an arbitrary `D d`, position-dependent `c` |
| `rayleigh_transfer_posdep_sum` | the `d = id` instance — denominator `Σ_i x_i` |
| `rayleigh_transfer_sqnorm` | the `d = (· * ·)` instance |
| `rayleigh_transfer_toeplitz`, `rayleigh_transfer_toeplitz_sum` | the `toep a b c` instances |

**`restr_D_preserved` assumes only `d 0 = 0`.** No positivity, no monotonicity, no shape
condition at all. The proof never looks at `d` beyond that one value: under `Nonneg` every
entry outside a run is exactly `0` in every restriction, so it contributes `d 0 = 0` to both
sides. Positivity of `d` is needed only in the *transfer*, to know that each block's
denominator is strictly positive.

**Denominators are position-blind.** `D d` never sees where an entry sits, so — unlike the
quadratic form — extraction and masking give the same denominator for free. That is exactly
why the position-dependence trap is invisible in Parts 2–3 of the original development and
fatal in Part 1.

`rayleigh_transfer_posdep` is stated by **cross multiplication**, so no division and no
rationals: everything stays in `Int`.

```lean
theorem rayleigh_transfer_posdep (hband : Bandwidth c 2) (hc2 : ∀ i, 0 < c i 2)
    (d : Int → Int) (hd0 : d 0 = 0) (hdpos : ∀ t, 0 < t → 0 < d t)
    {x : List Int} (hx : Nonneg x) (hiso : 0 < iso x) (hDx : 0 < D d x) :
    ∃ B ∈ restr x, 0 < D d B ∧ Qf c B * D d x < Qf c x * D d B
```

The hypothesis "`0 < c`" of the Toeplitz version becomes "`0 < c i 2` at every position".

## Part 5 — copositive matrices

```
Copositive c    :  ∀ x ≥ 0, Qf c x ≥ 0
IsZero c u      :  u ≥ 0, u ≠ 0, Qf c u = 0
MinimalZero c u :  a zero no other zero sits strictly inside
IsInterval x    :  (restr x).length ≤ 1 — the positive positions form one contiguous run
```

Fix a copositive `c` with `Bandwidth c 2` and `0 < c i 2` at every position.

| theorem | statement |
|---|---|
| `copositive_zero_iso` | **(i)** every zero `u` has `iso u = 0`: its support is cut by gaps of width `≥ 2` |
| `copositive_restr_isZero` | every block restriction of a zero is itself a zero |
| `copositive_minimalZero_isInterval` | **(ii)** the support of a minimal zero is an interval |

Both are four-line consequences of Part 1 and Lemma 4.1. If `iso u > 0` then

```
Σ_r Qf c (u^(r)) = Qf c u − isoW c 0 u = − isoW c 0 u < 0,
```

while every `u^(r) ≥ 0`, so copositivity forces every `Qf c (u^(r)) ≥ 0` — contradiction.
Hence `iso u = 0`, the sum is `0`, every term is `0`, and every `u^(r)` is itself a zero. If
there were two or more runs, the first restriction would be a *proper* masking of `u` (its
mass is strictly smaller, by `restr_D_preserved` at `d = id`), contradicting minimality.

Minimality is stated as "`Masked w u` and `IsZero c w` imply `w = u`", which is exactly "no
zero has strictly smaller support": a masking with the same support *is* the original.

## Why nonnegativity is required

The identity is **false** without it. For `x = [1,-1,1]` the positive runs are `[1,0,0]` and
`[0,0,1]`, so position `1` sits outside every run and its contributions `c 1 0 · x_1²` and
`c 1 1 · x_1 · x_2` are simply lost; the identity fails by `c 1 0 − c 1 1`
(`nonneg_is_needed`). Nonnegativity forces every non-run entry to be exactly `0`; that is
what kills the lag-1 cross-boundary term and turns the lag-2 cross-boundary term into `isoW`.

## Build

```
lake build
```

Requires only the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.33.0`).
Nothing is downloaded; there is no dependency to fetch.

The build runs **eight** executable exhaustive traversals, each over every `x ∈ {0,1,2,3}^n`
for `n = 0 … 7` (21 845 signals per traversal), tracking **eighteen** invariants in total,
and prints one line each:

```
[(0,0,0), (0,0,0), (0,3,0), (0,24,0), (0,135,0), (0,660,0), (0,3003,0), (0,13104,0)]
      Thm 2.1 / EXTRACTION form / Cor 2.1, for the non-Toeplitz cVar
[(0,0,0), (0,0,0), (0,0,0), (0,21,0), (0,75,0), (0,264,0), (0,1488,0), (0,6924,0)]
      the same three, for the diagonal counterexample family cEx
[(0,0), (0,0), (0,0), (0,0), (0,63), (0,423), (0,2295), (0,10755)]
      Thm 2.1 at lag 3 / signals with a nonzero cross term there
[(0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0), (0,0)]
      Part 0's gd_identity / Qblocks_eq_Qrestr
[0, 0, 0, 0, 0, 0, 0, 0]
      Thm 2.2: a bandwidth-1 matrix never straddles a block boundary
[(0,0), (0,1), (0,1), (0,10), (0,82), (0,487), (0,2467), (0,11476)]
      Lemma 4.1 for d t = 7t − 3t² / for d t = t + 1  (d 0 = 1 ≠ 0, so it must fail)
[(0,0,0), (0,0,0), (0,0,0), (0,9,0), (0,81,0), (0,486,0), (0,2466,0), (0,11475,0)]
      restrictions are length-preserving maskings / signals with ≥ 2 runs / (ii)'s core
[(0,0), (0,0), (0,0), (9,0), (72,0), (405,0), (2007,0), (9333,0)]
      copositive (i): signals tested / violations
```

These are *checks*, not proofs — the theorems already cover every nonnegative list. They are
here because:

* the **middle column of lines 1–2** is the whole reason for the refactor: the extraction
  form of the identity fails on 13 104 signals of length 7 for a generic non-Toeplitz matrix,
  and on 6 924 even for a diagonal one, while the outer columns stay at `0`;
* **line 4** shows the two forms agree on every signal once the coefficients are Toeplitz;
* **line 3** shows the cross term is not identically zero, so `straddle_lag_ge_two` is a real
  restriction and not a vacuous one;
* **line 6** brackets the hypothesis of `restr_D_preserved` from both sides — dropping
  positivity of `d` changes nothing, dropping `d 0 = 0` breaks it at `n = 1`;
* **lines 7–8** show the copositive corollaries are tested on a non-empty set (9 333 and
  11 475 signals of length 7) and never fail.

## Trust

`#print axioms` on every one of the 211 declarations in the file reports exactly

```
[propext, Quot.sound]
```

(a few report just `[propext]`, or nothing). No `Classical.choice`, no `sorryAx`, no
`native_decide`. The file contains no `sorry`, no `admit`, and declares no `axiom`.

The two places excluded middle would normally creep in:

* the existential in the `rayleigh_transfer*` family — obtained constructively from
  `list_forall_or_exists`, a `Decidable`-driven finite search over `restr x`;
* every proof by contradiction — written as `by_cases` on a decidable proposition, never as
  `by_contra`.

One subtlety worth recording: `omega` preprocesses `∃`-typed hypotheses through
`Classical.choice`. In `D_pos_of_mem_pos` the existential is therefore destructed *before*
any call to `omega`; otherwise eight downstream theorems pick up `Classical.choice`.

Squares are written `v * v` rather than `v ^ 2` so that `omega` sees them as atoms;
`Q_cons_sq` records that this agrees with the `^ 2` form.

## Numeric anchors (a selection of the `example`s checked by `decide`)

| expression | value |
|---|--:|
| `Q 4369 (-6314) 2050 [1,1,0,1,1]` | 6898 |
| `Q 4369 (-6314) 0 [1,1,0,1,1]` = `2 * Q 4369 (-6314) 0 [1,1]` | 4848 |
| margin at `[1,0,1]`, `c = 2050` / `c = 0` | +2050 / 0 |
| margin at `[3,0,3,0,3,0,3]`, `c = −100` | −2700 |
| `restr [1,1,0,1,1]` | `[[1,1,0,0,0],[0,0,0,1,1]]` |
| `Qf cEx [1,0,1]` / `Σ` over `restr` / `Σ` over `blocks` | 6 / 6 / **2** |
| `isoW (toep 4369 (-6314) 2050) 0 [3,0,3,0,3,0,3]` | 2050 · 27 |
| `isoW cVar 0 [1,0,1,0,1]` | 2050 + 2064 |
| `Qf cLag3 [1,0,0,1,0,0,1]` / `Σ` over `restr` / `cross` | 8 / 3 / 5 |
| `sqnorm [1,1,0,1,1]` | 4 |

("margin" = `Q − Σ_B Q B`, which `gd_identity` says is exactly `c · iso x`.)

## Scope

Deliberately **not** formalised here: the complete classification of the equality locus
(needs reals and measures), the sharp constant `α` (an algebraic number), and the
cyclic / stationary transfer. Those are cited from existing reports in the accompanying
Letter.
