/-
# Lag-2 positivity: the block decomposition with position-dependent coefficients

A self-contained formalisation of the exact decomposition of a banded quadratic form over a
nonnegative integer signal into its *positive blocks* plus an *isolated-zero* coupling, and
of the consequences for copositive matrices.

## Coefficients depend on position, not only on lag

    c : Nat → Nat → Int          -- `c i L` is the coefficient of `x_i · x_{i+L}`
    Qf c x = Σ_L Σ_i c i L · x_i · x_{i+L}

No Toeplitz (diagonal-constant) structure is assumed anywhere in Parts 1–5.  `Bandwidth c K`
says that `c i L = 0` for every `L > K`.

## Blocks must preserve position

`restr x` lists one list per maximal run of strictly positive entries of `x`.  Each of them
has **the same length as `x`**: it agrees with `x` on its own run and is `0` everywhere else.

This is not cosmetic.  With blocks taken as *extracted sublists* — re-indexed from `0` — the
decomposition identity is **false** as soon as the coefficients depend on position.  Already
a diagonal matrix breaks it: take `c i 0 = (1, 1, 5)` and all other `c i L = 0`, and
`x = [1,0,1]`.  Then `Qf c x = 6` and the cross term is `0`; the position-preserving blocks
give `Qf c [1,0,0] + Qf c [0,0,1] = 1 + 5 = 6`, but the extracted blocks give
`Qf c [1] + Qf c [1] = 1 + 1 = 2`.  `extraction_breaks_position_dependence` records exactly
this, and the build-time sweep `identityCounts` measures how often it happens.

## What is here

### Part 0 — the lag-2 Toeplitz form (kept for §6–§7 of the Letter)

`Q a b c x = Σ_i a·x_i² + Σ_i b·x_i·x_{i+1} + Σ_i c·x_i·x_{i+2}`, `blocks x` the *extracted*
maximal positive runs, `iso x = Σ_{isolated zeros i} x_{i-1}·x_{i+1}`.

  * `gd_identity`          `Q x = Σ_{B ∈ blocks x} Q B + c · iso x`   (Toeplitz only!)
  * `isolated_zero_strict` `0 < c` and `0 < iso x`  ⟹  `Σ_B Q B < Q x`
  * `sharpness_at_zero`    `Q a b 0 [1,1,0,1,1] = 2 · Q a b 0 [1,1]`  — criticality at `c = 0`

### Part 1 — position-dependent coefficients (Theorems 2.1, 2.2, Corollary 2.1)

  * `gd_identity_posdep`         `Qf c x = Σ_r Qf c (x^(r)) + cross c 0 x`
  * `straddle_lag_ge_two`        the lag-1 coefficient cancels identically out of `cross`
  * `cross_eq_zero_of_band_one`  `Bandwidth c 1` ⟹ `cross ≡ 0`
  * `cross_eq_isoW`              `Bandwidth c 2` ⟹ `cross c i x = isoW c i x`,
                                 `isoW c 0 x = Σ_{isolated zeros k} c (k-1) 2 · x_{k-1}·x_{k+1}`
  * `adjacent_same_restr`        two adjacent positive marks share a run

### Part 2 — the Toeplitz specialisation

`toep a b c i L` is `a, b, c, 0, 0, …` independently of `i`.

  * `Qf_toep`               `Qf (toep a b c) = Q a b c`
  * `gd_identity_restr`     Part 0's identity re-derived from `cross_eq_isoW`
  * `Qblocks_eq_Qrestr`     **extraction and masking agree exactly when `c` is Toeplitz**

and §7's minimality claim, at `(a, b, c) = (4369, -6314, -100)` with
`defect x = Q x − Qblocks x`:

  * `iso_pair_bound`        isolated zeros are never adjacent: `2 · iso x + 9 ≤ 9 · |x|`
  * `iso_le_27`             marks in `{0,…,3}` and `|x| ≤ 7`  ⟹  `iso x ≤ 27`
  * `defect_ge_neg_2700`    hence `defect x ≥ −2700` for **every** such signal
  * `defect_attained`       and `(3,0,3,0,3,0,3)` is such a signal, with `defect = −2700`
  * `defectMin_eq_neg_2700` the same over the sweeps' own search space `allLists 7`

### Part 3 — masking and support

  * `Masked w u`        `w` is `u` with some entries zeroed (same length, same order)
  * `restr_masked`      every `x^(r)` is a masking of `x`
  * `restr_mem_pos`     every `x^(r)` carries a strictly positive mark

### Part 4 — denominators and Rayleigh transfer (Lemma 4.1, Cor. 3.1, Thm 4.1, Cor. 4.1)

`D d x = Σ_i d (x_i)`.

  * `restr_D_preserved`            `d 0 = 0` ⟹ `Σ_r D d (x^(r)) = D d x`.  **No positivity of `d`.**
  * `blocks_D_preserved`           the same for *extracted* blocks — denominators are
                                   position-blind, so only the quadratic form needs masking
  * `isolated_zero_strict_posdep`  `Bandwidth c 2`, all `c i 2 > 0`, `0 < iso x`
                                   ⟹ `Σ_r Qf c (x^(r)) < Qf c x`
  * `rayleigh_transfer_posdep`     some block strictly beats the whole, for an arbitrary
                                   pointwise denominator, stated by cross multiplication so
                                   everything stays in `Int`
  * `rayleigh_transfer_posdep_sum`, `rayleigh_transfer_sqnorm`, `rayleigh_transfer_toeplitz`

### Part 5 — copositive matrices

`Copositive c` is `∀ x ≥ 0, Qf c x ≥ 0`; a *zero* is a nonnegative `u ≠ 0` with `Qf c u = 0`;
a *minimal* zero is one no other zero sits strictly inside.

  * `copositive_zero_iso`               (i)  every zero has `iso u = 0`: its support is cut
                                             by gaps of width `≥ 2`
  * `copositive_restr_isZero`                every block restriction of a zero is a zero
  * `copositive_minimalZero_isInterval` (ii) the support of a minimal zero is an interval

Both are four-line consequences of `cross_eq_isoW` and `restr_D_preserved`: if `iso u > 0`
then `Σ_r Qf c (u^(r)) = Qf c u − isoW c 0 u < 0`, while every `u^(r) ≥ 0` forces every
`Qf c (u^(r)) ≥ 0`.

## The nonnegativity hypothesis

The identity is **false** without `Nonneg x`.  For `x = [1,-1,1]` the positive runs are
`[1,0,0]` and `[0,0,1]`, so position `1` sits outside every run and its contributions
`c 1 0 · x_1²` and `c 1 1 · x_1 · x_2` are simply lost: the identity fails by exactly
`c 1 0 − c 1 1`.  With the diagonal `cEx` of the counterexample family that is
`7 ≠ 6 + 0` (`nonneg_is_needed`).  Nonnegativity is what forces every non-block entry to be
exactly `0`, which kills the lag-1 cross-boundary term and turns the lag-2 cross-boundary
term into `isoW`.

## Dependencies

**Lean 4 core only.**  No Mathlib, no Batteries, no `native_decide`.
`#print axioms` on every theorem reports exactly `[propext, Quot.sound]` — in particular
no `Classical.choice` and no `sorryAx`.  The one finite search (`list_forall_or_exists`,
used by the Rayleigh transfers) is decidable, so it needs no excluded middle; likewise
every proof by contradiction goes through `by_cases` on a decidable proposition.

Two `omega` traps to keep the audit clean: `omega` preprocesses `∃`-typed **hypotheses**
through `Classical.choice` (so `D_pos_of_mem_pos` destructs its existential first), and it
also uses choice to split a **conjunctive goal** (so `allLists_spec` splits by hand).

Squares are written `v * v` rather than `v ^ 2` so that `omega` sees them as atoms;
`Q_cons_sq` records that this agrees with the `^ 2` form.

## Deliberately out of scope

The complete classification of the equality locus (needs reals and measures), the sharp
constant `α` (an algebraic number), and the cyclic / stationary transfer are **not**
formalised here.  Those are cited from the existing reports in the accompanying Letter.
-/

namespace LagTwoPositivity


/-! ## Part 0.  The lag-2 Toeplitz form

`Q a b c` and the *extracted* blocks of the original development.  Everything here is the
`c i L = (a, b, c, 0, …)` instance of Part 1 (see Part 2), and it is kept because §6–§7 of
the Letter are statements about the single scalar `c`. -/
def hd : List Int → Int
  | []     => 0
  | v :: _ => v

def tl {α : Type _} : List α → List α
  | []     => []
  | _ :: r => r

def Q (a b c : Int) : List Int → Int
  | []     => 0
  | v :: r => a * (v * v) + b * (v * hd r) + c * (v * hd (tl r)) + Q a b c r

def blocks : List Int → List (List Int)
  | []     => []
  | v :: r =>
      if 0 < v then
        (if 0 < hd r then (v :: (blocks r).headD []) :: (blocks r).tail
         else [v] :: blocks r)
      else blocks r

def iso : List Int → Int
  | []     => 0
  | v :: r => (if hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r) then v * hd (tl r) else 0) + iso r

def Nonneg : List Int → Prop
  | []     => True
  | v :: r => 0 ≤ v ∧ Nonneg r

def Qblocks (a b c : Int) (x : List Int) : Int := ((blocks x).map (Q a b c)).sum

section Basic
variable {a b c v : Int} {r x : List Int}

@[simp] theorem hd_nil : hd [] = 0 := rfl
@[simp] theorem hd_cons : hd (v :: r) = v := rfl
@[simp] theorem tl_nil {α : Type _} : tl ([] : List α) = [] := rfl
@[simp] theorem tl_cons {α : Type _} {u : α} {s : List α} : tl (u :: s) = s := rfl

@[simp] theorem Q_nil : Q a b c [] = 0 := rfl
theorem Q_cons : Q a b c (v :: r)
    = a * (v * v) + b * (v * hd r) + c * (v * hd (tl r)) + Q a b c r := rfl

/-- The defining recursion written with `^ 2`, matching the informal statement
`Q x = Σ a·x_i² + Σ b·x_i·x_{i+1} + Σ c·x_i·x_{i+2}`. -/
theorem Q_cons_sq : Q a b c (v :: r)
    = a * v ^ 2 + b * (v * hd r) + c * (v * hd (tl r)) + Q a b c r := by
  rw [Q_cons]
  simp [Int.pow_succ, Int.pow_zero, Int.one_mul]

@[simp] theorem iso_nil : iso [] = 0 := rfl
theorem iso_cons : iso (v :: r)
    = (if hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r) then v * hd (tl r) else 0) + iso r := rfl

@[simp] theorem blocks_nil : blocks [] = [] := rfl
@[simp] theorem Qblocks_nil : Qblocks a b c [] = 0 := rfl

theorem nonneg_hd (h : Nonneg x) : 0 ≤ hd x := by
  cases x with
  | nil => simp
  | cons u s => exact h.1

theorem nonneg_tail (h : Nonneg (v :: r)) : Nonneg r := h.2

theorem nonneg_tl (h : Nonneg x) : Nonneg (tl x) := by
  cases x with
  | nil => trivial
  | cons u s => exact h.2

theorem nonneg_iff_forall_mem : ∀ x : List Int, Nonneg x ↔ ∀ v ∈ x, 0 ≤ v
  | [] => by simp [Nonneg]
  | v :: r => by
      simp only [Nonneg, List.mem_cons, forall_eq_or_imp]
      rw [nonneg_iff_forall_mem r]

end Basic

section Blocks
variable {v : Int} {r : List Int}

theorem blocks_cons_nonpos (h : ¬ 0 < v) : blocks (v :: r) = blocks r := by
  simp [blocks, h]

theorem blocks_cons_pos_pos (h : 0 < v) (h2 : 0 < hd r) :
    blocks (v :: r) = (v :: (blocks r).headD []) :: (blocks r).tail := by
  simp [blocks, h, h2]

theorem blocks_cons_pos_nonpos (h : 0 < v) (h2 : ¬ 0 < hd r) :
    blocks (v :: r) = [v] :: blocks r := by
  simp [blocks, h, h2]

theorem blocks_ne_nil (h : 0 < hd x) : blocks x ≠ [] := by
  cases x with
  | nil => simp at h
  | cons u s =>
      simp only [hd_cons] at h
      by_cases hs : 0 < hd s
      · rw [blocks_cons_pos_pos h hs]; simp
      · rw [blocks_cons_pos_nonpos h hs]; simp

theorem hd_firstBlock (h : 0 < hd x) : hd ((blocks x).headD []) = hd x := by
  cases x with
  | nil => simp at h
  | cons u s =>
      simp only [hd_cons] at h
      by_cases hs : 0 < hd s
      · rw [blocks_cons_pos_pos h hs]; simp
      · rw [blocks_cons_pos_nonpos h hs]; simp

theorem hd_tl_firstBlock (hx : Nonneg x) (h : 0 < hd x) :
    hd (tl ((blocks x).headD [])) = hd (tl x) := by
  cases x with
  | nil => simp at h
  | cons u s =>
      simp only [hd_cons] at h
      by_cases hs : 0 < hd s
      · rw [blocks_cons_pos_pos h hs]
        simpa using hd_firstBlock hs
      · rw [blocks_cons_pos_nonpos h hs]
        have hge : 0 ≤ hd s := nonneg_hd (nonneg_tail hx)
        have h0 : hd s = 0 := by omega
        simp [h0]

/-- Every entry of every block is strictly positive.  Together with the defining
equations this is the correctness witness for "block = maximal run of strictly
positive entries". -/
theorem blocks_pos : ∀ {x : List Int}, ∀ B ∈ blocks x, ∀ u ∈ B, 0 < u := by
  intro x
  induction x with
  | nil => intro B hB; simp at hB
  | cons v r ih =>
    intro B hB u hu
    by_cases hv : 0 < v
    · by_cases hw : 0 < hd r
      · rw [blocks_cons_pos_pos hv hw] at hB
        cases hb : blocks r with
        | nil => exact absurd hb (blocks_ne_nil hw)
        | cons H T =>
          rw [hb] at hB
          simp only [List.headD_cons, List.tail_cons, List.mem_cons] at hB
          rcases hB with rfl | hB
          · rcases List.mem_cons.1 hu with rfl | hu
            · exact hv
            · exact ih H (by rw [hb]; exact List.mem_cons_self ..) u hu
          · exact ih B (by rw [hb]; exact List.mem_cons_of_mem _ hB) u hu
      · rw [blocks_cons_pos_nonpos hv hw] at hB
        rcases List.mem_cons.1 hB with rfl | hB
        · rcases List.mem_cons.1 hu with rfl | hu
          · exact hv
          · simp at hu
        · exact ih B hB u hu
    · rw [blocks_cons_nonpos hv] at hB
      exact ih B hB u hu

end Blocks

section QblocksRec
variable {a b c v : Int} {r : List Int}

theorem Qblocks_cons_nonpos (h : ¬ 0 < v) :
    Qblocks a b c (v :: r) = Qblocks a b c r := by
  simp [Qblocks, blocks_cons_nonpos h]

theorem Qblocks_cons_pos_nonpos (h : 0 < v) (h2 : ¬ 0 < hd r) :
    Qblocks a b c (v :: r) = a * (v * v) + Qblocks a b c r := by
  simp [Qblocks, blocks_cons_pos_nonpos h h2, Q_cons]

theorem Qblocks_cons_pos_pos (hr : Nonneg r) (h : 0 < v) (h2 : 0 < hd r) :
    Qblocks a b c (v :: r)
      = a * (v * v) + b * (v * hd r) + c * (v * hd (tl r)) + Qblocks a b c r := by
  have hH := hd_firstBlock (x := r) h2
  have hT := hd_tl_firstBlock (x := r) hr h2
  rw [Qblocks, blocks_cons_pos_pos h h2]
  cases hb : blocks r with
  | nil => exact absurd hb (blocks_ne_nil h2)
  | cons H T =>
      rw [hb] at hH hT
      simp only [List.headD_cons, List.tail_cons, List.map_cons, List.sum_cons] at *
      rw [Q_cons, hH, hT, Qblocks, hb]
      simp only [List.map_cons, List.sum_cons]
      omega

end QblocksRec

/-! ### Part 0, main results -/

section Main
variable (a b c : Int)

/-- **GD identity.**  On a nonnegative signal the lag-2 form splits exactly into the
sum of its block forms plus `c` times the isolated-zero coupling. -/
theorem gd_identity :
    ∀ x : List Int, Nonneg x → Q a b c x = Qblocks a b c x + c * iso x := by
  intro x
  induction x with
  | nil => intro _; simp
  | cons v r ih =>
    intro hx
    have hr : Nonneg r := nonneg_tail hx
    have IH := ih hr
    rw [Q_cons, iso_cons]
    by_cases hv : 0 < v
    · by_cases hw : 0 < hd r
      · have hne : ¬ (hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)) := by
          rintro ⟨h0, -, -⟩; omega
        rw [Qblocks_cons_pos_pos hr hv hw, if_neg hne, Int.zero_add]
        omega
      · have hge : 0 ≤ hd r := nonneg_hd hr
        have h0 : hd r = 0 := by omega
        rw [Qblocks_cons_pos_nonpos hv hw]
        by_cases hz : 0 < hd (tl r)
        · rw [if_pos ⟨h0, hv, hz⟩, h0, Int.mul_add]
          omega
        · have hge2 : 0 ≤ hd (tl r) := nonneg_hd (nonneg_tl hr)
          have h0' : hd (tl r) = 0 := by omega
          have hne : ¬ (hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)) := by
            rintro ⟨-, -, h⟩; omega
          rw [if_neg hne, h0, h0', Int.zero_add]
          omega
    · have hv0 : v = 0 := by have := hx.1; omega
      have hne : ¬ (hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)) := by
        rintro ⟨-, h, -⟩; omega
      rw [Qblocks_cons_nonpos hv, if_neg hne, Int.zero_add, hv0]
      omega

/-- A single isolated zero flanked by two positive marks makes the block sum
*strictly* smaller than the whole, as soon as `c > 0`. -/
theorem isolated_zero_strict {x : List Int}
    (hx : Nonneg x) (hc : 0 < c) (hiso : 0 < iso x) :
    Qblocks a b c x < Q a b c x := by
  have h := gd_identity a b c x hx
  have hpos : 0 < c * iso x := Int.mul_pos hc hiso
  omega

/-- **Sharpness at `c = 0`.**  The gap closes exactly at `c = 0`: the isolated-zero
configuration `[1,1,0,1,1]` costs precisely two copies of the block `[1,1]`. -/
theorem sharpness_at_zero : Q a b 0 [1,1,0,1,1] = 2 * Q a b 0 [1,1] := by
  simp only [Q_cons, Q_nil, hd_cons, hd_nil, tl_cons, tl_nil]
  omega

/-- The same statement with nonnegativity written as `∀ v ∈ x, 0 ≤ v`, and with
`Qblocks` unfolded to `(blocks x).map (Q a b c) |>.sum`. -/
theorem gd_identity' (x : List Int) (hx : ∀ v ∈ x, 0 ≤ v) :
    Q a b c x = (((blocks x).map (Q a b c)).sum) + c * iso x :=
  gd_identity a b c x ((nonneg_iff_forall_mem x).2 hx)

theorem isolated_zero_strict' (x : List Int) (hx : ∀ v ∈ x, 0 ≤ v)
    (hc : 0 < c) (hiso : 0 < iso x) :
    (((blocks x).map (Q a b c)).sum) < Q a b c x :=
  isolated_zero_strict a b c ((nonneg_iff_forall_mem x).2 hx) hc hiso

theorem Qblocks_eq (x : List Int) :
    Qblocks a b c x = ((blocks x).map (Q a b c)).sum := rfl

end Main


/-! ## Part 1.  Position-dependent coefficients

`c i L` is the coefficient of `x_i · x_{i+L}` — an arbitrary function of position *and* lag.
Blocks become `restr`, the *position-preserving* restrictions: same length as the signal,
equal to it on one maximal positive run, `0` elsewhere. -/
/-! ## Part 1.  Position-dependent coefficients and position-preserving blocks -/

section PosDep

/-- `cdot c i L r = Σ_k c i (L+k) * r[k]`: the coefficient *row* at absolute position `i`,
read from lag `L` onwards, paired against `r`. -/
def cdot (c : Nat → Nat → Int) (i : Nat) : Nat → List Int → Int
  | _, []      => 0
  | L, v :: vs => c i L * v + cdot c i (L + 1) vs

/-- The all-zero list of the same length. -/
def zeros : List Int → List Int
  | []     => []
  | _ :: r => 0 :: zeros r

/-- `Qfrom c i x` is the quadratic form on the window whose first entry sits at absolute
position `i`:  `Σ_L Σ_k c (i+k) L * x_k * x_{k+L}`. -/
def Qfrom (c : Nat → Nat → Int) : Nat → List Int → Int
  | _, []     => 0
  | i, v :: r => c i 0 * (v * v) + v * cdot c i 1 r + Qfrom c (i + 1) r

/-- `Qf c x = Σ_L Σ_i c i L * x_i * x_{i+L}`. -/
def Qf (c : Nat → Nat → Int) (x : List Int) : Int := Qfrom c 0 x

/-- **Position-preserving block restriction.**  `restr x` lists, in order, one list per
maximal run of strictly positive entries of `x`.  Each of them has *the same length as `x`*:
it agrees with `x` on its own run and is `0` everywhere else.  This is what makes the
decomposition identity survive position-dependent coefficients. -/
def restr : List Int → List (List Int)
  | []     => []
  | v :: r =>
      if 0 < v then
        (if 0 < hd r then
            (v :: (restr r).headD (zeros r)) :: (restr r).tail.map (fun B => (0 : Int) :: B)
         else
            (v :: zeros r) :: (restr r).map (fun B => (0 : Int) :: B))
      else (restr r).map (fun B => (0 : Int) :: B)

/-- The restriction to the run containing the head, or the all-zero list when the head is
not positive. -/
def headRestr (r : List Int) : List Int :=
  if 0 < hd r then (restr r).headD (zeros r) else zeros r

/-- `cross c i x = Σ_k x_k * (Σ_{l > k, l outside k's run} c (i+k) (l-k) * x_l)`, written as
"all later partners minus the partners inside one's own run". -/
def cross (c : Nat → Nat → Int) : Nat → List Int → Int
  | _, []     => 0
  | i, v :: r => (if 0 < v then v * (cdot c i 1 r - cdot c i 1 (headRestr r)) else 0)
                 + cross c (i + 1) r

/-- `isoW c i x = Σ_{isolated zeros k of x} c (i+k-1) 2 * x_{k-1} * x_{k+1}`. -/
def isoW (c : Nat → Nat → Int) : Nat → List Int → Int
  | _, []     => 0
  | i, v :: r => (if hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r) then c i 2 * (v * hd (tl r)) else 0)
                 + isoW c (i + 1) r

/-- `Bandwidth c K`: no lag beyond `K` occurs, i.e. the matrix is `K`-banded. -/
def Bandwidth (c : Nat → Nat → Int) (K : Nat) : Prop := ∀ i L, K < L → c i L = 0

variable {c : Nat → Nat → Int} {i L : Nat} {v : Int} {r x : List Int}

/-! ### `cdot`, `zeros`, `Qfrom` -/

@[simp] theorem cdot_nil : cdot c i L [] = 0 := rfl

theorem cdot_cons {vs : List Int} :
    cdot c i L (v :: vs) = c i L * v + cdot c i (L + 1) vs := rfl

/-- `cdot` peels one index, with no side condition. -/
theorem cdot_eq (c : Nat → Nat → Int) (i L : Nat) (r : List Int) :
    cdot c i L r = c i L * hd r + cdot c i (L + 1) (tl r) := by
  cases r with
  | nil => simp
  | cons u s => rfl

@[simp] theorem zeros_nil : zeros [] = [] := rfl
@[simp] theorem zeros_cons : zeros (v :: r) = 0 :: zeros r := rfl

@[simp] theorem hd_zeros : hd (zeros r) = 0 := by cases r <;> rfl
@[simp] theorem tl_zeros : tl (zeros r) = zeros (tl r) := by cases r <;> rfl

theorem zeros_nonneg : ∀ r : List Int, Nonneg (zeros r)
  | []     => trivial
  | _ :: s => ⟨by omega, zeros_nonneg s⟩

@[simp] theorem cdot_zeros : ∀ (r : List Int) (L : Nat), cdot c i L (zeros r) = 0
  | [],     _ => rfl
  | _ :: s, L => by rw [zeros_cons, cdot_cons, cdot_zeros s (L + 1)]; simp

@[simp] theorem Qfrom_nil : Qfrom c i [] = 0 := rfl

theorem Qfrom_cons :
    Qfrom c i (v :: r) = c i 0 * (v * v) + v * cdot c i 1 r + Qfrom c (i + 1) r := rfl

@[simp] theorem Qfrom_cons_zero {B : List Int} : Qfrom c i (0 :: B) = Qfrom c (i + 1) B := by
  rw [Qfrom_cons]; simp

@[simp] theorem Qfrom_zeros : ∀ (r : List Int) (i : Nat), Qfrom c i (zeros r) = 0
  | [],     _ => rfl
  | _ :: s, i => by rw [zeros_cons, Qfrom_cons_zero, Qfrom_zeros s (i + 1)]

@[simp] theorem Qf_nil : Qf c [] = 0 := rfl

/-- Beyond the bandwidth the coefficient row contributes nothing. -/
theorem cdot_of_gt {K : Nat} (h : Bandwidth c K) (i : Nat) :
    ∀ (s : List Int) (L : Nat), K < L → cdot c i L s = 0
  | [],     _, _  => rfl
  | _ :: t, L, hL => by
      rw [cdot_cons, h i L hL, cdot_of_gt h i t (L + 1) (by omega)]; simp

/-- Under `Bandwidth c 2` the coefficient row has exactly two off-diagonal entries. -/
theorem cdot_band_two (h : Bandwidth c 2) (i : Nat) (r : List Int) :
    cdot c i 1 r = c i 1 * hd r + c i 2 * hd (tl r) := by
  rw [cdot_eq c i 1 r, cdot_eq c i 2 (tl r), cdot_of_gt h i (tl (tl r)) 3 (by omega)]
  omega

/-- Under `Bandwidth c 1` the coefficient row has exactly one off-diagonal entry. -/
theorem cdot_band_one (h : Bandwidth c 1) (i : Nat) (r : List Int) :
    cdot c i 1 r = c i 1 * hd r := by
  rw [cdot_eq c i 1 r, cdot_of_gt h i (tl r) 2 (by omega)]
  omega

/-! ### `restr` -/

@[simp] theorem restr_nil : restr [] = [] := rfl

@[simp] theorem cross_nil : cross c i [] = 0 := rfl

theorem cross_cons :
    cross c i (v :: r)
      = (if 0 < v then v * (cdot c i 1 r - cdot c i 1 (headRestr r)) else 0)
        + cross c (i + 1) r := rfl

@[simp] theorem isoW_nil : isoW c i [] = 0 := rfl

theorem isoW_cons :
    isoW c i (v :: r)
      = (if hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r) then c i 2 * (v * hd (tl r)) else 0)
        + isoW c (i + 1) r := rfl

theorem mul_left_comm' (u w z : Int) : u * (w * z) = w * (u * z) := by
  rw [← Int.mul_assoc, Int.mul_comm u w, Int.mul_assoc]

theorem restr_cons_nonpos (h : ¬ 0 < v) :
    restr (v :: r) = (restr r).map (fun B => (0 : Int) :: B) := by simp [restr, h]

theorem restr_cons_pos_pos (h : 0 < v) (h2 : 0 < hd r) :
    restr (v :: r)
      = (v :: (restr r).headD (zeros r)) :: (restr r).tail.map (fun B => (0 : Int) :: B) := by
  simp [restr, h, h2]

theorem restr_cons_pos_nonpos (h : 0 < v) (h2 : ¬ 0 < hd r) :
    restr (v :: r) = (v :: zeros r) :: (restr r).map (fun B => (0 : Int) :: B) := by
  simp [restr, h, h2]

theorem restr_ne_nil (h : 0 < hd x) : restr x ≠ [] := by
  cases x with
  | nil => simp at h
  | cons u s =>
      simp only [hd_cons] at h
      by_cases hs : 0 < hd s
      · rw [restr_cons_pos_pos h hs]; simp
      · rw [restr_cons_pos_nonpos h hs]; simp

theorem hd_firstRestr (h : 0 < hd x) : hd ((restr x).headD (zeros x)) = hd x := by
  cases x with
  | nil => simp at h
  | cons u s =>
      simp only [hd_cons] at h
      by_cases hs : 0 < hd s
      · rw [restr_cons_pos_pos h hs]; simp
      · rw [restr_cons_pos_nonpos h hs]; simp

theorem headRestr_of_pos (h : 0 < hd r) : headRestr r = (restr r).headD (zeros r) := by
  simp [headRestr, h]

theorem headRestr_of_nonpos (h : ¬ 0 < hd r) : headRestr r = zeros r := by
  simp [headRestr, h]

/-- The restriction to the head's run starts at the head itself — including the degenerate
case `x_i = 0`, where both sides are `0`. -/
theorem hd_headRestr (hr : Nonneg r) : hd (headRestr r) = hd r := by
  by_cases h : 0 < hd r
  · rw [headRestr_of_pos h]; exact hd_firstRestr h
  · have hge : 0 ≤ hd r := nonneg_hd hr
    have h0 : hd r = 0 := by omega
    rw [headRestr_of_nonpos h, h0]; simp

theorem hd_tl_headRestr (hr : Nonneg r) (h : 0 < hd r) :
    hd (tl (headRestr r)) = hd (tl r) := by
  rw [headRestr_of_pos h]
  cases r with
  | nil => simp at h
  | cons u s =>
      simp only [hd_cons] at h
      by_cases hs : 0 < hd s
      · rw [restr_cons_pos_pos h hs]
        simpa using hd_firstRestr hs
      · rw [restr_cons_pos_nonpos h hs]
        have hge : 0 ≤ hd s := nonneg_hd (nonneg_tail hr)
        have h0 : hd s = 0 := by omega
        simp [h0]

/-- **Adjacent positive marks share a run.**  Positions `0` and `1` of the restriction to
the head's run carry `x_0` and `x_1` themselves. -/
theorem adjacent_same_restr (hv : 0 < v) (hw : 0 < hd r) :
    (restr (v :: r)).headD (zeros (v :: r)) = v :: headRestr r ∧ hd (headRestr r) = hd r := by
  refine ⟨?_, by rw [headRestr_of_pos hw]; exact hd_firstRestr hw⟩
  rw [restr_cons_pos_pos hv hw, headRestr_of_pos hw]
  simp

end PosDep

section PosDepMain

variable {c : Nat → Nat → Int} {i : Nat} {v : Int} {r x : List Int}

theorem sum_map_cons_zero (c : Nat → Nat → Int) (i : Nat) :
    ∀ L : List (List Int),
      ((L.map (fun B => (0 : Int) :: B)).map (Qfrom c i)).sum
        = (L.map (Qfrom c (i + 1))).sum
  | []      => rfl
  | B :: T  => by
      simp only [List.map_cons, List.sum_cons, Qfrom_cons_zero]
      rw [sum_map_cons_zero c i T]

/-- **Theorem 2.1 (block decomposition, position-dependent).**  On a nonnegative signal the
form splits exactly into the sum of its *position-preserving* block restrictions plus the
cross-block coupling.  The coefficients `c i L` are arbitrary functions of *both* the
position `i` and the lag `L`; no Toeplitz structure is assumed. -/
theorem gd_identity_posdep (c : Nat → Nat → Int) :
    ∀ x : List Int, Nonneg x → ∀ i : Nat,
      Qfrom c i x = ((restr x).map (Qfrom c i)).sum + cross c i x := by
  intro x
  induction x with
  | nil => intro _ _; simp [cross]
  | cons v r ih =>
    intro hx i
    have hr : Nonneg r := nonneg_tail hx
    have IH := ih hr (i + 1)
    rw [Qfrom_cons, cross_cons]
    by_cases hv : 0 < v
    · by_cases hw : 0 < hd r
      · rw [restr_cons_pos_pos hv hw, if_pos hv, headRestr_of_pos hw]
        cases hb : restr r with
        | nil => exact absurd hb (restr_ne_nil hw)
        | cons H T =>
          rw [hb] at IH
          simp only [List.headD_cons, List.tail_cons, List.map_cons, List.sum_cons] at IH ⊢
          rw [Qfrom_cons, sum_map_cons_zero c i T, Int.mul_sub]
          omega
      · rw [restr_cons_pos_nonpos hv hw, if_pos hv, headRestr_of_nonpos hw]
        simp only [List.map_cons, List.sum_cons]
        rw [Qfrom_cons, sum_map_cons_zero c i (restr r), cdot_zeros, Qfrom_zeros,
          Int.sub_zero]
        omega
    · have hv0 : v = 0 := by have := hx.1; omega
      rw [restr_cons_nonpos hv, if_neg hv, hv0, sum_map_cons_zero c i (restr r)]
      simp only [Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]
      omega

/-- The `i = 0` form: `Q(x) - Σ_r Q(x^(r)) = cross(x)`. -/
theorem gd_identity_posdep' (c : Nat → Nat → Int) (x : List Int) (hx : Nonneg x) :
    Qf c x = ((restr x).map (Qf c)).sum + cross c 0 x :=
  gd_identity_posdep c x hx 0

/-- **Theorem 2.2 (straddling pairs have lag ≥ 2).**  The lag-1 coefficient cancels
identically out of `cross`; hence a bandwidth-1 matrix has no cross-block coupling at all. -/
theorem straddle_lag_ge_two (c : Nat → Nat → Int) (i : Nat) (hr : Nonneg r) :
    cdot c i 1 r - cdot c i 1 (headRestr r)
      = cdot c i 2 (tl r) - cdot c i 2 (tl (headRestr r)) := by
  rw [cdot_eq c i 1 r, cdot_eq c i 1 (headRestr r), hd_headRestr hr,
    show (1 : Nat) + 1 = 2 from rfl]
  omega

/-- **Theorem 2.2, corollary.**  `K ≤ 1` ⟹ `cross ≡ 0`. -/
theorem cross_eq_zero_of_band_one (h : Bandwidth c 1) :
    ∀ x : List Int, Nonneg x → ∀ i : Nat, cross c i x = 0 := by
  intro x
  induction x with
  | nil => intro _ _; rfl
  | cons v r ih =>
    intro hx i
    have hr : Nonneg r := nonneg_tail hx
    rw [cross_cons, ih hr (i + 1),
        cdot_band_one h i r, cdot_band_one h i (headRestr r), hd_headRestr hr]
    simp

/-- **Corollary 2.1.**  For a bandwidth-2 matrix the cross term is exactly the
isolated-zero coupling, weighted at each isolated zero `k` by its own coefficient
`c (k-1) 2`. -/
theorem cross_eq_isoW (h : Bandwidth c 2) :
    ∀ x : List Int, Nonneg x → ∀ i : Nat, cross c i x = isoW c i x := by
  intro x
  induction x with
  | nil => intro _ _; rfl
  | cons v r ih =>
    intro hx i
    have hr : Nonneg r := nonneg_tail hx
    rw [cross_cons,
        isoW_cons,
        ih hr (i + 1)]
    by_cases hv : 0 < v
    · by_cases hw : 0 < hd r
      · have hH : hd (headRestr r) = hd r := hd_headRestr hr
        have hT : hd (tl (headRestr r)) = hd (tl r) := hd_tl_headRestr hr hw
        have hne : ¬ (hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)) := by rintro ⟨h0, -, -⟩; omega
        rw [if_pos hv, if_neg hne, cdot_band_two h i r, cdot_band_two h i (headRestr r),
          hH, hT]
        simp
      · have hge : 0 ≤ hd r := nonneg_hd hr
        have h0 : hd r = 0 := by omega
        rw [if_pos hv, headRestr_of_nonpos hw, cdot_band_two h i r,
          cdot_band_two h i (zeros r), hd_zeros, tl_zeros, hd_zeros, h0]
        simp only [Int.mul_zero, Int.zero_add, Int.add_zero, Int.sub_zero, true_and]
        by_cases hz : 0 < hd (tl r)
        · rw [if_pos ⟨hv, hz⟩, mul_left_comm' v (c i 2) (hd (tl r))]
        · have hge2 : 0 ≤ hd (tl r) := nonneg_hd (nonneg_tl hr)
          have h0' : hd (tl r) = 0 := by omega
          have hne : ¬ (0 < v ∧ 0 < hd (tl r)) := by rintro ⟨-, hcon⟩; omega
          rw [if_neg hne, h0']
          simp
    · rw [if_neg hv]
      have hne : ¬ (hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)) := by rintro ⟨-, hcon, -⟩; omega
      rw [if_neg hne]

/-- **Corollary 2.1, in the shape used later.** -/
theorem gd_identity_band_two (h : Bandwidth c 2) (x : List Int) (hx : Nonneg x) :
    Qf c x = ((restr x).map (Qf c)).sum + isoW c 0 x := by
  rw [gd_identity_posdep' c x hx, cross_eq_isoW h x hx 0]

end PosDepMain

section IsoWeight

variable {c : Nat → Nat → Int}

theorem iso_nonneg : ∀ x : List Int, Nonneg x → 0 ≤ iso x := by
  intro x
  induction x with
  | nil => intro _; simp
  | cons v r ih =>
    intro hx
    have := ih (nonneg_tail hx)
    rw [iso_cons]
    by_cases h : hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)
    · rw [if_pos h]
      have : 0 < v * hd (tl r) := Int.mul_pos h.2.1 h.2.2
      omega
    · rw [if_neg h]; omega

theorem isoW_nonneg (hc2 : ∀ i, 0 < c i 2) :
    ∀ x : List Int, Nonneg x → ∀ i : Nat, 0 ≤ isoW c i x := by
  intro x
  induction x with
  | nil => intro _ _; exact Int.le_refl 0
  | cons v r ih =>
    intro hx i
    have IH := ih (nonneg_tail hx) (i + 1)
    rw [isoW_cons]
    by_cases h : hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)
    · rw [if_pos h]
      have : 0 < c i 2 * (v * hd (tl r)) := Int.mul_pos (hc2 i) (Int.mul_pos h.2.1 h.2.2)
      omega
    · rw [if_neg h]; omega

theorem isoW_pos (hc2 : ∀ i, 0 < c i 2) :
    ∀ x : List Int, Nonneg x → ∀ i : Nat, 0 < iso x → 0 < isoW c i x := by
  intro x
  induction x with
  | nil => intro _ _ h; simp at h
  | cons v r ih =>
    intro hx i hpos
    have hr : Nonneg r := nonneg_tail hx
    have IHnn : 0 ≤ isoW c (i + 1) r := isoW_nonneg hc2 r hr (i + 1)
    rw [isoW_cons]
    by_cases h : hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)
    · rw [if_pos h]
      have : 0 < c i 2 * (v * hd (tl r)) := Int.mul_pos (hc2 i) (Int.mul_pos h.2.1 h.2.2)
      omega
    · rw [if_neg h, Int.zero_add]
      rw [iso_cons, if_neg h, Int.zero_add] at hpos
      exact ih hr (i + 1) hpos

theorem isoW_eq_zero_of_iso_eq_zero :
    ∀ x : List Int, Nonneg x → ∀ i : Nat, iso x = 0 → isoW c i x = 0 := by
  intro x
  induction x with
  | nil => intro _ _ _; rfl
  | cons v r ih =>
    intro hx i h0
    have hr : Nonneg r := nonneg_tail hx
    have hnn : 0 ≤ iso r := iso_nonneg r hr
    rw [iso_cons] at h0
    have hcond : ¬ (hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)) := by
      intro h
      rw [if_pos h] at h0
      have : 0 < v * hd (tl r) := Int.mul_pos h.2.1 h.2.2
      omega
    rw [if_neg hcond, Int.zero_add] at h0
    rw [isoW_cons, if_neg hcond, Int.zero_add, ih hr (i + 1) h0]

end IsoWeight

/-! ## Part 2.  The Toeplitz specialisation

Part 0's lag-2 form is the `c i L = (a, b, c, 0, 0, …)` instance of `Qf`, uniformly in the
position `i`.  Everything in Part 0 is therefore a corollary of Part 1 — and, because the
coefficients no longer see the position, extraction and masking give the *same* value. -/

section Toeplitz

/-- The Toeplitz (diagonal-constant) coefficient function of Part 0. -/
def toep (a b c : Int) : Nat → Nat → Int :=
  fun _ L => if L = 0 then a else if L = 1 then b else if L = 2 then c else 0

variable (a b c : Int)

@[simp] theorem toep_zero (i : Nat) : toep a b c i 0 = a := by simp [toep]
@[simp] theorem toep_one (i : Nat) : toep a b c i 1 = b := by simp [toep]
@[simp] theorem toep_two (i : Nat) : toep a b c i 2 = c := by simp [toep]

theorem toep_band : Bandwidth (toep a b c) 2 := by
  intro i L h
  simp only [toep]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- `Qf (toep a b c)` is Part 0's `Q a b c`, from every starting position. -/
theorem Qfrom_toep : ∀ (x : List Int) (i : Nat), Qfrom (toep a b c) i x = Q a b c x := by
  intro x
  induction x with
  | nil => intro _; rfl
  | cons v r ih =>
    intro i
    rw [Qfrom_cons, ih (i + 1), cdot_band_two (toep_band a b c) i r, Q_cons,
      toep_zero, toep_one, toep_two, Int.mul_add,
      mul_left_comm' v b (hd r), mul_left_comm' v c (hd (tl r))]
    omega

theorem Qf_toep (x : List Int) : Qf (toep a b c) x = Q a b c x := Qfrom_toep a b c x 0

/-- With Toeplitz coefficients the position-weighted isolated-zero sum collapses to `c · iso`. -/
theorem isoW_toep : ∀ (x : List Int) (i : Nat), isoW (toep a b c) i x = c * iso x := by
  intro x
  induction x with
  | nil => intro _; simp
  | cons v r ih =>
    intro i
    rw [isoW_cons,
      ih (i + 1), iso_cons, Int.mul_add, toep_two]
    by_cases h : hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; simp

/-- Part 0's identity in position-preserving form, obtained from `cross_eq_isoW`. -/
theorem gd_identity_restr (x : List Int) (hx : Nonneg x) :
    Q a b c x = ((restr x).map (Q a b c)).sum + c * iso x := by
  have hfun : Qf (toep a b c) = Q a b c := funext (Qf_toep a b c)
  have h := gd_identity_band_two (toep_band a b c) x hx
  rw [isoW_toep a b c x 0, hfun] at h
  exact h

/-- **Extraction and masking agree exactly when the coefficients are Toeplitz.**  This is
the precise sense in which Part 0 is safe and the general case is not: subtracting the two
identities, the `c · iso` terms cancel and the two block sums must coincide.  For a
position-dependent `c` they do not — see `extraction_breaks_position_dependence`. -/
theorem Qblocks_eq_Qrestr (x : List Int) (hx : Nonneg x) :
    Qblocks a b c x = ((restr x).map (Q a b c)).sum := by
  have h1 := gd_identity a b c x hx
  have h2 := gd_identity_restr a b c x hx
  omega

end Toeplitz

/-! ### §7.  The defect minimum at `(a, b, c) = (4369, -6314, -100)`

`gd_identity` turns the defect `Q − Qblocks` into `c · iso`, so with `c < 0` minimising the
defect is the same as *maximising* the isolated-zero coupling.  With marks in `{0,…,3}` each
isolated zero contributes at most `3 · 3 = 9`, and two isolated zeros can never be adjacent
(an isolated zero needs a strictly positive right neighbour), so a signal of length `L`
carries at most `⌊(L−1)/2⌋` of them.  At `L = 7` that is `3`, hence `iso ≤ 27` and
`defect ≥ −2700`.  The bound is proved for **every** such signal, not only for the `21 845`
that the sweeps below enumerate. -/

section DefectMin

/-- Two marks in `{0,…,3}` pair up to at most `9`. -/
theorem mul_le_nine {p q : Int} (hp : p ≤ 3) (hq0 : 0 ≤ q) (hq : q ≤ 3) : p * q ≤ 9 := by
  have := Int.mul_le_mul hp hq hq0 (by omega)
  omega

/-- **Isolated zeros are never adjacent.**  For a nonempty signal with marks in `{0,…,3}`,
`2 · iso x + 9 ≤ 9 · |x|`.  The bound is carried together with the same bound for `tl x`,
because the case where the coupling fires consumes *two* positions — the mark and the zero
just after it — and so needs the induction hypothesis one step further down. -/
theorem iso_pair_bound :
    ∀ x : List Int, Nonneg x → (∀ v ∈ x, v ≤ 3) →
      (x ≠ [] → 2 * iso x + 9 ≤ 9 * (x.length : Int)) ∧
      (tl x ≠ [] → 2 * iso (tl x) + 9 ≤ 9 * ((tl x).length : Int)) := by
  intro x
  induction x with
  | nil => intro _ _; exact ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩
  | cons v r ih =>
    intro hx hb
    have hr : Nonneg r := nonneg_tail hx
    have hbr : ∀ w ∈ r, w ≤ 3 := fun w hw => hb w (List.mem_cons_of_mem _ hw)
    obtain ⟨IH1, IH2⟩ := ih hr hbr
    refine ⟨fun _ => ?_, fun h => IH1 (by simpa using h)⟩
    rw [iso_cons]
    by_cases hc : hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)
    · rw [if_pos hc]
      have h0 := hc.1
      have hsp := hc.2.2
      cases r with
      | nil => simp at hsp
      | cons u s =>
        cases s with
        | nil => simp at hsp
        | cons w s' =>
          simp only [hd_cons, tl_cons] at h0 hsp ⊢
          have hIH := IH2 (by simp)
          simp only [tl_cons] at hIH
          -- the zero at position 1 cannot itself carry a coupling
          have hisor : iso (u :: w :: s') = iso (w :: s') := by
            rw [iso_cons, if_neg (by rintro ⟨-, hcon, -⟩; omega), Int.zero_add]
          have hvw : v * w ≤ 9 :=
            mul_le_nine (hb v (List.mem_cons_self ..)) (by omega)
              (hb w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
          simp only [List.length_cons] at hIH ⊢
          omega
    · rw [if_neg hc]
      by_cases hrnil : r = []
      · subst hrnil; simp
      · have hI := IH1 hrnil
        have hnn := iso_nonneg r hr
        simp only [List.length_cons]
        omega

/-- With marks in `{0,…,3}` and length at most seven, `iso x ≤ 27`, attained by
`(3,0,3,0,3,0,3)`. -/
theorem iso_le_27 (x : List Int) (hx : Nonneg x) (hb : ∀ v ∈ x, v ≤ 3)
    (hlen : x.length ≤ 7) : iso x ≤ 27 := by
  cases x with
  | nil => simp
  | cons v r =>
    have h := (iso_pair_bound (v :: r) hx hb).1 (by simp)
    have hl : (v :: r).length ≤ 7 := hlen
    omega

/-- The §7 defect: the amount by which the block sum falls short of the whole form at
`(a, b, c) = (4369, -6314, -100)`. -/
def defect (x : List Int) : Int :=
  Q 4369 (-6314) (-100) x - Qblocks 4369 (-6314) (-100) x

theorem defect_eq_iso (x : List Int) (hx : Nonneg x) : defect x = -100 * iso x := by
  have := gd_identity 4369 (-6314) (-100) x hx
  simp only [defect]
  omega

/-- **§7, lower bound.**  Every nonnegative signal with marks in `{0,…,3}` and length at most
seven has defect at least `−2700`. -/
theorem defect_ge_neg_2700 (x : List Int) (hx : Nonneg x) (hb : ∀ v ∈ x, v ≤ 3)
    (hlen : x.length ≤ 7) : -2700 ≤ defect x := by
  have hid := defect_eq_iso x hx
  have h27 := iso_le_27 x hx hb hlen
  have hnn := iso_nonneg x hx
  omega

/-- **§7, the bound is attained.**  `(3,0,3,0,3,0,3)` is a legitimate configuration — it is
nonnegative, has marks in `{0,…,3}`, has length seven and does carry an isolated zero — and
its defect is exactly `−2700`.  Together with `defect_ge_neg_2700` this is the §7 claim:
the minimum over all such configurations is `−2700`. -/
theorem defect_attained :
    Nonneg [3,0,3,0,3,0,3]
      ∧ (∀ v ∈ ([3,0,3,0,3,0,3] : List Int), v ≤ 3)
      ∧ ([3,0,3,0,3,0,3] : List Int).length ≤ 7
      ∧ 0 < iso [3,0,3,0,3,0,3]
      ∧ defect [3,0,3,0,3,0,3] = -2700 :=
  ⟨(nonneg_iff_forall_mem _).2 (by decide), by decide, by decide, by decide, by decide⟩

end DefectMin

/-! ## Part 3.  Masking and support -/

section Masking

/-- `Masked w u`: `w` is `u` with some entries replaced by `0` (same length, same order).
This is "`supp w ⊆ supp u` and `w` agrees with `u` on `supp w`". -/
def Masked : List Int → List Int → Prop
  | [],      []      => True
  | [],      _ :: _  => False
  | _ :: _,  []      => False
  | w :: ws, v :: vs => (w = v ∨ w = 0) ∧ Masked ws vs

@[simp] theorem Masked_nil_nil : Masked [] [] := trivial

theorem Masked_cons {w v : Int} {ws vs : List Int} :
    Masked (w :: ws) (v :: vs) ↔ ((w = v ∨ w = 0) ∧ Masked ws vs) := Iff.rfl

theorem Masked_zeros : ∀ r : List Int, Masked (zeros r) r
  | []     => trivial
  | _ :: s => ⟨Or.inr rfl, Masked_zeros s⟩

theorem Masked_refl : ∀ r : List Int, Masked r r
  | []     => trivial
  | _ :: s => ⟨Or.inl rfl, Masked_refl s⟩

theorem Masked_nonneg : ∀ {w u : List Int}, Masked w u → Nonneg u → Nonneg w
  | [],      [],      _, _  => trivial
  | _ :: _,  [],      h, _  => absurd h (by simp [Masked])
  | [],      _ :: _,  h, _  => absurd h (by simp [Masked])
  | w :: ws, v :: vs, h, hu =>
      ⟨by have := hu.1; rcases h.1 with hh | hh <;> omega,
       Masked_nonneg h.2 hu.2⟩

/-- Every block restriction is a masking of the original signal. -/
theorem restr_masked : ∀ {x : List Int}, ∀ B ∈ restr x, Masked B x := by
  intro x
  induction x with
  | nil => intro B hB; simp at hB
  | cons v r ih =>
    intro B hB
    have hmap : ∀ (L : List (List Int)), (∀ C ∈ L, Masked C r) →
        ∀ C ∈ L.map (fun B => (0 : Int) :: B), Masked C (v :: r) := by
      intro L hL C hC
      rcases List.mem_map.1 hC with ⟨C', hC', rfl⟩
      exact ⟨Or.inr rfl, hL C' hC'⟩
    by_cases hv : 0 < v
    · by_cases hw : 0 < hd r
      · rw [restr_cons_pos_pos hv hw] at hB
        cases hb : restr r with
        | nil => exact absurd hb (restr_ne_nil hw)
        | cons H T =>
          rw [hb] at hB
          simp only [List.headD_cons, List.tail_cons, List.mem_cons] at hB
          rcases hB with rfl | hB
          · exact ⟨Or.inl rfl, ih H (by rw [hb]; exact List.mem_cons_self ..)⟩
          · exact hmap T (fun C hC => ih C (by rw [hb]; exact List.mem_cons_of_mem _ hC)) B hB
      · rw [restr_cons_pos_nonpos hv hw] at hB
        rcases List.mem_cons.1 hB with rfl | hB
        · exact ⟨Or.inl rfl, Masked_zeros r⟩
        · exact hmap (restr r) (fun C hC => ih C hC) B hB
    · rw [restr_cons_nonpos hv] at hB
      exact hmap (restr r) (fun C hC => ih C hC) B hB

theorem restr_nonneg {x : List Int} (hx : Nonneg x) : ∀ B ∈ restr x, Nonneg B :=
  fun B hB => Masked_nonneg (restr_masked B hB) hx

/-- Every block restriction carries at least one strictly positive mark. -/
theorem restr_mem_pos : ∀ {x : List Int}, ∀ B ∈ restr x, ∃ u ∈ B, 0 < u := by
  intro x
  induction x with
  | nil => intro B hB; simp at hB
  | cons v r ih =>
    intro B hB
    have hmap : ∀ (L : List (List Int)), (∀ C ∈ L, ∃ u ∈ C, 0 < u) →
        ∀ C ∈ L.map (fun B => (0 : Int) :: B), ∃ u ∈ C, 0 < u := by
      intro L hL C hC
      rcases List.mem_map.1 hC with ⟨C', hC', rfl⟩
      rcases hL C' hC' with ⟨u, hu, hup⟩
      exact ⟨u, List.mem_cons_of_mem _ hu, hup⟩
    by_cases hv : 0 < v
    · by_cases hw : 0 < hd r
      · rw [restr_cons_pos_pos hv hw] at hB
        cases hb : restr r with
        | nil => exact absurd hb (restr_ne_nil hw)
        | cons H T =>
          rw [hb] at hB
          simp only [List.headD_cons, List.tail_cons, List.mem_cons] at hB
          rcases hB with rfl | hB
          · exact ⟨v, List.mem_cons_self .., hv⟩
          · exact hmap T (fun C hC => ih C (by rw [hb]; exact List.mem_cons_of_mem _ hC)) B hB
      · rw [restr_cons_pos_nonpos hv hw] at hB
        rcases List.mem_cons.1 hB with rfl | hB
        · exact ⟨v, List.mem_cons_self .., hv⟩
        · exact hmap (restr r) (fun C hC => ih C hC) B hB
    · rw [restr_cons_nonpos hv] at hB
      exact hmap (restr r) (fun C hC => ih C hC) B hB



/-- Boolean form of `Masked`, for the executable checks. -/
def maskedB : List Int → List Int → Bool
  | [],      []      => true
  | [],      _ :: _  => false
  | _ :: _,  []      => false
  | w :: ws, v :: vs => ((w == v) || (w == 0)) && maskedB ws vs

theorem masked_iff : ∀ w u : List Int, Masked w u ↔ maskedB w u = true
  | [],      []      => Iff.intro (fun _ => rfl) (fun _ => trivial)
  | [],      _ :: _  => Iff.intro (fun h => False.elim h) (fun h => Bool.noConfusion h)
  | _ :: _,  []      => Iff.intro (fun h => False.elim h) (fun h => Bool.noConfusion h)
  | w :: ws, v :: vs => by
      rw [Masked_cons, masked_iff ws vs]
      simp [maskedB]

end Masking

/-! ## Part 4.  Denominators and Rayleigh transfer

`D d x = Σ_i d (x_i)`.  The preservation law never touches the shape of `d`: entries outside
every block are exactly `0` under `Nonneg`, so they contribute `d 0 = 0` to both sides.
Positivity of `d` enters only in the transfer, to know each block has a strictly positive
denominator. -/

section Denom
/-- `sqnorm x = Σ_i x_i²`. -/
def sqnorm : List Int → Int
  | []     => 0
  | v :: r => v * v + sqnorm r

@[simp] theorem sqnorm_nil : sqnorm [] = 0 := rfl

theorem sqnorm_cons {v : Int} {r : List Int} : sqnorm (v :: r) = v * v + sqnorm r := rfl

/-- `D d x = Σ_i d (x_i)`. -/
def D (d : Int → Int) (x : List Int) : Int := (x.map d).sum

@[simp] theorem D_nil {d : Int → Int} : D d [] = 0 := rfl

theorem D_cons {d : Int → Int} {v : Int} {r : List Int} : D d (v :: r) = d v + D d r := by
  simp [D]

theorem sqnorm_eq_D : ∀ x : List Int, sqnorm x = D (fun t => t * t) x := by
  intro x
  induction x with
  | nil => rfl
  | cons v r ih => rw [sqnorm_cons, D_cons, ih]

theorem D_id_eq_sum : ∀ x : List Int, D id x = x.sum := by
  intro x
  induction x with
  | nil => rfl
  | cons v r ih => rw [D_cons, ih]; simp


/-- No block is empty. -/
theorem blocks_mem_ne_nil : ∀ {x : List Int}, ∀ B ∈ blocks x, B ≠ [] := by
  intro x
  induction x with
  | nil => intro B hB; simp at hB
  | cons v r ih =>
    intro B hB
    by_cases hv : 0 < v
    · by_cases hw : 0 < hd r
      · rw [blocks_cons_pos_pos hv hw] at hB
        cases hb : blocks r with
        | nil => exact absurd hb (blocks_ne_nil hw)
        | cons H T =>
          rw [hb] at hB
          simp only [List.headD_cons, List.tail_cons, List.mem_cons] at hB
          rcases hB with rfl | hB
          · simp
          · exact ih B (by rw [hb]; exact List.mem_cons_of_mem _ hB)
      · rw [blocks_cons_pos_nonpos hv hw] at hB
        rcases List.mem_cons.1 hB with rfl | hB
        · simp
        · exact ih B hB
    · rw [blocks_cons_nonpos hv] at hB
      exact ih B hB

/-- **Generalised denominator preservation.**  Only `d 0 = 0` is assumed. -/
theorem blocks_D_preserved (d : Int → Int) (hd0 : d 0 = 0) :
    ∀ x : List Int, Nonneg x → ((blocks x).map (D d)).sum = D d x := by
  intro x
  induction x with
  | nil => intro _; simp
  | cons v r ih =>
    intro hx
    have hr : Nonneg r := nonneg_tail hx
    have IH := ih hr
    by_cases hv : 0 < v
    · by_cases hw : 0 < hd r
      · rw [blocks_cons_pos_pos hv hw]
        cases hb : blocks r with
        | nil => exact absurd hb (blocks_ne_nil hw)
        | cons H T =>
          rw [hb] at IH
          simp only [List.headD_cons, List.tail_cons, List.map_cons, List.sum_cons] at IH ⊢
          rw [D_cons, D_cons]
          omega
      · rw [blocks_cons_pos_nonpos hv hw]
        simp only [List.map_cons, List.sum_cons, D_cons, D_nil, Int.add_zero]
        omega
    · have hv0 : v = 0 := by have := hx.1; omega
      rw [blocks_cons_nonpos hv, D_cons, hv0, hd0]
      omega

/-- **Blocking preserves the squared norm** — the `d = (· * ·)` instance of
`blocks_D_preserved`. -/
theorem blocks_sqnorm_preserved (x : List Int) (hx : Nonneg x) :
    ((blocks x).map sqnorm).sum = sqnorm x := by
  have hfun : sqnorm = D (fun t => t * t) := funext sqnorm_eq_D
  rw [hfun]
  exact blocks_D_preserved (fun t => t * t) (by simp) x hx

/-- Cross-multiplied mediant step: if every member satisfies `T * g u ≤ f u * S`, so does
the pair of sums.  Contrapositive of "some member beats the average". -/
theorem sum_mul_le {α : Type _} (f g : α → Int) (S T : Int) :
    ∀ l : List α, (∀ u ∈ l, T * g u ≤ f u * S) →
      T * ((l.map g).sum) ≤ ((l.map f).sum) * S := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons u t ih =>
    intro h
    have hu := h u (List.mem_cons_self ..)
    have ht := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    simp only [List.map_cons, List.sum_cons, Int.mul_add, Int.add_mul]
    omega

/-- Decidable finite search: no `Classical.choice` needed. -/
theorem list_forall_or_exists {α : Type _} (P : α → Prop) [DecidablePred P] :
    ∀ l : List α, (∀ u ∈ l, ¬ P u) ∨ (∃ u ∈ l, P u) := by
  intro l
  induction l with
  | nil => exact Or.inl (by simp)
  | cons u t ih =>
    by_cases h : P u
    · exact Or.inr ⟨u, List.mem_cons_self .., h⟩
    · rcases ih with ht | ⟨w, hw, hPw⟩
      · refine Or.inl ?_
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact h
        · exact ht z hz
      · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hPw⟩

theorem mul_lt_mul_right' {p q S : Int} (h : p < q) (hS : 0 < S) : p * S < q * S := by
  have hpos : 0 < (q - p) * S := Int.mul_pos (by omega) hS
  rw [Int.sub_mul] at hpos
  omega
end Denom

section RestrDenom

/-- Sum of a mapped list is `≥ 0` as soon as every term is. -/
theorem sum_map_nonneg {α : Type _} (f : α → Int) :
    ∀ l : List α, (∀ u ∈ l, 0 ≤ f u) → 0 ≤ (l.map f).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons u t ih =>
    intro h
    have := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have := h u (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A sum of nonnegative terms vanishes only if every term does. -/
theorem sum_map_eq_zero {α : Type _} (f : α → Int) :
    ∀ l : List α, (∀ u ∈ l, 0 ≤ f u) → (l.map f).sum = 0 → ∀ u ∈ l, f u = 0 := by
  intro l
  induction l with
  | nil => intro _ _ u hu; simp at hu
  | cons u t ih =>
    intro h hsum w hw
    have hnn := sum_map_nonneg f t (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have hu := h u (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons] at hsum
    have hu0 : f u = 0 := by omega
    have ht0 : (t.map f).sum = 0 := by omega
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hu0
    · exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz)) ht0 w hw

variable {d : Int → Int}

@[simp] theorem D_zeros (hd0 : d 0 = 0) : ∀ r : List Int, D d (zeros r) = 0
  | []     => rfl
  | _ :: s => by rw [zeros_cons, D_cons, hd0, D_zeros hd0 s]; simp

theorem sum_map_D_cons_zero (hd0 : d 0 = 0) :
    ∀ L : List (List Int),
      ((L.map (fun B => (0 : Int) :: B)).map (D d)).sum = (L.map (D d)).sum
  | []     => rfl
  | B :: T => by
      simp only [List.map_cons, List.sum_cons, D_cons, hd0, Int.zero_add]
      rw [sum_map_D_cons_zero hd0 T]

/-- **Lemma 4.1 (denominator preservation).**  Only `d 0 = 0` is assumed — no positivity.
The position-preserving restrictions pad with zeros, and `d 0 = 0` makes the padding free. -/
theorem restr_D_preserved (d : Int → Int) (hd0 : d 0 = 0) :
    ∀ x : List Int, Nonneg x → ((restr x).map (D d)).sum = D d x := by
  intro x
  induction x with
  | nil => intro _; simp
  | cons v r ih =>
    intro hx
    have hr : Nonneg r := nonneg_tail hx
    have IH := ih hr
    by_cases hv : 0 < v
    · by_cases hw : 0 < hd r
      · rw [restr_cons_pos_pos hv hw]
        cases hb : restr r with
        | nil => exact absurd hb (restr_ne_nil hw)
        | cons H T =>
          rw [hb] at IH
          simp only [List.headD_cons, List.tail_cons, List.map_cons, List.sum_cons] at IH ⊢
          rw [D_cons, D_cons, sum_map_D_cons_zero hd0 T]
          omega
      · rw [restr_cons_pos_nonpos hv hw]
        simp only [List.map_cons, List.sum_cons]
        rw [D_cons, D_cons, D_zeros hd0, sum_map_D_cons_zero hd0 (restr r)]
        omega
    · have hv0 : v = 0 := by have := hx.1; omega
      rw [restr_cons_nonpos hv, D_cons, hv0, hd0,
        sum_map_D_cons_zero hd0 (restr r), Int.zero_add]
      exact IH

theorem D_nonneg_of_nonneg (hd0 : d 0 = 0) (hdpos : ∀ t, 0 < t → 0 < d t) :
    ∀ {B : List Int}, Nonneg B → 0 ≤ D d B := by
  intro B
  induction B with
  | nil => intro _; simp
  | cons u t ih =>
    intro h
    have htail := ih h.2
    rw [D_cons]
    by_cases hu : 0 < u
    · have := hdpos u hu; omega
    · have : u = 0 := by have := h.1; omega
      rw [this, hd0]; omega

theorem D_pos_of_mem_pos (hd0 : d 0 = 0) (hdpos : ∀ t, 0 < t → 0 < d t) :
    ∀ {B : List Int}, Nonneg B → (∃ u ∈ B, 0 < u) → 0 < D d B := by
  intro B
  induction B with
  | nil => intro _ h; rcases h with ⟨u, hu, -⟩; cases hu
  | cons u t ih =>
    intro h hex
    -- destruct the existential *before* any call to `omega`: `omega` preprocesses
    -- `∃`-hypotheses through `Classical.choice`, which would spoil the axiom audit
    rcases hex with ⟨w, hw, hwp⟩
    have htail := D_nonneg_of_nonneg hd0 hdpos h.2
    rw [D_cons]
    by_cases hu : 0 < u
    · have := hdpos u hu; omega
    · have hu0 : u = 0 := by have := h.1; omega
      have hwt : w ∈ t := by
        rcases List.mem_cons.1 hw with he | hw'
        · exfalso; rw [he, hu0] at hwp; omega
        · exact hw'
      have := ih h.2 ⟨w, hwt, hwp⟩
      rw [hu0, hd0]; omega

theorem restr_D_pos (hd0 : d 0 = 0) (hdpos : ∀ t, 0 < t → 0 < d t)
    {x : List Int} (hx : Nonneg x) : ∀ B ∈ restr x, 0 < D d B :=
  fun B hB => D_pos_of_mem_pos hd0 hdpos (restr_nonneg hx B hB) (restr_mem_pos B hB)

end RestrDenom

section PosDepTransfer

variable {c : Nat → Nat → Int}

/-- **Corollary 3.1 (strict deficit), position-dependent.**  If some isolated zero is
flanked by two positive marks and *every* relevant lag-2 coefficient is positive, the block
sum is strictly below the whole. -/
theorem isolated_zero_strict_posdep (hband : Bandwidth c 2) (hc2 : ∀ i, 0 < c i 2)
    {x : List Int} (hx : Nonneg x) (hiso : 0 < iso x) :
    ((restr x).map (Qf c)).sum < Qf c x := by
  have hid := gd_identity_band_two hband x hx
  have hW : 0 < isoW c 0 x := isoW_pos hc2 x hx 0 hiso
  omega

/-- **Theorem 4.1 (Rayleigh transfer), position-dependent and with an arbitrary pointwise
denominator.**  The witness is produced by a decidable finite search over the blocks, so no
choice principle is used. -/
theorem rayleigh_transfer_posdep (hband : Bandwidth c 2) (hc2 : ∀ i, 0 < c i 2)
    (d : Int → Int) (hd0 : d 0 = 0) (hdpos : ∀ t, 0 < t → 0 < d t)
    {x : List Int} (hx : Nonneg x) (hiso : 0 < iso x) (hDx : 0 < D d x) :
    ∃ B ∈ restr x, 0 < D d B ∧ Qf c B * D d x < Qf c x * D d B := by
  rcases list_forall_or_exists
      (fun B => 0 < D d B ∧ Qf c B * D d x < Qf c x * D d B) (restr x) with hall | hex
  · exfalso
    have hle : ∀ B ∈ restr x, Qf c x * D d B ≤ Qf c B * D d x := by
      intro B hB
      have hpos : 0 < D d B := restr_D_pos hd0 hdpos hx B hB
      have hnn : ¬ (Qf c B * D d x < Qf c x * D d B) := fun hlt => hall B hB ⟨hpos, hlt⟩
      omega
    have hsum := sum_mul_le (Qf c) (D d) (D d x) (Qf c x) (restr x) hle
    rw [restr_D_preserved d hd0 x hx] at hsum
    have hlt := isolated_zero_strict_posdep hband hc2 hx hiso
    have hmul := mul_lt_mul_right' hlt hDx
    omega
  · exact hex

/-- **Corollary 4.1.**  The plain mass denominator `Σ_i x_i` is the `d = id` instance. -/
theorem rayleigh_transfer_posdep_sum (hband : Bandwidth c 2) (hc2 : ∀ i, 0 < c i 2)
    {x : List Int} (hx : Nonneg x) (hiso : 0 < iso x) (hM : 0 < D id x) :
    ∃ B ∈ restr x, 0 < D id B ∧ Qf c B * D id x < Qf c x * D id B :=
  rayleigh_transfer_posdep hband hc2 id rfl (fun _ ht => ht) hx hiso hM

end PosDepTransfer


section RestrRayleighToeplitz

/-- The squared norm is the `d = (· * ·)` instance of `restr_D_preserved`. -/
theorem restr_sqnorm_preserved (x : List Int) (hx : Nonneg x) :
    ((restr x).map sqnorm).sum = sqnorm x := by
  have hfun : sqnorm = D (fun t => t * t) := funext sqnorm_eq_D
  rw [hfun]
  exact restr_D_preserved (fun t => t * t) (by simp) x hx

/-- **Denominators are position-blind.**  `D d` never looks at where an entry sits, so for
denominators — unlike for the quadratic form — extraction and masking always agree. -/
theorem blocks_restr_D_agree (d : Int → Int) (hd0 : d 0 = 0) (x : List Int) (hx : Nonneg x) :
    ((blocks x).map (D d)).sum = ((restr x).map (D d)).sum := by
  rw [blocks_D_preserved d hd0 x hx, restr_D_preserved d hd0 x hx]

/-- **Rayleigh transfer, squared-norm denominator.** -/
theorem rayleigh_transfer_sqnorm {c : Nat → Nat → Int}
    (hband : Bandwidth c 2) (hc2 : ∀ i, 0 < c i 2) {x : List Int}
    (hx : Nonneg x) (hiso : 0 < iso x) (hS : 0 < sqnorm x) :
    ∃ B ∈ restr x, 0 < sqnorm B ∧ Qf c B * sqnorm x < Qf c x * sqnorm B := by
  have hfun : sqnorm = D (fun t => t * t) := funext sqnorm_eq_D
  rw [hfun] at hS ⊢
  exact rayleigh_transfer_posdep hband hc2 (fun t => t * t) (by simp)
    (fun t ht => Int.mul_pos ht ht) hx hiso hS

/-- **Rayleigh transfer, Toeplitz lag-2 form.**  Part 0's transfer, now over the
position-preserving blocks and derived from the general statement. -/
theorem rayleigh_transfer_toeplitz (a b c : Int) (hc : 0 < c) {x : List Int}
    (hx : Nonneg x) (hiso : 0 < iso x) (hS : 0 < sqnorm x) :
    ∃ B ∈ restr x, 0 < sqnorm B ∧ Q a b c B * sqnorm x < Q a b c x * sqnorm B := by
  have hfun : Qf (toep a b c) = Q a b c := funext (Qf_toep a b c)
  have hc2 : ∀ i, 0 < toep a b c i 2 := fun i => by rw [toep_two]; exact hc
  have h := rayleigh_transfer_sqnorm (toep_band a b c) hc2 hx hiso hS
  rw [hfun] at h
  exact h

/-- **Rayleigh transfer for the plain mass denominator `Σ_i x_i`.**  This is the shape the
application needs: the denominator is the total mass, not the squared norm. -/
theorem rayleigh_transfer_toeplitz_sum (a b c : Int) (hc : 0 < c) {x : List Int}
    (hx : Nonneg x) (hiso : 0 < iso x) (hM : 0 < x.sum) :
    ∃ B ∈ restr x, 0 < B.sum ∧ Q a b c B * x.sum < Q a b c x * B.sum := by
  have hfun : Qf (toep a b c) = Q a b c := funext (Qf_toep a b c)
  have hdi : ∀ y : List Int, D id y = y.sum := D_id_eq_sum
  have hc2 : ∀ i, 0 < toep a b c i 2 := fun i => by rw [toep_two]; exact hc
  have hM' : 0 < D id x := by rw [hdi]; exact hM
  rcases rayleigh_transfer_posdep (toep_band a b c) hc2 id rfl (fun _ ht => ht) hx hiso hM'
    with ⟨B, hB, hpos, hlt⟩
  rw [hfun] at hlt
  simp only [hdi] at hpos hlt
  exact ⟨B, hB, hpos, hlt⟩

end RestrRayleighToeplitz

/-! ## Part 5.  Copositive matrices -/

section Copositive

variable {c : Nat → Nat → Int}

/-- `A` is **copositive**: `Q(x) ≥ 0` for every nonnegative `x`. -/
def Copositive (c : Nat → Nat → Int) : Prop := ∀ x : List Int, Nonneg x → 0 ≤ Qf c x

/-- `u` is a **zero** of `A`: nonnegative, not identically zero, and `Q(u) = 0`. -/
structure IsZero (c : Nat → Nat → Int) (u : List Int) : Prop where
  nonneg     : Nonneg u
  nontrivial : ∃ v ∈ u, 0 < v
  vanishes   : Qf c u = 0

/-- `u` is a **minimal zero**: no zero of `A` has strictly smaller support.  A `w` with
`Masked w u` is exactly a `w` with `supp w ⊆ supp u` agreeing with `u` there, and such a `w`
has `supp w = supp u` precisely when `w = u`. -/
def MinimalZero (c : Nat → Nat → Int) (u : List Int) : Prop :=
  IsZero c u ∧ ∀ w : List Int, Masked w u → IsZero c w → w = u

/-- The support of `x` is an **interval**: `x` has at most one maximal run of strictly
positive entries. -/
def IsInterval (x : List Int) : Prop := (restr x).length ≤ 1

/-- **Copositive corollary (i).**  For a copositive bandwidth-2 matrix with every `c i 2 > 0`,
no zero has an isolated zero entry: the support is separated by gaps of width `≥ 2`. -/
theorem copositive_zero_iso (hband : Bandwidth c 2) (hc2 : ∀ i, 0 < c i 2)
    (hcop : Copositive c) {u : List Int} (hu : IsZero c u) : iso u = 0 := by
  have hnn : 0 ≤ iso u := iso_nonneg u hu.nonneg
  by_cases hpos : 0 < iso u
  · exfalso
    have hW : 0 < isoW c 0 u := isoW_pos hc2 u hu.nonneg 0 hpos
    have hid := gd_identity_band_two hband u hu.nonneg
    rw [hu.vanishes] at hid
    have hblocks : 0 ≤ ((restr u).map (Qf c)).sum :=
      sum_map_nonneg (Qf c) (restr u) (fun B hB => hcop B (restr_nonneg hu.nonneg B hB))
    omega
  · omega

/-- Under the hypotheses of (i), every block restriction of a zero is itself a zero. -/
theorem copositive_restr_isZero (hband : Bandwidth c 2) (hc2 : ∀ i, 0 < c i 2)
    (hcop : Copositive c) {u : List Int} (hu : IsZero c u) :
    ∀ B ∈ restr u, IsZero c B := by
  have hiso : iso u = 0 := copositive_zero_iso hband hc2 hcop hu
  have hW : isoW c 0 u = 0 := isoW_eq_zero_of_iso_eq_zero u hu.nonneg 0 hiso
  have hid := gd_identity_band_two hband u hu.nonneg
  rw [hu.vanishes, hW, Int.add_zero] at hid
  have hnn : ∀ B ∈ restr u, 0 ≤ Qf c B :=
    fun B hB => hcop B (restr_nonneg hu.nonneg B hB)
  have hzero := sum_map_eq_zero (Qf c) (restr u) hnn hid.symm
  exact fun B hB =>
    { nonneg := restr_nonneg hu.nonneg B hB
      nontrivial := restr_mem_pos B hB
      vanishes := hzero B hB }

/-- **Copositive corollary (ii).**  For a copositive bandwidth-2 matrix with every
`c i 2 > 0`, the support of a minimal zero is an interval. -/
theorem copositive_minimalZero_isInterval (hband : Bandwidth c 2) (hc2 : ∀ i, 0 < c i 2)
    (hcop : Copositive c) {u : List Int} (hu : MinimalZero c u) : IsInterval u := by
  have hu0 := hu.1
  have hblocks := copositive_restr_isZero hband hc2 hcop hu0
  have hD := restr_D_preserved id rfl u hu0.nonneg
  by_cases hlen : (restr u).length ≤ 1
  · exact hlen
  · exfalso
    have h2 : 2 ≤ (restr u).length := by omega
    cases hb : restr u with
    | nil => rw [hb] at h2; simp at h2
    | cons B L =>
      cases hL : L with
      | nil => rw [hb, hL] at h2; simp at h2
      | cons C T =>
        have hBmem : B ∈ restr u := by rw [hb]; exact List.mem_cons_self ..
        have hCmem : C ∈ restr u := by
          rw [hb, hL]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        -- the first restriction is a zero of `A` and a masking of `u`, hence *is* `u`
        have hBu : B = u := hu.2 B (restr_masked B hBmem) (hblocks B hBmem)
        -- but the second run carries strictly positive mass, so `B` is strictly lighter
        have hCpos : 0 < D id C := restr_D_pos rfl (fun _ ht => ht) hu0.nonneg C hCmem
        have hTnn : 0 ≤ (T.map (D id)).sum :=
          sum_map_nonneg (D id) T (fun z hz =>
            have := restr_D_pos (d := id) rfl (fun _ ht => ht) hu0.nonneg z
              (by rw [hb, hL]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
            Int.le_of_lt this)
        rw [hb, hL] at hD
        simp only [List.map_cons, List.sum_cons] at hD
        rw [hBu] at hD
        omega

end Copositive

/-! ## Numeric cross-checks against the exhaustive Python sweep -/

section Checks
-- a = 4369, b = -6314, c = 2050

example : Q 4369 (-6314) 2050 [1,1,0,1,1] = 6898 := by decide
example : Q 4369 (-6314) 0    [1,1,0,1,1] = 4848 := by decide
example : 2 * Q 4369 (-6314) 0 [1,1]      = 4848 := by decide

-- margin  Q - Qblocks  equals  c * iso
example : Q 4369 (-6314) 2050   [1,0,1] - Qblocks 4369 (-6314) 2050   [1,0,1] = 2050  := by decide
example : Q 4369 (-6314) 0      [1,0,1] - Qblocks 4369 (-6314) 0      [1,0,1] = 0     := by decide
example : Q 4369 (-6314) (-100) [3,0,3,0,3,0,3]
        - Qblocks 4369 (-6314) (-100) [3,0,3,0,3,0,3] = -2700 := by decide

example : blocks [1,1,0,1,1] = [[1,1],[1,1]] := by decide
example : iso [1,1,0,1,1] = 1 := by decide
example : iso [3,0,3,0,3,0,3] = 27 := by decide

-- edge cases of `blocks`
example : blocks ([] : List Int) = []            := by decide
example : blocks [0]             = []            := by decide
example : blocks [0,0]           = []            := by decide
example : blocks [1]             = [[1]]         := by decide
example : blocks [1,2,3]         = [[1,2,3]]     := by decide
example : blocks [0,1,0]         = [[1]]         := by decide
example : blocks [1,0,0,1]       = [[1],[1]]     := by decide
example : blocks [3,0,3,0,3,0,3] = [[3],[3],[3],[3]] := by decide

-- the position-preserving restrictions of the same signals: same length as the input
example : restr ([] : List Int) = []                       := by decide
example : restr [0,0]           = []                       := by decide
example : restr [1,2,3]         = [[1,2,3]]                := by decide
example : restr [0,1,0]         = [[0,1,0]]                := by decide
example : restr [1,0,0,1]       = [[1,0,0,0],[0,0,0,1]]    := by decide
example : restr [1,1,0,1,1]     = [[1,1,0,0,0],[0,0,0,1,1]] := by decide

-- `iso` ignores zeros that are not flanked on both sides
example : iso [1,0,0,1] = 0 := by decide
example : iso [0,1,0]   = 0 := by decide

/-! ### The counterexample family: extraction versus masking -/

/-- The minimal counterexample of the introduction: a **diagonal** matrix whose diagonal is
`(1, 1, 5)`.  Every off-diagonal coefficient vanishes, so the cross term is identically `0`
and the identity is a statement about the diagonal alone. -/
def cEx : Nat → Nat → Int := fun i L => if L = 0 then (if i = 2 then 5 else 1) else 0

example : Qf cEx [1,0,1]                            = 6 := by decide
example : cross cEx 0 [1,0,1]                       = 0 := by decide
example : ((restr  [1,0,1]).map (Qf cEx)).sum       = 6 := by decide
example : ((blocks [1,0,1]).map (Qf cEx)).sum       = 2 := by decide

/-- **The extraction form of the identity is false for position-dependent coefficients.**
Extracted blocks are re-indexed from `0`, so the mark at position `2` is charged the
coefficient of position `0`.  Contrast `Qblocks_eq_Qrestr`, where Toeplitz coefficients make
the two forms agree for every nonnegative signal. -/
theorem extraction_breaks_position_dependence :
    ((blocks [1,0,1]).map (Qf cEx)).sum + cross cEx 0 [1,0,1] ≠ Qf cEx [1,0,1] := by decide

/-- …while the position-preserving form is exact on the same data. -/
example : ((restr [1,0,1]).map (Qf cEx)).sum + cross cEx 0 [1,0,1] = Qf cEx [1,0,1] := by decide

/-- **Nonnegativity is required.**  At `x = [1,-1,1]` position `1` lies outside every run, so
its diagonal contribution is lost and even the position-preserving identity fails. -/
theorem nonneg_is_needed :
    ((restr [1,-1,1]).map (Qf cEx)).sum + cross cEx 0 [1,-1,1] ≠ Qf cEx [1,-1,1] := by decide

example : restr [1,-1,1] = [[1,0,0],[0,0,1]] := by decide
example : Qf cEx [1,-1,1] = 7 := by decide
example : ((restr [1,-1,1]).map (Qf cEx)).sum = 6 := by decide

/-! ### Position-dependent coefficient functions used by the sweeps -/

/-- A genuinely non-Toeplitz bandwidth-2 matrix: **every** diagonal varies with position. -/
def cVar : Nat → Nat → Int := fun i L =>
  if L = 0 then 4369 + 11 * (i : Int)
  else if L = 1 then -6314 + 5 * (i : Int)
  else if L = 2 then 2050 + 7 * (i : Int)
  else 0

theorem cVar_band : Bandwidth cVar 2 := by
  intro i L h
  simp only [cVar]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem cVar_c2_pos (i : Nat) : 0 < cVar i 2 := by
  show (0 : Int) < 2050 + 7 * (i : Int)
  omega

/-- A non-Toeplitz matrix with a *negative* varying diagonal: it has many zeros, which is
what makes the copositive sweeps non-vacuous. -/
def cNeg : Nat → Nat → Int := fun i L =>
  if L = 0 then -(2 + (i : Int))
  else if L = 1 then 1
  else if L = 2 then 3 + (i : Int)
  else 0

theorem cNeg_band : Bandwidth cNeg 2 := by
  intro i L h
  simp only [cNeg]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem cNeg_c2_pos (i : Nat) : 0 < cNeg i 2 := by
  show (0 : Int) < 3 + (i : Int)
  omega

/-- Bandwidth 1: no lag-2 coefficient at all, so `cross_eq_zero_of_band_one` applies. -/
def cBand1 : Nat → Nat → Int := fun i L =>
  if L = 0 then 7 + (i : Int) else if L = 1 then -3 - 2 * (i : Int) else 0

/-- Bandwidth 3: lag 3 genuinely straddles a block boundary, so `cross` is not vacuous. -/
def cLag3 : Nat → Nat → Int := fun i L =>
  if L = 0 then 1 else if L = 3 then 1 + (i : Int) else 0

example : Qf cLag3 [1,0,0,1]                          = 3 := by decide
example : ((restr [1,0,0,1]).map (Qf cLag3)).sum      = 2 := by decide
example : cross cLag3 0 [1,0,0,1]                     = 1 := by decide
-- the two lag-3 straddling pairs carry *different* coefficients, `1` and `4`
example : Qf cLag3 [1,0,0,1,0,0,1]                     = 8 := by decide
example : ((restr [1,0,0,1,0,0,1]).map (Qf cLag3)).sum = 3 := by decide
example : cross cLag3 0 [1,0,0,1,0,0,1]                = 5 := by decide

-- Part 2: the Toeplitz bridge
example : Qf (toep 4369 (-6314) 2050) [1,1,0,1,1] = Q 4369 (-6314) 2050 [1,1,0,1,1] := by decide
example : cross (toep 4369 (-6314) 2050) 0 [1,1,0,1,1] = 2050 := by decide
example : cross (toep 4369 (-6314) 2050) 0 [1,0,1]     = 2050 := by decide
example : isoW (toep 4369 (-6314) 2050) 0 [3,0,3,0,3,0,3] = 2050 * 27 := by decide
-- …and the position-dependent weighting really does differ from `c · iso`
example : isoW cVar 0 [1,0,1,0,1] = (2050 + 0) + (2050 + 14) := by decide

-- Part 4: preservation of an arbitrary pointwise `d` with `d 0 = 0`
example : D id [1,1,0,1,1] = ([1,1,0,1,1] : List Int).sum := by decide
example : D (fun t => t * t) [1,1,0,1,1] = sqnorm [1,1,0,1,1] := by decide
example : ((restr [1,1,0,1,1]).map (D id)).sum = D id [1,1,0,1,1] := by decide
example : ((restr [1,2,0,3,1]).map (D (fun t => 7*t - 3*t*t))).sum
        = D (fun t => 7*t - 3*t*t) [1,2,0,3,1] := by decide
-- `d t = t + 1` has `d 0 = 1 ≠ 0`, and preservation genuinely breaks
example : ((restr [1,0,1]).map (D (fun t => t + 1))).sum ≠ D (fun t => t + 1) [1,0,1] := by decide

-- Part 3: the restrictions really are length-preserving maskings
example : maskedB [1,0,0,0] [1,0,0,1] = true  := by decide
example : maskedB [1,0,0,2] [1,0,0,1] = false := by decide
example : (restr [1,1,0,1,1]).all (fun B => maskedB B [1,1,0,1,1]) = true := by decide

/-! ### Executable exhaustive re-run of the Python sweep

`n ≤ 7`, marks `0..3`: `4^0 + 4^1 + … + 4^7 = 21845` signals per sweep.  These are
*executable checks*, not proofs — the theorems above already cover every nonnegative list.
They exist so that the Lean definitions can be confronted with the independent Python sweep
on identical data, and so that the failure of the extraction form is pinned down by a
number rather than by a single hand-picked example. -/

/-- The search space of every sweep below, and of the §7 minimality claim: all signals of
length `n` with marks in `{0,…,3}`. -/
def allLists : Nat → List (List Int)
  | 0     => [[]]
  | n + 1 => (allLists n).flatMap (fun l => [0, 1, 2, 3].map (fun v => v :: l))

/-! ### §7 over the sweep's own search space

The bound `defect_ge_neg_2700` is about *every* nonnegative signal with marks in `{0,…,3}`
and length at most seven.  Specialised to the `21 845` signals the sweeps enumerate, it says
that the running minimum `defectMin` printed below can never drop under `−2700` — and, with
`(3,0,3,0,3,0,3)` sitting in `allLists 7`, that it reaches exactly `−2700` there.  Nothing
here is decided by enumeration: `defectMin_eq_neg_2700` is a proof. -/

/-- Every enumerated signal has the length, sign and mark bound the sweep intends. -/
theorem allLists_spec : ∀ n : Nat, ∀ x ∈ allLists n,
    x.length = n ∧ Nonneg x ∧ ∀ v ∈ x, v ≤ 3 := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have hnil : x = [] := by simpa [allLists] using hx
    subst hnil
    exact ⟨rfl, trivial, by simp⟩
  | succ n ih =>
    intro x hx
    have heq : allLists (n + 1)
        = (allLists n).flatMap (fun l => [0, 1, 2, 3].map (fun v => v :: l)) := rfl
    rw [heq] at hx
    rcases List.mem_flatMap.1 hx with ⟨l, hl, hxl⟩
    rcases List.mem_map.1 hxl with ⟨v, hv, rfl⟩
    obtain ⟨hlen, hnn, hb⟩ := ih l hl
    have hv3 : 0 ≤ v ∧ v ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> decide
    refine ⟨by simp [hlen], ⟨hv3.1, hnn⟩, ?_⟩
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hv3.2
    · exact hb w hw

theorem mem_allLists_cons {n : Nat} {v : Int} {l : List Int}
    (hv : v ∈ ([0,1,2,3] : List Int)) (hl : l ∈ allLists n) : v :: l ∈ allLists (n + 1) := by
  show v :: l ∈ (allLists n).flatMap (fun l => [0, 1, 2, 3].map (fun v => v :: l))
  exact List.mem_flatMap.2 ⟨l, hl, List.mem_map.2 ⟨v, hv, rfl⟩⟩

theorem alternating_mem_allLists : ([3,0,3,0,3,0,3] : List Int) ∈ allLists 7 := by
  have h0 : ([] : List Int) ∈ allLists 0 := by decide
  exact mem_allLists_cons (by decide) (mem_allLists_cons (by decide)
    (mem_allLists_cons (by decide) (mem_allLists_cons (by decide)
      (mem_allLists_cons (by decide) (mem_allLists_cons (by decide)
        (mem_allLists_cons (by decide) h0))))))

/-- One step of the running minimum: signals without an isolated zero are skipped, matching
the §7 phrase "over all configurations with an isolated zero". -/
def defectStep (acc : Int) (x : List Int) : Int :=
  if 0 < iso x then (if defect x < acc then defect x else acc) else acc

/-- The smallest defect among the signals of length `n` that carry an isolated zero; `0` when
there are none (which is a harmless upper start, since every defect here is `≤ 0`). -/
def defectMin (n : Nat) : Int := (allLists n).foldl defectStep 0

theorem defectStep_le (acc : Int) (x : List Int) : defectStep acc x ≤ acc := by
  simp only [defectStep]
  by_cases h : 0 < iso x
  · rw [if_pos h]
    by_cases h' : defect x < acc
    · rw [if_pos h']; omega
    · rw [if_neg h']; omega
  · rw [if_neg h]; omega

theorem defectStep_ge {acc : Int} {x : List Int} (hacc : -2700 ≤ acc)
    (hx : -2700 ≤ defect x) : -2700 ≤ defectStep acc x := by
  simp only [defectStep]
  by_cases h : 0 < iso x
  · rw [if_pos h]
    by_cases h' : defect x < acc
    · rw [if_pos h']; omega
    · rw [if_neg h']; omega
  · rw [if_neg h]; omega

theorem foldl_defectStep_le_acc :
    ∀ (l : List (List Int)) (acc : Int), l.foldl defectStep acc ≤ acc := by
  intro l
  induction l with
  | nil => intro acc; exact Int.le_refl acc
  | cons x t ih =>
    intro acc
    have h1 := ih (defectStep acc x)
    have h2 := defectStep_le acc x
    rw [List.foldl_cons]
    omega

theorem foldl_defectStep_ge :
    ∀ (l : List (List Int)) (acc : Int), -2700 ≤ acc →
      (∀ x ∈ l, -2700 ≤ defect x) → -2700 ≤ l.foldl defectStep acc := by
  intro l
  induction l with
  | nil => intro acc hacc _; exact hacc
  | cons x t ih =>
    intro acc hacc hall
    rw [List.foldl_cons]
    exact ih (defectStep acc x) (defectStep_ge hacc (hall x (List.mem_cons_self ..)))
      (fun z hz => hall z (List.mem_cons_of_mem _ hz))

theorem foldl_defectStep_le :
    ∀ (l : List (List Int)) (acc : Int) (y : List Int), y ∈ l → 0 < iso y →
      l.foldl defectStep acc ≤ defect y := by
  intro l
  induction l with
  | nil => intro _ y hy _; simp at hy
  | cons x t ih =>
    intro acc y hy hiso
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hy with rfl | hy
    · have h1 := foldl_defectStep_le_acc t (defectStep acc y)
      have h2 : defectStep acc y ≤ defect y := by
        simp only [defectStep, if_pos hiso]
        by_cases h' : defect y < acc
        · rw [if_pos h']; omega
        · rw [if_neg h']; omega
      omega
    · exact ih (defectStep acc x) y hy hiso

/-- **§7 over the search space, lower bound.**  For `n ≤ 7` the running minimum never drops
under `−2700`. -/
theorem defectMin_ge_neg_2700 (n : Nat) (hn : n ≤ 7) : -2700 ≤ defectMin n :=
  foldl_defectStep_ge (allLists n) 0 (by omega) (fun x hx =>
    have h := allLists_spec n x hx
    defect_ge_neg_2700 x h.2.1 h.2.2 (by omega))

/-- **§7 over the search space, exactly.**  `−2700` is the minimum defect over all
configurations with an isolated zero, marks in `{0,…,3}` and length seven. -/
theorem defectMin_eq_neg_2700 : defectMin 7 = -2700 := by
  have hge := defectMin_ge_neg_2700 7 (by omega)
  have hle : defectMin 7 ≤ defect [3,0,3,0,3,0,3] :=
    foldl_defectStep_le (allLists 7) 0 [3,0,3,0,3,0,3] alternating_mem_allLists (by decide)
  rw [defect_attained.2.2.2.2] at hle
  omega

/-- **Theorem 2.1, its extraction form, and Corollary 2.1 — in one pass.**  Per signal the
triple counts violations of

  1. `Qf c x = Σ_r Qf c (x^(r)) + cross c x`   (position-preserving blocks — must be `0`),
  2. the same equation with *extracted* blocks (must be nonzero off Toeplitz),
  3. `cross c x = isoW c x`                    (Corollary 2.1 — must be `0` when `c` is
     bandwidth 2, which both matrices below are).

Sharing `Qf c x` and `cross c 0 x` across the three keeps the sweep to a single traversal. -/
private def identityCounts (c : Nat → Nat → Int) (n : Nat) : Nat × Nat × Nat :=
  (allLists n).foldl
    (fun acc x =>
      let k := Qf c x - cross c 0 x
      (acc.1        + (if ((restr  x).map (Qf c)).sum == k       then 0 else 1),
       acc.2.1      + (if ((blocks x).map (Qf c)).sum == k       then 0 else 1),
       acc.2.2      + (if cross c 0 x == isoW c 0 x              then 0 else 1)))
    (0, 0, 0)

/-- Signals whose cross term is nonzero. -/
private def crossNonzero (c : Nat → Nat → Int) (n : Nat) : Nat :=
  ((allLists n).filter (fun x => cross c 0 x != 0)).length

/-- Theorem 2.1 beyond bandwidth 2, and the non-vacuity of `cross` there.  The pair is
`(violations of the position-preserving identity, signals with a nonzero cross term)`. -/
private def lagThreeCounts (c : Nat → Nat → Int) (n : Nat) : Nat × Nat :=
  (allLists n).foldl
    (fun acc x =>
      let k := cross c 0 x
      (acc.1 + (if Qf c x == ((restr x).map (Qf c)).sum + k then 0 else 1),
       acc.2 + (if k == 0 then 0 else 1)))
    (0, 0)

/-- Part 0's lag-2 GD identity with *extracted* blocks, and `Qblocks_eq_Qrestr`: for Toeplitz
coefficients extraction and masking agree.  The pair is `(gd violations, agree violations)`. -/
private def toeplitzCounts (a b c : Int) (n : Nat) : Nat × Nat :=
  (allLists n).foldl
    (fun acc x =>
      let Qb := Qblocks a b c x
      (acc.1 + (if Q a b c x == Qb + c * iso x                   then 0 else 1),
       acc.2 + (if ((restr x).map (Q a b c)).sum == Qb           then 0 else 1)))
    (0, 0)

/-- Lemma 4.1: `Σ_r D d (x^(r)) = D d x` whenever `d 0 = 0`.  The pair is
`(violations for d t = 7t − 3t², violations for d t = t + 1)`; the second `d` has `d 0 = 1`,
so it must fail — `d 0 = 0` is not a convenience hypothesis. -/
private def restrDCounts (n : Nat) : Nat × Nat :=
  (allLists n).foldl
    (fun acc x =>
      let R := restr x
      (acc.1 + (if (R.map (D (fun t => 7*t - 3*t*t))).sum == D (fun t => 7*t - 3*t*t) x
                then 0 else 1),
       acc.2 + (if (R.map (D (fun t => t + 1))).sum == D (fun t => t + 1) x
                then 0 else 1)))
    (0, 0)

/-- **Structure of the restrictions, and copositive corollary (ii).**  The triple counts

  1. signals with a restriction that is not a length-preserving masking (must be `0`),
  2. signals with two or more runs (the test set for (ii) — must be nonzero),
  3. among those, signals whose first restriction is *not* a proper masking of `x`
     (must be `0`): this is what contradicts minimality in
     `copositive_minimalZero_isInterval`. -/
private def submaskCounts (n : Nat) : Nat × Nat × Nat :=
  (allLists n).foldl
    (fun acc x =>
      let R := restr x
      let m := if R.all (fun B => maskedB B x && B.length == x.length) then 0 else 1
      if 2 ≤ R.length then
        let B := R.headD []
        (acc.1 + m, acc.2.1 + 1,
         acc.2.2 + (if maskedB B x ∧ D id B < D id x then 0 else 1))
      else (acc.1 + m, acc.2.1, acc.2.2))
    (0, 0, 0)

/-- **Copositive corollary (i), engine form.**  Whenever `Qf c x ≤ 0` and `x` has an isolated
zero, some block restriction must satisfy `Qf c B < 0`, because
`Σ_r Qf c (x^(r)) = Qf c x − isoW c 0 x < 0`.  A copositive matrix cannot do that, which is
exactly the proof of `copositive_zero_iso` (there `Qf c x = 0`; `≤ 0` runs the same argument
on a larger test set).  The pair is `(signals tested, violations)`. -/
private def copositiveCounts (c : Nat → Nat → Int) (n : Nat) : Nat × Nat :=
  (allLists n).foldl
    (fun acc x =>
      if Qf c x ≤ 0 ∧ 0 < iso x then
        (acc.1 + 1, acc.2 + (if (restr x).any (fun B => decide (Qf c B < 0)) then 0 else 1))
      else acc)
    (0, 0)

-- Each line is one entry per `n = 0 .. 7`; `21845` signals in total per line.

-- Expected: `[(0,0,0), (0,0,0), (0,3,0), (0,24,0), (0,135,0), (0,660,0), (0,3003,0),
--             (0,13104,0)]`
-- Theorem 2.1 and Corollary 2.1 hold for a genuinely non-Toeplitz bandwidth-2 matrix;
-- the EXTRACTION form does not.
#eval (List.range 8).map (identityCounts cVar)
-- Expected: middle component nonzero from n = 3 on, outer components all `0`.
-- The same for the diagonal counterexample family of the introduction.
#eval (List.range 8).map (identityCounts cEx)
-- Expected: first component all `0` (Theorem 2.1 also holds at lag 3), second nonzero from
-- n = 4 on (lag 3 DOES straddle a block boundary, so `cross` is not vacuous).
#eval (List.range 8).map (lagThreeCounts cLag3)
-- Expected: `[(0,0), …]`  — Part 0's identity, and `Qblocks_eq_Qrestr`.
#eval (List.range 8).map (toeplitzCounts 4369 (-6314) 2050)
-- Expected: `[0, 0, 0, 0, 0, 0, 0, 0]`  — Theorem 2.2: bandwidth 1 never straddles.
#eval (List.range 8).map (crossNonzero cBand1)
-- Expected: first component all `0`, second nonzero from n = 1 on (`d 0 = 1 ≠ 0` breaks it).
#eval (List.range 8).map restrDCounts
-- Expected: first and third components all `0`, second nonzero from n = 3 on.
#eval (List.range 8).map submaskCounts
-- Expected: second component all `0`, first nonzero (the test is not vacuous).
#eval (List.range 8).map (copositiveCounts cNeg)
-- Expected: `[0, 0, 0, -900, -900, -1800, -1800, -2700]`  — the §7 running minimum of the
-- defect over the configurations with an isolated zero.  Unlike the lines above this one is
-- backed by proofs and not only by the enumeration: `defectMin_ge_neg_2700` bounds every
-- entry from below and `defectMin_eq_neg_2700` pins the last one down.
#eval (List.range 8).map defectMin

end Checks

end LagTwoPositivity
