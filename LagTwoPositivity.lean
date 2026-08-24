/-
# Lag-2 positivity: the block-decomposition (GD) identity

A self-contained formalisation of the exact decomposition of a lag-2 quadratic form
over a nonnegative integer signal into its *positive blocks* plus an *isolated-zero*
coupling term.

## What is here

For integer coefficients `a b c` and a list `x : List Int`,

    Q a b c x  =  Σ_i a·x_i²  +  Σ_i b·x_i·x_{i+1}  +  Σ_i c·x_i·x_{i+2}

(indices taken only inside range),

    blocks x   =  the maximal runs of strictly positive entries of `x`
    iso x      =  Σ over i with x_i = 0, x_{i-1} > 0, x_{i+1} > 0  of  x_{i-1}·x_{i+1}

### Part 0 — the lag-2 results

  * `gd_identity`          `Q x = Σ_{B ∈ blocks x} Q B + c · iso x`
  * `isolated_zero_strict` `0 < c` and `0 < iso x`  ⟹  `Σ_B Q B < Q x`
  * `sharpness_at_zero`    `Q a b 0 [1,1,0,1,1] = 2 · Q a b 0 [1,1]`

### Part 1 — an arbitrary lag-coefficient list

`Qgen coef x = Σ_{L < coef.length} coef[L] · Σ_i x_i · x_{i+L}` and

  * `Q_eq_Qgen`             `Q a b c = Qgen [a,b,c]`
  * `gd_identity_general`   `Qgen coef x = Σ_B Qgen coef B + crossDefect coef x`
  * `straddle_lag_ge_two`   the lag-1 coefficient cancels identically out of `crossDefect`
  * `adjacent_same_block`   `x_i > 0` and `x_{i+1} > 0` ⟹ both lie in one block
  * `crossDefect_abc`       `crossDefect [a,b,c] x = c · iso x`
  * `gd_identity_is_specialization`  `gd_identity` re-derived from the general one

`crossDefect coef x` is the cross-block pair sum, written as *all* later partners minus the
partners inside one's own block: `Σ_i x_i · (dot (tl coef) rᵢ − dot (tl coef) (headBlock rᵢ))`.

### Part 2 — norm preservation and Rayleigh transfer

  * `blocks_sqnorm_preserved`  `Σ_B sqnorm B = sqnorm x`
  * `rayleigh_transfer`        some block strictly beats the whole, stated by cross
                               multiplication so everything stays in `Int`

### Part 3 — an arbitrary pointwise denominator

`D d x = Σ_i d (x_i)`.

  * `blocks_D_preserved`   `d 0 = 0` ⟹ `Σ_B D d B = D d x`.  **No positivity of `d`.**
  * `blocks_sqnorm_preserved_from_D`  Part 2's law as the `d = (· * ·)` instance
  * `rayleigh_transfer_general`       arbitrary `d` with `d 0 = 0` and `0 < t → 0 < d t`
  * `rayleigh_transfer_from_general`  Part 2's transfer as the `d = (· * ·)` instance
  * `rayleigh_transfer_sum`           the `d = id` instance: denominator `Σ_i x_i`

The preservation law never touches the shape of `d`: entries outside every block are exactly
`0` under `Nonneg`, so they contribute `d 0 = 0` to both sides.  Positivity of `d` enters only
in the transfer, to know each block has a strictly positive denominator.

## The nonnegativity hypothesis

`gd_identity` is **false** without `Nonneg x`.  For `x = [1,-1,1]` the positive runs are
`[[1],[1]]` and `iso x = 0`, so the right-hand side is `2a`, while `Q x = 3a - 2b + c`.
Nonnegativity is what forces every non-block entry to be exactly `0`, which is what kills
the lag-1 cross-boundary term and turns the lag-2 cross-boundary term into `iso`.

## Dependencies

**Lean 4 core only.**  No Mathlib, no Batteries, no `native_decide`.
`#print axioms` on every theorem reports exactly `[propext, Quot.sound]` — in particular
no `Classical.choice` and no `sorryAx`.  The one finite search (`list_forall_or_exists`,
used by `rayleigh_transfer`) is decidable, so it needs no excluded middle.

Squares are written `v * v` rather than `v ^ 2` so that `omega` sees them as atoms;
`Q_cons_sq` records that this agrees with the `^ 2` form.

## Deliberately out of scope

The complete classification of the equality locus (needs reals and measures), the sharp
constant `α` (an algebraic number), and the cyclic / stationary transfer are **not**
formalised here.  Those are cited from the existing reports in the accompanying Letter.
-/

namespace LagTwoPositivity

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


/-! ## Part 1.  A lag-indexed generalisation

`Qgen coef x = Σ_{L < coef.length} coef[L] * Σ_i x_i * x_{i+L}`, written with a
one-step cons recursion.  `dot cs r` is the truncating inner product `Σ_k cs[k] * r[k]`,
so `v * dot (tl coef) r` collects every pair whose left endpoint is the head `v`. -/

section Gen

/-- Truncating inner product `Σ_k cs[k] * r[k]`. -/
def dot : List Int → List Int → Int
  | [],      _       => 0
  | _,       []      => 0
  | c :: cs, v :: vs => c * v + dot cs vs

/-- `Qgen coef x = Σ_{L < coef.length} coef[L] * Σ_i x_i * x_{i+L}`. -/
def Qgen (coef : List Int) : List Int → Int
  | []     => 0
  | v :: r => hd coef * (v * v) + v * dot (tl coef) r + Qgen coef r

@[simp] theorem dot_nil_left {r : List Int} : dot [] r = 0 := by cases r <;> rfl
@[simp] theorem dot_nil_right {cs : List Int} : dot cs [] = 0 := by cases cs <;> rfl

/-- `dot` peels one index off both arguments, with no side condition. -/
theorem dot_eq (cs r : List Int) : dot cs r = hd cs * hd r + dot (tl cs) (tl r) := by
  cases cs with
  | nil => simp
  | cons c cs' =>
    cases r with
    | nil => simp
    | cons v vs => simp [dot]

@[simp] theorem Qgen_nil {coef : List Int} : Qgen coef [] = 0 := rfl

theorem Qgen_cons {coef : List Int} {v : Int} {r : List Int} :
    Qgen coef (v :: r) = hd coef * (v * v) + v * dot (tl coef) r + Qgen coef r := rfl

theorem mul_left_comm' (u w z : Int) : u * (w * z) = w * (u * z) := by
  rw [← Int.mul_assoc, Int.mul_comm u w, Int.mul_assoc]

/-- The lag-2 form of Part 0 is the `coef = [a,b,c]` instance of `Qgen`. -/
theorem Q_eq_Qgen (a b c : Int) : ∀ x : List Int, Q a b c x = Qgen [a, b, c] x := by
  intro x
  induction x with
  | nil => rfl
  | cons v r ih =>
    rw [Q_cons, Qgen_cons, ih]
    have hdot : dot [b, c] r = b * hd r + c * hd (tl r) := by
      rw [dot_eq [b, c] r]
      simp only [hd_cons, tl_cons]
      rw [dot_eq [c] (tl r)]
      simp
    simp only [hd_cons, tl_cons, hdot, Int.mul_add, mul_left_comm' v b, mul_left_comm' v c]
    omega


/-- `dot` against a two-element coefficient list. -/
theorem dot_pair (b c : Int) (r : List Int) : dot [b, c] r = b * hd r + c * hd (tl r) := by
  rw [dot_eq [b, c] r]
  simp only [hd_cons, tl_cons]
  rw [dot_eq [c] (tl r)]
  simp

/-- The block that the head of `r` belongs to, or `[]` when the head is not positive. -/
def headBlock (r : List Int) : List Int := if 0 < hd r then (blocks r).headD [] else []

/-- `crossDefect coef x` is `Σ_i x_i * (Σ_{j > i, j outside i's block} coef[j-i] * x_j)`.
The inner factor is written as `dot (tl coef) r - dot (tl coef) (headBlock r)`: the sum over
*all* later partners minus the sum over the partners inside `i`'s own block. -/
def crossDefect (coef : List Int) : List Int → Int
  | []     => 0
  | v :: r => (if 0 < v then v * (dot (tl coef) r - dot (tl coef) (headBlock r)) else 0)
              + crossDefect coef r

@[simp] theorem crossDefect_nil {coef : List Int} : crossDefect coef [] = 0 := rfl

theorem crossDefect_cons {coef : List Int} {v : Int} {r : List Int} :
    crossDefect coef (v :: r)
      = (if 0 < v then v * (dot (tl coef) r - dot (tl coef) (headBlock r)) else 0)
        + crossDefect coef r := rfl

theorem headBlock_of_pos {r : List Int} (h : 0 < hd r) :
    headBlock r = (blocks r).headD [] := by simp [headBlock, h]

theorem headBlock_of_nonpos {r : List Int} (h : ¬ 0 < hd r) : headBlock r = [] := by
  simp [headBlock, h]

/-- Under nonnegativity the head of `i`'s block is `x_i` itself — including the degenerate
case `x_i = 0`, where both sides are `0`. -/
theorem hd_headBlock {r : List Int} (hr : Nonneg r) : hd (headBlock r) = hd r := by
  by_cases h : 0 < hd r
  · rw [headBlock_of_pos h]; exact hd_firstBlock h
  · have hge : 0 ≤ hd r := nonneg_hd hr
    have h0 : hd r = 0 := by omega
    rw [headBlock_of_nonpos h, h0]; rfl

theorem headBlock_ne_nil {r : List Int} (h : 0 < hd r) : headBlock r ≠ [] := by
  intro hnil
  have : hd (headBlock r) = hd r := by rw [headBlock_of_pos h]; exact hd_firstBlock h
  rw [hnil] at this
  simp only [hd_nil] at this
  omega

theorem hd_mem {x : List Int} (h : x ≠ []) : hd x ∈ x := by
  cases x with
  | nil => exact absurd rfl h
  | cons u t => simp [hd]

/-- **Lag 0 and lag 1 never straddle a block boundary.**  In `crossDefect` the coefficient
`cs[0]` — i.e. `coef[1]`, the lag-1 coefficient — cancels identically, so the cross term is
supported on lags `≥ 2`. -/
theorem straddle_lag_ge_two (cs : List Int) {r : List Int} (hr : Nonneg r) :
    dot cs r - dot cs (headBlock r)
      = dot (tl cs) (tl r) - dot (tl cs) (tl (headBlock r)) := by
  rw [dot_eq cs r, dot_eq cs (headBlock r), hd_headBlock hr]
  omega

/-- The block-membership form of the same fact: if `x_i > 0` and `x_{i+1} > 0` then both sit
in one and the same block. -/
theorem adjacent_same_block {v : Int} {r : List Int} (hv : 0 < v) (hw : 0 < hd r) :
    v ∈ (blocks (v :: r)).headD [] ∧ hd r ∈ (blocks (v :: r)).headD [] := by
  rw [blocks_cons_pos_pos hv hw]
  simp only [List.headD_cons]
  refine ⟨List.mem_cons_self .., ?_⟩
  refine List.mem_cons_of_mem _ ?_
  have hne : headBlock r ≠ [] := headBlock_ne_nil hw
  have hh : hd (headBlock r) = hd r := by rw [headBlock_of_pos hw]; exact hd_firstBlock hw
  have := hd_mem hne
  rw [hh] at this
  rw [← headBlock_of_pos hw]
  exact this

/-- **General GD identity.**  For an arbitrary lag-coefficient list, the excess of the whole
form over the sum of its block forms is exactly the cross-block pair sum. -/
theorem gd_identity_general (coef : List Int) :
    ∀ x : List Int, Nonneg x →
      Qgen coef x = ((blocks x).map (Qgen coef)).sum + crossDefect coef x := by
  intro x
  induction x with
  | nil => intro _; simp
  | cons v r ih =>
    intro hx
    have hr : Nonneg r := nonneg_tail hx
    have IH := ih hr
    rw [Qgen_cons, crossDefect_cons]
    by_cases hv : 0 < v
    · by_cases hw : 0 < hd r
      · rw [blocks_cons_pos_pos hv hw, if_pos hv, headBlock_of_pos hw]
        cases hb : blocks r with
        | nil => exact absurd hb (blocks_ne_nil hw)
        | cons H T =>
          rw [hb] at IH
          simp only [List.headD_cons, List.tail_cons, List.map_cons, List.sum_cons] at IH ⊢
          rw [Qgen_cons, Int.mul_sub]
          omega
      · rw [blocks_cons_pos_nonpos hv hw, if_pos hv, headBlock_of_nonpos hw]
        simp only [List.map_cons, List.sum_cons, Qgen_cons, dot_nil_right, Qgen_nil,
          Int.sub_zero, Int.mul_zero, Int.add_zero]
        omega
    · have hv0 : v = 0 := by have := hx.1; omega
      rw [blocks_cons_nonpos hv, if_neg hv, hv0]
      omega

/-- The lag-2 cross term is exactly `c * iso`: the `coef = [a,b,c]` instance of
`crossDefect`.  This is the bridge that makes `gd_identity` a special case of
`gd_identity_general`. -/
theorem crossDefect_abc (a b c : Int) :
    ∀ x : List Int, Nonneg x → crossDefect [a, b, c] x = c * iso x := by
  intro x
  induction x with
  | nil => intro _; simp
  | cons v r ih =>
    intro hx
    have hr : Nonneg r := nonneg_tail hx
    rw [crossDefect_cons, iso_cons, ih hr]
    simp only [tl_cons]
    by_cases hv : 0 < v
    · by_cases hw : 0 < hd r
      · have hH : hd (headBlock r) = hd r := hd_headBlock hr
        have hT : hd (tl (headBlock r)) = hd (tl r) := by
          rw [headBlock_of_pos hw]; exact hd_tl_firstBlock hr hw
        have hne : ¬ (hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)) := by rintro ⟨h0, -, -⟩; omega
        rw [if_pos hv, if_neg hne, dot_pair, dot_pair, hH, hT, Int.zero_add]
        simp only [Int.sub_self, Int.mul_zero, Int.zero_add]
      · have hge : 0 ≤ hd r := nonneg_hd hr
        have h0 : hd r = 0 := by omega
        rw [if_pos hv, headBlock_of_nonpos hw, dot_pair, dot_pair, h0]
        simp only [hd_nil, tl_nil, Int.mul_zero, Int.zero_add, Int.add_zero, Int.sub_zero,
          true_and]
        by_cases hz : 0 < hd (tl r)
        · rw [if_pos ⟨hv, hz⟩, mul_left_comm' v c (hd (tl r)), Int.mul_add]
        · have hge2 : 0 ≤ hd (tl r) := nonneg_hd (nonneg_tl hr)
          have h0' : hd (tl r) = 0 := by omega
          have hne : ¬ (0 < v ∧ 0 < hd (tl r)) := by rintro ⟨-, h⟩; omega
          rw [if_neg hne, h0', Int.mul_zero, Int.mul_zero, Int.zero_add, Int.zero_add]
    · rw [if_neg hv, Int.zero_add]
      have hne : ¬ (hd r = 0 ∧ 0 < v ∧ 0 < hd (tl r)) := by rintro ⟨-, h, -⟩; omega
      rw [if_neg hne, Int.zero_add]

/-- `gd_identity` is the `coef = [a,b,c]` case of `gd_identity_general`. -/
theorem gd_identity_is_specialization (a b c : Int) (x : List Int) (hx : Nonneg x) :
    Q a b c x = ((blocks x).map (Q a b c)).sum + c * iso x := by
  have hfun : (Q a b c) = (Qgen [a, b, c]) := funext (Q_eq_Qgen a b c)
  rw [hfun, gd_identity_general [a, b, c] x hx, crossDefect_abc a b c x hx]

end Gen

/-! ## Main results -/

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


/-! ## Part 2.  Norm preservation and Rayleigh transfer -/

section Rayleigh

/-- `sqnorm x = Σ_i x_i²`. -/
def sqnorm : List Int → Int
  | []     => 0
  | v :: r => v * v + sqnorm r

@[simp] theorem sqnorm_nil : sqnorm [] = 0 := rfl

theorem sqnorm_cons {v : Int} {r : List Int} : sqnorm (v :: r) = v * v + sqnorm r := rfl

/-- **Blocking preserves the squared norm.**  Entries outside every block are `0`, so they
contribute nothing to `Σ x_i²`. -/
theorem blocks_sqnorm_preserved :
    ∀ x : List Int, Nonneg x → ((blocks x).map sqnorm).sum = sqnorm x := by
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
          rw [sqnorm_cons, sqnorm_cons]
          omega
      · rw [blocks_cons_pos_nonpos hv hw]
        simp only [List.map_cons, List.sum_cons, sqnorm_cons, sqnorm_nil, Int.add_zero]
        omega
    · have hv0 : v = 0 := by have := hx.1; omega
      rw [blocks_cons_nonpos hv, sqnorm_cons, hv0]
      omega

theorem sqnorm_nonneg_of_pos :
    ∀ {B : List Int}, (∀ u ∈ B, 0 < u) → 0 ≤ sqnorm B := by
  intro B
  induction B with
  | nil => intro _; simp
  | cons u t ih =>
    intro h
    have hu : 0 < u := h u (List.mem_cons_self ..)
    have huu : 0 < u * u := Int.mul_pos hu hu
    have := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    rw [sqnorm_cons]
    omega

theorem sqnorm_pos {B : List Int} (h : ∀ u ∈ B, 0 < u) (hne : B ≠ []) : 0 < sqnorm B := by
  cases B with
  | nil => exact absurd rfl hne
  | cons u t =>
    have hu : 0 < u := h u (List.mem_cons_self ..)
    have huu : 0 < u * u := Int.mul_pos hu hu
    have := sqnorm_nonneg_of_pos (fun w hw => h w (List.mem_cons_of_mem _ hw))
    rw [sqnorm_cons]
    omega

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

theorem blocks_sqnorm_pos {x : List Int} : ∀ B ∈ blocks x, 0 < sqnorm B := by
  intro B hB
  exact sqnorm_pos (fun u hu => blocks_pos B hB u hu) (blocks_mem_ne_nil B hB)

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

/-- **Rayleigh transfer.**  If the isolated-zero coupling is active with `c > 0`, then some
block has a strictly smaller Rayleigh quotient than the whole signal.  Stated by cross
multiplication, so everything stays in `Int`. -/
theorem rayleigh_transfer (a b c : Int) {x : List Int}
    (hx : Nonneg x) (hc : 0 < c) (hiso : 0 < iso x) (hS : 0 < sqnorm x) :
    ∃ B ∈ blocks x, 0 < sqnorm B ∧
      Q a b c B * sqnorm x < Q a b c x * sqnorm B := by
  rcases list_forall_or_exists
      (fun B => 0 < sqnorm B ∧ Q a b c B * sqnorm x < Q a b c x * sqnorm B)
      (blocks x) with hall | hex
  · exfalso
    have hle : ∀ B ∈ blocks x, Q a b c x * sqnorm B ≤ Q a b c B * sqnorm x := by
      intro B hB
      have hpos : 0 < sqnorm B := blocks_sqnorm_pos B hB
      have hnn : ¬ (Q a b c B * sqnorm x < Q a b c x * sqnorm B) :=
        fun hlt => hall B hB ⟨hpos, hlt⟩
      omega
    have hsum := sum_mul_le (Q a b c) sqnorm (sqnorm x) (Q a b c x) (blocks x) hle
    rw [blocks_sqnorm_preserved x hx] at hsum
    have hlt : ((blocks x).map (Q a b c)).sum < Q a b c x :=
      isolated_zero_strict a b c hx hc hiso
    have hmul := mul_lt_mul_right' hlt hS
    omega
  · exact hex

end Rayleigh


/-! ## Part 3.  An arbitrary pointwise denominator

`blocks_sqnorm_preserved` never uses that the summand is a square: the whole argument is
"entries outside every block are `0`, and they contribute `0` to both sides".  So it
generalises to any pointwise `d : Int → Int` with `d 0 = 0` — **no positivity of `d` is
needed for the preservation law**.  Positivity is only needed later, to know that each block
has a strictly positive denominator. -/

section GenDenom

/-- `D d x = Σ_i d (x_i)`. -/
def D (d : Int → Int) (x : List Int) : Int := (x.map d).sum

@[simp] theorem D_nil {d : Int → Int} : D d [] = 0 := rfl

theorem D_cons {d : Int → Int} {v : Int} {r : List Int} : D d (v :: r) = d v + D d r := by
  simp [D]

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

theorem sqnorm_eq_D : ∀ x : List Int, sqnorm x = D (fun t => t * t) x := by
  intro x
  induction x with
  | nil => rfl
  | cons v r ih => rw [sqnorm_cons, D_cons, ih]

/-- `blocks_sqnorm_preserved` is the `d = (· * ·)` instance of `blocks_D_preserved`. -/
theorem blocks_sqnorm_preserved_from_D (x : List Int) (hx : Nonneg x) :
    ((blocks x).map sqnorm).sum = sqnorm x := by
  have hfun : sqnorm = D (fun t => t * t) := funext sqnorm_eq_D
  rw [hfun]
  exact blocks_D_preserved (fun t => t * t) (by simp) x hx

theorem D_nonneg_of_pos {d : Int → Int} (hdpos : ∀ t, 0 < t → 0 < d t) :
    ∀ {B : List Int}, (∀ u ∈ B, 0 < u) → 0 ≤ D d B := by
  intro B
  induction B with
  | nil => intro _; simp
  | cons u t ih =>
    intro h
    have hu : 0 < d u := hdpos u (h u (List.mem_cons_self ..))
    have := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    rw [D_cons]
    omega

theorem D_pos {d : Int → Int} (hdpos : ∀ t, 0 < t → 0 < d t) {B : List Int}
    (h : ∀ u ∈ B, 0 < u) (hne : B ≠ []) : 0 < D d B := by
  cases B with
  | nil => exact absurd rfl hne
  | cons u t =>
    have hu : 0 < d u := hdpos u (h u (List.mem_cons_self ..))
    have := D_nonneg_of_pos hdpos (fun w hw => h w (List.mem_cons_of_mem _ hw))
    rw [D_cons]
    omega

theorem blocks_D_pos {d : Int → Int} (hdpos : ∀ t, 0 < t → 0 < d t) {x : List Int} :
    ∀ B ∈ blocks x, 0 < D d B := by
  intro B hB
  exact D_pos hdpos (fun u hu => blocks_pos B hB u hu) (blocks_mem_ne_nil B hB)

/-- **Generalised Rayleigh transfer.**  Same mediant argument, arbitrary pointwise
denominator, still stated by cross multiplication so nothing leaves `Int`. -/
theorem rayleigh_transfer_general (a b c : Int) (d : Int → Int)
    (hd0 : d 0 = 0) (hdpos : ∀ t, 0 < t → 0 < d t) {x : List Int}
    (hx : Nonneg x) (hc : 0 < c) (hiso : 0 < iso x) (hDx : 0 < D d x) :
    ∃ B ∈ blocks x, 0 < D d B ∧
      Q a b c B * D d x < Q a b c x * D d B := by
  rcases list_forall_or_exists
      (fun B => 0 < D d B ∧ Q a b c B * D d x < Q a b c x * D d B)
      (blocks x) with hall | hex
  · exfalso
    have hle : ∀ B ∈ blocks x, Q a b c x * D d B ≤ Q a b c B * D d x := by
      intro B hB
      have hpos : 0 < D d B := blocks_D_pos hdpos B hB
      have hnn : ¬ (Q a b c B * D d x < Q a b c x * D d B) :=
        fun hlt => hall B hB ⟨hpos, hlt⟩
      omega
    have hsum := sum_mul_le (Q a b c) (D d) (D d x) (Q a b c x) (blocks x) hle
    rw [blocks_D_preserved d hd0 x hx] at hsum
    have hlt : ((blocks x).map (Q a b c)).sum < Q a b c x :=
      isolated_zero_strict a b c hx hc hiso
    have hmul := mul_lt_mul_right' hlt hDx
    omega
  · exact hex

/-- `rayleigh_transfer` is the `d = (· * ·)` instance of `rayleigh_transfer_general`. -/
theorem rayleigh_transfer_from_general (a b c : Int) {x : List Int}
    (hx : Nonneg x) (hc : 0 < c) (hiso : 0 < iso x) (hS : 0 < sqnorm x) :
    ∃ B ∈ blocks x, 0 < sqnorm B ∧
      Q a b c B * sqnorm x < Q a b c x * sqnorm B := by
  have hfun : sqnorm = D (fun t => t * t) := funext sqnorm_eq_D
  rw [hfun] at hS ⊢
  exact rayleigh_transfer_general a b c (fun t => t * t) (by simp)
    (fun t ht => Int.mul_pos ht ht) hx hc hiso hS

theorem D_id_eq_sum : ∀ x : List Int, D id x = x.sum := by
  intro x
  induction x with
  | nil => rfl
  | cons v r ih => rw [D_cons, ih]; simp

/-- **Rayleigh transfer for the plain mass denominator `Σ_i x_i`.**  This is the shape the
application needs: the denominator is the total mass, not the squared norm. -/
theorem rayleigh_transfer_sum (a b c : Int) {x : List Int}
    (hx : Nonneg x) (hc : 0 < c) (hiso : 0 < iso x) (hM : 0 < x.sum) :
    ∃ B ∈ blocks x, 0 < B.sum ∧
      Q a b c B * x.sum < Q a b c x * B.sum := by
  have hfun : ∀ y : List Int, D id y = y.sum := D_id_eq_sum
  have hM' : 0 < D id x := by rw [hfun]; exact hM
  rcases rayleigh_transfer_general a b c id rfl (fun _ ht => ht) hx hc hiso hM'
    with ⟨B, hB, hpos, hlt⟩
  simp only [hfun] at hpos hlt
  exact ⟨B, hB, hpos, hlt⟩

end GenDenom

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

-- `iso` ignores zeros that are not flanked on both sides
example : iso [1,0,0,1] = 0 := by decide
example : iso [0,1,0]   = 0 := by decide

-- Part 1: `Q` really is the `coef = [a,b,c]` instance, and the cross term really is `c · iso`
example : Q 4369 (-6314) 2050 [1,1,0,1,1] = Qgen [4369,-6314,2050] [1,1,0,1,1] := by decide
example : crossDefect [4369,-6314,2050] [1,1,0,1,1] = 2050 := by decide
example : crossDefect [4369,-6314,2050] [1,0,1]     = 2050 := by decide

-- Part 1: at lag 3 the cross term is genuinely nonzero — `coef = [1,0,0,1]`, `x = [1,0,0,1]`
example : Qgen [1,0,0,1] [1,0,0,1] = 3 := by decide
example : ((blocks [1,0,0,1]).map (Qgen [1,0,0,1])).sum = 2 := by decide
example : crossDefect [1,0,0,1] [1,0,0,1] = 1 := by decide

-- Part 2: blocking preserves the squared norm
example : sqnorm [1,1,0,1,1] = 4 := by decide
example : ((blocks [1,1,0,1,1]).map sqnorm).sum = 4 := by decide
example : ((blocks [3,0,3,0,3,0,3]).map sqnorm).sum = sqnorm [3,0,3,0,3,0,3] := by decide

-- Part 3: the same preservation for an arbitrary pointwise `d` with `d 0 = 0`
example : D id [1,1,0,1,1] = ([1,1,0,1,1] : List Int).sum := by decide
example : D (fun t => t * t) [1,1,0,1,1] = sqnorm [1,1,0,1,1] := by decide
example : (blocks [1,1,0,1,1]).map (fun B => B.sum) = [2, 2] := by decide
example : ((blocks [1,1,0,1,1]).map (D id)).sum = D id [1,1,0,1,1] := by decide
-- `d t = 7t - 3t²` is nowhere near positive-definite, yet preservation still holds
example : ((blocks [1,2,0,3,1]).map (D (fun t => 7*t - 3*t*t))).sum
        = D (fun t => 7*t - 3*t*t) [1,2,0,3,1] := by decide
-- `d t = t + 1` has `d 0 = 1 ≠ 0`, and preservation genuinely breaks
example : ((blocks [1,0,1]).map (D (fun t => t + 1))).sum ≠ D (fun t => t + 1) [1,0,1] := by decide

/-! ### Executable exhaustive re-run of the Python sweep

`n ≤ 7`, marks `0..3`, `a = 4369, b = -6314, c = 2050`.  This is an *executable check*,
not a proof — `gd_identity` already covers every nonnegative list.  It exists so that the
Lean definitions can be confronted with the independent Python sweep on identical data. -/

private def allLists : Nat → List (List Int)
  | 0     => [[]]
  | n + 1 => (allLists n).flatMap (fun l => [0, 1, 2, 3].map (fun v => v :: l))

private def gdViolations (a b c : Int) (n : Nat) : Nat :=
  ((allLists n).filter (fun x => Q a b c x != Qblocks a b c x + c * iso x)).length

private def genViolations (coef : List Int) (n : Nat) : Nat :=
  ((allLists n).filter (fun x =>
    Qgen coef x != ((blocks x).map (Qgen coef)).sum + crossDefect coef x)).length

private def sqnormViolations (n : Nat) : Nat :=
  ((allLists n).filter (fun x => ((blocks x).map sqnorm).sum != sqnorm x)).length

private def crossNonzero (coef : List Int) (n : Nat) : Nat :=
  ((allLists n).filter (fun x => crossDefect coef x != 0)).length

private def dViolations (d : Int → Int) (n : Nat) : Nat :=
  ((allLists n).filter (fun x => ((blocks x).map (D d)).sum != D d x)).length

-- Each line is one entry per `n = 0 .. 7`.
-- Expected: `[0, 0, 0, 0, 0, 0, 0, 0]`  — lag-2 GD identity.
#eval (List.range 8).map (gdViolations 4369 (-6314) 2050)
-- Expected: `[0, 0, 0, 0, 0, 0, 0, 0]`  — general GD identity at lag 4.
#eval (List.range 8).map (genViolations [7, -3, 5, 11, -2])
-- Expected: `[0, 0, 0, 0, 0, 0, 0, 0]`  — squared norm preserved by blocking.
#eval (List.range 8).map sqnormViolations
-- Expected: `[0, 0, 0, 0, 0, 0, 0, 0]`  — pure lag 0 never straddles a block boundary.
#eval (List.range 8).map (crossNonzero [1])
-- Expected: `[0, 0, 0, 0, 0, 0, 0, 0]`  — pure lag 1 never straddles either (`straddle_lag_ge_two`).
#eval (List.range 8).map (crossNonzero [0, 1])
-- Expected: nonzero from n = 4 on  — lag 3 DOES straddle, so the cross term is not vacuous.
#eval (List.range 8).map (crossNonzero [0, 0, 0, 1])
-- Expected: `[0, 0, 0, 0, 0, 0, 0, 0]`  — `d t = 7t - 3t²` satisfies only `d 0 = 0`, and that
-- is enough: `blocks_D_preserved` needs no positivity of `d`.
#eval (List.range 8).map (dViolations (fun t => 7*t - 3*t*t))
-- Expected: nonzero from n = 1 on  — `d t = t + 1` has `d 0 = 1 ≠ 0`, and preservation breaks.
-- So `d 0 = 0` is not a convenience hypothesis; it is exactly what the law needs.
#eval (List.range 8).map (dViolations (fun t => t + 1))

end Checks

end LagTwoPositivity
