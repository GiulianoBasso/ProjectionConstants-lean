/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Invariant.Circulant
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic

/-!
# The projection constant of `ℓ₁ⁿ`

We prove Grünbaum's formula [G, Theorem 3]

  `λ(ℓ₁ⁿ) = n C(n-1, ⌊(n-1)/2⌋) / 2ⁿ⁻¹`,

together with the remark after it that `λ(ℓ₁²ᵐ⁺¹) = λ(ℓ₁²ᵐ⁺²)`.

The Rademacher functions `rᵢ(a) = (-1)^{aᵢ}`, `i < n`, on the group `G = (ℤ/2)ⁿ` span an isometric
copy of `ℓ₁ⁿ` in `ℓ∞(G)`: `‖∑ᵢ xᵢ rᵢ‖_∞ = max_a |∑ᵢ (-1)^{aᵢ} xᵢ| = ∑ᵢ |xᵢ|`. They are orthogonal,
`∑_a rᵢ(a) rⱼ(a) = 2ⁿ δᵢⱼ`, and the orthogonal projection onto their span is the circulant matrix
`P_{ab} = 2⁻ⁿ ∑ᵢ (-1)^{aᵢ - bᵢ}`. By `absProjConst_range_eq_sum_norm` this projection is minimal and

  `λ(ℓ₁ⁿ) = 2⁻ⁿ ∑_a |∑ᵢ (-1)^{aᵢ}| = 2⁻ⁿ ∑ₖ C(n, k) |n - 2k|`,

and the last sum equals `2n C(n-1, ⌊(n-1)/2⌋)` by a telescoping argument. Grünbaum uses the same
embedding (with the `2ⁿ⁻¹` sign vectors whose first coordinate is `+1`) and proves the minimality
of `P` by a direct computation.

## Main definitions

* `rademacher n`: the `2ⁿ × n` matrix of the Rademacher functions `rᵢ(a) = (-1)^{aᵢ}`.
* `l1Kernel n`: the function `a ↦ 2⁻ⁿ ∑ᵢ (-1)^{aᵢ}` with `circulant (l1Kernel n) = 2⁻ⁿ r rᵀ`.
* `l1Embedding n`: the isometric embedding `ℓ₁ⁿ → ℓ∞((ℤ/2)ⁿ)`, `x ↦ ∑ᵢ xᵢ rᵢ`.

## Main statements

* `absProjConst_l1_eq_sum`: `λ(ℓ₁ⁿ) = 2⁻ⁿ ∑ₖ C(n, k) |n - 2k|`.
* `sum_choose_mul_abs_sub`: `∑ₖ C(n, k) |n - 2k| = 2n C(n-1, ⌊(n-1)/2⌋)`.
* `absProjConst_l1`: **Grünbaum's formula** `λ(ℓ₁ⁿ) = n C(n-1, ⌊(n-1)/2⌋) / 2ⁿ⁻¹`.
* `absProjConst_l1_odd_eq_even`: `λ(ℓ₁²ᵐ⁺¹) = λ(ℓ₁²ᵐ⁺²)`.
* `absProjConst_l1_three`: `λ(ℓ₁³) = 3/2`.

## Implementation notes

`ℓ₁ⁿ` is `PiLp 1 (fun _ : Fin n ↦ ℝ)`, and the group `(ℤ/2)ⁿ` is `Fin n → ZMod 2`.

## References

* [G] B. Grünbaum, *Projection constants*, Trans. Amer. Math. Soc. 95 (1960), 451–465.

## Tags

projection constant, ℓ₁, cross-polytope, Rademacher functions, binomial coefficients
-/

open Matrix Finset WithLp

namespace ProjectionConstants

/-! ### Signs in `ℤ/2` -/

section Sign

private lemma neg_one_pow_val_sub (s t : ZMod 2) :
    (-1 : ℝ) ^ (s - t).val = (-1) ^ s.val * (-1) ^ t.val := by
  have h : (s - t).val = (s.val + t.val) % 2 := by revert s t; decide
  rw [h, ← neg_one_pow_eq_pow_mod_two, pow_add]

private lemma neg_one_pow_val_add_one (t : ZMod 2) : (-1 : ℝ) ^ (t + 1).val = -(-1) ^ t.val := by
  have h : (t + 1).val = (t.val + 1) % 2 := by revert t; decide
  rw [h, ← neg_one_pow_eq_pow_mod_two, pow_succ, mul_neg_one]

private lemma neg_one_pow_val_mul_self (t : ZMod 2) : (-1 : ℝ) ^ t.val * (-1) ^ t.val = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

private lemma neg_one_pow_val_eq (t : ZMod 2) :
    (-1 : ℝ) ^ t.val = 1 - 2 * (if t = 1 then 1 else 0) := by
  rcases (by revert t; decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) t with rfl | rfl
  · simp
  · simp [ZMod.val_one]
    norm_num

end Sign

/-! ### The Rademacher functions -/

variable (n : ℕ)

/-- The **Rademacher functions** `rᵢ(a) = (-1)^{aᵢ}` on `(ℤ/2)ⁿ`, as the columns of a matrix. -/
def rademacher : Matrix (Fin n → ZMod 2) (Fin n) ℝ := Matrix.of fun a i ↦ (-1) ^ (a i).val

/-- The Rademacher functions are orthogonal: `rᵀ r = 2ⁿ • 1`. -/
theorem rademacher_transpose_mul_self :
    (rademacher n)ᵀ * rademacher n = (2 ^ n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [mul_apply, transpose_apply, rademacher, of_apply, Matrix.smul_apply, one_apply,
    smul_eq_mul]
  split_ifs with h
  · subst h
    simp [neg_one_pow_val_mul_self]
  · -- translating by the unit vector at `i` changes the sign of every term
    have key := Fintype.sum_equiv (Equiv.addRight (Pi.single i (1 : ZMod 2)))
      (fun a : Fin n → ZMod 2 ↦ (-1 : ℝ) ^ (a i).val * (-1) ^ (a j).val)
      (fun a : Fin n → ZMod 2 ↦ -((-1 : ℝ) ^ (a i).val * (-1) ^ (a j).val)) fun a ↦ by
        simp [Ne.symm h, neg_one_pow_val_add_one]
    rw [Finset.sum_neg_distrib] at key
    linarith

/-- The function `a ↦ 2⁻ⁿ ∑ᵢ (-1)^{aᵢ}` on `(ℤ/2)ⁿ`: the orthogonal projection onto the span of
the Rademacher functions is `circulant (l1Kernel n)`. -/
noncomputable def l1Kernel (a : Fin n → ZMod 2) : ℝ := (∑ i, (-1 : ℝ) ^ (a i).val) / 2 ^ n

/-- `circulant (l1Kernel n) = 2⁻ⁿ • r rᵀ`: the orthogonal projection onto the span of the
Rademacher functions is circulant. -/
theorem circulant_l1Kernel :
    circulant (l1Kernel n) = (2 ^ n : ℝ)⁻¹ • (rademacher n * (rademacher n)ᵀ) := by
  ext a b
  simp only [circulant_apply, l1Kernel, Pi.sub_apply, neg_one_pow_val_sub, Matrix.smul_apply,
    mul_apply, transpose_apply, rademacher, of_apply, smul_eq_mul]
  ring

/-- The **projection constant of the span of the Rademacher functions** in `ℓ∞((ℤ/2)ⁿ)`. -/
theorem absProjConst_range_rademacher :
    absProjConst ℝ (LinearMap.range (rademacher n).toLin') = ∑ a, |l1Kernel n a| := by
  have hc : (2 ^ n : ℝ) ≠ 0 := pow_ne_zero n two_ne_zero
  rw [absProjConst_range_eq_sum_norm hc (M := rademacher n)
    (by rw [conjTranspose_eq_transpose_of_trivial, rademacher_transpose_mul_self])
    (by rw [conjTranspose_eq_transpose_of_trivial, circulant_l1Kernel])]
  simp only [Real.norm_eq_abs]

/-! ### The embedding of `ℓ₁ⁿ` -/

/-- The isometric embedding `ℓ₁ⁿ → ℓ∞((ℤ/2)ⁿ)`, `x ↦ ∑ᵢ xᵢ rᵢ`: the norm of the image of `x` is
`max_a |∑ᵢ (-1)^{aᵢ} xᵢ| = ∑ᵢ |xᵢ|`. -/
noncomputable def l1Embedding : (PiLp 1 fun _ : Fin n ↦ ℝ) →ₗᵢ[ℝ] ((Fin n → ZMod 2) → ℝ) where
  toLinearMap := (rademacher n).toLin'.comp (WithLp.linearEquiv 1 ℝ (Fin n → ℝ)).toLinearMap
  norm_map' x := by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      WithLp.linearEquiv_apply, Matrix.toLin'_apply]
    rw [PiLp.norm_eq_of_L1]
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun a ↦ ?_) ?_
    · simp only [mulVec, dotProduct, rademacher, of_apply]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
      simp [norm_mul]
    · -- the sign vector of `x`
      let a : Fin n → ZMod 2 := fun i ↦ if x i < 0 then 1 else 0
      have ha : (rademacher n *ᵥ ofLp x) a = ∑ i, ‖x i‖ := by
        simp only [mulVec, dotProduct, rademacher, of_apply]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases hx : x i < 0
        · simp [a, hx, ZMod.val_one, abs_of_neg hx]
        · simp [a, hx, abs_of_nonneg (not_lt.1 hx)]
      calc ∑ i, ‖x i‖ = ‖(rademacher n *ᵥ ofLp x) a‖ := by
            rw [ha, Real.norm_of_nonneg (by positivity)]
        _ ≤ ‖rademacher n *ᵥ ofLp x‖ := norm_le_pi_norm _ a

/-- The image of `ℓ₁ⁿ` is the span of the Rademacher functions. -/
theorem range_l1Embedding :
    LinearMap.range (l1Embedding n).toLinearMap = LinearMap.range (rademacher n).toLin' :=
  LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)

/-- `λ(ℓ₁ⁿ) = ∑_a |2⁻ⁿ ∑ᵢ (-1)^{aᵢ}|`. -/
theorem absProjConst_l1_eq_sum_abs_l1Kernel :
    absProjConst ℝ (PiLp 1 fun _ : Fin n ↦ ℝ) = ∑ a, |l1Kernel n a| := by
  rw [(hasExtensionProperty_pi (Fin n → ZMod 2)).absProjConst_eq_of_linearIsometry (l1Embedding n),
    range_l1Embedding, ← absProjConst_eq_relProjConst_pi, absProjConst_range_rademacher]

/-! ### Counting signs -/

/-- `∑_a |2⁻ⁿ ∑ᵢ (-1)^{aᵢ}| = 2⁻ⁿ ∑ₖ C(n, k) |n - 2k|`: the sum `∑ᵢ (-1)^{aᵢ}` equals `n - 2k` for
the `C(n, k)` vectors `a` with `k` entries equal to `1`. -/
theorem sum_abs_l1Kernel :
    ∑ a, |l1Kernel n a| =
      (∑ k ∈ range (n + 1), (n.choose k : ℝ) * |(n : ℝ) - 2 * k|) / 2 ^ n := by
  have hsum : ∀ a : Fin n → ZMod 2, ∑ i, (-1 : ℝ) ^ (a i).val = n - 2 * #{i | a i = 1} := by
    intro a
    simp only [neg_one_pow_val_eq, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp
  -- vectors in `(ℤ/2)ⁿ` are indicator functions of subsets of `Fin n`
  let e : (Fin n → ZMod 2) ≃ Finset (Fin n) :=
    { toFun := fun a ↦ {i | a i = 1}
      invFun := fun S i ↦ if i ∈ S then 1 else 0
      left_inv := fun a ↦ funext fun i ↦ by
        have h : ∀ t : ZMod 2, (if t = 1 then 1 else 0) = t := by decide
        simpa using h (a i)
      right_inv := fun S ↦ by ext i; simp }
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  calc ∑ a, |l1Kernel n a| = ∑ a, |(n : ℝ) - 2 * #(e a)| / 2 ^ n := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [l1Kernel, hsum, abs_div, abs_of_pos h2]
        rfl
    _ = ∑ S : Finset (Fin n), |(n : ℝ) - 2 * #S| / 2 ^ n :=
        Fintype.sum_equiv e _ _ fun _ ↦ rfl
    _ = (∑ k ∈ range (n + 1), (n.choose k : ℝ) * |(n : ℝ) - 2 * k|) / 2 ^ n := by
        rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card
          (fun k ↦ |(n : ℝ) - 2 * k| / 2 ^ n), Finset.card_univ, Fintype.card_fin,
          Finset.sum_div]
        simp [nsmul_eq_mul, mul_div_assoc]

/-- `λ(ℓ₁ⁿ) = 2⁻ⁿ ∑ₖ C(n, k) |n - 2k|`. -/
theorem absProjConst_l1_eq_sum :
    absProjConst ℝ (PiLp 1 fun _ : Fin n ↦ ℝ) =
      (∑ k ∈ range (n + 1), (n.choose k : ℝ) * |(n : ℝ) - 2 * k|) / 2 ^ n := by
  rw [absProjConst_l1_eq_sum_abs_l1Kernel, sum_abs_l1Kernel]

/-! ### Evaluation of the binomial sum -/

/-- Telescoping: `∑_{k ≤ m} C(n+1, k) (n + 1 - 2k) = (n + 1) C(n, m)`. -/
theorem sum_range_choose_mul_sub (n m : ℕ) :
    ∑ k ∈ range (m + 1), ((n + 1).choose k : ℝ) * ((n + 1 : ℝ) - 2 * k) = (n + 1) * n.choose m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : ((n + 1).choose (m + 1) : ℝ) * (m + 1) = (n + 1) * n.choose m := by
      exact_mod_cast (Nat.add_one_mul_choose_eq n m).symm
    have h2 : ((n + 1).choose (m + 1) : ℝ) * (n - m) = (n + 1) * n.choose (m + 1) := by
      rcases le_or_gt m n with hm | hm
      · have h := Nat.choose_mul_succ_eq n (m + 1)
        rw [show n + 1 - (m + 1) = n - m by omega] at h
        have h' : ((n.choose (m + 1) * (n + 1) : ℕ) : ℝ) =
            (((n + 1).choose (m + 1) * (n - m) : ℕ) : ℝ) := by rw [h]
        push_cast [Nat.cast_sub hm] at h'
        linarith
      · rw [Nat.choose_eq_zero_of_lt (by omega : n + 1 < m + 1),
          Nat.choose_eq_zero_of_lt (by omega : n < m + 1)]
        simp
    push_cast
    linear_combination h2 - h1

/-- `∑ₖ C(n, k) |n - 2k| = 2n C(n-1, ⌊(n-1)/2⌋)`. -/
theorem sum_choose_mul_abs_sub (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℝ) * |(n : ℝ) - 2 * k| =
      2 * n * (n - 1).choose ((n - 1) / 2) := by
  rcases n with _ | n
  · simp
  simp only [Nat.add_sub_cancel]
  push_cast
  set f : ℕ → ℝ := fun k ↦ ((n + 1).choose k : ℝ) * ((n + 1 : ℝ) - 2 * k) with hf
  -- `∑ₖ C(n+1, k) (n + 1 - 2k) = 0`, by the symmetry `k ↦ n + 1 - k`
  have hzero : ∑ k ∈ range (n + 1 + 1), f k = 0 := by
    have h := Finset.sum_range_reflect f (n + 1 + 1)
    have h' : ∀ j ∈ range (n + 1 + 1), f (n + 1 + 1 - 1 - j) = -f j := fun j hj ↦ by
      have hj' : j ≤ n + 1 := Nat.lt_succ_iff.1 (mem_range.1 hj)
      simp only [hf, show n + 1 + 1 - 1 - j = n + 1 - j by omega, Nat.choose_symm hj',
        Nat.cast_sub hj']
      push_cast
      ring
    rw [Finset.sum_congr rfl h', Finset.sum_neg_distrib] at h
    linarith
  -- `|x| = 2 max(x, 0) - x`
  have hmax : ∀ k ∈ range (n + 1 + 1), ((n + 1).choose k : ℝ) * |(n + 1 : ℝ) - 2 * k| =
      2 * (((n + 1).choose k : ℝ) * max ((n + 1 : ℝ) - 2 * k) 0) - f k := fun k _ ↦ by
    rcases le_total 0 ((n + 1 : ℝ) - 2 * k) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, hf]
      ring
    · rw [abs_of_nonpos h, max_eq_right h, hf]
      ring
  rw [Finset.sum_congr rfl hmax, Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, sub_zero]
  -- only the terms with `2k ≤ n` contribute to the positive part
  rw [show n + 1 + 1 = (n / 2 + 1) + (n + 1 - n / 2) by omega, Finset.sum_range_add]
  have h1 : ∀ k ∈ range (n / 2 + 1), ((n + 1).choose k : ℝ) * max ((n + 1 : ℝ) - 2 * k) 0 =
      f k := fun k hk ↦ by
    have hk' : 2 * k ≤ n := by have := mem_range.1 hk; omega
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast hk'
    rw [max_eq_left (by linarith), hf]
  have h2 : ∀ k ∈ range (n + 1 - n / 2), ((n + 1).choose (n / 2 + 1 + k) : ℝ) *
      max ((n + 1 : ℝ) - 2 * ((n / 2 + 1 + k : ℕ) : ℝ)) 0 = 0 := fun k _ ↦ by
    have hk' : n + 1 ≤ 2 * (n / 2 + 1 + k) := by omega
    have : ((n + 1 : ℕ) : ℝ) ≤ ((2 * (n / 2 + 1 + k) : ℕ) : ℝ) := by exact_mod_cast hk'
    push_cast at this
    rw [max_eq_right (by push_cast; linarith), mul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero, hf,
    sum_range_choose_mul_sub]
  ring

/-! ### Grünbaum's formula -/

/-- **Grünbaum's formula** [G, Theorem 3]: `λ(ℓ₁ⁿ) = n C(n-1, ⌊(n-1)/2⌋) / 2ⁿ⁻¹`. -/
theorem absProjConst_l1 :
    absProjConst ℝ (PiLp 1 fun _ : Fin n ↦ ℝ) = n * (n - 1).choose ((n - 1) / 2) / 2 ^ (n - 1) := by
  rw [absProjConst_l1_eq_sum, sum_choose_mul_abs_sub]
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    field_simp

/-- [G, §4, Remark]: `λ(ℓ₁²ᵐ⁺¹) = λ(ℓ₁²ᵐ⁺²)`. -/
theorem absProjConst_l1_odd_eq_even (m : ℕ) :
    absProjConst ℝ (PiLp 1 fun _ : Fin (2 * m + 1) ↦ ℝ) =
      absProjConst ℝ (PiLp 1 fun _ : Fin (2 * m + 2) ↦ ℝ) := by
  rw [absProjConst_l1, absProjConst_l1, show 2 * m + 1 - 1 = 2 * m by omega,
    show 2 * m + 2 - 1 = 2 * m + 1 by omega, show 2 * m / 2 = m by omega,
    show (2 * m + 1) / 2 = m by omega]
  -- `(2m + 1) C(2m, m) = (m + 1) C(2m + 1, m)`
  have h := Nat.add_one_mul_choose_eq (2 * m) m
  rw [Nat.choose_symm_half] at h
  have h' : ((2 * m + 1 : ℕ) : ℝ) * (2 * m).choose m = (2 * m + 1).choose m * (m + 1 : ℕ) := by
    exact_mod_cast h
  rw [pow_succ, div_eq_div_iff (by positivity) (by positivity)]
  push_cast at h' ⊢
  linear_combination (2 * 2 ^ (2 * m) : ℝ) * h'

/-- `λ(ℓ₁³) = 3/2`, and hence `λ(ℓ₁⁴) = 3/2` by `absProjConst_l1_odd_eq_even`. -/
theorem absProjConst_l1_three : absProjConst ℝ (PiLp 1 fun _ : Fin 3 ↦ ℝ) = 3 / 2 := by
  rw [absProjConst_l1]
  norm_num [Nat.choose]

end ProjectionConstants
