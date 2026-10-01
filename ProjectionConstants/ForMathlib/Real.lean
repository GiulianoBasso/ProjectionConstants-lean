/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# Elementary real inequalities

Elementary facts about real numbers used throughout the library: first-order conditions for
quadratic polynomials, two consequences of the Cauchy–Schwarz inequality, an estimate for the
difference of two square roots, and the triangular number `m(m+1)/2` as a real number.

## Main statements

* `eq_zero_of_forall_quadratic_nonpos`, `eq_zero_of_forall_quadratic_nonneg`: the linear
  coefficient of a quadratic polynomial with a local extremum at `0` vanishes.
* `Real.sqrt_mul_add_sqrt_mul_le`: `√a √b + √c √d ≤ √(a + c) √(b + d)`.
* `Real.eq_of_sum_mul_eq_sqrt_mul_sqrt`: the equality case of the Cauchy–Schwarz inequality.
* `Real.sq_sqrt_sub_sqrt_le`: `(√a - √b)² ≤ (a - b)² / b`.
* `Nat.cast_mul_succ_div_two`: `m(m+1)/2`, computed in `ℕ`, as a real number.
-/

open Finset

/-- If `2 t β + t² c ≤ 0` for all real `t`, then `β = 0`. -/
theorem eq_zero_of_forall_quadratic_nonpos {β c : ℝ} (h : ∀ t : ℝ, 2 * t * β + t ^ 2 * c ≤ 0) :
    β = 0 := by
  have hK : 0 < |c| + 1 := by positivity
  have h1 := h (β / (|c| + 1))
  have key : 2 * (β / (|c| + 1)) * β + (β / (|c| + 1)) ^ 2 * c =
      β ^ 2 * (2 * (|c| + 1) + c) / (|c| + 1) ^ 2 := by
    field_simp
  rw [key] at h1
  have hpos : 0 < 2 * (|c| + 1) + c := by have := neg_abs_le c; linarith
  have h2 : β ^ 2 * (2 * (|c| + 1) + c) ≤ 0 := by
    have hden : 0 < (|c| + 1) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right h1 hden.le
    rwa [div_mul_cancel₀ _ hden.ne', zero_mul] at this
  have hb2 : β ^ 2 = 0 := by nlinarith [sq_nonneg β]
  exact pow_eq_zero_iff two_ne_zero |>.mp hb2

/-- If `2 s a + s² q ≥ 0` for all `s` with `|s| ≤ δ`, where `δ > 0`, then `a = 0`. -/
theorem eq_zero_of_forall_quadratic_nonneg {a q δ : ℝ} (hδ : 0 < δ)
    (h : ∀ s, |s| ≤ δ → 0 ≤ 2 * s * a + s ^ 2 * q) : a = 0 := by
  by_contra ha
  set σ := min δ (|a| / (|q| + 1)) with hσ
  have hq1 : 0 < |q| + 1 := by positivity
  have hσ0 : 0 < σ := lt_min hδ (div_pos (abs_pos.mpr ha) hq1)
  have hσδ : σ ≤ δ := min_le_left _ _
  have hσa : σ * (|q| + 1) ≤ |a| := by
    have := min_le_right δ (|a| / (|q| + 1))
    rwa [← hσ, le_div_iff₀ hq1] at this
  have hq : q ≤ |q| := le_abs_self q
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have h1 := h σ (by rw [abs_of_pos hσ0]; exact hσδ)
    rw [abs_of_neg hneg] at hσa
    nlinarith [mul_nonneg (sq_nonneg σ) (sub_nonneg.2 hq), mul_pos hσ0 hσ0,
      mul_le_mul_of_nonneg_left hσa hσ0.le]
  · have h1 := h (-σ) (by rw [abs_neg, abs_of_pos hσ0]; exact hσδ)
    rw [abs_of_pos hpos] at hσa
    nlinarith [mul_nonneg (sq_nonneg σ) (sub_nonneg.2 hq), mul_pos hσ0 hσ0,
      mul_le_mul_of_nonneg_left hσa hσ0.le]

namespace Real

/-- `√a √b + √c √d ≤ √(a + c) √(b + d)`. -/
theorem sqrt_mul_add_sqrt_mul_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) : √a * √b + √c * √d ≤ √(a + c) * √(b + d) := by
  have h := sum_sqrt_mul_sqrt_le (univ : Finset (Fin 2)) (f := ![a, c]) (g := ![b, d])
    (fun i ↦ by fin_cases i <;> simp [ha, hc]) (fun i ↦ by fin_cases i <;> simp [hb, hd])
  simpa [Fin.sum_univ_two] using h

/-- The equality case of the Cauchy–Schwarz inequality: if
`∑ᵢ fᵢ gᵢ = ‖f‖ ‖g‖`, then `‖g‖ f = ‖f‖ g`. -/
theorem eq_of_sum_mul_eq_sqrt_mul_sqrt {α : Type*} {s : Finset α} {f g : α → ℝ}
    (h : ∑ i ∈ s, f i * g i = √(∑ i ∈ s, f i ^ 2) * √(∑ i ∈ s, g i ^ 2)) :
    ∀ i ∈ s, √(∑ i ∈ s, g i ^ 2) * f i = √(∑ i ∈ s, f i ^ 2) * g i := by
  set A := √(∑ i ∈ s, f i ^ 2) with hAdef
  set B := √(∑ i ∈ s, g i ^ 2) with hBdef
  have hA : A ^ 2 = ∑ i ∈ s, f i ^ 2 := sq_sqrt (sum_nonneg fun i _ ↦ sq_nonneg _)
  have hB : B ^ 2 = ∑ i ∈ s, g i ^ 2 := sq_sqrt (sum_nonneg fun i _ ↦ sq_nonneg _)
  have hsum : ∑ i ∈ s, (B * f i - A * g i) ^ 2 = 0 := by
    have e : ∀ i, (B * f i - A * g i) ^ 2 =
        B ^ 2 * f i ^ 2 - 2 * A * B * (f i * g i) + A ^ 2 * g i ^ 2 := fun i ↦ by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum]
    rw [h, ← hA, ← hB]
    ring
  intro i hi
  have h0 := (sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (B * f j - A * g j))).1 hsum i hi
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
  linarith

/-- `(√a - √b)² ≤ (a - b)² / b` for `a ≥ 0` and `b > 0`. -/
theorem sq_sqrt_sub_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (√a - √b) ^ 2 ≤ (a - b) ^ 2 / b := by
  rw [le_div_iff₀ hb]
  have hsa := sq_sqrt ha
  have hsb := sq_sqrt hb.le
  have h0a := sqrt_nonneg a
  have h0b := sqrt_nonneg b
  have key : (a - b) ^ 2 = (√a - √b) ^ 2 * (√a + √b) ^ 2 := by
    rw [← mul_pow]
    have : (√a - √b) * (√a + √b) = a - b := by nlinarith
    rw [this]
  rw [key]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith

end Real

/-- `m(m+1)/2`, computed in `ℕ`, as a real number. -/
theorem Nat.cast_mul_succ_div_two (m : ℕ) : ((m * (m + 1) / 2 : ℕ) : ℝ) = m * (m + 1) / 2 := by
  have h2 : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  rw [Nat.cast_div h2 (by norm_num)]
  push_cast
  ring
