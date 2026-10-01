/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Bounds.Welch
import ProjectionConstants.ChalmersLewicki.Defs

/-!
# A frame bound from the Sidelnikov–Welch inequality

Let `U ∈ 𝕂^{m×N}` with `U U* = I_m`, i.e. the columns `u₁, …, u_N` form a Parseval frame of
`𝕂^m`, and let `t ∈ ℝ^N_+` with `‖t‖₂ ≤ 1`. With `S = ∑ᵢ tᵢ ‖uᵢ‖`, [DL26, Lemma 3.1] states

* `∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩| ≤ (2 + (m-1)√(m+2)) / (2(m+1)²) · (m + 2 + S²)` if `𝕂 = ℝ`,
* `∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩| ≤ √(m+1)/2 + (1 + (m/2 - 1)√(m+1)) / m² · S²` if `𝕂 = ℂ`.

It is the main ingredient of the upper bound for maximal relative projection constants in
complementary dimensions (`ProjectionConstants.Complementary.Main`). The proof uses the case
`t = 2` of the recursive Sidelnikov–Welch inequality (`ProjectionConstants.Bounds.Welch`).

## Main definitions

* `colNorm U i`: the Euclidean norm `‖uᵢ‖` of the `i`-th column of `U`.

## Main statements

* `frame_estimate`: if all unit vectors `xᵢ ∈ 𝕂^m` and real weights `wᵢ` satisfy the
  Sidelnikov–Welch type inequality `c X₂ ≤ s² X₄`, where `X_k = ∑ᵢⱼ wᵢ wⱼ |⟨xᵢ, xⱼ⟩|^k`, then
  `2s(s+1)² ∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩| ≤ s²((s+1)² + 2 - c) + ((s+1)² - 1) S²`.
* `frame_bound_real`, `frame_bound_complex`: its instances `s = √(m+2)` (real) and `s = √(m+1)`
  (complex).
* `weightedAbsSum_gram_le_real`, `weightedAbsSum_gram_le_complex`: [DL26, Lemma 3.1] in the form
  of the paper; the complex case holds for every `RCLike` field.

## Proof sketch

Write `uᵢ = ‖uᵢ‖ xᵢ` with unit vectors `xᵢ` (`exists_unit_columns`), `wᵢ = tᵢ ‖uᵢ‖` and
`rᵢⱼ = |⟨xᵢ, xⱼ⟩| ≤ 1`, so that `∑ tᵢ tⱼ |⟨uᵢ, uⱼ⟩| = ∑ wᵢ wⱼ rᵢⱼ` and `S = ∑ wᵢ`. As in [DL26]
we use the inequality `(1 + φ)² (r - φ)² ≥ (r² - φ²)²` for `0 ≤ r ≤ 1`, here with `φ = 1/s` and
in the polynomial form
`2s(s+1)² r ≤ s²((s+1)² + 2) r² + (s+1)² - 1 - s⁴ r⁴`.
Summing with the weights `wᵢ wⱼ`, and using the Sidelnikov–Welch inequality `c X₂ ≤ s² X₄`
(`c = 3`, `s² = m + 2` over `ℝ`, `welch_real`; `c = 2`, `s² = m + 1` over `ℂ`, `welch_complex`)
and `X₂ = ∑ wᵢ wⱼ rᵢⱼ² ≤ 1` (by the AM-GM inequality and the Parseval identity
`∑ⱼ ‖uⱼ‖² |⟨xᵢ, xⱼ⟩|² = ‖xᵢ‖² = 1`, see `sum_norm_sq_conj_mul`), gives `frame_estimate`.

## References

* [DL26] B. Deręgowska, B. Lewandowska, *From Sidelnikov–Welch bounds to projection constants*,
  arXiv:2609.29422.

## Tags

Parseval frame, Sidelnikov–Welch bound, projection constant
-/

open Finset Matrix ComplexConjugate

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {m : ℕ}

/-- The Euclidean norm `‖uᵢ‖` of the `i`-th column of `U`. -/
noncomputable def colNorm (U : Matrix (Fin m) ι 𝕜) (i : ι) : ℝ := √(∑ k, ‖U k i‖ ^ 2)

/-- `‖uᵢ‖ ≥ 0`. -/
lemma colNorm_nonneg (U : Matrix (Fin m) ι 𝕜) (i : ι) : 0 ≤ colNorm U i := Real.sqrt_nonneg _

/-- `‖uᵢ‖² = ∑ₖ |Uₖᵢ|²`. -/
lemma colNorm_sq (U : Matrix (Fin m) ι 𝕜) (i : ι) : colNorm U i ^ 2 = ∑ k, ‖U k i‖ ^ 2 :=
  Real.sq_sqrt (sum_nonneg fun _ _ ↦ sq_nonneg _)

variable [Fintype ι]

omit [Fintype ι] in
/-- `Re (Uᴴ U)ᵢᵢ = ‖uᵢ‖²`. -/
lemma re_gram_diag (U : Matrix (Fin m) ι 𝕜) (i : ι) :
    RCLike.re ((Uᴴ * U) i i) = colNorm U i ^ 2 := by
  rw [colNorm_sq, Matrix.mul_apply, map_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow,
    RCLike.ofReal_re]

omit [Fintype ι] in
/-- Every column of `U` is `‖uᵢ‖ xᵢ` for a unit vector `xᵢ`. -/
lemma exists_unit_columns (hm : 1 ≤ m) (U : Matrix (Fin m) ι 𝕜) :
    ∃ x : ι → Fin m → 𝕜, (∀ i, ∑ k, ‖x i k‖ ^ 2 = 1) ∧
      ∀ k i, U k i = (colNorm U i : 𝕜) * x i k := by
  classical
  let k₀ : Fin m := ⟨0, hm⟩
  refine ⟨fun i k ↦ if colNorm U i = 0 then (if k = k₀ then 1 else 0)
    else U k i / (colNorm U i : 𝕜), fun i ↦ ?_, fun k i ↦ ?_⟩
  · by_cases h : colNorm U i = 0
    · simp [h, apply_ite]
    · have h' : (colNorm U i : 𝕜) ≠ 0 := by exact_mod_cast h
      simp only [h, ite_false, norm_div, RCLike.norm_ofReal, abs_of_nonneg (colNorm_nonneg U i),
        div_pow]
      rw [← Finset.sum_div, ← colNorm_sq, div_self (pow_ne_zero 2 h)]
  · by_cases h : colNorm U i = 0
    · have h0 : ∑ l, ‖U l i‖ ^ 2 = 0 := by rw [← colNorm_sq, h]; ring
      have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ ↦ sq_nonneg ‖U l i‖)).1 h0 k
        (mem_univ k)
      have : U k i = 0 := by simpa using hk
      simp [h, this]
    · have h' : (colNorm U i : 𝕜) ≠ 0 := by exact_mod_cast h
      simp only [h, ite_false]
      field_simp

/-- Parseval: if `U Uᴴ = 1`, then `∑ⱼ |⟨y, uⱼ⟩|² = ‖y‖²`. -/
lemma sum_norm_sq_conj_mul {U : Matrix (Fin m) ι 𝕜} (hU : U * Uᴴ = 1) (y : Fin m → 𝕜) :
    ∑ j, ‖∑ k, conj (y k) * U k j‖ ^ 2 = ∑ k, ‖y k‖ ^ 2 := by
  apply RCLike.ofReal_injective (K := 𝕜)
  push_cast
  simp only [← RCLike.mul_conj]
  have hUU : ∀ k l, ∑ j, U k j * conj (U l j) = if k = l then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hU k) l
    simpa [Matrix.mul_apply, Matrix.one_apply, RCLike.star_def] using this
  calc ∑ j, (∑ k, conj (y k) * U k j) * conj (∑ k, conj (y k) * U k j)
      = ∑ j, ∑ k, ∑ l, conj (y k) * y l * (U k j * conj (U l j)) := by
        refine sum_congr rfl fun j _ ↦ ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
        simp only [map_mul, RCLike.conj_conj]
        ring
    _ = ∑ k, ∑ l, conj (y k) * y l * ∑ j, U k j * conj (U l j) := by
        rw [Fintype.sum_comm_cycle]
        simp only [Finset.mul_sum]
    _ = ∑ k, y k * conj (y k) := by
        simp only [hUU, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true]
        exact sum_congr rfl fun k _ ↦ mul_comm _ _

/-- The elementary inequality behind [DL26, Lemma 3.1]: for `0 ≤ r ≤ 1` and `s ≥ 0`,
`2s(s+1)² r ≤ s²((s+1)² + 2) r² + (s+1)² - 1 - s⁴ r⁴`; the difference is
`(sr - 1)² s (1 - r)(s + sr + 2)`. -/
private lemma pair_ineq {r s : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) :
    2 * s * (s + 1) ^ 2 * r ≤
      s ^ 2 * ((s + 1) ^ 2 + 2) * r ^ 2 + ((s + 1) ^ 2 - 1) - s ^ 4 * r ^ 4 := by
  have h : 0 ≤ (s * r - 1) ^ 2 * s * ((1 - r) * (s + s * r + 2)) := by
    have : 0 ≤ 1 - r := by linarith
    positivity
  nlinarith [h]

/-- **The frame bound, general form** (cf. [DL26, Lemma 3.1]). Let `U Uᴴ = 1` with columns
`uᵢ ∈ 𝕜^m`, `t ≥ 0` with `‖t‖ ≤ 1`, and suppose that the unit vectors of `𝕜^m` satisfy the
Sidelnikov–Welch type inequality `c X₂ ≤ s² X₄` (with `c ≤ (s+1)² + 2`). Then, with
`F = ∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩|` and `S = ∑ᵢ tᵢ ‖uᵢ‖`,
`2s(s+1)² F ≤ s²((s+1)² + 2 - c) + ((s+1)² - 1) S²`. -/
theorem frame_estimate (hm : 1 ≤ m) {U : Matrix (Fin m) ι 𝕜} (hU : U * Uᴴ = 1) {t : ι → ℝ}
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i ^ 2 ≤ 1) {s c : ℝ} (hs : 0 ≤ s)
    (hc : c ≤ (s + 1) ^ 2 + 2)
    (hW : ∀ x : ι → Fin m → 𝕜, (∀ i, ∑ a, ‖x i a‖ ^ 2 = 1) → ∀ w : ι → ℝ,
      c * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ 2 ≤
        s ^ 2 * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ 4) :
    2 * s * (s + 1) ^ 2 * ∑ i, ∑ j, t i * t j * ‖(Uᴴ * U) i j‖ ≤
      s ^ 2 * ((s + 1) ^ 2 + 2 - c) + ((s + 1) ^ 2 - 1) * (∑ i, t i * colNorm U i) ^ 2 := by
  obtain ⟨x, hx1, hUx⟩ := exists_unit_columns hm U
  set n := colNorm U with hn
  have hn0 : ∀ i, 0 ≤ n i := colNorm_nonneg U
  set r : ι → ι → ℝ := fun i j ↦ ‖∑ a, conj (x i a) * x j a‖ with hr
  set w : ι → ℝ := fun i ↦ t i * n i with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i ↦ mul_nonneg (ht0 i) (hn0 i)
  -- the Gram matrix in terms of the unit vectors
  have hgram : ∀ i j, ‖(Uᴴ * U) i j‖ = n i * n j * r i j := by
    intro i j
    have e : (Uᴴ * U) i j = (n i : 𝕜) * n j * ∑ a, conj (x i a) * x j a := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, hUx, map_mul,
        RCLike.conj_ofReal, Finset.mul_sum]
      exact sum_congr rfl fun a _ ↦ by ring
    rw [e, norm_mul, norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg (hn0 i),
      abs_of_nonneg (hn0 j)]
  -- `|⟨xᵢ, xⱼ⟩| ≤ 1`
  have hr0 : ∀ i j, 0 ≤ r i j := fun _ _ ↦ norm_nonneg _
  have hr1 : ∀ i j, r i j ≤ 1 := by
    intro i j
    have h1 : r i j ≤ ∑ a, ‖x i a‖ * ‖x j a‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 : (∑ a, ‖x i a‖ * ‖x j a‖) ^ 2 ≤ (∑ a, ‖x i a‖ ^ 2) * ∑ a, ‖x j a‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    rw [hx1 i, hx1 j, one_mul] at h2
    have h3 : 0 ≤ ∑ a, ‖x i a‖ * ‖x j a‖ := sum_nonneg fun _ _ ↦ by positivity
    nlinarith
  have hrsymm : ∀ i j, r i j = r j i := by
    intro i j
    simp only [hr]
    rw [← norm_star, star_sum]
    congr 1
    refine sum_congr rfl fun a _ ↦ ?_
    simp [RCLike.star_def, mul_comm]
  -- Parseval: `∑ⱼ ‖uⱼ‖² |⟨xᵢ, xⱼ⟩|² = 1`
  have hpars : ∀ i, ∑ j, (n j * r i j) ^ 2 = 1 := by
    intro i
    rw [← hx1 i, ← sum_norm_sq_conj_mul hU (x i)]
    refine sum_congr rfl fun j _ ↦ ?_
    have e : ∑ k, conj (x i k) * U k j = (n j : 𝕜) * ∑ a, conj (x i a) * x j a := by
      rw [Finset.mul_sum]
      exact sum_congr rfl fun k _ ↦ by rw [hUx k j]; ring
    rw [e, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (hn0 j)]
  -- `X₂ ≤ 1`
  have hX2 : ∑ i, ∑ j, w i * w j * r i j ^ 2 ≤ 1 := by
    have hamgm : ∀ i j, 2 * (w i * w j * r i j ^ 2) ≤
        t i ^ 2 * (n j * r i j) ^ 2 + t j ^ 2 * (n i * r j i) ^ 2 := by
      intro i j
      rw [hrsymm j i]
      nlinarith [sq_nonneg (t i * n j * r i j - t j * n i * r i j)]
    have h1 : ∑ i, ∑ j, t i ^ 2 * (n j * r i j) ^ 2 ≤ 1 := by
      simp only [← Finset.mul_sum, hpars, mul_one]
      exact ht1
    have h2 : ∑ i, ∑ j, t j ^ 2 * (n i * r j i) ^ 2 ≤ 1 := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hpars, mul_one]
      exact ht1
    have h3 : ∑ i, ∑ j, 2 * (w i * w j * r i j ^ 2) ≤
        ∑ i, ∑ j, t i ^ 2 * (n j * r i j) ^ 2 + ∑ i, ∑ j, t j ^ 2 * (n i * r j i) ^ 2 := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun i _ ↦ by
        rw [← sum_add_distrib]; exact sum_le_sum fun j _ ↦ hamgm i j
    have h4 : ∑ i, ∑ j, 2 * (w i * w j * r i j ^ 2) = 2 * ∑ i, ∑ j, w i * w j * r i j ^ 2 := by
      rw [Finset.mul_sum]
      exact sum_congr rfl fun i _ ↦ by rw [Finset.mul_sum]
    linarith
  -- `F = ∑ wᵢ wⱼ rᵢⱼ` and `S² = ∑ wᵢ wⱼ`
  have hF : ∑ i, ∑ j, t i * t j * ‖(Uᴴ * U) i j‖ = ∑ i, ∑ j, w i * w j * r i j :=
    sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by rw [hgram]; ring
  have hS : (∑ i, t i * n i) ^ 2 = ∑ i, w i * ∑ j, w j := by
    rw [sq, Finset.sum_mul]
  -- summing the elementary inequality
  have hpair := sum_le_sum fun i (_ : i ∈ univ) ↦ sum_le_sum fun j (_ : j ∈ univ) ↦
    mul_le_mul_of_nonneg_left (pair_ineq (hr0 i j) (hr1 i j) hs)
      (mul_nonneg (hw0 i) (hw0 j))
  have e1 : ∀ i j, w i * w j * (2 * s * (s + 1) ^ 2 * r i j) =
      2 * s * (s + 1) ^ 2 * (w i * w j * r i j) := fun i j ↦ by ring
  have e2 : ∀ i j, w i * w j * (s ^ 2 * ((s + 1) ^ 2 + 2) * r i j ^ 2 + ((s + 1) ^ 2 - 1) -
      s ^ 4 * r i j ^ 4) = s ^ 2 * ((s + 1) ^ 2 + 2) * (w i * w j * r i j ^ 2) +
        ((s + 1) ^ 2 - 1) * (w i * w j) - s ^ 4 * (w i * w j * r i j ^ 4) := fun i j ↦ by ring
  simp only [e1, e2, sum_add_distrib, sum_sub_distrib, ← Finset.mul_sum] at hpair
  -- the Sidelnikov–Welch inequality
  have hWx := hW x hx1 w
  have hWx' : s ^ 2 * (c * ∑ i, ∑ j, w i * w j * r i j ^ 2) ≤
      s ^ 2 * (s ^ 2 * ∑ i, ∑ j, w i * w j * r i j ^ 4) :=
    mul_le_mul_of_nonneg_left hWx (sq_nonneg s)
  have hcoef : 0 ≤ s ^ 2 * ((s + 1) ^ 2 + 2 - c) := mul_nonneg (sq_nonneg s) (by linarith)
  have hX2' := mul_le_mul_of_nonneg_left hX2 hcoef
  rw [hF, hS]
  linarith

/-! ### The real and the complex case -/

/-- **The frame bound, real case** ([DL26, Lemma 3.1], with `s = √(m+2)`):
`2 (s+1)² ∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩| ≤ (s + 2)(m + 2 + (∑ᵢ tᵢ ‖uᵢ‖)²)`. -/
theorem frame_bound_real (hm : 1 ≤ m) {U : Matrix (Fin m) ι ℝ} (hU : U * Uᴴ = 1) {t : ι → ℝ}
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i ^ 2 ≤ 1) :
    2 * (√(m + 2) + 1) ^ 2 * weightedAbsSum t (Uᴴ * U) ≤
      (√(m + 2) + 2) * (m + 2 + (∑ i, t i * colNorm U i) ^ 2) := by
  set s := √((m : ℝ) + 2) with hs
  have hs2 : s ^ 2 = m + 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hW : ∀ x : ι → Fin m → ℝ, (∀ i, ∑ a, ‖x i a‖ ^ 2 = 1) → ∀ w : ι → ℝ,
      3 * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ 2 ≤
        s ^ 2 * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ 4 := by
    intro x hx w
    have hx' : ∀ i, ∑ a, x i a ^ 2 = 1 := fun i ↦ by simpa [Real.norm_eq_abs, sq_abs] using hx i
    have e2 : ∀ i j, ‖∑ a, conj (x i a) * x j a‖ ^ 2 = (∑ a, x i a * x j a) ^ 2 := by
      intro i j
      simp [Real.norm_eq_abs, sq_abs]
    have e4 : ∀ i j, ‖∑ a, conj (x i a) * x j a‖ ^ 4 = (∑ a, x i a * x j a) ^ 4 := by
      intro i j
      simp [Real.norm_eq_abs, Even.pow_abs (show Even 4 by decide)]
    simp only [e2, e4, hs2]
    exact welch_real x hx' w
  have h := frame_estimate hm hU ht0 ht1 hs0.le (by nlinarith) hW
  rw [hs2] at h
  have key : s * (2 * (s + 1) ^ 2 * weightedAbsSum t (Uᴴ * U)) ≤
      s * ((s + 2) * (m + 2 + (∑ i, t i * colNorm U i) ^ 2)) := by
    unfold weightedAbsSum
    linarith [h]
  exact le_of_mul_le_mul_left key hs0

/-- **The frame bound, complex case** ([DL26, Lemma 3.1], with `s = √(m+1)`, for any `RCLike`
field): `2 (s+1)² ∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩| ≤ s (s+1)² + (s + 2)(∑ᵢ tᵢ ‖uᵢ‖)²`. -/
theorem frame_bound_complex (hm : 1 ≤ m) {U : Matrix (Fin m) ι 𝕜} (hU : U * Uᴴ = 1)
    {t : ι → ℝ} (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i ^ 2 ≤ 1) :
    2 * (√(m + 1) + 1) ^ 2 * weightedAbsSum t (Uᴴ * U) ≤
      √(m + 1) * (√(m + 1) + 1) ^ 2 + (√(m + 1) + 2) * (∑ i, t i * colNorm U i) ^ 2 := by
  set s := √((m : ℝ) + 1) with hs
  have hs2 : s ^ 2 = m + 1 := Real.sq_sqrt (by positivity)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hW : ∀ x : ι → Fin m → 𝕜, (∀ i, ∑ a, ‖x i a‖ ^ 2 = 1) → ∀ w : ι → ℝ,
      2 * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ 2 ≤
        s ^ 2 * ∑ i, ∑ j, w i * w j * ‖∑ a, conj (x i a) * x j a‖ ^ 4 := by
    intro x hx w
    rw [hs2]
    exact welch_complex x hx w
  have h := frame_estimate hm hU ht0 ht1 hs0.le (by nlinarith) hW
  have key : s * (2 * (s + 1) ^ 2 * weightedAbsSum t (Uᴴ * U)) ≤
      s * (s * (s + 1) ^ 2 + (s + 2) * (∑ i, t i * colNorm U i) ^ 2) := by
    unfold weightedAbsSum
    linarith [h]
  exact le_of_mul_le_mul_left key hs0

/-- **The frame bound, real case**, in the form of [DL26, Lemma 3.1]: if `U ∈ ℝ^{m×N}`,
`U Uᵀ = I`, and `t ≥ 0` with `‖t‖₂ ≤ 1`, then
`∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩| ≤ (2 + (m-1)√(m+2)) / (2(m+1)²) · (m + 2 + (∑ᵢ tᵢ ‖uᵢ‖)²)`. -/
theorem weightedAbsSum_gram_le_real (hm : 1 ≤ m) {U : Matrix (Fin m) ι ℝ} (hU : U * Uᴴ = 1)
    {t : ι → ℝ} (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i ^ 2 ≤ 1) :
    weightedAbsSum t (Uᴴ * U) ≤ (2 + (m - 1) * √(m + 2)) / (2 * (m + 1) ^ 2) *
      (m + 2 + (∑ i, t i * colNorm U i) ^ 2) := by
  have h := frame_bound_real hm hU ht0 ht1
  set s := √((m : ℝ) + 2) with hs
  have hs2 : s ^ 2 = m + 2 := Real.sq_sqrt (by positivity)
  have hm' : (m : ℝ) = s ^ 2 - 2 := by linarith
  have h' := mul_le_mul_of_nonneg_left h (sq_nonneg (s - 1))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  rw [hm'] at h' ⊢
  linarith [h']

/-- **The frame bound, complex case**, in the form of [DL26, Lemma 3.1]: if `U ∈ ℂ^{m×N}`,
`U U* = I`, and `t ≥ 0` with `‖t‖₂ ≤ 1`, then
`∑ᵢⱼ tᵢ tⱼ |⟨uᵢ, uⱼ⟩| ≤ √(m+1)/2 + (1 + (m/2 - 1)√(m+1)) / m² · (∑ᵢ tᵢ ‖uᵢ‖)²`. -/
theorem weightedAbsSum_gram_le_complex (hm : 1 ≤ m) {U : Matrix (Fin m) ι 𝕜}
    (hU : U * Uᴴ = 1) {t : ι → ℝ} (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i ^ 2 ≤ 1) :
    weightedAbsSum t (Uᴴ * U) ≤ √(m + 1) / 2 +
      (1 + (m / 2 - 1) * √(m + 1)) / m ^ 2 * (∑ i, t i * colNorm U i) ^ 2 := by
  have h := frame_bound_complex hm hU ht0 ht1
  set s := √((m : ℝ) + 1) with hs
  have hs2 : s ^ 2 = m + 1 := Real.sq_sqrt (by positivity)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm' : (m : ℝ) = s ^ 2 - 1 := by linarith
  have h' := mul_le_mul_of_nonneg_left h (sq_nonneg (s - 1))
  rw [div_mul_eq_mul_div, div_add_div _ _ (two_ne_zero' ℝ) (by positivity),
    le_div_iff₀ (by positivity)]
  rw [hm']
  linarith [h']

end ProjectionConstants
