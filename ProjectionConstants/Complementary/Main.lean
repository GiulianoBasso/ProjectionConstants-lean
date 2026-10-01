/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Bounds.FrameBound
import ProjectionConstants.Complementary.Complement
import ProjectionConstants.Values
import ProjectionConstants.FourSix.Main

/-!
# Maximal relative projection constants in complementary dimensions

We prove [DL26, Theorem 3.1]: let `m ≥ 2` and suppose that `𝕂^m` admits a maximal equiangular
tight frame, i.e. an `ETF(m, M)` with `M = M_ℝ = m(m+1)/2`, resp. `M = M_ℂ = m²`. Then for every
`k ≥ 1`,
`λ_𝕂(kM - m, kM) = λ_𝕂(m) - 2m/(kM) + 1`,
and the maximum is attained with equal weights, `μ_𝕂(kM - m, kM) = λ_𝕂(kM - m, kM)`. The formula
also holds for `m = 1` (`M = 1`), where it reads `λ_𝕂(N - 1, N) = 2 - 2/N`.

With the maximal ETFs of `ProjectionConstants.ETF.Maximal.Certificates` and
`ProjectionConstants.ETF.Maximal.Seidel` this gives
`λ_ℝ(3k-2, 3k) = 7/3 - 4/(3k)`, `λ_ℝ(6k-3, 6k) = (3+√5)/2 - 1/k`,
`λ_ℝ(28k-7, 28k) = 7/2 - 1/(2k)`, `λ_ℝ(276k-23, 276k) = 17/3 - 1/(6k)`,
`λ_ℂ(4k-2, 4k) = (3+√3)/2 - 1/k` and `λ_ℂ(9k-3, 9k) = 8/3 - 2/(3k)`.

## Main statements

* `maxRelProjConst_compl_real`, `maxRelProjConst_compl_complex`: the formula
  `λ_𝕂(kM - m, kM) = λ_𝕂(m) - 2m/(kM) + 1` [DL26, Theorem 3.1].
* `quasiRelConst_compl_real`, `quasiRelConst_compl_complex`: the same formula for
  `μ_𝕂(kM - m, kM)`, i.e. the maximum is attained with equal weights.
* `clConst_compl_le_real`, `clConst_compl_le_complex`: the upper bound
  `λ_𝕂(N - m, N) ≤ δ_{m,M} + 1 - 2m/N` under a numerical condition on `N`.
* `delta_compl`: `δ_{M-m,M} = δ_{m,M} + 1 - 2m/M`.
* `maxRelProjConst_hyperplane`: `λ_𝕂(N - 1, N) = 2 - 2/N`, the case `m = 1`.
* `maxRelProjConst_compl_real_two`, `maxRelProjConst_compl_real_three`,
  `maxRelProjConst_compl_real_seven`, `maxRelProjConst_compl_real_twentyThree`,
  `maxRelProjConst_compl_complex_two`, `maxRelProjConst_compl_complex_three`: the explicit
  values above.

## Proof sketch

* **Upper bound.** For an orthogonal projection `P` of rank `N - m` write `1 - P = U* U` with
  `U U* = I_m` (`exists_compl_frame`). Then
  `∑ tᵢ tⱼ |Pᵢⱼ| = 1 - 2 ∑ tᵢ² ‖uᵢ‖² + ∑ tᵢ tⱼ |⟨uᵢ, uⱼ⟩|`, and [DL26, Lemma 3.1] together with
  `S² ≤ m` and `S² ≤ N ∑ tᵢ² ‖uᵢ‖²` (Cauchy–Schwarz, `S = ∑ tᵢ ‖uᵢ‖`) gives
  `λ_𝕂(N - m, N) ≤ δ_{m,M} + 1 - 2m/N` whenever `4(s+1)² ≤ (s+2)N`, where `s = √(m+2)`,
  resp. `s = √(m+1)` (`clConst_compl_le_real`, `clConst_compl_le_complex`).
* **Lower bound.** `quasiRelConst_add_le_clConst` (`ProjectionConstants.Complementary.Complement`)
  and `μ_𝕂(m, M) = δ_{m,M} = λ_𝕂(m)` for maximal ETFs ([DL, Theorem 1.2], [DL, Theorem 2.3]).
* **Small cases.** For `k ≥ 2` the condition `4(s+1)² ≤ (s+2)kM` holds except for
  `(m, k) = (2, 2)` in the real case, which is `λ_ℝ(4, 6) = 5/3` ([JFA, §4.4], [JFA-E];
  `maxRelProjConst_four_six`). For `k = 1` we use the bound `λ_𝕂(M - m, M) ≤ δ_{M-m,M}` of König,
  Lewis and Lin and the identity `δ_{M-m,M} = δ_{m,M} + 1 - 2m/M` (`delta_compl`). [DL26] treats
  `k = 1` through the values `λ_ℝ(1, 3) = 1`, `λ_ℝ(3, 6) = λ_ℝ(3)` and `λ_ℂ(2, 4) = λ_ℂ(2)`, using
  that real maximal ETFs can only exist in the dimensions `2`, `3` and `(2j+1)² - 2`; the argument
  via `δ_{M-m,M}` needs no such information (in particular no separate treatment of `m = 4`).
* **Hyperplanes.** For `m = 1` both bounds come from the simplex `ETF(N - 1, N)`.

[DL26] also shows that for `k ≥ 2` the extremal frame is biangular; this is not formalized.

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
* [DL26] B. Deręgowska, B. Lewandowska, *From Sidelnikov–Welch bounds to projection constants*,
  arXiv:2609.29422.
* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.

## Tags

projection constant, complementary dimension, equiangular tight frame
-/

open Finset Matrix

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Passing to the complementary projection `Q = 1 - P = Uᴴ U`:
`∑ tᵢ tⱼ |Pᵢⱼ| = 1 - 2 ∑ tᵢ² ‖uᵢ‖² + ∑ tᵢ tⱼ |⟨uᵢ, uⱼ⟩|`, together with the two Cauchy–Schwarz
estimates `(∑ tᵢ ‖uᵢ‖)² ≤ m` and `(∑ tᵢ ‖uᵢ‖)² ≤ N ∑ tᵢ² ‖uᵢ‖²`. -/
lemma exists_compl_frame {m N : ℕ} (hmN : m ≤ N) {t : Fin N → ℝ} (ht : IsUnitWeight t)
    {P : Matrix (Fin N) (Fin N) 𝕜} (hP : P ∈ orthProjs 𝕜 (Fin N) (N - m)) :
    ∃ U : Matrix (Fin m) (Fin N) 𝕜, U * Uᴴ = 1 ∧
      weightedAbsSum t P =
        1 - 2 * ∑ i, t i ^ 2 * colNorm U i ^ 2 + weightedAbsSum t (Uᴴ * U) ∧
      (∑ i, t i * colNorm U i) ^ 2 ≤ m ∧
      (∑ i, t i * colNorm U i) ^ 2 ≤ N * ∑ i, t i ^ 2 * colNorm U i ^ 2 := by
  have hQ : 1 - P ∈ orthProjs 𝕜 (Fin N) m := by
    have := one_sub_mem_orthProjs hP
    rwa [Fintype.card_fin, Nat.sub_sub_self hmN] at this
  obtain ⟨U, hU, hUQ⟩ := exists_parseval_of_mem_orthProjs hQ
  have hn : ∑ i, colNorm U i ^ 2 = m := by
    rw [← sum_re_diag (conjTranspose_mul_self_mem_orthProjs hU)]
    exact sum_congr rfl fun i _ ↦ (re_gram_diag U i).symm
  refine ⟨U, hU, ?_, ?_, ?_⟩
  · have hPQ : P = 1 - (1 - P) := (sub_sub_cancel 1 P).symm
    rw [hPQ, weightedAbsSum_one_sub t hQ.1, ht.sum_sq, ← hUQ]
    simp only [re_gram_diag]
  · have h := Finset.sum_mul_sq_le_sq_mul_sq univ t (colNorm U)
    rwa [ht.sum_sq, hn, one_mul] at h
  · have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ ↦ (1 : ℝ)) (fun i ↦ t i * colNorm U i)
    simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, mul_pow] at h
    exact h

/-! ### The upper bounds -/

/-- `2/(m+1) (1 + (m-1)/2 √(m+2)) = (s + 2)(m + 1)/(s + 1)²` for `s = √(m+2)`. -/
lemma bukhCoxReal_eq {m : ℕ} :
    bukhCoxReal m = (√(m + 2) + 2) * (m + 1) / (√(m + 2) + 1) ^ 2 := by
  rw [bukhCoxReal]
  have hs2 : √((m : ℝ) + 2) ^ 2 = m + 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ √((m : ℝ) + 2) := Real.sqrt_nonneg _
  generalize √((m : ℝ) + 2) = s at hs2 hs0 ⊢
  have hm' : (m : ℝ) = s ^ 2 - 2 := by linarith
  rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity), hm']
  ring

/-- `1/m (1 + (m-1) √(m+1)) = (s (s+1)² + m (s + 2))/(2 (s+1)²)` for `s = √(m+1)`. -/
lemma bukhCoxComplex_eq {m : ℕ} (hm : 1 ≤ m) :
    bukhCoxComplex m = (√(m + 1) * (√(m + 1) + 1) ^ 2 + m * (√(m + 1) + 2)) /
      (2 * (√(m + 1) + 1) ^ 2) := by
  rw [bukhCoxComplex]
  have hs2 : √((m : ℝ) + 1) ^ 2 = m + 1 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ √((m : ℝ) + 1) := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  generalize √((m : ℝ) + 1) = s at hs2 hs0 ⊢
  have hm' : (m : ℝ) = s ^ 2 - 1 := by linarith
  rw [one_div_mul_eq_div, div_eq_div_iff hm0.ne' (by positivity), hm']
  ring

/-- `1 ≤ 2/(m+1) (1 + (m-1)/2 √(m+2))` for `m ≥ 1`. -/
lemma one_le_bukhCoxReal {m : ℕ} (hm : 1 ≤ m) : 1 ≤ bukhCoxReal m := by
  have hs1 : 1 ≤ √((m : ℝ) + 2) := by
    rw [Real.one_le_sqrt]; have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [bukhCoxReal, ← sub_nonneg]
  have e : 2 / ((m : ℝ) + 1) * (1 + (m - 1) / 2 * √(m + 2)) - 1 =
      (m - 1) * (√(m + 2) - 1) / (m + 1) := by
    field_simp
    ring
  rw [e]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)

/-- `1 ≤ 1/m (1 + (m-1) √(m+1))` for `m ≥ 1`. -/
lemma one_le_bukhCoxComplex {m : ℕ} (hm : 1 ≤ m) : 1 ≤ bukhCoxComplex m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs1 : 1 ≤ √((m : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; linarith
  rw [bukhCoxComplex, ← sub_nonneg]
  have e : 1 / (m : ℝ) * (1 + (m - 1) * √(m + 1)) - 1 = (m - 1) * (√(m + 1) - 1) / m := by
    field_simp
    ring
  rw [e]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)

/-- **The upper bound of [DL26, Theorem 3.1], real case.** If `4 (s+1)² ≤ (s+2) N` for
`s = √(m+2)`, then `λ_ℝ(N - m, N) ≤ 2/(m+1) (1 + (m-1)/2 √(m+2)) + 1 - 2m/N`. -/
theorem clConst_compl_le_real {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hN : 4 * (√(m + 2) + 1) ^ 2 ≤ (√(m + 2) + 2) * N) :
    clConst ℝ (Fin N) (N - m) ≤ bukhCoxReal m + 1 - 2 * m / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hc0 : 0 ≤ bukhCoxReal m + 1 - 2 * m / N := by
    have := one_le_bukhCoxReal hm
    have : 2 * (m : ℝ) / N ≤ 2 := by rw [div_le_iff₀ hN0]; linarith
    linarith
  refine clConst_le hc0 fun t P ht hP ↦ ?_
  obtain ⟨U, hU, heq, hSm, hSN⟩ := exists_compl_frame hmN ht hP
  have hF := frame_bound_real (by omega) hU ht.nonneg ht.sum_sq.le
  rw [heq, bukhCoxReal_eq]
  set s := √((m : ℝ) + 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set F := weightedAbsSum t (Uᴴ * U)
  set S := ∑ i, t i * colNorm U i
  set D := ∑ i, t i ^ 2 * colNorm U i ^ 2
  have key : (2 * (s + 1) ^ 2 * N) * (1 - 2 * D + F) ≤
      (2 * (s + 1) ^ 2 * N) * ((s + 2) * (m + 1) / (s + 1) ^ 2 + 1 - 2 * m / N) := by
    have e : (2 * (s + 1) ^ 2 * N) * ((s + 2) * (m + 1) / (s + 1) ^ 2 + 1 - 2 * m / N) =
        2 * (s + 2) * (m + 1) * N + 2 * (s + 1) ^ 2 * N - 4 * (s + 1) ^ 2 * m := by
      field_simp
      ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left hF hN0.le
    have h2 := mul_le_mul_of_nonneg_left hSN (show 0 ≤ 4 * (s + 1) ^ 2 by positivity)
    have h3 : 0 ≤ (m - S ^ 2) * ((s + 2) * N - 4 * (s + 1) ^ 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h1, h2, h3]
  exact le_of_mul_le_mul_left key (by positivity)

/-- **The upper bound of [DL26, Theorem 3.1], complex case.** If `4 (s+1)² ≤ (s+2) N` for
`s = √(m+1)`, then `λ_𝕜(N - m, N) ≤ 1/m (1 + (m-1) √(m+1)) + 1 - 2m/N`. -/
theorem clConst_compl_le_complex {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hN : 4 * (√(m + 1) + 1) ^ 2 ≤ (√(m + 1) + 2) * N) :
    clConst 𝕜 (Fin N) (N - m) ≤ bukhCoxComplex m + 1 - 2 * m / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hc0 : 0 ≤ bukhCoxComplex m + 1 - 2 * m / N := by
    have := one_le_bukhCoxComplex hm
    have : 2 * (m : ℝ) / N ≤ 2 := by rw [div_le_iff₀ hN0]; linarith
    linarith
  refine clConst_le hc0 fun t P ht hP ↦ ?_
  obtain ⟨U, hU, heq, hSm, hSN⟩ := exists_compl_frame hmN ht hP
  have hF := frame_bound_complex (by omega) hU ht.nonneg ht.sum_sq.le
  rw [heq, bukhCoxComplex_eq hm]
  set s := √((m : ℝ) + 1)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set F := weightedAbsSum t (Uᴴ * U)
  set S := ∑ i, t i * colNorm U i
  set D := ∑ i, t i ^ 2 * colNorm U i ^ 2
  have key : (2 * (s + 1) ^ 2 * N) * (1 - 2 * D + F) ≤ (2 * (s + 1) ^ 2 * N) *
      ((s * (s + 1) ^ 2 + m * (s + 2)) / (2 * (s + 1) ^ 2) + 1 - 2 * m / N) := by
    have e : (2 * (s + 1) ^ 2 * N) *
        ((s * (s + 1) ^ 2 + m * (s + 2)) / (2 * (s + 1) ^ 2) + 1 - 2 * m / N) =
        (s * (s + 1) ^ 2 + m * (s + 2)) * N + 2 * (s + 1) ^ 2 * N - 4 * (s + 1) ^ 2 * m := by
      field_simp
      ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left hF hN0.le
    have h2 := mul_le_mul_of_nonneg_left hSN (show 0 ≤ 4 * (s + 1) ^ 2 by positivity)
    have h3 : 0 ≤ (m - S ^ 2) * ((s + 2) * N - 4 * (s + 1) ^ 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h1, h2, h3]
  exact le_of_mul_le_mul_left key (by positivity)

/-! ### The case `k = 1`: the bound of König, Lewis and Lin -/

private lemma mul_sqrt_div {a : ℝ} (ha : 0 ≤ a) (b : ℝ) : a * √(b / a) = √(a * b) := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  · rw [show a * b = a ^ 2 * (b / a) by field_simp, Real.sqrt_mul (sq_nonneg a),
      Real.sqrt_sq ha]

/-- `δ_{M-m, M} = δ_{m, M} + 1 - 2m/M`. -/
lemma delta_compl {m M : ℕ} (hm : 1 ≤ m) (hmM : m < M) :
    delta (M - m) M = delta m M + 1 - 2 * m / M := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hMm : (0 : ℝ) < M - m := by
    have : (m : ℝ) < M := by exact_mod_cast hmM
    linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hM0 : (0 : ℝ) < M := by linarith
  rw [delta, delta, Nat.cast_sub hmM.le]
  have h1 : ((M : ℝ) - m) / M * (1 + √((M - 1) * (M - (M - m)) / (M - m))) =
      ((M : ℝ) - m) / M + √(m * (M - 1) * (M - m)) / M := by
    rw [mul_add, mul_one, div_mul_eq_mul_div, show (M : ℝ) - (M - m) = m by ring,
      mul_sqrt_div hMm.le, show ((M : ℝ) - m) * ((M - 1) * m) =
        m * (M - 1) * (M - m) by ring]
  have h2 : (m : ℝ) / M * (1 + √((M - 1) * (M - m) / m)) =
      (m : ℝ) / M + √(m * (M - 1) * (M - m)) / M := by
    rw [mul_add, mul_one, div_mul_eq_mul_div, mul_sqrt_div hm0.le,
      show (m : ℝ) * ((M - 1) * (M - m)) = m * (M - 1) * (M - m) by ring]
  rw [h1, h2]
  field_simp
  ring

/-! ### The numerical conditions -/

private lemma cond_real {m k M : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) (h22 : ¬(m = 2 ∧ k = 2))
    (hM : 2 * M = m * (m + 1)) :
    4 * (√(m + 2) + 1) ^ 2 ≤ (√(m + 2) + 2) * ((k * M : ℕ) : ℝ) := by
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · obtain rfl : m = 2 := by omega
    have hk3 : 3 ≤ k := by omega
    obtain rfl : M = 3 := by omega
    have hs : √(((2 : ℕ) : ℝ) + 2) = 2 := by
      rw [show ((2 : ℕ) : ℝ) + 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    rw [hs]
    push_cast
    nlinarith
  · have h2M : 2 * M ≤ k * M := Nat.mul_le_mul_right M hk
    have hN1 : 2 * m + 6 ≤ k * M := by nlinarith
    have hN2 : 8 ≤ k * M := by nlinarith
    have hs2 : √((m : ℝ) + 2) ^ 2 = m + 2 := Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ √((m : ℝ) + 2) := Real.sqrt_nonneg _
    have hN1' : (2 * m + 6 : ℝ) ≤ ((k * M : ℕ) : ℝ) := by exact_mod_cast hN1
    have hN2' : (8 : ℝ) ≤ ((k * M : ℕ) : ℝ) := by exact_mod_cast hN2
    nlinarith [mul_nonneg hs0 (sub_nonneg.2 hN2')]

private lemma cond_complex {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) :
    4 * (√(m + 1) + 1) ^ 2 ≤ (√(m + 1) + 2) * ((k * m ^ 2 : ℕ) : ℝ) := by
  have h2M : 2 * m ^ 2 ≤ k * m ^ 2 := Nat.mul_le_mul_right _ hk
  have hN1 : 2 * m + 4 ≤ k * m ^ 2 := by nlinarith
  have hN2 : 8 ≤ k * m ^ 2 := by nlinarith
  have hs2 : √((m : ℝ) + 1) ^ 2 = m + 1 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ √((m : ℝ) + 1) := Real.sqrt_nonneg _
  have hN1' : (2 * m + 4 : ℝ) ≤ ((k * m ^ 2 : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN2' : (8 : ℝ) ≤ ((k * m ^ 2 : ℕ) : ℝ) := by exact_mod_cast hN2
  nlinarith [mul_nonneg hs0 (sub_nonneg.2 hN2')]

/-! ### Complementary dimensions -/

/-- **Complementary dimensions, real case** ([DL26, Theorem 3.1]). If `ℝ^m`, `m ≥ 2`, admits a
maximal equiangular tight frame, i.e. an `ETF(m, M)` with `M = m(m+1)/2`, then for every `k ≥ 1`,
`λ_ℝ(kM - m, kM) = λ_ℝ(m) - 2m/(kM) + 1`. -/
theorem maxRelProjConst_compl_real {m k M : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hM : M = m * (m + 1) / 2) (h : ExistsETF ℝ m M) :
    maxRelProjConst ℝ (k * M - m) (k * M) = maxProjConst ℝ m - 2 * m / (k * M) + 1 := by
  have hM2 : 2 * M = m * (m + 1) := by
    rw [hM]; exact Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd
  have hmM : m < M := by nlinarith
  have hlam : maxProjConst ℝ m = delta m M := by
    subst hM; exact maxProjConst_real_eq_delta (by omega) h
  have hμ : quasiRelConst ℝ (Fin M) m = delta m M :=
    (quasiRelConst_eq_delta_of_existsETF (by omega) h).1
  have hδ : delta m M = bukhCoxReal m := by rw [hM]; exact delta_eq_bukhCoxReal (by omega)
  rw [hlam]
  apply le_antisymm
  · rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · obtain rfl : k = 1 := by omega
      simp only [one_mul, Nat.cast_one]
      refine (maxRelProjConst_le_delta (by omega)).trans (le_of_eq ?_)
      rw [delta_compl (by omega) hmM]
      ring
    · by_cases h22 : m = 2 ∧ k = 2
      · obtain ⟨rfl, rfl⟩ := h22
        obtain rfl : M = 3 := by omega
        rw [show 2 * 3 - 2 = 4 from rfl, show 2 * 3 = 6 from rfl, maxRelProjConst_four_six,
          delta]
        norm_num
      · rw [maxRelProjConst_eq_clConst]
        have hmN : m ≤ k * M := by nlinarith
        refine (clConst_compl_le_real (by omega) hmN (cond_real hm hk2 h22 hM2)).trans
          (le_of_eq ?_)
        rw [hδ]
        push_cast
        ring
  · rw [maxRelProjConst_eq_clConst]
    have := quasiRelConst_add_le_clConst (𝕜 := ℝ) hk (by omega) hmM.le
    rw [hμ] at this
    linarith

/-- **Complementary dimensions, complex case** ([DL26, Theorem 3.1]). If `ℂ^m`, `m ≥ 2`, admits a
maximal equiangular tight frame, i.e. an `ETF(m, M)` with `M = m²` (a SIC-POVM), then for every
`k ≥ 1`, `λ_ℂ(kM - m, kM) = λ_ℂ(m) - 2m/(kM) + 1`. -/
theorem maxRelProjConst_compl_complex {m k M : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) (hM : M = m ^ 2)
    (h : ExistsETF ℂ m M) :
    maxRelProjConst ℂ (k * M - m) (k * M) = maxProjConst ℂ m - 2 * m / (k * M) + 1 := by
  have hmM : m < M := by rw [hM]; nlinarith
  have hlam : maxProjConst ℂ m = delta m M := by
    subst hM; exact maxProjConst_complex_eq_delta (by omega) h
  have hμ : quasiRelConst ℂ (Fin M) m = delta m M :=
    (quasiRelConst_eq_delta_of_existsETF (by omega) h).1
  have hδ : delta m M = bukhCoxComplex m := by rw [hM]; exact delta_eq_bukhCoxComplex (by omega)
  rw [hlam]
  apply le_antisymm
  · rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · obtain rfl : k = 1 := by omega
      simp only [one_mul, Nat.cast_one]
      refine (maxRelProjConst_le_delta (by omega)).trans (le_of_eq ?_)
      rw [delta_compl (by omega) hmM]
      ring
    · rw [maxRelProjConst_eq_clConst]
      have hmN : m ≤ k * M := by nlinarith
      have hcond := cond_complex hm hk2
      rw [← hM] at hcond
      refine (clConst_compl_le_complex (by omega) hmN hcond).trans (le_of_eq ?_)
      rw [hδ]
      push_cast
      ring
  · rw [maxRelProjConst_eq_clConst]
    have := quasiRelConst_add_le_clConst (𝕜 := ℂ) hk (by omega) hmM.le
    rw [hμ] at this
    linarith

/-- **Complementary dimensions, attainment (real case)** ([DL26, Theorem 3.1]). The maximum is
attained with equal weights, i.e. by an equal-norm tight frame:
`μ_ℝ(kM - m, kM) = λ_ℝ(kM - m, kM) = λ_ℝ(m) - 2m/(kM) + 1`. -/
theorem quasiRelConst_compl_real {m k M : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hM : M = m * (m + 1) / 2) (h : ExistsETF ℝ m M) :
    quasiRelConst ℝ (Fin (k * M)) (k * M - m) = maxProjConst ℝ m - 2 * m / (k * M) + 1 := by
  refine le_antisymm ?_ ?_
  · rw [← maxRelProjConst_compl_real hm hk hM h]
    exact quasiRelConst_le_maxRelProjConst _ _
  · have hM2 : 2 * M = m * (m + 1) := by
      rw [hM]; exact Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd
    have hmM : m < M := by nlinarith
    have hlam : maxProjConst ℝ m = delta m M := by
      subst hM; exact maxProjConst_real_eq_delta (by omega) h
    have hμ := (quasiRelConst_eq_delta_of_existsETF (by omega) h).1
    have := quasiRelConst_add_le_quasiRelConst (𝕜 := ℝ) hk (by omega) hmM.le
    rw [hμ] at this
    rw [hlam]
    linarith

/-- **Complementary dimensions, attainment (complex case)** ([DL26, Theorem 3.1]). The maximum is
attained with equal weights, i.e. by an equal-norm tight frame:
`μ_ℂ(kM - m, kM) = λ_ℂ(kM - m, kM) = λ_ℂ(m) - 2m/(kM) + 1`. -/
theorem quasiRelConst_compl_complex {m k M : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) (hM : M = m ^ 2)
    (h : ExistsETF ℂ m M) :
    quasiRelConst ℂ (Fin (k * M)) (k * M - m) = maxProjConst ℂ m - 2 * m / (k * M) + 1 := by
  refine le_antisymm ?_ ?_
  · rw [← maxRelProjConst_compl_complex hm hk hM h]
    exact quasiRelConst_le_maxRelProjConst _ _
  · have hmM : m < M := by rw [hM]; nlinarith
    have hlam : maxProjConst ℂ m = delta m M := by
      subst hM; exact maxProjConst_complex_eq_delta (by omega) h
    have hμ := (quasiRelConst_eq_delta_of_existsETF (by omega) h).1
    have := quasiRelConst_add_le_quasiRelConst (𝕜 := ℂ) hk (by omega) hmM.le
    rw [hμ] at this
    rw [hlam]
    linarith

/-! ### The case `m = 1`: hyperplanes -/

/-- **Hyperplanes**: `λ_𝕜(N - 1, N) = 2 - 2/N`. This is the case `m = 1` of the formula of
[DL26, Theorem 3.1] (`M = 1`, `k = N`, `λ_𝕜(1) = 1`); here both bounds come from the simplex, the
`ETF(N - 1, N)`: the König–Lewis–Lin bound `δ_{N-1,N} = 2 - 2/N` and the repeated frame. For
`N = 6` this recovers `Π(5, 6) = 5/3` in the notation of [JFA] (`maxRelProjConst_five_six`). -/
theorem maxRelProjConst_hyperplane {N : ℕ} (hN : 1 ≤ N) :
    maxRelProjConst 𝕜 (N - 1) N = 2 - 2 / N := by
  rcases hN.lt_or_eq with hN2 | rfl
  · have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hδ1 : delta 1 N = 1 := by
      rw [delta, Nat.cast_one, div_one, Real.sqrt_mul_self (by linarith)]
      field_simp
      ring
    apply le_antisymm
    · refine (maxRelProjConst_le_delta (by omega)).trans (le_of_eq ?_)
      rw [delta_compl le_rfl hN2, hδ1]
      push_cast
      ring
    · have h := quasiRelConst_add_le_clConst (𝕜 := 𝕜) (m := 1) (M := 1) (k := N) (by omega)
        le_rfl le_rfl
      have hμ : quasiRelConst 𝕜 (Fin 1) 1 = 1 := by
        rw [(quasiRelConst_eq_delta_of_existsETF one_ne_zero (MaximalETF.existsETF_one 𝕜)).1, delta]
        norm_num
      rw [hμ, mul_one, ← maxRelProjConst_eq_clConst] at h
      push_cast at h
      simp only [mul_one] at h
      linarith
  · refine le_antisymm ?_ ?_
    · simpa using maxRelProjConst_le_sqrt (𝕜 := 𝕜) 0 1
    · norm_num
      exact maxRelProjConst_nonneg 0 1

/-! ### Explicit values -/

open MaximalETF

/-- `λ_ℝ(3k - 2, 3k) = 7/3 - 4/(3k)`; e.g. `λ_ℝ(1, 3) = 1`, `λ_ℝ(4, 6) = 5/3`,
`λ_ℝ(7, 9) = 17/9`. -/
theorem maxRelProjConst_compl_real_two {k : ℕ} (hk : 1 ≤ k) :
    maxRelProjConst ℝ (3 * k - 2) (3 * k) = 7 / 3 - 4 / (3 * k) := by
  have h := maxRelProjConst_compl_real (M := 3) (le_refl 2) hk (by norm_num) existsETF_two
  rw [mul_comm k 3, maxProjConst_real_two] at h
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [h]
  field_simp
  ring

/-- `λ_ℝ(6k - 3, 6k) = (3 + √5)/2 - 1/k`. -/
theorem maxRelProjConst_compl_real_three {k : ℕ} (hk : 1 ≤ k) :
    maxRelProjConst ℝ (6 * k - 3) (6 * k) = (3 + √5) / 2 - 1 / k := by
  have h := maxRelProjConst_compl_real (m := 3) (M := 6) (by norm_num) hk (by norm_num)
    existsETF_three_real
  rw [mul_comm k 6, maxProjConst_real_three] at h
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [h]
  field_simp
  ring

/-- `λ_ℝ(28k - 7, 28k) = 7/2 - 1/(2k)`. -/
theorem maxRelProjConst_compl_real_seven {k : ℕ} (hk : 1 ≤ k) :
    maxRelProjConst ℝ (28 * k - 7) (28 * k) = 7 / 2 - 1 / (2 * k) := by
  have h := maxRelProjConst_compl_real (m := 7) (M := 28) (by norm_num) hk (by norm_num)
    existsETF_seven
  rw [mul_comm k 28, maxProjConst_real_seven] at h
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [h]
  field_simp
  ring

/-- `λ_ℝ(276k - 23, 276k) = 17/3 - 1/(6k)`. -/
theorem maxRelProjConst_compl_real_twentyThree {k : ℕ} (hk : 1 ≤ k) :
    maxRelProjConst ℝ (276 * k - 23) (276 * k) = 17 / 3 - 1 / (6 * k) := by
  have h := maxRelProjConst_compl_real (m := 23) (M := 276) (by norm_num) hk (by norm_num)
    existsETF_twentyThree
  rw [mul_comm k 276, maxProjConst_real_twentyThree] at h
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [h]
  field_simp
  ring

/-- `λ_ℂ(4k - 2, 4k) = (3 + √3)/2 - 1/k`. -/
theorem maxRelProjConst_compl_complex_two {k : ℕ} (hk : 1 ≤ k) :
    maxRelProjConst ℂ (4 * k - 2) (4 * k) = (3 + √3) / 2 - 1 / k := by
  have h := maxRelProjConst_compl_complex (m := 2) (M := 4) (le_refl 2) hk (by norm_num)
    existsETF_two_complex
  rw [mul_comm k 4, maxProjConst_complex_two] at h
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [h]
  field_simp
  ring

/-- `λ_ℂ(9k - 3, 9k) = 8/3 - 2/(3k)`. -/
theorem maxRelProjConst_compl_complex_three {k : ℕ} (hk : 1 ≤ k) :
    maxRelProjConst ℂ (9 * k - 3) (9 * k) = 8 / 3 - 2 / (3 * k) := by
  have h := maxRelProjConst_compl_complex (m := 3) (M := 9) (by norm_num) hk (by norm_num)
    existsETF_three_complex
  rw [mul_comm k 9, maxProjConst_complex_three] at h
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [h]
  field_simp
  ring

end ProjectionConstants
