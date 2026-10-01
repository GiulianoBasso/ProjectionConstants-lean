/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Bounds.BukhCox
import ProjectionConstants.Bounds.KLL
import ProjectionConstants.Quasimaximal

/-!
# Upper bounds for `λ_𝕜(m)` at the Gerzon bounds

By Gerzon's bound there are at most `m(m+1)/2` equiangular lines in `ℝ^m` and at most `m²` in
`ℂ^m`; an equiangular tight frame of that many vectors is called *maximal*. At these values of
`N`, `δ_{m,N}` becomes the Bukh–Cox bound of `ProjectionConstants.Bounds.BukhCox`, which gives
the bounds `μ_ℝ(m, N) ≤ δ_{m, m(m+1)/2}` and `μ_ℂ(m, N) ≤ δ_{m, m²}` for all `N`
[DL, Theorem 2.1]. Since `λ_𝕜(m) = μ_𝕜(m) = sup_N μ_𝕜(m, N)` ([DL, Theorem 2.2],
`maxProjConst_eq_quasiMaxConst`), these are also bounds for `λ_𝕜(m)`. They are attained if
there is a maximal equiangular tight frame in `𝕜^m`, since an `ETF(m, N)` gives
`λ_𝕜(m, N) = δ_{m,N}` (`quasiRelConst_eq_delta_of_existsETF`) [DL, Theorem 2.3].

[DL] assumes `m > 1`; the statements here also hold for `m = 1`.

## Main statements

* `delta_eq_bukhCoxReal`, `delta_eq_bukhCoxComplex`: `δ_{m, m(m+1)/2} = bukhCoxReal m` and
  `δ_{m, m²} = bukhCoxComplex m`.
* `quasiRelConst_real_le_delta`, `quasiRelConst_complex_le_delta`: `μ_ℝ(m, N) ≤ δ_{m, m(m+1)/2}`
  and `μ_𝕜(m, N) ≤ δ_{m, m²}` [DL, Theorem 2.1].
* `maxProjConst_real_le_delta`, `maxProjConst_complex_le_delta`: `λ_ℝ(m) ≤ δ_{m, m(m+1)/2}` and
  `λ_ℂ(m) ≤ δ_{m, m²}` [DL, Theorem 2.3].
* `delta_le_maxProjConst_of_existsETF`: an `ETF(m, N)` gives `δ_{m,N} ≤ λ_𝕜(m)`.
* `maxProjConst_real_eq_delta`, `maxProjConst_complex_eq_delta`: equality in the presence of a
  maximal equiangular tight frame [DL, Theorem 2.3].

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.

## Tags

projection constant, equiangular tight frame, Gerzon bound
-/

open Matrix Finset

namespace ProjectionConstants

/-! ### The values of `δ` at the Gerzon bounds -/

/-- `δ_{m, m(m+1)/2} = 2/(m+1) · (1 + (m-1)/2 · √(m+2))`. -/
theorem delta_eq_bukhCoxReal {m : ℕ} (hm : 1 ≤ m) : delta m (m * (m + 1) / 2) = bukhCoxReal m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [delta, bukhCoxReal, Nat.cast_mul_succ_div_two]
  have e : ((m : ℝ) * (m + 1) / 2 - 1) * ((m : ℝ) * (m + 1) / 2 - m) / m =
      ((m - 1) / 2) ^ 2 * (m + 2) := by
    field_simp
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  field_simp

/-- `δ_{m, m²} = 1/m · (1 + (m-1) √(m+1))`. -/
theorem delta_eq_bukhCoxComplex {m : ℕ} (hm : 1 ≤ m) : delta m (m ^ 2) = bukhCoxComplex m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [delta, bukhCoxComplex]
  push_cast
  have e : ((m : ℝ) ^ 2 - 1) * ((m : ℝ) ^ 2 - m) / m = (m - 1) ^ 2 * (m + 1) := by
    field_simp
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  field_simp

/-! ### Bounds for `μ_𝕜(m, N)` -/

/-- **The Bukh–Cox bound, real case** ([DL, Theorem 2.1]). `μ_ℝ(m, N) ≤ δ_{m, m(m+1)/2}`. -/
theorem quasiRelConst_real_le_delta {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    quasiRelConst ℝ (Fin N) m ≤ delta m (m * (m + 1) / 2) := by
  rw [delta_eq_bukhCoxReal hm]
  have h0 : 0 ≤ bukhCoxReal m := by
    rw [bukhCoxReal]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : 0 ≤ ((m : ℝ) - 1) / 2 * √(m + 2) := by
      apply mul_nonneg _ (Real.sqrt_nonneg _); linarith
    positivity
  refine quasiRelConst_le h0 fun P hP ↦ ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [h0]
  rw [div_le_iff₀ (by simpa using hN), mul_comm]
  exact absSum_le_bukhCoxReal hm hP

/-- **The Bukh–Cox bound, complex case** ([DL, Theorem 2.1]). `μ_𝕜(m, N) ≤ δ_{m, m²}` (for
`𝕜 = ℂ`, and also for `𝕜 = ℝ`). -/
theorem quasiRelConst_complex_le_delta {𝕜 : Type*} [RCLike 𝕜] {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    quasiRelConst 𝕜 (Fin N) m ≤ delta m (m ^ 2) := by
  rw [delta_eq_bukhCoxComplex hm]
  have h0 : 0 ≤ bukhCoxComplex m := by
    rw [bukhCoxComplex]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : 0 ≤ ((m : ℝ) - 1) * √(m + 1) := by
      apply mul_nonneg _ (Real.sqrt_nonneg _); linarith
    positivity
  refine quasiRelConst_le h0 fun P hP ↦ ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [h0]
  rw [div_le_iff₀ (by simpa using hN), mul_comm]
  exact absSum_le_bukhCoxComplex hm hP

/-! ### Bounds for `λ_𝕜(m)` -/

/-- **An upper bound for `λ_ℝ(m)`** ([DL, Theorem 2.3]).
`λ_ℝ(m) ≤ δ_{m, m(m+1)/2} = 2/(m+1) · (1 + (m-1)/2 · √(m+2))`. -/
theorem maxProjConst_real_le_delta {m : ℕ} (hm : 1 ≤ m) :
    maxProjConst ℝ m ≤ delta m (m * (m + 1) / 2) := by
  rw [maxProjConst_eq_quasiMaxConst]
  exact quasiMaxConst_le (by rw [delta]; positivity) fun N ↦ quasiRelConst_real_le_delta hm N

/-- **An upper bound for `λ_ℂ(m)`** ([DL, Theorem 2.3]).
`λ_ℂ(m) ≤ δ_{m, m²} = 1/m · (1 + (m-1) √(m+1))`. -/
theorem maxProjConst_complex_le_delta {m : ℕ} (hm : 1 ≤ m) :
    maxProjConst ℂ m ≤ delta m (m ^ 2) := by
  rw [maxProjConst_eq_quasiMaxConst]
  exact quasiMaxConst_le (by rw [delta]; positivity) fun N ↦ quasiRelConst_complex_le_delta hm N

/-- An equiangular tight frame of `N` vectors in `𝕜^m` gives `δ_{m,N} ≤ λ_𝕜(m)`. -/
theorem delta_le_maxProjConst_of_existsETF {𝕜 : Type} [RCLike 𝕜] {m N : ℕ} (hm : m ≠ 0)
    (h : ExistsETF 𝕜 m N) : delta m N ≤ maxProjConst 𝕜 m := by
  rw [← (quasiRelConst_eq_delta_of_existsETF hm h).2]
  exact maxRelProjConst_le_maxProjConst m N

/-- **The equality case for real maximal ETFs** ([DL, Theorem 2.3]). If there is a maximal
equiangular tight frame in `ℝ^m`, i.e. an `ETF(m, m(m+1)/2)`, then `λ_ℝ(m) = δ_{m, m(m+1)/2}`. -/
theorem maxProjConst_real_eq_delta {m : ℕ} (hm : 1 ≤ m) (h : ExistsETF ℝ m (m * (m + 1) / 2)) :
    maxProjConst ℝ m = delta m (m * (m + 1) / 2) :=
  le_antisymm (maxProjConst_real_le_delta hm)
    (delta_le_maxProjConst_of_existsETF (Nat.one_le_iff_ne_zero.1 hm) h)

/-- **The equality case for complex maximal ETFs** ([DL, Theorem 2.3]). If there is a maximal
equiangular tight frame in `ℂ^m`, i.e. an `ETF(m, m²)` (a SIC-POVM), then `λ_ℂ(m) = δ_{m, m²}`. -/
theorem maxProjConst_complex_eq_delta {m : ℕ} (hm : 1 ≤ m) (h : ExistsETF ℂ m (m ^ 2)) :
    maxProjConst ℂ m = delta m (m ^ 2) :=
  le_antisymm (maxProjConst_complex_le_delta hm)
    (delta_le_maxProjConst_of_existsETF (Nat.one_le_iff_ne_zero.1 hm) h)

end ProjectionConstants
