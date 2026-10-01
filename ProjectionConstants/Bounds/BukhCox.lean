/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Matrix.HermCoords
import ProjectionConstants.ChalmersLewicki.Defs
import ProjectionConstants.ForMathlib.Matrix.RankTrace

/-!
# The bound of Bukh and Cox

We prove the matrix form of [DL, Theorem 2.1], a special case of [BC, Lemma 5]: every orthogonal
projection `P` of rank `m ≥ 1` on `N` coordinates satisfies

* `(1/N) ∑ᵢⱼ |Pᵢⱼ| ≤ 2/(m+1) · (1 + (m-1)/2 · √(m+2))` if `P` is real,
* `(1/N) ∑ᵢⱼ |Pᵢⱼ| ≤ 1/m · (1 + (m-1) √(m+1))` if `P` is complex (or real).

The right-hand sides are `δ_{m, m(m+1)/2}` and `δ_{m, m²}`. The resulting bounds for the
quasimaximal constants `μ_𝕜(m, N)` and for `λ_𝕜(m)` are derived in
`ProjectionConstants.Bounds.Gerzon`.

## Main definitions

* `bukhCoxReal m`: the real bound `2/(m+1) · (1 + (m-1)/2 · √(m+2))`.
* `bukhCoxComplex m`: the complex bound `1/m · (1 + (m-1) √(m+1))`.

## Main statements

* `two_mul_absSum_le_of_hermCoords`: the Bukh–Cox inequality
  `2 d φ ∑ᵢⱼ |Pᵢⱼ| ≤ d N + (d φ² - (1-φ)²) N m` whenever `(1 - φ)² ≤ d φ²`, where `d` is the
  number of real coordinates on the Hermitian `m × m` matrices (`HermCoords`).
* `absSum_le_bukhCoxReal`: `∑ᵢⱼ |Pᵢⱼ| ≤ N · bukhCoxReal m` for real `P`.
* `absSum_le_bukhCoxComplex`: `∑ᵢⱼ |Pᵢⱼ| ≤ N · bukhCoxComplex m`.

## Proof sketch

Let `P = Uᴴ U` with `U Uᴴ = 1`, with columns `uᵢ`, and put `aᵢ = ‖uᵢ‖ = √Pᵢᵢ`, `gᵢⱼ = |Pᵢⱼ|`.
The rank-one matrices `Xᵢ = uᵢ uᵢᴴ` are Hermitian with `Re tr(XᵢXⱼ) = gᵢⱼ²` and `tr Xᵢ = aᵢ²`, so
(`HermCoords.rank_le`) the matrix
`Aᵢⱼ = (gᵢⱼ² - φ² aᵢ² aⱼ²) / ((1 + φ) (aᵢaⱼ)^{3/2})` has rank at most `d`, the real dimension of
the Hermitian matrices. Then, as in [DL],

`∑ᵢⱼ (gᵢⱼ - φ aᵢaⱼ)²/(aᵢaⱼ) ≥ ∑ᵢⱼ Aᵢⱼ² ≥ (tr A)²/d = (1-φ)² (∑ aᵢ)²/d`

by `(tr A)² ≤ rank A · ∑ Aᵢⱼ²` (`Matrix.IsHermitian.sq_trace_le_rank_mul`). Expanding the
left-hand side and using `∑ᵢⱼ gᵢⱼ²/(aᵢaⱼ) ≤ N` and `(∑ aᵢ)² ≤ N m` gives
`two_mul_absSum_le_of_hermCoords`. Choosing `φ = 1/√(m+2)`, `d = m(m+1)/2` (real,
`HermCoords.real`) and `φ = 1/√(m+1)`, `d = m²` (complex, `HermCoords.full`) gives the bounds.

## Implementation notes

Coordinates with vanishing `aᵢ` are harmless thanks to the convention `x / 0 = 0`.

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
* [BC] B. Bukh, C. Cox, *Nearly orthogonal vectors and small antipodal spherical codes*,
  arXiv:1803.02949.

## Tags

projection constant, Hermitian matrix, rank, trace
-/

open Matrix Finset

namespace ProjectionConstants

/-! ### Scalar inequalities -/

section Scalar

/-- The termwise estimate `Aᵢⱼ² ≤ (gᵢⱼ - φ aᵢaⱼ)²/(aᵢaⱼ)`. -/
private lemma bc_term {g a b φ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hg0 : 0 ≤ g) (hg : g ≤ a * b)
    (hφ : 0 ≤ φ) :
    (1 / √a ^ 3 * ((g ^ 2 - φ ^ 2 * a ^ 2 * b ^ 2) / (1 + φ)) * (1 / √b ^ 3)) ^ 2 ≤
      (g - φ * a * b) ^ 2 / (a * b) := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  rcases hb.eq_or_lt with rfl | hb'
  · simp
  have hsa : √a ^ 6 = a ^ 3 := by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Real.sq_sqrt ha]
  have hsb : √b ^ 6 = b ^ 3 := by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Real.sq_sqrt hb]
  have hlhs : (1 / √a ^ 3 * ((g ^ 2 - φ ^ 2 * a ^ 2 * b ^ 2) / (1 + φ)) * (1 / √b ^ 3)) ^ 2 =
      (g - φ * a * b) ^ 2 * (g + φ * a * b) ^ 2 / ((1 + φ) ^ 2 * a ^ 3 * b ^ 3) := by
    rw [← hsa, ← hsb]
    have : √a ≠ 0 := (Real.sqrt_pos.2 ha').ne'
    have : √b ≠ 0 := (Real.sqrt_pos.2 hb').ne'
    field_simp
    ring
  rw [hlhs, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (g + φ * a * b) ^ 2 ≤ ((1 + φ) * (a * b)) ^ 2 := by
    have : 0 ≤ g + φ * a * b := by positivity
    have : g + φ * a * b ≤ (1 + φ) * (a * b) := by nlinarith
    gcongr
  have h2 : 0 ≤ (g - φ * a * b) ^ 2 := sq_nonneg _
  have h3 : 0 < a * b := mul_pos ha' hb'
  calc (g - φ * a * b) ^ 2 * (g + φ * a * b) ^ 2 * (a * b)
      ≤ (g - φ * a * b) ^ 2 * ((1 + φ) * (a * b)) ^ 2 * (a * b) := by gcongr
    _ = (g - φ * a * b) ^ 2 * ((1 + φ) ^ 2 * a ^ 3 * b ^ 3) := by ring

/-- `(g - φab)²/(ab) = g²/(ab) - 2φg + φ²ab` (also when `ab = 0`, since then `g = 0`). -/
private lemma bc_expand {g a b φ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hg0 : 0 ≤ g) (hg : g ≤ a * b) :
    (g - φ * a * b) ^ 2 / (a * b) = g ^ 2 / (a * b) - 2 * φ * g + φ ^ 2 * (a * b) := by
  rcases (mul_nonneg ha hb).eq_or_lt with h | h
  · have hg' : g = 0 := le_antisymm (h ▸ hg) hg0
    rw [← h, hg']
    simp
  · have ha' : a ≠ 0 := by rintro rfl; simp at h
    have hb' : b ≠ 0 := by rintro rfl; simp at h
    field_simp
    ring

/-- `g²/(ab) ≤ (g²/a² + g²/b²)/2`. -/
private lemma bc_amgm {g a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    g ^ 2 / (a * b) ≤ (g ^ 2 / a ^ 2 + g ^ 2 / b ^ 2) / 2 := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_mul, div_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_add]
    positivity
  rcases hb.eq_or_lt with rfl | hb'
  · simp only [mul_zero, div_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero]
    positivity
  rw [div_add_div _ _ (by positivity) (by positivity), div_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  have : 0 ≤ g ^ 2 * (a - b) ^ 2 * (a * b) := by positivity
  nlinarith [sq_nonneg (a - b)]

/-- The diagonal: `Aᵢᵢ = (1 - φ) aᵢ`. -/
private lemma bc_diag {a φ : ℝ} (ha : 0 ≤ a) (hφ : 0 ≤ φ) :
    1 / √a ^ 3 * (((a ^ 2) ^ 2 - φ ^ 2 * a ^ 2 * a ^ 2) / (1 + φ)) * (1 / √a ^ 3) =
      (1 - φ) * a := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  have hsa : √a ^ 6 = a ^ 3 := by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Real.sq_sqrt ha]
  have : √a ≠ 0 := (Real.sqrt_pos.2 ha').ne'
  have h1 : (1 + φ) ≠ 0 := by positivity
  rw [show 1 / √a ^ 3 * (((a ^ 2) ^ 2 - φ ^ 2 * a ^ 2 * a ^ 2) / (1 + φ)) * (1 / √a ^ 3) =
    (1 - φ) * (1 + φ) * a ^ 4 / ((1 + φ) * √a ^ 6) by field_simp; ring, hsa]
  field_simp

end Scalar

/-! ### The main inequality -/

variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The Bukh–Cox inequality** (cf. [BC, Lemma 5] and the proof of [DL, Theorem 2.1]). If the
Hermitian `m × m` matrices admit coordinates with `d` entries (`HermCoords`) and
`(1 - φ)² ≤ d φ²`, then for every orthogonal projection `P` of rank `m` on `N` coordinates,
`2 d φ ∑ᵢⱼ |Pᵢⱼ| ≤ d N + (d φ² - (1 - φ)²) N m`. -/
theorem two_mul_absSum_le_of_hermCoords (H : HermCoords 𝕜 m) {P : Matrix ι ι 𝕜}
    (hP : P ∈ orthProjs 𝕜 ι m) {φ : ℝ} (hφ : 0 < φ)
    (hd : (1 - φ) ^ 2 ≤ Fintype.card H.Idx * φ ^ 2) :
    Fintype.card H.Idx * (2 * φ * absSum P) ≤
      Fintype.card H.Idx * Fintype.card ι +
        (Fintype.card H.Idx * φ ^ 2 - (1 - φ) ^ 2) * Fintype.card ι * m := by
  classical
  set d : ℝ := (Fintype.card H.Idx : ℝ) with hd_def
  set N : ℝ := (Fintype.card ι : ℝ) with hN_def
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  -- the Parseval frame and the rank-one matrices `Xᵢ = uᵢ uᵢᴴ`
  obtain ⟨U, hU, hUP⟩ := exists_parseval_of_mem_orthProjs hP
  set u : ι → Fin m → 𝕜 := fun i k ↦ U k i with hu
  set X : ι → Matrix (Fin m) (Fin m) 𝕜 := fun i ↦ vecMulVec (u i) (star (u i)) with hX
  have hXh : ∀ i, (X i).IsHermitian := fun i ↦ by
    simp [X, Matrix.IsHermitian, conjTranspose_vecMulVec]
  have hPuu : ∀ i j, P i j = star (u i) ⬝ᵥ u j := by
    intro i j
    rw [← hUP]
    simp [mul_apply, dotProduct, u, conjTranspose_apply]
  have hPuu' : ∀ i j, u i ⬝ᵥ star (u j) = P j i := by
    intro i j
    rw [hPuu, dotProduct_comm]
  -- the entries
  set g : ι → ι → ℝ := fun i j ↦ ‖P i j‖ with hg
  set a : ι → ℝ := fun i ↦ √(RCLike.re (P i i)) with ha_def
  have ha0 : ∀ i, 0 ≤ a i := fun i ↦ Real.sqrt_nonneg _
  have hasq : ∀ i, a i ^ 2 = RCLike.re (P i i) := fun i ↦ Real.sq_sqrt (hP.1.re_diag_nonneg i)
  have hg0 : ∀ i j, 0 ≤ g i j := fun i j ↦ norm_nonneg _
  have hgab : ∀ i j, g i j ≤ a i * a j := by
    intro i j
    have h := hP.1.norm_apply_sq_le_mul i j
    rw [← hasq, ← hasq] at h
    have h' : g i j ^ 2 ≤ (a i * a j) ^ 2 := by rw [mul_pow]; exact h
    have hab := mul_nonneg (ha0 i) (ha0 j)
    nlinarith [hg0 i j]
  have hgsymm : ∀ i j, g j i = g i j := fun i j ↦ hP.1.norm_apply_symm i j
  -- tightness
  have hrow : ∀ i, ∑ j, g i j ^ 2 = a i ^ 2 := fun i ↦ by
    rw [hasq, hP.1.re_diag_eq_sum_row]
  have hcol : ∀ j, ∑ i, g i j ^ 2 = a j ^ 2 := fun j ↦ by
    rw [hasq, hP.1.re_diag]
  have hsum_a2 : ∑ i, a i ^ 2 = m := by
    simp_rw [hasq]; exact sum_re_diag hP
  have hgii : ∀ i, g i i = a i ^ 2 := fun i ↦ by
    rw [hasq]; exact hP.1.norm_diag_eq i
  -- traces of the rank-one matrices
  have htrXX : ∀ i j, RCLike.re (X i * X j).trace = g i j ^ 2 := by
    intro i j
    simp only [X, vecMulVec_mul_vecMulVec, trace_vecMulVec, dotProduct_smul, smul_eq_mul]
    rw [hPuu' i j, ← hPuu i j, hP.1.apply_symm i j, RCLike.star_def, RCLike.mul_conj]
    simp [g]
  have htrX : ∀ i, RCLike.re (X i).trace = a i ^ 2 := by
    intro i
    simp only [X, trace_vecMulVec]
    rw [hPuu' i i, hasq]
  -- the matrices `M` and `A`
  set M : Matrix ι ι ℝ := Matrix.of fun i j ↦ (1 / (1 + φ)) * RCLike.re (X i * X j).trace -
    (φ ^ 2 / (1 + φ)) * RCLike.re (X i).trace * RCLike.re (X j).trace with hM
  have hMrank : M.rank ≤ Fintype.card H.Idx := H.rank_le X hXh _ _
  have hMentry : ∀ i j, M i j = (g i j ^ 2 - φ ^ 2 * a i ^ 2 * a j ^ 2) / (1 + φ) := by
    intro i j
    simp only [M, of_apply, htrXX, htrX]
    field_simp
  set s : ι → ℝ := fun i ↦ 1 / √(a i) ^ 3 with hs
  set A : Matrix ι ι ℝ := diagonal s * M * diagonal s with hA
  have hAentry : ∀ i j, A i j = s i * M i j * s j := by
    intro i j
    rw [hA, mul_diagonal, diagonal_mul]
  have hArank : A.rank ≤ Fintype.card H.Idx :=
    (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans hMrank)
  have hAh : A.IsHermitian := by
    ext i j
    simp only [conjTranspose_apply, star_trivial, hAentry, hMentry, hgsymm]
    ring
  -- the chain of inequalities
  have htrA : A.trace = (1 - φ) * ∑ i, a i := by
    rw [Finset.mul_sum]
    simp only [Matrix.trace, diag_apply, hAentry, hMentry, hgii, s]
    exact Finset.sum_congr rfl fun i _ ↦ bc_diag (ha0 i) hφ.le
  have hAsq : ∑ i, ∑ j, A i j ^ 2 ≤ ∑ i, ∑ j, (g i j - φ * a i * a j) ^ 2 / (a i * a j) := by
    refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
    rw [hAentry, hMentry]
    exact bc_term (ha0 i) (ha0 j) (hg0 i j) (hgab i j) hφ.le
  have habs : absSum P = ∑ i, ∑ j, g i j := rfl
  have hexp : ∑ i, ∑ j, (g i j - φ * a i * a j) ^ 2 / (a i * a j) =
      ∑ i, ∑ j, g i j ^ 2 / (a i * a j) - 2 * φ * ∑ i, ∑ j, g i j + φ ^ 2 * (∑ i, a i) ^ 2 := by
    have h1 : ∀ i j, (g i j - φ * a i * a j) ^ 2 / (a i * a j) =
        g i j ^ 2 / (a i * a j) - 2 * φ * g i j + φ ^ 2 * (a i * a j) := fun i j ↦
      bc_expand (ha0 i) (ha0 j) (hg0 i j) (hgab i j)
    calc ∑ i, ∑ j, (g i j - φ * a i * a j) ^ 2 / (a i * a j)
        = ∑ i, ∑ j, (g i j ^ 2 / (a i * a j) - 2 * φ * g i j + φ ^ 2 * (a i * a j)) := by
          simp only [h1]
      _ = ∑ i, ∑ j, g i j ^ 2 / (a i * a j) - 2 * φ * ∑ i, ∑ j, g i j +
            φ ^ 2 * ∑ i, ∑ j, a i * a j := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by rw [sq (∑ i, a i), Finset.sum_mul_sum]
  have hT : ∑ i, ∑ j, g i j ^ 2 / (a i * a j) ≤ N := by
    have e0 : ∑ i, ∑ j, (g i j ^ 2 / a i ^ 2 + g i j ^ 2 / a j ^ 2) / 2 =
        ((∑ i, ∑ j, g i j ^ 2 / a i ^ 2) + ∑ i, ∑ j, g i j ^ 2 / a j ^ 2) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [← Finset.sum_add_distrib, Finset.sum_div]
    have e1 : ∑ i, ∑ j, g i j ^ 2 / a i ^ 2 = ∑ i, a i ^ 2 / a i ^ 2 :=
      Finset.sum_congr rfl fun i _ ↦ by rw [← Finset.sum_div, hrow]
    have e2 : ∑ i, ∑ j, g i j ^ 2 / a j ^ 2 = ∑ j, a j ^ 2 / a j ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [← Finset.sum_div, hcol]
    have e3 : ∑ i, a i ^ 2 / a i ^ 2 ≤ N := by
      calc ∑ i, a i ^ 2 / a i ^ 2 ≤ ∑ _i : ι, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ ↦ div_self_le_one _
        _ = N := by simp [hN_def]
    calc ∑ i, ∑ j, g i j ^ 2 / (a i * a j)
        ≤ ∑ i, ∑ j, (g i j ^ 2 / a i ^ 2 + g i j ^ 2 / a j ^ 2) / 2 :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ bc_amgm (ha0 i) (ha0 j)
      _ ≤ N := by rw [e0, e1, e2]; linarith
  have hσ : (∑ i, a i) ^ 2 ≤ N * m := by
    rw [← hsum_a2]
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := a)
    simpa [hN_def] using this
  have hrk : A.trace ^ 2 ≤ d * ∑ i, ∑ j, A i j ^ 2 := by
    refine hAh.sq_trace_le_rank_mul.trans ?_
    have hnn : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
    have hr : (A.rank : ℝ) ≤ d := by rw [hd_def]; exact_mod_cast hArank
    exact mul_le_mul_of_nonneg_right hr hnn
  -- combine
  rw [htrA] at hrk
  have hS := absSum_nonneg P
  have hc : 0 ≤ d * φ ^ 2 - (1 - φ) ^ 2 := by linarith
  have key : (1 - φ) ^ 2 * (∑ i, a i) ^ 2 ≤
      d * (∑ i, ∑ j, g i j ^ 2 / (a i * a j) - 2 * φ * ∑ i, ∑ j, g i j +
        φ ^ 2 * (∑ i, a i) ^ 2) := by
    rw [← hexp]
    calc (1 - φ) ^ 2 * (∑ i, a i) ^ 2 = ((1 - φ) * ∑ i, a i) ^ 2 := by ring
      _ ≤ d * ∑ i, ∑ j, A i j ^ 2 := hrk
      _ ≤ _ := mul_le_mul_of_nonneg_left hAsq hd0
  have h1 : d * ∑ i, ∑ j, g i j ^ 2 / (a i * a j) ≤ d * N := mul_le_mul_of_nonneg_left hT hd0
  have h2 : (d * φ ^ 2 - (1 - φ) ^ 2) * (∑ i, a i) ^ 2 ≤ (d * φ ^ 2 - (1 - φ) ^ 2) * (N * m) :=
    mul_le_mul_of_nonneg_left hσ hc
  rw [habs]
  nlinarith

/-! ### The closed forms -/

/-- The Bukh–Cox bound for real subspaces, `2/(m+1) · (1 + (m-1)/2 · √(m+2))`; it equals
`δ_{m, m(m+1)/2}` (`delta_eq_bukhCoxReal`). -/
noncomputable def bukhCoxReal (m : ℕ) : ℝ := 2 / (m + 1) * (1 + (m - 1) / 2 * √(m + 2))

/-- The Bukh–Cox bound for complex subspaces, `1/m · (1 + (m-1) √(m+1))`; it equals `δ_{m, m²}`
(`delta_eq_bukhCoxComplex`). -/
noncomputable def bukhCoxComplex (m : ℕ) : ℝ := 1 / m * (1 + (m - 1) * √(m + 1))

section ClosedForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma card_real_cast (m : ℕ) :
    (Fintype.card (HermCoords.real m).Idx : ℝ) = m * (m + 1) / 2 := by
  rw [HermCoords.card_real]
  have h2 : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  rw [Nat.cast_div h2 (by norm_num)]
  push_cast
  ring

omit [DecidableEq ι] in
/-- **The Bukh–Cox bound, real case** (matrix form of [DL, Theorem 2.1]). For every real
orthogonal projection `P` of rank `m ≥ 1` on `N` coordinates,
`(1/N) ∑ᵢⱼ |Pᵢⱼ| ≤ 2/(m+1) · (1 + (m-1)/2 · √(m+2))`. -/
theorem absSum_le_bukhCoxReal {m : ℕ} (hm : 1 ≤ m) {P : Matrix ι ι ℝ} (hP : P ∈ orthProjs ℝ ι m) :
    absSum P ≤ Fintype.card ι * bukhCoxReal m := by
  set r := √((m : ℝ) + 2) with hr
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr0 : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr2 : r ^ 2 = m + 2 := Real.sq_sqrt (by linarith)
  have hr17 : 1.7 < r := by nlinarith
  have hφ : 0 < 1 / r := by positivity
  set d : ℝ := m * (m + 1) / 2 with hd
  have hcond : (1 - 1 / r) ^ 2 ≤ (Fintype.card (HermCoords.real m).Idx : ℝ) * (1 / r) ^ 2 := by
    rw [card_real_cast]
    rw [div_pow, one_pow, ← hd, mul_one_div, one_sub_div hr0.ne', div_pow,
      div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  have key := two_mul_absSum_le_of_hermCoords (HermCoords.real m) hP hφ hcond
  rw [card_real_cast, ← hd] at key
  set S := absSum P
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hd0 : 0 < d := by rw [hd]; positivity
  -- clear the denominators `r`
  have key2 : 2 * d * r * S ≤ N * (d * r ^ 2 + (d - (r - 1) ^ 2) * m) := by
    have e : d * (2 * (1 / r) * S) = 2 * d * r * S / r ^ 2 := by field_simp
    have e2 : d * N + (d * (1 / r) ^ 2 - (1 - 1 / r) ^ 2) * N * m =
        N * (d * r ^ 2 + (d - (r - 1) ^ 2) * m) / r ^ 2 := by
      field_simp
    rw [e, e2, div_le_div_iff_of_pos_right (by positivity)] at key
    exact key
  have hval : bukhCoxReal m = (r * (m - 1) + 2) / (m + 1) := by
    rw [bukhCoxReal, ← hr]
    field_simp
    ring
  rw [hval, mul_div_assoc', le_div_iff₀ (by positivity)]
  -- `d r² + (d - (r-1)²) m = m ((m+2)(m-1) + 2r) = m r (r(m-1) + 2)`
  have e3 : d * r ^ 2 + (d - (r - 1) ^ 2) * m = m * r * (r * (m - 1) + 2) := by
    rw [hd]
    have : r ^ 2 = m + 2 := hr2
    nlinarith [this]
  rw [e3] at key2
  have hmr : 0 < (m : ℝ) * r := by positivity
  have : 2 * d * r * S = (m * r) * ((m + 1) * S) := by rw [hd]; ring
  rw [this] at key2
  have : N * (↑m * r * (r * (↑m - 1) + 2)) = (m * r) * (N * (r * (m - 1) + 2)) := by ring
  rw [this] at key2
  exact le_of_mul_le_mul_left key2 hmr |>.trans_eq' (by ring)

private lemma card_full_cast (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) :
    (Fintype.card (HermCoords.full 𝕜 m).Idx : ℝ) = (m : ℝ) ^ 2 := by
  rw [HermCoords.card_full]; push_cast; ring

omit [DecidableEq ι] in
/-- **The Bukh–Cox bound, complex case** (matrix form of [DL, Theorem 2.1]). For every
orthogonal projection `P` of rank `m ≥ 1` on `N` coordinates (over `ℝ` or `ℂ`),
`(1/N) ∑ᵢⱼ |Pᵢⱼ| ≤ 1/m · (1 + (m-1) √(m+1))`. -/
theorem absSum_le_bukhCoxComplex {𝕜 : Type*} [RCLike 𝕜] {m : ℕ} (hm : 1 ≤ m) {P : Matrix ι ι 𝕜}
    (hP : P ∈ orthProjs 𝕜 ι m) : absSum P ≤ Fintype.card ι * bukhCoxComplex m := by
  set r := √((m : ℝ) + 1) with hr
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr0 : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr2 : r ^ 2 = m + 1 := Real.sq_sqrt (by linarith)
  have hr1 : 1 ≤ r := by nlinarith
  have hrm : r ≤ m + 1 := by nlinarith
  have hφ : 0 < 1 / r := by positivity
  set d : ℝ := (m : ℝ) ^ 2 with hd
  have hcond : (1 - 1 / r) ^ 2 ≤ (Fintype.card (HermCoords.full 𝕜 m).Idx : ℝ) * (1 / r) ^ 2 := by
    rw [card_full_cast, ← hd, div_pow, one_pow, mul_one_div, one_sub_div hr0.ne', div_pow,
      div_le_div_iff_of_pos_right (by positivity), hd]
    have h1 : 0 ≤ r - 1 := by linarith
    have h2 : r - 1 ≤ m := by linarith
    nlinarith
  have key := two_mul_absSum_le_of_hermCoords (HermCoords.full 𝕜 m) hP hφ hcond
  rw [card_full_cast, ← hd] at key
  set S := absSum P
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have key2 : 2 * d * r * S ≤ N * (d * r ^ 2 + (d - (r - 1) ^ 2) * m) := by
    have e : d * (2 * (1 / r) * S) = 2 * d * r * S / r ^ 2 := by field_simp
    have e2 : d * N + (d * (1 / r) ^ 2 - (1 - 1 / r) ^ 2) * N * m =
        N * (d * r ^ 2 + (d - (r - 1) ^ 2) * m) / r ^ 2 := by
      field_simp
    rw [e, e2, div_le_div_iff_of_pos_right (by positivity)] at key
    exact key
  have hm0 : (0 : ℝ) < m := by linarith
  have hval : bukhCoxComplex m = ((m - 1) * r + 1) / m := by
    rw [bukhCoxComplex, ← hr]
    field_simp
    ring
  rw [hval, mul_div_assoc', le_div_iff₀ hm0]
  have e3 : d * r ^ 2 + (d - (r - 1) ^ 2) * m = 2 * m * r * ((m - 1) * r + 1) := by
    rw [hd]
    nlinarith [hr2]
  rw [e3] at key2
  have hmr : 0 < 2 * (m : ℝ) * r := by positivity
  have e4 : 2 * d * r * S = (2 * m * r) * (S * m) := by rw [hd]; ring
  have e5 : N * (2 * ↑m * r * ((↑m - 1) * r + 1)) = (2 * m * r) * (N * ((m - 1) * r + 1)) := by
    ring
  rw [e4, e5] at key2
  exact le_of_mul_le_mul_left key2 hmr

end ClosedForm

end ProjectionConstants
