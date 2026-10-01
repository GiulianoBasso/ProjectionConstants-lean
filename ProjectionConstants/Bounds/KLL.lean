/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ETF.Basic
import ProjectionConstants.ForMathlib.Real
import ProjectionConstants.ForMathlib.BigOperators
import Mathlib.Algebra.Order.Chebyshev

/-!
# The bound of König, Lewis and Lin

For `1 ≤ m ≤ N`, every unit weight `t` (`t ≥ 0`, `∑ᵢ tᵢ² = 1`) and every orthogonal projection
`P` of rank `m` on `𝕜^N` satisfy `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ δ_{m,N}`, where
`δ_{m,N} = (m/N)(1 + √((N-1)(N-m)/m))` (`delta m N`). By the formula of Chalmers and Lewicki
[DL, Theorem 1.1], this is the bound `λ_𝕜(m, N) ≤ δ_{m,N}` of König, Lewis and Lin [KLL], in the
form of [FS, Theorem 5]; it is the first part of [DL, Theorem 1.2].

If there is an equiangular tight frame of `N` vectors in `𝕜^m`, then the bound is attained, even
with equal weights: `μ_𝕜(m, N) = λ_𝕜(m, N) = δ_{m,N}`. The converse is proved in
`ProjectionConstants.Bounds.KLLEquality`.

## Main statements

* `weightedAbsSum_le_delta`: `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ δ_{m,N}` for unit weights `t` and orthogonal
  projections `P` of rank `m ≥ 1` on `N` coordinates.
* `maxRelProjConst_le_delta`: `λ_𝕜(m, N) ≤ δ_{m,N}` for `m ≠ 0` [DL, Theorem 1.2].
* `quasiRelConst_le_delta`: `μ_𝕜(m, N) ≤ δ_{m,N}` for `m ≠ 0`.
* `quasiRelConst_eq_delta_of_existsETF`: if there is an `ETF(m, N)`, then
  `μ_𝕜(m, N) = λ_𝕜(m, N) = δ_{m,N}`.

## Proof sketch

Write `xᵢ = tᵢ²` and `pᵢ = Pᵢᵢ`. Then `∑ tᵢ tⱼ |Pᵢⱼ| = ∑ xᵢ pᵢ + ∑_{i≠j} tᵢ tⱼ |Pᵢⱼ|`, and by
Cauchy–Schwarz

* `∑_{i≠j} tᵢ tⱼ |Pᵢⱼ| ≤ √(1 - ∑ xᵢ²) √(m - ∑ pᵢ²)` (using `∑ⱼ |Pᵢⱼ|² = pᵢ`),
* `∑ xᵢ pᵢ = m/N + ∑ (xᵢ - 1/N)(pᵢ - m/N) ≤ m/N + √(∑ xᵢ² - 1/N) √(∑ pᵢ² - m²/N)`,
* `√a √b + √c √d ≤ √(a + c) √(b + d)` (`Real.sqrt_mul_add_sqrt_mul_le`),

which gives `m/N + √(1 - 1/N) √(m - m²/N) = δ_{m,N}` (`delta_eq`).

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
* [KLL] H. König, D. R. Lewis, P.-K. Lin, *Finite dimensional projection constants*,
  Studia Math. 75 (1983).
* [FS] S. Foucart, L. Skrzypek, *On maximal relative projection constants* (2017).

## Tags

projection constant, equiangular tight frame, Cauchy–Schwarz inequality
-/

open Matrix Finset

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- `δ_{m,N} = m/N + √(1 - 1/N) √(m - m²/N)` for `1 ≤ m ≤ N`. -/
lemma delta_eq {m N : ℕ} (hm : m ≠ 0) (hmN : m ≤ N) :
    delta m N = m / N + √(1 - 1 / N) * √(m - m ^ 2 / N) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hm0 hmN'
  rw [delta, mul_add, mul_one, ← Real.sqrt_mul (by
    rw [sub_nonneg, div_le_one hN0]; linarith [show (1 : ℝ) ≤ m by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 hm])]
  congr 1
  rw [show (m : ℝ) / N = √((m / N) ^ 2) by rw [Real.sqrt_sq (by positivity)],
    ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  field_simp

/-- **The bound of König, Lewis and Lin, matrix form** ([DL, Theorem 1.2], [KLL]).
`∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ δ_{m,N}` for unit weights `t` and orthogonal projections `P` of rank `m ≥ 1`
on `N` coordinates. -/
theorem weightedAbsSum_le_delta {m : ℕ} (hm : m ≠ 0) {t : ι → ℝ}
    (ht : IsUnitWeight t) {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    weightedAbsSum t P ≤ delta m (Fintype.card ι) := by
  classical
  have hmN := le_card_of_mem_orthProjs hP
  rw [delta_eq hm hmN]
  set N : ℝ := (Fintype.card ι : ℝ) with hN_def
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmN' : (m : ℝ) ≤ N := by rw [hN_def]; exact_mod_cast hmN
  have hN0 : 0 < N := lt_of_lt_of_le hm0 hmN'
  -- notation
  set x : ι → ℝ := fun i ↦ t i ^ 2 with hx
  set p : ι → ℝ := fun i ↦ RCLike.re (P i i) with hp
  set g : ι → ι → ℝ := fun i j ↦ ‖P i j‖ with hg
  have hx1 : ∑ i, x i = 1 := ht.sum_sq
  have hp1 : ∑ i, p i = m := sum_re_diag hP
  have hgii : ∀ i, g i i = p i := fun i ↦ hP.1.norm_diag_eq i
  have hrow : ∀ i, ∑ j, g i j ^ 2 = p i := fun i ↦ (hP.1.re_diag_eq_sum_row i).symm
  have hp0 : ∀ i, 0 ≤ p i := fun i ↦ hP.1.re_diag_nonneg i
  have hp_le : ∀ i, p i ≤ 1 := fun i ↦ hP.1.re_diag_le_one i
  have hx0 : ∀ i, 0 ≤ x i := fun i ↦ sq_nonneg _
  set X := ∑ i, x i ^ 2 with hX
  set Q := ∑ i, p i ^ 2 with hQ
  -- the diagonal and off-diagonal parts
  set S := univ.filter (fun p : ι × ι ↦ p.1 ≠ p.2) with hS
  have hsplit : weightedAbsSum t P = ∑ i, x i * p i +
      ∑ q ∈ S, (t q.1 * t q.2) * g q.1 q.2 := by
    have h := Fintype.sum_prod_eq_sum_diag_add_sum_offDiag
      (fun q : ι × ι ↦ (t q.1 * t q.2) * g q.1 q.2)
    rw [Fintype.sum_prod_type] at h; simp only at h
    change ∑ i, ∑ j, t i * t j * g i j = _
    rw [h]
    congr 1
    refine sum_congr rfl fun i _ ↦ ?_
    rw [hgii]; simp [x, sq]
  -- off-diagonal Cauchy–Schwarz
  have hoff : ∑ q ∈ S, (t q.1 * t q.2) * g q.1 q.2 ≤ √(1 - X) * √(m - Q) := by
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans_eq ?_
    congr 2
    · have h := Fintype.sum_prod_eq_sum_diag_add_sum_offDiag (fun q : ι × ι ↦ x q.1 * x q.2)
      rw [Fintype.sum_prod_type] at h; simp only at h; rw [← Finset.sum_mul_sum, hx1] at h
      have e : ∑ q ∈ S, (t q.1 * t q.2) ^ 2 = ∑ q ∈ S, x q.1 * x q.2 :=
        sum_congr rfl fun q _ ↦ by simp [x]; ring
      rw [e, hX]
      simp only [← sq] at h
      linarith
    · have h := Fintype.sum_prod_eq_sum_diag_add_sum_offDiag (fun q : ι × ι ↦ g q.1 q.2 ^ 2)
      rw [Fintype.sum_prod_type] at h; simp only at h
      have e : ∑ i, ∑ j, g i j ^ 2 = m := by
        rw [← hp1]; exact sum_congr rfl fun i _ ↦ hrow i
      simp only [hgii] at h
      rw [hQ]
      linarith
  -- the diagonal part
  have hdiag : ∑ i, x i * p i ≤ m / N + √(X - 1 / N) * √(Q - m ^ 2 / N) := by
    have e : ∑ i, x i * p i = m / N + ∑ i, (x i - 1 / N) * (p i - m / N) := by
      have : ∑ i, (x i - 1 / N) * (p i - m / N) =
          ∑ i, x i * p i - (m / N) * ∑ i, x i - (1 / N) * ∑ i, p i + N * (1 / N * (m / N)) := by
        simp only [sub_mul, mul_sub, sum_sub_distrib, ← mul_sum, ← sum_mul]
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring
      rw [this, hx1, hp1]
      field_simp
      ring
    have e1 : ∑ i, (x i - 1 / N) ^ 2 = X - 1 / N := by
      have : ∑ i, (x i - 1 / N) ^ 2 = X - 2 / N * ∑ i, x i + N * (1 / N) ^ 2 := by
        simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul]
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring
      rw [this, hx1]
      field_simp
      ring
    have e2 : ∑ i, (p i - m / N) ^ 2 = Q - m ^ 2 / N := by
      have : ∑ i, (p i - m / N) ^ 2 = Q - 2 * (m / N) * ∑ i, p i + N * (m / N) ^ 2 := by
        simp only [sub_sq, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul]
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring
      rw [this, hp1]
      field_simp
      ring
    rw [e, ← e1, ← e2]
    linarith [Real.sum_mul_le_sqrt_mul_sqrt univ (fun i ↦ x i - 1 / N) (fun i ↦ p i - m / N)]
  -- nonnegativity of the quantities under the roots
  have hX1 : 1 / N ≤ X := by
    have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := x)
    rw [hx1, card_univ] at h
    rw [div_le_iff₀ hN0]
    linarith
  have hX2 : X ≤ 1 := by
    rw [← hx1]
    exact sum_le_sum fun i _ ↦ by
      have : x i ≤ 1 := by
        rw [← hx1]
        exact single_le_sum (fun j _ ↦ hx0 j) (mem_univ i)
      nlinarith [hx0 i]
  have hQ1 : m ^ 2 / N ≤ Q := by
    have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := p)
    rw [hp1, card_univ] at h
    rw [div_le_iff₀ hN0]
    linarith
  have hQ2 : Q ≤ m := by
    rw [← hp1]
    exact sum_le_sum fun i _ ↦ by nlinarith [hp0 i, hp_le i]
  -- the two-dimensional Cauchy–Schwarz inequality
  have h2d := Real.sqrt_mul_add_sqrt_mul_le (sub_nonneg.2 hX1) (sub_nonneg.2 hQ1)
    (sub_nonneg.2 hX2) (sub_nonneg.2 hQ2)
  rw [show X - 1 / N + (1 - X) = 1 - 1 / N by ring,
    show Q - m ^ 2 / N + (m - Q) = m - m ^ 2 / N by ring] at h2d
  rw [hsplit]
  linarith

/-- **The bound of König, Lewis and Lin** ([DL, Theorem 1.2], [KLL]).
`λ_𝕜(m, N) ≤ δ_{m,N}` for `m ≠ 0`. -/
theorem maxRelProjConst_le_delta {m N : ℕ} (hm : m ≠ 0) :
    maxRelProjConst 𝕜 m N ≤ delta m N := by
  rw [maxRelProjConst_eq_clConst]
  have hδ : 0 ≤ delta m N := by
    rw [delta]; positivity
  refine clConst_le hδ fun t P ht hP ↦ ?_
  simpa using weightedAbsSum_le_delta hm ht hP

/-- `μ_𝕜(m, N) ≤ δ_{m,N}` for `m ≠ 0`. -/
theorem quasiRelConst_le_delta {m N : ℕ} (hm : m ≠ 0) :
    quasiRelConst 𝕜 (Fin N) m ≤ delta m N :=
  (quasiRelConst_le_maxRelProjConst m N).trans (maxRelProjConst_le_delta hm)

/-- **Equality for equiangular tight frames** ([DL, Theorem 1.2], (i) ⇒ (ii), (iii)). If there is
an equiangular tight frame of `N` vectors in `𝕜^m`, then `μ_𝕜(m, N) = λ_𝕜(m, N) = δ_{m,N}`. -/
theorem quasiRelConst_eq_delta_of_existsETF {m N : ℕ} (hm : m ≠ 0) (h : ExistsETF 𝕜 m N) :
    quasiRelConst 𝕜 (Fin N) m = delta m N ∧ maxRelProjConst 𝕜 m N = delta m N := by
  obtain ⟨U, hU⟩ := h
  have hP := hU.isETFProj hm
  have h1 : delta m N ≤ quasiRelConst 𝕜 (Fin N) m := by
    have := le_quasiRelConst hP.mem
    rwa [hP.absSum_div_eq hm, Fintype.card_fin] at this
  have h2 := quasiRelConst_le_delta (𝕜 := 𝕜) (N := N) hm
  have h3 := maxRelProjConst_le_delta (𝕜 := 𝕜) (N := N) hm
  have h4 := quasiRelConst_le_maxRelProjConst (𝕜 := 𝕜) m N
  exact ⟨le_antisymm h2 h1, le_antisymm h3 (h1.trans h4)⟩

end ProjectionConstants
