/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.AlmostMinimal.L1

/-!
# Blow-ups of projections and sign matrices

Let `pᵢ ≥ 1`, `i ∈ Fin m`, be integers and `d = ∑ pᵢ`. The blown-up index set `BlowupIndex p` has
`pᵢ` copies of each index `i`, so it has `d` elements. For `m × m` matrices `Q` and `S` we set,
for a copy `a` of `i` and a copy `b` of `j`,

* `blowupProj p Q a b = Qᵢⱼ / √(pᵢ pⱼ)`,
* `blowupSign p S a b = Sᵢⱼ`.

If `Q` is an orthogonal projection, then so is `blowupProj p Q`, and it has the same trace as `Q`.
If `S` is a sign matrix, then so is `blowupSign p S`. If `Q` commutes with `√Λ S √Λ`, where
`Λ = diag(p)`, then `blowupProj p Q` commutes with `blowupSign p S`. If `S ∘ Q = |Q|`, then
`blowupSign p S ∘ blowupProj p Q = |blowupProj p Q|`.

In the proof of [AMOP, Theorem 1.2] (`ProjectionConstants.AlmostMinimal.Main`), an optimal
configuration for the rational weights `pᵢ/d` is blown up in this way to a configuration on `d`
points with equal weights.

## Main definitions

* `BlowupIndex p`: the index set `Σ i : Fin m, Fin (p i)`.
* `sqrtMult p i`: the number `√pᵢ`.
* `blowupProj p Q`, `blowupSign p S`: the blow-ups of `Q` and `S`.

## Main statements

* `isStarProjection_blowupProj`, `trace_blowupProj`: the blow-up of an orthogonal projection is an
  orthogonal projection of the same trace.
* `isSignMatrix_blowupSign`: the blow-up of a sign matrix is a sign matrix.
* `blowupSign_mul_blowupProj`: commutation of the blow-ups.
* `blowupSign_mul_blowupProj_apply`: the sign pattern of the blow-ups.
* `sum_abs_blowupProj_apply`, `sum_sum_abs_blowupProj`, `sum_sq_sum_abs_blowupProj`: the column
  sums of `|blowupProj p Q|`, their sum, and the sum of their squares.

## References

* [AMOP] G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698.
-/

open Finset Matrix

namespace ProjectionConstants.AlmostMinimal

variable {m : ℕ} (p : Fin m → ℕ)

/-- The blown-up index set: `pᵢ` copies of each `i`. -/
abbrev BlowupIndex := Σ i : Fin m, Fin (p i)

/-- `sqrtMult p i = √pᵢ`. -/
noncomputable def sqrtMult (i : Fin m) : ℝ := √(p i : ℝ)

/-- The blow-up of a matrix `Q` (typically an orthogonal projection): its entry at a copy of `i`
and a copy of `j` is `Qᵢⱼ / √(pᵢ pⱼ)`. -/
noncomputable def blowupProj (Q : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (BlowupIndex p) (BlowupIndex p) ℝ :=
  Matrix.of fun a b ↦ Q a.1 b.1 / (sqrtMult p a.1 * sqrtMult p b.1)

/-- The blow-up of a matrix `S` (typically a sign matrix): its entry at a copy of `i` and a copy
of `j` is `Sᵢⱼ`. -/
def blowupSign (S : Matrix (Fin m) (Fin m) ℝ) : Matrix (BlowupIndex p) (BlowupIndex p) ℝ :=
  Matrix.of fun a b ↦ S a.1 b.1

variable {p}

/-- `BlowupIndex p` has `∑ pᵢ` elements. -/
lemma card_blowupIndex : Fintype.card (BlowupIndex p) = ∑ i, p i := by
  simp [BlowupIndex, Fintype.card_sigma]

/-- `√pᵢ > 0` if all `pᵢ ≥ 1`. -/
lemma sqrtMult_pos (hp : ∀ i, 1 ≤ p i) (i : Fin m) : 0 < sqrtMult p i := by
  unfold sqrtMult
  exact Real.sqrt_pos.2 (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (hp i)))

/-- `√pᵢ √pᵢ = pᵢ`. -/
lemma sqrtMult_mul_self (i : Fin m) : sqrtMult p i * sqrtMult p i = p i :=
  Real.mul_self_sqrt (Nat.cast_nonneg _)

/-- Sums over `BlowupIndex p` of functions of the first coordinate. -/
lemma sum_blowupIndex (f : Fin m → ℝ) : ∑ a : BlowupIndex p, f a.1 = ∑ i, (p i : ℝ) * f i := by
  rw [Fintype.sum_sigma]
  simp [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The blow-up of an orthogonal projection is an orthogonal projection. -/
lemma isStarProjection_blowupProj (hp : ∀ i, 1 ≤ p i) {Q : Matrix (Fin m) (Fin m) ℝ}
    (hQ : IsStarProjection Q) : IsStarProjection (blowupProj p Q) := by
  refine IsStarProjection.of_apply (fun a b ↦ ?_) (fun a b ↦ ?_)
  · simp only [blowupProj, Matrix.of_apply, hQ.apply_comm]
    ring
  · simp only [blowupProj, Matrix.of_apply]
    rw [sum_blowupIndex (fun k ↦ Q a.1 k / (sqrtMult p a.1 * sqrtMult p k) *
      (Q k b.1 / (sqrtMult p k * sqrtMult p b.1)))]
    have e : ∀ k, (p k : ℝ) * (Q a.1 k / (sqrtMult p a.1 * sqrtMult p k) *
          (Q k b.1 / (sqrtMult p k * sqrtMult p b.1))) =
        Q a.1 k * Q k b.1 / (sqrtMult p a.1 * sqrtMult p b.1) := by
      intro k
      have h1 := sqrtMult_pos hp k
      have h2 := sqrtMult_pos hp a.1
      have h3 := sqrtMult_pos hp b.1
      rw [← sqrtMult_mul_self k]
      field_simp
    simp only [e, ← sum_div, hQ.sum_mul_apply]

/-- The blow-up preserves the trace. -/
lemma trace_blowupProj (hp : ∀ i, 1 ≤ p i) (Q : Matrix (Fin m) (Fin m) ℝ) :
    ∑ a, blowupProj p Q a a = ∑ i, Q i i := by
  simp only [blowupProj, Matrix.of_apply]
  rw [sum_blowupIndex (fun i ↦ Q i i / (sqrtMult p i * sqrtMult p i))]
  refine sum_congr rfl fun i _ ↦ ?_
  have h1 := sqrtMult_pos hp i
  rw [sqrtMult_mul_self i]
  have : (p i : ℝ) ≠ 0 := by rw [← sqrtMult_mul_self i]; positivity
  field_simp

/-- The blow-up of a sign matrix is a sign matrix. -/
lemma isSignMatrix_blowupSign {S : Matrix (Fin m) (Fin m) ℝ} (hS : IsSignMatrix S) :
    IsSignMatrix (blowupSign p S) :=
  ⟨fun a b ↦ hS.symm a.1 b.1, fun a b ↦ hS.pm a.1 b.1, fun a ↦ hS.diag a.1⟩

/-- **Commutation of the blow-ups.** If `Q` commutes with `√Λ S √Λ`, where `Λ = diag(p)`, then
`blowupProj p Q` commutes with `blowupSign p S`. -/
lemma blowupSign_mul_blowupProj (hp : ∀ i, 1 ≤ p i) {S Q : Matrix (Fin m) (Fin m) ℝ}
    (hXQ : ∀ i j, ∑ k, sqrtMult p i * S i k * sqrtMult p k * Q k j =
      ∑ k, Q i k * (sqrtMult p k * S k j * sqrtMult p j))
    (a b : BlowupIndex p) :
    ∑ c, blowupSign p S a c * blowupProj p Q c b =
      ∑ c, blowupProj p Q a c * blowupSign p S c b := by
  simp only [blowupSign, blowupProj, Matrix.of_apply]
  rw [sum_blowupIndex (fun k ↦ S a.1 k * (Q k b.1 / (sqrtMult p k * sqrtMult p b.1))),
    sum_blowupIndex (fun k ↦ Q a.1 k / (sqrtMult p a.1 * sqrtMult p k) * S k b.1)]
  have hi := sqrtMult_pos hp a.1
  have hj := sqrtMult_pos hp b.1
  have e1 : ∀ k, (p k : ℝ) * (S a.1 k * (Q k b.1 / (sqrtMult p k * sqrtMult p b.1))) =
      (sqrtMult p a.1 * S a.1 k * sqrtMult p k * Q k b.1) /
        (sqrtMult p a.1 * sqrtMult p b.1) := by
    intro k
    have hk := sqrtMult_pos hp k
    rw [← sqrtMult_mul_self k]
    field_simp
  have e2 : ∀ k, (p k : ℝ) * (Q a.1 k / (sqrtMult p a.1 * sqrtMult p k) * S k b.1) =
      (Q a.1 k * (sqrtMult p k * S k b.1 * sqrtMult p b.1)) /
        (sqrtMult p a.1 * sqrtMult p b.1) := by
    intro k
    have hk := sqrtMult_pos hp k
    rw [← sqrtMult_mul_self k]
    field_simp
  simp only [e1, e2, ← sum_div]
  rw [hXQ]

/-- **The sign pattern of the blow-ups.** If `Sᵢⱼ Qᵢⱼ ≥ 0` for all `i, j`, then
`blowupSign p S ∘ blowupProj p Q = |blowupProj p Q|`. -/
lemma blowupSign_mul_blowupProj_apply (hp : ∀ i, 1 ≤ p i) {S Q : Matrix (Fin m) (Fin m) ℝ}
    (hS : IsSignMatrix S) (hSQ : ∀ i j, 0 ≤ S i j * Q i j) (a b : BlowupIndex p) :
    blowupSign p S a b * blowupProj p Q a b = |blowupProj p Q a b| := by
  simp only [blowupSign, blowupProj, Matrix.of_apply]
  have hi := sqrtMult_pos hp a.1
  have hj := sqrtMult_pos hp b.1
  have h1 : S a.1 b.1 * (Q a.1 b.1 / (sqrtMult p a.1 * sqrtMult p b.1)) =
      S a.1 b.1 * Q a.1 b.1 / (sqrtMult p a.1 * sqrtMult p b.1) := by ring
  rw [h1, abs_div, abs_of_pos (mul_pos hi hj)]
  congr 1
  have h2 : |S a.1 b.1 * Q a.1 b.1| = |Q a.1 b.1| := by rw [abs_mul, hS.abs_eq, one_mul]
  rw [← h2, abs_of_nonneg (hSQ _ _)]

/-- The column sums of `|blowupProj p Q|`: the column of a copy of `j` sums to
`(∑ᵢ √pᵢ |Qᵢⱼ|) / √pⱼ`. -/
lemma sum_abs_blowupProj_apply (hp : ∀ i, 1 ≤ p i) (Q : Matrix (Fin m) (Fin m) ℝ)
    (b : BlowupIndex p) :
    ∑ a, |blowupProj p Q a b| = (∑ i, sqrtMult p i * |Q i b.1|) / sqrtMult p b.1 := by
  simp only [blowupProj, Matrix.of_apply]
  rw [sum_blowupIndex (fun i ↦ |Q i b.1 / (sqrtMult p i * sqrtMult p b.1)|), sum_div]
  refine sum_congr rfl fun i _ ↦ ?_
  have hi := sqrtMult_pos hp i
  have hj := sqrtMult_pos hp b.1
  rw [abs_div, abs_of_pos (mul_pos hi hj), ← sqrtMult_mul_self i]
  field_simp

/-- The sum of the column sums of `|blowupProj p Q|` is `∑ᵢⱼ √(pᵢ pⱼ) |Qᵢⱼ|`. -/
lemma sum_sum_abs_blowupProj (hp : ∀ i, 1 ≤ p i) (Q : Matrix (Fin m) (Fin m) ℝ) :
    ∑ b, ∑ a, |blowupProj p Q a b| = ∑ i, ∑ j, sqrtMult p i * sqrtMult p j * |Q i j| := by
  simp only [sum_abs_blowupProj_apply hp]
  rw [sum_blowupIndex (fun j ↦ (∑ i, sqrtMult p i * |Q i j|) / sqrtMult p j), sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  have hj := sqrtMult_pos hp j
  rw [← sqrtMult_mul_self j]
  have e : sqrtMult p j * sqrtMult p j * ((∑ i, sqrtMult p i * |Q i j|) / sqrtMult p j) =
      sqrtMult p j * ∑ i, sqrtMult p i * |Q i j| := by
    field_simp
  rw [e, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  ring

/-- The sum of the squared column sums of `|blowupProj p Q|` is `∑ⱼ (∑ᵢ √pᵢ |Qᵢⱼ|)²`. -/
lemma sum_sq_sum_abs_blowupProj (hp : ∀ i, 1 ≤ p i) (Q : Matrix (Fin m) (Fin m) ℝ) :
    ∑ b, (∑ a, |blowupProj p Q a b|) ^ 2 = ∑ j, (∑ i, sqrtMult p i * |Q i j|) ^ 2 := by
  simp only [sum_abs_blowupProj_apply hp]
  rw [sum_blowupIndex (fun j ↦ ((∑ i, sqrtMult p i * |Q i j|) / sqrtMult p j) ^ 2)]
  refine sum_congr rfl fun j _ ↦ ?_
  have hj := sqrtMult_pos hp j
  rw [← sqrtMult_mul_self j]
  field_simp

end ProjectionConstants.AlmostMinimal
