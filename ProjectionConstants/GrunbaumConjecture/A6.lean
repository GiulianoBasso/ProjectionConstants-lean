/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The matrix `A₆` is not a sign pattern of vectors in the plane

The sign matrix `A₆ = 𝟙₆ + S(K₁ ∪ C₅)` of [JFA, Section 4.1], where `S(G)` is the Seidel matrix
of the graph `G`, is indexed here by `Fin 6 = {0, …, 5}`: the vertex `0` is isolated, and
`1–4–3–2–5–1` is the `5`-cycle. We prove [JFA-E, Lemma D]: there are no six vectors
`uᵢ = (xᵢ, yᵢ) ∈ ℝ²` such that `A₆ i j ⟨uᵢ, uⱼ⟩ > 0` for all `i, j` (`not_signPattern_A6`). This
excludes `A₆` in Step 4 of the proof of [JFA-E, Theorem A]; the version up to switching and
relabelling is `not_signPattern_A6_of_embedding` in
`ProjectionConstants.GrunbaumConjecture.TwoGraph`.

Since the vertex `0` is isolated, every `uⱼ` makes an acute angle with `u₀`. So the vectors `uⱼ`
lie in an open half-plane, and they can be compared by their slopes `σⱼ` relative to `u₀`. On
`{1, …, 5}`, the pairs with positive inner product form the `5`-cycle `1–2–4–5–3–1`. The vertex of
this cycle with the smallest slope gives a contradiction: its two neighbours make an acute angle
with each other (`acute_of_min`), although they are not adjacent.

## Main definitions

* `A6`: the matrix `A₆`.

## Main statements

* `not_signPattern_A6`: `A₆` is not the sign pattern of six vectors in the plane
  ([JFA-E, Lemma D]).

## References

* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Matrix

namespace ProjectionConstants.GrunbaumConjecture

/-- The sign matrix `A₆ = 𝟙₆ + S(K₁ ∪ C₅)` of [JFA, Section 4.1], with indices `0, …, 5`. -/
def A6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1,  1,  1,  1,  1,  1;
     1,  1,  1,  1, -1, -1;
     1,  1,  1, -1,  1, -1;
     1,  1, -1,  1, -1,  1;
     1, -1,  1, -1,  1,  1;
     1, -1, -1,  1,  1,  1]

/-- The key inequality: if `a` is the smallest of three slopes `a, b, c` and the directions with
slopes `b` and `c` both make an acute angle with the direction of slope `a`, then they make an
acute angle with each other. -/
lemma acute_of_min {a b c : ℝ} (hb : a ≤ b) (hc : a ≤ c) (h1 : 0 < 1 + a * b)
    (h2 : 0 < 1 + a * c) : 0 < 1 + b * c := by
  rcases lt_or_ge 0 c with hc0 | hc0
  · nlinarith [mul_nonneg (sub_nonneg.2 hb) hc0.le]
  rcases lt_or_ge 0 b with hb0 | hb0
  · nlinarith [mul_nonneg (sub_nonneg.2 hc) hb0.le]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos hb0 hc0]

/-- **[JFA-E, Lemma D].** `A₆` is not the sign pattern `(sgn⟨uᵢ, uⱼ⟩)ᵢⱼ` of six vectors
`uᵢ = (xᵢ, yᵢ) ∈ ℝ²` with pairwise non-zero inner products. -/
theorem not_signPattern_A6 (x y : Fin 6 → ℝ)
    (h : ∀ i j, 0 < A6 i j * (x i * x j + y i * y j)) : False := by
  -- coordinates relative to `u₀`: `aⱼ = ⟨uⱼ, u₀⟩`, `bⱼ = det(u₀, uⱼ)`, slope `σⱼ = bⱼ / aⱼ`
  set a : Fin 6 → ℝ := fun j ↦ x j * x 0 + y j * y 0 with ha_def
  set b : Fin 6 → ℝ := fun j ↦ x 0 * y j - y 0 * x j with hb_def
  set σ : Fin 6 → ℝ := fun j ↦ b j / a j with hσ_def
  -- vertex `0` is isolated: `⟨u₀, uⱼ⟩ > 0` for all `j`
  have hrow : ∀ j, A6 0 j = 1 := by intro j; fin_cases j <;> simp [A6]
  have ha : ∀ j, 0 < a j := by
    intro j
    have := h 0 j
    rw [hrow j, one_mul] at this
    simp only [ha_def]
    linarith
  have hr : 0 < x 0 ^ 2 + y 0 ^ 2 := by
    have := ha 0
    simp only [ha_def] at this
    nlinarith
  -- `⟨uᵢ, uⱼ⟩ |u₀|² = aᵢ aⱼ (1 + σᵢ σⱼ)`
  have hq : ∀ i j, (x i * x j + y i * y j) * (x 0 ^ 2 + y 0 ^ 2) =
      a i * a j * (1 + σ i * σ j) := by
    intro i j
    have hai := (ha i).ne'
    have haj := (ha j).ne'
    simp only [hσ_def]
    field_simp
    simp only [ha_def, hb_def]
    ring
  -- so the sign of `1 + σᵢ σⱼ` is the entry `A₆ i j`
  have key : ∀ i j, 0 < A6 i j * (1 + σ i * σ j) := by
    intro i j
    have h1 : 0 < A6 i j * (x i * x j + y i * y j) * (x 0 ^ 2 + y 0 ^ 2) := mul_pos (h i j) hr
    rw [mul_assoc, hq i j] at h1
    have h2 : 0 < A6 i j * (1 + σ i * σ j) * (a i * a j) := by linarith
    exact pos_of_mul_pos_left h2 (mul_pos (ha i) (ha j)).le
  -- the graph `{i, j : A₆ i j = 1}` on `{1, …, 5}` is the 5-cycle `1–2–4–5–3–1`
  have e12 : 0 < 1 + σ 1 * σ 2 := by simpa [A6] using key 1 2
  have e13 : 0 < 1 + σ 1 * σ 3 := by simpa [A6] using key 1 3
  have e24 : 0 < 1 + σ 2 * σ 4 := by simpa [A6] using key 2 4
  have e35 : 0 < 1 + σ 3 * σ 5 := by simpa [A6] using key 3 5
  have e45 : 0 < 1 + σ 4 * σ 5 := by simpa [A6] using key 4 5
  have n23 : 1 + σ 2 * σ 3 < 0 := by have := key 2 3; simp [A6] at this; linarith
  have n14 : 1 + σ 1 * σ 4 < 0 := by have := key 1 4; simp [A6] at this; linarith
  have n25 : 1 + σ 2 * σ 5 < 0 := by have := key 2 5; simp [A6] at this; linarith
  have n34 : 1 + σ 3 * σ 4 < 0 := by have := key 3 4; simp [A6] at this; linarith
  have n15 : 1 + σ 1 * σ 5 < 0 := by have := key 1 5; simp [A6] at this; linarith
  -- a vertex of the 5-cycle cannot have the smallest slope among itself and its two neighbours
  have v1 : σ 2 < σ 1 ∨ σ 3 < σ 1 := by
    by_contra hcon
    push Not at hcon
    have := acute_of_min hcon.1 hcon.2 e12 e13
    linarith
  have v2 : σ 1 < σ 2 ∨ σ 4 < σ 2 := by
    by_contra hcon
    push Not at hcon
    have := acute_of_min hcon.1 hcon.2 (by linarith [e12, mul_comm (σ 1) (σ 2)]) e24
    linarith
  have v4 : σ 2 < σ 4 ∨ σ 5 < σ 4 := by
    by_contra hcon
    push Not at hcon
    have := acute_of_min hcon.1 hcon.2 (by linarith [e24, mul_comm (σ 2) (σ 4)]) e45
    linarith
  have v5 : σ 4 < σ 5 ∨ σ 3 < σ 5 := by
    by_contra hcon
    push Not at hcon
    have := acute_of_min hcon.1 hcon.2 (by linarith [e45, mul_comm (σ 4) (σ 5)])
      (by linarith [e35, mul_comm (σ 3) (σ 5)])
    linarith [mul_comm (σ 3) (σ 4)]
  have v3 : σ 5 < σ 3 ∨ σ 1 < σ 3 := by
    by_contra hcon
    push Not at hcon
    have := acute_of_min hcon.1 hcon.2 e35 (by linarith [e13, mul_comm (σ 1) (σ 3)])
    linarith [mul_comm (σ 1) (σ 5)]
  -- the vertex with the smallest slope gives a contradiction
  rcases v1 with h1 | h1 <;> rcases v2 with h2 | h2 <;> rcases v3 with h3 | h3 <;>
    rcases v4 with h4 | h4 <;> rcases v5 with h5 | h5 <;> linarith

end ProjectionConstants.GrunbaumConjecture
