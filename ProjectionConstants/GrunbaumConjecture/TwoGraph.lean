/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.GrunbaumConjecture.SignPattern
import ProjectionConstants.GrunbaumConjecture.A6

/-!
# Two-graphs of sign matrices

The two-graph `[S]` of a sign matrix `S` consists of the coherent triples `{i, j, k}`, i.e. those
with `sᵢⱼ sᵢₖ sⱼₖ = -1`; switching `S` does not change it. A clique of order `4` of `[S]` is a set
of four indices all of whose triples are coherent. This file defines these notions and proves two
consequences of the strict sign pattern `sᵢⱼ ⟨yᵢ, yⱼ⟩ > 0` of vectors `yᵢ = (uᵢ, vᵢ)` in the
plane (see `sign_mul_gram_pos`), which are used in Steps 1 and 4 of the proof of
[JFA-E, Theorem A]: `[S]` has no clique of order `4`, and `S` is not, up to switching and
relabelling, the matrix `A₆`.

## Main definitions

* `IsCoherentTriple S i j k`: `sᵢⱼ sᵢₖ sⱼₖ = -1`.
* `K4Free S`: `[S]` has no clique of order `4`.
* `HasCoherentTriple S`: `[S]` has a coherent triple.

## Main statements

* `false_of_four_pairwise_obtuse`: four vectors in the plane cannot be pairwise obtuse.
* `k4Free_of_forall_mul_gram_pos`: a sign pattern of vectors in the plane is `K₄`-free
  ([JFA-E, Lemma B(d)] for `n = 2`, as in the proof of [JFA, Theorem 1.2]).
* `not_signPattern_A6_of_embedding`: [JFA-E, Lemma D] up to switching and relabelling.

## References

* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Finset Matrix

namespace ProjectionConstants.GrunbaumConjecture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `{i, j, k}` is coherent: `sᵢⱼ sᵢₖ sⱼₖ = -1`. -/
def IsCoherentTriple (S : Matrix ι ι ℝ) (i j k : ι) : Prop := S i j * S i k * S j k = -1

/-- The two-graph `[S]` is `K₄`-free: there are no four distinct indices all of whose triples are
coherent. -/
def K4Free (S : Matrix ι ι ℝ) : Prop :=
  ∀ a b c d : ι, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬ (IsCoherentTriple S a b c ∧ IsCoherentTriple S a b d ∧ IsCoherentTriple S a c d ∧
      IsCoherentTriple S b c d)

/-- The two-graph `[S]` has a coherent triple. -/
def HasCoherentTriple (S : Matrix ι ι ℝ) : Prop := ∃ i j k, IsCoherentTriple S i j k

/-- Four vectors in the plane cannot be pairwise obtuse. -/
lemma false_of_four_pairwise_obtuse (x0 y0 x1 y1 x2 y2 x3 y3 : ℝ) (h01 : x0 * x1 + y0 * y1 < 0)
    (h02 : x0 * x2 + y0 * y2 < 0) (h03 : x0 * x3 + y0 * y3 < 0) (h12 : x1 * x2 + y1 * y2 < 0)
    (h13 : x1 * x3 + y1 * y3 < 0) (h23 : x2 * x3 + y2 * y3 < 0) : False := by
  have hr : 0 < x0 ^ 2 + y0 ^ 2 := by
    by_contra hcon
    have hx : x0 = 0 := by nlinarith [sq_nonneg x0, sq_nonneg y0]
    have hy : y0 = 0 := by nlinarith [sq_nonneg x0, sq_nonneg y0]
    rw [hx, hy] at h01
    linarith
  -- `aₘ = ⟨uₘ, u₀⟩ < 0` and `bₘ = det(u₀, uₘ)`; then `|u₀|² ⟨uₘ, uₘ'⟩ = aₘ aₘ' + bₘ bₘ'`
  have key : ∀ xa ya xb yb : ℝ, xa * x0 + ya * y0 < 0 → xb * x0 + yb * y0 < 0 →
      xa * xb + ya * yb < 0 → (x0 * ya - y0 * xa) * (x0 * yb - y0 * xb) < 0 := by
    intro xa ya xb yb ha hb hab
    have lag : (xa * xb + ya * yb) * (x0 ^ 2 + y0 ^ 2) =
        (xa * x0 + ya * y0) * (xb * x0 + yb * y0) +
          (x0 * ya - y0 * xa) * (x0 * yb - y0 * xb) := by
      ring
    have h1 : (xa * xb + ya * yb) * (x0 ^ 2 + y0 ^ 2) < 0 := mul_neg_of_neg_of_pos hab hr
    have h2 : 0 < (xa * x0 + ya * y0) * (xb * x0 + yb * y0) := mul_pos_of_neg_of_neg ha hb
    linarith
  have e1 : x1 * x0 + y1 * y0 < 0 := by linarith
  have e2 : x2 * x0 + y2 * y0 < 0 := by linarith
  have e3 : x3 * x0 + y3 * y0 < 0 := by linarith
  have b12 := key x1 y1 x2 y2 e1 e2 h12
  have b13 := key x1 y1 x3 y3 e1 e3 h13
  have b23 := key x2 y2 x3 y3 e2 e3 h23
  nlinarith [mul_pos_of_neg_of_neg b12 b13, sq_nonneg (x0 * y1 - y0 * x1)]

omit [DecidableEq ι] [Fintype ι] in
/-- **[JFA-E, Lemma B(d)]** for `n = 2`: a sign pattern of vectors in the plane is `K₄`-free. -/
theorem k4Free_of_forall_mul_gram_pos {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {u v : ι → ℝ}
    (h : ∀ i j, 0 < S i j * (u i * u j + v i * v j)) : K4Free S := by
  rintro a b c d hab hac had hbc hbd hcd ⟨habc, habd, hacd, -⟩
  have hsq : ∀ i j, S i j * S i j = 1 := hS.mul_self_eq
  -- coherence of `{a, m, m'}` gives `sₐₘ sₐₘ' = - sₘₘ'`
  have ebc : S a b * S a c = - S b c := by
    unfold IsCoherentTriple at habc
    linear_combination S b c * habc - S a b * S a c * hsq b c
  have ebd : S a b * S a d = - S b d := by
    unfold IsCoherentTriple at habd
    linear_combination S b d * habd - S a b * S a d * hsq b d
  have ecd : S a c * S a d = - S c d := by
    unfold IsCoherentTriple at hacd
    linear_combination S c d * hacd - S a c * S a d * hsq c d
  -- after switching, the vectors `u_a, -s_ab u_b, -s_ac u_c, -s_ad u_d` are pairwise obtuse
  apply false_of_four_pairwise_obtuse (u a) (v a) (-S a b * u b) (-S a b * v b) (-S a c * u c)
    (-S a c * v c) (-S a d * u d) (-S a d * v d)
  · linarith [h a b]
  · linarith [h a c]
  · linarith [h a d]
  · have : (-S a b * u b) * (-S a c * u c) + (-S a b * v b) * (-S a c * v c) =
        -(S b c * (u b * u c + v b * v c)) := by
      linear_combination (u b * u c + v b * v c) * ebc
    rw [this]; linarith [h b c]
  · have : (-S a b * u b) * (-S a d * u d) + (-S a b * v b) * (-S a d * v d) =
        -(S b d * (u b * u d + v b * v d)) := by
      linear_combination (u b * u d + v b * v d) * ebd
    rw [this]; linarith [h b d]
  · have : (-S a c * u c) * (-S a d * u d) + (-S a c * v c) * (-S a d * v d) =
        -(S c d * (u c * u d + v c * v d)) := by
      linear_combination (u c * u d + v c * v d) * ecd
    rw [this]; linarith [h c d]

omit [DecidableEq ι] [Fintype ι] in
/-- **[JFA-E, Lemma D]** up to switching and relabelling: `A₆` is not the sign pattern of vectors
in the plane. -/
theorem not_signPattern_A6_of_embedding {S : Matrix ι ι ℝ} {u v : ι → ℝ}
    (h : ∀ i j, 0 < S i j * (u i * u j + v i * v j)) (ψ : Fin 6 → ι) (δ : Fin 6 → ℝ)
    (hδ : ∀ a, δ a * δ a = 1) (hψ : ∀ a b, S (ψ a) (ψ b) = δ a * δ b * A6 a b) : False := by
  apply not_signPattern_A6 (fun a ↦ δ a * u (ψ a)) (fun a ↦ δ a * v (ψ a))
  intro a b
  have e : A6 a b = δ a * δ b * S (ψ a) (ψ b) := by
    rw [hψ]
    linear_combination (-(A6 a b) * δ b * δ b) * hδ a + (-(A6 a b)) * hδ b
  have := h (ψ a) (ψ b)
  calc 0 < S (ψ a) (ψ b) * (u (ψ a) * u (ψ b) + v (ψ a) * v (ψ b)) := this
    _ = A6 a b * (δ a * u (ψ a) * (δ b * u (ψ b)) + δ a * v (ψ a) * (δ b * v (ψ b))) := by
        rw [e]
        linear_combination (-(S (ψ a) (ψ b) * (u (ψ a) * u (ψ b) + v (ψ a) * v (ψ b))) * δ b * δ b)
          * hδ a + (-(S (ψ a) (ψ b) * (u (ψ a) * u (ψ b) + v (ψ a) * v (ψ b)))) * hδ b

end ProjectionConstants.GrunbaumConjecture
