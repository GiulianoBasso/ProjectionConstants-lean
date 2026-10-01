/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.GrunbaumConjecture.Reduction
import ProjectionConstants.GrunbaumConjecture.R5.Eigenvalues
import ProjectionConstants.ChalmersLewicki.SignMatrix

/-!
# `Π₂ = 4/3`

In the notation of [JFA], `Π₂ = λ_ℝ(2)` is `maxProjConst ℝ 2`. By the formula of Chalmers and
Lewicki in terms of sign matrices ([JFA, Theorem 2.1], `maxProjConst_real_eq_sSup`), `Π₂` is the
supremum of the values `kyFanSum 2 (√D S √D)` over all dimensions `d`, all `d × d` sign matrices
`S` and all weights `D = diag(w)` (`signMatrixValues 2`); here `kyFanSum 2 A` is the sum of the
two largest eigenvalues of the symmetric matrix `A`. This file completes the proof of
[JFA-E, Corollary G]: `Π₂ = 4/3`, which is Grünbaum's conjecture `λ_ℝ(2) = 4/3`, a theorem of
Chalmers and Lewicki [CL]. The proof combines:

* [JFA-E, Proposition F]: `kyFanSum 2 (√D R₅ √D) ≤ 4/3` for all weights, with strict inequality
  if all weights are positive;
* `R₃ = 2 𝟙₃ - J₃` is, up to switching, a principal submatrix of `R₅`, and
  `kyFanSum 2 (⅓ R₃) = 4/3`;
* by the reduction [JFA-E, Theorem A] (`kyFanSum_two_weightedSign_le_of_R5`), every value
  `kyFanSum 2 (√D S √D)` is at most `4/3`.

This proof of Grünbaum's conjecture is independent of the proof via equiangular tight frames of
[DL] (`ProjectionConstants.maxProjConst_real_two`).

## Main definitions

* `R3`: the sign matrix `R₃ = 2 𝟙₃ - J₃`.

## Main statements

* `kyFanSum_two_weightedSign_R5_le`, `kyFanSum_two_weightedSign_R5_lt`,
  `isGreatest_kyFanSum_two_weightedSign_R5`: [JFA-E, Proposition F].
* `kyFanSum_two_weightedSign_R3`: `kyFanSum 2 (⅓ R₃) = 4/3`.
* `ProjectionConstants.kyFanSum_two_weightedSign_le`: `kyFanSum 2 (√D S √D) ≤ 4/3` for every sign
  matrix `S` and every weight.
* `ProjectionConstants.isGreatest_signMatrixValues_two`: `4/3` is the greatest element of
  `signMatrixValues 2` ([JFA-E, Corollary G]).
* `ProjectionConstants.GrunbaumConjecture.maxProjConst_real_two`: Grünbaum's conjecture
  `maxProjConst ℝ 2 = 4/3`.

## References

* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
* [CL] B. L. Chalmers, G. Lewicki, *A proof of the Grünbaum conjecture*.
* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
-/

open Finset Matrix

namespace ProjectionConstants.GrunbaumConjecture

/-- **[JFA-E, Proposition F]**, the upper bound: `kyFanSum 2 (√D R₅ √D) ≤ 4/3`. -/
theorem kyFanSum_two_weightedSign_R5_le {w : Fin 5 → ℝ} (hw : IsWeight w) :
    kyFanSum 2 (weightedSign R5 w) ≤ 4 / 3 := by
  have hA := isHermitian_scaledR5 fun i ↦ √(w i)
  refine kyFanSum_two_le_of_pairs hA (by simp) fun i j hij ↦ ?_
  exact (eigenvalues_add_le_four_thirds hA hw.isUnitWeight_sqrt.sum_sq i j hij).1

/-- **[JFA-E, Proposition F]**, strict form: `kyFanSum 2 (√D R₅ √D) < 4/3` if all weights are
positive. -/
theorem kyFanSum_two_weightedSign_R5_lt {w : Fin 5 → ℝ} (hw : IsWeight w)
    (hpos : ∀ i, 0 < w i) : kyFanSum 2 (weightedSign R5 w) < 4 / 3 := by
  have hA := isHermitian_scaledR5 fun i ↦ √(w i)
  obtain ⟨a, b, hab, ha, hb⟩ := exists_top_two hA.eigenvalues (by simp)
  change kyFanSum 2 (scaledR5 fun i ↦ √(w i)) < 4 / 3
  rw [kyFanSum_two_eq hA hab ha hb]
  exact (eigenvalues_add_le_four_thirds hA hw.isUnitWeight_sqrt.sum_sq a b hab).2
    fun k ↦ (Real.sqrt_pos.2 (hpos k)).ne'

/-- The sign matrix `R₃ = 2 𝟙₃ - J₃`. -/
def R3 : Matrix (Fin 3) (Fin 3) ℝ := !![1, -1, -1; -1, 1, -1; -1, -1, 1]

/-- `R₃` is a sign matrix. -/
lemma isSignMatrix_R3 : IsSignMatrix R3 := by
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun a ↦ ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [R3]
  · fin_cases a <;> fin_cases b <;> simp [R3]
  · fin_cases a <;> simp [R3]

/-- The uniform weight `(1/3, 1/3, 1/3)`. -/
lemma isWeight_const_third : IsWeight (fun _ : Fin 3 ↦ (1 : ℝ) / 3) :=
  ⟨fun _ ↦ by norm_num, by simp⟩

/-- The lower bound `kyFanSum 2 (⅓ R₃) ≥ 4/3`, since `R₃` has the eigenvalue `2` twice. -/
theorem le_kyFanSum_two_weightedSign_R3 : 4 / 3 ≤ kyFanSum 2 (weightedSign R3 fun _ ↦ 1 / 3) := by
  set a := √2 with ha
  set b := √6 with hb
  have ha2 : a * a = 2 := Real.mul_self_sqrt (by norm_num)
  have hb2 : b * b = 6 := Real.mul_self_sqrt (by norm_num)
  have ha0 : a ≠ 0 := by rw [ha]; positivity
  have hb0 : b ≠ 0 := by rw [hb]; positivity
  have h3 : √(1 / 3 : ℝ) * √(1 / 3) = 1 / 3 := Real.mul_self_sqrt (by norm_num)
  set u : Fin 3 → ℝ := ![1 / a, -1 / a, 0] with hu
  set v : Fin 3 → ℝ := ![1 / b, 1 / b, -2 / b] with hv
  have hon : IsOrthonormalPair u v := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [dotProduct, Fin.sum_univ_three, hu]
      simp
      field_simp
      linarith
    · simp only [dotProduct, Fin.sum_univ_three, hv]
      simp
      field_simp
      linarith
    · simp only [dotProduct, Fin.sum_univ_three, hu, hv]
      simp
      field_simp
      ring
  have hval : fanValue (weightedSign R3 fun _ ↦ 1 / 3) u v = 4 / 3 := by
    simp only [fanValue, dotProduct_mulVec_self_eq_sum, Fin.sum_univ_three, weightedSign,
      Matrix.of_apply, hu, hv, R3]
    simp
    field_simp
    have e3 : √(3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have ea : a ^ 2 = 2 := by rw [sq]; exact ha2
    have eb : b ^ 2 = 6 := by rw [sq]; exact hb2
    rw [e3, ea, eb]
    norm_num
  rw [← hval]
  exact fanValue_le_kyFanSum_two _ hon

/-- `R₃` is the principal submatrix of `R₅` on the coherent triple `{0, 1, 3}`, up to switching. -/
lemma R3_eq_switch_R5 (a b : Fin 3) :
    R3 a b = (![1, 1, -1] : Fin 3 → ℝ) a * (![1, 1, -1] : Fin 3 → ℝ) b *
      R5 ((![0, 1, 3] : Fin 3 → Fin 5) a) ((![0, 1, 3] : Fin 3 → Fin 5) b) := by
  fin_cases a <;> fin_cases b <;> simp [R3, R5]

/-- `kyFanSum 2 (√D R₃ √D) ≤ 4/3`, by transfer to `R₅`. -/
theorem kyFanSum_two_weightedSign_R3_le {w : Fin 3 → ℝ} (hw : IsWeight w) :
    kyFanSum 2 (weightedSign R3 w) ≤ 4 / 3 := by
  obtain ⟨hw', hle⟩ := kyFanSum_two_weightedSign_le_of_eq_mul isSignMatrix_R5 hw injective_013
    (ε := ![1, 1, -1]) (fun i ↦ by fin_cases i <;> simp) R3_eq_switch_R5
  exact hle.trans (kyFanSum_two_weightedSign_R5_le hw')

/-- `kyFanSum 2 (⅓ R₃) = 4/3`. -/
theorem kyFanSum_two_weightedSign_R3 : kyFanSum 2 (weightedSign R3 fun _ ↦ 1 / 3) = 4 / 3 :=
  le_antisymm (kyFanSum_two_weightedSign_R3_le isWeight_const_third)
    le_kyFanSum_two_weightedSign_R3

/-- **[JFA-E, Proposition F]**: the maximum of `kyFanSum 2 (√D R₅ √D)` over all weights is
`4/3`. -/
theorem isGreatest_kyFanSum_two_weightedSign_R5 :
    IsGreatest ((fun w ↦ kyFanSum 2 (weightedSign R5 w)) '' {w | IsWeight w}) (4 / 3) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨hw', hle⟩ := kyFanSum_two_weightedSign_le_of_eq_mul isSignMatrix_R5
      isWeight_const_third injective_013 (ε := ![1, 1, -1]) (fun i ↦ by fin_cases i <;> simp)
      R3_eq_switch_R5
    exact ⟨_, hw', le_antisymm (kyFanSum_two_weightedSign_R5_le hw')
      ((le_of_eq kyFanSum_two_weightedSign_R3.symm).trans hle)⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact kyFanSum_two_weightedSign_R5_le hw

end ProjectionConstants.GrunbaumConjecture

namespace ProjectionConstants

open GrunbaumConjecture

/-- **[JFA-E, Corollary G]**, the upper bound: `kyFanSum 2 (√D S √D) ≤ 4/3` for every sign
matrix `S` and every weight `w`. -/
theorem kyFanSum_two_weightedSign_le {ι : Type} [Fintype ι] {S : Matrix ι ι ℝ}
    (hS : IsSignMatrix S) {w : ι → ℝ} (hw : IsWeight w) : kyFanSum 2 (weightedSign S w) ≤ 4 / 3 :=
  kyFanSum_two_weightedSign_le_of_R5 (by norm_num) (fun _ hw ↦ kyFanSum_two_weightedSign_R5_le hw)
    _ ι rfl S w hS hw

/-- **[JFA-E, Corollary G].** The number `4/3` is the greatest value of
`kyFanSum 2 (√D S √D)` over all `d`, `S ∈ 𝒮_d` and `D ∈ 𝒟_d`. -/
theorem isGreatest_signMatrixValues_two : IsGreatest (signMatrixValues 2) (4 / 3) := by
  refine ⟨⟨3, R3, _, isSignMatrix_R3, isWeight_const_third, kyFanSum_two_weightedSign_R3⟩, ?_⟩
  rintro x ⟨d, S, w, hS, hw, rfl⟩
  exact kyFanSum_two_weightedSign_le hS hw

end ProjectionConstants

namespace ProjectionConstants.GrunbaumConjecture

/-- **Grünbaum's conjecture** `λ_ℝ(2) = 4/3`, via Ky Fan's maximum principle and the corrected
argument of [JFA-E] for [JFA] ([JFA-E, Corollary G]). This proof is independent of the proof via
equiangular tight frames of [DL] (`ProjectionConstants.maxProjConst_real_two`). -/
theorem maxProjConst_real_two : maxProjConst ℝ 2 = 4 / 3 := by
  rw [maxProjConst_real_eq_sSup (by norm_num)]
  exact isGreatest_signMatrixValues_two.csSup_eq

end ProjectionConstants.GrunbaumConjecture
