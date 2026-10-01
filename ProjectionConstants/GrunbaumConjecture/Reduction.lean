/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.GrunbaumConjecture.Merge
import ProjectionConstants.GrunbaumConjecture.TwoGraph
import ProjectionConstants.GrunbaumConjecture.Classify
import ProjectionConstants.GrunbaumConjecture.Embed
import ProjectionConstants.GrunbaumConjecture.Exists
import ProjectionConstants.Matrix.KyFan.Fan
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Reduction to `R₅`

This file proves the reduction theorem [JFA-E, Theorem A] in the following form: if `c ≥ 1` and
`kyFanSum 2 (√D R₅ √D) ≤ c` for all weights, then `kyFanSum 2 (√D S √D) ≤ c` for all sign
matrices `S` and all weights (`kyFanSum_two_weightedSign_le_of_R5`). Since `R₃` is, up to
switching, a principal submatrix of `R₅`, this gives `Π₂ = Π(2, R₅) = max {Π(2, R₃), Π(2, R₅)}`
in the notation of [JFA] and [JFA-E], where `Π₂ = maxProjConst ℝ 2` and `Π(2, S)` is the maximum
of `kyFanSum 2 (√D S √D)` over all weights.

The proof follows [JFA-E], with a simpler Step 4, by strong induction on the number of indices.
Take a maximizer `(S, w)` (`exists_isMaximizer`). By the induction hypothesis, it has no zero
weight (`fanValue_le_kyFanSum_two_restrict`). By [JFA-E, Lemma B], it has the strict sign pattern
of vectors in the plane (`sign_mul_gram_pos`), hence `[S]` has no clique of order `4` (Step 1,
`k4Free_of_forall_mul_gram_pos`). By the cloning lemma, it has no coclique of order `4` (Step 3,
`exists_kernel_of_four` and `exists_zero_weight_of_kernel`). So every `4`-set has exactly two
coherent triples. Instead of the classification of Frankl and Füredi, Step 4 uses
`exists_embedding_A6`: `S` is, up to switching and relabelling, a principal submatrix of `A₆`.
`A₆` itself is excluded by [JFA-E, Lemma D], and its other principal submatrices are principal
submatrices of `R₅` by [JFA-E, (A1)]. Twins (Step 2) need not be excluded. A coherent triple
exists since, otherwise, `S` is switching equivalent to the all-ones matrix, so four indices would
form a coclique, and three indices give a principal submatrix of `R₅`.

## Main statements

* `exists_kernel_of_four`: four rank-one matrices `yᵢyᵢᵀ` with `yᵢ ∈ ℝ²` are linearly dependent.
* `kyFanSum_two_weightedSign_le_one_of_card_le_two`: `kyFanSum 2 (√D S √D) ≤ 1` if there are at
  most two indices.
* `kyFanSum_two_weightedSign_le_of_R5`: the reduction to `R₅` ([JFA-E, Theorem A]).

## References

* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Finset Matrix

namespace ProjectionConstants.GrunbaumConjecture

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Four rank-one matrices `yᵢyᵢᵀ` (`yᵢ = (uᵢ, vᵢ)`) in the 3-dimensional space of symmetric
`2 × 2` matrices are linearly dependent: there is `h`, supported on the range of `c` and with a
negative entry, such that `∑ᵢ hᵢ yᵢyᵢᵀ = 0`. -/
lemma exists_kernel_of_four (c : Fin 4 → ι) (hc : Function.Injective c) (u v : ι → ℝ) :
    ∃ h : ι → ℝ, ∑ i, h i * (u i * u i) = 0 ∧ ∑ i, h i * (u i * v i) = 0 ∧
      ∑ i, h i * (v i * v i) = 0 ∧ (∃ i, h i < 0) ∧ (∀ i, h i ≠ 0 → ∃ a, c a = i) := by
  set K : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun r m ↦
    if r = 0 then u (c m) * u (c m) else if r = 1 then u (c m) * v (c m)
    else if r = 2 then v (c m) * v (c m) else 0 with hK
  have hdet : K.det = 0 := Matrix.det_eq_zero_of_row_eq_zero 3 (fun m ↦ by simp [hK])
  obtain ⟨g, hg0, hg⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨m₀, hm₀⟩ : ∃ m, g m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg0 (funext hcon)
  -- from a kernel vector with a negative entry
  have key : ∀ g' : Fin 4 → ℝ, Matrix.mulVec K g' = 0 → g' m₀ < 0 → ∃ h : ι → ℝ,
      ∑ i, h i * (u i * u i) = 0 ∧ ∑ i, h i * (u i * v i) = 0 ∧
      ∑ i, h i * (v i * v i) = 0 ∧ (∃ i, h i < 0) ∧ (∀ i, h i ≠ 0 → ∃ a, c a = i) := by
    intro g' hg' hneg
    have hrow : ∀ r, ∑ m, K r m * g' m = 0 := fun r ↦ by
      have := congrFun hg' r
      simpa [Matrix.mulVec, dotProduct] using this
    have h0 := hrow 0
    have h1 := hrow 1
    have h2 := hrow 2
    simp only [hK, Matrix.of_apply] at h0 h1 h2
    simp only [↓reduceIte, Fin.isValue, one_ne_zero, Fin.reduceEq] at h0 h1 h2
    have hout : ∀ i, (¬ ∃ a, c a = i) → Function.extend c g' 0 i = 0 := by
      intro i hi; rw [Function.extend_apply' _ _ _ hi]; rfl
    refine ⟨Function.extend c g' 0, ?_, ?_, ?_, ⟨c m₀, ?_⟩, ?_⟩
    · rw [Fintype.sum_eq_sum_comp_of_injective hc]
      · simp only [hc.extend_apply]
        rw [← h0]; exact sum_congr rfl fun m _ ↦ by ring
      · intro i hi; rw [hout i hi, zero_mul]
    · rw [Fintype.sum_eq_sum_comp_of_injective hc]
      · simp only [hc.extend_apply]
        rw [← h1]; exact sum_congr rfl fun m _ ↦ by ring
      · intro i hi; rw [hout i hi, zero_mul]
    · rw [Fintype.sum_eq_sum_comp_of_injective hc]
      · simp only [hc.extend_apply]
        rw [← h2]; exact sum_congr rfl fun m _ ↦ by ring
      · intro i hi; rw [hout i hi, zero_mul]
    · rw [hc.extend_apply]; exact hneg
    · intro i hi
      by_contra hcon
      exact hi (hout i hcon)
  rcases lt_or_gt_of_ne hm₀ with hlt | hgt
  · exact key g hg hlt
  · refine key (-g) ?_ (by simp only [Pi.neg_apply]; linarith)
    rw [Matrix.mulVec_neg, hg, neg_zero]

omit [DecidableEq ι] in
/-- With at most two indices, `kyFanSum 2 (√D S √D) ≤ 1`. -/
lemma kyFanSum_two_weightedSign_le_one_of_card_le_two {S : Matrix ι ι ℝ} {w : ι → ℝ}
    (hS : IsSignMatrix S) (hw : IsWeight w) (hcard : Fintype.card ι ≤ 2) :
    kyFanSum 2 (weightedSign S w) ≤ 1 :=
  kyFanSum_two_le' zero_le_one fun _ _ huv ↦ fanValue_le_one_of_card_le_two hS hw huv hcard

end

private lemma mul_self_of_eq_one_or_eq_neg_one {x : ℝ} (h : x = 1 ∨ x = -1) : x * x = 1 := by
  rcases h with h | h <;> simp [h]

/-- **Reduction to `R₅`** ([JFA-E, Theorem A]). If `c ≥ 1` bounds `kyFanSum 2 (√D R₅ √D)` for
all weights, then `c` bounds `kyFanSum 2 (√D S √D)` for all sign matrices `S` and all weights. -/
theorem kyFanSum_two_weightedSign_le_of_R5 {c : ℝ} (hc : 1 ≤ c)
    (hR5 : ∀ w : Fin 5 → ℝ, IsWeight w → kyFanSum 2 (weightedSign R5 w) ≤ c) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ (S : Matrix ι ι ℝ) (w : ι → ℝ), IsSignMatrix S → IsWeight w →
        kyFanSum 2 (weightedSign S w) ≤ c := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard
  -- configurations with a zero weight: restrict and use the induction hypothesis
  have hzero : ∀ (S : Matrix ι ι ℝ) (w : ι → ℝ), IsSignMatrix S → IsWeight w → (∃ j, w j = 0) →
      kyFanSum 2 (weightedSign S w) ≤ c := by
    rintro S w hS hw ⟨j, hj⟩
    by_contra hcon
    push Not at hcon
    have h2 : 1 < Fintype.card ι := by
      by_contra h2
      push Not at h2
      have := kyFanSum_two_weightedSign_le_one_of_card_le_two hS hw (by omega)
      linarith
    obtain ⟨u, v, huv, hval⟩ :=
      exists_fanValue_eq_kyFanSum_two (IsSignMatrix.isHermitian_weightedSign hS w) h2
    have hmax : ∀ x y, IsOrthonormalPair x y →
        fanValue (weightedSign S w) x y ≤ fanValue (weightedSign S w) u v :=
      fun x y hxy ↦ hval ▸ fanValue_le_kyFanSum_two _ hxy
    obtain ⟨hS', hw', hle⟩ :=
      fanValue_le_kyFanSum_two_restrict hS hw hj huv hmax (by rw [hval]; linarith)
    have hcard' : Fintype.card {k // k ≠ j} = n - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard]
    have := IH (n - 1) (by omega) {k // k ≠ j} hcard' _ _ hS' hw'
    rw [hval] at hle
    linarith
  intro S₀ w₀ hS₀ hw₀
  by_cases hc2 : Fintype.card ι ≤ 2
  · linarith [kyFanSum_two_weightedSign_le_one_of_card_le_two hS₀ hw₀ hc2]
  push Not at hc2
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨S, w, hmaxSw⟩ := exists_isMaximizer (ι := ι)
  suffices hV : kyFanSum 2 (weightedSign S w) ≤ c from (hmaxSw.2.2 S₀ w₀ hS₀ hw₀).trans hV
  obtain ⟨hS, hw, hall⟩ := hmaxSw
  by_contra hgt
  push Not at hgt
  -- no zero weight
  by_cases hz : ∃ j, w j = 0
  · linarith [hzero S w hS hw hz]
  push Not at hz
  have hpos : ∀ i, 0 < w i := fun i ↦ lt_of_le_of_ne (hw.nonneg i) (hz i).symm
  obtain ⟨u, v, huv, hval⟩ :=
    exists_fanValue_eq_kyFanSum_two (IsSignMatrix.isHermitian_weightedSign hS w) (by omega)
  -- a maximizer with a zero weight is impossible
  have hnew : ∀ w', IsWeight w' → (∃ j, w' j = 0) →
      kyFanSum 2 (weightedSign S w) ≤ kyFanSum 2 (weightedSign S w') → False := by
    intro w' hw' hz' hle
    linarith [hzero S w' hS hw' hz']
  -- [JFA-E, Lemma B]: the strict sign pattern, hence no `K₄` (Step 1)
  have hsp := sign_mul_gram_pos hS hpos hc2 (fun S' hS' ↦ hall S' w hS' hw) hval huv
  have hK4 := k4Free_of_forall_mul_gram_pos hS hsp
  -- Step 3: no coclique of order `4`
  have hcoc : ∀ (c : Fin 4 → ι), Function.Injective c → ∀ ε : ι → ℝ,
      (∀ a b, S (c a) (c b) = ε (c a) * ε (c b)) → False := by
    intro c hc ε hε
    obtain ⟨h, h1, h2, h3, hneg, hsupp⟩ := exists_kernel_of_four c hc u v
    have hC : ∀ i j, h i ≠ 0 → h j ≠ 0 → S i j = ε i * ε j := by
      intro i j hi hj
      obtain ⟨a, rfl⟩ := hsupp i hi
      obtain ⟨b, rfl⟩ := hsupp j hj
      exact hε a b
    obtain ⟨w', hw', hz', hle⟩ :=
      exists_zero_weight_of_kernel ⟨hS, hw, hall⟩ hpos huv hval (by linarith) hC h1 h2 h3 hneg
    exact hnew w' hw' hz' hle
  -- the transfer to `R₅` bounds the value
  have htrans : ∀ (ψ : ι → Fin 5), Function.Injective ψ → ∀ δ : ι → ℝ, (∀ i, δ i * δ i = 1) →
      (∀ i j, S i j = δ i * δ j * R5 (ψ i) (ψ j)) → False := by
    intro ψ hψ δ hδ hSψ
    obtain ⟨hw', hle⟩ := kyFanSum_two_weightedSign_le_of_eq_mul isSignMatrix_R5 hw hψ hδ hSψ
    linarith [hR5 _ hw']
  -- there is a coherent triple: otherwise `S` is switching equivalent to `J`, so four indices
  -- would form a coclique, and three indices form a principal submatrix of `R₅`
  have hcoh : HasCoherentTriple S := by
    by_contra hno
    obtain ⟨i₀⟩ : Nonempty ι := inferInstance
    have hSε : ∀ a b, S a b = S i₀ a * S i₀ b := by
      intro a b
      have hk : ¬ IsCoherentTriple S i₀ a b := fun hk ↦ hno ⟨i₀, a, b, hk⟩
      unfold IsCoherentTriple at hk
      rcases hS.pm i₀ a with h1 | h1 <;> rcases hS.pm i₀ b with h2 | h2 <;>
        rcases hS.pm a b with h3 | h3 <;> rw [h1, h2, h3] at hk ⊢ <;> (try norm_num at hk) <;>
        norm_num
    by_cases h4 : 4 ≤ Fintype.card ι
    · obtain ⟨f⟩ : Nonempty (Fin 4 ↪ ι) :=
        Function.Embedding.nonempty_of_card_le (by simpa using h4)
      exact hcoc f f.injective (fun k ↦ S i₀ k) (fun a b ↦ hSε _ _)
    · obtain e := Fintype.equivFinOfCardEq (show Fintype.card ι = 3 by omega)
      refine htrans (fun i ↦ (![0, 1, 2] : Fin 3 → Fin 5) (e i)) (injective_012.comp e.injective)
        (fun i ↦ S i₀ i * (![1, -1, 1] : Fin 3 → ℝ) (e i)) (fun i ↦ ?_) (fun i j ↦ ?_)
      · linear_combination (![1, -1, 1] : Fin 3 → ℝ) (e i) * (![1, -1, 1] : Fin 3 → ℝ) (e i) *
          hS.mul_self_eq i₀ i + sign012_mul_self (e i)
      · rw [hSε i j]
        linear_combination (-(S i₀ i * S i₀ j)) * switch_R5_012 (e i) (e j)
  -- Step 4: `S` is a principal submatrix of `A₆`, up to switching and relabelling
  obtain ⟨ε, hε, φ, hinj, hSφ⟩ := exists_embedding_A6 hS hK4 hcoc hcoh
  have hεε : ∀ i, ε i * ε i = 1 := fun i ↦ mul_self_of_eq_one_or_eq_neg_one (hε i)
  by_cases hsurj : Function.Surjective φ
  · -- all of `A₆`: excluded by [JFA-E, Lemma D]
    refine not_signPattern_A6_of_embedding hsp (Function.surjInv hsurj)
      (fun a ↦ ε (Function.surjInv hsurj a)) (fun a ↦ hεε _) (fun a b ↦ ?_)
    rw [hSφ, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj]
  · -- a principal submatrix of a `5 × 5` principal submatrix of `A₆`, i.e. of `R₅` ([JFA-E, (A1)])
    obtain ⟨k, hk⟩ : ∃ k, ∀ i, φ i ≠ k := by
      by_contra hcon
      push Not at hcon
      exact hsurj fun k ↦ let ⟨i, hi⟩ := hcon k; ⟨i, hi⟩
    refine htrans (fun i ↦ relabelA6 k (φ i))
      (fun i j h ↦ hinj (relabelA6_injective k _ _ (hk i) (hk j) h))
      (fun i ↦ ε i * switchA6 k (φ i)) (fun i ↦ ?_) (fun i j ↦ ?_)
    · linear_combination switchA6 k (φ i) * switchA6 k (φ i) * hεε i + switchA6_mul_self k (φ i)
    · rw [hSφ, A6_eq_switch_R5 k _ _ (hk i) (hk j)]; ring

end ProjectionConstants.GrunbaumConjecture
