/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.GrunbaumConjecture.SignPattern
import Mathlib.Algebra.BigOperators.Field

/-!
# The cloning lemma

A sign matrix `S` and a weight `w` form a maximizer (`IsMaximizer S w`) if they maximize
`kyFanSum 2 (√D S √D)` over all sign matrices and all weights on `ι`, where `D = diag(w)`. This
file proves the cloning lemma of [KMMP, Claim 2.4] ([JFA-E, Lemma C]), combined with the argument
of Step 3 of the proof of [JFA-E, Theorem A], which excludes cocliques of order `4`.

Let `(S, w)` be a maximizer with `w > 0`, and let `u, v` be an orthonormal pair with
`fanValue M u v = kyFanSum 2 M > 0` for `M = √D S √D`. Let `h : ι → ℝ` have a negative entry, let
`S` be switching equivalent to the all-ones matrix on the support of `h`, and let
`∑ᵢ hᵢ yᵢyᵢᵀ = 0` for `yᵢ = (uᵢ, vᵢ)`. Then the weights can be shifted along `h` until one of them
vanishes, without decreasing `kyFanSum 2` (`exists_zero_weight_of_kernel`). For `c = 1 + t h`,
the new weights are `cₖ wₖ / ∑ₗ cₗ wₗ`, and the vectors `√cₖ uₖ, √cₖ vₖ` form an orthonormal pair
(`fanValue_clone` computes its value). This value is `(kyFanSum 2 M + t² Q) / (1 + t b)` with
`Q ≥ 0` and `b = ∑ₖ hₖ wₖ`, since the linear term vanishes by the stationarity of `u, v`.
Maximality for small `|t|` gives `Q = 0` and `b = 0`, and so the value `kyFanSum 2 M` is kept up
to `t = -1 / minₖ hₖ`, where a weight vanishes.

## Main definitions

* `IsMaximizer S w`: `(S, w)` maximizes `kyFanSum 2 (√D S √D)` over all sign matrices and all
  weights.

## Main statements

* `fanValue_clone`: the value of the cloned configuration.
* `exists_zero_weight_of_kernel`: the weights can be shifted along `h` until one of them vanishes.

## References

* [KMMP] H. Kumar, B. Mohar, S. A. Mojallal, S. Pragada, *Stability of maximal relative
  projection constants*, arXiv:2609.03200.
* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Finset Matrix

namespace ProjectionConstants.GrunbaumConjecture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sign matrix `S` and the weight `w` maximize `kyFanSum 2 (√D S √D)` over all sign
matrices and all weights on `ι`. -/
def IsMaximizer (S : Matrix ι ι ℝ) (w : ι → ℝ) : Prop :=
  IsSignMatrix S ∧ IsWeight w ∧
    ∀ (S' : Matrix ι ι ℝ) (w' : ι → ℝ), IsSignMatrix S' → IsWeight w' →
      kyFanSum 2 (weightedSign S' w') ≤ kyFanSum 2 (weightedSign S w)

omit [DecidableEq ι] in
/-- A maximizer `(S, w)` maximizes over the sign matrices for its own weights `w`. -/
lemma IsMaximizer.isMaxSign {S : Matrix ι ι ℝ} {w : ι → ℝ} (h : IsMaximizer S w) : IsMaxSign S w :=
  fun S' hS' ↦ h.2.2 S' w hS' h.2.1

private lemma sqrt_div_mul_sqrt {c w Z : ℝ} (hc : 0 ≤ c) (hw : 0 ≤ w) :
    √(c * w / Z) * √c = c * √w / √Z := by
  rw [Real.sqrt_div (mul_nonneg hc hw), Real.sqrt_mul hc, div_mul_eq_mul_div]
  congr 1
  rw [mul_comm (√c) (√w), mul_assoc, Real.mul_self_sqrt hc, mul_comm]

omit [DecidableEq ι] in
/-- The value of the cloned configuration: for the weights `cₖ wₖ / ∑ₗ cₗ wₗ`, the value of the
vectors `√cₖ uₖ, √cₖ vₖ` is `∑ₖₗ cₖ cₗ √wₖ √wₗ sₖₗ (uₖuₗ + vₖvₗ) / ∑ₗ cₗ wₗ`. -/
lemma fanValue_clone (S : Matrix ι ι ℝ) (w u v c : ι → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hw : ∀ k, 0 ≤ w k) (hZ : 0 < ∑ k, c k * w k) :
    fanValue (weightedSign S (fun k ↦ c k * w k / ∑ l, c l * w l)) (fun k ↦ √(c k) * u k)
        (fun k ↦ √(c k) * v k) =
      (∑ k, ∑ l, c k * c l * (√(w k) * √(w l) * S k l * (u k * u l + v k * v l))) /
        ∑ l, c l * w l := by
  set Z := ∑ l, c l * w l with hZdef
  rw [fanValue_eq_sum, sum_div]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [sum_div]
  refine sum_congr rfl fun l _ ↦ ?_
  simp only [weightedSign, Matrix.of_apply]
  have hk := sqrt_div_mul_sqrt (Z := Z) (hc k) (hw k)
  have hl := sqrt_div_mul_sqrt (Z := Z) (hc l) (hw l)
  have hZZ : √Z * √Z = Z := Real.mul_self_sqrt hZ.le
  have hZ0 : √Z ≠ 0 := (Real.sqrt_pos.2 hZ).ne'
  calc √(c k * w k / Z) * S k l * √(c l * w l / Z)
        * (√(c k) * u k * (√(c l) * u l) + √(c k) * v k * (√(c l) * v l))
      = (√(c k * w k / Z) * √(c k)) * (√(c l * w l / Z) * √(c l)) * S k l
          * (u k * u l + v k * v l) := by ring
    _ = (c k * √(w k) / √Z) * (c l * √(w l) / √Z) * S k l * (u k * u l + v k * v l) := by
          rw [hk, hl]
    _ = c k * c l * (√(w k) * √(w l) * S k l * (u k * u l + v k * v l)) / Z := by
          have e : (c k * √(w k) / √Z) * (c l * √(w l) / √Z) =
              c k * √(w k) * (c l * √(w l)) / Z := by
            rw [div_mul_div_comm, hZZ]
          rw [e]
          ring

omit [DecidableEq ι] in
/-- **Cloning** ([KMMP, Claim 2.4], [JFA-E, Lemma C] and Step 3 of the proof of
[JFA-E, Theorem A]). Let `(S, w)` be a maximizer with `w > 0`, and let `u, v` realize
`kyFanSum 2 (√D S √D) > 0`. If `h` has a negative entry, `S i j = εᵢ εⱼ` on the support of `h`,
and `∑ᵢ hᵢ yᵢyᵢᵀ = 0` for `yᵢ = (uᵢ, vᵢ)`, then there is a weight `w'` with a zero entry and
`kyFanSum 2 (√D S √D) ≤ kyFanSum 2 (√D' S √D')`, where `D' = diag(w')`. -/
theorem exists_zero_weight_of_kernel {S : Matrix ι ι ℝ} {w : ι → ℝ} (hmax : IsMaximizer S w)
    (hpos : ∀ i, 0 < w i) {u v : ι → ℝ} (huv : IsOrthonormalPair u v)
    (hval : fanValue (weightedSign S w) u v = kyFanSum 2 (weightedSign S w))
    (hPv : 0 < kyFanSum 2 (weightedSign S w)) {h : ι → ℝ} {ε : ι → ℝ}
    (hC : ∀ i j, h i ≠ 0 → h j ≠ 0 → S i j = ε i * ε j)
    (h1 : ∑ i, h i * (u i * u i) = 0) (h2 : ∑ i, h i * (u i * v i) = 0)
    (h3 : ∑ i, h i * (v i * v i) = 0) (hneg : ∃ i, h i < 0) :
    ∃ w', IsWeight w' ∧ (∃ i, w' i = 0) ∧
      kyFanSum 2 (weightedSign S w) ≤ kyFanSum 2 (weightedSign S w') := by
  obtain ⟨hS, hw, hall⟩ := hmax
  set M := weightedSign S w with hM
  set Pv := kyFanSum 2 M with hPvdef
  set G : ι → ι → ℝ := fun k l ↦ √(w k) * √(w l) * S k l * (u k * u l + v k * v l) with hG
  have hGsymm : ∀ k l, G l k = G k l := by
    intro k l; simp only [hG, hS.symm]; ring
  have hsumG : ∑ k, ∑ l, G k l = Pv := by
    rw [← hval, fanValue_eq_sum]
    refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
    simp only [hG, hM, weightedSign, Matrix.of_apply]; ring
  -- invariance of the plane of `u, v`
  have hMs : ∀ k l, M l k = M k l := IsSignMatrix.weightedSign_comm hS w
  have hmaxM : ∀ x y, IsOrthonormalPair x y → fanValue M x y ≤ fanValue M u v := fun x y hxy ↦
    hval ▸ fanValue_le_kyFanSum_two M hxy
  have hinvu := mulVec_apply_eq_of_fanValue_le (.ext hMs) huv hmaxM
  have hinvv := mulVec_apply_eq_of_fanValue_le' (.ext hMs) huv hmaxM
  -- the linear coefficient vanishes
  have hrow : ∀ k, ∑ l, G k l = u k * (M *ᵥ u) k + v k * (M *ᵥ v) k := by
    intro k
    simp only [hG, mulVec_apply_eq_sum, hM, weightedSign, Matrix.of_apply, mul_sum,
      ← sum_add_distrib]
    refine sum_congr rfl fun l _ ↦ ?_
    ring
  have ha : ∑ k, h k * ∑ l, G k l = 0 := by
    simp only [hrow, hinvu, hinvv]
    have e : ∀ k, h k * (u k * ((u ⬝ᵥ M *ᵥ u) * u k + (v ⬝ᵥ M *ᵥ u) * v k) +
        v k * ((u ⬝ᵥ M *ᵥ v) * u k + (v ⬝ᵥ M *ᵥ v) * v k)) =
        (u ⬝ᵥ M *ᵥ u) * (h k * (u k * u k)) + (v ⬝ᵥ M *ᵥ u + u ⬝ᵥ M *ᵥ v) *
          (h k * (u k * v k)) + (v ⬝ᵥ M *ᵥ v) * (h k * (v k * v k)) := fun k ↦ by ring
    simp only [e, sum_add_distrib, ← mul_sum, h1, h2, h3]
    ring
  -- the quadratic coefficient is a sum of squares
  have hQ : ∑ k, ∑ l, h k * h l * G k l =
      (∑ k, h k * √(w k) * ε k * u k) ^ 2 + (∑ k, h k * √(w k) * ε k * v k) ^ 2 := by
    rw [sq, sq, sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun l _ ↦ ?_
    by_cases hk : h k = 0
    · simp [hk]
    · by_cases hl : h l = 0
      · simp [hl]
      · simp only [hG, hC k l hk hl]; ring
  have hQnn : 0 ≤ ∑ k, ∑ l, h k * h l * G k l := by rw [hQ]; positivity
  -- the value along the path `c = 1 + t h`
  have hpath : ∀ t : ℝ, (∀ k, 0 ≤ 1 + t * h k) → 0 < ∑ k, (1 + t * h k) * w k →
      (Pv + t ^ 2 * ∑ k, ∑ l, h k * h l * G k l) / (∑ k, (1 + t * h k) * w k) ≤
        kyFanSum 2 (weightedSign S (fun k ↦ (1 + t * h k) * w k / ∑ l, (1 + t * h l) * w l)) := by
    intro t hc hZ
    have hon : IsOrthonormalPair (fun k ↦ √(1 + t * h k) * u k) (fun k ↦ √(1 + t * h k) * v k) := by
      have hsq : ∀ k, √(1 + t * h k) * √(1 + t * h k) = 1 + t * h k :=
        fun k ↦ Real.mul_self_sqrt (hc k)
      refine ⟨?_, ?_, ?_⟩
      · have : (fun k ↦ √(1 + t * h k) * u k) ⬝ᵥ (fun k ↦ √(1 + t * h k) * u k) =
            u ⬝ᵥ u + t * ∑ k, h k * (u k * u k) := by
          simp only [dotProduct, mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun k _ ↦ ?_
          have := hsq k
          linear_combination (u k * u k) * this
        rw [this, huv.left_self, h1]; ring
      · have : (fun k ↦ √(1 + t * h k) * v k) ⬝ᵥ (fun k ↦ √(1 + t * h k) * v k) =
            v ⬝ᵥ v + t * ∑ k, h k * (v k * v k) := by
          simp only [dotProduct, mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun k _ ↦ ?_
          have := hsq k
          linear_combination (v k * v k) * this
        rw [this, huv.right_self, h3]; ring
      · have : (fun k ↦ √(1 + t * h k) * u k) ⬝ᵥ (fun k ↦ √(1 + t * h k) * v k) =
            u ⬝ᵥ v + t * ∑ k, h k * (u k * v k) := by
          simp only [dotProduct, mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun k _ ↦ ?_
          have := hsq k
          linear_combination (u k * v k) * this
        rw [this, huv.left_right, h2]; ring
    have hv := fanValue_clone S w u v (fun k ↦ 1 + t * h k) hc (fun k ↦ hw.nonneg k) hZ
    have hexp : ∑ k, ∑ l, (1 + t * h k) * (1 + t * h l) * G k l =
        Pv + t ^ 2 * ∑ k, ∑ l, h k * h l * G k l := by
      have e1 : ∑ k, ∑ l, (1 + t * h k) * (1 + t * h l) * G k l =
          ∑ k, ∑ l, G k l + t * (∑ k, h k * ∑ l, G k l) +
            t * (∑ l, h l * ∑ k, G k l) + t ^ 2 * ∑ k, ∑ l, h k * h l * G k l := by
        simp only [mul_sum]
        rw [sum_comm (f := fun l k ↦ t * (h l * G k l))]
        simp only [← sum_add_distrib]
        refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
        ring
      have e2 : ∑ l, h l * ∑ k, G k l = ∑ k, h k * ∑ l, G k l := by
        refine sum_congr rfl fun l _ ↦ ?_
        congr 1
        exact sum_congr rfl fun k _ ↦ hGsymm l k
      rw [e1, e2, ha, hsumG]; ring
    have hv' : fanValue (weightedSign S (fun k ↦ (1 + t * h k) * w k / ∑ l, (1 + t * h l) * w l))
        (fun k ↦ √(1 + t * h k) * u k) (fun k ↦ √(1 + t * h k) * v k) =
        (Pv + t ^ 2 * ∑ k, ∑ l, h k * h l * G k l) / ∑ k, (1 + t * h k) * w k := by
      rw [hv]
      exact congrArg (fun x ↦ x / ∑ k, (1 + t * h k) * w k) hexp
    rw [← hv']
    exact fanValue_le_kyFanSum_two _ hon
  -- two small values of `t` give `Q = 0` and `∑ hₖ wₖ = 0`
  set Q := ∑ k, ∑ l, h k * h l * G k l with hQdef
  set b := ∑ k, h k * w k with hbdef
  set K := 1 + ∑ k, |h k| with hKdef
  have hK : 0 < K := by positivity
  have hsmall : ∀ t : ℝ, |t| ≤ 1 / K → (∀ k, 0 < 1 + t * h k) := by
    intro t ht k
    have hhk : |h k| ≤ ∑ j, |h j| := single_le_sum (f := fun j ↦ |h j|)
      (fun j _ ↦ abs_nonneg _) (mem_univ k)
    have : |t * h k| < 1 := by
      rw [abs_mul]
      calc |t| * |h k| ≤ (1 / K) * |h k| := by gcongr
        _ < 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_lt_one hK]
          linarith
    linarith [neg_abs_le (t * h k)]
  have hZpos : ∀ t : ℝ, (∀ k, 0 < 1 + t * h k) → 0 < ∑ k, (1 + t * h k) * w k := by
    intro t hc
    obtain ⟨k₀⟩ : Nonempty ι := by
      obtain ⟨i, _⟩ := hneg; exact ⟨i⟩
    have : 0 < (1 + t * h k₀) * w k₀ := mul_pos (hc k₀) (hpos k₀)
    exact lt_of_lt_of_le this (single_le_sum (f := fun k ↦ (1 + t * h k) * w k)
      (fun k _ ↦ (mul_pos (hc k) (hpos k)).le) (mem_univ k₀))
  have hbound : ∀ t : ℝ, |t| ≤ 1 / K → Pv + t ^ 2 * Q ≤ Pv * (1 + t * b) := by
    intro t ht
    have hc := hsmall t ht
    have hZ := hZpos t hc
    have hZ' : ∑ k, (1 + t * h k) * w k = 1 + t * b := by
      simp only [hbdef, add_mul, one_mul, sum_add_distrib, hw.sum_eq, mul_assoc, ← mul_sum]
    have hle := (hpath t (fun k ↦ (hc k).le) hZ).trans
      (hall S _ hS (by
        refine ⟨fun k ↦ div_nonneg (mul_nonneg (hc k).le (hw.nonneg k)) hZ.le, ?_⟩
        rw [← sum_div, div_self hZ.ne']))
    rw [hZ'] at hZ hle
    rw [div_le_iff₀ hZ] at hle
    exact hle
  have hδ : 0 < 1 / K := by positivity
  have hp := hbound (1 / K) (by rw [abs_of_pos hδ])
  have hm := hbound (-(1 / K)) (by rw [abs_neg, abs_of_pos hδ])
  have hQ0 : Q = 0 := by
    have : 2 * (1 / K) ^ 2 * Q ≤ 0 := by nlinarith
    have hQle : Q ≤ 0 := by
      by_contra hcon; push Not at hcon
      have : 0 < 2 * (1 / K) ^ 2 * Q := by positivity
      linarith
    exact le_antisymm hQle hQnn
  have hb0 : b = 0 := by
    rw [hQ0, mul_zero, add_zero] at hp hm
    have h1' : 0 ≤ Pv * (1 / K) * b := by nlinarith
    have h2' : Pv * (1 / K) * b ≤ 0 := by nlinarith
    have : Pv * (1 / K) * b = 0 := le_antisymm h2' h1'
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · linarith
      · linarith
    · exact h
  -- the endpoint: `t* = -1 / min h`
  obtain ⟨k₀, -, hk₀⟩ := exists_min_image univ h ⟨hneg.choose, mem_univ _⟩
  have hk₀neg : h k₀ < 0 := lt_of_le_of_lt (hk₀ _ (mem_univ _)) hneg.choose_spec
  set t := -1 / h k₀ with htdef
  have hct : ∀ k, 0 ≤ 1 + t * h k := by
    intro k
    rw [htdef]
    by_cases hk : 0 ≤ h k
    · have : 0 ≤ -1 / h k₀ := div_nonneg_of_nonpos (by norm_num) hk₀neg.le
      nlinarith
    · push Not at hk
      have hle : h k₀ ≤ h k := hk₀ k (mem_univ k)
      rw [div_mul_eq_mul_div, neg_one_mul, neg_div, ← sub_eq_add_neg, sub_nonneg,
        div_le_one_of_neg hk₀neg]
      exact hle
  have hct0 : 1 + t * h k₀ = 0 := by
    rw [htdef, div_mul_cancel₀ (-1) hk₀neg.ne]; ring
  have hZt : ∑ k, (1 + t * h k) * w k = 1 := by
    simp only [add_mul, one_mul, sum_add_distrib, hw.sum_eq, mul_assoc, ← mul_sum, ← hbdef, hb0,
      mul_zero, add_zero]
  have hval' := hpath t hct (by rw [hZt]; norm_num)
  have hlhs : (Pv + t ^ 2 * Q) / ∑ k, (1 + t * h k) * w k = Pv := by
    rw [hQ0, hZt]; ring
  rw [hlhs] at hval'
  refine ⟨fun k ↦ (1 + t * h k) * w k / ∑ l, (1 + t * h l) * w l, ?_, ⟨k₀, ?_⟩, hval'⟩
  · refine ⟨fun k ↦ div_nonneg (mul_nonneg (hct k) (hw.nonneg k)) (by rw [hZt]; norm_num), ?_⟩
    rw [← sum_div, hZt, div_one]
  · simp only [hct0, zero_mul, zero_div]

end ProjectionConstants.GrunbaumConjecture
