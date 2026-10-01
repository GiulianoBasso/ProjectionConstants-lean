/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Matrix.SignMatrix
import ProjectionConstants.ForMathlib.BigOperators

/-!
# Transfer along signed injections

Let `f : ι → κ` be injective and let `εᵢ = ±1`, and suppose that `A i j = εᵢ εⱼ B (f i) (f j)`.
Multiplying a vector by the signs and extending it by zero along `f` (`signedExtend f ε`) maps
orthonormal pairs to orthonormal pairs and preserves the value `fanValue A u v = uᵀAu + vᵀAv`.
Hence `kyFanSum 2 A ≤ kyFanSum 2 B`. This covers switching, relabelling and passing to principal
submatrices, the basic operations on sign matrices used throughout [JFA-E]. For weighted sign
matrices, the weights are extended by zero (`kyFanSum_two_weightedSign_le_of_eq_mul`); this is
how sign matrices are compared with `R₅` in the proof of [JFA-E, Theorem A]
(`ProjectionConstants.GrunbaumConjecture.Reduction`).

## Main definitions

* `signedExtend f ε x`: the vector with entries `εᵢ xᵢ` at `f i`, and `0` outside the range of
  `f`.
* `basisVec a`: the standard basis vector at `a`.

## Main statements

* `isOrthonormalPair_signedExtend_and_fanValue_eq`: the transfer of orthonormal pairs and of
  their values.
* `kyFanSum_two_le_of_eq_mul`: `kyFanSum 2 A ≤ kyFanSum 2 B`.
* `kyFanSum_two_weightedSign_nonneg`: `kyFanSum 2 (√D S √D) ≥ 0`.
* `kyFanSum_two_weightedSign_le_of_eq_mul`: the transfer for weighted sign matrices.

## References

* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Finset Matrix

namespace ProjectionConstants.GrunbaumConjecture

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Extension by zero along `f`, twisted by the signs `ε`. -/
noncomputable def signedExtend (f : ι → κ) (ε x : ι → ℝ) : κ → ℝ :=
  Function.extend f (fun i ↦ ε i * x i) 0

omit [Fintype ι] [Fintype κ] in
lemma signedExtend_apply {f : ι → κ} (hf : Function.Injective f) (ε x : ι → ℝ) (i : ι) :
    signedExtend f ε x (f i) = ε i * x i :=
  hf.extend_apply _ _ i

omit [Fintype ι] [Fintype κ] in
lemma signedExtend_apply_of_not_mem {f : ι → κ} (ε x : ι → ℝ) {k : κ} (hk : ¬ ∃ i, f i = k) :
    signedExtend f ε x k = 0 := by
  simp [signedExtend, Function.extend_apply' _ _ _ hk]

/-- `signedExtend f ε` preserves inner products if `εᵢ = ±1`. -/
lemma signedExtend_dotProduct_signedExtend {f : ι → κ} (hf : Function.Injective f) {ε : ι → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (x y : ι → ℝ) :
    (signedExtend f ε x) ⬝ᵥ (signedExtend f ε y) = x ⬝ᵥ y := by
  rw [dotProduct, Fintype.sum_eq_sum_comp_of_injective hf]
  · simp only [signedExtend_apply hf, dotProduct]
    refine sum_congr rfl fun i _ ↦ ?_
    have := hε i
    linear_combination (x i * y i) * this
  · intro k hk
    simp [signedExtend_apply_of_not_mem _ _ hk]

/-- If `A i j = εᵢ εⱼ B (f i) (f j)`, then `x'ᵀ B x' = xᵀ A x` for `x' = signedExtend f ε x`. -/
lemma signedExtend_dotProduct_mulVec_signedExtend {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    {f : ι → κ} (hf : Function.Injective f) {ε : ι → ℝ}
    (hAB : ∀ i j, A i j = ε i * ε j * B (f i) (f j)) (x : ι → ℝ) :
    (signedExtend f ε x) ⬝ᵥ B *ᵥ (signedExtend f ε x) = x ⬝ᵥ A *ᵥ x := by
  rw [dotProduct_mulVec_self_eq_sum, dotProduct_mulVec_self_eq_sum,
    Fintype.sum_eq_sum_comp_of_injective hf]
  · refine sum_congr rfl fun i _ ↦ ?_
    rw [Fintype.sum_eq_sum_comp_of_injective hf]
    · refine sum_congr rfl fun j _ ↦ ?_
      rw [signedExtend_apply hf, signedExtend_apply hf, hAB]
      ring
    · intro k hk
      simp [signedExtend_apply_of_not_mem _ _ hk]
  · intro k hk
    simp [signedExtend_apply_of_not_mem _ _ hk]

/-- **Transfer.** If `A i j = εᵢ εⱼ B (f i) (f j)` with `f` injective and `εᵢ = ±1`, then
`signedExtend f ε` maps orthonormal pairs to orthonormal pairs and preserves `fanValue`. -/
theorem isOrthonormalPair_signedExtend_and_fanValue_eq {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    {f : ι → κ} (hf : Function.Injective f) {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1)
    (hAB : ∀ i j, A i j = ε i * ε j * B (f i) (f j)) {x y : ι → ℝ} (h : IsOrthonormalPair x y) :
    IsOrthonormalPair (signedExtend f ε x) (signedExtend f ε y) ∧
      fanValue B (signedExtend f ε x) (signedExtend f ε y) = fanValue A x y := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [signedExtend_dotProduct_signedExtend hf hε]; exact h.left_self
  · rw [signedExtend_dotProduct_signedExtend hf hε]; exact h.right_self
  · rw [signedExtend_dotProduct_signedExtend hf hε]; exact h.left_right
  · simp only [fanValue, signedExtend_dotProduct_mulVec_signedExtend hf hAB]

/-- Hence `kyFanSum 2 A ≤ kyFanSum 2 B`, provided that `A` has an orthonormal pair. -/
theorem kyFanSum_two_le_of_eq_mul {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ} {f : ι → κ}
    (hf : Function.Injective f) {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1)
    (hAB : ∀ i j, A i j = ε i * ε j * B (f i) (f j)) (hne : (fanValues A).Nonempty) :
    kyFanSum 2 A ≤ kyFanSum 2 B := by
  refine kyFanSum_two_le hne fun x y h ↦ ?_
  obtain ⟨h', hval⟩ := isOrthonormalPair_signedExtend_and_fanValue_eq hf hε hAB h
  rw [← hval]
  exact fanValue_le_kyFanSum_two B h'

/-! ### Weighted sign matrices -/

/-- The standard basis vector at `a`. -/
def basisVec [DecidableEq ι] (a : ι) : ι → ℝ := fun i ↦ if i = a then 1 else 0

lemma basisVec_dotProduct_basisVec [DecidableEq ι] (a b : ι) :
    (basisVec a) ⬝ᵥ (basisVec b) = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst hab; simp [dotProduct, basisVec]
  · rw [ite_eq_right hab]
    apply sum_eq_zero
    intro i _
    by_cases hia : i = a
    · subst hia; simp [basisVec, hab]
    · simp [basisVec, hia]

lemma isOrthonormalPair_basisVec [DecidableEq ι] {a b : ι} (hab : a ≠ b) :
    IsOrthonormalPair (basisVec a) (basisVec b) :=
  ⟨by simp [basisVec_dotProduct_basisVec], by simp [basisVec_dotProduct_basisVec],
    by simp [basisVec_dotProduct_basisVec, hab]⟩

lemma basisVec_dotProduct_mulVec_basisVec [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι) :
    (basisVec a) ⬝ᵥ A *ᵥ (basisVec a) = A a a := by
  simp [dotProduct_mulVec_self_eq_sum, basisVec]

/-- `kyFanSum 2 (√D S √D) ≥ 0` for a sign matrix `S` and a weight `w`. -/
lemma kyFanSum_two_weightedSign_nonneg {S : Matrix ι ι ℝ} {w : ι → ℝ} (hS : IsSignMatrix S)
    (hw : IsWeight w) : 0 ≤ kyFanSum 2 (weightedSign S w) := by
  classical
  by_cases h : (fanValues (weightedSign S w)).Nonempty
  · obtain ⟨_, x, y, hxy, rfl⟩ := h
    -- there are two distinct indices
    have h2 : ∃ a b : ι, a ≠ b := by
      by_contra hcon
      push Not at hcon
      have hsub : ∀ a b : ι, a = b := hcon
      obtain ⟨i⟩ : Nonempty ι := by
        by_contra hi
        rw [not_nonempty_iff] at hi
        have := hxy.left_self
        simp [dotProduct] at this
      have hx : ∀ k, k = i := fun k ↦ hsub k i
      have e1 : x i * x i = 1 := by
        have := hxy.left_self
        rw [dotProduct, Fintype.sum_eq_single i (fun k hk ↦ absurd (hx k) hk)] at this
        exact this
      have e2 : y i * y i = 1 := by
        have := hxy.right_self
        rw [dotProduct, Fintype.sum_eq_single i (fun k hk ↦ absurd (hx k) hk)] at this
        exact this
      have e3 : x i * y i = 0 := by
        have := hxy.left_right
        rw [dotProduct, Fintype.sum_eq_single i (fun k hk ↦ absurd (hx k) hk)] at this
        exact this
      nlinarith [e1, e2, e3]
    obtain ⟨a, b, hab⟩ := h2
    have := fanValue_le_kyFanSum_two (weightedSign S w) (isOrthonormalPair_basisVec hab)
    have haa : (weightedSign S w) a a = w a := by
      simp [weightedSign, hS.diag, Real.mul_self_sqrt (hw.nonneg a)]
    have hbb : (weightedSign S w) b b = w b := by
      simp [weightedSign, hS.diag, Real.mul_self_sqrt (hw.nonneg b)]
    simp only [fanValue, basisVec_dotProduct_mulVec_basisVec, haa, hbb] at this
    linarith [hw.nonneg a, hw.nonneg b]
  · rw [kyFanSum_two_of_not_nonempty h]

/-- Transfer for weighted sign matrices: if `S i j = εᵢ εⱼ T (f i) (f j)` with `f` injective, then
`kyFanSum 2 (√D S √D) ≤ kyFanSum 2 (√D' T √D')`, where `D'` extends `D` by zero along `f`. -/
theorem kyFanSum_two_weightedSign_le_of_eq_mul {S : Matrix ι ι ℝ} {T : Matrix κ κ ℝ} {w : ι → ℝ}
    (hT : IsSignMatrix T) (hw : IsWeight w) {f : ι → κ} (hf : Function.Injective f)
    {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1) (hST : ∀ i j, S i j = ε i * ε j * T (f i) (f j)) :
    IsWeight (Function.extend f w 0) ∧
      kyFanSum 2 (weightedSign S w) ≤ kyFanSum 2 (weightedSign T (Function.extend f w 0)) := by
  classical
  have hw' : IsWeight (Function.extend f w 0) := by
    refine ⟨fun k ↦ ?_, ?_⟩
    · by_cases hk : ∃ i, f i = k
      · obtain ⟨i, rfl⟩ := hk
        rw [hf.extend_apply]; exact hw.nonneg i
      · rw [Function.extend_apply' _ _ _ hk]; simp
    · rw [Fintype.sum_eq_sum_comp_of_injective hf]
      · simp only [hf.extend_apply]; exact hw.sum_eq
      · intro k hk; rw [Function.extend_apply' _ _ _ hk]; simp
  refine ⟨hw', ?_⟩
  by_cases hne : (fanValues (weightedSign S w)).Nonempty
  · refine kyFanSum_two_le_of_eq_mul hf hε (fun i j ↦ ?_) hne
    simp only [weightedSign, Matrix.of_apply, hf.extend_apply, hST]
    ring
  · rw [kyFanSum_two_of_not_nonempty hne]
    exact kyFanSum_two_weightedSign_nonneg hT hw'

end ProjectionConstants.GrunbaumConjecture
