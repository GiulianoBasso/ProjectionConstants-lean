/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.GrunbaumConjecture.Cloning
import ProjectionConstants.GrunbaumConjecture.Transfer

/-!
# Zero weights and twins

Let `M = √D S √D` for a sign matrix `S` and a weight `w`, where `D = diag(w)`, and let `u, v` be
an orthonormal pair that maximizes `fanValue M` with `fanValue M u v > 1`. Since all eigenvalues
of `M` are at most `1`, the `2 × 2` block of `M` on the plane of `u, v` has positive determinant.
So every linear functional that kills `M u` and `M v` kills `u` and `v`
(`map_eq_zero_of_map_mulVec_eq_zero`). Consequently:

* if `w j = 0`, then `u j = v j = 0`, and the value of `u, v` is at most `kyFanSum 2` of the
  restriction of `(S, w)` to the indices `k ≠ j` (`fanValue_le_kyFanSum_two_restrict`);
* if `i, j` are twins, i.e. the rows of `S` satisfy `sⱼ = ±sᵢ`, then the weight of `j` can be
  merged into `i` without decreasing the value (`exists_zero_weight_of_twins`).

The proof of [JFA-E, Theorem A] in `ProjectionConstants.GrunbaumConjecture.Reduction` uses the first
point in its induction on the number of indices, and `fanValue_le_one_of_card_le_two` for at most
two indices. The second point is Step 2 of the proof of [JFA-E, Theorem A]. It is not needed in
`ProjectionConstants.GrunbaumConjecture.Reduction`, where Step 4 is done by `exists_embedding_A6`
instead of the classification of Frankl and Füredi.

## Main statements

* `map_eq_zero_of_map_mulVec_eq_zero`: `M` is invertible on the plane of `u, v`.
* `fanValue_le_kyFanSum_two_restrict`: zero weights can be removed.
* `exists_zero_weight_of_twins`: twins can be merged.
* `fanValue_le_one_of_card_le_two`: `fanValue M u v ≤ 1` if there are at most two indices.

## References

* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Finset Matrix

namespace ProjectionConstants.GrunbaumConjecture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section

variable {S : Matrix ι ι ℝ} {w : ι → ℝ} {u v : ι → ℝ}

omit [DecidableEq ι] in
/-- The `2 × 2` block of `M` on the plane of an orthonormal pair with value `> 1` has positive
determinant. -/
private lemma det_block_pos (hS : IsSignMatrix S) (hw : IsWeight w) (huv : IsOrthonormalPair u v)
    (hgt : 1 < fanValue (weightedSign S w) u v) :
    0 < (u ⬝ᵥ weightedSign S w *ᵥ u) * (v ⬝ᵥ weightedSign S w *ᵥ v) -
      (v ⬝ᵥ weightedSign S w *ᵥ u) * (v ⬝ᵥ weightedSign S w *ᵥ u) := by
  have hMs : ∀ k l, weightedSign S w l k = weightedSign S w k l :=
    IsSignMatrix.weightedSign_comm hS w
  obtain ⟨α, hα⟩ : ∃ α, u ⬝ᵥ weightedSign S w *ᵥ u = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, v ⬝ᵥ weightedSign S w *ᵥ u = β := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, v ⬝ᵥ weightedSign S w *ᵥ v = γ := ⟨_, rfl⟩
  rw [hα, hβ, hγ]
  -- Rayleigh bound on the plane
  have hq : ∀ a b : ℝ, a ^ 2 * α + 2 * a * b * β + b ^ 2 * γ ≤ a ^ 2 + b ^ 2 := by
    intro a b
    have h1 := dotProduct_mulVec_weightedSign_le hS hw (fun i ↦ a * u i + b * v i)
    rw [linearComb_dotProduct_mulVec_linearComb (.ext hMs), linearComb_dotProduct,
      dotProduct_linearComb, dotProduct_linearComb, huv.left_self, huv.right_self,
      huv.left_right, dotProduct_comm v u, huv.left_right, hα, hβ, hγ] at h1
    linarith
  have hsum : α + γ = fanValue (weightedSign S w) u v := by
    rw [← hα, ← hγ]; simp only [fanValue]
  have hα1 : α ≤ 1 := by have := hq 1 0; simpa using this
  have hγ1 : γ ≤ 1 := by have := hq 0 1; simpa using this
  have key : β ^ 2 ≤ (1 - α) * (1 - γ) := by
    rcases lt_or_eq_of_le hα1 with hlt | heq
    · have := hq β (1 - α)
      have h2 : 0 ≤ (1 - α) * ((1 - α) * (1 - γ) - β ^ 2) := by nlinarith
      have h3 : 0 < 1 - α := by linarith
      nlinarith [(mul_nonneg_iff_of_pos_left h3).mp h2]
    · -- `α = 1` forces `β = 0`
      have hβ0 : β = 0 := by
        by_contra hβne
        have := hq ((2 - γ) / (2 * β)) 1
        have e : 2 * ((2 - γ) / (2 * β)) * 1 * β = 2 - γ := by field_simp
        rw [heq] at this
        nlinarith [e]
      rw [hβ0, heq]; simp
  rw [← hsum] at hgt
  nlinarith [key, hgt]

omit [DecidableEq ι] in
/-- If `u, v` maximizes `fanValue M` with a value `> 1`, where `M = √D S √D`, then every linear
functional that kills `M u` and `M v` kills `u` and `v`. -/
lemma map_eq_zero_of_map_mulVec_eq_zero (hS : IsSignMatrix S) (hw : IsWeight w)
    (huv : IsOrthonormalPair u v)
    (hmax : ∀ x y, IsOrthonormalPair x y →
      fanValue (weightedSign S w) x y ≤ fanValue (weightedSign S w) u v)
    (hgt : 1 < fanValue (weightedSign S w) u v) {L : (ι → ℝ) → ℝ}
    (hL : ∀ (a b : ℝ) (x y : ι → ℝ), L (fun k ↦ a * x k + b * y k) = a * L x + b * L y)
    (hLu : L (weightedSign S w *ᵥ u) = 0) (hLv : L (weightedSign S w *ᵥ v) = 0) :
    L u = 0 ∧ L v = 0 := by
  have hMs : ∀ k l, weightedSign S w l k = weightedSign S w k l :=
    IsSignMatrix.weightedSign_comm hS w
  have hu := mulVec_apply_eq_of_fanValue_le (.ext hMs) huv hmax
  have hv := mulVec_apply_eq_of_fanValue_le' (.ext hMs) huv hmax
  have hsym : v ⬝ᵥ weightedSign S w *ᵥ u = u ⬝ᵥ weightedSign S w *ᵥ v :=
    (IsSymm.ext hMs).dotProduct_mulVec_comm
  have hD := det_block_pos hS hw huv hgt
  have hMu : weightedSign S w *ᵥ u =
      fun k ↦ (u ⬝ᵥ weightedSign S w *ᵥ u) * u k + (v ⬝ᵥ weightedSign S w *ᵥ u) * v k :=
    funext hu
  have hMv : weightedSign S w *ᵥ v =
      fun k ↦ (u ⬝ᵥ weightedSign S w *ᵥ v) * u k + (v ⬝ᵥ weightedSign S w *ᵥ v) * v k :=
    funext hv
  rw [hMu, hL] at hLu
  rw [hMv, hL, ← hsym] at hLv
  obtain ⟨α, hα⟩ : ∃ α, u ⬝ᵥ weightedSign S w *ᵥ u = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, v ⬝ᵥ weightedSign S w *ᵥ u = β := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, v ⬝ᵥ weightedSign S w *ᵥ v = γ := ⟨_, rfl⟩
  rw [hα, hβ] at hLu
  rw [hβ, hγ] at hLv
  rw [hα, hβ, hγ] at hD
  have e1 : (α * γ - β * β) * L u = 0 := by linear_combination γ * hLu - β * hLv
  have e2 : (α * γ - β * β) * L v = 0 := by linear_combination α * hLv - β * hLu
  exact ⟨(mul_eq_zero.mp e1).resolve_left hD.ne', (mul_eq_zero.mp e2).resolve_left hD.ne'⟩

/-- **Zero weights.** If `w j = 0` and `u, v` maximizes `fanValue (√D S √D)` with a value `> 1`,
then this value is at most `kyFanSum 2` of the restriction of `(S, w)` to the indices `k ≠ j`. -/
theorem fanValue_le_kyFanSum_two_restrict (hS : IsSignMatrix S) (hw : IsWeight w) {j : ι}
    (hj : w j = 0) (huv : IsOrthonormalPair u v)
    (hmax : ∀ x y, IsOrthonormalPair x y →
      fanValue (weightedSign S w) x y ≤ fanValue (weightedSign S w) u v)
    (hgt : 1 < fanValue (weightedSign S w) u v) :
    IsSignMatrix (fun a b : {k // k ≠ j} ↦ S a.1 b.1) ∧ IsWeight (fun a : {k // k ≠ j} ↦ w a.1) ∧
      fanValue (weightedSign S w) u v ≤
        kyFanSum 2 (weightedSign (fun a b : {k // k ≠ j} ↦ S a.1 b.1) (fun a ↦ w a.1)) := by
  -- the `j`-th coordinates of `u` and `v` vanish
  have hL : ∀ (a b : ℝ) (x y : ι → ℝ), (fun z : ι → ℝ ↦ z j) (fun k ↦ a * x k + b * y k) =
      a * (fun z : ι → ℝ ↦ z j) x + b * (fun z : ι → ℝ ↦ z j) y := fun _ _ _ _ ↦ rfl
  have hMj : ∀ x, (weightedSign S w *ᵥ x) j = 0 := by
    intro x; rw [mulVec_weightedSign, hj, Real.sqrt_zero, zero_mul]
  obtain ⟨huj, hvj⟩ :=
    map_eq_zero_of_map_mulVec_eq_zero (L := fun z ↦ z j) hS hw huv hmax hgt hL (hMj u) (hMj v)
  have hinj : Function.Injective (Subtype.val : {k // k ≠ j} → ι) := Subtype.val_injective
  have hnot : ∀ k, (¬ ∃ a : {k // k ≠ j}, a.1 = k) → k = j := by
    intro k hk; by_contra hkj; exact hk ⟨⟨k, hkj⟩, rfl⟩
  have hε : ∀ _a : {k // k ≠ j}, (1 : ℝ) * 1 = 1 := fun _ ↦ by norm_num
  have hpush : ∀ x : ι → ℝ, x j = 0 →
      signedExtend (Subtype.val : {k // k ≠ j} → ι) (fun _ ↦ (1 : ℝ))
        (fun a : {k // k ≠ j} ↦ x a.1) = x := by
    intro x hx
    funext k
    by_cases hk : ∃ a : {k // k ≠ j}, a.1 = k
    · obtain ⟨a, rfl⟩ := hk
      rw [signedExtend_apply hinj]; ring
    · rw [signedExtend_apply_of_not_mem _ _ hk, hnot k hk, hx]
  refine ⟨⟨fun a b ↦ hS.symm _ _, fun a b ↦ hS.pm _ _, fun a ↦ hS.diag _⟩,
    ⟨fun a ↦ hw.nonneg _, ?_⟩, ?_⟩
  · rw [← hw.sum_eq, Fintype.sum_eq_sum_comp_of_injective hinj (fun k ↦ w k)]
    intro k hk; rw [hnot k hk, hj]
  · have hAB : ∀ a b : {k // k ≠ j},
        weightedSign (fun a b : {k // k ≠ j} ↦ S a.1 b.1) (fun a ↦ w a.1) a b =
          1 * 1 * weightedSign S w a.1 b.1 := by
      intro a b; simp [weightedSign]
    obtain ⟨hon, hval⟩ := isOrthonormalPair_signedExtend_and_fanValue_eq hinj hε hAB
      (x := fun a ↦ u a.1) (y := fun a ↦ v a.1) (by
      refine ⟨?_, ?_, ?_⟩
      · have := signedExtend_dotProduct_signedExtend hinj hε (fun a ↦ u a.1) (fun a ↦ u a.1)
        rw [hpush u huj] at this; rw [← this]; exact huv.left_self
      · have := signedExtend_dotProduct_signedExtend hinj hε (fun a ↦ v a.1) (fun a ↦ v a.1)
        rw [hpush v hvj] at this; rw [← this]; exact huv.right_self
      · have := signedExtend_dotProduct_signedExtend hinj hε (fun a ↦ u a.1) (fun a ↦ v a.1)
        rw [hpush u huj, hpush v hvj] at this; rw [← this]; exact huv.left_right)
    rw [hpush u huj, hpush v hvj] at hval
    rw [hval]
    exact fanValue_le_kyFanSum_two _ (by
      refine ⟨?_, ?_, ?_⟩
      · have := signedExtend_dotProduct_signedExtend hinj hε (fun a ↦ u a.1) (fun a ↦ u a.1)
        rw [hpush u huj] at this; rw [← this]; exact huv.left_self
      · have := signedExtend_dotProduct_signedExtend hinj hε (fun a ↦ v a.1) (fun a ↦ v a.1)
        rw [hpush v hvj] at this; rw [← this]; exact huv.right_self
      · have := signedExtend_dotProduct_signedExtend hinj hε (fun a ↦ u a.1) (fun a ↦ v a.1)
        rw [hpush u huj, hpush v hvj] at this; rw [← this]; exact huv.left_right)

omit [DecidableEq ι] in
/-- **Twins** (Step 2 of the proof of [JFA-E, Theorem A]). If `i, j` are twins, i.e.
`sⱼₖ = ε sᵢₖ` for all `k` with `ε = ±1`, and `u, v` maximizes `fanValue (√D S √D)` with a value
`> 1`, then moving the weight of `j` to `i` gives a weight `w'` with `w' j = 0` and at least the
same value. -/
theorem exists_zero_weight_of_twins (hS : IsSignMatrix S) (hw : IsWeight w) (hpos : ∀ k, 0 < w k)
    (huv : IsOrthonormalPair u v)
    (hmax : ∀ x y, IsOrthonormalPair x y →
      fanValue (weightedSign S w) x y ≤ fanValue (weightedSign S w) u v)
    (hgt : 1 < fanValue (weightedSign S w) u v) {i j : ι} (hij : i ≠ j) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (htw : ∀ k, S j k = ε * S i k) :
    ∃ w', IsWeight w' ∧ w' j = 0 ∧
      fanValue (weightedSign S w) u v ≤ kyFanSum 2 (weightedSign S w') := by
  classical
  have hji : j ≠ i := Ne.symm hij
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  -- twin relation `√wᵢ xⱼ = ε √wⱼ xᵢ` for `x = u, v`
  set L : (ι → ℝ) → ℝ := fun z ↦ √(w i) * z j - ε * √(w j) * z i with hLdef
  have hL : ∀ (a b : ℝ) (x y : ι → ℝ), L (fun k ↦ a * x k + b * y k) = a * L x + b * L y := by
    intro a b x y; simp only [hLdef]; ring
  have hLM : ∀ x, L (weightedSign S w *ᵥ x) = 0 := by
    intro x
    simp only [hLdef, mulVec_weightedSign]
    have : ∑ l, S j l * (√(w l) * x l) = ε * ∑ l, S i l * (√(w l) * x l) := by
      rw [mul_sum]; exact sum_congr rfl fun l _ ↦ by rw [htw]; ring
    rw [this]; ring
  obtain ⟨hLu, hLv⟩ := map_eq_zero_of_map_mulVec_eq_zero hS hw huv hmax hgt hL (hLM u) (hLM v)
  simp only [hLdef] at hLu hLv
  -- the merged configuration
  have hwi := hpos i
  have hwj := hpos j
  have hsi : √(w i) * √(w i) = w i := Real.mul_self_sqrt hwi.le
  have hsj : √(w j) * √(w j) = w j := Real.mul_self_sqrt hwj.le
  have hs : 0 < w i + w j := by linarith
  have hss : √(w i + w j) * √(w i + w j) = w i + w j := Real.mul_self_sqrt hs.le
  have hsne : √(w i + w j) ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  set w' : ι → ℝ := fun k ↦ if k = j then 0 else if k = i then w i + w j else w k with hw'
  set m : (ι → ℝ) → (ι → ℝ) := fun x k ↦ if k = j then 0 else if k = i then
      (√(w i) * x i + ε * √(w j) * x j) / √(w i + w j) else x k with hm
  -- weighted vectors: `√w' ⊙ m x = √w ⊙ x - (√wⱼ xⱼ) d` with `d = eⱼ - ε eᵢ`
  set d : ι → ℝ := fun k ↦ (if k = j then 1 else 0) - ε * (if k = i then 1 else 0) with hd
  have hweighted : ∀ x : ι → ℝ, (fun k ↦ √(w' k) * m x k) =
      fun k ↦ 1 * (√(w k) * x k) + (-(√(w j) * x j)) * d k := by
    intro x; funext k
    simp only [hw', hm, hd]
    by_cases hkj : k = j
    · subst hkj; simp [hji]
    · by_cases hki : k = i
      · subst hki
        simp only [hkj, ite_false, ite_true]
        field_simp
        ring
      · simp [hkj, hki]
  -- `S d = 0`
  have hSd : ∀ k, (S *ᵥ d) k = 0 := by
    intro k
    simp only [mulVec_apply_eq_sum, hd, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ite_true]
    rw [hS.symm j k, htw k, hS.symm i k]; ring
  have hSs : ∀ k l, S l k = S k l := hS.symm
  have hqf : ∀ x : ι → ℝ, (m x) ⬝ᵥ weightedSign S w' *ᵥ (m x) = x ⬝ᵥ weightedSign S w *ᵥ x := by
    intro x
    rw [dotProduct_mulVec_weightedSign, dotProduct_mulVec_weightedSign, hweighted x,
      linearComb_dotProduct_mulVec_linearComb (.ext hSs)]
    have h1 : d ⬝ᵥ S *ᵥ (fun k ↦ √(w k) * x k) = 0 := by
      rw [(IsSymm.ext hSs).dotProduct_mulVec_comm]; simp [dotProduct, hSd]
    have h2 : d ⬝ᵥ S *ᵥ d = 0 := by simp [dotProduct, hSd]
    rw [h1, h2]
    simp only [one_pow, one_mul, mul_zero, add_zero]
  -- `m` preserves inner products of `u, v`
  have hmdot : ∀ x y : ι → ℝ, √(w i) * x j = ε * √(w j) * x i →
      √(w i) * y j = ε * √(w j) * y i → (m x) ⬝ᵥ (m y) = x ⬝ᵥ y := by
    intro x y hx hy
    have hmi : m x i * m y i = x i * y i + x j * y j := by
      have hN : (√(w i) * x i + ε * √(w j) * x j) * (√(w i) * y i + ε * √(w j) * y j) =
          (x i * y i + x j * y j) * (w i + w j) := by
        linear_combination (ε * √(w j) * y i - √(w i) * y j) * hx +
          √(w j) * √(w j) * (x i * y i + x j * y j) * hεε +
          (x i * y i + x j * y j) * hsi + (x i * y i + x j * y j) * hsj
      have hmx : m x i = (√(w i) * x i + ε * √(w j) * x j) / √(w i + w j) := by
        simp only [hm, hij, ite_false, ite_true]
      have hmy : m y i = (√(w i) * y i + ε * √(w j) * y j) / √(w i + w j) := by
        simp only [hm, hij, ite_false, ite_true]
      rw [hmx, hmy, div_mul_div_comm, hss, hN]
      field_simp
    have hmj : m x j * m y j = 0 := by simp [hm]
    have e : (m x) ⬝ᵥ (m y) - x ⬝ᵥ y =
        (m x i * m y i - x i * y i) + (m x j * m y j - x j * y j) := by
      simp only [dotProduct, ← sum_sub_distrib]
      rw [Fintype.sum_eq_add i j hij]
      intro k ⟨hki, hkj⟩
      simp [hm, hki, hkj]
    rw [hmi, hmj] at e
    linarith
  refine ⟨w', ⟨fun k ↦ ?_, ?_⟩, by simp [hw'], ?_⟩
  · simp only [hw']; split_ifs <;> linarith [hw.nonneg k]
  · have e : ∑ k, w' k - ∑ k, w k = (w' i - w i) + (w' j - w j) := by
      rw [← sum_sub_distrib, Fintype.sum_eq_add i j hij]
      intro k ⟨hki, hkj⟩
      simp [hw', hki, hkj]
    simp only [hw', hij, hji, ite_false, ite_true] at e
    rw [hw.sum_eq] at e
    linarith
  · have hon : IsOrthonormalPair (m u) (m v) :=
      ⟨by rw [hmdot u u (by linarith) (by linarith)]; exact huv.left_self,
        by rw [hmdot v v (by linarith) (by linarith)]; exact huv.right_self,
        by rw [hmdot u v (by linarith) (by linarith)]; exact huv.left_right⟩
    have := fanValue_le_kyFanSum_two (weightedSign S w') hon
    simp only [fanValue, hqf] at this
    exact this

omit [DecidableEq ι] in
/-- With at most two indices, `fanValue (√D S √D) u v ≤ 1` for every orthonormal pair `u, v`
(in fact, it equals `Tr (√D S √D) = 1`). -/
theorem fanValue_le_one_of_card_le_two (hS : IsSignMatrix S) (hw : IsWeight w)
    (huv : IsOrthonormalPair u v) (hcard : Fintype.card ι ≤ 2) :
    fanValue (weightedSign S w) u v ≤ 1 := by
  classical
  rcases Nat.lt_or_ge (Fintype.card ι) 2 with hlt | hge
  · -- no orthonormal pair exists
    exfalso
    obtain ⟨a⟩ : Nonempty ι := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have := huv.left_self
      simp [dotProduct] at this
    have hall : ∀ k : ι, k = a := fun k ↦
      Fintype.card_le_one_iff.mp (by omega) k a
    have hsum : ∀ f : ι → ℝ, ∑ k, f k = f a := fun f ↦
      Fintype.sum_eq_single a (fun k hk ↦ absurd (hall k) hk)
    have e1 := huv.left_self; have e2 := huv.right_self; have e3 := huv.left_right
    simp only [dotProduct, hsum] at e1 e2 e3
    nlinarith [e1, e2, e3]
  · have h2 : Fintype.card ι = 2 := le_antisymm hcard hge
    have hcu : (univ : Finset ι).card = 2 := by rw [card_univ]; exact h2
    obtain ⟨a, b, hab, huniv⟩ := Finset.card_eq_two.mp hcu
    have hsum : ∀ f : ι → ℝ, ∑ k, f k = f a + f b := fun f ↦ by
      rw [huniv, sum_pair hab]
    have hbes : ∀ k, u k * u k + v k * v k ≤ 1 := by
      intro k
      have := IsOrthonormalPair.sq_add_sq_le huv (basisVec k)
      have e1 : u ⬝ᵥ (basisVec k) = u k := by simp [dotProduct, basisVec]
      have e2 : v ⬝ᵥ (basisVec k) = v k := by simp [dotProduct, basisVec]
      have e3 : (basisVec k) ⬝ᵥ (basisVec k) = 1 := by simp [basisVec_dotProduct_basisVec]
      rw [e1, e2, e3] at this
      nlinarith [this]
    have hnu := huv.left_self; have hnv := huv.right_self
    simp only [dotProduct, hsum] at hnu hnv
    have hpa : u a * u a + v a * v a = 1 := by linarith [hbes a, hbes b]
    have hpb : u b * u b + v b * v b = 1 := by linarith [hbes a, hbes b]
    have hfr := sum_sum_gram_sq huv
    simp only [hsum] at hfr
    have hpab : u a * u b + v a * v b = 0 := by
      have : (u a * u b + v a * v b) ^ 2 = 0 := by
        have e : (u b * u a + v b * v a) = (u a * u b + v a * v b) := by ring
        rw [e] at hfr
        nlinarith [hfr, hpa, hpb]
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    rw [fanValue_eq_sum]
    simp only [hsum, weightedSign, Matrix.of_apply, hS.diag]
    have hwa := Real.mul_self_sqrt (hw.nonneg a)
    have hwb := Real.mul_self_sqrt (hw.nonneg b)
    have hwsum : w a + w b = 1 := by rw [← hsum, hw.sum_eq]
    have e : u b * u a + v b * v a = 0 := by linarith [hpab]
    rw [hpab, e, hpa, hpb]
    nlinarith [hwa, hwb, hwsum]

end

end ProjectionConstants.GrunbaumConjecture
