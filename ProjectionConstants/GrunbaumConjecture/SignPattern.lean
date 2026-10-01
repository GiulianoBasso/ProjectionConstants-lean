/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Matrix.KyFan.Stationary

/-!
# The sign pattern of a maximizer

Fix weights `w > 0`, let `D = diag(w)`, and let the sign matrix `S` maximize
`kyFanSum 2 (√D S' √D)` over all sign matrices `S'` (`IsMaxSign S w`). Let `u, v` be an
orthonormal pair with `fanValue M u v = kyFanSum 2 M` for `M = √D S √D`, and write
`pᵢⱼ = uᵢuⱼ + vᵢvⱼ` for the entries of the orthogonal projection `uuᵀ + vvᵀ`. If `|ι| ≥ 3`, then
`sᵢⱼ pᵢⱼ > 0` for all `i, j` (`sign_mul_gram_pos`). So `S` is the sign pattern of the vectors
`(uᵢ, vᵢ) ∈ ℝ²`, and their inner products are all non-zero. This is [AMOP, Lemma 3.2] for rank
two, i.e. [JFA-E, Lemma B(b)] for `n = 2`; it is used in Steps 1 and 4 of the proof of
[JFA-E, Theorem A] in `ProjectionConstants.GrunbaumConjecture.Reduction`.

The proof compares `S` with the sign matrices obtained by changing a symmetric pair of entries
(`updateSymm`). Flipping the sign of `sᵢⱼ` changes the value of `u, v` by
`-4 sᵢⱼ √wᵢ √wⱼ pᵢⱼ`, which gives `sᵢⱼ pᵢⱼ ≥ 0`. If `pᵢⱼ = 0`, then `u, v` also maximizes the
average of the two choices of the entry `(i, j)`, so the plane of `u, v` is invariant under
`Eᵢⱼ + Eⱼᵢ`. This forces `uuᵀ + vvᵀ` to be a multiple of the identity, which is impossible for
`|ι| ≥ 3`, since its trace and the sum of the squares of its entries are both `2`.

## Main definitions

* `IsMaxSign S w`: `S` maximizes `kyFanSum 2 (weightedSign S' w)` over all sign matrices `S'`.
* `symmSingle i j`: the symmetric matrix `Eᵢⱼ + Eⱼᵢ`.
* `updateSymm S i j t`: the matrix `S` with the entries `(i, j)` and `(j, i)` replaced by `t`.

## Main statements

* `sign_mul_gram_nonneg`: the weak sign pattern `sᵢⱼ pᵢⱼ ≥ 0` for `i ≠ j`.
* `gram_of_gram_eq_zero`: the consequences of a vanishing entry `pᵢⱼ = 0` with `i ≠ j`.
* `sign_mul_gram_pos`: the strict sign pattern `sᵢⱼ pᵢⱼ > 0` ([AMOP, Lemma 3.2]).

## References

* [AMOP] G. Basso, *Almost minimal orthogonal projections*, arXiv:2001.08698.
* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Finset Matrix

namespace ProjectionConstants.GrunbaumConjecture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `S` maximizes `kyFanSum 2 (√D S √D)` among all sign matrices, for fixed weights `w`. -/
def IsMaxSign (S : Matrix ι ι ℝ) (w : ι → ℝ) : Prop :=
  ∀ S', IsSignMatrix S' → kyFanSum 2 (weightedSign S' w) ≤ kyFanSum 2 (weightedSign S w)

/-- The symmetric matrix `Eᵢⱼ + Eⱼᵢ`. -/
def symmSingle (i j : ι) : Matrix ι ι ℝ :=
  Matrix.of fun k l ↦ (if k = i ∧ l = j then 1 else 0) + (if k = j ∧ l = i then 1 else 0)

omit [Fintype ι] in
lemma symmSingle_apply_comm (i j : ι) : ∀ k l, symmSingle i j l k = symmSingle i j k l := by
  intro k l
  simp only [symmSingle, Matrix.of_apply]
  simp only [@and_comm (l = i) (k = j), @and_comm (l = j) (k = i)]
  ring

lemma mulVec_symmSingle_apply (i j : ι) (x : ι → ℝ) (k : ι) :
    (symmSingle i j *ᵥ x) k = (if k = i then x j else 0) + (if k = j then x i else 0) := by
  simp only [mulVec_apply_eq_sum, symmSingle, Matrix.of_apply, add_mul, sum_add_distrib, ite_mul,
    one_mul, zero_mul]
  congr 1
  · by_cases hk : k = i <;> simp [hk]
  · by_cases hk : k = j <;> simp [hk]

lemma dotProduct_mulVec_symmSingle (i j : ι) (x : ι → ℝ) :
    x ⬝ᵥ symmSingle i j *ᵥ x = 2 * (x i * x j) := by
  simp only [dotProduct, mulVec_symmSingle_apply, mul_add, sum_add_distrib, mul_ite, mul_zero,
    sum_ite_eq', mem_univ, ite_true]
  ring

lemma fanValue_symmSingle (i j : ι) (x y : ι → ℝ) :
    fanValue (symmSingle i j) x y = 2 * (x i * x j + y i * y j) := by
  simp only [fanValue, dotProduct_mulVec_symmSingle]; ring

omit [DecidableEq ι] in
/-- Linearity of `fanValue` in the matrix. -/
lemma fanValue_eq_add_mul {A A' B : Matrix ι ι ℝ} {c : ℝ} (h : ∀ k l, A' k l = A k l + c * B k l)
    (x y : ι → ℝ) : fanValue A' x y = fanValue A x y + c * fanValue B x y := by
  simp only [fanValue_eq_sum, h, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
  ring

omit [DecidableEq ι] in
/-- Linearity of `A *ᵥ x` in the matrix. -/
lemma mulVec_apply_eq_add_mul {A A' B : Matrix ι ι ℝ} {c : ℝ}
    (h : ∀ k l, A' k l = A k l + c * B k l) (x : ι → ℝ) (k : ι) :
    (A' *ᵥ x) k = (A *ᵥ x) k + c * (B *ᵥ x) k := by
  simp only [mulVec_apply_eq_sum, h, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun l _ ↦ ?_
  ring

/-- `S` with the entries `(i, j)` and `(j, i)` replaced by `t`. -/
def updateSymm (S : Matrix ι ι ℝ) (i j : ι) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun k l ↦ if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then t else S k l

omit [Fintype ι] in
/-- Changing a symmetric pair of off-diagonal entries of a sign matrix to `±1` gives a sign
matrix. -/
lemma isSignMatrix_updateSymm {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {i j : ι} (hij : i ≠ j)
    {t : ℝ} (ht : t = 1 ∨ t = -1) : IsSignMatrix (updateSymm S i j t) := by
  refine ⟨fun k l ↦ ?_, fun k l ↦ ?_, fun k ↦ ?_⟩
  · simp only [updateSymm, Matrix.of_apply]
    by_cases h : (k = i ∧ l = j) ∨ (k = j ∧ l = i)
    · have h' : (l = i ∧ k = j) ∨ (l = j ∧ k = i) := by tauto
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : ¬ ((l = i ∧ k = j) ∨ (l = j ∧ k = i)) := by tauto
      rw [ite_eq_right h, ite_eq_right h', hS.symm]
  · simp only [updateSymm, Matrix.of_apply]
    split_ifs
    · exact ht
    · exact hS.pm k l
  · simp only [updateSymm, Matrix.of_apply]
    have : ¬ ((k = i ∧ k = j) ∨ (k = j ∧ k = i)) := by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hij rfl
    rw [ite_eq_right this, hS.diag]

omit [Fintype ι] in
/-- Changing the entries `(i, j)` and `(j, i)` of `S` to `t` adds
`(t - sᵢⱼ) √wᵢ √wⱼ (Eᵢⱼ + Eⱼᵢ)` to `√D S √D`. -/
lemma weightedSign_updateSymm {S : Matrix ι ι ℝ} (hS : IsSignMatrix S) {i j : ι} (hij : i ≠ j)
    (t : ℝ) (w : ι → ℝ) :
    ∀ k l, weightedSign (updateSymm S i j t) w k l =
      weightedSign S w k l + ((t - S i j) * (√(w i) * √(w j))) * symmSingle i j k l := by
  intro k l
  simp only [weightedSign, updateSymm, symmSingle, Matrix.of_apply]
  by_cases h1 : k = i ∧ l = j
  · obtain ⟨rfl, rfl⟩ := h1
    have h2 : ¬ (k = l ∧ l = k) := fun h ↦ hij h.1
    simp [h2]
    ring
  · by_cases h2 : k = j ∧ l = i
    · obtain ⟨rfl, rfl⟩ := h2
      have h1' : ¬ (k = l ∧ l = k) := fun h ↦ hij h.2
      simp [h1', hS.symm]
      ring
    · simp [h1, h2]

/-! ### The weak sign pattern -/

section

variable {S : Matrix ι ι ℝ} {w : ι → ℝ} {u v : ι → ℝ}

omit [DecidableEq ι] in
/-- The weak sign pattern: at a maximizer, `sᵢⱼ (uᵢuⱼ + vᵢvⱼ) ≥ 0` for `i ≠ j`. -/
lemma sign_mul_gram_nonneg (hS : IsSignMatrix S) (hpos : ∀ i, 0 < w i) (hmax : IsMaxSign S w)
    (hval : fanValue (weightedSign S w) u v = kyFanSum 2 (weightedSign S w))
    (huv : IsOrthonormalPair u v) {i j : ι} (hij : i ≠ j) :
    0 ≤ S i j * (u i * u j + v i * v j) := by
  classical
  have hS' := isSignMatrix_updateSymm hS hij (t := - S i j)
    (by rcases hS.pm i j with h | h <;> simp [h])
  have h1 := fanValue_eq_add_mul (weightedSign_updateSymm hS hij (- S i j) w) u v
  rw [fanValue_symmSingle] at h1
  have h2 : fanValue (weightedSign (updateSymm S i j (-S i j)) w) u v ≤
      fanValue (weightedSign S w) u v :=
    (fanValue_le_kyFanSum_two _ huv).trans (hval ▸ hmax _ hS')
  have hw : 0 < √(w i) * √(w j) := mul_pos (Real.sqrt_pos.2 (hpos i)) (Real.sqrt_pos.2 (hpos j))
  have h3 : 0 ≤ (S i j * (u i * u j + v i * v j)) * (4 * (√(w i) * √(w j))) := by nlinarith
  exact nonneg_of_mul_nonneg_left h3 (by positivity)

omit [DecidableEq ι] in
/-- Coefficients of a vector in the plane of an orthonormal pair are its inner products. -/
lemma apply_eq_dotProduct_mul_add {z : ι → ℝ} (huv : IsOrthonormalPair u v) {a b : ℝ}
    (hz : ∀ k, z k = a * u k + b * v k) :
    ∀ k, z k = (u ⬝ᵥ z) * u k + (v ⬝ᵥ z) * v k := by
  have hz' : z = fun k ↦ a * u k + b * v k := funext hz
  have ha : u ⬝ᵥ z = a := by
    rw [hz', dotProduct_linearComb, huv.left_self, huv.left_right]; ring
  have hb : v ⬝ᵥ z = b := by
    rw [hz', dotProduct_linearComb, dotProduct_comm v u, huv.left_right, huv.right_self]; ring
  intro k
  rw [ha, hb]
  exact hz k

/-- At a maximizer, a vanishing entry `uᵢuⱼ + vᵢvⱼ = 0` with `i ≠ j` forces the plane of `u, v`
to be invariant under `Eᵢⱼ + Eⱼᵢ`. -/
lemma mulVec_symmSingle_apply_eq (hS : IsSignMatrix S) (hpos : ∀ i, 0 < w i) (hmax : IsMaxSign S w)
    (hval : fanValue (weightedSign S w) u v = kyFanSum 2 (weightedSign S w))
    (huv : IsOrthonormalPair u v) {i j : ι} (hij : i ≠ j) (hp : u i * u j + v i * v j = 0) :
    (∀ k, (symmSingle i j *ᵥ u) k =
      (u ⬝ᵥ symmSingle i j *ᵥ u) * u k + (v ⬝ᵥ symmSingle i j *ᵥ u) * v k) ∧
    (∀ k, (symmSingle i j *ᵥ v) k =
      (u ⬝ᵥ symmSingle i j *ᵥ v) * u k + (v ⬝ᵥ symmSingle i j *ᵥ v) * v k) := by
  set M := weightedSign S w with hM
  set c : ℝ := S i j * (√(w i) * √(w j)) with hc
  have hc0 : c ≠ 0 := by
    have hw : 0 < √(w i) * √(w j) :=
      mul_pos (Real.sqrt_pos.2 (hpos i)) (Real.sqrt_pos.2 (hpos j))
    rcases hS.pm i j with h | h <;> rw [hc, h] <;> nlinarith
  set A₀ : Matrix ι ι ℝ := Matrix.of fun k l ↦ M k l + (-c) * symmSingle i j k l with hA₀
  have hA₀e : ∀ k l, A₀ k l = M k l + (-c) * symmSingle i j k l := fun k l ↦ rfl
  have hMs : ∀ k l, M l k = M k l := IsSignMatrix.weightedSign_comm hS w
  have hA₀s : ∀ k l, A₀ l k = A₀ k l := by
    intro k l; rw [hA₀e, hA₀e, hMs, symmSingle_apply_comm]
  -- `(u, v)` maximizes `fanValue M`
  have hmaxM : ∀ x y, IsOrthonormalPair x y → fanValue M x y ≤ fanValue M u v := fun x y hxy ↦
    hval ▸ fanValue_le_kyFanSum_two M hxy
  -- `(u, v)` maximizes `fanValue A₀`, since `A₀` is the average of two flips of `M`
  have hmaxA : ∀ x y, IsOrthonormalPair x y → fanValue A₀ x y ≤ fanValue A₀ u v := by
    intro x y hxy
    have hp1 := fanValue_eq_add_mul (weightedSign_updateSymm hS hij 1 w) x y
    have hm1 := fanValue_eq_add_mul (weightedSign_updateSymm hS hij (-1) w) x y
    have h1 : fanValue (weightedSign (updateSymm S i j 1) w) x y ≤ fanValue M u v :=
      (fanValue_le_kyFanSum_two _ hxy).trans
        (hval ▸ hmax _ (isSignMatrix_updateSymm hS hij (Or.inl rfl)))
    have h2 : fanValue (weightedSign (updateSymm S i j (-1)) w) x y ≤ fanValue M u v :=
      (fanValue_le_kyFanSum_two _ hxy).trans
        (hval ▸ hmax _ (isSignMatrix_updateSymm hS hij (Or.inr rfl)))
    have hx := fanValue_eq_add_mul hA₀e x y
    have hu := fanValue_eq_add_mul hA₀e u v
    rw [fanValue_symmSingle] at hu
    rw [hp] at hu
    rw [hx, hu]
    rw [← hM] at hp1 hm1
    have : fanValue M x y + -c * fanValue (symmSingle i j) x y =
        (fanValue (weightedSign (updateSymm S i j 1) w) x y +
          fanValue (weightedSign (updateSymm S i j (-1)) w) x y) / 2 := by
      rw [hp1, hm1, hc]; ring
    rw [this]
    linarith
  have hinvM := mulVec_apply_eq_of_fanValue_le (.ext hMs) huv hmaxM
  have hinvM' := mulVec_apply_eq_of_fanValue_le' (.ext hMs) huv hmaxM
  have hinvA := mulVec_apply_eq_of_fanValue_le (.ext hA₀s) huv hmaxA
  have hinvA' := mulVec_apply_eq_of_fanValue_le' (.ext hA₀s) huv hmaxA
  -- the difference `M - A₀ = c (Eᵢⱼ + Eⱼᵢ)`
  have hdiff : ∀ x k, (symmSingle i j *ᵥ x) k = ((M *ᵥ x) k - (A₀ *ᵥ x) k) / c := by
    intro x k
    rw [mulVec_apply_eq_add_mul hA₀e x k]
    field_simp
    ring
  constructor
  · refine apply_eq_dotProduct_mul_add huv (a := (u ⬝ᵥ M *ᵥ u - u ⬝ᵥ A₀ *ᵥ u) / c)
      (b := (v ⬝ᵥ M *ᵥ u - v ⬝ᵥ A₀ *ᵥ u) / c) fun k ↦ ?_
    rw [hdiff, hinvM k, hinvA k]
    field_simp
    ring
  · refine apply_eq_dotProduct_mul_add huv (a := (u ⬝ᵥ M *ᵥ v - u ⬝ᵥ A₀ *ᵥ v) / c)
      (b := (v ⬝ᵥ M *ᵥ v - v ⬝ᵥ A₀ *ᵥ v) / c) fun k ↦ ?_
    rw [hdiff, hinvM' k, hinvA' k]
    field_simp
    ring

omit [DecidableEq ι] in
/-- At a maximizer, a vanishing off-diagonal entry `pᵢⱼ = 0` forces `pᵢᵢ = pⱼⱼ` and
`pᵢₗ = pⱼₗ = 0` for all `l ≠ i, j`, where `pₖₗ = uₖuₗ + vₖvₗ`. -/
lemma gram_of_gram_eq_zero (hS : IsSignMatrix S) (hpos : ∀ i, 0 < w i) (hmax : IsMaxSign S w)
    (hval : fanValue (weightedSign S w) u v = kyFanSum 2 (weightedSign S w))
    (huv : IsOrthonormalPair u v) {i j : ι} (hij : i ≠ j) (hp : u i * u j + v i * v j = 0) :
    u i * u i + v i * v i = u j * u j + v j * v j ∧
      ∀ l, l ≠ i → l ≠ j → u i * u l + v i * v l = 0 ∧ u j * u l + v j * v l = 0 := by
  classical
  obtain ⟨ha, hb⟩ := mulVec_symmSingle_apply_eq hS hpos hmax hval huv hij hp
  -- the symmetry `⟨v, F u⟩ = ⟨u, F v⟩`
  have hsym : v ⬝ᵥ symmSingle i j *ᵥ u = u ⬝ᵥ symmSingle i j *ᵥ v :=
    (IsSymm.ext (symmSingle_apply_comm i j)).dotProduct_mulVec_comm
  -- `a_k u_l + b_k v_l = a_l u_k + b_l v_k`
  have key : ∀ k l, (symmSingle i j *ᵥ u) k * u l + (symmSingle i j *ᵥ v) k * v l =
      (symmSingle i j *ᵥ u) l * u k + (symmSingle i j *ᵥ v) l * v k := by
    intro k l
    rw [ha k, hb k, ha l, hb l, hsym]
    ring
  have hji : j ≠ i := Ne.symm hij
  refine ⟨?_, fun l hli hlj ↦ ⟨?_, ?_⟩⟩
  · have := key i j
    simp only [mulVec_symmSingle_apply, ite_eq_right hij, ite_eq_right hji] at this
    simp at this
    linarith
  · have := key j l
    simp only [mulVec_symmSingle_apply, ite_eq_right hji, ite_eq_right hli,
      ite_eq_right hlj] at this
    simp at this
    linarith
  · have := key i l
    simp only [mulVec_symmSingle_apply, ite_eq_right hij, ite_eq_right hli,
      ite_eq_right hlj] at this
    simp at this
    linarith

omit [DecidableEq ι] in
/-- `∑ₖₗ (uₖuₗ + vₖvₗ)² = 2` for an orthonormal pair `u, v`. -/
lemma sum_sum_gram_sq (huv : IsOrthonormalPair u v) :
    ∑ k, ∑ l, (u k * u l + v k * v l) ^ 2 = 2 := by
  have h1 : ∑ l, u l * u l = 1 := huv.left_self
  have h2 : ∑ l, v l * v l = 1 := huv.right_self
  have h3 : ∑ l, u l * v l = 0 := huv.left_right
  have e : ∀ k, ∑ l, (u k * u l + v k * v l) ^ 2 = u k * u k + v k * v k := by
    intro k
    have : ∑ l, (u k * u l + v k * v l) ^ 2 = u k * u k * (∑ l, u l * u l) +
        2 * (u k * v k) * (∑ l, u l * v l) + v k * v k * (∑ l, v l * v l) := by
      simp only [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun l _ ↦ ?_
      ring
    rw [this, h1, h2, h3]; ring
  rw [sum_congr rfl fun k _ ↦ e k, sum_add_distrib, h1, h2]; norm_num

omit [DecidableEq ι] in
/-- **Strict sign pattern** ([AMOP, Lemma 3.2], [JFA-E, Lemma B(b)]): if `|ι| ≥ 3`, then
`sᵢⱼ (uᵢuⱼ + vᵢvⱼ) > 0` for all `i, j`. -/
theorem sign_mul_gram_pos (hS : IsSignMatrix S) (hpos : ∀ i, 0 < w i) (h3 : 2 < Fintype.card ι)
    (hmax : IsMaxSign S w) (hval : fanValue (weightedSign S w) u v = kyFanSum 2 (weightedSign S w))
    (huv : IsOrthonormalPair u v) :
    ∀ i j, 0 < S i j * (u i * u j + v i * v j) := by
  -- first: no off-diagonal entry of `P` vanishes
  have hoff : ∀ i j, i ≠ j → u i * u j + v i * v j ≠ 0 := by
    intro i₀ j₀ hij₀ hp₀
    obtain ⟨-, hrow⟩ := gram_of_gram_eq_zero hS hpos hmax hval huv hij₀ hp₀
    -- row `i₀` vanishes off the diagonal
    have hrow0 : ∀ l, l ≠ i₀ → u i₀ * u l + v i₀ * v l = 0 := by
      intro l hl
      by_cases hlj : l = j₀
      · subst hlj; exact hp₀
      · exact (hrow l hl hlj).1
    -- hence `P = c · 1`
    set c := u i₀ * u i₀ + v i₀ * v i₀ with hc
    have hdiag : ∀ l, u l * u l + v l * v l = c := by
      intro l
      by_cases hl : l = i₀
      · subst hl; rfl
      · exact ((gram_of_gram_eq_zero hS hpos hmax hval huv (Ne.symm hl) (hrow0 l hl)).1).symm
    have hoffall : ∀ k l, k ≠ l → u k * u l + v k * v l = 0 := by
      intro k l hkl
      by_cases hk : k = i₀
      · subst hk; exact hrow0 l (Ne.symm hkl)
      · by_cases hl : l = i₀
        · subst hl
          have := hrow0 k hk
          linarith [mul_comm (u l) (u k), mul_comm (v l) (v k)]
        · have h' := (gram_of_gram_eq_zero hS hpos hmax hval huv (Ne.symm hk) (hrow0 k hk)).2 l hl
            (Ne.symm hkl)
          exact h'.2
    -- trace and Frobenius norm
    have htr : ∑ k, (u k * u k + v k * v k) = 2 := by
      rw [sum_add_distrib]
      have h1 : ∑ k, u k * u k = 1 := huv.left_self
      have h2 : ∑ k, v k * v k = 1 := huv.right_self
      rw [h1, h2]; norm_num
    have hfr := sum_sum_gram_sq huv
    have hfr' : ∑ k, ∑ l, (u k * u l + v k * v l) ^ 2 = ∑ k : ι, c ^ 2 := by
      refine sum_congr rfl fun k _ ↦ ?_
      rw [Fintype.sum_eq_single k]
      · rw [hdiag k]
      · intro l hl
        rw [hoffall k l (Ne.symm hl)]
        ring
    simp only [hdiag, sum_const, card_univ, nsmul_eq_mul] at htr hfr'
    rw [hfr'] at hfr
    have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (by omega : 0 < Fintype.card ι)
    have hc1 : c = 1 := by
      have hc0 : c ≠ 0 := by
        intro h0; rw [h0, mul_zero] at htr; norm_num at htr
      have : (Fintype.card ι : ℝ) * c * (c - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · linarith
        · exact absurd h' hc0
      · linarith
    rw [hc1, mul_one] at htr
    have : (Fintype.card ι : ℝ) = 2 := htr
    have : Fintype.card ι = 2 := by exact_mod_cast this
    omega
  -- second: no diagonal entry of `P` vanishes
  have hdiag : ∀ i, u i * u i + v i * v i ≠ 0 := by
    intro i hi
    obtain ⟨l, hl⟩ : ∃ l, l ≠ i := by
      by_contra hcon
      push Not at hcon
      have : Fintype.card ι ≤ 1 :=
        Fintype.card_le_one_iff.mpr fun a b ↦ (hcon a).trans (hcon b).symm
      omega
    apply hoff i l (Ne.symm hl)
    have hcs : (u i * u l + v i * v l) ^ 2 ≤ (u i * u i + v i * v i) * (u l * u l + v l * v l) := by
      nlinarith [sq_nonneg (u i * v l - v i * u l)]
    rw [hi, zero_mul] at hcs
    exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hcs (sq_nonneg _))
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hS.diag, one_mul]
    exact lt_of_le_of_ne (by nlinarith [mul_self_nonneg (u i), mul_self_nonneg (v i)])
      (Ne.symm (hdiag i))
  · have h0 := sign_mul_gram_nonneg hS hpos hmax hval huv hij
    have hne : S i j * (u i * u j + v i * v j) ≠ 0 := by
      intro h0
      apply hoff i j hij
      rcases hS.pm i j with h | h <;> rw [h] at h0 <;> linarith
    exact lt_of_le_of_ne h0 (Ne.symm hne)

end

end ProjectionConstants.GrunbaumConjecture
