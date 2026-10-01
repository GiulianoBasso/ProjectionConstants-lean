/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Matrix.KyFan.Basic
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Ky Fan's maximum principle

For a symmetric real matrix `A` and `n ≤ |ι|`, the Ky Fan sum
`kyFanSum n A = sup { Tr(AP) : P an orthogonal projection of rank n }` is the sum of the `n`
largest eigenvalues of `A`. The supremum is attained at the orthogonal projection onto the span of
eigenvectors for the `n` largest eigenvalues. For the upper bound, write
`Tr(AP) = ∑ₖ λₖ eₖᵀPeₖ` in an orthonormal eigenbasis `(eₖ)`: the weights `eₖᵀPeₖ` lie in
`[0, 1]` and have total mass `Tr P = n`.

## Main definitions

* `eigenvec hA k`: the `k`-th eigenvector of a symmetric matrix, as a function `ι → ℝ`.
* `spectralProj hA T`: the orthogonal projection onto the span of the eigenvectors `k ∈ T`.

## Main statements

* `kyFanSum_eq_sum_eigenvalues₀`: **Ky Fan's maximum principle**, with Mathlib's `eigenvalues₀`
  listing the eigenvalues in decreasing order.
* `fanValue_le`, `fanValue_eigenvec`, `kyFanSum_two_eq`: the case `n = 2`, in terms of
  orthonormal pairs; `kyFanSum 2 A` is the sum of the two largest eigenvalues, attained at a pair
  of eigenvectors (`exists_fanValue_eq_kyFanSum_two`).
* `kyFanSum_two_le_of_pairs`: if every sum of two eigenvalues is at most `c`, then
  `kyFanSum 2 A ≤ c`.

## References

* [K. Fan, *On a theorem of Weyl concerning eigenvalues of linear transformations I*][Fan1949]
-/

open Finset Matrix

namespace ProjectionConstants

/-! ### Two elementary inequalities -/

section Elementary

variable {κ : Type*} [Fintype κ]

/-- If `a` is a largest and `b` a second largest index of `l`, and `0 ≤ α ≤ 1` with `∑ α = 2`,
then `∑ lⱼ αⱼ ≤ l a + l b`. -/
private lemma sum_mul_le_top_two (l α : κ → ℝ) (h0 : ∀ j, 0 ≤ α j) (h1 : ∀ j, α j ≤ 1)
    (hsum : ∑ j, α j = 2) {a b : κ} (ha : ∀ j, l j ≤ l a)
    (hb : ∀ j, j ≠ a → l j ≤ l b) : ∑ j, l j * α j ≤ l a + l b := by
  classical
  have key : ∑ j, l j * α j = ∑ j, (l j - l b) * α j + 2 * l b := by
    rw [← hsum, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  have hrest : ∑ j ∈ univ.erase a, (l j - l b) * α j ≤ 0 := by
    refine sum_nonpos fun j hj ↦ ?_
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hb j (ne_of_mem_erase hj)]) (h0 j)
  have htop : (l a - l b) * α a ≤ l a - l b := by
    have := ha b
    nlinarith [h1 a, h0 a]
  rw [key, ← add_sum_erase _ _ (mem_univ a)]
  linarith

/-- Every family indexed by a type with at least two elements has a largest and a second largest
index. -/
lemma exists_top_two (l : κ → ℝ) (h2 : 1 < Fintype.card κ) :
    ∃ a b, a ≠ b ∧ (∀ j, l j ≤ l a) ∧ (∀ j, j ≠ a → l j ≤ l b) := by
  classical
  obtain ⟨a, -, ha⟩ := exists_max_image univ l (univ_nonempty_iff.2 (by
    exact Fintype.card_pos_iff.mp (by omega)))
  have hne : (univ.erase a).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ a), card_univ]
    omega
  obtain ⟨b, hb, hbmax⟩ := exists_max_image (univ.erase a) l hne
  refine ⟨a, b, (ne_of_mem_erase hb).symm, fun j ↦ ha j (mem_univ j), fun j hj ↦ ?_⟩
  exact hbmax j (mem_erase.2 ⟨hj, mem_univ j⟩)

omit [Fintype κ] in
/-- For a top pair `(a, b)`, every pair sum `l i + l j` with `i ≠ j` is at most `l a + l b`. -/
private lemma add_le_top_two (l : κ → ℝ) {a b : κ} (ha : ∀ j, l j ≤ l a)
    (hb : ∀ j, j ≠ a → l j ≤ l b) {i j : κ} (hij : i ≠ j) : l i + l j ≤ l a + l b := by
  by_cases hi : i = a
  · subst hi
    linarith [hb j (Ne.symm hij)]
  · by_cases hj : j = a
    · subst hj
      linarith [hb i hij]
    · linarith [ha i, hb j hj, ha j, hb i hi, ha b]

/-- The knapsack inequality: if `0 ≤ α ≤ 1` has total mass `|T|` and `T` collects the largest
values of `l`, then `∑ₖ lₖ αₖ ≤ ∑_{k ∈ T} lₖ`. -/
private lemma sum_mul_le_sum_of_top (l α : κ → ℝ) (T : Finset κ) (c : ℝ)
    (h0 : ∀ k, 0 ≤ α k) (h1 : ∀ k, α k ≤ 1) (hsum : ∑ k, α k = T.card)
    (hT : ∀ k ∈ T, c ≤ l k) (hTc : ∀ k ∉ T, l k ≤ c) :
    ∑ k, l k * α k ≤ ∑ k ∈ T, l k := by
  classical
  have e1 : ∑ k, l k * α k - ∑ k ∈ T, l k =
      ∑ k ∈ T, (l k - c) * (α k - 1) + ∑ k ∈ Tᶜ, (l k - c) * α k := by
    have hsplit := sum_add_sum_compl T (fun k ↦ (l k - c) * α k)
    have hs2 : ∑ k ∈ T, (l k - c) * (α k - 1) =
        ∑ k ∈ T, (l k - c) * α k - ∑ k ∈ T, l k + c * T.card := by
      simp only [mul_sub, mul_one, sum_sub_distrib, sum_const, nsmul_eq_mul]
      ring
    have hs3 : ∑ k, (l k - c) * α k = ∑ k, l k * α k - c * T.card := by
      simp only [sub_mul, sum_sub_distrib, ← mul_sum, hsum]
    rw [hs2]
    linarith
  have e2 : ∑ k ∈ T, (l k - c) * (α k - 1) ≤ 0 :=
    sum_nonpos fun k hk ↦ mul_nonpos_of_nonneg_of_nonpos (by linarith [hT k hk])
      (by linarith [h1 k])
  have e3 : ∑ k ∈ Tᶜ, (l k - c) * α k ≤ 0 :=
    sum_nonpos fun k hk ↦ mul_nonpos_of_nonpos_of_nonneg
      (by linarith [hTc k (Finset.mem_compl.mp hk)]) (h0 k)
  linarith

end Elementary

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-! ### Eigenvectors -/

/-- The `k`-th eigenvector of a symmetric matrix (the `k`-th column of the eigenvector matrix). -/
noncomputable def eigenvec (hA : A.IsHermitian) (k : ι) : ι → ℝ :=
  fun i ↦ (hA.eigenvectorUnitary : Matrix ι ι ℝ) i k

/-- The eigenvectors are orthonormal: `eₖ ⬝ᵥ eₗ = δₖₗ`. -/
lemma eigenvec_dotProduct (hA : A.IsHermitian) (k l : ι) :
    eigenvec hA k ⬝ᵥ eigenvec hA l = if k = l then 1 else 0 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have := congrFun (congrFun h k) l
  simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply] at this
  rw [← this]
  simp only [dotProduct, eigenvec]

/-- The eigenvectors form an orthonormal basis: `∑ₖ (eₖ)ᵢ (eₖ)ⱼ = δᵢⱼ`. -/
lemma sum_eigenvec_mul (hA : A.IsHermitian) (i j : ι) :
    ∑ k, eigenvec hA k i * eigenvec hA k j = if i = j then 1 else 0 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have := congrFun (congrFun h i) j
  simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply] at this
  rw [← this]
  simp only [eigenvec]

/-- `A eₖ = λₖ eₖ`. -/
lemma mulVec_eigenvec (hA : A.IsHermitian) (k i : ι) :
    (A *ᵥ eigenvec hA k) i = hA.eigenvalues k * eigenvec hA k i := by
  have h := congrFun (hA.mulVec_eigenvectorBasis k) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  simp only [Matrix.mulVec, dotProduct, eigenvec, Matrix.IsHermitian.eigenvectorUnitary_apply]
  exact h

/-- The expansion of a vector in the eigenbasis. -/
lemma eq_sum_eigenvec (hA : A.IsHermitian) (x : ι → ℝ) (i : ι) :
    x i = ∑ k, (eigenvec hA k ⬝ᵥ x) * eigenvec hA k i := by
  have : ∑ k, (eigenvec hA k ⬝ᵥ x) * eigenvec hA k i =
      ∑ j, x j * ∑ k, eigenvec hA k j * eigenvec hA k i := by
    simp only [dotProduct, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring
  rw [this]
  simp only [sum_eigenvec_mul, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]

/-- Parseval's identity for the eigenbasis. -/
lemma sum_eigenvec_dotProduct_mul (hA : A.IsHermitian) (x y : ι → ℝ) :
    ∑ k, (eigenvec hA k ⬝ᵥ x) * (eigenvec hA k ⬝ᵥ y) = x ⬝ᵥ y := by
  calc ∑ k, (eigenvec hA k ⬝ᵥ x) * (eigenvec hA k ⬝ᵥ y)
      = ∑ k, ∑ i, ∑ j, (eigenvec hA k i * x i) * (eigenvec hA k j * y j) := by
        refine sum_congr rfl fun k _ ↦ ?_
        rw [dotProduct, dotProduct, sum_mul_sum]
    _ = ∑ i, ∑ j, ∑ k, (eigenvec hA k i * x i) * (eigenvec hA k j * y j) := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ ↦ sum_comm
    _ = ∑ i, ∑ j, x i * y j * (∑ k, eigenvec hA k i * eigenvec hA k j) := by
        refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
        rw [mul_sum]
        exact sum_congr rfl fun k _ ↦ by ring
    _ = ∑ i, x i * y i := by
        refine sum_congr rfl fun i _ ↦ ?_
        simp only [sum_eigenvec_mul, mul_ite, mul_one, mul_zero]
        simp
    _ = x ⬝ᵥ y := rfl

/-- `xᵀAx = ∑ₖ λₖ ⟨eₖ, x⟩²`. -/
lemma dotProduct_mulVec_eq_sum_eigenvalues (hA : A.IsHermitian) (x : ι → ℝ) :
    x ⬝ᵥ A *ᵥ x = ∑ k, hA.eigenvalues k * (eigenvec hA k ⬝ᵥ x) ^ 2 := by
  have hmv : A *ᵥ x = fun i ↦ ∑ k, (eigenvec hA k ⬝ᵥ x) * (hA.eigenvalues k * eigenvec hA k i) := by
    funext i
    conv_lhs =>
      rw [show x = fun j ↦ ∑ k, (eigenvec hA k ⬝ᵥ x) * eigenvec hA k j from
        funext (eq_sum_eigenvec hA x)]
    simp only [Matrix.mulVec, dotProduct, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [← mulVec_eigenvec hA k i]
    simp only [Matrix.mulVec, dotProduct, mul_sum]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [hmv]
  simp only [dotProduct, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  simp only [sq, mul_sum]
  exact sum_congr rfl fun i _ ↦ by ring

/-- The spectral decomposition `Aᵢⱼ = ∑ₖ λₖ (eₖ)ᵢ (eₖ)ⱼ`. -/
lemma apply_eq_sum_eigenvalues (hA : A.IsHermitian) (i j : ι) :
    A i j = ∑ k, hA.eigenvalues k * eigenvec hA k i * eigenvec hA k j := by
  calc A i j = ∑ l, A i l * (if l = j then 1 else 0) := by simp
    _ = ∑ l, A i l * ∑ k, eigenvec hA k l * eigenvec hA k j := by simp only [sum_eigenvec_mul]
    _ = ∑ k, (∑ l, A i l * eigenvec hA k l) * eigenvec hA k j := by
        simp only [mul_sum, sum_mul]
        rw [sum_comm]
        exact sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ by ring
    _ = ∑ k, hA.eigenvalues k * eigenvec hA k i * eigenvec hA k j := by
        refine sum_congr rfl fun k _ ↦ ?_
        have := mulVec_eigenvec hA k i
        simp only [Matrix.mulVec, dotProduct] at this
        rw [this]

/-- `Tr(AP) = ∑ₖ λₖ eₖᵀPeₖ`. -/
lemma frobeniusInner_eq_sum_eigenvalues (hA : A.IsHermitian) (P : Matrix ι ι ℝ) :
    frobeniusInner A P = ∑ k, hA.eigenvalues k * (eigenvec hA k ⬝ᵥ P *ᵥ eigenvec hA k) := by
  have h1 : frobeniusInner A P =
      ∑ i, ∑ j, ∑ k, hA.eigenvalues k * (P i j * eigenvec hA k i * eigenvec hA k j) := by
    simp only [frobeniusInner]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    rw [apply_eq_sum_eigenvalues hA i j, sum_mul]
    exact sum_congr rfl fun k _ ↦ by ring
  rw [h1]
  simp only [dotProduct_mulVec_self_eq_sum, mul_sum]
  calc ∑ i, ∑ j, ∑ k, hA.eigenvalues k * (P i j * eigenvec hA k i * eigenvec hA k j)
      = ∑ i, ∑ k, ∑ j, hA.eigenvalues k * (P i j * eigenvec hA k i * eigenvec hA k j) :=
        sum_congr rfl fun i _ ↦ sum_comm
    _ = ∑ k, ∑ i, ∑ j, hA.eigenvalues k * (P i j * eigenvec hA k i * eigenvec hA k j) :=
        sum_comm

/-- `∑ₖ eₖᵀPeₖ = Tr P`. -/
lemma sum_eigenvec_dotProduct_mulVec (hA : A.IsHermitian) (P : Matrix ι ι ℝ) :
    ∑ k, eigenvec hA k ⬝ᵥ P *ᵥ eigenvec hA k = P.trace := by
  simp only [dotProduct_mulVec_self_eq_sum]
  calc ∑ k, ∑ i, ∑ j, P i j * eigenvec hA k i * eigenvec hA k j
      = ∑ i, ∑ j, P i j * ∑ k, eigenvec hA k i * eigenvec hA k j := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ ↦ ?_
        rw [sum_comm]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [mul_sum]
        exact sum_congr rfl fun k _ ↦ by ring
    _ = P.trace := by
        simp only [sum_eigenvec_mul, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true]
        rfl

/-! ### Spectral projections -/

/-- The orthogonal projection onto the span of the eigenvectors `eₖ`, `k ∈ T`. -/
noncomputable def spectralProj (hA : A.IsHermitian) (T : Finset ι) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ ∑ k ∈ T, eigenvec hA k i * eigenvec hA k j

/-- `spectralProj hA T` is an orthogonal projection. -/
lemma isStarProjection_spectralProj (hA : A.IsHermitian) (T : Finset ι) :
    IsStarProjection (spectralProj hA T) := by
  refine .of_conjTranspose_eq ?_ ?_
  · ext i j
    simp only [spectralProj, conjTranspose_apply, Matrix.of_apply, star_trivial]
    exact sum_congr rfl fun k _ ↦ by ring
  · ext i j
    simp only [spectralProj, Matrix.mul_apply, Matrix.of_apply]
    calc ∑ l, (∑ k ∈ T, eigenvec hA k i * eigenvec hA k l) *
          (∑ k' ∈ T, eigenvec hA k' l * eigenvec hA k' j)
        = ∑ l, ∑ k ∈ T, ∑ k' ∈ T,
            eigenvec hA k i * eigenvec hA k' j * (eigenvec hA k l * eigenvec hA k' l) := by
          refine sum_congr rfl fun l _ ↦ ?_
          rw [sum_mul_sum]
          exact sum_congr rfl fun k _ ↦ sum_congr rfl fun k' _ ↦ by ring
      _ = ∑ k ∈ T, ∑ l, ∑ k' ∈ T,
            eigenvec hA k i * eigenvec hA k' j * (eigenvec hA k l * eigenvec hA k' l) :=
          sum_comm
      _ = ∑ k ∈ T, ∑ k' ∈ T, ∑ l,
            eigenvec hA k i * eigenvec hA k' j * (eigenvec hA k l * eigenvec hA k' l) :=
          sum_congr rfl fun k _ ↦ sum_comm
      _ = ∑ k ∈ T, ∑ k' ∈ T,
            eigenvec hA k i * eigenvec hA k' j * (eigenvec hA k ⬝ᵥ eigenvec hA k') := by
          refine sum_congr rfl fun k _ ↦ sum_congr rfl fun k' _ ↦ ?_
          rw [dotProduct, mul_sum]
      _ = ∑ k ∈ T, eigenvec hA k i * eigenvec hA k j := by
          refine sum_congr rfl fun k hk ↦ ?_
          simp only [eigenvec_dotProduct, mul_ite, mul_one, mul_zero]
          rw [sum_ite_eq]
          simp [hk]

/-- `spectralProj hA T` has trace, equivalently rank, `|T|`. -/
lemma trace_spectralProj (hA : A.IsHermitian) (T : Finset ι) :
    (spectralProj hA T).trace = T.card := by
  simp only [Matrix.trace, Matrix.diag, spectralProj, Matrix.of_apply]
  rw [sum_comm]
  have h1 : ∀ k, ∑ i, eigenvec hA k i * eigenvec hA k i = 1 := fun k ↦ by
    have := eigenvec_dotProduct hA k k
    simpa [dotProduct] using this
  simp only [h1, sum_const, nsmul_eq_mul, mul_one]

/-- `eₖᵀ (spectralProj hA T) eₖ` is `1` for `k ∈ T` and `0` otherwise. -/
lemma eigenvec_dotProduct_mulVec_spectralProj (hA : A.IsHermitian) (T : Finset ι) (k : ι) :
    eigenvec hA k ⬝ᵥ spectralProj hA T *ᵥ eigenvec hA k = if k ∈ T then 1 else 0 := by
  have e1 : eigenvec hA k ⬝ᵥ spectralProj hA T *ᵥ eigenvec hA k =
      ∑ k' ∈ T, (eigenvec hA k' ⬝ᵥ eigenvec hA k) ^ 2 := by
    calc eigenvec hA k ⬝ᵥ spectralProj hA T *ᵥ eigenvec hA k
        = ∑ i, ∑ j, ∑ k' ∈ T,
            eigenvec hA k' i * eigenvec hA k i * (eigenvec hA k' j * eigenvec hA k j) := by
          simp only [dotProduct_mulVec_self_eq_sum, spectralProj, Matrix.of_apply]
          refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
          rw [sum_mul, sum_mul]
          exact sum_congr rfl fun k' _ ↦ by ring
      _ = ∑ i, ∑ k' ∈ T, ∑ j,
            eigenvec hA k' i * eigenvec hA k i * (eigenvec hA k' j * eigenvec hA k j) :=
          sum_congr rfl fun i _ ↦ sum_comm
      _ = ∑ k' ∈ T, ∑ i, ∑ j,
            eigenvec hA k' i * eigenvec hA k i * (eigenvec hA k' j * eigenvec hA k j) :=
          sum_comm
      _ = ∑ k' ∈ T, (eigenvec hA k' ⬝ᵥ eigenvec hA k) ^ 2 := by
          refine sum_congr rfl fun k' _ ↦ ?_
          rw [sq, dotProduct, sum_mul_sum]
  rw [e1]
  simp only [eigenvec_dotProduct, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  rw [sum_ite_eq']

/-- `Tr(A · spectralProj hA T) = ∑_{k ∈ T} λₖ`. -/
lemma frobeniusInner_spectralProj (hA : A.IsHermitian) (T : Finset ι) :
    frobeniusInner A (spectralProj hA T) = ∑ k ∈ T, hA.eigenvalues k := by
  rw [frobeniusInner_eq_sum_eigenvalues hA]
  simp only [eigenvec_dotProduct_mulVec_spectralProj, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext k
  simp

/-! ### Ky Fan's maximum principle -/

/-- **Ky Fan's maximum principle.** For a symmetric matrix `A` and `n ≤ |ι|`, `kyFanSum n A` is the
sum of the `n` largest eigenvalues of `A`. -/
theorem kyFanSum_eq_sum_eigenvalues₀ (hA : A.IsHermitian) {n : ℕ} (hn : n ≤ Fintype.card ι) :
    kyFanSum n A = ∑ k ∈ univ.filter (fun k : Fin (Fintype.card ι) ↦ k.val < n),
      hA.eigenvalues₀ k := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) with he
  have hev : ∀ i, hA.eigenvalues i = hA.eigenvalues₀ (e.symm i) := fun i ↦ rfl
  set T : Finset ι := univ.filter fun i ↦ (e.symm i).val < n with hT
  have hsumT : ∑ i ∈ T, hA.eigenvalues i =
      ∑ k ∈ univ.filter (fun k : Fin (Fintype.card ι) ↦ k.val < n), hA.eigenvalues₀ k :=
    Finset.sum_equiv e.symm (fun i ↦ by simp [hT]) (fun i _ ↦ hev i)
  have hcardT : T.card = n := by
    have h1 : T.card = (univ.filter fun k : Fin (Fintype.card ι) ↦ k.val < n).card :=
      Finset.card_equiv e.symm (fun i ↦ by simp [hT])
    rw [h1, Fin.card_filter_val_lt, min_eq_right hn]
  have hPT : spectralProj hA T ∈ orthProjs ℝ ι n :=
    ⟨isStarProjection_spectralProj hA T, by rw [trace_spectralProj, hcardT]⟩
  -- every projection of rank `n` gives at most the top sum
  have hbound : ∀ P ∈ orthProjs ℝ ι n, frobeniusInner A P ≤ ∑ i ∈ T, hA.eigenvalues i := by
    intro P hP
    rw [frobeniusInner_eq_sum_eigenvalues hA]
    have h0 : ∀ k, 0 ≤ eigenvec hA k ⬝ᵥ P *ᵥ eigenvec hA k := fun k ↦
      hP.1.dotProduct_mulVec_nonneg _
    have h1 : ∀ k, eigenvec hA k ⬝ᵥ P *ᵥ eigenvec hA k ≤ 1 := fun k ↦ by
      have := hP.1.dotProduct_mulVec_le (eigenvec hA k)
      rwa [eigenvec_dotProduct, ite_eq_left rfl] at this
    have hs : ∑ k, eigenvec hA k ⬝ᵥ P *ᵥ eigenvec hA k = T.card := by
      rw [sum_eigenvec_dotProduct_mulVec hA, hP.2, hcardT]
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- `n = 0`: all weights vanish
      have hs0 : ∑ k, eigenvec hA k ⬝ᵥ P *ᵥ eigenvec hA k = 0 := by
        rw [hs, hcardT, hn0, Nat.cast_zero]
      have hz : ∀ k, eigenvec hA k ⬝ᵥ P *ᵥ eigenvec hA k = 0 := fun k ↦
        (sum_eq_zero_iff_of_nonneg (fun k _ ↦ h0 k)).mp hs0 k (mem_univ k)
      have hT0 : T = ∅ := by rw [← card_eq_zero, hcardT, hn0]
      simp [hz, hT0]
    · set k₀ : Fin (Fintype.card ι) := ⟨n - 1, by omega⟩ with hk₀
      refine sum_mul_le_sum_of_top _ _ T (hA.eigenvalues₀ k₀) h0 h1 hs (fun k hk ↦ ?_)
        (fun k hk ↦ ?_)
      · rw [hev]
        apply hA.eigenvalues₀_antitone
        simp only [hT, mem_filter, mem_univ, true_and] at hk
        change ((e.symm k : Fin _) : ℕ) ≤ n - 1
        omega
      · rw [hev]
        apply hA.eigenvalues₀_antitone
        simp only [hT, mem_filter, mem_univ, true_and, not_lt] at hk
        change n - 1 ≤ ((e.symm k : Fin _) : ℕ)
        omega
  rw [← hsumT]
  refine le_antisymm (csSup_le ⟨_, spectralProj hA T, hPT, rfl⟩ ?_) ?_
  · rintro _ ⟨P, hP, rfl⟩
    exact hbound P hP
  · rw [← frobeniusInner_spectralProj hA T]
    exact frobeniusInner_le_kyFanSum A hPT

/-! ### The case `n = 2` -/

/-- **Ky Fan's inequality** for `n = 2`: `uᵀAu + vᵀAv ≤ λ_a + λ_b` for orthonormal `u, v`, where
`λ_a ≥ λ_b` are the two largest eigenvalues. -/
theorem fanValue_le (hA : A.IsHermitian) {u v : ι → ℝ} (huv : IsOrthonormalPair u v) {a b : ι}
    (ha : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues a)
    (hb : ∀ j, j ≠ a → hA.eigenvalues j ≤ hA.eigenvalues b) :
    fanValue A u v ≤ hA.eigenvalues a + hA.eigenvalues b := by
  have hsum : fanValue A u v =
      ∑ k, hA.eigenvalues k * ((eigenvec hA k ⬝ᵥ u) ^ 2 + (eigenvec hA k ⬝ᵥ v) ^ 2) := by
    simp only [fanValue, dotProduct_mulVec_eq_sum_eigenvalues hA, mul_add, sum_add_distrib]
  rw [hsum]
  have h1 : ∀ k, (eigenvec hA k ⬝ᵥ u) ^ 2 + (eigenvec hA k ⬝ᵥ v) ^ 2 ≤ 1 := by
    intro k
    have := huv.sq_add_sq_le (eigenvec hA k)
    rw [dotProduct_comm u, dotProduct_comm v, eigenvec_dotProduct] at this
    simpa using this
  have h2 : ∑ k, ((eigenvec hA k ⬝ᵥ u) ^ 2 + (eigenvec hA k ⬝ᵥ v) ^ 2) = 2 := by
    rw [sum_add_distrib]
    have e1 := sum_eigenvec_dotProduct_mul hA u u
    have e2 := sum_eigenvec_dotProduct_mul hA v v
    simp only [sq]
    rw [e1, e2, huv.left_self, huv.right_self]
    norm_num
  exact sum_mul_le_top_two _ _ (fun k ↦ by positivity) h1 h2 ha hb

/-- Pairs of eigenvectors realize Ky Fan's bound. -/
theorem fanValue_eigenvec (hA : A.IsHermitian) {a b : ι} (hab : a ≠ b) :
    IsOrthonormalPair (eigenvec hA a) (eigenvec hA b) ∧
      fanValue A (eigenvec hA a) (eigenvec hA b) = hA.eigenvalues a + hA.eigenvalues b := by
  refine ⟨⟨by simp [eigenvec_dotProduct], by simp [eigenvec_dotProduct],
    by simp [eigenvec_dotProduct, hab]⟩, ?_⟩
  have e : ∀ k, eigenvec hA k ⬝ᵥ A *ᵥ eigenvec hA k = hA.eigenvalues k := by
    intro k
    have : A *ᵥ eigenvec hA k = fun i ↦ hA.eigenvalues k * eigenvec hA k i :=
      funext (mulVec_eigenvec hA k)
    rw [this]
    simp only [dotProduct, mul_left_comm _ (hA.eigenvalues k), ← mul_sum]
    have := eigenvec_dotProduct hA k k
    simp only [dotProduct, ite_true] at this
    rw [this, mul_one]
  simp only [fanValue, e]

/-- `kyFanSum 2 A` is the sum of the two largest eigenvalues. -/
theorem kyFanSum_two_eq (hA : A.IsHermitian) {a b : ι} (hab : a ≠ b)
    (ha : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues a)
    (hb : ∀ j, j ≠ a → hA.eigenvalues j ≤ hA.eigenvalues b) :
    kyFanSum 2 A = hA.eigenvalues a + hA.eigenvalues b := by
  obtain ⟨hon, hval⟩ := fanValue_eigenvec hA hab
  apply le_antisymm
  · exact kyFanSum_two_le ⟨_, _, _, hon, rfl⟩ fun u v huv ↦ fanValue_le hA huv ha hb
  · rw [← hval]; exact fanValue_le_kyFanSum_two A hon

/-- If every pair of eigenvalues sums to at most `c`, then `kyFanSum 2 A ≤ c` (for `|ι| ≥ 2`). -/
theorem kyFanSum_two_le_of_pairs (hA : A.IsHermitian) (h2 : 1 < Fintype.card ι) {c : ℝ}
    (h : ∀ i j, i ≠ j → hA.eigenvalues i + hA.eigenvalues j ≤ c) : kyFanSum 2 A ≤ c := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_top_two hA.eigenvalues h2
  rw [kyFanSum_two_eq hA hab ha hb]
  exact h a b hab

omit [DecidableEq ι] in
/-- `kyFanSum 2 A` is attained by an orthonormal pair, for symmetric `A` and `|ι| ≥ 2`. -/
theorem exists_fanValue_eq_kyFanSum_two (hA : A.IsHermitian) (h2 : 1 < Fintype.card ι) :
    ∃ u v, IsOrthonormalPair u v ∧ fanValue A u v = kyFanSum 2 A := by
  classical
  obtain ⟨a, b, hab, ha, hb⟩ := exists_top_two hA.eigenvalues h2
  obtain ⟨hon, hval⟩ := fanValue_eigenvec hA hab
  exact ⟨_, _, hon, by rw [hval, kyFanSum_two_eq hA hab ha hb]⟩

end ProjectionConstants
