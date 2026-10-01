/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Matrix.OrthProj
import ProjectionConstants.ForMathlib.Matrix.DotProduct
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Matrix

/-!
# Ky Fan sums

Let `A` be a real square matrix indexed by a finite type `ι`. The Ky Fan sum `kyFanSum n A` is
the supremum of `Tr(AP)` over the orthogonal projections `P` of rank `n`. By Ky Fan's maximum
principle (`kyFanSum_eq_sum_eigenvalues₀` in `ProjectionConstants.Matrix.KyFan.Fan`) it is the
sum of the `n` largest eigenvalues of `A` if `A` is symmetric.

The orthogonal projections of rank two are the matrices `uuᵀ + vvᵀ` for the orthonormal pairs
`u, v`, so `kyFanSum 2 A` is the supremum of `uᵀAu + vᵀAv` over these pairs.

## Main definitions

* `frobeniusInner A B`: the Frobenius inner product `∑ᵢⱼ Aᵢⱼ Bᵢⱼ`; it is `Tr(AB)` if `B` is
  symmetric.
* `orthProjsLe ι n`: the orthogonal projections of trace, equivalently rank, at most `n`.
* `kyFanSum n A`: the supremum of `Tr(AP)` over `P ∈ orthProjs ℝ ι n`.
* `kyFanSumLe n A`: the supremum of `Tr(AP)` over `P ∈ orthProjsLe ι n`; for symmetric `A` this
  is the sum of the positive parts of the `n` largest eigenvalues.
* `IsOrthonormalPair u v`: the vectors `u, v ∈ ℝ^ι` are orthonormal.
* `fanValue A u v`: the value `uᵀAu + vᵀAv` of Ky Fan's functional; `fanValues A` is the set of
  its values at the orthonormal pairs.

## Main statements

* `exists_frobeniusInner_eq_kyFanSumLe`: the supremum defining `kyFanSumLe` is attained.
* `kyFanSumLe_le_add`: `kyFanSumLe n` is Lipschitz in the entries.
* `kyFanSum_submatrix`, `kyFanSumLe_submatrix`: invariance under relabelling the index set.
* `IsOrthonormalPair.sq_add_sq_le`: Bessel's inequality for an orthonormal pair.
* `frobeniusInner_image_orthProjs_two`, `kyFanSum_two_eq_sSup`: `kyFanSum 2 A` is the supremum of
  `uᵀAu + vᵀAv` over the orthonormal pairs `u, v`.

## References

* [K. Fan, *On a theorem of Weyl concerning eigenvalues of linear transformations I*][Fan1949]
-/

open Finset Matrix

namespace ProjectionConstants

variable {ι : Type*} [Fintype ι]

/-- The Frobenius inner product `∑ᵢⱼ Aᵢⱼ Bᵢⱼ` of two real matrices; it is `Tr(AB)` if `B` is
symmetric. -/
def frobeniusInner (A B : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

variable (ι) in
/-- The real orthogonal projections of trace, equivalently rank, at most `n`. -/
def orthProjsLe (n : ℕ) : Set (Matrix ι ι ℝ) := {P | IsStarProjection P ∧ P.trace ≤ n}

/-- The **Ky Fan sum** `sup { Tr(AP) : P an orthogonal projection of rank n }`. For a symmetric
matrix `A` it is the sum of the `n` largest eigenvalues of `A`. -/
noncomputable def kyFanSum (n : ℕ) (A : Matrix ι ι ℝ) : ℝ :=
  sSup (frobeniusInner A '' orthProjs ℝ ι n)

/-- `sup { Tr(AP) : P an orthogonal projection of rank at most n }`. For a symmetric matrix `A`
it is the sum of the positive parts of the `n` largest eigenvalues of `A`. -/
noncomputable def kyFanSumLe (n : ℕ) (A : Matrix ι ι ℝ) : ℝ :=
  sSup (frobeniusInner A '' orthProjsLe ι n)

/-! ### Orthogonal projections of rank at most `n` -/

/-- An orthogonal projection of rank `n` has rank at most `n`. -/
lemma orthProjs_subset_orthProjsLe (n : ℕ) : orthProjs ℝ ι n ⊆ orthProjsLe ι n :=
  fun _ hP ↦ ⟨hP.1, hP.2.le⟩

/-- The zero matrix is an orthogonal projection of rank at most `n`. -/
lemma zero_mem_orthProjsLe (n : ℕ) : (0 : Matrix ι ι ℝ) ∈ orthProjsLe ι n :=
  ⟨IsStarProjection.zero _, by simp⟩

/-- The orthogonal projections of rank at most `n` form a closed set. -/
lemma isClosed_orthProjsLe (n : ℕ) : IsClosed (orthProjsLe ι n) := by
  have h1 : IsClosed {P : Matrix ι ι ℝ | Pᴴ = P} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have h2 : IsClosed {P : Matrix ι ι ℝ | P * P = P} :=
    isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_id
  have h3 : IsClosed {P : Matrix ι ι ℝ | P.trace ≤ n} :=
    isClosed_le continuous_id.matrix_trace continuous_const
  have : orthProjsLe ι n =
      ({P : Matrix ι ι ℝ | Pᴴ = P} ∩ {P | P * P = P}) ∩ {P | P.trace ≤ n} := by
    ext P
    exact ⟨fun h ↦ ⟨⟨h.1.conjTranspose_eq, h.1.mul_self⟩, h.2⟩,
      fun h ↦ ⟨.of_conjTranspose_eq h.1.1 h.1.2, h.2⟩⟩
  rw [this]
  exact (h1.inter h2).inter h3

/-- The orthogonal projections of rank at most `n` form a compact set. -/
lemma isCompact_orthProjsLe (n : ℕ) : IsCompact (orthProjsLe ι n) := by
  let K : Set (Matrix ι ι ℝ) :=
    Set.univ.pi fun _ : ι ↦ Set.univ.pi fun _ : ι ↦ Metric.closedBall (0 : ℝ) 1
  have hK : IsCompact K :=
    isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_closedBall _ _
  refine hK.of_isClosed_subset (isClosed_orthProjsLe n) fun P hP i _ j _ ↦ ?_
  exact Metric.mem_closedBall.2 (by simpa using hP.1.norm_apply_le_one i j)

/-! ### The Frobenius inner product -/

/-- `Tr(AP) ≤ ∑ᵢⱼ |Aᵢⱼ|` for an orthogonal projection `P`. -/
lemma frobeniusInner_le_sum_abs (A : Matrix ι ι ℝ) {P : Matrix ι ι ℝ} (hP : IsStarProjection P) :
    frobeniusInner A P ≤ ∑ i, ∑ j, |A i j| := by
  refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
  calc A i j * P i j ≤ |A i j * P i j| := le_abs_self _
    _ = |A i j| * |P i j| := abs_mul _ _
    _ ≤ |A i j| * 1 := by gcongr; exact hP.abs_apply_le_one i j
    _ = |A i j| := mul_one _

/-- `frobeniusInner` is additive in the first argument. -/
lemma frobeniusInner_add (A B P : Matrix ι ι ℝ) :
    frobeniusInner (A + B) P = frobeniusInner A P + frobeniusInner B P := by
  simp only [frobeniusInner, Matrix.add_apply, add_mul, sum_add_distrib]

/-- `frobeniusInner` commutes with subtraction in the first argument. -/
lemma frobeniusInner_sub (A B P : Matrix ι ι ℝ) :
    frobeniusInner (A - B) P = frobeniusInner A P - frobeniusInner B P := by
  simp only [frobeniusInner, ← sum_sub_distrib, Matrix.sub_apply]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

/-- `P ↦ frobeniusInner A P` is continuous. -/
lemma continuous_frobeniusInner (A : Matrix ι ι ℝ) : Continuous (frobeniusInner A) := by
  unfold frobeniusInner
  refine continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦ ?_
  exact continuous_const.mul (continuous_id.matrix_elem i j)

/-! ### Ky Fan sums -/

section KyFanSum

variable {n : ℕ}

/-- The values `Tr(AP)`, `P ∈ orthProjsLe ι n`, are bounded above. -/
lemma bddAbove_frobeniusInner_orthProjsLe (n : ℕ) (A : Matrix ι ι ℝ) :
    BddAbove (frobeniusInner A '' orthProjsLe ι n) :=
  ⟨∑ i, ∑ j, |A i j|, by rintro _ ⟨P, hP, rfl⟩; exact frobeniusInner_le_sum_abs A hP.1⟩

/-- The values `Tr(AP)`, `P ∈ orthProjs ℝ ι n`, are bounded above. -/
lemma bddAbove_frobeniusInner_orthProjs (n : ℕ) (A : Matrix ι ι ℝ) :
    BddAbove (frobeniusInner A '' orthProjs ℝ ι n) :=
  ⟨∑ i, ∑ j, |A i j|, by rintro _ ⟨P, hP, rfl⟩; exact frobeniusInner_le_sum_abs A hP.1⟩

/-- `Tr(AP) ≤ kyFanSumLe n A` for `P ∈ orthProjsLe ι n`. -/
lemma frobeniusInner_le_kyFanSumLe (A : Matrix ι ι ℝ) {P : Matrix ι ι ℝ}
    (hP : P ∈ orthProjsLe ι n) : frobeniusInner A P ≤ kyFanSumLe n A :=
  le_csSup (bddAbove_frobeniusInner_orthProjsLe n A) ⟨P, hP, rfl⟩

/-- Upper bounds for `kyFanSumLe n A` can be checked on the projections `P ∈ orthProjsLe ι n`. -/
lemma kyFanSumLe_le {A : Matrix ι ι ℝ} {c : ℝ}
    (h : ∀ P ∈ orthProjsLe ι n, frobeniusInner A P ≤ c) : kyFanSumLe n A ≤ c :=
  csSup_le ⟨_, 0, zero_mem_orthProjsLe n, rfl⟩ (by rintro _ ⟨P, hP, rfl⟩; exact h P hP)

/-- `0 ≤ kyFanSumLe n A`, as witnessed by the zero projection. -/
lemma kyFanSumLe_nonneg (n : ℕ) (A : Matrix ι ι ℝ) : 0 ≤ kyFanSumLe n A := by
  have := frobeniusInner_le_kyFanSumLe A (zero_mem_orthProjsLe (ι := ι) n)
  simpa [frobeniusInner] using this

/-- `Tr(AP) ≤ kyFanSum n A` for `P ∈ orthProjs ℝ ι n`. -/
lemma frobeniusInner_le_kyFanSum (A : Matrix ι ι ℝ) {P : Matrix ι ι ℝ}
    (hP : P ∈ orthProjs ℝ ι n) : frobeniusInner A P ≤ kyFanSum n A :=
  le_csSup (bddAbove_frobeniusInner_orthProjs n A) ⟨P, hP, rfl⟩

/-- Nonnegative upper bounds for `kyFanSum n A` can be checked on the projections
`P ∈ orthProjs ℝ ι n`. -/
lemma kyFanSum_le {A : Matrix ι ι ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ P ∈ orthProjs ℝ ι n, frobeniusInner A P ≤ c) : kyFanSum n A ≤ c :=
  Real.sSup_le (by rintro _ ⟨P, hP, rfl⟩; exact h P hP) hc

/-- `kyFanSumLe` is Lipschitz in the entries:
`kyFanSumLe n A ≤ kyFanSumLe n B + ∑ᵢⱼ |Aᵢⱼ - Bᵢⱼ|`. -/
lemma kyFanSumLe_le_add (n : ℕ) (A B : Matrix ι ι ℝ) :
    kyFanSumLe n A ≤ kyFanSumLe n B + ∑ i, ∑ j, |A i j - B i j| := by
  refine kyFanSumLe_le fun P hP ↦ ?_
  have h1 := frobeniusInner_le_kyFanSumLe B hP
  have h2 := frobeniusInner_le_sum_abs (A - B) hP.1
  have h3 := frobeniusInner_sub A B P
  simp only [Matrix.sub_apply] at h2
  linarith

/-- The supremum defining `kyFanSumLe` is attained. -/
theorem exists_frobeniusInner_eq_kyFanSumLe (n : ℕ) (A : Matrix ι ι ℝ) :
    ∃ P ∈ orthProjsLe ι n, frobeniusInner A P = kyFanSumLe n A := by
  obtain ⟨P, hP, hmax⟩ := (isCompact_orthProjsLe (ι := ι) n).exists_isMaxOn
    ⟨0, zero_mem_orthProjsLe n⟩ (continuous_frobeniusInner A).continuousOn
  exact ⟨P, hP, le_antisymm (frobeniusInner_le_kyFanSumLe A hP)
    (kyFanSumLe_le fun P' hP' ↦ hmax hP')⟩

end KyFanSum

/-! ### Relabelling the index set -/

section Submatrix

variable {κ : Type*} [Fintype κ]

/-- Relabelling the index set along an equivalence preserves `orthProjsLe`. -/
lemma submatrix_mem_orthProjsLe {n : ℕ} (e : κ ≃ ι) {P : Matrix ι ι ℝ}
    (hP : P ∈ orthProjsLe ι n) : P.submatrix e e ∈ orthProjsLe κ n :=
  ⟨hP.1.submatrix e, by rw [trace_submatrix_equiv]; exact hP.2⟩

/-- Relabelling the index set along an equivalence does not change `frobeniusInner`. -/
lemma frobeniusInner_submatrix (e : κ ≃ ι) (A P : Matrix ι ι ℝ) :
    frobeniusInner (A.submatrix e e) (P.submatrix e e) = frobeniusInner A P := by
  simp only [frobeniusInner, submatrix_apply]
  rw [Equiv.sum_comp e fun i ↦ ∑ j, A i (e j) * P i (e j)]
  exact sum_congr rfl fun i _ ↦ Equiv.sum_comp e fun j ↦ A i j * P i j

/-- Relabelling the index set along an equivalence does not change `kyFanSum`. -/
lemma kyFanSum_submatrix (n : ℕ) (e : κ ≃ ι) (A : Matrix ι ι ℝ) :
    kyFanSum n (A.submatrix e e) = kyFanSum n A := by
  unfold kyFanSum
  congr 1
  ext x
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    refine ⟨Q.submatrix e.symm e.symm, submatrix_mem_orthProjs e.symm hQ, ?_⟩
    rw [← frobeniusInner_submatrix e]
    simp
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P.submatrix e e, submatrix_mem_orthProjs e hP, frobeniusInner_submatrix e A P⟩

/-- Relabelling the index set along an equivalence does not change `kyFanSumLe`. -/
lemma kyFanSumLe_submatrix (n : ℕ) (e : κ ≃ ι) (A : Matrix ι ι ℝ) :
    kyFanSumLe n (A.submatrix e e) = kyFanSumLe n A := by
  unfold kyFanSumLe
  congr 1
  ext x
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    refine ⟨Q.submatrix e.symm e.symm, submatrix_mem_orthProjsLe e.symm hQ, ?_⟩
    rw [← frobeniusInner_submatrix e]
    simp
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P.submatrix e e, submatrix_mem_orthProjsLe e hP, frobeniusInner_submatrix e A P⟩

end Submatrix

/-! ### Orthonormal pairs -/

/-- `u, v ∈ ℝ^ι` are orthonormal. -/
structure IsOrthonormalPair (u v : ι → ℝ) : Prop where
  /-- `u` is a unit vector. -/
  left_self : u ⬝ᵥ u = 1
  /-- `v` is a unit vector. -/
  right_self : v ⬝ᵥ v = 1
  /-- `u` and `v` are orthogonal. -/
  left_right : u ⬝ᵥ v = 0

/-- If `u, v` are orthonormal, then so are `v, u`. -/
lemma IsOrthonormalPair.symm {u v : ι → ℝ} (h : IsOrthonormalPair u v) :
    IsOrthonormalPair v u :=
  ⟨h.right_self, h.left_self, by rw [dotProduct_comm]; exact h.left_right⟩

/-- **Bessel's inequality** for an orthonormal pair: `(uᵀx)² + (vᵀx)² ≤ xᵀx`. -/
lemma IsOrthonormalPair.sq_add_sq_le {u v : ι → ℝ} (h : IsOrthonormalPair u v) (x : ι → ℝ) :
    (u ⬝ᵥ x) ^ 2 + (v ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
  set a := u ⬝ᵥ x
  set b := v ⬝ᵥ x
  have h0 : 0 ≤ ∑ i, (x i - a * u i - b * v i) ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg _
  have expand : ∑ i, (x i - a * u i - b * v i) ^ 2 =
      x ⬝ᵥ x - 2 * a * (u ⬝ᵥ x) - 2 * b * (v ⬝ᵥ x) + a ^ 2 * (u ⬝ᵥ u) +
        2 * a * b * (u ⬝ᵥ v) + b ^ 2 * (v ⬝ᵥ v) := by
    simp only [dotProduct, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    ring
  rw [expand, h.left_self, h.right_self, h.left_right] at h0
  nlinarith [h0]

/-- `uᵀAu + vᵀAv`, the value of Ky Fan's functional at the pair `u, v`. -/
def fanValue (A : Matrix ι ι ℝ) (u v : ι → ℝ) : ℝ := u ⬝ᵥ A *ᵥ u + v ⬝ᵥ A *ᵥ v

/-- `fanValue A u v` is symmetric in `u` and `v`. -/
lemma fanValue_comm (A : Matrix ι ι ℝ) (u v : ι → ℝ) : fanValue A u v = fanValue A v u := by
  simp only [fanValue, add_comm]

/-- `uᵀAu + vᵀAv = ∑ᵢⱼ Aᵢⱼ (uᵢ uⱼ + vᵢ vⱼ)`. -/
lemma fanValue_eq_sum (A : Matrix ι ι ℝ) (u v : ι → ℝ) :
    fanValue A u v = ∑ i, ∑ j, A i j * (u i * u j + v i * v j) := by
  simp only [fanValue, dotProduct_mulVec_self_eq_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

/-- A crude bound: `uᵀAu + vᵀAv ≤ 2 ∑ |Aᵢⱼ|` for orthonormal `u, v`. -/
lemma fanValue_le_sum_abs (A : Matrix ι ι ℝ) {u v : ι → ℝ} (h : IsOrthonormalPair u v) :
    fanValue A u v ≤ 2 * ∑ i, ∑ j, |A i j| := by
  rw [fanValue_eq_sum, mul_sum]
  refine sum_le_sum fun i _ ↦ ?_
  rw [mul_sum]
  refine sum_le_sum fun j _ ↦ ?_
  have hu := abs_le_one_of_dotProduct_self h.left_self
  have hv := abs_le_one_of_dotProduct_self h.right_self
  have h1 : |u i * u j + v i * v j| ≤ 2 := by
    calc |u i * u j + v i * v j| ≤ |u i| * |u j| + |v i| * |v j| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * 1 + 1 * 1 := by
          gcongr
          · exact hu i
          · exact hu j
          · exact hv i
          · exact hv j
      _ = 2 := by norm_num
  calc A i j * (u i * u j + v i * v j) ≤ |A i j * (u i * u j + v i * v j)| := le_abs_self _
    _ = |A i j| * |u i * u j + v i * v j| := abs_mul _ _
    _ ≤ |A i j| * 2 := by gcongr
    _ = 2 * |A i j| := by ring

/-- The values `uᵀAu + vᵀAv` over the orthonormal pairs `u, v`. -/
def fanValues (A : Matrix ι ι ℝ) : Set ℝ :=
  {x | ∃ u v, IsOrthonormalPair u v ∧ fanValue A u v = x}

/-- The values `uᵀAu + vᵀAv` over the orthonormal pairs are bounded above. -/
lemma bddAbove_fanValues (A : Matrix ι ι ℝ) : BddAbove (fanValues A) :=
  ⟨2 * ∑ i, ∑ j, |A i j|, by rintro x ⟨u, v, h, rfl⟩; exact fanValue_le_sum_abs A h⟩

/-- `Tr(A Uᵀ U) = uᵀAu + vᵀAv` if `u, v` are the rows of `U ∈ ℝ^{2×ι}`. -/
lemma frobeniusInner_conjTranspose_mul_self (A : Matrix ι ι ℝ) (U : Matrix (Fin 2) ι ℝ) :
    frobeniusInner A (Uᴴ * U) = fanValue A (U 0) (U 1) := by
  rw [fanValue_eq_sum, frobeniusInner]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The orthogonal projections of rank two are the matrices `uuᵀ + vvᵀ` for orthonormal `u, v`,
so `{Tr(AP) : P ∈ orthProjs ℝ ι 2}` is the set of the values `uᵀAu + vᵀAv`. -/
theorem frobeniusInner_image_orthProjs_two (A : Matrix ι ι ℝ) :
    frobeniusInner A '' orthProjs ℝ ι 2 = fanValues A := by
  ext x
  constructor
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨U, hU, rfl⟩ := exists_parseval_of_mem_orthProjs hP
    have hUU : ∀ a b, U a ⬝ᵥ U b = if a = b then 1 else 0 := by
      intro a b
      have := congrFun (congrFun hU a) b
      simpa [Matrix.mul_apply, dotProduct, Matrix.one_apply] using this
    refine ⟨U 0, U 1, ⟨?_, ?_, ?_⟩, (frobeniusInner_conjTranspose_mul_self A U).symm⟩
    · simpa using hUU 0 0
    · simpa using hUU 1 1
    · simpa using hUU 0 1
  · rintro ⟨u, v, huv, rfl⟩
    let U : Matrix (Fin 2) ι ℝ := Matrix.of ![u, v]
    have hU : U * Uᴴ = 1 := by
      ext a b
      fin_cases a <;> fin_cases b
      · simpa [U, Matrix.mul_apply, dotProduct] using huv.left_self
      · simpa [U, Matrix.mul_apply, dotProduct] using huv.left_right
      · simpa [U, Matrix.mul_apply, dotProduct] using huv.symm.left_right
      · simpa [U, Matrix.mul_apply, dotProduct] using huv.right_self
    refine ⟨Uᴴ * U, conjTranspose_mul_self_mem_orthProjs hU, ?_⟩
    rw [frobeniusInner_conjTranspose_mul_self]
    rfl

/-- `kyFanSum 2 A = sup { uᵀAu + vᵀAv : u, v orthonormal }`. -/
theorem kyFanSum_two_eq_sSup (A : Matrix ι ι ℝ) : kyFanSum 2 A = sSup (fanValues A) := by
  rw [kyFanSum, frobeniusInner_image_orthProjs_two]

/-- `uᵀAu + vᵀAv ≤ kyFanSum 2 A` for every orthonormal pair `u, v`. -/
lemma fanValue_le_kyFanSum_two (A : Matrix ι ι ℝ) {u v : ι → ℝ} (h : IsOrthonormalPair u v) :
    fanValue A u v ≤ kyFanSum 2 A := by
  rw [kyFanSum_two_eq_sSup]
  exact le_csSup (bddAbove_fanValues A) ⟨u, v, h, rfl⟩

/-- If there are orthonormal pairs and `uᵀAu + vᵀAv ≤ c` for all of them, then
`kyFanSum 2 A ≤ c`. -/
lemma kyFanSum_two_le {A : Matrix ι ι ℝ} {c : ℝ} (hne : (fanValues A).Nonempty)
    (h : ∀ u v, IsOrthonormalPair u v → fanValue A u v ≤ c) : kyFanSum 2 A ≤ c := by
  rw [kyFanSum_two_eq_sSup]
  exact csSup_le hne (by rintro x ⟨u, v, huv, rfl⟩; exact h u v huv)

/-- If there is no orthonormal pair, then `kyFanSum 2 A = 0`. -/
lemma kyFanSum_two_of_not_nonempty {A : Matrix ι ι ℝ} (h : ¬ (fanValues A).Nonempty) :
    kyFanSum 2 A = 0 := by
  rw [Set.not_nonempty_iff_eq_empty] at h
  rw [kyFanSum_two_eq_sSup, h, Real.sSup_empty]

/-- `kyFanSum 2 A ≤ c` as soon as `uᵀAu + vᵀAv ≤ c` for all orthonormal pairs and `0 ≤ c`. -/
lemma kyFanSum_two_le' {A : Matrix ι ι ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ u v, IsOrthonormalPair u v → fanValue A u v ≤ c) : kyFanSum 2 A ≤ c := by
  by_cases hne : (fanValues A).Nonempty
  · exact kyFanSum_two_le hne h
  · rw [kyFanSum_two_of_not_nonempty hne]; exact hc

end ProjectionConstants
