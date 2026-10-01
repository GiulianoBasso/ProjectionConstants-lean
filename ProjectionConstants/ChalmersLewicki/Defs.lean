/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Matrix.OrthProj
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.MeanInequalities

/-!
# The Chalmers–Lewicki quantity and quasimaximal projection constants

Let `ι` be a finite index set (think `ι = {1, …, N}`). For a weight vector `t ∈ ℝ^ι` with `t ≥ 0`
and `‖t‖₂ = 1` and an orthogonal projection matrix `P ∈ orthProjs 𝕜 ι m` of rank `m` we consider
`weightedAbsSum t P = ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|`. Writing `P = Uᴴ U` with `U Uᴴ = I_m`, this is the
expression `∑ᵢⱼ tᵢ tⱼ |(Uᴴ U)ᵢⱼ|` in the formula of Chalmers and Lewicki [DL, Theorem 1.1]. Its
supremum `clConst 𝕜 ι m` is the right-hand side of this formula; by
`ProjectionConstants.ChalmersLewicki.Formula`, it equals `λ_𝕜(m, N) = maxRelProjConst 𝕜 m N`.
The special case of equal weights `tᵢ = 1/√N` gives the quasimaximal projection constants of [DL].

The paper phrases these notions with matrices `U ∈ 𝕜^{m×N}` satisfying `U Uᴴ = I_m`; the
equivalence with our formulation (via `P = Uᴴ U`) is `quasiRelConst_eq_sSup_parseval` and
`clConst_eq_sSup_parseval`. We also prove the elementary bound `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ √m`
(Cauchy–Schwarz), which yields the bound `λ(Y) ≤ √m` of Kadec and Snobar in
`ProjectionConstants.ChalmersLewicki.Absolute`.

## Main definitions

* `absSum P`: the sum `∑ᵢⱼ |Pᵢⱼ|` of the moduli of the entries of `P`.
* `weightedAbsSum t P`: the weighted sum `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|`.
* `IsUnitWeight t`: `t ≥ 0` and `∑ᵢ tᵢ² = 1`.
* `clConst 𝕜 ι m`: the **Chalmers–Lewicki quantity**, the supremum of `weightedAbsSum t P` over
  all unit weights `t` and all `P ∈ orthProjs 𝕜 ι m`.
* `quasiRelConst 𝕜 ι m`: the **quasimaximal relative projection constant**
  `μ_𝕜(m, N) = sup { (1/N) ∑ᵢⱼ |Pᵢⱼ| : P ∈ orthProjs 𝕜 ι m }` of [DL, (2)], where `N = card ι`.
* `quasiMaxConst 𝕜 m`: the **quasimaximal absolute projection constant**
  `μ_𝕜(m) = sup_N μ_𝕜(m, N)` of [DL, (3)].

## Main statements

* `weightedAbsSum_le_sqrt`: `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ √m`; hence `clConst_le_sqrt`,
  `quasiRelConst_le_sqrt` and `quasiMaxConst_le_sqrt`.
* `quasiRelConst_le_clConst`: `μ_𝕜(m, N) ≤ clConst 𝕜 ι m` (equal weights).
* `quasiRelConst_congr`: `μ_𝕜(m, N)` only depends on the cardinality `N` of the index set.
* `quasiRelConst_eq_sSup_parseval`, `clConst_eq_sSup_parseval`: the formulations of [DL] with
  matrices `U ∈ 𝕜^{m×N}` satisfying `U Uᴴ = I_m`.

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
-/

open Matrix Finset

namespace ProjectionConstants

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- The sum `∑ᵢⱼ |Pᵢⱼ|` of the moduli of the entries of a matrix. -/
noncomputable def absSum (P : Matrix ι ι 𝕜) : ℝ := ∑ i, ∑ j, ‖P i j‖

/-- The weighted sum `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|` of the moduli of the entries of a matrix. -/
noncomputable def weightedAbsSum (t : ι → ℝ) (P : Matrix ι ι 𝕜) : ℝ :=
  ∑ i, ∑ j, t i * t j * ‖P i j‖

/-- A nonnegative weight vector of Euclidean norm one. -/
structure IsUnitWeight (t : ι → ℝ) : Prop where
  /-- The weights are nonnegative. -/
  nonneg : ∀ i, 0 ≤ t i
  /-- The weight vector has Euclidean norm one. -/
  sum_sq : ∑ i, t i ^ 2 = 1

variable (𝕜 ι) in
/-- The **Chalmers–Lewicki quantity**
`sup { ∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| : t ≥ 0, ‖t‖₂ = 1, P ∈ orthProjs 𝕜 ι m }`, the right-hand side of the
formula of Chalmers and Lewicki [DL, Theorem 1.1]. -/
noncomputable def clConst (m : ℕ) : ℝ :=
  sSup {x | ∃ t P, IsUnitWeight t ∧ P ∈ orthProjs 𝕜 ι m ∧ x = weightedAbsSum t P}

variable (𝕜 ι) in
/-- The **quasimaximal relative projection constant**
`μ_𝕜(m, N) = sup { (1/N) ∑ᵢⱼ |Pᵢⱼ| : P ∈ orthProjs 𝕜 ι m }` of [DL, (2)], where `N = card ι`. -/
noncomputable def quasiRelConst (m : ℕ) : ℝ :=
  sSup {x | ∃ P ∈ orthProjs 𝕜 ι m, x = absSum P / Fintype.card ι}

variable (𝕜) in
/-- The **quasimaximal absolute projection constant** `μ_𝕜(m) = sup_N μ_𝕜(m, N)` of [DL, (3)]. -/
noncomputable def quasiMaxConst (m : ℕ) : ℝ := ⨆ N : ℕ, quasiRelConst 𝕜 (Fin N) m

/-! ### Elementary estimates -/

lemma absSum_nonneg (P : Matrix ι ι 𝕜) : 0 ≤ absSum P :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ norm_nonneg _

lemma weightedAbsSum_nonneg {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) (P : Matrix ι ι 𝕜) :
    0 ≤ weightedAbsSum t P :=
  sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ by have := ht i; have := ht j; positivity

/-- `∑ᵢⱼ |Pᵢⱼ|² = m`: the Frobenius norm of an orthogonal projection of rank `m` is `√m`. -/
lemma sum_norm_sq_of_mem_orthProjs {m : ℕ} {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    ∑ i, ∑ j, ‖P i j‖ ^ 2 = m := by
  rw [← sum_re_diag hP]
  exact sum_congr rfl fun i _ ↦ (hP.1.re_diag_eq_sum_row i).symm

/-- `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| ≤ √m` by the Cauchy–Schwarz inequality. -/
theorem weightedAbsSum_le_sqrt {m : ℕ} {t : ι → ℝ} (ht : IsUnitWeight t) {P : Matrix ι ι 𝕜}
    (hP : P ∈ orthProjs 𝕜 ι m) : weightedAbsSum t P ≤ √m := by
  have hcs : (∑ ij : ι × ι, (t ij.1 * t ij.2) * ‖P ij.1 ij.2‖) ^ 2 ≤
      (∑ ij : ι × ι, (t ij.1 * t ij.2) ^ 2) * ∑ ij : ι × ι, ‖P ij.1 ij.2‖ ^ 2 :=
    sum_mul_sq_le_sq_mul_sq _ _ _
  have h1 : ∑ ij : ι × ι, (t ij.1 * t ij.2) ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [mul_pow, ← mul_sum, ← sum_mul, ht.sum_sq, one_mul]
  have h2 : ∑ ij : ι × ι, ‖P ij.1 ij.2‖ ^ 2 = m := by
    rw [Fintype.sum_prod_type]
    exact sum_norm_sq_of_mem_orthProjs hP
  have h3 : weightedAbsSum t P = ∑ ij : ι × ι, (t ij.1 * t ij.2) * ‖P ij.1 ij.2‖ := by
    rw [Fintype.sum_prod_type]; rfl
  rw [h1, h2, one_mul] at hcs
  rw [h3]
  exact Real.le_sqrt_of_sq_le hcs

/-- The uniform weight `tᵢ = 1/√N` is a unit weight. -/
lemma isUnitWeight_uniform [Nonempty ι] :
    IsUnitWeight (fun _ : ι ↦ 1 / √(Fintype.card ι : ℝ)) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨fun _ ↦ by positivity, ?_⟩
  simp only [div_pow, one_pow, Real.sq_sqrt hN.le, sum_const, card_univ, nsmul_eq_mul]
  field_simp

lemma weightedAbsSum_uniform [Nonempty ι] (P : Matrix ι ι 𝕜) :
    weightedAbsSum (fun _ : ι ↦ 1 / √(Fintype.card ι : ℝ)) P = absSum P / Fintype.card ι := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h : 1 / √(Fintype.card ι : ℝ) * (1 / √(Fintype.card ι : ℝ)) = 1 / Fintype.card ι := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hN.le]
  unfold weightedAbsSum absSum
  simp only [Finset.sum_div]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [h]
  ring

/-- `(1/N) ∑ᵢⱼ |Pᵢⱼ| ≤ √m`. -/
theorem absSum_div_card_le_sqrt {m : ℕ} {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    absSum P / Fintype.card ι ≤ √m := by
  cases isEmpty_or_nonempty ι
  · simp
  · rw [← weightedAbsSum_uniform]
    exact weightedAbsSum_le_sqrt isUnitWeight_uniform hP

/-! ### Basic properties of the constants -/

section Constants

variable {m : ℕ}

lemma bddAbove_clConst_set :
    BddAbove {x | ∃ t P, IsUnitWeight t ∧ P ∈ orthProjs 𝕜 ι m ∧ x = weightedAbsSum t P} :=
  ⟨√m, by rintro _ ⟨t, P, ht, hP, rfl⟩; exact weightedAbsSum_le_sqrt ht hP⟩

lemma bddAbove_quasiRelConst_set :
    BddAbove {x | ∃ P ∈ orthProjs 𝕜 ι m, x = absSum P / Fintype.card ι} :=
  ⟨√m, by rintro _ ⟨P, hP, rfl⟩; exact absSum_div_card_le_sqrt hP⟩

lemma le_clConst {t : ι → ℝ} (ht : IsUnitWeight t) {P : Matrix ι ι 𝕜}
    (hP : P ∈ orthProjs 𝕜 ι m) : weightedAbsSum t P ≤ clConst 𝕜 ι m :=
  le_csSup bddAbove_clConst_set ⟨t, P, ht, hP, rfl⟩

lemma clConst_le_sqrt : clConst 𝕜 ι m ≤ √m :=
  Real.sSup_le (by rintro _ ⟨t, P, ht, hP, rfl⟩; exact weightedAbsSum_le_sqrt ht hP)
    (Real.sqrt_nonneg _)

lemma clConst_nonneg : 0 ≤ clConst 𝕜 ι m :=
  Real.sSup_nonneg (by rintro _ ⟨t, P, ht, hP, rfl⟩; exact weightedAbsSum_nonneg ht.nonneg P)

lemma clConst_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t P, IsUnitWeight t → P ∈ orthProjs 𝕜 ι m → weightedAbsSum t P ≤ c) :
    clConst 𝕜 ι m ≤ c :=
  Real.sSup_le (by rintro _ ⟨t, P, ht, hP, rfl⟩; exact h t P ht hP) hc

lemma le_quasiRelConst {P : Matrix ι ι 𝕜} (hP : P ∈ orthProjs 𝕜 ι m) :
    absSum P / Fintype.card ι ≤ quasiRelConst 𝕜 ι m :=
  le_csSup bddAbove_quasiRelConst_set ⟨P, hP, rfl⟩

lemma quasiRelConst_le_sqrt : quasiRelConst 𝕜 ι m ≤ √m :=
  Real.sSup_le (by rintro _ ⟨P, hP, rfl⟩; exact absSum_div_card_le_sqrt hP) (Real.sqrt_nonneg _)

lemma quasiRelConst_nonneg : 0 ≤ quasiRelConst 𝕜 ι m :=
  Real.sSup_nonneg (by rintro _ ⟨P, -, rfl⟩; exact div_nonneg (absSum_nonneg P) (by positivity))

lemma quasiRelConst_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ P ∈ orthProjs 𝕜 ι m, absSum P / Fintype.card ι ≤ c) : quasiRelConst 𝕜 ι m ≤ c :=
  Real.sSup_le (by rintro _ ⟨P, hP, rfl⟩; exact h P hP) hc

/-- `μ_𝕜(m, N) ≤ clConst 𝕜 ι m`: equal weights are a special case. -/
lemma quasiRelConst_le_clConst : quasiRelConst 𝕜 ι m ≤ clConst 𝕜 ι m := by
  refine quasiRelConst_le clConst_nonneg fun P hP ↦ ?_
  cases isEmpty_or_nonempty ι
  · simp [absSum, clConst_nonneg]
  · rw [← weightedAbsSum_uniform]
    exact le_clConst isUnitWeight_uniform hP

lemma bddAbove_range_quasiRelConst : BddAbove (Set.range fun N : ℕ ↦ quasiRelConst 𝕜 (Fin N) m) :=
  ⟨√m, by rintro _ ⟨N, rfl⟩; exact quasiRelConst_le_sqrt⟩

lemma quasiRelConst_le_quasiMaxConst (N : ℕ) : quasiRelConst 𝕜 (Fin N) m ≤ quasiMaxConst 𝕜 m :=
  le_ciSup bddAbove_range_quasiRelConst N

lemma quasiMaxConst_le_sqrt : quasiMaxConst 𝕜 m ≤ √m :=
  Real.iSup_le (fun _ ↦ quasiRelConst_le_sqrt) (Real.sqrt_nonneg _)

lemma quasiMaxConst_nonneg : 0 ≤ quasiMaxConst 𝕜 m :=
  Real.iSup_nonneg fun _ ↦ quasiRelConst_nonneg

lemma quasiMaxConst_le {c : ℝ} (hc : 0 ≤ c) (h : ∀ N, quasiRelConst 𝕜 (Fin N) m ≤ c) :
    quasiMaxConst 𝕜 m ≤ c :=
  Real.iSup_le h hc

end Constants

/-! ### Relabelling the index set -/

section Reindex

variable {κ : Type*} [Fintype κ]

lemma absSum_submatrix (e : κ ≃ ι) (P : Matrix ι ι 𝕜) : absSum (P.submatrix e e) = absSum P := by
  simp only [absSum, Matrix.submatrix_apply]
  rw [Equiv.sum_comp e (fun i ↦ ∑ j, ‖P i (e j)‖)]
  exact sum_congr rfl fun i _ ↦ Equiv.sum_comp e (fun j ↦ ‖P i j‖)

lemma quasiRelConst_le_of_equiv {m : ℕ} (e : κ ≃ ι) :
    quasiRelConst 𝕜 ι m ≤ quasiRelConst 𝕜 κ m := by
  refine quasiRelConst_le quasiRelConst_nonneg fun P hP ↦ ?_
  have h := le_quasiRelConst (submatrix_mem_orthProjs e hP)
  rwa [absSum_submatrix, Fintype.card_congr e] at h

lemma quasiRelConst_congr {m : ℕ} (e : κ ≃ ι) : quasiRelConst 𝕜 κ m = quasiRelConst 𝕜 ι m :=
  le_antisymm (quasiRelConst_le_of_equiv e.symm) (quasiRelConst_le_of_equiv e)

/-- `μ_𝕜(m, N) ≤ μ_𝕜(m)`, for an arbitrary finite index type `ι` with `N` elements. -/
lemma quasiRelConst_le_quasiMaxConst' {m : ℕ} : quasiRelConst 𝕜 ι m ≤ quasiMaxConst 𝕜 m := by
  rw [← quasiRelConst_congr (Fintype.equivFin ι).symm]
  exact quasiRelConst_le_quasiMaxConst _

end Reindex

/-! ### The formulation of the paper, with `U Uᴴ = I` -/

section Paper

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- The definition [DL, (2)] of the quasimaximal relative projection constant:
`μ_𝕜(m, N) = sup { (1/N) ∑ᵢⱼ |(Uᴴ U)ᵢⱼ| : U ∈ 𝕜^{m×N}, U Uᴴ = I_m }`. -/
theorem quasiRelConst_eq_sSup_parseval (m : ℕ) :
    quasiRelConst 𝕜 ι m = sSup {x | ∃ U : Matrix (Fin m) ι 𝕜, U * Uᴴ = 1 ∧
      x = (1 / Fintype.card ι) * ∑ i, ∑ j, ‖(Uᴴ * U) i j‖} := by
  unfold quasiRelConst
  congr 1
  ext x
  constructor
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨U, hU, rfl⟩ := exists_parseval_of_mem_orthProjs hP
    exact ⟨U, hU, by rw [absSum, one_div_mul_eq_div]⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨_, conjTranspose_mul_self_mem_orthProjs hU, by rw [absSum, one_div_mul_eq_div]⟩

omit [DecidableEq ι] in
/-- The right-hand side of the formula of Chalmers and Lewicki in the formulation of
[DL, Theorem 1.1]: `clConst 𝕜 ι m` is the supremum of `∑ᵢⱼ tᵢ tⱼ |(Uᴴ U)ᵢⱼ|` over `t ≥ 0` with
`∑ᵢ tᵢ² = 1` and `U ∈ 𝕜^{m×N}` with `U Uᴴ = I_m`. -/
theorem clConst_eq_sSup_parseval (m : ℕ) :
    clConst 𝕜 ι m = sSup {x | ∃ (t : ι → ℝ) (U : Matrix (Fin m) ι 𝕜), (∀ i, 0 ≤ t i) ∧
      ∑ i, t i ^ 2 = 1 ∧ U * Uᴴ = 1 ∧ x = ∑ i, ∑ j, t i * t j * ‖(Uᴴ * U) i j‖} := by
  unfold clConst
  congr 1
  ext x
  constructor
  · rintro ⟨t, P, ht, hP, rfl⟩
    obtain ⟨U, hU, rfl⟩ := exists_parseval_of_mem_orthProjs hP
    exact ⟨t, U, ht.nonneg, ht.sum_sq, hU, rfl⟩
  · rintro ⟨t, U, ht0, ht1, hU, rfl⟩
    exact ⟨t, _, ⟨ht0, ht1⟩, conjTranspose_mul_self_mem_orthProjs hU, rfl⟩

end Paper

end ProjectionConstants
