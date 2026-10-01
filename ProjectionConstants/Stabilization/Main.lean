/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Stabilization.Caratheodory
import ProjectionConstants.Stabilization.Reweight
import ProjectionConstants.ChalmersLewicki.Absolute
import Mathlib.Data.Sym.Card

/-!
# Stabilization of the maximal relative projection constants

We prove the theorem of Kumar, Mohar, Mojallal and Pragada [KMMP, Theorem 1.3], which answers a
question of Basso: for `N_r = 2^r C(r+1, 2)` (`stabilizationBound r`) and every `n ≥ N_r`, the
maximal relative projection constant `λ_ℝ(r, n)` (`maxRelProjConst ℝ r n`) is equal to the
maximal projection constant `λ_ℝ(r)` (`maxProjConst ℝ r`) (`maxRelProjConst_eq_maxProjConst`).

By the formula of Chalmers and Lewicki (`maxRelProjConst_eq_clConst`), `λ_ℝ(r, n)` is the
Chalmers–Lewicki quantity `clConst ℝ (Fin n) r`, the supremum of `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ|` over the
unit weights `t ∈ ℝⁿ` and the orthogonal projections `P` of rank `r`. The auxiliary results are
in the namespace `ProjectionConstants.Stabilization`, the main theorems in `ProjectionConstants`.

## Proof

Take a maximizer `(t, U)` of the Chalmers–Lewicki quantity for `λ(r, n)` (`IsMaximizer`), with
columns `uᵢ ∈ ℝ^r`, and sort the indices by the sign pattern of `uᵢ` (`columnSigns`): within one
of the `2^r` classes, all inner products `⟨uᵢ, uⱼ⟩` are nonnegative
(`inner_nonneg_of_columnSigns_eq`).

* In a class `C`, the matrix `∑_{i ∈ C} uᵢ uᵢᵀ` lies in the cone spanned by the `uᵢ uᵢᵀ`, in the
  space of symmetric matrices of dimension `C(r+1, 2)` (here `Sym2 (Fin r) → ℝ`, `symSq`). By
  Carathéodory's theorem for cones (`exists_sparse_conic_combination`) it equals
  `∑_{i ∈ C} cᵢ uᵢ uᵢᵀ` with `cᵢ ≥ 0` and at most `C(r+1, 2)` of the `cᵢ` nonzero
  (`exists_reweighting`).
* Reweighting by `√cᵢ` keeps a maximizer (`IsMaximizer.reweight`). Doing this class after class
  gives a maximizer supported on at most `2^r C(r+1, 2)` indices (`IsMaximizer.exists_sparse`).
* Moving the support into `Fin N_r` (`weightedAbsSum_le_clConst_of_support`) gives
  `λ(r, n) ≤ λ(r, N_r)` for every `n` (`clConst_le_clConst_stabilizationBound`), so
  `λ(r) = sup_n λ(r, n) = λ(r, N_r)` (`maxProjConst_eq_maxRelProjConst_stabilizationBound`);
  monotonicity in `n` (`clConst_le_of_card_le`) gives the theorem.

## Main definitions

* `stabilizationBound r`: the bound `N_r = 2^r C(r+1, 2)`.
* `symSq u`: the entries `uₖ uₗ` of `u uᵀ`, indexed by the unordered pairs `{k, l}`.
* `columnSigns U i`: the sign pattern of the column `uᵢ` of `U`.

## Main statements

* `exists_reweighting`: Carathéodory for `∑_{i ∈ C} uᵢ uᵢᵀ` ([KMMP, Claim 2.5]).
* `IsMaximizer.exists_sparse`: a maximizer with at most `2^r C(r+1, 2)` nonzero weights.
* `weightedAbsSum_le_clConst_of_support`, `clConst_le_of_card_le`: padding with zeros, and the
  monotonicity of `λ(r, n)` in `n`.
* `maxProjConst_eq_maxRelProjConst_stabilizationBound`: `λ_ℝ(r) = λ_ℝ(r, N_r)`.
* `maxRelProjConst_eq_maxProjConst`: `λ_ℝ(r, n) = λ_ℝ(r)` for `n ≥ N_r` ([KMMP, Theorem 1.3]).
* `exists_weightedAbsSum_eq_maxProjConst`: the supremum defining `λ_ℝ(r)` is attained on
  `ℝ^{N_r}`.

## References

* [KMMP] H. Kumar, B. Mohar, S. A. Mojallal, S. Pragada, *Stability of maximal relative
  projection constants*, arXiv:2609.03200.
-/

open Matrix Finset

namespace ProjectionConstants.Stabilization

/-! ### Carathéodory in the space of symmetric matrices -/

section Sym

variable {r : ℕ}

/-- The entries `(uₖ uₗ)` of `u uᵀ`, indexed by unordered pairs `{k, l}`. -/
def symSq (u : Fin r → ℝ) : Sym2 (Fin r) → ℝ :=
  Sym2.lift ⟨fun k l ↦ u k * u l, fun _ _ ↦ mul_comm _ _⟩

@[simp] lemma symSq_mk (u : Fin r → ℝ) (k l : Fin r) : symSq u s(k, l) = u k * u l := rfl

/-- The space `Sym2 (Fin r) → ℝ` of symmetric `r × r` matrices has dimension `C(r+1, 2)`. -/
lemma finrank_sym2 : Module.finrank ℝ (Sym2 (Fin r) → ℝ) = (r + 1).choose 2 := by
  rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin]

variable {ι : Type*} [Fintype ι]

/-- **Carathéodory for `∑_{i ∈ C} uᵢ uᵢᵀ`** ([KMMP, Claim 2.5]): there are `cᵢ ≥ 0`, equal to `1`
off `C`, with `∑ᵢ cᵢ uᵢ uᵢᵀ = ∑ᵢ uᵢ uᵢᵀ` and at most `C(r+1, 2)` nonzero `cᵢ` in `C`. -/
theorem exists_reweighting (U : Matrix (Fin r) ι ℝ) (C : Finset ι) :
    ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ (∀ i ∉ C, c i = 1) ∧
      (∀ k l, ∑ i, c i * (U k i * U l i) = ∑ i, U k i * U l i) ∧
      (C.filter (c · ≠ 0)).card ≤ (r + 1).choose 2 := by
  classical
  obtain ⟨b, hb, hsum, hcard⟩ := exists_sparse_conic_combination C
    (fun i ↦ symSq fun k ↦ U k i) (fun _ ↦ 1) (fun _ _ ↦ zero_le_one)
  refine ⟨fun i ↦ if i ∈ C then b i else 1, fun i ↦ ?_, fun i hi ↦ by simp [hi],
    fun k l ↦ ?_, ?_⟩
  · dsimp only
    split_ifs with hi
    exacts [hb i hi, zero_le_one]
  · have e := congrFun hsum s(k, l)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, symSq_mk, one_mul] at e
    simp only [ite_mul, one_mul]
    rw [sum_ite, ← sum_filter_add_sum_filter_not univ (· ∈ C) (fun i ↦ U k i * U l i),
      filter_mem_eq_inter, univ_inter, e]
  · rw [finrank_sym2] at hcard
    refine le_trans (card_le_card fun i hi ↦ ?_) hcard
    obtain ⟨hiC, hne⟩ := mem_filter.1 hi
    exact mem_filter.2 ⟨hiC, by simpa [hiC] using hne⟩

end Sym

/-! ### Sign patterns -/

section Signs

variable {ι : Type*} {r : ℕ}

/-- The sign pattern of the column `uᵢ` of `U`: which coordinates are `≥ 0`. -/
noncomputable def columnSigns (U : Matrix (Fin r) ι ℝ) (i : ι) : Fin r → Bool :=
  fun k ↦ decide (0 ≤ U k i)

/-- Columns with the same sign pattern have a nonnegative inner product. -/
lemma inner_nonneg_of_columnSigns_eq (U : Matrix (Fin r) ι ℝ) {i j : ι}
    (hij : columnSigns U i = columnSigns U j) : 0 ≤ ∑ k, U k i * U k j := by
  refine sum_nonneg fun k _ ↦ ?_
  have e := congrFun hij k
  simp only [columnSigns, decide_eq_decide] at e
  by_cases hk : 0 ≤ U k i
  · exact mul_nonneg hk (e.mp hk)
  · have hk' : U k i < 0 := not_le.mp hk
    have hj : U k j < 0 := not_le.mp fun h' ↦ hk (e.mpr h')
    exact (mul_pos_of_neg_of_neg hk' hj).le

end Signs

/-! ### Sparse maximizers -/

section Sparse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} {t : ι → ℝ} {U : Matrix (Fin r) ι ℝ}

/-- **A maximizer with small support.** From a maximizer `(t, U)` one obtains, by rescaling the
indices with factors `aᵢ ≥ 0`, a maximizer with at most `2^r C(r+1, 2)` nonzero factors. -/
theorem IsMaximizer.exists_sparse (h : IsMaximizer r t U) (hL0 : 0 < clConst ℝ ι r) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ IsMaximizer r (fun i ↦ a i * t i) (U * diagonal a) ∧
      (univ.filter (a · ≠ 0)).card ≤ 2 ^ r * (r + 1).choose 2 := by
  set part := columnSigns U with hpart
  set K := (r + 1).choose 2 with hK
  -- process the sign classes one by one
  have key : ∀ S : Finset (Fin r → Bool), ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧
      IsMaximizer r (fun i ↦ a i * t i) (U * diagonal a) ∧
      ∀ σ ∈ S, (univ.filter fun i ↦ part i = σ ∧ a i ≠ 0).card ≤ K := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨fun _ ↦ 1, fun _ ↦ zero_le_one, ?_, by simp⟩
      simpa [Matrix.diagonal_one] using h
    | insert σ S hσ ih =>
      obtain ⟨a, ha0, ha, hcard⟩ := ih
      set C := univ.filter fun i ↦ part i = σ with hCdef
      have hC : ∀ i ∈ C, ∀ j ∈ C,
          0 ≤ ((U * diagonal a)ᴴ * (U * diagonal a)) i j := by
        intro i hi j hj
        rw [IsMaximizer.gram_mul_diagonal, IsMaximizer.gram_apply]
        exact mul_nonneg (mul_nonneg (ha0 i) (ha0 j)) (inner_nonneg_of_columnSigns_eq U
          ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm))
      obtain ⟨c, hc0, hc1, hcU, hccard⟩ := exists_reweighting (U * diagonal a) C
      have hnew := ha.reweight hL0 C hC hc0 hc1 hcU
      refine ⟨fun i ↦ √(c i) * a i, fun i ↦ mul_nonneg (Real.sqrt_nonneg _) (ha0 i), ?_,
        fun σ' hσ' ↦ ?_⟩
      · have e1 : (fun i ↦ √(c i) * (a i * t i)) = fun i ↦ √(c i) * a i * t i :=
          funext fun i ↦ by ring
        have e2 : U * diagonal a * diagonal (fun i ↦ √(c i)) =
            U * diagonal fun i ↦ √(c i) * a i := by
          rw [Matrix.mul_assoc, diagonal_mul_diagonal]
          congr 2
          exact funext fun i ↦ mul_comm _ _
        rw [e1, e2] at hnew
        exact hnew
      · rcases mem_insert.1 hσ' with rfl | hσ'
        · -- the new class
          refine le_trans (card_le_card fun i hi ↦ ?_) hccard
          obtain ⟨hpi, hne⟩ := (mem_filter.1 hi).2
          have hiC : i ∈ C := mem_filter.2 ⟨mem_univ i, hpi⟩
          refine mem_filter.2 ⟨hiC, fun hci ↦ hne ?_⟩
          simp only [hci, Real.sqrt_zero, zero_mul]
        · -- an old class: nothing changed there
          have hne : σ' ≠ σ := fun h' ↦ hσ (h' ▸ hσ')
          refine le_of_eq_of_le ?_ (hcard σ' hσ')
          congr 1
          ext i
          simp only [mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨hpi, hi⟩
            have hiC : i ∉ C := fun hiC ↦ hne (hpi ▸ (mem_filter.1 hiC).2)
            refine ⟨hpi, ?_⟩
            rwa [hc1 i hiC, Real.sqrt_one, one_mul] at hi
          · rintro ⟨hpi, hi⟩
            have hiC : i ∉ C := fun hiC ↦ hne (hpi ▸ (mem_filter.1 hiC).2)
            refine ⟨hpi, ?_⟩
            rwa [hc1 i hiC, Real.sqrt_one, one_mul]
  obtain ⟨a, ha0, ha, hcard⟩ := key univ
  refine ⟨a, ha0, ha, ?_⟩
  calc (univ.filter (a · ≠ 0)).card
      = ∑ σ : Fin r → Bool, ((univ.filter (a · ≠ 0)).filter fun i ↦ part i = σ).card :=
        card_eq_sum_card_fiberwise fun i _ ↦ mem_univ (part i)
    _ ≤ ∑ _σ : Fin r → Bool, K := by
        refine sum_le_sum fun σ _ ↦ le_of_eq_of_le ?_ (hcard σ (mem_univ σ))
        congr 1
        ext i
        simp [and_comm]
    _ = 2 ^ r * K := by simp

end Sparse

/-! ### Moving a configuration to another index set -/

section Padding

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {r : ℕ}

/-- **Padding with zeros.** A configuration `(t, U)` supported on `J` gives the same value on any
index set into which `J` embeds. -/
theorem weightedAbsSum_le_clConst_of_support {t : ι → ℝ} (ht : IsUnitWeight t)
    {U : Matrix (Fin r) ι ℝ} (hU : U * Uᴴ = 1) (J : Finset ι) (htJ : ∀ i ∉ J, t i = 0)
    (hUJ : ∀ k, ∀ i ∉ J, U k i = 0) (φ : J → ι') (hφ : Function.Injective φ) :
    weightedAbsSum t (Uᴴ * U) ≤ clConst ℝ ι' r := by
  classical
  -- transferring sums
  have transfer : ∀ (g : ι → ℝ) (g' : ι' → ℝ), (∀ i ∉ J, g i = 0) →
      (∀ m ∉ Set.range φ, g' m = 0) → (∀ j : J, g j = g' (φ j)) → ∑ i, g i = ∑ m, g' m := by
    intro g g' hg hg' hgg'
    rw [← Fintype.sum_of_injective (Subtype.val : J → ι) Subtype.val_injective (fun j ↦ g j) g
      (fun i hi ↦ hg i fun hiJ ↦ hi ⟨⟨i, hiJ⟩, rfl⟩) fun _ ↦ rfl]
    exact Fintype.sum_of_injective φ hφ (fun j ↦ g j) g' hg' hgg'
  set t' : ι' → ℝ := Function.extend φ (fun j ↦ t j) 0 with ht'def
  set U' : Matrix (Fin r) ι' ℝ := Matrix.of fun k ↦ Function.extend φ (fun j ↦ U k j) 0
    with hU'def
  have ht'φ : ∀ j, t' (φ j) = t j := fun j ↦ hφ.extend_apply _ _ j
  have ht'0 : ∀ m ∉ Set.range φ, t' m = 0 := fun m hm ↦ by
    rw [ht'def, Function.extend_apply' _ _ _ (by simpa using hm), Pi.zero_apply]
  have hU'φ : ∀ k j, U' k (φ j) = U k j := fun k j ↦ by
    simp only [hU'def, Matrix.of_apply]
    exact hφ.extend_apply _ _ j
  have hU'0 : ∀ k, ∀ m ∉ Set.range φ, U' k m = 0 := fun k m hm ↦ by
    simp only [hU'def, Matrix.of_apply]
    rw [Function.extend_apply' _ _ _ (by simpa using hm), Pi.zero_apply]
  have hgram : ∀ j₁ j₂ : J, (U'ᴴ * U') (φ j₁) (φ j₂) = (Uᴴ * U) j₁ j₂ := by
    intro j₁ j₂
    rw [IsMaximizer.gram_apply, IsMaximizer.gram_apply]
    exact sum_congr rfl fun k _ ↦ by rw [hU'φ, hU'φ]
  have ht' : IsUnitWeight t' := by
    refine ⟨fun m ↦ ?_, ?_⟩
    · by_cases hm : m ∈ Set.range φ
      · obtain ⟨j, rfl⟩ := hm
        rw [ht'φ]
        exact ht.nonneg j
      · rw [ht'0 m hm]
    · rw [← ht.sum_sq]
      exact (transfer (fun i ↦ t i ^ 2) (fun m ↦ t' m ^ 2)
        (fun i hi ↦ by simp [htJ i hi]) (fun m hm ↦ by simp [ht'0 m hm])
        fun j ↦ by simp [ht'φ]).symm
  have hU' : U' * U'ᴴ = 1 := by
    rw [← hU]
    ext k l
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact (transfer (fun i ↦ U k i * U l i) (fun m ↦ U' k m * U' l m)
      (fun i hi ↦ by simp [hUJ k i hi]) (fun m hm ↦ by simp [hU'0 k m hm])
      fun j ↦ by simp [hU'φ]).symm
  have hval : weightedAbsSum t (Uᴴ * U) = weightedAbsSum t' (U'ᴴ * U') := by
    unfold weightedAbsSum
    refine transfer _ _ (fun i hi ↦ by simp [htJ i hi]) (fun m hm ↦ by simp [ht'0 m hm])
      fun j₁ ↦ ?_
    refine transfer _ _ (fun i hi ↦ by simp [htJ i hi]) (fun m hm ↦ by simp [ht'0 m hm])
      fun j₂ ↦ ?_
    rw [ht'φ, ht'φ, hgram]
  rw [hval]
  exact le_clConst ht' (conjTranspose_mul_self_mem_orthProjs hU')

/-- **Monotonicity**: `clConst ℝ ι r ≤ clConst ℝ ι' r` if `ι` has at most as many elements as
`ι'`; so `λ(r, n)` is nondecreasing in `n`. -/
theorem clConst_le_of_card_le (h : Fintype.card ι ≤ Fintype.card ι') :
    clConst ℝ ι r ≤ clConst ℝ ι' r := by
  classical
  refine clConst_le clConst_nonneg fun t P ht hP ↦ ?_
  obtain ⟨U, hU, rfl⟩ := exists_parseval_of_mem_orthProjs hP
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le h
  exact weightedAbsSum_le_clConst_of_support ht hU univ (by simp) (by simp)
    (fun j ↦ f j) (f.injective.comp Subtype.val_injective)

end Padding

end ProjectionConstants.Stabilization

/-! ### The stabilization theorem -/

namespace ProjectionConstants

open Stabilization

/-- The bound `N_r = 2^r C(r+1, 2)` of [KMMP, Theorem 1.3]. -/
def stabilizationBound (r : ℕ) : ℕ := 2 ^ r * (r + 1).choose 2

/-- `λ(r, n) > 0` for `1 ≤ r ≤ n`: the Chalmers–Lewicki quantity `clConst ℝ ι r` is positive if
`1 ≤ r ≤ |ι|`. -/
lemma clConst_pos {ι : Type*} [Fintype ι] {r : ℕ} (hr : 0 < r)
    (hrι : r ≤ Fintype.card ι) : 0 < clConst ℝ ι r := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (hr.trans_le hrι)
  obtain ⟨P, hP⟩ := orthProjs_nonempty (𝕜 := ℝ) hrι
  have h1 := le_clConst isUnitWeight_uniform hP
  rw [weightedAbsSum_uniform] at h1
  have h2 : (r : ℝ) ≤ absSum P := by
    rw [← sum_re_diag hP]
    unfold absSum
    exact sum_le_sum fun i _ ↦ (RCLike.re_le_norm _).trans
      (single_le_sum (f := fun j ↦ ‖P i j‖) (fun j _ ↦ norm_nonneg _) (mem_univ i))
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have : 0 < absSum P / Fintype.card ι := div_pos (hr'.trans_le h2) hN
  linarith

/-- **The key inequality**: `λ(r, n) ≤ λ(r, N_r)` for every `n`. -/
theorem clConst_le_clConst_stabilizationBound (ι : Type*) [Fintype ι] (r : ℕ) :
    clConst ℝ ι r ≤ clConst ℝ (Fin (stabilizationBound r)) r := by
  classical
  refine clConst_le clConst_nonneg fun t₀ P₀ ht₀ hP₀ ↦ ?_
  have hr : r ≤ Fintype.card ι := le_card_of_mem_orthProjs hP₀
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · have := weightedAbsSum_le_sqrt ht₀ hP₀
    simp only [Nat.cast_zero, Real.sqrt_zero] at this
    exact this.trans clConst_nonneg
  have : Nonempty ι := Fintype.card_pos_iff.mp (hr0.trans_le hr)
  obtain ⟨t, P, ht, hP, heq⟩ := exists_clConst_eq (𝕜 := ℝ) hr
  obtain ⟨U, hU, rfl⟩ := exists_parseval_of_mem_orthProjs hP
  obtain ⟨a, ha0, ha, hcard⟩ := IsMaximizer.exists_sparse ⟨ht, hU, heq⟩ (clConst_pos hr0 hr)
  set J := univ.filter (a · ≠ 0) with hJ
  have htJ : ∀ i ∉ J, a i * t i = 0 := fun i hi ↦ by
    simp only [hJ, mem_filter, mem_univ, true_and, not_not] at hi
    rw [hi, zero_mul]
  have hUJ : ∀ k, ∀ i ∉ J, (U * diagonal a) k i = 0 := fun k i hi ↦ by
    simp only [hJ, mem_filter, mem_univ, true_and, not_not] at hi
    rw [Matrix.mul_diagonal, hi, mul_zero]
  calc weightedAbsSum t₀ P₀ ≤ clConst ℝ ι r := le_clConst ht₀ hP₀
    _ = weightedAbsSum (fun i ↦ a i * t i) ((U * diagonal a)ᴴ * (U * diagonal a)) := ha.eq.symm
    _ ≤ clConst ℝ (Fin (stabilizationBound r)) r :=
        weightedAbsSum_le_clConst_of_support ha.unit ha.parseval J htJ hUJ
          (fun j ↦ Fin.castLE hcard (J.equivFin j))
          ((Fin.castLE_injective hcard).comp J.equivFin.injective)

/-- `λ_ℝ(r, n) ≤ λ_ℝ(r, N_r)` for every `n`. -/
theorem maxRelProjConst_le_stabilizationBound (r n : ℕ) :
    maxRelProjConst ℝ r n ≤ maxRelProjConst ℝ r (stabilizationBound r) := by
  rw [maxRelProjConst_eq_clConst, maxRelProjConst_eq_clConst]
  exact clConst_le_clConst_stabilizationBound _ r

/-- **`λ(r) = λ(r, N_r)`**: the maximal projection constant is attained in `ℓ∞^{N_r}`. -/
theorem maxProjConst_eq_maxRelProjConst_stabilizationBound (r : ℕ) :
    maxProjConst ℝ r = maxRelProjConst ℝ r (stabilizationBound r) :=
  le_antisymm
    (by
      rw [maxProjConst_eq_iSup_maxRelProjConst]
      exact ciSup_le (maxRelProjConst_le_stabilizationBound r))
    (maxRelProjConst_le_maxProjConst r _)

/-- **Stabilization** ([KMMP, Theorem 1.3]): `λ_ℝ(r, n) = λ_ℝ(r)` for all
`n ≥ N_r = 2^r C(r+1, 2)`. -/
theorem maxRelProjConst_eq_maxProjConst {r n : ℕ} (hn : stabilizationBound r ≤ n) :
    maxRelProjConst ℝ r n = maxProjConst ℝ r := by
  refine le_antisymm (maxRelProjConst_le_maxProjConst r n) ?_
  rw [maxProjConst_eq_maxRelProjConst_stabilizationBound, maxRelProjConst_eq_clConst,
    maxRelProjConst_eq_clConst]
  exact clConst_le_of_card_le (by simpa using hn)

/-- The supremum defining `λ_ℝ(r)` is a maximum: some unit weight `t` and orthogonal projection
`P` of rank `r` on `ℝ^{N_r}` attain `∑ᵢⱼ tᵢ tⱼ |Pᵢⱼ| = λ_ℝ(r)`. -/
theorem exists_weightedAbsSum_eq_maxProjConst {r : ℕ} (hr : 1 ≤ r) :
    ∃ (t : Fin (stabilizationBound r) → ℝ)
      (P : Matrix (Fin (stabilizationBound r)) (Fin (stabilizationBound r)) ℝ),
      IsUnitWeight t ∧ P ∈ orthProjs ℝ (Fin (stabilizationBound r)) r ∧
        weightedAbsSum t P = maxProjConst ℝ r := by
  have hN : r ≤ stabilizationBound r :=
    (Nat.lt_two_pow_self).le.trans (Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega)))
  have : Nonempty (Fin (stabilizationBound r)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨t, P, ht, hP, heq⟩ := exists_clConst_eq (𝕜 := ℝ) (ι := Fin (stabilizationBound r))
    (by simpa using hN)
  refine ⟨t, P, ht, hP, ?_⟩
  rw [heq, maxProjConst_eq_maxRelProjConst_stabilizationBound, maxRelProjConst_eq_clConst]

end ProjectionConstants
