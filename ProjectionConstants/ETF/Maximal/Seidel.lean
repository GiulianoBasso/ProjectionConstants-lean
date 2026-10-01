/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ETF.Basic

/-!
# Equiangular tight frames from Seidel matrices

An ETF projection with `N` rows can be written as `P = α I + β S`, where the **Seidel matrix**
`S` is Hermitian with zero diagonal and unimodular off-diagonal entries. Conversely
(`isETFProj_seidel`), if `S² = k I + l S`, `α² + kβ² = α`, `2αβ + lβ² = β` and `αN = m`, then
`α I + β S` is an ETF projection of rank `m`.

We use this for the trivial frame and for the maximal ETFs whose Gram matrices are not rational:

* `m = 1` (`existsETF_one`): the trivial frame;
* `m = 3`, real (`existsETF_three_real`): the six diagonals of the icosahedron, from the
  symmetric conference matrix `C` of order 6 (`C² = 5I`), `P = ½ (I + C/√5)`;
* `m = 2`, complex (`existsETF_two_complex`): the tetrahedral SIC, `S = A + iB` with `S² = 3I`,
  `P = ½ (I + S/√3)`;
* `m = 3`, complex (`existsETF_three_complex`): the Hesse SIC, `S = ½ (A + i√3 B)` with
  entries sixth roots of unity and `S² = 8I + 2S`, `P = ⅓ I + ⅙ S`.

The matrix identities for the integer matrices `C`, `A`, `B` are checked by the kernel
(`decide +kernel`). These frames give the values `λ_ℝ(1) = 1`, `λ_ℝ(3) = (1 + √5)/2`,
`λ_ℂ(1) = 1`, `λ_ℂ(2) = (1 + √3)/2` and `λ_ℂ(3) = 5/3` of [DL, Theorems 2.4 and 2.5], see
`ProjectionConstants.Values`. All declarations are in the namespace
`ProjectionConstants.MaximalETF`.

## Main definitions

* `conference6`: the symmetric conference matrix of order `6`.
* `sicA2`, `sicB2`: the real and imaginary parts of the Seidel matrix of the tetrahedral SIC.
* `sicA3`, `sicB3`: the integer matrices `A`, `B` with `S = ½ (A + i√3 B)` for the Hesse SIC.
* `complexify c A B`: the complex matrix `A + c B` for integer matrices `A`, `B`.

## Main statements

* `isETFProj_seidel`, `existsETF_of_seidel`: ETF projections and ETFs from Seidel matrices.
* `existsETF_one`: there is an equiangular tight frame of one vector in `𝕜¹`.
* `existsETF_three_real`: there is an equiangular tight frame of `6` vectors in `ℝ³`.
* `existsETF_two_complex`, `existsETF_three_complex`: there are equiangular tight frames of `4`
  vectors in `ℂ²` and of `9` vectors in `ℂ³` (SICs).

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
-/

open Matrix

namespace ProjectionConstants

namespace MaximalETF

section Seidel

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **ETF projections from Seidel matrices.** Let `S` be Hermitian with zero diagonal and
unimodular off-diagonal entries such that `S² = k I + l S`. If `α² + kβ² = α`, `2αβ + lβ² = β`
and `αN = m`, then `α I + β S` is an ETF projection of rank `m`. -/
theorem isETFProj_seidel {S : Matrix ι ι 𝕜} (hS : Sᴴ = S) (hdiag : ∀ i, S i i = 0)
    (hoff : ∀ i j, i ≠ j → ‖S i j‖ = 1) {k l α β : ℝ}
    (hsq : S * S = (k : 𝕜) • (1 : Matrix ι ι 𝕜) + (l : 𝕜) • S) (h1 : α ^ 2 + k * β ^ 2 = α)
    (h2 : 2 * α * β + l * β ^ 2 = β) {m : ℕ} (hm : α * Fintype.card ι = m) :
    IsETFProj m ((α : 𝕜) • (1 : Matrix ι ι 𝕜) + (β : 𝕜) • S) := by
  have hm𝕜 : (α : 𝕜) * Fintype.card ι = m := by
    have := congrArg (fun x : ℝ ↦ (x : 𝕜)) hm
    push_cast at this
    exact this
  refine ⟨⟨.of_conjTranspose_eq ?_ ?_, ?_⟩, fun i ↦ ?_, ⟨|β|, fun i j hij ↦ ?_⟩⟩
  · rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_one, hS]
    simp [RCLike.star_def, RCLike.conj_ofReal]
  · have e : ((α : 𝕜) • (1 : Matrix ι ι 𝕜) + (β : 𝕜) • S) * ((α : 𝕜) • 1 + (β : 𝕜) • S) =
        ((α ^ 2 + k * β ^ 2 : ℝ) : 𝕜) • (1 : Matrix ι ι 𝕜) +
          ((2 * α * β + l * β ^ 2 : ℝ) : 𝕜) • S := by
      simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hsq, smul_add, smul_smul]
      push_cast
      module
    rw [e, h1, h2]
  · rw [trace_add, trace_smul, trace_smul, trace_one]
    have : S.trace = 0 := by simp [Matrix.trace, hdiag]
    rw [this, smul_zero, add_zero, smul_eq_mul, ← hm𝕜]
  · have hN : (Fintype.card ι : 𝕜) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.2 ⟨i⟩).ne'
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, one_apply_eq, hdiag, smul_zero,
      add_zero, smul_eq_mul, mul_one, ← hm𝕜]
    field_simp
  · rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, one_apply_ne hij, smul_zero,
      zero_add, smul_eq_mul, norm_mul, hoff i j hij, mul_one, RCLike.norm_ofReal]

/-- **ETFs from Seidel matrices.** Under the hypotheses of `isETFProj_seidel` with `m ≠ 0`, there
is an equiangular tight frame of `N` vectors in `𝕜^m`. -/
theorem existsETF_of_seidel {N : ℕ} {S : Matrix (Fin N) (Fin N) 𝕜} (hS : Sᴴ = S)
    (hdiag : ∀ i, S i i = 0) (hoff : ∀ i j, i ≠ j → ‖S i j‖ = 1) {k l α β : ℝ}
    (hsq : S * S = (k : 𝕜) • (1 : Matrix (Fin N) (Fin N) 𝕜) + (l : 𝕜) • S)
    (h1 : α ^ 2 + k * β ^ 2 = α) (h2 : 2 * α * β + l * β ^ 2 = β) {m : ℕ} (hm0 : m ≠ 0)
    (hm : α * N = m) : ExistsETF 𝕜 m N :=
  (isETFProj_seidel hS hdiag hoff hsq h1 h2 (by simpa using hm)).exists_isETF hm0

end Seidel

/-! ### `m = 1` -/

/-- The trivial equiangular tight frame of one vector in `𝕜¹`. -/
theorem existsETF_one (𝕜 : Type*) [RCLike 𝕜] : ExistsETF 𝕜 1 1 :=
  existsETF_of_seidel (S := 0) (k := 0) (l := 0) (α := 1) (β := 0) (by simp) (fun _ ↦ rfl)
    (fun i j h ↦ absurd (Subsingleton.elim i j) h) (by simp) (by norm_num) (by norm_num)
    one_ne_zero (by norm_num)

/-! ### `m = 3`, real: the icosahedron -/

/-- The symmetric conference matrix of order 6 (Paley, `q = 5`). -/
def conference6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 0, 1, -1, -1, 1;
     1, 1, 0, 1, -1, -1;
     1, -1, 1, 0, 1, -1;
     1, -1, -1, 1, 0, 1;
     1, 1, -1, -1, 1, 0]

/-- `C² = 5 I`, `Cᵀ = C`, `C` has zero diagonal and off-diagonal entries `±1`, for the
conference matrix `C = conference6`. -/
lemma conference6_facts :
    (∀ i j, (conference6 * conference6) i j = if i = j then 5 else 0) ∧ conference6ᵀ = conference6 ∧
    (∀ i, conference6 i i = 0) ∧ (∀ i j, i ≠ j → conference6 i j ^ 2 = 1) := by decide +kernel

/-- There is an equiangular tight frame of 6 vectors in `ℝ³` (the diagonals of the
icosahedron). -/
theorem existsETF_three_real : ExistsETF ℝ 3 6 := by
  obtain ⟨hsq, hT, hdiag, hoff⟩ := conference6_facts
  set S : Matrix (Fin 6) (Fin 6) ℝ := conference6.map (Int.castRingHom ℝ) with hSdef
  have h5 : (0 : ℝ) < 5 := by norm_num
  refine existsETF_of_seidel (S := S) (k := 5) (l := 0) (α := 1 / 2) (β := 1 / (2 * √5))
    ?_ ?_ ?_ ?_ ?_ (by ring) (by norm_num) (by norm_num)
  · rw [hSdef, conjTranspose_eq_transpose_of_trivial, ← transpose_map, hT]
  · intro i; simp [hSdef, hdiag]
  · intro i j hij
    have h := hoff i j hij
    have h' : ((conference6 i j : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast h
    simp only [hSdef, map_apply, Int.coe_castRingHom, Real.norm_eq_abs]
    rw [← sq_eq_sq₀ (abs_nonneg _) zero_le_one, sq_abs, h', one_pow]
  · ext i j
    rw [hSdef, ← Matrix.map_mul, map_apply, hsq]
    by_cases hij : i = j <;> simp [hij]
  · rw [show (1 / (2 * √5)) ^ 2 = 1 / 20 by
      rw [div_pow, mul_pow, Real.sq_sqrt h5.le]; norm_num]
    norm_num

/-! ### `m = 2`, complex: the tetrahedral SIC -/

/-- Real part of the Seidel matrix of the tetrahedral SIC. -/
def sicA2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 1, 1;
     1, 0, 0, 0;
     1, 0, 0, 0;
     1, 0, 0, 0]

/-- Imaginary part of the Seidel matrix of the tetrahedral SIC. -/
def sicB2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 0;
     0, 0, 1, -1;
     0, -1, 0, 1;
     0, 1, -1, 0]

/-- The matrix `A` in the Seidel matrix `S = ½ (A + i√3 B)` of the Hesse SIC. -/
def sicA3 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0, -2, -2, -2, 1, 1, -2, 1, 1;
     -2, 0, -2, 1, 1, -2, 1, 1, -2;
     -2, -2, 0, 1, -2, 1, 1, -2, 1;
     -2, 1, 1, 0, -2, -2, -2, 1, 1;
     1, 1, -2, -2, 0, -2, 1, 1, -2;
     1, -2, 1, -2, -2, 0, 1, -2, 1;
     -2, 1, 1, -2, 1, 1, 0, -2, -2;
     1, 1, -2, 1, 1, -2, -2, 0, -2;
     1, -2, 1, 1, -2, 1, -2, -2, 0]

/-- The matrix `B` in the Seidel matrix `S = ½ (A + i√3 B)` of the Hesse SIC. -/
def sicB3 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0, 0, 0, 0, -1, 1, 0, 1, -1;
     0, 0, 0, -1, 1, 0, 1, -1, 0;
     0, 0, 0, 1, 0, -1, -1, 0, 1;
     0, 1, -1, 0, 0, 0, 0, -1, 1;
     1, -1, 0, 0, 0, 0, -1, 1, 0;
     -1, 0, 1, 0, 0, 0, 1, 0, -1;
     0, -1, 1, 0, 1, -1, 0, 0, 0;
     -1, 1, 0, 1, -1, 0, 0, 0, 0;
     1, 0, -1, -1, 0, 1, 0, 0, 0]

/-- The integer identities behind `S² = 3 I` for `S = A + iB` (`A = sicA2`, `B = sicB2`), and
the conditions making `S` a Seidel matrix. -/
lemma sic2_facts :
    sicA2 * sicA2 - sicB2 * sicB2 = 3 • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
    sicA2 * sicB2 + sicB2 * sicA2 = 0 ∧ sicA2ᵀ = sicA2 ∧ sicB2ᵀ = -sicB2 ∧
    (∀ i, sicA2 i i = 0 ∧ sicB2 i i = 0) ∧
    (∀ i j, i ≠ j → sicA2 i j ^ 2 + sicB2 i j ^ 2 = 1) := by decide +kernel

/-- The integer identities behind `T² = 32 I + 4 T` for `T = A + i√3 B` (`A = sicA3`,
`B = sicB3`), and the conditions making `T / 2` a Seidel matrix. -/
lemma sic3_facts :
    sicA3 * sicA3 - 3 • (sicB3 * sicB3) = 32 • (1 : Matrix (Fin 9) (Fin 9) ℤ) + 4 • sicA3 ∧
    sicA3 * sicB3 + sicB3 * sicA3 = 4 • sicB3 ∧ sicA3ᵀ = sicA3 ∧ sicB3ᵀ = -sicB3 ∧
    (∀ i, sicA3 i i = 0 ∧ sicB3 i i = 0) ∧
    (∀ i j, i ≠ j → sicA3 i j ^ 2 + 3 * sicB3 i j ^ 2 = 4) := by decide +kernel

section Complexify

variable {n : ℕ}

/-- The entrywise cast of integer matrices to complex matrices, as a ring homomorphism. -/
noncomputable abbrev castComplex : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℂ :=
  (Int.castRingHom ℂ).mapMatrix

/-- The complex matrix `A + c B` for integer matrices `A`, `B`. -/
noncomputable def complexify (c : ℂ) (A B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℂ :=
  castComplex A + c • castComplex B

lemma complexify_apply (c : ℂ) (A B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    complexify c A B i j = (A i j : ℂ) + c * (B i j : ℂ) := by
  simp [complexify, castComplex, RingHom.mapMatrix_apply]

lemma complexify_mul_self (c : ℂ) (A B : Matrix (Fin n) (Fin n) ℤ) :
    complexify c A B * complexify c A B =
      castComplex (A * A) + c • castComplex (A * B + B * A) + c ^ 2 • castComplex (B * B) := by
  simp only [complexify, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, map_mul, map_add,
    smul_add, smul_smul]
  module

lemma complexify_conjTranspose {c : ℂ} (hc : star c = -c) {A B : Matrix (Fin n) (Fin n) ℤ}
    (hA : Aᵀ = A) (hB : Bᵀ = -B) : (complexify c A B)ᴴ = complexify c A B := by
  ext i j
  have hA' : A j i = A i j := by rw [← transpose_apply A i j, hA]
  have hB' : B j i = -B i j := by rw [← transpose_apply B i j, hB, neg_apply]
  rw [conjTranspose_apply, complexify_apply, complexify_apply, hA', hB', star_add, star_mul', hc]
  simp

lemma complexify_diag {c : ℂ} {A B : Matrix (Fin n) (Fin n) ℤ} (h : ∀ i, A i i = 0 ∧ B i i = 0)
    (i : Fin n) : complexify c A B i i = 0 := by
  rw [complexify_apply, (h i).1, (h i).2]; simp

lemma norm_complexify_apply (s : ℝ) (A B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    ‖complexify (Complex.I * s) A B i j‖ ^ 2 = (A i j : ℝ) ^ 2 + s ^ 2 * (B i j : ℝ) ^ 2 := by
  rw [complexify_apply, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

end Complexify

/-- There is an equiangular tight frame of 4 vectors in `ℂ²` (a SIC-POVM). -/
theorem existsETF_two_complex : ExistsETF ℂ 2 4 := by
  obtain ⟨hsq, hanti, hA, hB, hdiag, hnorm⟩ := sic2_facts
  set S := complexify (Complex.I * ((1 : ℝ) : ℂ)) sicA2 sicB2 with hSdef
  have h3 : (0 : ℝ) < 3 := by norm_num
  refine existsETF_of_seidel (S := S) (k := 3) (l := 0) (α := 1 / 2) (β := 1 / (2 * √3))
    (complexify_conjTranspose (by simp) hA hB) (complexify_diag hdiag) ?_ ?_ ?_ (by ring)
    (by norm_num) (by norm_num)
  · intro i j hij
    have h := norm_complexify_apply 1 sicA2 sicB2 i j
    have hij' : ((sicA2 i j : ℝ)) ^ 2 + (sicB2 i j : ℝ) ^ 2 = 1 := by
      exact_mod_cast hnorm i j hij
    rw [one_pow, one_mul, hij'] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  · have hc : (Complex.I * ((1 : ℝ) : ℂ)) ^ 2 = -1 := by simp
    rw [hSdef, complexify_mul_self, hanti, map_zero, smul_zero, add_zero, hc, neg_one_smul,
      ← sub_eq_add_neg, ← map_sub, hsq, map_nsmul, map_one, ← Nat.cast_smul_eq_nsmul ℂ]
    simp
  · rw [show (1 / (2 * √3)) ^ 2 = 1 / 12 by
      rw [div_pow, mul_pow, Real.sq_sqrt h3.le]; norm_num]
    norm_num

/-- There is an equiangular tight frame of 9 vectors in `ℂ³` (the Hesse SIC). -/
theorem existsETF_three_complex : ExistsETF ℂ 3 9 := by
  obtain ⟨hsq, hanti, hA, hB, hdiag, hnorm⟩ := sic3_facts
  set c : ℂ := Complex.I * ((√3 : ℝ) : ℂ) with hcdef
  set T := complexify c sicA3 sicB3 with hTdef
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hs : c ^ 2 = -3 := by
    rw [hcdef, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt h3.le]; push_cast; ring
  have hTT : T * T = (32 : ℂ) • (1 : Matrix (Fin 9) (Fin 9) ℂ) + (4 : ℂ) • T := by
    rw [hTdef, complexify_mul_self, hs, hanti]
    have e : sicA3 * sicA3 = 32 • 1 + 4 • sicA3 + 3 • (sicB3 * sicB3) := by
      rw [← hsq]; abel
    rw [e]
    simp only [map_add, map_nsmul, map_one, complexify, ← Nat.cast_smul_eq_nsmul ℂ]
    module
  refine existsETF_of_seidel (S := ((1 / 2 : ℝ) : ℂ) • T) (k := 8) (l := 2) (α := 1 / 3)
    (β := 1 / 6) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [conjTranspose_smul, hTdef, complexify_conjTranspose (by simp [hcdef]) hA hB]
    simp
  · intro i; simp [hTdef, complexify_diag hdiag]
  · intro i j hij
    have h := norm_complexify_apply (√3) sicA3 sicB3 i j
    have hij' : ((sicA3 i j : ℝ)) ^ 2 + 3 * (sicB3 i j : ℝ) ^ 2 = 4 := by
      exact_mod_cast hnorm i j hij
    rw [Real.sq_sqrt h3.le, hij'] at h
    have h2 : ‖T i j‖ = 2 := by
      have := norm_nonneg (T i j)
      nlinarith [sq_nonneg (‖T i j‖ - 2)]
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, h2, Complex.norm_real]
    norm_num
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hTT]
    push_cast
    module

end MaximalETF

end ProjectionConstants
