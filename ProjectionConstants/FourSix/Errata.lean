/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.FourSix.Certificate

/-!
# The three maxima `M₁`, `M₂` and `M₃`

Write `Π(n, d)` for the maximal relative projection constant of [JFA] (in Lean
`maxRelProjConst ℝ n d`), `𝒮₆` for the set of `6 × 6` sign matrices (`IsSignMatrix`) and `𝒟₆`
for the set of weights `D = diag(w)` (`IsWeight w`); `√D S √D` is `weightedSign S w` and
`Tr(AP)` is `frobeniusInner A P`. [JFA, §4.4] reduces `Π(4, 6)` to the three sign matrices
`A1, A2, A3 ∈ 𝒮₆` below. They represent the three two-graphs on six vertices whose sign matrices
have signature `(n₊, n₋) = (4, 2)` (Bussemaker–Mathon–Seidel), and `Π(4, 6) = max(M₁, M₂, M₃)`
for `Mᵢ = max { kyFanSum 4 (√D Aᵢ √D) : D ∈ 𝒟₆ }`. This file proves `M₁ ≤ 5/3`, `M₂ ≤ 5/3` and
`M₃ = 5/3`.

* `M₁ ≤ 5/3`, by the argument of [JFA-E, item 4]. For the six unit vectors
  `v₁ = v₂ = (1, 0)`, `v₃ = (-1/2, √3/2)`, `v₄ = (-1/2, -√3/2)`, `v₅ = (-√3/2, -1/2)`,
  `v₆ = (-√3/2, 1/2)` of `ℝ²`, the matrix `C = (2/3)(⟨vⱼ, vₖ⟩)` is positive semidefinite with
  diagonal `2/3`, and `B = A1 + C` is positive semidefinite (`posSemidef_A1_add_C1`). The
  certificate argument (`frobeniusInner_weightedSign_le_of_certificate`) gives
  `kyFanSum 4 (√D A1 √D) ≤ Tr(√D B √D) = ∑ⱼ wⱼ Bⱼⱼ = 5/3`.
* `M₂ ≤ 5/3`. The paper uses the concavity in `D` of the sum of the four largest eigenvalues of
  `A2 D` (Lieb–Siedentop), a symmetrization ([JFA, Lemma 4.4]), an estimate for the largest root
  of a cubic ([JFA, Lemma 4.5]) and Lagrange multipliers. We use the certificate argument of
  [JFA-E] instead, with a rational matrix `C` (`certificateA2`) that is invariant under the
  symmetries of `A2`.
* `M₃ = 5/3`. The matrix `A3 = J - 2K` (with `J` the all-ones matrix and `K` the reversal
  permutation matrix) has the eigenvalues `4, 2, 2, 2, -2, -2`. The lower bound is
  `kyFanSum 4 (A3/6) = 5/3`, attained at the spectral projection `P₊ = J/6 + (I - K)/2` of rank
  four (`projA3`). The upper bound is again a certificate: `C = 2 Π₋ = I + K - J/3`, twice the
  projection onto the eigenspace of `-2` (`certificateA3`; the paper uses the symmetrization of
  [JFA, Lemma 4.4] instead).

## Main definitions

* `A1`, `A2`, `A3`: the sign matrices of [JFA, §4.4]; `A1Int`, `A2Int`, `A3Int` are the same
  matrices with integer entries.
* `planeVectors`, `C1`: the vectors `vⱼ` and the matrix `C` of [JFA-E, item 4].
* `certificateA2`, `certificateA3`: the rational certificates (`SosCertificate`) for `A2` and
  `A3`.
* `projA3`: the spectral projection `P₊` of `A3`.

## Main statements

* `kyFanSum_four_weightedSign_A1_le`: `M₁ ≤ 5/3`.
* `kyFanSum_four_weightedSign_A2_le`: `M₂ ≤ 5/3`.
* `isGreatest_kyFanSum_four_weightedSign_A3`: `M₃ = 5/3`, attained at `D = I/6`.
* `frobeniusInner_weightedSign_A1_le`, `frobeniusInner_weightedSign_A2_le`,
  `frobeniusInner_weightedSign_A3_le`: `Tr(√D Aᵢ √D P) ≤ 5/3` for every orthogonal projection
  `P`, whatever its rank (used in `ProjectionConstants.FourSix.Classification`).
* `map_ratCast_mem_orthProjs`: a rational symmetric idempotent matrix of trace `n` is an
  orthogonal projection of rank `n`.

## References

* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Finset Matrix

namespace ProjectionConstants.FourSix

/-! ### Sign matrices from integer matrices -/

/-- A symmetric integer matrix with entries `±1` and ones on the diagonal is a sign matrix. -/
lemma isSignMatrix_map_intCast {ι : Type*} {T : Matrix ι ι ℤ} (hs : Tᵀ = T)
    (hpm : ∀ p : ι × ι, T p.1 p.2 = 1 ∨ T p.1 p.2 = -1) (hd : ∀ i, T i i = 1) :
    IsSignMatrix (T.map (Int.cast : ℤ → ℝ)) := by
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i ↦ ?_⟩
  · simp only [map_apply]
    exact congrArg Int.cast (congrFun (congrFun hs j) i).symm
  · rcases hpm (i, j) with h | h <;> simp [h]
  · simp [hd i]

/-! ### The matrices `A1, A2, A3` -/

/-- `A1` of [JFA, §4.4], as an integer matrix. -/
def A1Int : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1, -1, 1, 1, 1, 1;
    -1, 1, 1, 1, 1, 1;
    1, 1, 1, 1, 1, -1;
    1, 1, 1, 1, -1, 1;
    1, 1, 1, -1, 1, -1;
    1, 1, -1, 1, -1, 1]

/-- `A2` of [JFA, §4.4], as an integer matrix. -/
def A2Int : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
    1, 1, -1, 1, 1, 1;
    1, -1, 1, 1, 1, 1;
    1, 1, 1, 1, -1, -1;
    1, 1, 1, -1, 1, -1;
    1, 1, 1, -1, -1, 1]

/-- `A3` of [JFA, §4.4], as an integer matrix: `J - 2K` for the reversal permutation `K`. -/
def A3Int : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, -1;
    1, 1, 1, 1, -1, 1;
    1, 1, 1, -1, 1, 1;
    1, 1, -1, 1, 1, 1;
    1, -1, 1, 1, 1, 1;
    -1, 1, 1, 1, 1, 1]

/-- The sign matrix `A1 ∈ 𝒮₆` of [JFA, §4.4]. -/
noncomputable def A1 : Matrix (Fin 6) (Fin 6) ℝ := A1Int.map (↑)

/-- The sign matrix `A2 ∈ 𝒮₆` of [JFA, §4.4]. -/
noncomputable def A2 : Matrix (Fin 6) (Fin 6) ℝ := A2Int.map (↑)

/-- The sign matrix `A3 ∈ 𝒮₆` of [JFA, §4.4]. -/
noncomputable def A3 : Matrix (Fin 6) (Fin 6) ℝ := A3Int.map (↑)

/-- The diagonal entries of `A1Int` are `1`. -/
lemma A1Int_apply_self : ∀ i, A1Int i i = 1 := by decide

/-- The diagonal entries of `A2Int` are `1`. -/
lemma A2Int_apply_self : ∀ i, A2Int i i = 1 := by decide

/-- The diagonal entries of `A3Int` are `1`. -/
lemma A3Int_apply_self : ∀ i, A3Int i i = 1 := by decide

/-- `A1` is a sign matrix. -/
lemma isSignMatrix_A1 : IsSignMatrix A1 :=
  isSignMatrix_map_intCast (by decide) (by decide) A1Int_apply_self

/-- `A2` is a sign matrix. -/
lemma isSignMatrix_A2 : IsSignMatrix A2 :=
  isSignMatrix_map_intCast (by decide) (by decide) A2Int_apply_self

/-- `A3` is a sign matrix. -/
lemma isSignMatrix_A3 : IsSignMatrix A3 :=
  isSignMatrix_map_intCast (by decide) (by decide) A3Int_apply_self

/-! ### `M₁ ≤ 5/3`: the argument of the erratum -/

/-- The six unit vectors `vⱼ ∈ ℝ²` of [JFA-E, item 4]. -/
noncomputable def planeVectors : Fin 6 → Fin 2 → ℝ :=
  ![![1, 0], ![1, 0], ![-1 / 2, √3 / 2], ![-1 / 2, -√3 / 2], ![-√3 / 2, -1 / 2], ![-√3 / 2, 1 / 2]]

/-- The matrix `C = (2/3)(⟨vⱼ, vₖ⟩)ⱼₖ` of [JFA-E, item 4]. -/
noncomputable def C1 : Matrix (Fin 6) (Fin 6) ℝ :=
  of fun j k ↦ 2 / 3 * ∑ a, planeVectors j a * planeVectors k a

/-- `C` is a Gram matrix, hence positive semidefinite. -/
lemma posSemidef_C1 : C1.PosSemidef := by
  refine posSemidef_of_isSymm (.ext fun i j ↦ ?_) fun x ↦ ?_
  · simp only [C1, of_apply]
    congr 1
    exact sum_congr rfl fun a _ ↦ mul_comm _ _
  have e : x ⬝ᵥ C1 *ᵥ x = 2 / 3 * ∑ a, (∑ j, x j * planeVectors j a) ^ 2 := by
    simp only [dotProduct_mulVec_self_eq_sum, C1, of_apply, Fin.sum_univ_two, Fin.sum_univ_six]
    ring
  rw [e]
  positivity

private lemma sqrt_three_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- The diagonal of `C` is `2/3`: the `vⱼ` are unit vectors. -/
lemma C1_apply_self (j : Fin 6) : C1 j j = 2 / 3 := by
  have hs := sqrt_three_sq
  fin_cases j <;> simp [C1, planeVectors, Fin.sum_univ_two] <;> linarith [hs]

/-- The pivots `Δ₅ = (11√3 - 18)/3` and `Δ₆ = (28√3 - 44)/13` of `B = A1 + C` are positive. -/
private lemma pivots_pos : 0 < 11 * √3 - 18 ∧ 0 < 28 * √3 - 44 := by
  have hs := sqrt_three_sq
  have h0 : 0 ≤ √3 := Real.sqrt_nonneg 3
  constructor <;> nlinarith

/-- **`B = A1 + C` is positive semidefinite** ([JFA-E, item 4]: positive definite, with the leading
principal minors `5/3, 8/3, 8/3, 8/3, (88√3 - 144)/9, (1056 - 608√3)/9`). We verify the
equivalent factorization `B = LΔLᵀ`, whose pivots
`Δ = (5/3, 8/5, 1, 1, (11√3 - 18)/3, (28√3 - 44)/13)` are the quotients of consecutive leading
principal minors:
`xᵀBx = (5/3) y₁² + (8/5) y₂² + y₃² + y₄² + (11√3 - 18)/3 · y₅² + (28√3 - 44)/13 · y₆²`
for `y = Lᵀx`. -/
lemma posSemidef_A1_add_C1 : (A1 + C1).PosSemidef := by
  refine posSemidef_of_isSymm (.ext fun i j ↦ ?_) fun x ↦ ?_
  · simp only [Matrix.add_apply, isSignMatrix_A1.symm i j, C1, of_apply]
    congr 2
    exact sum_congr rfl fun a _ ↦ mul_comm _ _
  have hs := sqrt_three_sq
  set s := √3
  have key : x ⬝ᵥ (A1 + C1) *ᵥ x =
      5 / 3 * (x 0 - x 1 / 5 + 2 * x 2 / 5 + 2 * x 3 / 5 + (3 - s) / 5 * x 4 +
        (3 - s) / 5 * x 5) ^ 2 +
      8 / 5 * (x 1 + x 2 / 2 + x 3 / 2 + (3 - s) / 4 * x 4 + (3 - s) / 4 * x 5) ^ 2 +
      (x 2 + s / 3 * x 4 + (2 * s / 3 - 2) * x 5) ^ 2 +
      (x 3 + (2 * s / 3 - 2) * x 4 + s / 3 * x 5) ^ 2 +
      (11 * s - 18) / 3 * (x 4 + (5 - 2 * s) / 13 * x 5) ^ 2 +
      (28 * s - 44) / 13 * x 5 ^ 2 := by
    simp only [dotProduct_mulVec_self_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.add_apply, A1, A1Int, C1, planeVectors, map_apply, of_apply, cons_val_zero,
      cons_val_succ, cons_val_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    push_cast
    linear_combination (-44 * s * x 5 ^ 2 / 507 + x 2 ^ 2 / 6 - x 2 * x 3 / 3 + x 3 ^ 2 / 6 -
      5 * x 4 ^ 2 / 9 + 28 * x 4 * x 5 / 117 + 31 * x 5 ^ 2 / 1521) * hs
  rw [key]
  have h5 := pivots_pos.1
  have h6 := pivots_pos.2
  positivity

/-- `Tr(√D A1 √D P) ≤ 5/3` for every `D ∈ 𝒟₆` and every orthogonal projection `P`. -/
theorem frobeniusInner_weightedSign_A1_le {w : Fin 6 → ℝ} (hw : IsWeight w)
    {P : Matrix (Fin 6) (Fin 6) ℝ} (hP : IsStarProjection P) :
    frobeniusInner (weightedSign A1 w) P ≤ 5 / 3 := by
  have h := frobeniusInner_weightedSign_le_of_certificate (c := 2 / 3) isSignMatrix_A1.diag
    posSemidef_C1 posSemidef_A1_add_C1 (fun j ↦ (C1_apply_self j).le) hw hP
  linarith

/-- **`M₁ ≤ 5/3`** ([JFA, (4.4)], with the argument of [JFA-E, item 4]):
`kyFanSum 4 (√D A1 √D) ≤ 5/3` for every `D ∈ 𝒟₆`. -/
theorem kyFanSum_four_weightedSign_A1_le {w : Fin 6 → ℝ} (hw : IsWeight w) :
    kyFanSum 4 (weightedSign A1 w) ≤ 5 / 3 := by
  have h := kyFanSum_weightedSign_le_of_certificate (c := 2 / 3) (by norm_num)
    isSignMatrix_A1.diag posSemidef_C1 posSemidef_A1_add_C1 (fun j ↦ (C1_apply_self j).le) hw 4
  linarith

/-! ### `M₂ ≤ 5/3` -/

/-- A certificate for `A2`: `C` has the diagonal `13/20` and is invariant under the symmetries of
`A2`, which permute the orbits `{1}, {2, 3}, {4, 5, 6}`. The sums of squares use the vectors
`(1, 0, 0, 0, 0, 0)`, `(0, 1, 1, 0, 0, 0)`, `(0, 0, 0, 1, 1, 1)` (up to lower order terms) and,
for `A2 + C`, the vectors `e₂ - e₃`, `2e₄ - e₅ - e₆`, `e₅ - e₆` of the eigenvalue `2`. -/
def certificateA2 : SosCertificate (Fin 6) where
  C := !![13/20, 0, 0, -3/10, -3/10, -3/10;
      0, 13/20, 13/20, -11/20, -11/20, -11/20;
      0, 13/20, 13/20, -11/20, -11/20, -11/20;
      -3/10, -11/20, -11/20, 13/20, 13/20, 13/20;
      -3/10, -11/20, -11/20, 13/20, 13/20, 13/20;
      -3/10, -11/20, -11/20, 13/20, 13/20, 13/20]
  sosC := [(1/260, ![13, 0, 0, -6, -6, -6]),
      (1/260, ![0, 13, 13, -11, -11, -11]),
      (3/65, ![0, 0, 0, 1, 1, 1])]
  sosAddC := [(1/660, ![33, 20, 20, 14, 14, 14]),
      (1/19140, ![0, 29, 29, 17, 17, 17]),
      (2/435, ![0, 0, 0, 1, 1, 1]),
      (1, ![0, 1, -1, 0, 0, 0]),
      (1/3, ![0, 0, 0, 2, -1, -1]),
      (1, ![0, 0, 0, 0, 1, -1])]

/-- The certificate for `A2` is valid (checked by the kernel). -/
lemma certificateA2_isValid : certificateA2.IsValid A2Int := by decide +kernel

/-- `Tr(√D A2 √D P) ≤ 5/3` for every `D ∈ 𝒟₆` and every orthogonal projection `P`. -/
theorem frobeniusInner_weightedSign_A2_le {w : Fin 6 → ℝ} (hw : IsWeight w)
    {P : Matrix (Fin 6) (Fin 6) ℝ} (hP : IsStarProjection P) :
    frobeniusInner (weightedSign A2 w) P ≤ 5 / 3 :=
  SosCertificate.frobeniusInner_weightedSign_le A2Int_apply_self certificateA2_isValid hw hP

/-- **`M₂ ≤ 5/3`** ([JFA, §4.4]): `kyFanSum 4 (√D A2 √D) ≤ 5/3` for every `D ∈ 𝒟₆`. -/
theorem kyFanSum_four_weightedSign_A2_le {w : Fin 6 → ℝ} (hw : IsWeight w) :
    kyFanSum 4 (weightedSign A2 w) ≤ 5 / 3 :=
  kyFanSum_le (by norm_num) fun _ hP ↦ frobeniusInner_weightedSign_A2_le hw hP.1

/-! ### `M₃ = 5/3` -/

/-- A certificate for `A3`: `C = I + K - J/3`, twice the projection onto the eigenspace of the
eigenvalue `-2` of `A3 = J - 2K`. Then `A3 + C = (2/3) J + (I - K)` and `Cⱼⱼ = 2/3`. -/
def certificateA3 : SosCertificate (Fin 6) where
  C := !![2/3, -1/3, -1/3, -1/3, -1/3, 2/3;
      -1/3, 2/3, -1/3, -1/3, 2/3, -1/3;
      -1/3, -1/3, 2/3, 2/3, -1/3, -1/3;
      -1/3, -1/3, 2/3, 2/3, -1/3, -1/3;
      -1/3, 2/3, -1/3, -1/3, 2/3, -1/3;
      2/3, -1/3, -1/3, -1/3, -1/3, 2/3]
  sosC := [(1/6, ![2, -1, -1, -1, -1, 2]),
      (1/2, ![0, 1, -1, -1, 1, 0])]
  sosAddC := [(2/3, ![1, 1, 1, 1, 1, 1]),
      (1, ![1, 0, 0, 0, 0, -1]),
      (1, ![0, 1, 0, 0, -1, 0]),
      (1, ![0, 0, 1, -1, 0, 0])]

/-- The certificate for `A3` is valid (checked by the kernel). -/
lemma certificateA3_isValid : certificateA3.IsValid A3Int := by decide +kernel

/-- `Tr(√D A3 √D P) ≤ 5/3` for every `D ∈ 𝒟₆` and every orthogonal projection `P`. -/
theorem frobeniusInner_weightedSign_A3_le {w : Fin 6 → ℝ} (hw : IsWeight w)
    {P : Matrix (Fin 6) (Fin 6) ℝ} (hP : IsStarProjection P) :
    frobeniusInner (weightedSign A3 w) P ≤ 5 / 3 :=
  SosCertificate.frobeniusInner_weightedSign_le A3Int_apply_self certificateA3_isValid hw hP

/-- The spectral projection `P₊ = J/6 + (I - K)/2` of `A3` onto the eigenspaces of the
eigenvalues `4, 2, 2, 2`. -/
def projA3 : Matrix (Fin 6) (Fin 6) ℚ :=
  !![2/3, 1/6, 1/6, 1/6, 1/6, -1/3;
    1/6, 2/3, 1/6, 1/6, -1/3, 1/6;
    1/6, 1/6, 2/3, -1/3, 1/6, 1/6;
    1/6, 1/6, -1/3, 2/3, 1/6, 1/6;
    1/6, -1/3, 1/6, 1/6, 2/3, 1/6;
    -1/3, 1/6, 1/6, 1/6, 1/6, 2/3]

/-- A rational symmetric idempotent matrix of trace `n` is an orthogonal projection of rank `n`. -/
lemma map_ratCast_mem_orthProjs {ι : Type*} [Fintype ι] {n : ℕ} {P : Matrix ι ι ℚ} (hs : Pᵀ = P)
    (hi : P * P = P) (ht : P.trace = n) : P.map (Rat.cast : ℚ → ℝ) ∈ orthProjs ℝ ι n := by
  refine ⟨IsStarProjection.of_apply (fun i j ↦ ?_) (fun i j ↦ ?_), ?_⟩
  · simp only [map_apply]
    exact congrArg Rat.cast (congrFun (congrFun hs j) i).symm
  · have h := congrArg (fun M ↦ (M i j : ℝ)) hi
    simpa [mul_apply] using h
  · have h := congrArg (fun q : ℚ ↦ (q : ℝ)) ht
    simpa [Matrix.trace] using h

/-- `P₊` is an orthogonal projection of rank four. -/
lemma projA3_mem_orthProjs : projA3.map (Rat.cast : ℚ → ℝ) ∈ orthProjs ℝ (Fin 6) 4 :=
  map_ratCast_mem_orthProjs (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The uniform weight `D = I/6`. -/
lemma isWeight_const_sixth : IsWeight (fun _ : Fin 6 ↦ (1 / 6 : ℝ)) :=
  ⟨fun _ ↦ by norm_num, by norm_num⟩

/-- `Tr(√D T √D P) = (1/6) ∑ᵢⱼ Tᵢⱼ Pᵢⱼ` for the uniform weight `D = I/6`. -/
lemma frobeniusInner_weightedSign_const_sixth (T : Matrix (Fin 6) (Fin 6) ℤ)
    (P : Matrix (Fin 6) (Fin 6) ℚ) :
    frobeniusInner (weightedSign (T.map (Int.cast : ℤ → ℝ)) fun _ ↦ 1 / 6)
        (P.map (Rat.cast : ℚ → ℝ)) =
      1 / 6 * ((∑ i, ∑ j, (T i j : ℚ) * P i j : ℚ) : ℝ) := by
  have h6 : √(1 / 6 : ℝ) * √(1 / 6) = 1 / 6 := Real.mul_self_sqrt (by norm_num)
  simp only [frobeniusInner, weightedSign, map_apply, of_apply, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_intCast, mul_sum]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  linear_combination ((T i j : ℝ) * (P i j : ℝ)) * h6

/-- `Tr(A3 P₊ / 6) = 5/3`. -/
lemma frobeniusInner_weightedSign_A3_projA3 :
    frobeniusInner (weightedSign A3 fun _ ↦ 1 / 6) (projA3.map (Rat.cast : ℚ → ℝ)) = 5 / 3 := by
  have h : (∑ i, ∑ j, (A3Int i j : ℚ) * projA3 i j : ℚ) = 10 := by decide +kernel
  rw [A3, frobeniusInner_weightedSign_const_sixth, h]
  norm_num

/-- `kyFanSum 4 (A3/6) = 5/3`: the value at the uniform weight `D = I/6`. -/
lemma kyFanSum_four_weightedSign_A3_const_sixth :
    kyFanSum 4 (weightedSign A3 fun _ ↦ 1 / 6) = 5 / 3 :=
  le_antisymm
    (kyFanSum_le (by norm_num) fun _ hP ↦
      frobeniusInner_weightedSign_A3_le isWeight_const_sixth hP.1)
    (frobeniusInner_weightedSign_A3_projA3 ▸ frobeniusInner_le_kyFanSum _ projA3_mem_orthProjs)

/-- **`M₃ = 5/3`** ([JFA, §4.4]): the maximum of `kyFanSum 4 (√D A3 √D)` over `D ∈ 𝒟₆` is
`5/3`, attained at `D = I/6`. -/
theorem isGreatest_kyFanSum_four_weightedSign_A3 :
    IsGreatest {x | ∃ w : Fin 6 → ℝ, IsWeight w ∧ x = kyFanSum 4 (weightedSign A3 w)} (5 / 3) :=
  ⟨⟨_, isWeight_const_sixth, kyFanSum_four_weightedSign_A3_const_sixth.symm⟩, by
    rintro _ ⟨w, hw, rfl⟩
    exact kyFanSum_le (by norm_num) fun _ hP ↦ frobeniusInner_weightedSign_A3_le hw hP.1⟩

end ProjectionConstants.FourSix
