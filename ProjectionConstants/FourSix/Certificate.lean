/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Matrix.KyFan.Fan
import ProjectionConstants.AlmostMinimal.Config

/-!
# The certificate argument of the erratum

In [JFA, §4.4], the bound `M₁ ≤ 5/3`, that is `kyFanSum 4 (√D A1 √D) ≤ 5/3` for every weight `D`
(see `ProjectionConstants.FourSix.Errata`), is proved with calculus. The erratum
[JFA-E, item 4] replaces this calculus by the following short argument.

Let `S` have unit diagonal and let `C` be positive semidefinite (`C ⪰ 0`, see
`Matrix.PosSemidef`) with `S + C ⪰ 0` and `Cⱼⱼ ≤ c` for all `j`. Let `D = diag(w)` be a weight
(`IsWeight w`: `w ≥ 0` and `∑ⱼ wⱼ = 1`) and let `P` be an orthogonal projection
(`IsStarProjection P`). Then `√D C √D ⪰ 0` gives `Tr(√D S √D P) ≤ Tr(√D (S + C) √D P)`, and
`√D (S + C) √D ⪰ 0` gives `Tr(√D (S + C) √D P) ≤ Tr(√D (S + C) √D) = ∑ⱼ wⱼ (1 + Cⱼⱼ) ≤ 1 + c`.
Here `√D S √D` is `weightedSign S w` and `Tr(AP)` is `frobeniusInner A P`. Since the bound holds
for orthogonal projections of every rank, it gives `kyFanSum n (√D S √D) ≤ 1 + c` for every `n`.

To apply the argument with `c = 2/3` to many sign matrices, we use rational certificates: a
rational matrix `C` together with sums of squares `∑ₖ δₖ vₖ vₖᵀ` with `δₖ ≥ 0` for `C` and for
`T + C`, checked by `decide +kernel`. We also show that `Tr(√D S √D P)` is invariant under
switching, which is used in `ProjectionConstants.FourSix.Classification`.

## Main definitions

* `signSwitch ε M`: the switched matrix `EME` for the diagonal matrix `E = diag(ε)`.
* `sosMatrix l`: the rational matrix `∑ₖ δₖ vₖ vₖᵀ` of a list `l` of pairs `(δₖ, vₖ)`.
* `SosCertificate`: a rational certificate, that is, a rational matrix `C` together with
  sum-of-squares decompositions of `C` and of `T + C`.
* `SosCertificate.IsValid T c`: the certificate `c` proves `C ⪰ 0`, `T + C ⪰ 0` and `Cⱼⱼ ≤ 2/3`;
  this is decidable (`SosCertificate.decidableIsValid`).

## Main statements

* `frobeniusInner_weightedSign_le_of_certificate`: the argument above, `Tr(√D S √D P) ≤ 1 + c`.
* `kyFanSum_weightedSign_le_of_certificate`: `kyFanSum n (√D S √D) ≤ 1 + c` for every `n`.
* `frobeniusInner_signSwitch`: switching `A` and `P` by the same sign vector does not change
  `Tr(AP)`.
* `posSemidef_of_sos`: a rational sum of squares with nonnegative coefficients is positive
  semidefinite.
* `SosCertificate.frobeniusInner_weightedSign_le`: a valid certificate for `T` gives
  `Tr(√D T √D P) ≤ 5/3`.

## References

* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Finset Matrix

namespace ProjectionConstants.FourSix

variable {ι : Type*} [Fintype ι]

/-! ### The certificate argument -/

/-- **The certificate argument of the erratum** ([JFA-E, item 4], there for `S = A1`). Let `S`
have unit diagonal, let `C ⪰ 0` with `S + C ⪰ 0` and `Cⱼⱼ ≤ c` for all `j`. Then
`Tr(√D S √D P) ≤ 1 + c` for every weight `D = diag(w)` and every orthogonal projection `P`. -/
theorem frobeniusInner_weightedSign_le_of_certificate {S C : Matrix ι ι ℝ} {c : ℝ}
    (hS : ∀ i, S i i = 1) (hC : C.PosSemidef) (hSC : (S + C).PosSemidef) (hc : ∀ j, C j j ≤ c)
    {w : ι → ℝ} (hw : IsWeight w) {P : Matrix ι ι ℝ} (hP : IsStarProjection P) :
    frobeniusInner (weightedSign S w) P ≤ 1 + c := by
  have h1 := (hSC.weightedSign w).frobeniusInner_le_trace hP
  have h2 := (hC.weightedSign w).frobeniusInner_nonneg hP
  rw [weightedSign_add, frobeniusInner_add] at h1
  have h3 : (weightedSign S w + weightedSign C w).trace ≤ 1 + c := by
    have e : ∀ i, (weightedSign S w + weightedSign C w) i i = w i * (1 + C i i) := fun i ↦ by
      simp only [Matrix.add_apply, weightedSign_apply, hS]
      have := Real.mul_self_sqrt (hw.nonneg i)
      linear_combination (1 + C i i) * this
    simp only [Matrix.trace, Matrix.diag_apply, e]
    calc ∑ i, w i * (1 + C i i) ≤ ∑ i, w i * (1 + c) :=
          sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (by linarith [hc i]) (hw.nonneg i)
      _ = 1 + c := by rw [← sum_mul, hw.sum_eq, one_mul]
  linarith

/-- The certificate argument for the Ky Fan sums: `kyFanSum n (√D S √D) ≤ 1 + c` for every
`n`. -/
theorem kyFanSum_weightedSign_le_of_certificate {S C : Matrix ι ι ℝ} {c : ℝ} (hc0 : 0 ≤ c)
    (hS : ∀ i, S i i = 1) (hC : C.PosSemidef) (hSC : (S + C).PosSemidef) (hc : ∀ j, C j j ≤ c)
    {w : ι → ℝ} (hw : IsWeight w) (n : ℕ) : kyFanSum n (weightedSign S w) ≤ 1 + c :=
  kyFanSum_le (by linarith) fun _ hP ↦
    frobeniusInner_weightedSign_le_of_certificate hS hC hSC hc hw hP.1

/-! ### Switching -/

/-- **Switching**: `EME` for the diagonal sign matrix `E = diag(ε)`. -/
def signSwitch (ε : ι → ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := of fun i j ↦ ε i * M i j * ε j

omit [Fintype ι] in
/-- Switching by a sign vector `ε` preserves sign matrices. -/
lemma isSignMatrix_signSwitch {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1) {S : Matrix ι ι ℝ}
    (hS : IsSignMatrix S) : IsSignMatrix (signSwitch ε S) := by
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i ↦ ?_⟩
  · simp only [signSwitch, of_apply, hS.symm i j]
    ring
  · have hi : ε i = 1 ∨ ε i = -1 := mul_self_eq_one_iff.mp (hε i)
    have hj : ε j = 1 ∨ ε j = -1 := mul_self_eq_one_iff.mp (hε j)
    simp only [signSwitch, of_apply]
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> rcases hS.pm i j with h | h <;>
      simp [hi, hj, h]
  · simp only [signSwitch, of_apply, hS.diag]
    linear_combination hε i

/-- Switching by a sign vector `ε` preserves orthogonal projections. -/
lemma isStarProjection_signSwitch {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1) {P : Matrix ι ι ℝ}
    (hP : IsStarProjection P) : IsStarProjection (signSwitch ε P) := by
  refine IsStarProjection.of_apply (fun i j ↦ ?_) (fun i j ↦ ?_)
  · simp only [signSwitch, of_apply, hP.apply_comm i j]
    ring
  · simp only [signSwitch, of_apply]
    have e : ∀ k, ε i * P i k * ε k * (ε k * P k j * ε j) = ε i * ε j * (P i k * P k j) :=
      fun k ↦ by linear_combination (ε i * P i k * P k j * ε j) * hε k
    simp only [e, ← mul_sum, hP.sum_mul_apply i j]
    ring

omit [Fintype ι] in
/-- Switching commutes with the weighting `S ↦ √D S √D`. -/
lemma weightedSign_signSwitch (ε : ι → ℝ) (S : Matrix ι ι ℝ) (w : ι → ℝ) :
    weightedSign (signSwitch ε S) w = signSwitch ε (weightedSign S w) := by
  ext i j
  simp only [weightedSign, signSwitch, of_apply]
  ring

/-- Switching `A` and `P` by the same sign vector does not change `Tr(AP)`. -/
lemma frobeniusInner_signSwitch {ε : ι → ℝ} (hε : ∀ i, ε i * ε i = 1) (A P : Matrix ι ι ℝ) :
    frobeniusInner (signSwitch ε A) (signSwitch ε P) = frobeniusInner A P := by
  simp only [frobeniusInner, signSwitch, of_apply]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  linear_combination (A i j * P i j * (ε j * ε j)) * hε i + (A i j * P i j) * hε j

/-! ### Rational sums of squares -/

/-- The matrix `∑ₖ δₖ vₖ vₖᵀ` of a list of pairs `(δₖ, vₖ)`. -/
def sosMatrix (l : List (ℚ × (ι → ℚ))) : Matrix ι ι ℚ :=
  (l.map fun p ↦ p.1 • vecMulVec p.2 p.2).sum

omit [Fintype ι] in
/-- `sosMatrix l` is symmetric. -/
lemma sosMatrix_apply_comm (l : List (ℚ × (ι → ℚ))) (i j : ι) :
    sosMatrix l j i = sosMatrix l i j := by
  induction l with
  | nil => simp [sosMatrix]
  | cons p l ih =>
    simp only [sosMatrix, List.map_cons, List.sum_cons, Matrix.add_apply, Matrix.smul_apply,
      vecMulVec_apply, smul_eq_mul] at ih ⊢
    rw [ih, mul_comm (p.2 j)]

/-- The quadratic form of `∑ₖ δₖ vₖ vₖᵀ`, cast to `ℝ`, is `x ↦ ∑ₖ δₖ ⟨vₖ, x⟩²`. -/
lemma dotProduct_mulVec_map_sosMatrix (l : List (ℚ × (ι → ℚ))) (x : ι → ℝ) :
    x ⬝ᵥ (sosMatrix l).map (Rat.cast : ℚ → ℝ) *ᵥ x =
      (l.map fun p ↦ (p.1 : ℝ) * (∑ i, (p.2 i : ℝ) * x i) ^ 2).sum := by
  induction l with
  | nil => simp [sosMatrix]
  | cons p l ih =>
    have e : (sosMatrix (p :: l)).map (Rat.cast : ℚ → ℝ) =
        ((p.1 • vecMulVec p.2 p.2).map (Rat.cast : ℚ → ℝ)) + (sosMatrix l).map Rat.cast := by
      simp only [sosMatrix, List.map_cons, List.sum_cons]
      exact Matrix.map_add _ Rat.cast_add _ _
    rw [e, List.map_cons, List.sum_cons, ← ih]
    simp only [dotProduct_mulVec_self_eq_sum, Matrix.add_apply, add_mul, sum_add_distrib,
      Matrix.map_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Rat.cast_mul]
    congr 1
    rw [sq, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    ring

omit [Fintype ι] in
/-- A rational sum of squares with nonnegative coefficients is positive semidefinite. -/
theorem posSemidef_of_sos [Finite ι] {M : Matrix ι ι ℚ} {l : List (ℚ × (ι → ℚ))}
    (hl : ∀ p ∈ l, 0 ≤ p.1) (hM : M = sosMatrix l) : (M.map (Rat.cast : ℚ → ℝ)).PosSemidef := by
  have := Fintype.ofFinite ι
  subst hM
  refine posSemidef_of_isSymm (.ext fun i j ↦ by simp [sosMatrix_apply_comm l i j]) fun x ↦ ?_
  rw [dotProduct_mulVec_map_sosMatrix]
  refine List.sum_nonneg fun y hy ↦ ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  have := hl p hp
  have : (0 : ℝ) ≤ p.1 := by exact_mod_cast this
  positivity

/-! ### Rational certificates -/

/-- A **rational certificate** for a sign matrix `T`: a matrix `C` together with lists
`(δₖ, vₖ)` for sum-of-squares decompositions of `C` and of `T + C`. -/
structure SosCertificate (ι : Type*) where
  /-- The matrix `C`. -/
  C : Matrix ι ι ℚ
  /-- `C = ∑ₖ δₖ vₖ vₖᵀ`. -/
  sosC : List (ℚ × (ι → ℚ))
  /-- `T + C = ∑ₖ δₖ vₖ vₖᵀ`. -/
  sosAddC : List (ℚ × (ι → ℚ))

/-- The certificate `c` is valid for `T`: `C ⪰ 0`, `T + C ⪰ 0` (by the two sums of squares) and
`Cⱼⱼ ≤ 2/3`. -/
def SosCertificate.IsValid (T : Matrix ι ι ℤ) (c : SosCertificate ι) : Prop :=
  c.C = sosMatrix c.sosC ∧ T.map (Int.cast : ℤ → ℚ) + c.C = sosMatrix c.sosAddC ∧
    (∀ p ∈ c.sosC, 0 ≤ p.1) ∧ (∀ p ∈ c.sosAddC, 0 ≤ p.1) ∧ ∀ j, c.C j j ≤ 2 / 3

/-- Validity of a certificate is decidable, so that it can be checked by `decide +kernel`. -/
instance SosCertificate.decidableIsValid (T : Matrix ι ι ℤ) (c : SosCertificate ι) :
    Decidable (c.IsValid T) := by
  unfold SosCertificate.IsValid
  infer_instance

/-- A valid rational certificate for an integer matrix `T` with unit diagonal gives
`Tr(√D T √D P) ≤ 5/3` for every weight `D = diag(w)` and every orthogonal projection `P`. -/
theorem SosCertificate.frobeniusInner_weightedSign_le {T : Matrix ι ι ℤ} (hT : ∀ i, T i i = 1)
    {c : SosCertificate ι} (hc : c.IsValid T) {w : ι → ℝ} (hw : IsWeight w) {P : Matrix ι ι ℝ}
    (hP : IsStarProjection P) :
    frobeniusInner (weightedSign (T.map (Int.cast : ℤ → ℝ)) w) P ≤ 5 / 3 := by
  obtain ⟨h₁, h₂, hl₁, hl₂, hd⟩ := hc
  have hC := posSemidef_of_sos hl₁ h₁
  have hTC := posSemidef_of_sos hl₂ h₂
  have e : (T.map (Int.cast : ℤ → ℚ) + c.C).map (Rat.cast : ℚ → ℝ) =
      T.map (Int.cast : ℤ → ℝ) + c.C.map (Rat.cast : ℚ → ℝ) := by
    ext i j
    simp
  rw [e] at hTC
  have h := frobeniusInner_weightedSign_le_of_certificate (c := 2 / 3) (fun i ↦ by simp [hT i])
    hC hTC (fun j ↦ by simpa using (Rat.cast_le (K := ℝ)).mpr (hd j)) hw hP
  linarith

end ProjectionConstants.FourSix
