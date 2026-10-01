/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.FourSix.Classification
import ProjectionConstants.ChalmersLewicki.SignMatrix

/-!
# The maximal relative projection constant `Π(4, 6) = 5/3`

Write `Π(n, d)` for the maximal relative projection constant of [JFA]; in Lean it is
`maxRelProjConst ℝ n d`, also written `λ_ℝ(n, d)`. We prove the result of [JFA, §4.4]: the
maximal relative projection constant of four-dimensional subspaces of `ℓ∞⁶` is
`Π(4, 6) = λ_ℝ(4, 6) = sup { λ(Y, ℓ∞⁶) : Y ⊆ ℓ∞⁶, dim Y = 4 } = 5/3`
(`maxRelProjConst_four_six`). As a by-product, we also get `Π(5, 6) = 5/3`
(`maxRelProjConst_five_six`).

Below, `𝒮₆` is the set of `6 × 6` sign matrices (`IsSignMatrix`), `𝒟₆` is the set of weights
`D = diag(w)` (`IsWeight w`), `√D A √D` is `weightedSign A w`, `Tr(AP)` is `frobeniusInner A P`,
and the Ky Fan sum `kyFanSum n A` is the sum of the `n` largest eigenvalues of a symmetric
matrix `A`.

## The proof in [JFA] and its erratum [JFA-E]

1. By the formula of Chalmers and Lewicki ([JFA, Theorem 2.1]),
   `Π(4, 6) = max { kyFanSum 4 (√D A √D) : A ∈ 𝒮₆, D ∈ 𝒟₆ }`.
2. Since `Π(3, 6) < 5/3` and `Π(5, 6) ≤ 5/3` ([JFA-E, item 9]), only sign matrices `A` of
   signature `(4, 2)` matter. By the classification of two-graphs on six vertices
   (Bussemaker–Mathon–Seidel), such an `A` is, up to switching and permutations, one of
   `A1, A2, A3`, and `Π(4, 6) = max(M₁, M₂, M₃)` for `Mᵢ = max_D kyFanSum 4 (√D Aᵢ √D)`.
3. `M₁ ≤ 5/3` by the new argument of [JFA-E, item 4]:
   `kyFanSum 4 (√D A1 √D) ≤ Tr(√D (A1 + C) √D)` for an explicit positive semidefinite `C` with
   diagonal `2/3` and `A1 + C ⪰ 0`.
4. `M₂ ≤ 5/3` by the concavity in `D` of the sum of the four largest eigenvalues of `A2 D`
   (Lieb–Siedentop), a symmetrization ([JFA, Lemma 4.4]), an estimate for the roots of a cubic
   ([JFA, Lemma 4.5]) and Lagrange multipliers.
5. `M₃ = 5/3` by the symmetrization and the spectrum `4, 2, 2, 2, -2, -2` of `A3`.

## The formalization

The auxiliary results are in the namespace `ProjectionConstants.FourSix`, the main theorems in
`ProjectionConstants`.

* Step 1 is `kyFanSum_weightedSign_le_maxRelProjConst` and `maxRelProjConst_real_le`
  (`ProjectionConstants.ChalmersLewicki.SignMatrix`), derived from the formula of Chalmers and
  Lewicki in the form `maxRelProjConst_eq_clConst` ([DL, Theorem 1.1]).
* Step 3 is `kyFanSum_four_weightedSign_A1_le`, with the vectors, the matrix `C` and the pivots
  of `A1 + C` of [JFA-E, item 4].
* Step 5 is `isGreatest_kyFanSum_four_weightedSign_A3`. The lower bound is
  `kyFanSum 4 (A3/6) = 5/3`; for the upper bound we use the argument of step 3 with
  `C = I + K - J/3` instead of the symmetrization.
* Step 4 is `kyFanSum_four_weightedSign_A2_le`, also by the argument of step 3, with a rational
  `C`. The calculus of the paper is not formalized.
* Step 2 is replaced by `frobeniusInner_weightedSign_le_five_thirds`: all sixteen two-graphs on
  six vertices are treated, the three of signature `(4, 2)` by `M₁`, `M₂`, `M₃` and the others by
  the argument of step 3. The classification is checked by the kernel
  (`ProjectionConstants.FourSix.Classification`).

The argument of step 3 bounds `Tr(√D A √D P)` for every orthogonal projection `P`, whatever its
rank. So it also gives `Π(5, 6) ≤ 5/3`, and `A = 2I - J` (`simplexSign`) with the projection
onto the complement of `(1, …, 1)` (`simplexProj`) shows `Π(5, 6) = 5/3`.

## Main definitions

* `simplexSign`: the sign matrix `2I - J`.
* `simplexProj`: the orthogonal projection `I - J/6` onto the complement of `(1, …, 1)`.

## Main statements

* `isGreatest_kyFanSum_four_weightedSign_six`: the maximum of `kyFanSum 4 (√D S √D)` over
  `S ∈ 𝒮₆` and `D ∈ 𝒟₆` is `5/3`.
* `maxRelProjConst_four_six`: `Π(4, 6) = λ_ℝ(4, 6) = 5/3`.
* `maxRelProjConst_five_six`: `Π(5, 6) = λ_ℝ(5, 6) = 5/3`.

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
* [JFA] G. Basso, *Computation of maximal projection constants*, J. Funct. Anal. 277 (2019),
  arXiv:1901.07866.
* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Finset Matrix

namespace ProjectionConstants.FourSix

/-- The sign matrix `2I - J`. -/
def simplexSign : Matrix (Fin 6) (Fin 6) ℤ := of fun i j ↦ if i = j then 1 else -1

/-- The orthogonal projection `I - J/6` onto the complement of `(1, …, 1)`. -/
def simplexProj : Matrix (Fin 6) (Fin 6) ℚ := of fun i j ↦ (if i = j then 1 else 0) - 1 / 6

end ProjectionConstants.FourSix

namespace ProjectionConstants

open FourSix

/-- **`max { kyFanSum 4 (√D S √D) : S ∈ 𝒮₆, D ∈ 𝒟₆ } = 5/3`**, attained at `A3` and `D = I/6`. -/
theorem isGreatest_kyFanSum_four_weightedSign_six :
    IsGreatest {x | ∃ (S : Matrix (Fin 6) (Fin 6) ℝ) (w : Fin 6 → ℝ),
      IsSignMatrix S ∧ IsWeight w ∧ kyFanSum 4 (weightedSign S w) = x} (5 / 3) :=
  ⟨⟨A3, _, isSignMatrix_A3, isWeight_const_sixth, kyFanSum_four_weightedSign_A3_const_sixth⟩, by
    rintro _ ⟨S, w, hS, hw, rfl⟩
    exact kyFanSum_le (by norm_num) fun P hP ↦
      frobeniusInner_weightedSign_le_five_thirds hS hw hP.1⟩

/-- **`Π(4, 6) = 5/3`** ([JFA, §4.4], with the corrected argument of [JFA-E]): the maximal
relative projection constant of four-dimensional subspaces of `ℓ∞⁶` is `5/3`. -/
theorem maxRelProjConst_four_six : maxRelProjConst ℝ 4 6 = 5 / 3 := by
  refine le_antisymm (maxRelProjConst_real_le (by norm_num) fun S w hS hw ↦
    kyFanSum_le (by norm_num) fun P hP ↦ frobeniusInner_weightedSign_le_five_thirds hS hw hP.1) ?_
  calc (5 / 3 : ℝ) = kyFanSum 4 (weightedSign A3 fun _ ↦ 1 / 6) :=
        kyFanSum_four_weightedSign_A3_const_sixth.symm
    _ ≤ maxRelProjConst ℝ 4 6 :=
      kyFanSum_weightedSign_le_maxRelProjConst isSignMatrix_A3 isWeight_const_sixth

/-- **`Π(5, 6) = 5/3`**: the certificates bound all ranks at once (see [JFA-E, item 9]). -/
theorem maxRelProjConst_five_six : maxRelProjConst ℝ 5 6 = 5 / 3 := by
  refine le_antisymm (maxRelProjConst_real_le (by norm_num) fun S w hS hw ↦
    kyFanSum_le (by norm_num) fun P hP ↦ frobeniusInner_weightedSign_le_five_thirds hS hw hP.1) ?_
  have hS : IsSignMatrix (simplexSign.map (Int.cast : ℤ → ℝ)) :=
    isSignMatrix_map_intCast (by decide) (by decide) (by decide)
  have hP : simplexProj.map (Rat.cast : ℚ → ℝ) ∈ orthProjs ℝ (Fin 6) 5 :=
    map_ratCast_mem_orthProjs (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h : (∑ i, ∑ j, (simplexSign i j : ℚ) * simplexProj i j : ℚ) = 10 := by decide +kernel
  calc (5 / 3 : ℝ)
      = frobeniusInner (weightedSign (simplexSign.map (Int.cast : ℤ → ℝ)) fun _ ↦ 1 / 6)
          (simplexProj.map (Rat.cast : ℚ → ℝ)) := by
        rw [frobeniusInner_weightedSign_const_sixth, h]
        norm_num
    _ ≤ kyFanSum 5 (weightedSign (simplexSign.map (Int.cast : ℤ → ℝ)) fun _ ↦ 1 / 6) :=
      frobeniusInner_le_kyFanSum _ hP
    _ ≤ maxRelProjConst ℝ 5 6 := kyFanSum_weightedSign_le_maxRelProjConst hS isWeight_const_sixth

end ProjectionConstants
