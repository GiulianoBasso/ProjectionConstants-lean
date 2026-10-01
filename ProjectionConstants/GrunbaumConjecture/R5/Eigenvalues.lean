/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.GrunbaumConjecture.R5.Charpoly
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Real.Sqrt

/-!
# The eigenvalues of `√D R₅ √D`

For `s ∈ ℝ⁵` with `∑ sᵢ² = 1`, any two eigenvalues of the symmetric matrix
`scaledR5 s = diag(s) R₅ diag(s)` sum to at most `4/3`, strictly if all `sᵢ ≠ 0`
(`eigenvalues_add_le_four_thirds`). With `sᵢ = √wᵢ`, this gives the upper bound of
[JFA-E, Proposition F]: `kyFanSum 2 (√D R₅ √D) ≤ 4/3` for all weights, with strict inequality if
all weights are positive. These statements with Ky Fan sums, and the fact that `4/3` is attained,
are `kyFanSum_two_weightedSign_R5_le`, `kyFanSum_two_weightedSign_R5_lt` and
`isGreatest_kyFanSum_two_weightedSign_R5` in `ProjectionConstants.GrunbaumConjecture.Main`.

The eigenvalues are Mathlib's `Matrix.IsHermitian.eigenvalues`. The characteristic polynomial
splits as `∏ (X - λᵢ)` (`Matrix.IsHermitian.charpoly_eq`), so `root_add_root_le_of_charpoly`
applies.

## Main statements

* `isHermitian_scaledR5`: `scaledR5 s` is symmetric.
* `eigenvalues_add_le_four_thirds`: any two eigenvalues of `scaledR5 s` sum to at most `4/3`.

## References

* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Matrix
open Polynomial (X C)

namespace ProjectionConstants.GrunbaumConjecture

/-- `scaledR5 s = diag(s) R₅ diag(s)` is symmetric. -/
theorem isHermitian_scaledR5 (s : Fin 5 → ℝ) : (scaledR5 s).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [scaledR5, Matrix.of_apply, star_trivial]
  fin_cases i <;> fin_cases j <;> simp [R5] <;> ring

/-- `eigenvalues` is `eigenvalues₀` up to a relabelling of the indices. -/
private theorem exists_equiv {s : Fin 5 → ℝ} (hA : (scaledR5 s).IsHermitian) :
    ∃ E : Fin (Fintype.card (Fin 5)) ≃ Fin 5,
      ∀ i, hA.eigenvalues i = hA.eigenvalues₀ (E.symm i) :=
  ⟨Fintype.equivOfCardEq (Fintype.card_fin _), fun _ ↦ rfl⟩

/-- Any two eigenvalues of `scaledR5 s` sum to at most `4/3` if `∑ sᵢ² = 1`,
strictly if all `sᵢ ≠ 0`. -/
theorem eigenvalues_add_le_four_thirds {s : Fin 5 → ℝ} (hA : (scaledR5 s).IsHermitian)
    (hs : ∑ i, s i ^ 2 = 1) (i j : Fin 5) (hij : i ≠ j) :
    hA.eigenvalues i + hA.eigenvalues j ≤ 4/3 ∧
      ((∀ k, s k ≠ 0) → hA.eigenvalues i + hA.eigenvalues j < 4/3) := by
  have hc : (scaledR5 s).charpoly = ∏ k, (X - C (hA.eigenvalues k)) := by
    rw [hA.charpoly_eq]
    simp
  exact root_add_root_le_of_charpoly s _ hs hc i j hij

end ProjectionConstants.GrunbaumConjecture
