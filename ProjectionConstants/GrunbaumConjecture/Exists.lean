/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.GrunbaumConjecture.Cloning
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Existence of maximizers

For a nonempty finite index type `ι`, the function `w ↦ kyFanSum 2 (√D S √D)` is continuous
(`continuous_kyFanSum_weightedSign`), the weights form a compact set (`isCompact_setOf_isWeight`)
and there are finitely many sign matrices (`finite_setOf_isSignMatrix`). Hence
`kyFanSum 2 (√D S √D)` attains its maximum over all pairs `(S, w)` of a sign matrix and a weight.
The proof of [JFA-E, Theorem A] in `ProjectionConstants.GrunbaumConjecture.Reduction` starts
from such a maximizer.

## Main statements

* `exists_isMaximizer`: there is a maximizer `(S, w)` (see `IsMaximizer`).

## References

* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Finset Matrix

namespace ProjectionConstants.GrunbaumConjecture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Existence of maximizers**: some sign matrix `S` and weight `w` maximize
`kyFanSum 2 (√D S √D)`. -/
theorem exists_isMaximizer [Nonempty ι] : ∃ (S : Matrix ι ι ℝ) (w : ι → ℝ), IsMaximizer S w := by
  -- for each sign matrix, maximize over the weights
  have hmaxw : ∀ S : Matrix ι ι ℝ, ∃ w, IsWeight w ∧
      ∀ w', IsWeight w' → kyFanSum 2 (weightedSign S w') ≤ kyFanSum 2 (weightedSign S w) := by
    intro S
    obtain ⟨w, hw, hmax⟩ := isCompact_setOf_isWeight.exists_isMaxOn nonempty_setOf_isWeight
      (continuous_kyFanSum_weightedSign 2 S).continuousOn
    exact ⟨w, hw, fun w' hw' ↦ hmax hw'⟩
  choose W hW hWmax using hmaxw
  -- maximize over the finitely many sign matrices
  have hne : {S : Matrix ι ι ℝ | IsSignMatrix S}.Nonempty :=
    ⟨Matrix.of fun _ _ ↦ 1, fun _ _ ↦ rfl, fun _ _ ↦ Or.inl rfl, fun _ ↦ rfl⟩
  obtain ⟨S, hS, hSmax⟩ := Set.exists_max_image _ (fun S ↦ kyFanSum 2 (weightedSign S (W S)))
    finite_setOf_isSignMatrix hne
  refine ⟨S, W S, hS, hW S, fun S' w' hS' hw' ↦ ?_⟩
  exact (hWmax S' w' hw').trans (hSmax S' hS')

end ProjectionConstants.GrunbaumConjecture
