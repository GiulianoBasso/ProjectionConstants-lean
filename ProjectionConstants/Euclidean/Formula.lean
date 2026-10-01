/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Euclidean.LowerBound
import ProjectionConstants.Euclidean.UpperBound

/-!
# The projection constant of Euclidean space as a spherical mean

Let `E = 𝕜ⁿ` with the Euclidean norm (`𝕜 = ℝ` or `ℂ`), let `ν ≠ 0` be a finite measure on the
unit sphere `S` of `E` that is invariant under all linear isometries, and let `e ∈ S`. Then
`λ(E) = n ∫ |⟪u, e⟫| dν(u) / ν(S)`. The lower bound is `Euclidean.le_absProjConst`
(`ProjectionConstants.Euclidean.LowerBound`) and the upper bound is `Euclidean.absProjConst_le`
(`ProjectionConstants.Euclidean.UpperBound`). The formula is evaluated explicitly in
`ProjectionConstants.Euclidean.Values`.

This spherical-mean formula underlies the computations of Grünbaum [G] (real case) and
Rutovitz [R] (complex case); see [DGMMM, §1] for the formula in this form.

## Main statements

* `absProjConst_euclideanSpace_eq`: `λ(𝕜ⁿ) = n ∫ |⟪u, e⟫| dν(u) / ν(S)`.

## References

* [G] B. Grünbaum, *Projection constants*, Trans. Amer. Math. Soc. 95 (1960).
* [R] D. Rutovitz, *Some parameters associated with finite-dimensional Banach spaces*,
  J. London Math. Soc. 40 (1965).
* [DGMMM] A. Defant, D. Galicer, M. Mansilla, M. Mastyło, S. Muro, *Projection constants for
  spaces of multivariate polynomials*, arXiv:2208.06467.

## Tags

projection constant, Euclidean space, invariant measure
-/

open MeasureTheory Metric
open scoped InnerProductSpace

namespace ProjectionConstants

open Euclidean

variable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] {n : ℕ} [NeZero n]
  {ν : Measure (sphere (0 : EuclideanSpace 𝕜 (Fin n)) 1)} [IsFiniteMeasure ν]

/-- **The projection constant of `𝕜ⁿ` as a spherical mean** ([G], [R]; see [DGMMM, §1]):
`λ(𝕜ⁿ) = n ∫ |⟪u, e⟫| dν(u) / ν(S)` for every invariant finite measure `ν ≠ 0` on the unit
sphere and every unit vector `e`. -/
theorem absProjConst_euclideanSpace_eq (hν : IsInvariant 𝕜 ν) (hν0 : ν ≠ 0)
    {e : EuclideanSpace 𝕜 (Fin n)} (he : ‖e‖ = 1) :
    absProjConst 𝕜 (EuclideanSpace 𝕜 (Fin n)) =
      n * (∫ u, ‖⟪(u : EuclideanSpace 𝕜 (Fin n)), e⟫_𝕜‖ ∂ν) / ν.real Set.univ := by
  refine le_antisymm (absProjConst_le hν hν0 he) ?_
  have h := le_absProjConst hν hν0 he
  rwa [finrank_euclideanSpace_fin] at h

end ProjectionConstants
