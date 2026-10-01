/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
-- General lemmas
import ProjectionConstants.ForMathlib.BigOperators
import ProjectionConstants.ForMathlib.Real
import ProjectionConstants.ForMathlib.Matrix.DotProduct
import ProjectionConstants.ForMathlib.Matrix.RankTrace
import ProjectionConstants.ForMathlib.Matrix.StarProjection
-- Projection constants of normed spaces
import ProjectionConstants.Basic
import ProjectionConstants.Injective
import ProjectionConstants.Linfty
import ProjectionConstants.L1
import ProjectionConstants.Reduction
-- Matrices: orthogonal projections, sign matrices, Ky Fan sums
import ProjectionConstants.Matrix.OrthProj
import ProjectionConstants.Matrix.Commute
import ProjectionConstants.Matrix.HermCoords
import ProjectionConstants.Matrix.SignMatrix
import ProjectionConstants.Matrix.KyFan.Basic
import ProjectionConstants.Matrix.KyFan.Fan
import ProjectionConstants.Matrix.KyFan.Stationary
-- The formula of Chalmers and Lewicki
import ProjectionConstants.ChalmersLewicki.Defs
import ProjectionConstants.ChalmersLewicki.UpperBound
import ProjectionConstants.ChalmersLewicki.LowerBound
import ProjectionConstants.ChalmersLewicki.Formula
import ProjectionConstants.ChalmersLewicki.Absolute
import ProjectionConstants.ChalmersLewicki.SignMatrix
-- Quasimaximal projection constants
import ProjectionConstants.Quasimaximal
-- Invariant subspaces: Rudin's averaging theorem, circulant projections, `ℓ₁ⁿ`, regular polygons
import ProjectionConstants.Invariant.Rudin
import ProjectionConstants.Invariant.Circulant
import ProjectionConstants.Invariant.L1
import ProjectionConstants.Invariant.Polygon
-- The circle: trigonometric polynomials, Lebesgue constants and the disc algebra
import ProjectionConstants.Fourier.Trigonometric
import ProjectionConstants.Fourier.Lebesgue
import ProjectionConstants.Fourier.DiscAlgebra
-- Equiangular tight frames
import ProjectionConstants.ETF.Basic
import ProjectionConstants.ETF.Certificate
import ProjectionConstants.ETF.Maximal.Certificates
import ProjectionConstants.ETF.Maximal.Seidel
-- Upper bounds
import ProjectionConstants.Bounds.KLL
import ProjectionConstants.Bounds.KLLEquality
import ProjectionConstants.Bounds.BukhCox
import ProjectionConstants.Bounds.Gerzon
import ProjectionConstants.Bounds.Welch
import ProjectionConstants.Bounds.FrameBound
-- Explicit values
import ProjectionConstants.Values
-- Grünbaum's conjecture `λ_ℝ(2) = 4/3` via sign matrices
import ProjectionConstants.GrunbaumConjecture.SignPattern
import ProjectionConstants.GrunbaumConjecture.Transfer
import ProjectionConstants.GrunbaumConjecture.Cloning
import ProjectionConstants.GrunbaumConjecture.Merge
import ProjectionConstants.GrunbaumConjecture.Exists
import ProjectionConstants.GrunbaumConjecture.A6
import ProjectionConstants.GrunbaumConjecture.TwoGraph
import ProjectionConstants.GrunbaumConjecture.Embed
import ProjectionConstants.GrunbaumConjecture.R5.Charpoly
import ProjectionConstants.GrunbaumConjecture.R5.Eigenvalues
import ProjectionConstants.GrunbaumConjecture.Classify
import ProjectionConstants.GrunbaumConjecture.Reduction
import ProjectionConstants.GrunbaumConjecture.Main
-- Four-dimensional subspaces of `ℓ∞⁶`
import ProjectionConstants.FourSix.Certificate
import ProjectionConstants.FourSix.Errata
import ProjectionConstants.FourSix.Classification
import ProjectionConstants.FourSix.Main
-- Almost minimal orthogonal projections and monotonicity
import ProjectionConstants.AlmostMinimal.Config
import ProjectionConstants.AlmostMinimal.Stationary
import ProjectionConstants.AlmostMinimal.Estimates
import ProjectionConstants.AlmostMinimal.L1
import ProjectionConstants.AlmostMinimal.Blowup
import ProjectionConstants.AlmostMinimal.Main
import ProjectionConstants.AlmostMinimal.Mono
-- Stabilization of the maximal relative projection constants
import ProjectionConstants.Stabilization.Caratheodory
import ProjectionConstants.Stabilization.Maximizer
import ProjectionConstants.Stabilization.Reweight
import ProjectionConstants.Stabilization.Main
-- Euclidean spaces
import ProjectionConstants.Euclidean.Sphere
import ProjectionConstants.Euclidean.LowerBound
import ProjectionConstants.Euclidean.UpperBound
import ProjectionConstants.Euclidean.Formula
import ProjectionConstants.Euclidean.Polar
import ProjectionConstants.Euclidean.Values
-- Complementary dimensions
import ProjectionConstants.Complementary.Complement
import ProjectionConstants.Complementary.Main
-- Summary
import ProjectionConstants.MainResults

/-!
# Projection constants

A library on projection constants of finite-dimensional normed spaces. The main theorems are
restated in elementary terms in `ProjectionConstants.MainResults`.

* `ForMathlib/`: general lemmas that do not depend on the rest of the library (sums, real
  inequalities, dot products, star projections of matrices, `(Tr A)² ≤ rank A · ∑ᵢⱼ Aᵢⱼ²`).
* `Basic`, `Injective`, `Linfty`, `L1`, `Reduction`: relative, absolute and maximal projection
  constants; the extension property of `ℓ∞`, isometric invariance and the Banach–Mazur estimate of
  Grünbaum; the reduction of maximal projection constants to subspaces of `ℓ∞^N`; matrix
  projections on `ℓ∞^N` and on `ℓ₁^N`.
* `Matrix/`: orthogonal projection matrices and Parseval frames, a commutation lemma for
  maximizers on the Grassmannian, coordinates on Hermitian matrices, sign matrices, and Ky Fan's
  maximum principle.
* `ChalmersLewicki/`: the formula of Chalmers and Lewicki for maximal relative projection
  constants, the bound `λ(Y) ≤ √m` of Kadec and Snobar, and the formula in terms of sign
  matrices.
* `Quasimaximal`: quasimaximal projection constants and `λ_𝕜(m) = μ_𝕜(m)`.
* `Invariant/`: Rudin's averaging theorem for compact groups and Rudin's principle (a unique
  equivariant projection is minimal); idempotent circulant matrices are minimal projections;
  Grünbaum's projection constants of `ℓ₁ⁿ` and of the planes whose unit ball is a regular polygon.
* `Fourier/`: the circle `𝕋`: the theorem of Lozinskiĭ and Kharshiladze `λ(𝒯ₙ, C(𝕋)) = Lₙ`, the
  growth of the Lebesgue constants and its consequences (Kharshiladze–Lozinskiĭ, du Bois-Reymond),
  and Rudin's theorem on complemented translation-invariant subspaces of `C(𝕋)`, in particular
  that the disc algebra is not complemented.
* `ETF/`: equiangular tight frames, a kernel-checked certificate format for real ETFs, and
  explicit maximal ETFs in `ℝ²`, `ℝ³`, `ℝ⁷`, `ℝ²³`, `ℂ²` and `ℂ³`.
* `Bounds/`: the bound of König, Lewis and Lin and its equality case, the bound of Bukh and Cox,
  the upper bounds at the Gerzon bounds, the recursive Sidelnikov–Welch inequality and a frame
  bound.
* `Values`: explicit values of maximal projection constants.
* `GrunbaumConjecture/`: a second proof of Grünbaum's conjecture `λ_ℝ(2) = 4/3`, via sign
  matrices, two-graphs and the characteristic polynomial of a weighted pentagon.
* `FourSix/`: `λ_ℝ(4, 6) = λ_ℝ(5, 6) = 5/3`, with sums-of-squares certificates.
* `AlmostMinimal/`: almost minimal orthogonal projections and the (folklore) strict monotonicity of
  `λ_ℝ(n)`.
* `Stabilization/`: `λ_ℝ(r, n) = λ_ℝ(r)` for `n ≥ 2^r C(r+1, 2)`.
* `Euclidean/`: the projection constants of `ℓ₂ⁿ(ℝ)` and `ℓ₂ⁿ(ℂ)` (Grünbaum, Rutovitz), and
  `λ(ℓ₂²ᵐ⁺¹(ℝ)) = λ(ℓ₁²ᵐ⁺¹)`.
* `Complementary/`: maximal relative projection constants in complementary dimensions.
-/
