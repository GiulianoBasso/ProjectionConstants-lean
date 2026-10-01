/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.Injective
import ProjectionConstants.ChalmersLewicki.LowerBound
import Mathlib.LinearAlgebra.Matrix.Circulant

/-!
# Circulant projections are minimal

Let `G` be a finite abelian group. A matrix indexed by `G` is *circulant* if it has the form
`circulant v = (v (g - h))_{g, h}` for some `v : G → 𝕜`; these are exactly the operators on
`ℓ∞(G)` that commute with the translations of `G`. We show that an idempotent circulant matrix
`P = circulant v` is a minimal projection onto its range `Y ⊆ ℓ∞(G)`, and that

  `λ(Y) = λ(Y, ℓ∞(G)) = ‖P‖ = ∑_g |v g|`.

The upper bound is the maximal row sum of `P` (every row of `P` is a permutation of `v`). For the
lower bound we use trace duality in `ℓ∞` (`re_trace_le_relProjConst`) with the circulant matrix
`A = circulant w`, `w g = sgn(v (-g))‾ / |G|`: its columns are bounded by `1 / |G|`, it commutes
with `P` because circulant matrices commute, and `Re tr(A P) = ∑_g |v g|`. The absolute projection
constant equals the relative one because `ℓ∞(G)` has the extension property
(`absProjConst_eq_relProjConst_pi`).

This is the mechanism behind Grünbaum's computations [G] of the projection constants of `ℓ₁ⁿ`
(`G = (ℤ/2)ⁿ`, `ProjectionConstants.Invariant.L1`) and of the planes whose unit ball is a regular
polygon (`G = ℤ/2N`, `ProjectionConstants.Invariant.Polygon`), and a special case of Rudin's
averaging principle for translation-invariant subspaces.

## Main statements

* `rowSumNorm_circulant`: the norm of `circulant v` on `ℓ∞(G)` is `∑_g |v g|`.
* `relProjConst_range_circulant`: `λ(range P, ℓ∞(G)) = ∑_g |v g|` for an idempotent circulant
  matrix `P = circulant v`.
* `absProjConst_range_circulant`: `λ(range P) = ∑_g |v g|`.
* `absProjConst_eq_sum_norm_of_range_eq`: `λ(Y) = ∑_g |v g|` for every normed space `Y` that is
  isometric to `range P`.

## References

* [G] B. Grünbaum, *Projection constants*, Trans. Amer. Math. Soc. 95 (1960), 451–465.
* W. Rudin, *Projections on invariant subspaces*, Proc. Amer. Math. Soc. 13 (1962), 429–432.

## Tags

projection constant, circulant matrix, group matrix, minimal projection, trace duality
-/

open Matrix Finset

namespace ProjectionConstants

universe u

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [AddCommGroup G] [Fintype G]

/-- Every row of `circulant v` is a permutation of `v`, so the norm of `circulant v` on `ℓ∞(G)`
is `∑_g |v g|`. -/
theorem rowSumNorm_circulant (v : G → 𝕜) : rowSumNorm (circulant v) = ∑ g, ‖v g‖ := by
  have hrow : ∀ g, ∑ h, ‖circulant v g h‖ = ∑ h, ‖v h‖ := fun g ↦ by
    simp only [circulant_apply]
    exact Fintype.sum_equiv (Equiv.subLeft g) _ _ fun h ↦ rfl
  refine le_antisymm (rowSumNorm_le (sum_nonneg fun _ _ ↦ norm_nonneg _) fun g ↦ (hrow g).le) ?_
  rw [← hrow 0]
  exact row_le_rowSumNorm _ 0

/-- `Re tr(circulant w * circulant v) = ∑_g |v g|` for `w g = sgn(v (-g))‾ / |G|`. -/
private lemma re_trace_circulant_phase (v : G → 𝕜) :
    RCLike.re (circulant (fun g ↦ star (phase (v (-g))) / (Fintype.card G : 𝕜)) *
      circulant v).trace = ∑ g, ‖v g‖ := by
  have hstar : ∀ z : 𝕜, star (phase z) * z = (‖z‖ : 𝕜) := fun z ↦ by
    have h := congrArg star (phase_mul_star z)
    rwa [star_mul, star_star, mul_comm, RCLike.star_def, RCLike.conj_ofReal] at h
  have hterm : ∀ i j : G, star (phase (v (-(j - i)))) / (Fintype.card G : 𝕜) * v (i - j) =
      ((‖v (i - j)‖ / Fintype.card G : ℝ) : 𝕜) := fun i j ↦ by
    rw [neg_sub, div_mul_eq_mul_div, hstar]
    push_cast
    ring
  have hrow : ∀ j : G, ∑ i, ‖v (i - j)‖ = ∑ g, ‖v g‖ := fun j ↦
    Fintype.sum_equiv (Equiv.subRight j) _ _ fun _ ↦ rfl
  have hG : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, circulant_apply, hterm,
    ← RCLike.ofReal_sum, RCLike.ofReal_re, ← Finset.sum_div, hrow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp

variable [DecidableEq G]

/-- **Idempotent circulant matrices are minimal projections**: if `P = circulant v` is idempotent,
then `λ(range P, ℓ∞(G)) = ‖P‖ = ∑_g |v g|`. -/
theorem relProjConst_range_circulant {v : G → 𝕜} (hv : circulant v * circulant v = circulant v) :
    relProjConst (LinearMap.range (circulant v).toLin') = ∑ g, ‖v g‖ := by
  refine le_antisymm ((relProjConst_le_rowSumNorm _ (isMatrixProjOnto_range hv)).trans
    (rowSumNorm_circulant v).le) ?_
  -- trace duality with `A = circulant w`, `w g = sgn(v (-g))‾ / |G|`
  have hG : (0 : ℝ) < Fintype.card G := Nat.cast_pos.2 Fintype.card_pos
  have h := re_trace_le_relProjConst hv
    (circulant_mul_comm (fun g ↦ star (phase (v (-g))) / (Fintype.card G : 𝕜)) v)
    (α := fun _ ↦ 1 / Fintype.card G) (fun i j ↦ ?_) ?_
  · rwa [re_trace_circulant_phase] at h
  · rw [circulant_apply, norm_div, RCLike.norm_natCast, norm_star]
    gcongr
    exact norm_phase_le _
  · simp [Finset.card_univ, hG.ne']

/-- **Idempotent circulant matrices are minimal projections**: if `P = circulant v` is idempotent,
then `λ(range P) = ∑_g |v g|`. -/
theorem absProjConst_range_circulant {v : G → 𝕜} (hv : circulant v * circulant v = circulant v) :
    absProjConst 𝕜 (LinearMap.range (circulant v).toLin') = ∑ g, ‖v g‖ := by
  rw [absProjConst_eq_relProjConst_pi, relProjConst_range_circulant hv]

/-! ### Spans of orthogonal families -/

section Orthogonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix G ι 𝕜} {c : 𝕜} {v : G → 𝕜}

omit [DecidableEq G] in
/-- If `Mᴴ M = c • 1` with `c ≠ 0` and `circulant v = c⁻¹ • M Mᴴ` (the orthogonal projection onto
the span of the columns of `M`), then `circulant v` is idempotent. -/
theorem circulant_mul_self_of_conjTranspose_mul_self (hc : c ≠ 0) (hM : Mᴴ * M = c • 1)
    (hv : circulant v = c⁻¹ • (M * Mᴴ)) : circulant v * circulant v = circulant v := by
  rw [hv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ,
    hM, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul]
  congr 1
  field_simp

/-- If `Mᴴ M = c • 1` with `c ≠ 0` and `circulant v = c⁻¹ • M Mᴴ`, then `circulant v` and `M` have
the same range. -/
theorem range_circulant_of_conjTranspose_mul_self (hc : c ≠ 0) (hM : Mᴴ * M = c • 1)
    (hv : circulant v = c⁻¹ • (M * Mᴴ)) :
    LinearMap.range (circulant v).toLin' = LinearMap.range M.toLin' := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    refine ⟨c⁻¹ • (Mᴴ *ᵥ w), ?_⟩
    simp [hv, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
  · rintro _ ⟨x, rfl⟩
    have hvM : circulant v * M = M := by
      rw [hv, Matrix.smul_mul, Matrix.mul_assoc, hM, Matrix.mul_smul, Matrix.mul_one, smul_smul,
        inv_mul_cancel₀ hc, one_smul]
    refine ⟨M *ᵥ x, ?_⟩
    simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hvM]

omit [DecidableEq G] in
/-- **Projection constants of spans of orthogonal families.** Let the columns of `M : G × ι` be
orthogonal of equal length, `Mᴴ M = c • 1` with `c ≠ 0`, and suppose that the orthogonal
projection `c⁻¹ • M Mᴴ` onto their span is circulant, `= circulant v`. Then the span `Y ⊆ ℓ∞(G)`
of the columns of `M` has `λ(Y) = ∑_g |v g|`. -/
theorem absProjConst_range_eq_sum_norm (hc : c ≠ 0) (hM : Mᴴ * M = c • 1)
    (hv : circulant v = c⁻¹ • (M * Mᴴ)) :
    absProjConst 𝕜 (LinearMap.range M.toLin') = ∑ g, ‖v g‖ := by
  classical
  rw [← range_circulant_of_conjTranspose_mul_self hc hM hv,
    absProjConst_range_circulant (circulant_mul_self_of_conjTranspose_mul_self hc hM hv)]

omit [AddCommGroup G] [DecidableEq G] in
/-- If `Mᴴ M = c • 1` with `c ≠ 0`, then `M` is injective. -/
theorem injective_toLin'_of_conjTranspose_mul_self (hc : c ≠ 0) (hM : Mᴴ * M = c • 1) :
    Function.Injective M.toLin' := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h : Mᴴ *ᵥ (M *ᵥ x) = c • x := by
    rw [Matrix.mulVec_mulVec, hM, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hx' : M *ᵥ x = 0 := by simpa [Matrix.toLin'_apply] using hx
  rw [hx', Matrix.mulVec_zero] at h
  exact (smul_eq_zero.1 h.symm).resolve_left hc

end Orthogonal

/-- If a normed space `Y` is isometric to the range of an idempotent circulant matrix
`circulant v`, then `λ(Y) = ∑_g |v g|`. -/
theorem absProjConst_eq_sum_norm_of_range_eq {𝕜 : Type} [RCLike 𝕜] {G : Type u} [AddCommGroup G]
    [Fintype G] [DecidableEq G] {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y] (E : Y →ₗᵢ[𝕜] (G → 𝕜)) {v : G → 𝕜}
    (hv : circulant v * circulant v = circulant v)
    (hE : LinearMap.range E.toLinearMap = LinearMap.range (circulant v).toLin') :
    absProjConst 𝕜 Y = ∑ g, ‖v g‖ := by
  rw [(hasExtensionProperty_pi G).absProjConst_eq_of_linearIsometry E, hE,
    relProjConst_range_circulant hv]

end ProjectionConstants
