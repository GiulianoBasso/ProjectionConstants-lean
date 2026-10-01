/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.GrunbaumConjecture.TwoGraph
import ProjectionConstants.GrunbaumConjecture.R5.Charpoly

/-!
# The `5 × 5` principal submatrices of `A₆`

Every `5 × 5` principal submatrix of `A₆` is, up to switching and relabelling, the matrix
`R₅ = J - 2E` of `ProjectionConstants.GrunbaumConjecture.R5.Charpoly` ([JFA-E, (A1)]). The
relabellings `relabelA6` and the switching signs `switchA6` are given explicitly, and the identities
are checked by computation (`A6_eq_switch_R5`). This is used in Step 4 of the proof of
[JFA-E, Theorem A] in `ProjectionConstants.GrunbaumConjecture.Reduction`. We also show that `J₃` is,
up to switching, the principal submatrix of `R₅` on `{0, 1, 2}` (`switch_R5_012`); this is used
there for sign matrices of order `3`.

## Main definitions

* `relabelA6 k`: a map `Fin 6 → Fin 5` that is injective on the indices `≠ k`.
* `switchA6 k`: the switching signs.

## Main statements

* `A6_eq_switch_R5`: `A₆ i j = εᵢ εⱼ R₅ (φ i) (φ j)` for `i, j ≠ k`, where `φ = relabelA6 k` and
  `ε = switchA6 k` ([JFA-E, (A1)]).
* `relabelA6_injective`: `relabelA6 k` is injective on the indices `≠ k`.
* `isSignMatrix_R5`: `R₅` is a sign matrix.
* `switch_R5_012`: `J₃` is the principal submatrix of `R₅` on `{0, 1, 2}`, up to switching.

## References

* [JFA-E] G. Basso, *Erratum to "Computation of maximal projection constants"*,
  arXiv:2402.06672.
-/

open Matrix

namespace ProjectionConstants.GrunbaumConjecture

/-- `R₅` is a sign matrix. -/
lemma isSignMatrix_R5 : IsSignMatrix R5 := by
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun a ↦ ?_⟩
  · fin_cases a <;> fin_cases b <;> simp [R5]
  · fin_cases a <;> fin_cases b <;> simp [R5]
  · fin_cases a <;> simp [R5]

/-- The map `![0, 1, 3] : Fin 3 → Fin 5` is injective. -/
lemma injective_013 : Function.Injective (![0, 1, 3] : Fin 3 → Fin 5) := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all

/-- The map `![0, 1, 2] : Fin 3 → Fin 5` is injective. -/
lemma injective_012 : Function.Injective (![0, 1, 2] : Fin 3 → Fin 5) := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all

/-- The switching signs `(1, -1, 1)` square to `1`. -/
lemma sign012_mul_self (a : Fin 3) :
    (![1, -1, 1] : Fin 3 → ℝ) a * (![1, -1, 1] : Fin 3 → ℝ) a = 1 := by
  fin_cases a <;> simp

/-- `J₃` is the principal submatrix of `R₅` on `{0, 1, 2}`, up to switching. -/
lemma switch_R5_012 (a b : Fin 3) :
    (![1, -1, 1] : Fin 3 → ℝ) a * (![1, -1, 1] : Fin 3 → ℝ) b *
      R5 ((![0, 1, 2] : Fin 3 → Fin 5) a) ((![0, 1, 2] : Fin 3 → Fin 5) b) = 1 := by
  fin_cases a <;> fin_cases b <;> simp [R5]

/-- The relabellings of [JFA-E, (A1)]: `relabelA6 k` maps the indices `≠ k` of `A₆` to the
indices of `R₅` (its value at `k` is irrelevant). -/
def relabelA6 : Fin 6 → Fin 6 → Fin 5 :=
  ![![0, 0, 2, 3, 4, 1], ![0, 0, 2, 3, 1, 4], ![0, 2, 0, 1, 3, 4], ![0, 2, 1, 0, 4, 3],
    ![0, 1, 2, 4, 0, 3], ![0, 1, 4, 2, 3, 0]]

/-- The switching signs of [JFA-E, (A1)] for the principal submatrix of `A₆` on the indices
`≠ k`. -/
def switchA6 : Fin 6 → Fin 6 → ℝ :=
  ![![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, -1, -1], ![1, 1, 1, -1, 1, -1], ![1, 1, -1, 1, -1, 1],
    ![1, -1, 1, -1, 1, 1], ![1, -1, -1, 1, 1, 1]]

/-- The switching signs are `±1`. -/
lemma switchA6_mul_self (k a : Fin 6) : switchA6 k a * switchA6 k a = 1 := by
  fin_cases k <;> fin_cases a <;> simp [switchA6]

/-- **[JFA-E, (A1)]**: every `5 × 5` principal submatrix of `A₆` is `R₅` up to switching and
relabelling. -/
lemma A6_eq_switch_R5 (k a b : Fin 6) (ha : a ≠ k) (hb : b ≠ k) :
    A6 a b = switchA6 k a * switchA6 k b * R5 (relabelA6 k a) (relabelA6 k b) := by
  fin_cases k <;> fin_cases a <;> fin_cases b <;> simp_all [A6, R5, relabelA6, switchA6]

/-- `relabelA6 k` is injective on the indices `≠ k`. -/
lemma relabelA6_injective (k a b : Fin 6) (ha : a ≠ k) (hb : b ≠ k)
    (h : relabelA6 k a = relabelA6 k b) : a = b := by
  fin_cases k <;> fin_cases a <;> fin_cases b <;> simp_all [relabelA6]

end ProjectionConstants.GrunbaumConjecture
