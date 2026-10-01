/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ETF.Maximal.Certificates
import ProjectionConstants.FourSix.Classification

/-!
# Corrupted certificates are rejected

Run with `lake env lean scripts/CertificateNegativeTests.lean`. The kernel computations that
accept the certificates of `ETF/Maximal/Certificates.lean` and of `FourSix/` reject slightly
modified ones.
-/

namespace ProjectionConstants.MaximalETF

/-- `cert23` with its first octad replaced by a set that is not an octad. -/
def badOctad : ETFCertificate :=
  { cert23 with
    ws := (List.range' 1 23).map pointVec ++
      (octads.set 0 (1 + 2 + 4 + 8 + 16 + 32 + 64 + 256)).map octadVec }

theorem badOctad_check : badOctad.check = false := by decide +kernel

/-- `cert23` with the wrong modulus of the inner products. -/
def badAngle : ETFCertificate := { cert23 with innerAbs := 15 }

theorem badAngle_check : badAngle.check = false := by decide +kernel

/-- `cert7` with the wrong frame operator. -/
def badFrame : ETFCertificate := { cert7 with a := 11 }

theorem badFrame_check : badFrame.check = false := by decide +kernel

end ProjectionConstants.MaximalETF

namespace ProjectionConstants.FourSix

/-- The certificate for `A2` with a diagonal entry of `C` above `2/3`. -/
def badDiag : SosCertificate (Fin 6) :=
  { certificateA2 with C := certificateA2.C.updateRow 0 ![7/10, 0, 0, -3/10, -3/10, -3/10] }

theorem badDiag_invalid : ¬ badDiag.IsValid A2Int := by decide +kernel

/-- The certificate for `A2`, used for `A1`. -/
theorem wrongTarget_invalid : ¬ certificateA2.IsValid A1Int := by decide +kernel

/-- The certificate for `A3` with a negative coefficient in a sum of squares. -/
def badSign : SosCertificate (Fin 6) :=
  { certificateA3 with sosC := [(1/6, ![2, -1, -1, -1, -1, 2]), (-1/2, ![0, 1, -1, -1, 1, 0])] }

theorem badSign_invalid : ¬ badSign.IsValid A3Int := by decide +kernel

/-- The classification table with the first entry sent to the wrong representative. -/
def badTable : List (ℕ × ℕ × ℕ) := (0, 181896, 4) :: classificationTable.tail

theorem badTable_check : checkTable 0 badTable = false := by decide +kernel

/-- The classification table with a permutation that is not injective in its first entry. -/
def badPerm : List (ℕ × ℕ × ℕ) := (0, 181888, 3) :: classificationTable.tail

theorem badPerm_check : checkTable 0 badPerm = false := by decide +kernel

end ProjectionConstants.FourSix
