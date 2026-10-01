/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants.ETF.Certificate

/-!
# Maximal real equiangular tight frames from integer certificates

We construct maximal equiangular tight frames `ETF(m, m(m+1)/2)` in `ℝ^m` for `m = 2, 7, 23`
from integer certificates (`ETFCertificate`, see `ProjectionConstants.ETF.Certificate`), checked
by the Lean kernel (`decide +kernel`):

* `m = 2`: the three vectors `3eᵢ - 𝟙 ∈ ℝ³`, orthogonal to `𝟙` (the "Mercedes–Benz frame");
* `m = 7`: the 28 vectors `4·𝟙_S - 𝟙 ∈ ℝ⁸`, `S` a 2-subset of `{0, …, 7}`, orthogonal to `𝟙`;
* `m = 23`: the 276 equiangular lines in `ℝ²³` coming from the extended binary Golay code: in
  `ℝ²⁴ = ℝ^{0, …, 23}` the 23 vectors with entries `3` at `0`, `7` at `j` and `-1` elsewhere
  (`1 ≤ j ≤ 23`), and the 253 vectors `4·𝟙_(O ∖ 0) - 𝟙`, where `O` runs through the octads of
  the Golay code containing `0`. All of them are orthogonal to `u = (5, 1, …, 1)`, have squared
  norm `80` and pairwise inner products `±16`, and `∑ vᵢ vᵢᵀ = 960 I - 20 u uᵀ`.

These frames give the values `λ_ℝ(2) = 4/3`, `λ_ℝ(7) = 5/2` and `λ_ℝ(23) = 14/3` of
[DL, Theorem 2.4], see `ProjectionConstants.Values`. All declarations are in the namespace
`ProjectionConstants.MaximalETF`.

## Main definitions

* `cert2`, `cert7`, `cert23`: the certificates for `ETF(2, 3)`, `ETF(7, 28)` and `ETF(23, 276)`.
* `octads`: the 253 octads of the extended binary Golay code containing the coordinate `0`.

## Main statements

* `existsETF_two`, `existsETF_seven`, `existsETF_twentyThree`: there are equiangular tight frames
  of `3` vectors in `ℝ²`, of `28` vectors in `ℝ⁷` and of `276` vectors in `ℝ²³`.

## Implementation notes

The octads are given as bit masks; they were computed from the cyclic Golay code with generator
polynomial `1 + x² + x⁴ + x⁵ + x⁶ + x¹⁰ + x¹¹` (coordinate `0` is the parity coordinate). Their
use in the proof only depends on the certificate check, not on this provenance.

## References

* [DL] B. Deręgowska, B. Lewandowska, *A simple proof of the Grünbaum conjecture*,
  arXiv:2206.09454.
-/

namespace ProjectionConstants

namespace MaximalETF

open ETFCertificate

/-! ### `m = 2`: three lines in `ℝ²` -/

/-- The certificate for `ETF(2, 3)`. -/
def cert2 : ETFCertificate where
  n := 3
  t := 1
  ws := (List.range 3).map fun i ↦ (List.range 3).map fun k ↦ if k = i then 3 else 0
  u := [1, 1, 1]
  a := 3
  normSq := 6
  innerAbs := 3
  c := 9
  M := 3
  B := 32

/-- The certificate `cert2` is valid. -/
theorem cert2_check : cert2.check = true := by decide +kernel

/-- The certificate `cert2` consists of `3` vectors. -/
theorem cert2_N : cert2.N = 3 := by decide +kernel

/-- There is an equiangular tight frame of 3 vectors in `ℝ²`. -/
theorem existsETF_two : ExistsETF ℝ 2 3 :=
  cert2_N ▸ existsETF cert2_check (by norm_num) (by decide) (by decide +kernel)

/-! ### `m = 7`: 28 lines in `ℝ⁷` -/

/-- The certificate for `ETF(7, 28)`. -/
def cert7 : ETFCertificate where
  n := 8
  t := 1
  ws := (List.sublistsLen 2 (List.range 8)).map fun S ↦
    (List.range 8).map fun k ↦ if k ∈ S then 4 else 0
  u := List.replicate 8 1
  a := 12
  normSq := 24
  innerAbs := 8
  c := 96
  M := 4
  B := 512

set_option maxRecDepth 10000 in
/-- The certificate `cert7` is valid. -/
theorem cert7_check : cert7.check = true := by decide +kernel

/-- The certificate `cert7` consists of `28` vectors. -/
theorem cert7_N : cert7.N = 28 := by decide +kernel

/-- There is an equiangular tight frame of 28 vectors in `ℝ⁷`. -/
theorem existsETF_seven : ExistsETF ℝ 7 28 :=
  cert7_N ▸ existsETF cert7_check (by norm_num) (by decide) (by decide +kernel)

/-! ### `m = 23`: 276 lines in `ℝ²³` from the Golay code -/

/-- The 253 octads of the extended binary Golay code containing the coordinate `0`, as bit masks
of subsets of `{0, …, 23}`. -/
def octads : List ℕ := [
    1319699, 12650793, 86299, 2893845, 4331549, 1222017, 8398155, 1704611,
    460851, 5523073, 6293843, 1781777, 6685191, 2310229, 4888065, 14747201,
    172597, 3686801, 8524371, 6818441, 548979, 820101, 4483083, 2401801,
    6885637, 19095, 13124355, 1200901, 10557585, 9506893, 934425, 2527505,
    9193633, 9607201, 4273289, 6162689, 2103171, 2437187, 3442819, 1540673,
    333333, 4753447, 2195913, 192585, 3149879, 574603, 5767765, 5055009,
    11731203, 531249, 590013, 5550085, 12717187, 9465987, 12325377, 38189,
    4296817, 408193, 3162699, 5253297, 445445, 11046145, 1149205, 4596817,
    5423123, 4984979, 2172209, 1640201, 9240913, 3280401, 13636881, 12599513,
    2124993, 2360049, 1380769, 315939, 1086105, 2298409, 4759833, 3220101,
    690385, 921701, 14950785, 2148409, 8946281, 11575377, 2444033, 1610051,
    3265537, 666665, 1263753, 4461385, 1074205, 9748745, 3563553, 8716939,
    7127105, 1843401, 14716939, 10846245, 13771273, 1868849, 8412681, 12641313,
    6440201, 7873539, 1313325, 8546577, 1155115, 6560801, 12747077, 2666657,
    2626649, 8675909, 1333329, 14254209, 3081345, 2262115, 9963547, 10486557,
    8593633, 890889, 1068323, 12757, 8421811, 295007, 2883883, 5333313,
    4206341, 15335473, 9471495, 656663, 1180025, 816385, 8657159, 467213,
    7475393, 8663097, 271527, 4915275, 1916935, 5787689, 10881097, 265625,
    8619033, 385169, 4309517, 631877, 76377, 2165775, 12880401, 600451,
    10630149, 15747077, 8505411, 6320657, 9830549, 2720275, 5278793, 5440549,
    8783649, 6531073, 543053, 8499969, 345193, 11535529, 8431757, 10110017,
    4195899, 11100169, 537103, 2775043, 9112069, 10666625, 3409221, 233607,
    1632769, 611009, 4620457, 4524229, 152753, 4803601, 770337, 3737697,
    4344417, 1446923, 12587685, 6379, 13370381, 8922769, 790083, 7667737,
    48147, 4720097, 166667, 2379917, 8471941, 8983587, 102049, 6325397,
    1115347, 10765331, 2236571, 66407, 8536111, 3833869, 4235971, 8966165,
    96293, 5243279, 1580165, 13893731, 9440193, 9969957, 9776129, 1189959,
    10506593, 6373539, 4249985, 25513, 13062145, 2761537, 9048457, 305505,
    13121601, 222723, 6299757, 9519665, 4391825, 5315075, 1097957, 4473141,
    8391797, 10496547, 204097, 11010247, 51025, 2136645, 12656663, 2230693,
    4337955, 4874373, 410051, 2154759, 4215879, 1062497, 7373601, 9347075,
    4556035, 8688833, 3160329, 2639397, 132813]

/-- The shifted vector (`+ 𝟙`) of an octad `O ∋ 0`: `4` on `O ∖ 0`, `0` elsewhere. -/
def octadVec (O : ℕ) : List ℕ :=
  (List.range 24).map fun k ↦ if k ≠ 0 ∧ O.testBit k then 4 else 0

/-- The shifted vector (`+ 𝟙`) with `4` at `0`, `8` at `j` and `0` elsewhere. -/
def pointVec (j : ℕ) : List ℕ :=
  (List.range 24).map fun k ↦ if k = 0 then 4 else if k = j then 8 else 0

/-- The certificate for `ETF(23, 276)`. -/
def cert23 : ETFCertificate where
  n := 24
  t := 1
  ws := (List.range' 1 23).map pointVec ++ octads.map octadVec
  u := 5 :: List.replicate 23 1
  a := 20
  normSq := 80
  innerAbs := 16
  c := 960
  M := 8
  B := 32768

set_option maxRecDepth 100000 in
/-- The certificate `cert23` is valid. -/
theorem cert23_check : cert23.check = true := by decide +kernel

set_option maxRecDepth 10000 in
/-- The certificate `cert23` consists of `276` vectors. -/
theorem cert23_N : cert23.N = 276 := by decide +kernel

/-- There is an equiangular tight frame of 276 vectors in `ℝ²³`. -/
theorem existsETF_twentyThree : ExistsETF ℝ 23 276 :=
  cert23_N ▸ existsETF cert23_check (by norm_num) (by decide) (by decide +kernel)

end MaximalETF

end ProjectionConstants
