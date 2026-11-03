/-
Copyright (c) 2026 Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Milana Golich
-/
import Section_3_Solution.B_TheDigraphH
import Section_1_Introduction.B_DegreeProfile
import Mathlib.Tactic.FinCases

-- Kernel-decided finite checks in this file need more elaborator heartbeats.
set_option maxHeartbeats 0

/-!
# Section 3 (Solution): `D` is not isomorphic to `H`

The paper's argument, formalized. The invariant is the degree profile
`P_G(v)` (`degreeProfile`): an isomorphism preserves it
(`degreeProfile_eq_of_iso`). Computation gives
`P_D(0) = (4, (3,6,6,6), (4,4,4,5,5,7))`, while the vertices of `H` of
out-degree `4` are exactly `2, 4, 6, 9`, with profiles
`P_H(2) = (4, (4,4,6,7), (3,4,5,5,6,6))`,
`P_H(4) = (4, (3,4,6,6), (4,4,5,5,6,7))`,
`P_H(6) = P_H(9) = (4, (3,4,5,6), (4,5,6,6,6,7))`,
none equal to `P_D(0)`. Hence no isomorphism `D ≅ H` exists.

All profile computations are finite checks decided by the Lean kernel.
-/

namespace SwitchingReconstruction

/-- `P_D(0)` computed from `A` (paper): `0 → {5,7,8,10}` of out-degrees
`(6,6,3,6)`, in-neighbours `{1,2,4,6,9,11}` of out-degrees `(5,4,5,4,4,7)`. -/
theorem degreeProfile_matD_zero :
    degreeProfile matD 0 = (4, {3, 6, 6, 6}, {4, 4, 4, 5, 5, 7}) :=
  of_decide_eq_true rfl

/-- `P_H(2)` (paper). -/
theorem degreeProfile_matH_two :
    degreeProfile matH 2 = (4, {4, 4, 6, 7}, {3, 4, 5, 5, 6, 6}) :=
  of_decide_eq_true rfl

/-- `P_H(4)` (paper). -/
theorem degreeProfile_matH_four :
    degreeProfile matH 4 = (4, {3, 4, 6, 6}, {4, 4, 5, 5, 6, 7}) :=
  of_decide_eq_true rfl

/-- `P_H(6)` (paper). -/
theorem degreeProfile_matH_six :
    degreeProfile matH 6 = (4, {3, 4, 5, 6}, {4, 5, 6, 6, 6, 7}) :=
  of_decide_eq_true rfl

/-- `P_H(9)` (paper; equal to `P_H(6)`). -/
theorem degreeProfile_matH_nine :
    degreeProfile matH 9 = (4, {3, 4, 5, 6}, {4, 5, 6, 6, 6, 7}) :=
  of_decide_eq_true rfl

/-- The vertices of `H` of out-degree `4` are exactly `2, 4, 6, 9` (paper). -/
theorem outdeg_matH_eq_four (w : Fin 12) (hw : outdeg matH w = 4) :
    w = 2 ∨ w = 4 ∨ w = 6 ∨ w = 9 := by
  fin_cases w <;> revert hw <;> decide

/-- **`D` is not isomorphic to `H`** (paper, "D is not isomorphic to H"). -/
theorem matD_not_iso_matH : ¬ MatIso matD matH := by
  rintro ⟨φ, hφ⟩
  have hprof := degreeProfile_eq_of_iso φ hφ 0
  have hdeg : outdeg matH (φ 0) = 4 := by
    have h1 := congrArg Prod.fst hprof
    rw [degreeProfile_matD_zero] at h1
    exact h1
  rcases outdeg_matH_eq_four (φ 0) hdeg with h | h | h | h <;> rw [h] at hprof
  · rw [degreeProfile_matH_two, degreeProfile_matD_zero] at hprof
    exact (by decide : (4, {4, 4, 6, 7}, {3, 4, 5, 5, 6, 6}) ≠
      (4, {3, 6, 6, 6}, {4, 4, 4, 5, 5, 7})) hprof
  · rw [degreeProfile_matH_four, degreeProfile_matD_zero] at hprof
    exact (by decide : (4, {3, 4, 6, 6}, {4, 4, 5, 5, 6, 7}) ≠
      (4, {3, 6, 6, 6}, {4, 4, 4, 5, 5, 7})) hprof
  · rw [degreeProfile_matH_six, degreeProfile_matD_zero] at hprof
    exact (by decide : (4, {3, 4, 5, 6}, {4, 5, 6, 6, 6, 7}) ≠
      (4, {3, 6, 6, 6}, {4, 4, 4, 5, 5, 7})) hprof
  · rw [degreeProfile_matH_nine, degreeProfile_matD_zero] at hprof
    exact (by decide : (4, {3, 4, 5, 6}, {4, 5, 6, 6, 6, 7}) ≠
      (4, {3, 6, 6, 6}, {4, 4, 4, 5, 5, 7})) hprof

end SwitchingReconstruction
