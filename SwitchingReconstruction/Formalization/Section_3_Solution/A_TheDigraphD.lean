/-
Copyright (c) 2026 Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Milana Golich
-/
import Section_1_Introduction.A_OrientedGraphAndSwitching
import Mathlib.Tactic.FinCases

/-!
# Section 3 (Solution): the oriented graph `D`

The paper's oriented graph `D` on `V = {v₀, …, v₁₁}`, given by the
skew-symmetric signed adjacency matrix `A` printed in the paper. Vertices
`vᵢ` are identified with `i : Fin 12`.

All finite checks in this file are decided by the Lean kernel
(`of_decide_eq_true rfl` / `fin_cases` + `rfl`); no kernel-bypassing
decision procedure and no placeholder proof is used in this formalization.
-/

namespace SwitchingReconstruction

/-- The signed adjacency matrix `A` of `D` (paper, Solution, "Oriented
graphs `D` and `H`"): `matD i j = 1` iff `i → j`, `-1` iff `j → i`, and
`0` iff `i, j` are non-adjacent. -/
def matD : Matrix (Fin 12) (Fin 12) ℤ :=
  !![ 0, -1, -1,  0, -1,  1, -1,  1,  1, -1,  1, -1;
      1,  0,  1, -1,  0, -1,  1, -1, -1,  1, -1,  1;
      1, -1,  0, -1, -1,  0,  1, -1, -1,  1, -1,  1;
      0,  1,  1,  0,  1, -1, -1,  1,  1, -1,  1, -1;
      1,  0,  1, -1,  0, -1, -1,  1,  1, -1,  1, -1;
     -1,  1,  0,  1,  1,  0,  1, -1, -1,  1, -1,  1;
      1, -1, -1,  1,  1, -1,  0, -1,  1,  0, -1, -1;
     -1,  1,  1, -1, -1,  1,  1,  0,  1,  1,  0, -1;
     -1,  1,  1, -1, -1,  1, -1, -1,  0, -1, -1,  0;
      1, -1, -1,  1,  1, -1,  0, -1,  1,  0, -1, -1;
     -1,  1,  1, -1, -1,  1,  1,  0,  1,  1,  0, -1;
      1, -1, -1,  1,  1, -1,  1,  1,  0,  1,  1,  0]

/-- `D` is an oriented graph: `A` is skew-symmetric with entries in
`{-1, 0, 1}`. -/
theorem matD_isOrientedMat : IsOrientedMat matD := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j <;> decide

/-- The only non-adjacent distinct vertices of `D` (paper, Solution):
the six pairs `(0,3), (1,4), (2,5), (6,9), (7,10), (8,11)`, in either order. -/
theorem matD_eq_zero_iff (i j : Fin 12) :
    matD i j = 0 ↔ i = j ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
      (i = 1 ∧ j = 4) ∨ (i = 4 ∧ j = 1) ∨ (i = 2 ∧ j = 5) ∨ (i = 5 ∧ j = 2) ∨
      (i = 6 ∧ j = 9) ∨ (i = 9 ∧ j = 6) ∨ (i = 7 ∧ j = 10) ∨ (i = 10 ∧ j = 7) ∨
      (i = 8 ∧ j = 11) ∨ (i = 11 ∧ j = 8) := by
  fin_cases i <;> fin_cases j <;> decide

end SwitchingReconstruction
