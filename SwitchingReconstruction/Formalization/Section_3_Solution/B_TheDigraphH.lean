/-
Copyright (c) 2026 Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Milana Golich
-/
import Section_3_Solution.A_TheDigraphD
import Mathlib.Tactic.FinCases

-- Kernel-decided finite checks in this file need more elaborator heartbeats.
set_option maxHeartbeats 0

/-!
# Section 3 (Solution): the oriented graph `H`

The paper obtains `H` by switching `D` at the vertices `v₀` and `v₁`:
its signed adjacency matrix `C` satisfies `C i j = -A i j` if exactly one
of `i, j` lies in `{0, 1}`, and `C i j = A i j` otherwise. In matrix form
(paper) `C = S₀₁ A S₀₁`, the product of the two switching conjugations.
Accordingly we *define* `matH` as the two successive switchings of `matD`
and then check it equals the matrix `C` printed in the paper (`matC`).
-/

namespace SwitchingReconstruction

/-- The signed adjacency matrix of `H`: `D` switched at `v₀` and then
at `v₁` (paper, Solution). -/
def matH : Matrix (Fin 12) (Fin 12) ℤ :=
  switchMat (switchMat matD 0) 1

/-- The matrix `C` printed in the paper for `H`, entry by entry. -/
def matC : Matrix (Fin 12) (Fin 12) ℤ :=
  !![ 0, -1,  1,  0,  1, -1,  1, -1, -1,  1, -1,  1;
      1,  0, -1,  1,  0,  1, -1,  1,  1, -1,  1, -1;
     -1,  1,  0, -1, -1,  0,  1, -1, -1,  1, -1,  1;
      0, -1,  1,  0,  1, -1, -1,  1,  1, -1,  1, -1;
     -1,  0,  1, -1,  0, -1, -1,  1,  1, -1,  1, -1;
      1, -1,  0,  1,  1,  0,  1, -1, -1,  1, -1,  1;
     -1,  1, -1,  1,  1, -1,  0, -1,  1,  0, -1, -1;
      1, -1,  1, -1, -1,  1,  1,  0,  1,  1,  0, -1;
      1, -1,  1, -1, -1,  1, -1, -1,  0, -1, -1,  0;
     -1,  1, -1,  1,  1, -1,  0, -1,  1,  0, -1, -1;
      1, -1,  1, -1, -1,  1,  1,  0,  1,  1,  0, -1;
     -1,  1, -1,  1,  1, -1,  1,  1,  0,  1,  1,  0]

/-- Switching `D` at `0` and `1` gives exactly the printed matrix `C`.
This is the computation the paper displays; here it is a finite check
decided by the Lean kernel (the `maxHeartbeats` bump only gives the
elaborator time to present the kernel check). -/
theorem matH_eq_matC : matH = matC :=
  of_decide_eq_true rfl

/-- `H` is an oriented graph: switching preserves oriented graphs
(`IsOrientedMat.switchMat`), applied twice. -/
theorem matH_isOrientedMat : IsOrientedMat matH :=
  (matD_isOrientedMat.switchMat 0).switchMat 1

/-- Entry form of `H` exactly as in the paper: `C i j = -A i j` if exactly
one of `i, j` lies in `{0, 1}`, and `C i j = A i j` otherwise. -/
theorem matH_apply (i j : Fin 12) :
    matH i j = (if ((i = 0 ∨ i = 1) ∧ ¬ (j = 0 ∨ j = 1)) ∨
        (¬ (i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1)) then -matD i j else matD i j) := by
  fin_cases i <;> fin_cases j <;> rfl

end SwitchingReconstruction
