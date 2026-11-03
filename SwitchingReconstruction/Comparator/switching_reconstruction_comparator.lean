/-
Copyright (c) 2026 Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Milana Golich
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Ring

/-!
# Comparator challenge: switching reconstruction of oriented graphs

Challenge module for the comparator (see
`switching_reconstruction_comparator.json`). The definitions below are
stated independently in this file, by design: they must NOT be imported
from the solution (`Formalization/`), otherwise changing a solution
definition would change both sides of the comparison and the comparator
would certify nothing about the definitions themselves. They duplicate
the paper-facing definitions of the solution under the same names, and
every one of them is enumerated in `definition_names` in the JSON config.
The theorems are the paper-facing results, stated with these challenge
definitions and proved with placeholder proofs here; the comparator
checks that the solution proves the same statements (and uses the same
definitions) with only the permitted axioms.
-/

namespace SwitchingReconstruction

/-- Challenge copy of the solution's `IsOrientedMat`. -/
def IsOrientedMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, A i j = -A j i) ∧ ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1

/-- Challenge copy of the solution's `switchSign`. -/
def switchSign {n : ℕ} (v i : Fin n) : ℤ :=
  if i = v then -1 else 1

/-- Challenge copy of the solution's `switchMat`. -/
def switchMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => switchSign v i * A i j * switchSign v j

/-- Challenge copy of the solution's `permMat`. -/
def permMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → Fin n) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => A (φ i) (φ j)

/-- Challenge copy of the solution's `MatIso`. -/
def MatIso {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ φ : Fin n ≃ Fin n, ∀ i j, B (φ i) (φ j) = A i j

/-- Challenge copy of the solution's `SameSwitchingDeck`. -/
def SameSwitchingDeck {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ π : Fin n ≃ Fin n, ∀ v, MatIso (switchMat A v) (switchMat B (π v))

/-- Challenge copy of the solution's `IsSwitchingNonReconstructible`. -/
def IsSwitchingNonReconstructible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) ℤ, IsOrientedMat B ∧ SameSwitchingDeck A B ∧ ¬ MatIso A B

/-- Challenge copy of the solution's `outdeg`. -/
def outdeg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun w => A v w = 1).card

/-- Challenge copy of the solution's `degreeProfile`. -/
def degreeProfile {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) :
    ℕ × Multiset ℕ × Multiset ℕ :=
  (outdeg A v,
    (Finset.univ.filter fun w => A v w = 1).val.map (outdeg A),
    (Finset.univ.filter fun w => A v w = -1).val.map (outdeg A))

/-- Challenge copy of the solution's `SwitchingQuestion12`. -/
def SwitchingQuestion12 : Prop :=
  ∃ A B : Matrix (Fin 12) (Fin 12) ℤ,
    IsOrientedMat A ∧ IsOrientedMat B ∧ SameSwitchingDeck A B ∧ ¬ MatIso A B

/-- Challenge copy of the solution's `SwitchingQuestion`. -/
def SwitchingQuestion : Prop :=
  ∃ n : ℕ, 12 ≤ n ∧
    ∃ A B : Matrix (Fin n) (Fin n) ℤ,
      IsOrientedMat A ∧ IsOrientedMat B ∧ SameSwitchingDeck A B ∧ ¬ MatIso A B

/-- Challenge copy of the solution's `matD` (the paper's matrix `A`). -/
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

/-- Challenge copy of the solution's `matH`: `D` switched at `0` and `1`. -/
def matH : Matrix (Fin 12) (Fin 12) ℤ :=
  switchMat (switchMat matD 0) 1

/-- Challenge copy of the solution's `matC` (the paper's printed `C`). -/
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

end SwitchingReconstruction

namespace SwitchingReconstruction

theorem matD_isOrientedMat : IsOrientedMat matD := by
  sorry

theorem matH_eq_matC : matH = matC := by
  sorry

theorem matH_isOrientedMat : IsOrientedMat matH := by
  sorry

theorem sameSwitchingDeck_matD_matH : SameSwitchingDeck matD matH := by
  sorry

theorem degreeProfile_matD_zero :
    degreeProfile matD 0 = (4, {3, 6, 6, 6}, {4, 4, 4, 5, 5, 7}) := by
  sorry

theorem matD_not_iso_matH : ¬ MatIso matD matH := by
  sorry

theorem switching_nonreconstructible_matD : IsSwitchingNonReconstructible matD := by
  sorry

theorem switchingQuestion12 : SwitchingQuestion12 := by
  sorry

theorem exists_switching_nonreconstructible_ge_twelve : SwitchingQuestion := by
  sorry

end SwitchingReconstruction
