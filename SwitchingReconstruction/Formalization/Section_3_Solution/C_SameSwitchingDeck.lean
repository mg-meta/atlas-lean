/-
Copyright (c) 2026 Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Milana Golich
-/
import Section_3_Solution.B_TheDigraphH
import Mathlib.Tactic.FinCases

-- Kernel-decided finite checks in this file need more elaborator heartbeats.
set_option maxHeartbeats 0

/-!
# Section 3 (Solution): `D` and `H` have the same switching deck

Witness (paper, "Same switching deck"): the bijection
`π = (0 1)(2 5)(3 4)(6 7)(8 11)(9 10)`, i.e.
`π = [1,0,5,4,3,2,7,6,11,10,9,8]`, and for each `v` the permutation `ψ v`
tabulated in the paper. The claim `[D_v]_{ij} = [H_{π(v)}]_{ψ_v(i), ψ_v(j)}`
for all `v, i, j` says precisely that `ψ v` is an isomorphism
`switch(D, v) ≅ switch(H, π v)`; it is a finite signed-entry check over
`12 × 12 × 12` entries, decided by the Lean kernel.
-/

namespace SwitchingReconstruction

/-- The bijection `π : V(D) → V(H)` of the paper, as a function:
`π = (0 1)(2 5)(3 4)(6 7)(8 11)(9 10)`. -/
def piFun : Fin 12 → Fin 12 :=
  ![1, 0, 5, 4, 3, 2, 7, 6, 11, 10, 9, 8]

theorem piFun_bijective : Function.Bijective piFun := by decide

/-- The bijection `π` as a permutation. -/
noncomputable def piEquiv : Fin 12 ≃ Fin 12 :=
  Equiv.ofBijective piFun piFun_bijective

/-- The isomorphisms `ψ v` of the paper, tabulated row by row: `psiFun v`
is the list `[\psi_v(0), …, \psi_v(11)]` printed in the paper's table. -/
def psiFun : Fin 12 → Fin 12 → Fin 12 :=
  !![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11;
     3, 4, 5, 0, 1, 2, 6, 7, 8, 9, 10, 11;
     1, 2, 3, 4, 5, 0, 6, 7, 8, 9, 10, 11;
     3, 4, 5, 0, 1, 2, 6, 7, 8, 9, 10, 11;
     4, 5, 0, 1, 2, 3, 6, 7, 8, 9, 10, 11;
     4, 5, 0, 1, 2, 3, 6, 7, 8, 9, 10, 11;
     2, 3, 4, 5, 0, 1, 11, 6, 7, 8, 9, 10;
     2, 3, 4, 5, 0, 1, 7, 8, 9, 10, 11, 6;
     2, 3, 4, 5, 0, 1, 11, 6, 7, 8, 9, 10;
     2, 3, 4, 5, 0, 1, 8, 9, 10, 11, 6, 7;
     2, 3, 4, 5, 0, 1, 10, 11, 6, 7, 8, 9;
     2, 3, 4, 5, 0, 1, 10, 11, 6, 7, 8, 9]

theorem psiFun_bijective : ∀ v, Function.Bijective (psiFun v) := by decide

/-- The permutation `ψ v` as an equivalence, for each `v`. -/
noncomputable def psiEquiv (v : Fin 12) : Fin 12 ≃ Fin 12 :=
  Equiv.ofBijective (psiFun v) (psiFun_bijective v)

/-- The paper's claim, in matrix form: for every `v`, relabelling
`switch(H, π v)` by `ψ v` gives `switch(D, v)`. Entry by entry this is
`[D_v]_{ij} = [H_{π(v)}]_{ψ_v(i), ψ_v(j)}` for all `i, j`. Finite check
decided by the Lean kernel (elaborator heartbeat bump only). -/
theorem deckMatrixEq (v : Fin 12) :
    permMat (switchMat matH (piFun v)) (psiFun v) = switchMat matD v := by
  fin_cases v <;> exact of_decide_eq_true rfl

/-- `D` and `H` have the same switching deck, witnessed by `π` and the
`ψ v` (paper, "Same switching deck"). -/
theorem sameSwitchingDeck_matD_matH : SameSwitchingDeck matD matH := by
  refine ⟨piEquiv, fun v => ⟨psiEquiv v, fun i j => ?_⟩⟩
  have h := deckMatrixEq v
  have hij := congrFun (congrFun h i) j
  rw [permMat_apply] at hij
  exact hij

end SwitchingReconstruction
