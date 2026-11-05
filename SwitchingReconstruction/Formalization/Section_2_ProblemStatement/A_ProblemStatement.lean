/-
Copyright (c) 2026 Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Milana Golich
-/
import Section_1_Introduction.A_OrientedGraphAndSwitching

/-!
# Section 2: Problem Statement

The question posed in Bondy–Mercier (2011) and recalled in the paper
(Problem Statement):

> **Question.** Does there exist a switching, non-reconstructible digraph
> on twelve or more vertices?

The paper answers it for oriented graphs on `12` vertices. We state the
question here as a `Prop`, in the signed-matrix language of
`A_OrientedGraphAndSwitching`; it is answered (affirmatively, at `n = 12`)
by `exists_switching_nonreconstructible_ge_twelve` in
`Section_3_Solution/E_MainTheorem.lean`.

Background only (not results of this paper, not formalized): the
Kelly–Ulam graph reconstruction conjecture and Stanley's
vertex-switching question, cited in the Introduction.
-/

namespace SwitchingReconstruction

/-- The Bondy–Mercier question at order `12` (paper, Problem Statement):
there exist oriented graphs `D, H` on `12` vertices with the same switching
deck that are not isomorphic. -/
def SwitchingQuestion12 : Prop :=
  ∃ A B : Matrix (Fin 12) (Fin 12) ℤ,
    IsOrientedMat A ∧ IsOrientedMat B ∧ SameSwitchingDeck A B ∧ ¬ MatIso A B

/-- The Bondy–Mercier question as posed ("twelve or more vertices"):
there is some `n ≥ 12` carrying oriented graphs with the same switching
deck that are not isomorphic. The paper proves this with `n = 12`; it does
not give a construction for every `n ≥ 12`. -/
def SwitchingQuestion : Prop :=
  ∃ n : ℕ, 12 ≤ n ∧
    ∃ A B : Matrix (Fin n) (Fin n) ℤ,
      IsOrientedMat A ∧ IsOrientedMat B ∧ SameSwitchingDeck A B ∧ ¬ MatIso A B

end SwitchingReconstruction
