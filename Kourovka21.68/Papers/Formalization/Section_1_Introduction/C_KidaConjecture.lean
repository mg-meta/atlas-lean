/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Section_1_Introduction.A_SemiabelianDefinition
import Section_1_Introduction.B_MonomialDefinition

/-!
# Section 1: Kida's conjecture and the main theorem

Kida's conjecture (paper, Conjecture, `conj`) and the paper's main
theorem (`mainthm`): "Semiabelian groups need not be monomial." The main
theorem is the negation of the conjecture, witnessed by one finite
semiabelian non-monomial group; it is proved in
`Section_4_Counterexample/A_Counterexample.lean` from the tracked GAP
preliminary recorded in `../../GAPS.md` (G1).
-/

namespace SemiabelianNonMonomial

/-- **Kida's conjecture** (paper, Conjecture `conj`): if a group `G` is
semiabelian, then `G` is monomial. Stated for finite groups, as in the
paper. -/
def KidaConjecture : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSemiabelian G → IsMonomial G

/-- The content of the paper's main theorem: there is a finite
semiabelian group that is not monomial. -/
def ExistsSemiabelianNonMonomial : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), IsSemiabelian G ∧ ¬ IsMonomial G

end SemiabelianNonMonomial
