/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Section_1_Introduction.C_KidaConjecture
import Section_2_Preliminaries.A_TrackedPreliminaries

set_option linter.style.haveILetI false

/-!
# Section 4: the counterexample and the main theorem

The paper's counterexample is `G = SmallGroup(384, 20127)` in GAP's
SmallGroups library, reported as
`((C₂ × ((C₂ × Q₈) ⋊ C₂)) ⋊ C₂) ⋊ C₃`, with the Dentzer chain
`G = A₀M₀`, `M₀ = A₁M₁`, `M₁ = A₂M₂`, `M₂ = A₃M₃`, `M₃ = C₃`
(`A₀=A₁=A₂=C₂³`, `A₃=C₂²`) certifying semiabelianity, and GAP's
`IsMonomialGroup: false` certifying non-monomiality.

That computational fact is the tracked preliminary
`counterexample_exists` (see `../../GAPS.md`, G1: the paper does not
specify the semidirect actions, and Lean has no SmallGroups library).
Everything in this file — the disproof of Kida's conjecture and the
paper's main theorem — is proved from it without further assumptions.
-/

namespace SemiabelianNonMonomial

/-- **Kida's conjecture is false**: the GAP counterexample of order 384
is a finite semiabelian group that is not monomial, contradicting
`KidaConjecture`. Proved from the tracked preliminary
`counterexample_exists`. -/
theorem not_kidaConjecture : ¬ KidaConjecture := by
  intro hconj
  obtain ⟨G, hGrp, hFin, _hcard, hsemi, hnonmono⟩ := counterexample_exists
  letI := hGrp
  letI := hFin
  exact hnonmono (hconj G hsemi)

/-- **Main theorem** (paper, Theorem `mainthm`): semiabelian groups need
not be monomial — there is a finite semiabelian group that is not
monomial. Proved from the tracked preliminary `counterexample_exists`. -/
theorem semiabelian_need_not_be_monomial : ExistsSemiabelianNonMonomial := by
  obtain ⟨G, hGrp, hFin, _hcard, hsemi, hnonmono⟩ := counterexample_exists
  exact ⟨G, hGrp, hFin, hsemi, hnonmono⟩

/-- The paper's closing remark in formal form: direct products give
more examples. For every finite semiabelian group `H`, the product of
the order-384 counterexample with `H` is again semiabelian and
non-monomial (via Kida, Lemma 2.5 and van der Waall, Theorem 2 — the
tracked preliminaries `semiabelian_product` and
`monomial_product_iff`). -/
theorem counterexample_product (H : Type) [Group H] [Finite H]
    (hH : IsSemiabelian H) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G),
      IsSemiabelian G ∧ ¬ IsMonomial G := by
  obtain ⟨G₀, hGrp, hFin, _hcard, hsemi, hnonmono⟩ := counterexample_exists
  letI := hGrp
  letI := hFin
  exact ⟨G₀ × H, inferInstance, inferInstance,
    semiabelian_product G₀ H hsemi hH,
    fun hmono => hnonmono ((monomial_product_iff G₀ H).mp hmono).1⟩

end SemiabelianNonMonomial
