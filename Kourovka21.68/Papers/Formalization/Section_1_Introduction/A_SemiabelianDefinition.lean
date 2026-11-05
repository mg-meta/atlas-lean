/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.IntervalCases

/-!
# Section 1: semiabelian groups — definition

The paper's Definition 1 (Kida, Definition 2.1): a finite group `G` is
*semiabelian* if it has a sequence `G₀ = 1 ≤ ⋯ ≤ Gₙ = G` such that each
`Gᵢ₊₁` is a quotient group of `Gᵢ ⋊ Aᵢ` with `Aᵢ` a finite abelian group.

We formalize the sequence as a chain of subgroups of `G`
(`IsSemiabelian`), with the single step factored out
(`IsSemiabelianStep`). In Mathlib notation `A ⋊[α] H` is the semidirect
product with normal subgroup `A`, where `α : H →* MulAut A` is the action
of `H` on `A`; the paper's `Gᵢ ⋊ Aᵢ` is this with the roles read as
"`Gᵢ` acting on `Aᵢ`". A step only asks for an abstract quotient, as in
the source definition: a surjective homomorphism onto the next group.
-/

namespace SemiabelianNonMonomial

/-- One step of the semiabelian chain: `K` is a quotient of an abelian
semidirect product with `H`, i.e. there are a finite abelian group `A`,
an action `α` of `H` on `A`, and a surjective homomorphism
`A ⋊[α] H →* K`. -/
def IsSemiabelianStep (H K : Type) [Group H] [Group K] : Prop :=
  ∃ (A : Type) (_ : CommGroup A) (α : H →* MulAut A) (f : A ⋊[α] H →* K),
    Function.Surjective f

/-- **Definition 1 (semiabelian).** A group `G` is semiabelian if it has a
subgroup chain `C 0 = ⊥ ≤ ⋯ ≤ C n = ⊤` in which every successive group is
a quotient of an abelian semidirect product with its predecessor. -/
def IsSemiabelian (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (C : ℕ → Subgroup G),
    C 0 = ⊥ ∧ C n = ⊤ ∧ Monotone C ∧
    ∀ i < n, IsSemiabelianStep (C i) (C (i + 1))

/-- The trivial group is semiabelian (the empty chain, `n = 0`). More
generally this holds for any subsingleton group. -/
theorem isSemiabelian_of_subsingleton (G : Type) [Group G] [Subsingleton G] :
    IsSemiabelian G := by
  refine ⟨0, fun _ => ⊥, rfl, ?_, fun _ _ _ => bot_le, fun i hi => by omega⟩
  ext x
  simp only [Subgroup.mem_bot, Subgroup.mem_top]
  exact iff_of_true (Subsingleton.elim x 1) trivial

/-- Abelian groups are semiabelian (paper, Preliminaries: "it is easily
seen that abelian groups are semiabelian"), via the one-step chain
`1 ≤ G` and the quotient `G ⋊[1] 1 → G`. -/
theorem isSemiabelian_of_commGroup (G : Type) [CommGroup G] : IsSemiabelian G := by
  refine ⟨1, fun i => if i = 0 then ⊥ else ⊤, by simp, by simp, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i = 0
    · subst hi; simp
    · have hj : j ≠ 0 := fun hj => hi (by omega)
      simp [hi, hj]
  · intro i hi
    interval_cases i
    show IsSemiabelianStep (⊥ : Subgroup G) (⊤ : Subgroup G)
    refine ⟨G, inferInstance, 1,
      (Subgroup.topEquiv.symm.toMonoidHom).comp
        (SemidirectProduct.lift (MonoidHom.id G) (1 : ↥(⊥ : Subgroup G) →* G)
          (by intro g; ext n; simp)), ?_⟩
    intro y
    refine ⟨SemidirectProduct.inl (Subgroup.topEquiv y), ?_⟩
    exact Subtype.ext (by simp)

end SemiabelianNonMonomial
