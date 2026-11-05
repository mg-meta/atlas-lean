/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Section_1_Introduction.A_SemiabelianDefinition

/-!
# Semiabelianity is invariant under isomorphism

Used by the paper's conjugation lemma ("since conjugates are
isomorphic, `M` is semiabelian iff `M^g` is semiabelian") and by the
pullback lemma (passing between a subgroup `U ≤ M` and `U` seen as a
subgroup of `M`). A semiabelian step is transported along isomorphisms
of both groups: the action is precomposed with the inverse isomorphism,
and the quotient map is transported through the induced isomorphism of
semidirect products.
-/

namespace SemiabelianNonMonomial

/-- Transport a semiabelian step along isomorphisms of the two groups. -/
theorem IsSemiabelianStep.of_equiv {H K H' K' : Type} [Group H] [Group K]
    [Group H'] [Group K'] (eH : H ≃* H') (eK : K ≃* K')
    (h : IsSemiabelianStep H K) : IsSemiabelianStep H' K' := by
  obtain ⟨A, hA, α, f, hf⟩ := h
  refine ⟨A, hA, α.comp eH.symm.toMonoidHom,
    eK.toMonoidHom.comp (f.comp
      (SemidirectProduct.lift SemidirectProduct.inl
        (SemidirectProduct.inr.comp eH.symm.toMonoidHom)
        (by intro g'; ext n <;> simp [SemidirectProduct.inl_aut]))), ?_⟩
  apply Function.Surjective.comp (MulEquiv.surjective eK)
  apply Function.Surjective.comp hf
  intro x
  refine ⟨SemidirectProduct.inl x.1 * SemidirectProduct.inr (eH x.2), ?_⟩
  rw [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    SemidirectProduct.inl_left_mul_inr_right]

/-- **Isomorphism invariance of semiabelianity**: if `e : G ≃* H` and
`G` is semiabelian, so is `H`. The chain in `H` is the image of the
chain in `G` under `e`. -/
theorem IsSemiabelian.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (hG : IsSemiabelian G) : IsSemiabelian H := by
  obtain ⟨n, C, h0, hn, hmono, hstep⟩ := hG
  refine ⟨n, fun i => (C i).map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · simp [h0]
  · show (C n).map e.toMonoidHom = ⊤
    rw [hn]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective e)
  · intro i j hij
    exact Subgroup.map_mono (hmono hij)
  · intro i hi
    exact IsSemiabelianStep.of_equiv
      (Subgroup.equivMapOfInjective (C i) e.toMonoidHom e.injective)
      (Subgroup.equivMapOfInjective (C (i + 1)) e.toMonoidHom e.injective)
      (hstep i hi)

end SemiabelianNonMonomial
