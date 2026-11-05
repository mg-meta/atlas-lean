/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Section_2_Preliminaries.A_TrackedPreliminaries
import Section_3_SearchStrategy.A_IsoInvariance

/-!
# Section 3: the conjugation lemma (paper, second lemma of §3.1)

For a subgroup `M ≤ G` and `g ∈ G`, write `M^g` for the conjugate
subgroup. The paper defines `K^g = {g⁻¹ k g}`; Mathlib's
`MulAut.conj g` conjugates as `g * k * g⁻¹`, which gives the same family
of subgroups as `g` ranges over `G`. The paper's proof is:
`G = G^g = (AM)^g = A^g M^g = A M^g`, using `A ⊴ G`, and "since
conjugates are isomorphic, `M` is semiabelian iff `M^g` is" — the latter
is `IsSemiabelian.of_mulEquiv`.
-/

namespace SemiabelianNonMonomial

/-- The conjugate subgroup `M^g`, as the image of `M` under conjugation
by `g`. -/
def conjSubgroup {G : Type} [Group G] (M : Subgroup G) (g : G) : Subgroup G :=
  M.map (MulAut.conj g).toMonoidHom

/-- Conjugation by `g` is an isomorphism `M ≃* M^g`, so `M` is
semiabelian iff `M^g` is. -/
theorem isSemiabelian_conjSubgroup {G : Type} [Group G] (M : Subgroup G) (g : G) :
    IsSemiabelian (conjSubgroup M g) ↔ IsSemiabelian M :=
  ⟨fun h => IsSemiabelian.of_mulEquiv
      (MulEquiv.subgroupMap (MulAut.conj g) M).symm h,
    fun h => IsSemiabelian.of_mulEquiv
      (MulEquiv.subgroupMap (MulAut.conj g) M) h⟩

/-- **Conjugation lemma** (paper, §3.1): let `A ⊴ G` be a normal abelian
subgroup and `M ≤ G` with `G = A ⊔ M` (the paper's `G = AM`). Then `M`
is semiabelian iff `M^g` is, and `G = A ⊔ M^g`, for every `g ∈ G`. This
is why the semiabelian check in the paper's algorithm only needs one
representative of each conjugacy class of maximal subgroups. -/
theorem conjugation_lemma {G : Type} [Group G] (A M : Subgroup G) (hA : A.Normal)
    (hAM : A ⊔ M = ⊤) (g : G) :
    (IsSemiabelian (conjSubgroup M g) ↔ IsSemiabelian M) ∧
      A ⊔ conjSubgroup M g = ⊤ := by
  refine ⟨isSemiabelian_conjSubgroup M g, ?_⟩
  have hAmap : A.map (MulAut.conj g).toMonoidHom = A := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
      rw [← hax]
      exact hA.conj_mem a ha g
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, by simpa using hA.conj_mem x hx g⁻¹, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  show A ⊔ M.map (MulAut.conj g).toMonoidHom = ⊤
  calc A ⊔ M.map (MulAut.conj g).toMonoidHom
      = (A ⊔ M).map (MulAut.conj g).toMonoidHom := by
        rw [Subgroup.map_sup, hAmap]
    _ = ⊤ := by
        rw [hAM]
        exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)

end SemiabelianNonMonomial
