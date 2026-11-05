/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Section_2_Preliminaries.A_TrackedPreliminaries
import Section_3_SearchStrategy.A_IsoInvariance

set_option linter.style.haveILetI false

/-!
# Section 3: the pullback lemma (paper, Lemma `lem: semiabelian-pullback`)

If `G = AU` with `A` abelian normal and `U` semiabelian, then every
maximal subgroup `M ≥ U` still satisfies `G = AM`, and `M` is
semiabelian. (Maximality of `M` is not needed beyond `U ≤ M < G` being
available when it is used; the conclusion is stated for every `M ≥ U`.)

The paper's proof: Dedekind's modular law gives `M = (M ⊓ A) U`, and
`M ⊓ A ⊴ M` is abelian, so `M` is semiabelian by Dentzer's criterion
applied inside `M`. We make that last step explicit: it is exactly the
tracked preliminary `dentzer_characterization` (Dentzer, Theorem 2.3),
which the paper also uses. The Dedekind law for subgroups is proved
elementwise here (Mathlib has it only for commutative groups).
-/

namespace SemiabelianNonMonomial

/-- Dedekind's modular law for subgroups: if `U ≤ M`, then
`M ⊓ (A ⊔ U) = (M ⊓ A) ⊔ U`. -/
theorem dedekind_modular {G : Type} [Group G] (A U M : Subgroup G) (hUM : U ≤ M)
    (hAN : A.Normal) :
    M ⊓ (A ⊔ U) = (M ⊓ A) ⊔ U := by
  haveI := hAN
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, u, hu, hau⟩ := Subgroup.mem_sup_of_normal_left.mp hx.2
    have haM : a ∈ M := by
      have hau' : a = x * u⁻¹ := by
        calc a = a * u * u⁻¹ := (mul_inv_cancel_right a u).symm
        _ = x * u⁻¹ := by rw [hau]
      rw [hau']
      exact M.mul_mem hx.1 (M.inv_mem (hUM hu))
    rw [← hau]
    exact mul_mem (Subgroup.mem_sup_left ⟨haM, ha⟩) (Subgroup.mem_sup_right hu)
  · apply sup_le
    · exact inf_le_inf le_rfl le_sup_left
    · exact le_inf hUM le_sup_right

/-- **Pullback lemma** (paper, Lemma `lem: semiabelian-pullback`): let
`G` admit an abelian normal subgroup `A` and a semiabelian subgroup `U`
with `G = A ⊔ U` (the paper's `G = AU`). Then for every subgroup
`M ≥ U` — in particular every maximal one — `G = A ⊔ M` and `M` is
semiabelian. Proved modulo Dentzer's characterization, as in the paper. -/
theorem semiabelian_pullback {G : Type} [Group G] [Finite G]
    (A : Subgroup G) (hA : A.Normal) (hAab : IsAbelianSubgroup A)
    (U : Subgroup G) (hU : IsSemiabelian U) (hAU : A ⊔ U = ⊤)
    (M : Subgroup G) (hUM : U ≤ M) :
    A ⊔ M = ⊤ ∧ IsSemiabelian M := by
  refine ⟨?_, ?_⟩
  · apply top_unique
    rw [← hAU]
    exact sup_le_sup le_rfl hUM
  · by_cases hUMeq : U = M
    · subst hUMeq
      exact hU
    · have hUMproper : U < M := lt_of_le_of_ne hUM hUMeq
      have hMnontriv : ¬ Subsingleton ↥M := by
        intro hsub
        obtain ⟨x, hxM, hxU⟩ : ∃ x, x ∈ M ∧ x ∉ U := by
          by_contra hc
          simp only [not_exists, not_and] at hc
          exact hUMproper.2 (fun y hy => Classical.byContradiction (hc y hy))
        have hx1 : (⟨x, hxM⟩ : ↥M) = 1 := Subsingleton.elim _ _
        have hx : x = 1 := by
          have := Subtype.ext_iff.mp hx1
          simpa using this
        exact hxU (hx ▸ U.one_mem)
      rw [dentzer_characterization ↥M hMnontriv]
      refine ⟨(M ⊓ A).subgroupOf M, ?_, ?_, U.subgroupOf M, ?_, ?_, ?_⟩
      · refine ⟨fun n hn g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        refine ⟨?_, hA.conj_mem _ hn.2 _⟩
        have hg : (g : G) ∈ M := g.2
        have hnn : (n : G) ∈ M := n.2
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact M.mul_mem (M.mul_mem hg hnn) (M.inv_mem hg)
      · intro x hx y hy
        exact Subtype.ext (hAab x.1 (Subgroup.mem_subgroupOf.mp hx).2 y.1
          (Subgroup.mem_subgroupOf.mp hy).2)
      · refine lt_of_le_of_ne le_top (fun h => hUMeq ?_)
        apply le_antisymm hUM
        intro x hxM
        have hx : (⟨x, hxM⟩ : ↥M) ∈ U.subgroupOf M := by
          rw [h]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hx
      · exact IsSemiabelian.of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe hUM).symm hU
      · rw [Subgroup.eq_top_iff']
        intro ⟨m, hm⟩
        haveI := hA
        obtain ⟨a, haA, u, hu, hau⟩ :=
          Subgroup.mem_sup_of_normal_left.mp (hAU.symm ▸ Subgroup.mem_top m)
        have haM : a ∈ M := by
          have hau' : a = m * u⁻¹ := by
            calc a = a * u * u⁻¹ := (mul_inv_cancel_right a u).symm
            _ = m * u⁻¹ := by rw [hau]
          rw [hau']
          exact M.mul_mem hm (M.inv_mem (hUM hu))
        have hmem : (⟨a, haM⟩ : ↥M) * (⟨u, hUM hu⟩ : ↥M) ∈
            (M ⊓ A).subgroupOf M ⊔ U.subgroupOf M :=
          mul_mem (Subgroup.mem_sup_left ⟨haM, haA⟩) (Subgroup.mem_sup_right hu)
        rwa [show (⟨a, haM⟩ : ↥M) * (⟨u, hUM hu⟩ : ↥M) = ⟨m, hm⟩ from
          Subtype.ext hau] at hmem

end SemiabelianNonMonomial
