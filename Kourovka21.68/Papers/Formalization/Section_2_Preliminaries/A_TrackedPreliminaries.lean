/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Section_1_Introduction.A_SemiabelianDefinition
import Section_1_Introduction.B_MonomialDefinition
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.PresentedGroup

/-!
# Section 2: Preliminaries — definitions and tracked external results

Definitions from the paper's Preliminaries (modular `p`-groups,
quaternion-free 2-groups, isoclinism), followed by the **tracked
preliminaries**: results the paper quotes from the literature (or, in
the last case, obtains from GAP) and does not prove. Per `AGENTS.md`
these live in this one file as an explicit tracked list; every `sorry`
in the formalization is here, and each entry names its exact source.
The main argument is formalized modulo this list; see `../../GAPS.md`.

Tracked preliminaries:
1. `dentzer_characterization` — Dentzer, Theorem 2.3 (1995).
2. `dornhoff_theorem` — Dornhoff, Theorem 2.6 (1967). Background only.
3. `kida_theorem_1_4` — Kida, Theorem 1.4 (2025). Background only.
4. `semiabelian_product` — Kida, Lemma 2.5 (2025). Used in a remark.
5. `monomial_product_iff` — van der Waall, Theorem 2 (1988). Remark.
6. `presentedGroup_counterexample` — the GAP computation of the
   paper on the explicitly presented group `CounterexampleGroup`
   (SmallGroup(384, 20127)); see `../../GAPS.md`, G1. **Blocking.**
   (`counterexample_exists` is now proved from it.)
-/

open scoped commutatorElement

namespace SemiabelianNonMonomial

/-- A subgroup is abelian, elementwise: every two of its elements
commute. Used for the normal abelian subgroups in Dentzer's criterion. -/
def IsAbelianSubgroup {G : Type} [Group G] (A : Subgroup G) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x * y = y * x

/-- **Modular `p`-group** (paper, Preliminaries; Kida, Definition 3.1):
the subgroup lattice is modular, i.e. `⟨A, B⟩ ⊓ C = ⟨A, B ⊓ C⟩` for
subgroups `A ≤ C`. The finite `p`-group hypotheses are carried by the
statements that use this definition (e.g. `dornhoff_theorem`). -/
def IsModularGroup (G : Type) [Group G] : Prop :=
  ∀ A B C : Subgroup G, A ≤ C → (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C)

/-- A group is (isomorphic to) the quaternion group `Q₈`, stated by its
standard characterization among groups of order 8: order 8, nonabelian,
with a unique element of order two. `Q₈` itself is not in Mathlib; this
characterization is what the quaternion-free definition below needs. -/
def IsQuaternionGroup (G : Type) [Group G] [Finite G] : Prop :=
  Nat.card G = 8 ∧ (∃ a b : G, a * b ≠ b * a) ∧
    ∃! z : G, z ≠ 1 ∧ z * z = 1

/-- **Quaternion-free 2-group** (paper, Preliminaries; Kida,
Definition 3.7): no homomorphic image of any subgroup of `G` contains a
subgroup isomorphic to `Q₈`. Formalized as: for every subgroup `H ≤ G`,
every normal `N ⊴ H`, and every subgroup `K` of the quotient `H ⧸ N`,
`K` is not a quaternion group. -/
def IsQuaternionFreeGroup (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (N : Subgroup H) (_ : N.Normal) (K : Subgroup (H ⧸ N)),
    ¬ IsQuaternionGroup K

/-- **Isoclinism** (paper, Preliminaries, §Isoclinism; Hall 1940):
groups `G₁, G₂` are isoclinic if there are isomorphisms
`φ : G₁/Z(G₁) ≃* G₂/Z(G₂)` and `ψ : [G₁,G₁] ≃* [G₂,G₂]` making the
commutator diagram commute. The commuting condition is stated on
representatives: whenever `x', y'` lift `φ(x), φ(y)`, the commutator
`⁅x', y'⁆` is the `ψ`-image of `⁅x, y⁆`. -/
def Isoclinic (G₁ G₂ : Type) [Group G₁] [Group G₂] : Prop :=
  ∃ (φ : (G₁ ⧸ Subgroup.center G₁) ≃* (G₂ ⧸ Subgroup.center G₂))
    (ψ : ↥(⁅(⊤ : Subgroup G₁), (⊤ : Subgroup G₁)⁆) ≃*
      ↥(⁅(⊤ : Subgroup G₂), (⊤ : Subgroup G₂)⁆)),
    ∀ (x y : G₁) (x' y' : G₂),
      QuotientGroup.mk x' = φ (QuotientGroup.mk x) →
      QuotientGroup.mk y' = φ (QuotientGroup.mk y) →
      ψ ⟨⁅x, y⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
          (Subgroup.mem_top y)⟩ =
        ⟨⁅x', y'⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top x')
          (Subgroup.mem_top y')⟩

/-- **Tracked preliminary 1 — Dentzer's characterization** (Dentzer,
Theorem 2.3, 1995; paper, Lemma `Dentz`): a nontrivial finite group is
semiabelian iff it is the product of an abelian normal subgroup and a
proper semiabelian subgroup. Quoted in the paper, not proved there. -/
theorem dentzer_characterization (G : Type) [Group G] [Finite G]
    (hG : ¬ Subsingleton G) :
    IsSemiabelian G ↔
      ∃ (A : Subgroup G) (_ : A.Normal) (_ : IsAbelianSubgroup A)
        (M : Subgroup G), M < ⊤ ∧ IsSemiabelian M ∧ A ⊔ M = ⊤ := by
  sorry

/-- **Tracked preliminary 2 — Dornhoff's theorem** (Dornhoff,
Theorem 2.6, 1967; paper, Theorem `Dornhoff`): a solvable group whose
Sylow `p`-subgroups are modular for `p ≥ 3` and whose Sylow 2-subgroup
is quaternion-free is monomial. Background only; not used in the proof
of the main theorem. -/
theorem dornhoff_theorem (G : Type) [Group G] [Finite G] [Group.IsSolvable G]
    (hmod : ∀ (p : ℕ) (hp : 3 ≤ p) (P : Sylow p G), IsModularGroup (P : Subgroup G))
    (hqf : ∀ P : Sylow 2 G, IsQuaternionFreeGroup (P : Subgroup G)) :
    IsMonomial G := by
  sorry

/-- **Tracked preliminary 3 — Kida, Theorem 1.4** (2025; paper,
Theorem `Thm32`): an isoclinism-invariant class of finite groups,
closed under subgroups and homomorphic images and consisting of
semiabelian groups, consists of monomial groups. Background only. -/
theorem kida_theorem_1_4 (𝒜 : Type → Prop)
    (hsub : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ H : Subgroup G, 𝒜 H)
    (hquot : ∀ (G : Type) [Group G] [Finite G], 𝒜 G →
      ∀ (N : Subgroup G) [N.Normal], 𝒜 (G ⧸ N))
    (hsemi : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → IsSemiabelian G)
    (G : Type) [Group G] [Finite G] (hG : 𝒜 G) :
    IsMonomial G := by
  sorry

/-- **Tracked preliminary 4 — direct products of semiabelian groups**
(Kida, Lemma 2.5, 2025; paper, Remark after the counterexample): the
direct product of semiabelian groups is semiabelian. -/
theorem semiabelian_product (G H : Type) [Group G] [Group H] [Finite G] [Finite H]
    (hG : IsSemiabelian G) (hH : IsSemiabelian H) :
    IsSemiabelian (G × H) := by
  sorry

/-- **Tracked preliminary 5 — direct products of monomial groups**
(van der Waall, Theorem 2, 1988; paper, same Remark): `G × H` is
monomial iff `G` and `H` are monomial. Together with
`semiabelian_product` and the counterexample this builds countably many
semiabelian non-monomial groups, as the paper remarks. -/
theorem monomial_product_iff (G H : Type) [Group G] [Group H] [Finite G] [Finite H] :
    IsMonomial (G × H) ↔ IsMonomial G ∧ IsMonomial H := by
  sorry

/-- The GAP presentation of the counterexample group, on generators
`f1, …, f8` (here `Fin 8`, with `f_{i+1}` written `FreeGroup.of i`),
with the 36 relators below, as supplied from GAP for
`SmallGroup(384, 20127)`. An independent Todd–Coxeter enumeration of
this presentation (cosets of the trivial subgroup) closes with exactly
384 cosets, and the generator orders are `3, 2, 2, 4, 4, 2, 2, 2`,
consistent with the paper's order-384 group; see `../../GAPS.md`, G1. -/
def counterexampleRelators : Set (FreeGroup (Fin 8)) := {
    FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0,
    (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 2)⁻¹,
    (FreeGroup.of 2)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 2 * FreeGroup.of 0 * (FreeGroup.of 2)⁻¹ * (FreeGroup.of 1)⁻¹,
    (FreeGroup.of 3)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 3 * FreeGroup.of 0 * (FreeGroup.of 7)⁻¹ * (FreeGroup.of 4)⁻¹ * (FreeGroup.of 3)⁻¹,
    (FreeGroup.of 4)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 4 * FreeGroup.of 0 * (FreeGroup.of 3)⁻¹,
    (FreeGroup.of 5)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 5 * FreeGroup.of 0 * (FreeGroup.of 6)⁻¹,
    (FreeGroup.of 6)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 6 * FreeGroup.of 0 * (FreeGroup.of 6)⁻¹ * (FreeGroup.of 5)⁻¹,
    (FreeGroup.of 7)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 7 * FreeGroup.of 0,
    FreeGroup.of 1 * FreeGroup.of 1,
    (FreeGroup.of 2)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 2 * FreeGroup.of 1,
    (FreeGroup.of 3)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 3 * FreeGroup.of 1,
    (FreeGroup.of 4)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 4 * FreeGroup.of 1,
    (FreeGroup.of 5)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 5 * FreeGroup.of 1,
    (FreeGroup.of 6)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 6 * FreeGroup.of 1 * (FreeGroup.of 7)⁻¹,
    (FreeGroup.of 7)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 7 * FreeGroup.of 1,
    FreeGroup.of 2 * FreeGroup.of 2,
    (FreeGroup.of 3)⁻¹ * (FreeGroup.of 2)⁻¹ * FreeGroup.of 3 * FreeGroup.of 2,
    (FreeGroup.of 4)⁻¹ * (FreeGroup.of 2)⁻¹ * FreeGroup.of 4 * FreeGroup.of 2,
    (FreeGroup.of 5)⁻¹ * (FreeGroup.of 2)⁻¹ * FreeGroup.of 5 * FreeGroup.of 2 * (FreeGroup.of 7)⁻¹,
    (FreeGroup.of 6)⁻¹ * (FreeGroup.of 2)⁻¹ * FreeGroup.of 6 * FreeGroup.of 2,
    (FreeGroup.of 7)⁻¹ * (FreeGroup.of 2)⁻¹ * FreeGroup.of 7 * FreeGroup.of 2,
    FreeGroup.of 3 * FreeGroup.of 3 * (FreeGroup.of 7)⁻¹,
    (FreeGroup.of 4)⁻¹ * (FreeGroup.of 3)⁻¹ * FreeGroup.of 4 * FreeGroup.of 3 * (FreeGroup.of 7)⁻¹,
    (FreeGroup.of 5)⁻¹ * (FreeGroup.of 3)⁻¹ * FreeGroup.of 5 * FreeGroup.of 3,
    (FreeGroup.of 6)⁻¹ * (FreeGroup.of 3)⁻¹ * FreeGroup.of 6 * FreeGroup.of 3,
    (FreeGroup.of 7)⁻¹ * (FreeGroup.of 3)⁻¹ * FreeGroup.of 7 * FreeGroup.of 3,
    FreeGroup.of 4 * FreeGroup.of 4 * (FreeGroup.of 7)⁻¹,
    (FreeGroup.of 5)⁻¹ * (FreeGroup.of 4)⁻¹ * FreeGroup.of 5 * FreeGroup.of 4,
    (FreeGroup.of 6)⁻¹ * (FreeGroup.of 4)⁻¹ * FreeGroup.of 6 * FreeGroup.of 4,
    (FreeGroup.of 7)⁻¹ * (FreeGroup.of 4)⁻¹ * FreeGroup.of 7 * FreeGroup.of 4,
    FreeGroup.of 5 * FreeGroup.of 5,
    (FreeGroup.of 6)⁻¹ * (FreeGroup.of 5)⁻¹ * FreeGroup.of 6 * FreeGroup.of 5,
    (FreeGroup.of 7)⁻¹ * (FreeGroup.of 5)⁻¹ * FreeGroup.of 7 * FreeGroup.of 5,
    FreeGroup.of 6 * FreeGroup.of 6,
    (FreeGroup.of 7)⁻¹ * (FreeGroup.of 6)⁻¹ * FreeGroup.of 7 * FreeGroup.of 6,
    FreeGroup.of 7 * FreeGroup.of 7
  }

/-- The counterexample group, pinned down by the GAP presentation:
the group with generators `f1, …, f8` and relators
`counterexampleRelators`. -/
def CounterexampleGroup : Type :=
  PresentedGroup counterexampleRelators

instance : Group CounterexampleGroup :=
  inferInstanceAs (Group (PresentedGroup counterexampleRelators))

/-- **Tracked preliminary 6 — the presented counterexample group
(BLOCKING).** The group presented above has order 384 (independently
enumerated; see `counterexampleRelators`) and, by the paper's GAP
computation, it is semiabelian and not monomial. Semiabelianity and
non-monomiality are GAP's `IsSemiabelianGroup`/`IsMonomialGroup`
verdicts on `SmallGroup(384, 20127)`; the paper gives no human proof
of them and Lean has no character theory for presented groups of this
size. See `../../GAPS.md`, G1. -/
theorem presentedGroup_counterexample :
    ∃ (_ : Finite CounterexampleGroup),
      Nat.card CounterexampleGroup = 384 ∧ IsSemiabelian CounterexampleGroup ∧
        ¬ IsMonomial CounterexampleGroup := by
  sorry

/-- The paper's counterexample as an abstract existence statement,
**proved** from `presentedGroup_counterexample` applied to the
explicitly presented group above. (Previously this was itself the
tracked preliminary; the presentation data has since been supplied.) -/
theorem counterexample_exists :
    ∃ (G : Type) (_ : Group G) (_ : Finite G),
      Nat.card G = 384 ∧ IsSemiabelian G ∧ ¬ IsMonomial G := by
  obtain ⟨hFin, hcard, hsemi, hnonmono⟩ := presentedGroup_counterexample
  exact ⟨CounterexampleGroup, inferInstance, hFin, hcard, hsemi, hnonmono⟩

end SemiabelianNonMonomial
