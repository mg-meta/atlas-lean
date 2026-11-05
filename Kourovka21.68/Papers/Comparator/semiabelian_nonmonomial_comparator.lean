/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.IntervalCases

/-!
# Comparator challenge: semiabelian groups need not be monomial

Challenge module for the comparator (see
`semiabelian_nonmonomial_comparator.json`). The definitions below are
stated independently in this file, by design: they must NOT be imported
from the solution (`Formalization/`), otherwise changing a solution
definition would change both sides of the comparison and the comparator
would certify nothing about the definitions themselves. They duplicate
the paper-facing definitions of the solution under the same names, and
every one of them is enumerated in `definition_names` in the JSON
config. The theorems are the paper-facing results proved by the
solution, stated with these challenge definitions and proved with
placeholder proofs here; the comparator checks that the solution proves
the same statements (and uses the same definitions) with only the
permitted axioms.

The six tracked preliminaries of
`Formalization/Section_2_Preliminaries/A_TrackedPreliminaries.lean`
(Dentzer, Dornhoff, Kida 1.4, the two product lemmas, and the GAP
counterexample fact) are *not* comparator theorems: they are quoted
external/computational inputs that the solution itself does not prove,
tracked in `../GAPS.md`. The config therefore lists only the theorems
the solution proves outright; the main theorem is among them, since its
proof from the preliminaries is fully formalized.
-/

open scoped commutatorElement

namespace SemiabelianNonMonomial

/-- Challenge copy of the solution's `IsSemiabelianStep`. -/
def IsSemiabelianStep (H K : Type) [Group H] [Group K] : Prop :=
  ∃ (A : Type) (_ : CommGroup A) (α : H →* MulAut A) (f : A ⋊[α] H →* K),
    Function.Surjective f

/-- Challenge copy of the solution's `IsSemiabelian`. -/
def IsSemiabelian (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (C : ℕ → Subgroup G),
    C 0 = ⊥ ∧ C n = ⊤ ∧ Monotone C ∧
    ∀ i < n, IsSemiabelianStep (C i) (C (i + 1))

/-- Challenge copy of the solution's `linearRepresentation`. -/
def linearRepresentation {H : Type} [Group H] (θ : H →* ℂˣ) :
    Representation ℂ H ℂ where
  toFun g := (θ g : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
  map_one' := by ext; simp
  map_mul' g h := by
    ext
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.id_apply, smul_eq_mul]
    ring

/-- Challenge copy of the solution's `ReprIso`. -/
def ReprIso {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, ∀ g v, e (ρ g v) = σ g (e v)

/-- Challenge copy of the solution's `IsMonomialRepresentation`. -/
def IsMonomialRepresentation {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Prop :=
  ∃ (L : Subgroup G) (θ : L →* ℂˣ),
    ReprIso (Representation.ind L.subtype (linearRepresentation θ)) ρ

/-- Challenge copy of the solution's `IsMonomial`. -/
def IsMonomial (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), Representation.IsIrreducible ρ →
    IsMonomialRepresentation ρ

/-- Challenge copy of the solution's `KidaConjecture`. -/
def KidaConjecture : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSemiabelian G → IsMonomial G

/-- Challenge copy of the solution's `ExistsSemiabelianNonMonomial`. -/
def ExistsSemiabelianNonMonomial : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), IsSemiabelian G ∧ ¬ IsMonomial G

/-- Challenge copy of the solution's `IsAbelianSubgroup`. -/
def IsAbelianSubgroup {G : Type} [Group G] (A : Subgroup G) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x * y = y * x

/-- Challenge copy of the solution's `IsModularGroup`. -/
def IsModularGroup (G : Type) [Group G] : Prop :=
  ∀ A B C : Subgroup G, A ≤ C → (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C)

/-- Challenge copy of the solution's `IsQuaternionGroup`. -/
def IsQuaternionGroup (G : Type) [Group G] [Finite G] : Prop :=
  Nat.card G = 8 ∧ (∃ a b : G, a * b ≠ b * a) ∧
    ∃! z : G, z ≠ 1 ∧ z * z = 1

/-- Challenge copy of the solution's `IsQuaternionFreeGroup`. -/
def IsQuaternionFreeGroup (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (N : Subgroup H) (_ : N.Normal) (K : Subgroup (H ⧸ N)),
    ¬ IsQuaternionGroup K

/-- Challenge copy of the solution's `Isoclinic`. -/
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

/-- Challenge copy of the solution's `conjSubgroup`. -/
def conjSubgroup {G : Type} [Group G] (M : Subgroup G) (g : G) : Subgroup G :=
  M.map (MulAut.conj g).toMonoidHom

/-- Challenge copy of the solution's `counterexampleRelators` (the GAP presentation). -/
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

/-- Challenge copy of the solution's `CounterexampleGroup`. -/
def CounterexampleGroup : Type :=
  PresentedGroup counterexampleRelators

end SemiabelianNonMonomial

namespace SemiabelianNonMonomial

theorem isSemiabelian_of_subsingleton (G : Type) [Group G] [Subsingleton G] :
    IsSemiabelian G := by
  sorry

theorem isSemiabelian_of_commGroup (G : Type) [CommGroup G] : IsSemiabelian G := by
  sorry

theorem IsSemiabelianStep.of_equiv {H K H' K' : Type} [Group H] [Group K]
    [Group H'] [Group K'] (eH : H ≃* H') (eK : K ≃* K')
    (h : IsSemiabelianStep H K) : IsSemiabelianStep H' K' := by
  sorry

theorem IsSemiabelian.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (hG : IsSemiabelian G) : IsSemiabelian H := by
  sorry

theorem dedekind_modular {G : Type} [Group G] (A U M : Subgroup G) (hUM : U ≤ M)
    (hAN : A.Normal) :
    M ⊓ (A ⊔ U) = (M ⊓ A) ⊔ U := by
  sorry

theorem semiabelian_pullback {G : Type} [Group G] [Finite G]
    (A : Subgroup G) (hA : A.Normal) (hAab : IsAbelianSubgroup A)
    (U : Subgroup G) (hU : IsSemiabelian U) (hAU : A ⊔ U = ⊤)
    (M : Subgroup G) (hUM : U ≤ M) :
    A ⊔ M = ⊤ ∧ IsSemiabelian M := by
  sorry

theorem isSemiabelian_conjSubgroup {G : Type} [Group G] (M : Subgroup G) (g : G) :
    IsSemiabelian (conjSubgroup M g) ↔ IsSemiabelian M := by
  sorry

theorem conjugation_lemma {G : Type} [Group G] (A M : Subgroup G) (hA : A.Normal)
    (hAM : A ⊔ M = ⊤) (g : G) :
    (IsSemiabelian (conjSubgroup M g) ↔ IsSemiabelian M) ∧
      A ⊔ conjSubgroup M g = ⊤ := by
  sorry

theorem not_kidaConjecture : ¬ KidaConjecture := by
  sorry

theorem semiabelian_need_not_be_monomial : ExistsSemiabelianNonMonomial := by
  sorry

theorem counterexample_product (H : Type) [Group H] [Finite H]
    (hH : IsSemiabelian H) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G),
      IsSemiabelian G ∧ ¬ IsMonomial G := by
  sorry

end SemiabelianNonMonomial
