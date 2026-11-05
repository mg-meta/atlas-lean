/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Basic

/-!
# Section 1: monomial groups — definition

The paper's definition (Preliminaries, "Monomial Groups"): a group is
*monomial* if every irreducible representation of `G` can be obtained via
induction from a one-dimensional representation of some subgroup of `G`.

We work with complex representations, as the paper does (its monomiality
checks are character-theoretic). `Representation.ind` is Mathlib's
induced representation along a homomorphism; here it is induction along
the inclusion `L.subtype` of a subgroup `L ≤ G`. A one-dimensional
representation of `L` is the same as a linear character `L →* ℂˣ`, via
`linearRepresentation`. Isomorphism of representations is stated with a
linear equivalence intertwining the two actions.
-/

namespace SemiabelianNonMonomial

/-- The one-dimensional complex representation attached to a linear
character `θ : H →* ℂˣ`: `g` acts on `ℂ` by multiplication by `θ g`. -/
def linearRepresentation {H : Type} [Group H] (θ : H →* ℂˣ) :
    Representation ℂ H ℂ where
  toFun g := (θ g : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
  map_one' := by ext; simp
  map_mul' g h := by
    ext
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.id_apply, smul_eq_mul]
    ring

/-- Isomorphism of representations: a linear equivalence intertwining
the two actions. -/
def ReprIso {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, ∀ g v, e (ρ g v) = σ g (e v)

/-- A representation is *monomial* if it is induced from a
one-dimensional representation (a linear character) of some subgroup.
This is a single-representation form of the paper's definition. -/
def IsMonomialRepresentation {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Prop :=
  ∃ (L : Subgroup G) (θ : L →* ℂˣ),
    ReprIso (Representation.ind L.subtype (linearRepresentation θ)) ρ

/-- **Monomial group** (paper, Preliminaries): every irreducible complex
representation of `G` is induced from a one-dimensional representation
of some subgroup of `G`. Only finite-dimensional representations are
quantified over, as irreducible representations of a finite group are
finite-dimensional. -/
def IsMonomial (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), Representation.IsIrreducible ρ →
    IsMonomialRepresentation ρ

end SemiabelianNonMonomial
