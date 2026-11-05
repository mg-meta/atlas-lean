/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Mathlib.GroupTheory.PresentedGroup

/-!
# Section 4: GAP certificate data for the counterexample group

Obtained by running GAP 4.16.1 (built from source for this audit;
`SmallGroup(384, 20127)` with `IsomorphismFpGroup`, whose 36 relators
are exactly `counterexampleRelators`, so GAP's `f1, …, f8` are the
presentation generators of `CounterexampleGroup`).

GAP re-verified every computational claim of the paper: `IdGroup =
[384, 20127]`, solvable, `IsMonomialGroup = false`, irreducible degrees
`[1,1,1,3×21,8,8,8]`, 27 conjugacy classes, and only the three
degree-eight irreducibles are non-monomial (`TestMonomial` per
irreducible). The data below records, in presentation generators:

* the 27 conjugacy-class representatives, in GAP's class order — the
  order of the character values in `B_CharacterData`;
* the Dentzer chain `G = A₀M₀`, `M₀ = A₁M₁`, `M₁ = A₂M₂`, `M₂ = A₃M₃`
  with `M₃ ≅ C₃` abelian: `A₀,A₁,A₂` of order 8, `A₃` of order 4,
  `M₀,M₁,M₂,M₃` of orders 96, 24, 12, 3 (GAP also checks each `Aᵢ`
  abelian and normal in its ambient group, and `Aᵢ ⊔ Mᵢ` = ambient);
* the non-monomiality certificate in GAP: the subgroup orders of `G`
  are `[1,2,3,4,6,8,12,16,24,32,64,96,128,384]` — there is **no
  subgroup of order 48**, i.e. no subgroup of index 8. Since induction
  from a linear character of `L` has degree `[G:L]`, no degree-eight
  irreducible can be monomial. (The degree-3 irreducibles are induced
  from index-3 subgroups, which exist.)

These are still GAP-produced *data* recorded in Lean, not Lean proofs:
checking the chain products, normality and subgroup orders inside
`PresentedGroup`, and turning the character lists into Lean characters
of `CounterexampleGroup`, remains the blocked part of G1. But the
certificate is now fully explicit: every input a future Lean check
needs is in this file and `B_CharacterData.lean`.
-/

namespace SemiabelianNonMonomial

/-- Conjugacy-class representatives of `CounterexampleGroup`, as
words in the presentation generators `f1, …, f8` (with `f_{i+1}`
written `FreeGroup.of i`), in the same order as GAP's conjugacy
classes — hence in the same order as the character values in
`degreeEightChar₁/₂/₃`. Obtained from GAP 4.16.1
(`IsomorphismFpGroup(SmallGroup(384, 20127))`, whose relators are
exactly `counterexampleRelators`), and audited against the
Todd–Coxeter class computation: sizes
`[1, 64, 6, 6, 6, 1, 64, 64, 6, …, 64, 6, …]`, i.e.
$[1,1,6^{21},64^4]$ as a multiset. For example, class 6 is the
nontrivial central element `f8`, where all three degree-eight
characters take the value `-8`. -/
def conjugacyClassReps : List (FreeGroup (Fin 8)) := [
  1,
  FreeGroup.of 0,
  FreeGroup.of 1,
  FreeGroup.of 3,
  FreeGroup.of 5,
  FreeGroup.of 7,
  FreeGroup.of 0 * FreeGroup.of 0,
  FreeGroup.of 0 * FreeGroup.of 3,
  FreeGroup.of 1 * FreeGroup.of 3,
  FreeGroup.of 1 * FreeGroup.of 4,
  FreeGroup.of 1 * FreeGroup.of 5,
  FreeGroup.of 1 * FreeGroup.of 6,
  FreeGroup.of 2 * FreeGroup.of 4,
  FreeGroup.of 2 * FreeGroup.of 5,
  FreeGroup.of 3 * FreeGroup.of 5,
  FreeGroup.of 3 * FreeGroup.of 6,
  FreeGroup.of 4 * FreeGroup.of 6,
  FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 7,
  FreeGroup.of 1 * FreeGroup.of 3 * FreeGroup.of 5,
  FreeGroup.of 1 * FreeGroup.of 3 * FreeGroup.of 6,
  FreeGroup.of 1 * FreeGroup.of 4 * FreeGroup.of 5,
  FreeGroup.of 1 * FreeGroup.of 4 * FreeGroup.of 6,
  FreeGroup.of 2 * FreeGroup.of 3 * FreeGroup.of 5,
  FreeGroup.of 2 * FreeGroup.of 4 * FreeGroup.of 5,
  FreeGroup.of 2 * FreeGroup.of 4 * FreeGroup.of 6,
  FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 3 * FreeGroup.of 5,
  FreeGroup.of 1 * FreeGroup.of 2 * FreeGroup.of 4 * FreeGroup.of 6
]

theorem conjugacyClassReps_length : conjugacyClassReps.length = 27 := rfl

/-- Generators (as words in `f1, …, f8`) of the abelian normal
subgroups `A₀, A₁, A₂, A₃` in the Dentzer chain for
`CounterexampleGroup`, from GAP: `A₀, A₁, A₂ ≅ C₂³` (order 8) and
`A₃ ≅ C₂²` (order 4), each normal and abelian in its ambient group
below, with `Aᵢ ⊔ Mᵢ` the ambient group. -/
def dentzerChainAGenerators : List (List (FreeGroup (Fin 8))) := [
  [FreeGroup.of 1 * FreeGroup.of 3 * FreeGroup.of 4 * FreeGroup.of 5 * FreeGroup.of 6, FreeGroup.of 2 * FreeGroup.of 4 * FreeGroup.of 5 * FreeGroup.of 7, FreeGroup.of 7],
  [FreeGroup.of 1 * FreeGroup.of 5, FreeGroup.of 2 * FreeGroup.of 6, FreeGroup.of 7],
  [FreeGroup.of 1, FreeGroup.of 2, FreeGroup.of 7],
  [FreeGroup.of 1 * FreeGroup.of 2, FreeGroup.of 2]
]

/-- Generators of the semiabelian chain subgroups `M₀, M₁, M₂, M₃`
(orders 96, 24, 12, 3; structures $((C_2^3 \rtimes C_2^2) \rtimes C_3)$,
$C_2 \times A_4$, $A_4$, $C_3$), with $M_3$ abelian. Together with
`dentzerChainAGenerators` this is the paper's chain
$G = A_0M_0$, $M_0 = A_1M_1$, $M_1 = A_2M_2$, $M_2 = A_3M_3$,
expressed in the presentation generators. -/
def dentzerChainMGenerators : List (List (FreeGroup (Fin 8))) := [
  [FreeGroup.of 0, FreeGroup.of 1, FreeGroup.of 2, FreeGroup.of 5, FreeGroup.of 6, FreeGroup.of 7],
  [FreeGroup.of 0, FreeGroup.of 1, FreeGroup.of 2, FreeGroup.of 7],
  [FreeGroup.of 0, FreeGroup.of 1 * FreeGroup.of 2, FreeGroup.of 2],
  [FreeGroup.of 0]
]

theorem dentzerChainAGenerators_length : dentzerChainAGenerators.length = 4 := rfl

theorem dentzerChainMGenerators_length : dentzerChainMGenerators.length = 4 := rfl

end SemiabelianNonMonomial
