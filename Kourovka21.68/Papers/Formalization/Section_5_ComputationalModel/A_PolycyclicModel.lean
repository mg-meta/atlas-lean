 /-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-!
# Section 5: computational model — the polycyclic action (verified)

This file is the first step of the computational-model route to
discharging G1 (see `../../GAPS.md`): a *kernel-verified* action of the
free group on 8 generators on `Fin 384`, given by polycyclic collection
in the normal form `f1^e1 ⋯ f8^e8` with exponent ranges `[3,2,2,2,2,2,2,2]`.

Conjugation and power-carry tables are read off the GAP presentation
(`counterexampleRelators`): each conjugation relator
`f_j⁻¹ f_i⁻¹ f_j f_i · tail = 1` gives `f_i⁻¹ f_j f_i = f_j · tail⁻¹`
(in normal-form order), and the power relations are
`f1³ = f2² = f3² = f6² = f7² = f8² = 1`, `f4² = f5² = f8`. The collector
was validated in Python against the full Todd–Coxeter multiplication
table of the presentation (0 mismatches on all 384×384 products), and
then transcribed here. `actWord` is right multiplication by a word,
computed by collection; `presentationAction_relators` checks, by
`decide` in the Lean kernel, that every one of the 36 relators acts as
the identity on all 384 elements. That is the statement that the
polycyclic action factors through `CounterexampleGroup`
(`PresentedGroup counterexampleRelators`) — the homomorphism itself,
the group operation on `Fin 384`, the order argument, and the character
theory are still to be built on top of this action (see G1).
-/

namespace SemiabelianNonMonomial

/-- Relative orders of the pc generators f1..f8. -/
def pcRange (i : Nat) : Nat := [3, 2, 2, 2, 2, 2, 2, 2][i]!

/-- Conjugation word: f_j^{-1} f_k f_j, for k > j, as a list of
    (generator index, isInverse) atoms. -/
def conjWord (k j : Nat) : List (Nat × Bool) := match k, j with
  | 1, 0 => [(1, false), (2, false)]
  | 2, 0 => [(2, false), (1, false), (2, false)]
  | 2, 1 => [(2, false)]
  | 3, 0 => [(3, false), (3, false), (4, false), (7, false)]
  | 3, 1 => [(3, false)]
  | 3, 2 => [(3, false)]
  | 4, 0 => [(4, false), (3, false)]
  | 4, 1 => [(4, false)]
  | 4, 2 => [(4, false)]
  | 4, 3 => [(4, false), (7, false)]
  | 5, 0 => [(5, false), (6, false)]
  | 5, 1 => [(5, false)]
  | 5, 2 => [(5, false), (7, false)]
  | 5, 3 => [(5, false)]
  | 5, 4 => [(5, false)]
  | 6, 0 => [(6, false), (5, false), (6, false)]
  | 6, 1 => [(6, false), (7, false)]
  | 6, 2 => [(6, false)]
  | 6, 3 => [(6, false)]
  | 6, 4 => [(6, false)]
  | 6, 5 => [(6, false)]
  | 7, 0 => [(7, false)]
  | 7, 1 => [(7, false)]
  | 7, 2 => [(7, false)]
  | 7, 3 => [(7, false)]
  | 7, 4 => [(7, false)]
  | 7, 5 => [(7, false)]
  | 7, 6 => [(7, false)]
  | _, _ => []

/-- Carry word for f_i^{pcRange i} (in later generators). -/
def carryWord (i : Nat) : List (Nat × Bool) := match i with
  | 3 => [(7, false)]
  | 4 => [(7, false)]
  | _ => []

/-- Expansion of an inverse generator into positive atoms. -/
def invAtomWord (i : Nat) : List (Nat × Bool) := match i with
  | 0 => [(0, false), (0, false)]
  | 3 => [(3, false), (7, false)]
  | 4 => [(4, false), (7, false)]
  | _ => [(i, false)]

def getExp (e : List Nat) (i : Nat) : Nat := e.getD i 0
def setExp (e : List Nat) (i v : Nat) : List Nat := e.set i v
def zeroExps : List Nat := [0, 0, 0, 0, 0, 0, 0, 0]

/-- Right-multiply the normal form `e` by the generator `f_j`,
    renormalizing via conjugation and power carries. The collector
    argument is used only for words in generators strictly above `j`. -/
def insertOne (collect : List Nat → List (Nat × Bool) → List Nat)
    (e : List Nat) (j : Nat) : List Nat :=
  let suffixWord : List (Nat × Bool) :=
    (List.range 8).foldl (fun w k =>
      if j < k then w ++ (List.replicate (getExp e k) (conjWord k j)).flatten else w) []
  let newe : List Nat := setExp e j ((getExp e j + 1) % pcRange j)
  let suffixWord : List (Nat × Bool) :=
    if getExp e j + 1 = pcRange j then carryWord j ++ suffixWord else suffixWord
  let suffix : List Nat := collect zeroExps suffixWord
  (List.range 8).foldl (fun v k => if j < k then setExp v k (getExp suffix k) else v) newe

/-- Expand an atom (possibly inverse) and collect it, given a collector
    for the inverse expansion. -/
def insertAtom (collect : List Nat → List (Nat × Bool) → List Nat)
    (e : List Nat) (a : Nat × Bool) : List Nat :=
  match a with
  | (g, false) => insertOne collect e g
  | (g, true) => collect e (invAtomWord g)

/-- Collect a word of atoms into the exponent list `e`, right-multiplying
    by each atom in turn. Structural recursion on the fuel; generator
    indices strictly increase along conjugation chains, so fuel 9
    suffices for 8 generators. -/
def collectWord : Nat → List Nat → List (Nat × Bool) → List Nat
  | _, e, [] => e
  | 0, e, _ => e
  | fuel + 1, e, a :: as => collectWord fuel (insertAtom (collectWord fuel) e a) as

/-- Encode an exponent list as a natural < 384 (mixed radix). -/
def encodeExps (e : List Nat) : Nat :=
  e.getD 0 0 + 3 * (e.getD 1 0 + 2 * (e.getD 2 0 + 2 * (e.getD 3 0 + 2 * (e.getD 4 0 + 2 * (e.getD 5 0 + 2 * (e.getD 6 0 + 2 * e.getD 7 0))))))

/-- Decode a natural < 384 into exponent digits. -/
def decodeExps (n : Nat) : List Nat :=
  let e0 := n % 3
  let n1 := n / 3
  let e1 := n1 % 2
  let n2 := n1 / 2
  let e2 := n2 % 2
  let n3 := n2 / 2
  let e3 := n3 % 2
  let n4 := n3 / 2
  let e4 := n4 % 2
  let n5 := n4 / 2
  let e5 := n5 % 2
  let n6 := n5 / 2
  let e6 := n6 % 2
  let e7 := n6 / 2
  [e0, e1, e2, e3, e4, e5, e6, e7]

/-- Right action of a word on an element, in encoded form. -/
def actWord (w : List (Nat × Bool)) (x : Fin 384) : Fin 384 :=
  ⟨encodeExps (collectWord 10000 (decodeExps x.1) w) % 384, Nat.mod_lt _ (Nat.succ_pos 383)⟩


def presentationWords : List (List (Nat × Bool)) := [
  [(0, false), (0, false), (0, false)],
  [(1, true), (0, true), (1, false), (0, false), (2, true)],
  [(2, true), (0, true), (2, false), (0, false), (2, true), (1, true)],
  [(3, true), (0, true), (3, false), (0, false), (7, true), (4, true), (3, true)],
  [(4, true), (0, true), (4, false), (0, false), (3, true)],
  [(5, true), (0, true), (5, false), (0, false), (6, true)],
  [(6, true), (0, true), (6, false), (0, false), (6, true), (5, true)],
  [(7, true), (0, true), (7, false), (0, false)],
  [(1, false), (1, false)],
  [(2, true), (1, true), (2, false), (1, false)],
  [(3, true), (1, true), (3, false), (1, false)],
  [(4, true), (1, true), (4, false), (1, false)],
  [(5, true), (1, true), (5, false), (1, false)],
  [(6, true), (1, true), (6, false), (1, false), (7, true)],
  [(7, true), (1, true), (7, false), (1, false)],
  [(2, false), (2, false)],
  [(3, true), (2, true), (3, false), (2, false)],
  [(4, true), (2, true), (4, false), (2, false)],
  [(5, true), (2, true), (5, false), (2, false), (7, true)],
  [(6, true), (2, true), (6, false), (2, false)],
  [(7, true), (2, true), (7, false), (2, false)],
  [(3, false), (3, false), (7, true)],
  [(4, true), (3, true), (4, false), (3, false), (7, true)],
  [(5, true), (3, true), (5, false), (3, false)],
  [(6, true), (3, true), (6, false), (3, false)],
  [(7, true), (3, true), (7, false), (3, false)],
  [(4, false), (4, false), (7, true)],
  [(5, true), (4, true), (5, false), (4, false)],
  [(6, true), (4, true), (6, false), (4, false)],
  [(7, true), (4, true), (7, false), (4, false)],
  [(5, false), (5, false)],
  [(6, true), (5, true), (6, false), (5, false)],
  [(7, true), (5, true), (7, false), (5, false)],
  [(6, false), (6, false)],
  [(7, true), (6, true), (7, false), (6, false)],
  [(7, false), (7, false)]
]
theorem presentationWords_length : presentationWords.length = 36 := rfl

/-- Every relator of the GAP presentation acts trivially on all 384
    elements of the polycyclic model: the action factors through the
    presented group. Checked by the Lean kernel (`decide`), one relator
    at a time: a single kernel `decide` over all 36 relators takes
    ~20 minutes, so the checks are split per relator. -/
theorem presentationAction_relator_01 :
    ∀ x : Fin 384, actWord [(0, false), (0, false), (0, false)] x = x := by decide

theorem presentationAction_relator_02 :
    ∀ x : Fin 384, actWord [(1, true), (0, true), (1, false), (0, false), (2, true)] x = x := by decide

theorem presentationAction_relator_03 :
    ∀ x : Fin 384, actWord [(2, true), (0, true), (2, false), (0, false), (2, true), (1, true)] x = x := by decide

theorem presentationAction_relator_04 :
    ∀ x : Fin 384, actWord [(3, true), (0, true), (3, false), (0, false), (7, true), (4, true), (3, true)] x = x := by decide

theorem presentationAction_relator_05 :
    ∀ x : Fin 384, actWord [(4, true), (0, true), (4, false), (0, false), (3, true)] x = x := by decide

theorem presentationAction_relator_06 :
    ∀ x : Fin 384, actWord [(5, true), (0, true), (5, false), (0, false), (6, true)] x = x := by decide

theorem presentationAction_relator_07 :
    ∀ x : Fin 384, actWord [(6, true), (0, true), (6, false), (0, false), (6, true), (5, true)] x = x := by decide

theorem presentationAction_relator_08 :
    ∀ x : Fin 384, actWord [(7, true), (0, true), (7, false), (0, false)] x = x := by decide

theorem presentationAction_relator_09 :
    ∀ x : Fin 384, actWord [(1, false), (1, false)] x = x := by decide

theorem presentationAction_relator_10 :
    ∀ x : Fin 384, actWord [(2, true), (1, true), (2, false), (1, false)] x = x := by decide

theorem presentationAction_relator_11 :
    ∀ x : Fin 384, actWord [(3, true), (1, true), (3, false), (1, false)] x = x := by decide

theorem presentationAction_relator_12 :
    ∀ x : Fin 384, actWord [(4, true), (1, true), (4, false), (1, false)] x = x := by decide

theorem presentationAction_relator_13 :
    ∀ x : Fin 384, actWord [(5, true), (1, true), (5, false), (1, false)] x = x := by decide

theorem presentationAction_relator_14 :
    ∀ x : Fin 384, actWord [(6, true), (1, true), (6, false), (1, false), (7, true)] x = x := by decide

theorem presentationAction_relator_15 :
    ∀ x : Fin 384, actWord [(7, true), (1, true), (7, false), (1, false)] x = x := by decide

theorem presentationAction_relator_16 :
    ∀ x : Fin 384, actWord [(2, false), (2, false)] x = x := by decide

theorem presentationAction_relator_17 :
    ∀ x : Fin 384, actWord [(3, true), (2, true), (3, false), (2, false)] x = x := by decide

theorem presentationAction_relator_18 :
    ∀ x : Fin 384, actWord [(4, true), (2, true), (4, false), (2, false)] x = x := by decide

theorem presentationAction_relator_19 :
    ∀ x : Fin 384, actWord [(5, true), (2, true), (5, false), (2, false), (7, true)] x = x := by decide

theorem presentationAction_relator_20 :
    ∀ x : Fin 384, actWord [(6, true), (2, true), (6, false), (2, false)] x = x := by decide

theorem presentationAction_relator_21 :
    ∀ x : Fin 384, actWord [(7, true), (2, true), (7, false), (2, false)] x = x := by decide

theorem presentationAction_relator_22 :
    ∀ x : Fin 384, actWord [(3, false), (3, false), (7, true)] x = x := by decide

theorem presentationAction_relator_23 :
    ∀ x : Fin 384, actWord [(4, true), (3, true), (4, false), (3, false), (7, true)] x = x := by decide

theorem presentationAction_relator_24 :
    ∀ x : Fin 384, actWord [(5, true), (3, true), (5, false), (3, false)] x = x := by decide

theorem presentationAction_relator_25 :
    ∀ x : Fin 384, actWord [(6, true), (3, true), (6, false), (3, false)] x = x := by decide

theorem presentationAction_relator_26 :
    ∀ x : Fin 384, actWord [(7, true), (3, true), (7, false), (3, false)] x = x := by decide

theorem presentationAction_relator_27 :
    ∀ x : Fin 384, actWord [(4, false), (4, false), (7, true)] x = x := by decide

theorem presentationAction_relator_28 :
    ∀ x : Fin 384, actWord [(5, true), (4, true), (5, false), (4, false)] x = x := by decide

theorem presentationAction_relator_29 :
    ∀ x : Fin 384, actWord [(6, true), (4, true), (6, false), (4, false)] x = x := by decide

theorem presentationAction_relator_30 :
    ∀ x : Fin 384, actWord [(7, true), (4, true), (7, false), (4, false)] x = x := by decide

theorem presentationAction_relator_31 :
    ∀ x : Fin 384, actWord [(5, false), (5, false)] x = x := by decide

theorem presentationAction_relator_32 :
    ∀ x : Fin 384, actWord [(6, true), (5, true), (6, false), (5, false)] x = x := by decide

theorem presentationAction_relator_33 :
    ∀ x : Fin 384, actWord [(7, true), (5, true), (7, false), (5, false)] x = x := by decide

theorem presentationAction_relator_34 :
    ∀ x : Fin 384, actWord [(6, false), (6, false)] x = x := by decide

theorem presentationAction_relator_35 :
    ∀ x : Fin 384, actWord [(7, true), (6, true), (7, false), (6, false)] x = x := by decide

theorem presentationAction_relator_36 :
    ∀ x : Fin 384, actWord [(7, false), (7, false)] x = x := by decide

end SemiabelianNonMonomial
