/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Section_5_ComputationalModel.B_CollectLemmas
import Section_2_Preliminaries.A_TrackedPreliminaries

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-!
# The permutation homomorphism from the presented group

The polycyclic action is a *right* action: `actWord w x = x · (product
of w)`, so the map `g ↦ actWord [g]` is an anti-homomorphism. The
homomorphism into permutations is therefore given by the *inverse*
action: generator `fᵢ` acts by `actWord [fᵢ⁻¹]`. With this convention
the free-group homomorphism (`FreeGroup.lift`) sends a word to the
polycyclic action of its inverse word, and the 36 kernel-verified
relator identities (`presentationAction_relator_*`) show it kills
every relator, so it factors through `CounterexampleGroup`
(`PresentedGroup.toGroup`).

Conventions: word lists over `Nat` use `(g, false)` for a positive
generator and `(g, true)` for its inverse (the GAP/polycyclic
convention). `FreeGroup` words use the opposite Boolean convention
(`(a, true)` is `of a`). The bridge `actWordFin` reads a `Fin 8` word
in reverse order, which is exactly the inverse-action reading.
-/

namespace SemiabelianNonMonomial

/-- Encoding is inverse to decoding below 384. -/
theorem encode_decode (n : Nat) (hn : n < 384) : encodeExps (decodeExps n) = n := by
  simp [encodeExps, decodeExps]
  omega

/-- The empty word acts trivially. -/
theorem actWord_nil (x : Fin 384) : actWord [] x = x := by
  apply Fin.ext
  show encodeExps (collectWord 10000 (decodeExps x.1) []) % 384 = x.1
  rw [show collectWord 10000 (decodeExps x.1) [] = decodeExps x.1 from rfl,
    encode_decode x.1 x.2, Nat.mod_eq_of_lt hn]
  where
    hn : x.1 < 384 := x.2

/-- The action at an arbitrary fuel, for arguments that need more fuel
than the default 10000 (inverse words). -/
def actWordAt (F : Nat) (w : List (Nat × Bool)) (x : Fin 384) : Fin 384 :=
  ⟨encodeExps (collectWord F (decodeExps x.1) w) % 384, Nat.mod_lt _ (Nat.succ_pos 383)⟩

theorem actWordAt_append (F : Nat) (w₁ w₂ : List (Nat × Bool)) (x : Fin 384)
    (hats₁ : WordAtomsLt8 w₁) (hats₂ : WordAtomsLt8 w₂)
    (hF : wordBound (w₁ ++ w₂) ≤ F) :
    actWordAt F (w₁ ++ w₂) x = actWordAt F w₂ (actWordAt F w₁ x) := by
  have hvalid₁ : ValidExps (collectWord F (decodeExps x.1) w₁) :=
    collectWord_valid F w₁ (decodeExps x.1) (valid_decodeExps x.1 x.2) hats₁
  have hdec : decodeExps (actWordAt F w₁ x).1 = collectWord F (decodeExps x.1) w₁ := by
    have h1 : (actWordAt F w₁ x).1 =
        encodeExps (collectWord F (decodeExps x.1) w₁) % 384 := rfl
    rw [h1, Nat.mod_eq_of_lt (encodeExps_lt hvalid₁)]
    exact decode_encode hvalid₁
  apply Fin.ext
  show encodeExps (collectWord F (decodeExps x.1) (w₁ ++ w₂)) % 384 =
    encodeExps (collectWord F (decodeExps (actWordAt F w₁ x).1) w₂) % 384
  rw [hdec]
  rw [collectWord_append (decodeExps x.1) w₁ w₂ (valid_decodeExps x.1 x.2) hats₁ hats₂ hF]

theorem actWordAt_eq_actWord {F : Nat} (w : List (Nat × Bool)) (x : Fin 384)
    (hats : WordAtomsLt8 w) (hF : wordBound w ≤ F) (hF0 : wordBound w ≤ 10000) :
    actWordAt F w x = actWord w x := by
  apply Fin.ext
  show encodeExps (collectWord F (decodeExps x.1) w) % 384 =
    encodeExps (collectWord 10000 (decodeExps x.1) w) % 384
  rw [collectWord_fuel_eq (decodeExps x.1) w (valid_decodeExps x.1 x.2) hats hF hF0]

/-- Cancellation of a generator against its inverse, checked by `decide`. -/
theorem actWord_cancel (i : Fin 8) (x : Fin 384) :
    actWord [(i.1, true)] (actWord [(i.1, false)] x) = x := by
  have h : ∀ (i : Fin 8) (x : Fin 384),
      actWord [(i.1, true)] (actWord [(i.1, false)] x) = x := by decide
  exact h i x

theorem actWord_cancel' (i : Fin 8) (x : Fin 384) :
    actWord [(i.1, false)] (actWord [(i.1, true)] x) = x := by
  have h : ∀ (i : Fin 8) (x : Fin 384),
      actWord [(i.1, false)] (actWord [(i.1, true)] x) = x := by decide
  exact h i x

/-- Cancellation at fuel 30000, for the inverse-word argument. -/
theorem actWordAt_cancel (i : Fin 8) (b : Bool) (x : Fin 384) :
    actWordAt 30000 [(i.1, !b)] (actWordAt 30000 [(i.1, b)] x) = x := by
  have h : ∀ (i : Fin 8) (b : Bool) (x : Fin 384),
      actWordAt 30000 [(i.1, !b)] (actWordAt 30000 [(i.1, b)] x) = x := by decide
  exact h i b x

/-- The permutation given by one generator, in the inverse-action
convention: `genPerm i` is right multiplication by `fᵢ⁻¹`. -/
noncomputable def genPerm (i : Fin 8) : Equiv.Perm (Fin 384) where
  toFun := actWord [(i.1, true)]
  invFun := actWord [(i.1, false)]
  left_inv x := actWord_cancel' i x
  right_inv x := actWord_cancel i x

theorem genPerm_apply (i : Fin 8) (x : Fin 384) :
    genPerm i x = actWord [(i.1, true)] x := rfl

theorem genPerm_inv_apply (i : Fin 8) (x : Fin 384) :
    (genPerm i)⁻¹ x = actWord [(i.1, false)] x := rfl

/-- Every atom's step bound is small; in particular a single atom is
far below the action fuel. -/
theorem atomBound_le (a : Nat × Bool) (ha : a.1 < 8) : atomBound a ≤ 2000 := by
  obtain ⟨g, inv⟩ := a
  have hg : g < 8 := ha
  cases inv with
  | false =>
    simp only [atomBound]
    interval_cases g <;> simp [stepsAtom]
  | true =>
    simp only [atomBound]
    interval_cases g <;> simp [stepsAtom, pcRange]

theorem wordBound_singleton_le (a : Nat × Bool) (ha : a.1 < 8) :
    wordBound [a] ≤ 10000 := by
  rw [wordBound_cons, wordBound_nil, add_zero]
  have := atomBound_le a ha
  omega

/-- The word bound is monotone under taking prefixes. -/
theorem wordBound_append_le_left (w₁ w₂ : List (Nat × Bool)) :
    wordBound w₁ ≤ wordBound (w₁ ++ w₂) := by
  rw [wordBound_append]
  omega

/-- The inverse word: reverse with flipped signs. -/
def invWord (w : List (Nat × Bool)) : List (Nat × Bool) :=
  (w.map (fun a => (a.1, !a.2))).reverse

theorem invWord_cons (a : Nat × Bool) (w : List (Nat × Bool)) :
    invWord (a :: w) = invWord w ++ [(a.1, !a.2)] := by
  simp [invWord, List.map_cons, List.reverse_cons]

theorem wordBound_invWord_le (w : List (Nat × Bool)) (hats : WordAtomsLt8 w) :
    wordBound (invWord w) ≤ 2001 * w.length + wordBound w := by
  induction w with
  | nil => simp [invWord]
  | cons a as ih =>
    rw [invWord_cons, wordBound_append]
    have h1 : wordBound [(a.1, !a.2)] ≤ 2001 := by
      rw [wordBound_cons, wordBound_nil, add_zero]
      have h2 : atomBound (a.1, !a.2) ≤ 2000 :=
        atomBound_le (a.1, !a.2) (hats a (by simp))
      omega
    have h2 : wordBound (invWord as) ≤ 2001 * as.length + wordBound as :=
      ih (fun a' ha' => hats a' (by simp [ha']))
    have h3 : (a :: as).length = as.length + 1 := by simp
    rw [h3]
    have h4 : wordBound (a :: as) = atomBound a + 1 + wordBound as := wordBound_cons a as
    omega

/-- The inverse word acts as the inverse permutation, at fuel 30000. -/
theorem actWordAt_invWord (w : List (Nat × Bool)) (hats : WordAtomsLt8 w)
    (hwF : wordBound w ≤ 10000) (hlen : w.length ≤ 9) (x : Fin 384) :
    actWordAt 30000 (invWord w) (actWordAt 30000 w x) = x := by
  induction w generalizing x with
  | nil =>
    have h0 : actWordAt 30000 [] x = x := by
      apply Fin.ext
      show encodeExps (collectWord 30000 (decodeExps x.1) []) % 384 = x.1
      rw [show collectWord 30000 (decodeExps x.1) [] = decodeExps x.1 from rfl,
        encode_decode x.1 x.2, Nat.mod_eq_of_lt x.2]
    show actWordAt 30000 [] (actWordAt 30000 [] x) = x
    simp only [h0]
  | cons a as ih =>
    have hats_as : WordAtomsLt8 as := fun a' ha' => hats a' (by simp [ha'])
    have ha : a.1 < 8 := hats a (by simp)
    have hwF_as : wordBound as ≤ 10000 := by
      rw [wordBound_cons] at hwF
      omega
    have hlen_as : as.length ≤ 9 := by simp at hlen ⊢; omega
    have hlen_as8 : as.length ≤ 8 := by
      have h := hlen
      simp only [List.length_cons] at h
      omega
    have hats_inv : WordAtomsLt8 (invWord as) := by
      intro a' ha'
      simp only [invWord, List.mem_reverse, List.mem_map] at ha'
      obtain ⟨b, hb, rfl⟩ := ha'
      exact hats b (by simp [hb])
    have hats_single : WordAtomsLt8 [(a.1, !a.2)] := by
      intro a' ha'
      simp only [List.mem_singleton] at ha'
      rw [ha']
      exact ha
    have hats_a : WordAtomsLt8 [a] := by
      intro a' ha'
      simp only [List.mem_singleton] at ha'
      rw [ha']
      exact ha
    have hb1 : wordBound ((invWord as) ++ [(a.1, !a.2)]) ≤ 30000 := by
      rw [wordBound_append]
      have h1 := wordBound_invWord_le as hats_as
      have h2 : wordBound [(a.1, !a.2)] = atomBound (a.1, !a.2) + 1 := by
        rw [wordBound_cons, wordBound_nil, add_zero]
      have h3 : atomBound (a.1, !a.2) ≤ 2000 := atomBound_le _ ha
      have h4 : wordBound (a :: as) = atomBound a + 1 + wordBound as :=
        wordBound_cons a as
      omega
    have hb2 : wordBound ([a] ++ as) ≤ 30000 := by
      rw [wordBound_append]
      have h1 : wordBound [a] ≤ 2001 := by
        rw [wordBound_cons, wordBound_nil, add_zero]
        have h3 : atomBound a ≤ 2000 := atomBound_le a ha
        omega
      omega
    rw [invWord_cons]
    have key : actWordAt 30000 ((invWord as) ++ [(a.1, !a.2)])
        (actWordAt 30000 (a :: as) x) =
      actWordAt 30000 [(a.1, !a.2)]
        (actWordAt 30000 (invWord as) (actWordAt 30000 as (actWordAt 30000 [a] x))) := by
      calc actWordAt 30000 ((invWord as) ++ [(a.1, !a.2)])
            (actWordAt 30000 (a :: as) x)
          = actWordAt 30000 [(a.1, !a.2)]
              (actWordAt 30000 (invWord as) (actWordAt 30000 (a :: as) x)) :=
            actWordAt_append 30000 (invWord as) [(a.1, !a.2)] _ hats_inv hats_single hb1
        _ = actWordAt 30000 [(a.1, !a.2)]
              (actWordAt 30000 (invWord as)
                (actWordAt 30000 as (actWordAt 30000 [a] x))) := by
            have happ : actWordAt 30000 (a :: as) x =
                actWordAt 30000 as (actWordAt 30000 [a] x) :=
              actWordAt_append 30000 [a] as x hats_a hats_as hb2
            rw [happ]
    rw [key, ih hats_as hwF_as hlen_as]
    show actWordAt 30000 [(a.1, !a.2)] (actWordAt 30000 [(a.1, a.2)] x) = x
    exact actWordAt_cancel ⟨a.1, ha⟩ a.2 x

/-- The action of a `Fin 8`-indexed word, and its step bound. The word
is read in reverse order, since the inverse action reverses the
product. -/
def actWordFin (w : List (Fin 8 × Bool)) (x : Fin 384) : Fin 384 :=
  actWord (List.reverse (w.map (fun a => (a.1.1, a.2)))) x

def wordBoundFin (w : List (Fin 8 × Bool)) : Nat :=
  wordBound (w.map (fun a => (a.1.1, a.2)))

theorem wordBoundFin_cons (a : Fin 8 × Bool) (w : List (Fin 8 × Bool)) :
    wordBoundFin (a :: w) = atomBound (a.1.1, a.2) + 1 + wordBoundFin w := by
  simp [wordBoundFin, List.map_cons, List.reverse_cons, wordBound_append, wordBound_cons,
    wordBound, List.map_reverse, List.sum_reverse]

/-- The word permutation: the free-group homomorphism induced by the
generator permutations (inverse-action convention). -/
noncomputable def wordPerm : FreeGroup (Fin 8) →* Equiv.Perm (Fin 384) :=
  FreeGroup.lift (fun i => genPerm i)

theorem perm_mul_apply (f g : Equiv.Perm (Fin 384)) (x : Fin 384) :
    (f * g) x = f (g x) := rfl

/-- Applying a word permutation is the polycyclic action of the
inverse word. -/
theorem wordPerm_apply (w : List (Fin 8 × Bool)) (hF : wordBoundFin w ≤ 10000)
    (x : Fin 384) :
    wordPerm (FreeGroup.mk w) x = actWordFin w x := by
  induction w generalizing x with
  | nil =>
    simp only [wordPerm, FreeGroup.lift_mk, List.map_nil, List.prod_nil, actWordFin,
      List.map_nil, List.reverse_nil]
    rw [actWord_nil]
    rfl
  | cons a as ih =>
    have hprod : List.prod (as.map (fun x => cond x.2 (genPerm x.1) (genPerm x.1)⁻¹)) =
        wordPerm (FreeGroup.mk as) := by
      rw [wordPerm, FreeGroup.lift_mk]
    rw [wordPerm, FreeGroup.lift_mk, List.map_cons, List.prod_cons, hprod, perm_mul_apply]
    have hFas : wordBoundFin as ≤ 10000 := by
      rw [wordBoundFin_cons] at hF
      omega
    have hfin : actWordFin (a :: as) x =
        actWord [(a.1.1, a.2)] (actWordFin as x) := by
      unfold actWordFin
      rw [List.map_cons, List.reverse_cons]
      exact (actWord_append (List.reverse (as.map (fun b => (b.1.1, b.2))))
        [(a.1.1, a.2)] x ?_ ?_ ?_).symm
      · intro a' ha'
        rw [List.mem_reverse] at ha'
        rw [List.mem_map] at ha'
        obtain ⟨b, hb, rfl⟩ := ha'
        exact b.1.2
      · intro a' ha'
        simp only [List.mem_singleton] at ha'
        rw [ha']
        exact a.1.2
      · have h2 : wordBound (List.reverse (as.map (fun b => (b.1.1, b.2))) ++
            [(a.1.1, a.2)]) = wordBoundFin (a :: as) := by
          rw [wordBoundFin, List.map_cons, List.reverse_cons, wordBound_append]
          simp [wordBound, List.map_reverse, List.sum_reverse]
        rw [h2]
        exact hF
    rw [hfin]
    cases hb : a.2 with
    | false =>
      have h1 : (cond a.2 (genPerm a.1) (genPerm a.1)⁻¹) (wordPerm (FreeGroup.mk as) x) =
          actWord [(a.1.1, true)] (actWordFin as x) := by
        rw [hb]
        simp only [Bool.cond_false, genPerm_inv_apply, ih hFas]
      rw [h1]
    | true =>
      have h1 : (cond a.2 (genPerm a.1) (genPerm a.1)⁻¹) (wordPerm (FreeGroup.mk as) x) =
          actWord [(a.1.1, false)] (actWordFin as x) := by
        rw [hb]
        simp only [Bool.cond_true, genPerm_apply, ih hFas]
      rw [h1]

end SemiabelianNonMonomial
