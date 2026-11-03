/-
Copyright (c) 2026 Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Milana Golich
-/
import Section_1_Introduction.A_OrientedGraphAndSwitching
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

/-!
# Degree profiles: the isomorphism invariant `P_G(v)`

For the non-isomorphism argument (paper, "D is not isomorphic to H") we use
the invariant `P_G(v) = (outdeg v, sorted out-degrees over `N⁺(v)`, sorted
out-degrees over `N⁻(v)`)`. We formalize "sorted list" as a multiset, which
has the same content. The out-degree of `v` is the number of `+1`'s in row
`v` of the signed adjacency matrix; `N⁺(v)` (resp. `N⁻(v)`) is the set of
vertices `w` with entry `1` (resp. `-1`) in row `v` — note `A v w = -1` iff
`w → v`, by skew-symmetry.

The main result here is that `degreeProfile` is preserved by isomorphism:
`degreeProfile B (φ v) = degreeProfile A v` whenever `φ` is an isomorphism
from `A` to `B`. This is the formal content of the paper's sentence "Given
that an isomorphism preserves outdegrees of vertices and of their
neighbours, the multiset `{P_G(v) : v ∈ V}` would be invariant."
-/

namespace SwitchingReconstruction

/-- Out-degree of `v`: the number of `+1`'s in row `v`, i.e.
`|\{w : v → w\}|` (paper, "D is not isomorphic to H"). -/
def outdeg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun w => A v w = 1).card

/-- In-degree of `v`: the number of `-1`'s in row `v`, i.e.
`|\{u : u → v\}|` (paper, ibid.). Recorded for fidelity; the invariant
below uses the out-degrees of the in-neighbours directly. -/
def indeg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun w => A v w = -1).card

/-- The degree profile `P_G(v)` of the paper: out-degree of `v`, the
multiset of out-degrees over the out-neighbours `N⁺(v)`, and the multiset
of out-degrees over the in-neighbours `N⁻(v)`. Multisets play the role of
the paper's sorted lists. -/
def degreeProfile {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) :
    ℕ × Multiset ℕ × Multiset ℕ :=
  (outdeg A v,
    (Finset.univ.filter fun w => A v w = 1).val.map (outdeg A),
    (Finset.univ.filter fun w => A v w = -1).val.map (outdeg A))

/-- Under an isomorphism `φ : A ≃ B`, the row-`φ v` neighbours of sign `c`
in `B` are the `φ`-image of the row-`v` neighbours of sign `c` in `A`. -/
theorem filter_map_of_iso {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    (φ : Fin n ≃ Fin n) (hφ : ∀ i j, B (φ i) (φ j) = A i j) (v : Fin n) (c : ℤ) :
    (Finset.univ.filter fun w => B (φ v) w = c) =
      (Finset.univ.filter fun w => A v w = c).map φ.toEmbedding := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.coe_toEmbedding]
  constructor
  · intro hw
    refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
    have h := hφ v (φ.symm w)
    rw [φ.apply_symm_apply] at h
    rw [← h]
    exact hw
  · rintro ⟨u, hu, hwu⟩
    rw [← hwu]
    rw [hφ v u]
    exact hu

/-- An isomorphism preserves out-degrees: `outdeg B (φ v) = outdeg A v`. -/
theorem outdeg_eq_of_iso {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    (φ : Fin n ≃ Fin n) (hφ : ∀ i j, B (φ i) (φ j) = A i j) (v : Fin n) :
    outdeg B (φ v) = outdeg A v := by
  unfold outdeg
  rw [filter_map_of_iso φ hφ v 1, Finset.card_map]

/-- An isomorphism preserves the multiset of out-degrees over neighbours of
either sign, since it maps the neighbourhood bijectively and preserves the
out-degree of each neighbour. -/
theorem neighbour_multiset_eq_of_iso {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    (φ : Fin n ≃ Fin n) (hφ : ∀ i j, B (φ i) (φ j) = A i j) (v : Fin n) (c : ℤ) :
    (Finset.univ.filter fun w => B (φ v) w = c).val.map (outdeg B) =
      (Finset.univ.filter fun w => A v w = c).val.map (outdeg A) := by
  rw [filter_map_of_iso φ hφ v c, Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro u _
  exact outdeg_eq_of_iso φ hφ u

/-- **Isomorphism invariance of the degree profile** (paper, "D is not
isomorphic to H"): if `φ` is an isomorphism from `A` to `B`, then
`P_B(φ v) = P_A(v)` for every vertex `v`. -/
theorem degreeProfile_eq_of_iso {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    (φ : Fin n ≃ Fin n) (hφ : ∀ i j, B (φ i) (φ j) = A i j) (v : Fin n) :
    degreeProfile B (φ v) = degreeProfile A v := by
  unfold degreeProfile
  rw [outdeg_eq_of_iso φ hφ v, neighbour_multiset_eq_of_iso φ hφ v 1,
    neighbour_multiset_eq_of_iso φ hφ v (-1)]

end SwitchingReconstruction
