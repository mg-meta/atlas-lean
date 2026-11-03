/-
Copyright (c) 2026 Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Milana Golich
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

/-!
# Section 1 / Problem Statement: oriented graphs and switching

Definitions for the paper *Switching reconstruction of oriented graphs*
(`Switching_Reconstruction.pdf`, Problem Statement and Solution).

An **oriented graph** is a digraph with no loops and no symmetric pairs of
edges. The paper represents an oriented graph on `n` vertices by its signed
adjacency matrix `A`, which is skew-symmetric (`Aᵀ = -A`) with entries
`A i j ∈ {-1, 0, 1}` and `A i i = 0`; here `A i j = 1` means `i → j`.
We take that matrix representation as the definition (`IsOrientedMat`), and
derive the usual adjacency relation (`Adj`) from it.

**Switching** in `D` about `v` reverses every edge incident with `v`. In
matrix form (paper, Solution) this is conjugation by the diagonal sign
matrix `S v`: `switchMat A v = S v * A * S v`, i.e. row and column `v` are
multiplied by `-1`. We define it directly by that formula.

## Main definitions

* `IsOrientedMat`: a signed adjacency matrix of an oriented graph.
* `Adj`: the adjacency relation `A i j = 1` of such a matrix.
* `switchSign`, `switchMat`: switching about a vertex.
* `permMat`: relabelling a matrix by a function on vertices.
* `MatIso`: isomorphism of oriented graphs (signed-matrix form).
* `SameSwitchingDeck`: same switching deck, as defined in the paper.
* `IsSwitchingNonReconstructible`: switching non-reconstructibility.
-/

namespace SwitchingReconstruction

/-- A signed adjacency matrix of an oriented graph (paper, Solution):
skew-symmetric with entries in `{-1, 0, 1}`. The diagonal condition
`A i i = 0` follows, see `IsOrientedMat.diag_eq_zero`. -/
def IsOrientedMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, A i j = -A j i) ∧ ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1

/-- The adjacency relation of an oriented graph: `Adj A i j` means `i → j`,
i.e. the signed adjacency entry is `1`. -/
def Adj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : Prop :=
  A i j = 1

namespace IsOrientedMat

theorem diag_eq_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : IsOrientedMat A)
    (i : Fin n) : A i i = 0 := by
  have h := hA.1 i i
  omega

theorem adj_irrefl {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : IsOrientedMat A)
    (i : Fin n) : ¬ Adj A i i := by
  simp [Adj, hA.diag_eq_zero i]

theorem adj_asymm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : IsOrientedMat A)
    {i j : Fin n} : Adj A i j → ¬ Adj A j i := by
  intro h
  have hskew := hA.1 i j
  simp [Adj] at h ⊢
  omega

end IsOrientedMat

/-- The sign of vertex `i` when switching about `v`: `-1` at `v`, `1` elsewhere.
This is the diagonal entry of the paper's switching matrix `S v`. -/
def switchSign {n : ℕ} (v i : Fin n) : ℤ :=
  if i = v then -1 else 1

theorem switchSign_eq_one_or_neg_one {n : ℕ} (v i : Fin n) :
    switchSign v i = 1 ∨ switchSign v i = -1 := by
  by_cases h : i = v <;> simp [switchSign, h]

theorem switchSign_mul_self {n : ℕ} (v i : Fin n) :
    switchSign v i * switchSign v i = 1 := by
  by_cases h : i = v <;> simp [switchSign, h]

/-- Switching a signed adjacency matrix about `v` (paper, Solution):
`switchMat A v = S v * A * S v`, i.e. every edge incident with `v` is
reversed and all other signed entries are unchanged. Edges not incident
with `v`, non-edges and the (zero) diagonal are fixed. -/
def switchMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => switchSign v i * A i j * switchSign v j

theorem switchMat_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (v i j : Fin n) :
    switchMat A v i j = switchSign v i * A i j * switchSign v j :=
  rfl

/-- Switching preserves oriented graphs: `switchMat A v` is again a signed
adjacency matrix of an oriented graph. -/
theorem IsOrientedMat.switchMat {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hA : IsOrientedMat A) (v : Fin n) : IsOrientedMat (switchMat A v) := by
  constructor
  · intro i j
    rw [switchMat_apply, switchMat_apply, hA.1 i j]
    ring
  · intro i j
    rw [switchMat_apply]
    rcases switchSign_eq_one_or_neg_one v i with hi | hi <;>
      rcases switchSign_eq_one_or_neg_one v j with hj | hj <;>
      rcases hA.2 i j with h | h | h <;> rw [hi, hj, h] <;> decide

/-- Relabelling a matrix by a function `φ` on vertices: the `(i, j)` entry
of `permMat A φ` is `A (φ i) (φ j)`. For a bijection `φ` this is conjugation
by the permutation matrix of `φ`, as in the paper. -/
def permMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → Fin n) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => A (φ i) (φ j)

theorem permMat_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → Fin n)
    (i j : Fin n) : permMat A φ i j = A (φ i) (φ j) :=
  rfl

/-- Isomorphism of oriented graphs in signed-matrix form (paper: `≅`):
a bijection `φ` of vertices with `B (φ i) (φ j) = A i j` for all `i, j`. -/
def MatIso {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ φ : Fin n ≃ Fin n, ∀ i j, B (φ i) (φ j) = A i j

theorem MatIso.refl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : MatIso A A :=
  ⟨Equiv.refl _, fun _ _ => rfl⟩

/-- Same switching deck (paper, Problem Statement): a bijection
`π : V(D) → V(H)` such that `switch(D, v) ≅ switch(H, π v)` for every `v`. -/
def SameSwitchingDeck {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ π : Fin n ≃ Fin n, ∀ v, MatIso (switchMat A v) (switchMat B (π v))

/-- Switching non-reconstructibility (paper, Problem Statement): some
oriented graph `H`, not isomorphic to `D`, has the same switching deck. -/
def IsSwitchingNonReconstructible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) ℤ, IsOrientedMat B ∧ SameSwitchingDeck A B ∧ ¬ MatIso A B

end SwitchingReconstruction
