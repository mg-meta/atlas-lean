/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Section 4: the degree-eight irreducible characters (GAP data)

The paper's GAP output lists 27 irreducible degrees
`[1,1,1,3,…,3,8,8,8]`. The three degree-eight irreducibles — the
witnesses behind `IsMonomialGroup: false` — were supplied as character
values on GAP's 27 conjugacy classes of
`((C₂ × ((C₂ × Q₈) ⋊ C₂)) ⋊ C₂) ⋊ C₃`:

* `degreeEightChar₁ = [8, -1, 0,…, -8, -1, 1, 0,…, 1, 0,…]`,
* `degreeEightChar₂`, with `-E(3)², -E(3), E(3)², E(3)` in place of
  `-1, -1, 1, 1` at positions 2, 7, 8, 18,
* `degreeEightChar₃`, the same with `E(3)` and `E(3)²` interchanged,

where `E(3) = e^{2πi/3}` is GAP's cyclotomic notation. The values are
recorded here in GAP's class ordering; the class representatives in
that order, as words in the presentation generators, are now recorded
in `C_GapCertificateData.lean` (`conjugacyClassReps`), so each list is
pinned to explicit conjugacy classes of `CounterexampleGroup` — though
the lists are still data, not yet Lean characters of the group.

Independent audit (Python, from the presented group of
`A_TrackedPreliminaries`): the presented group has exactly 27
conjugacy classes, of sizes `[1, 1, 6×21, 64×4]`, with center of order
2. For `degreeEightChar₁` the irreducibility equations
`Σ |χ(C)|²·|C| = 384` and `Σ χ(C)·|C| = 0` then have a *unique*
solution: the value `-8` sits on the nontrivial central class and the
four remaining nonzero values sit on the four 64-element classes. This
is consistent with genuine irreducible characters of the presented
group, but it is not a Lean proof that they are characters of
`CounterexampleGroup`, nor that they are non-induced; that remains the
blocked part of G1 (see `../../GAPS.md`).
-/

namespace SemiabelianNonMonomial

/-- `E(3) = e^{2πi/3} = (-1 + √-3)/2`, GAP's cyclotomic generator. -/
noncomputable def E3 : ℂ :=
  ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem E3_sq : E3 ^ 2 = ⟨-1 / 2, -Real.sqrt 3 / 2⟩ := by
  rw [pow_two]
  apply Complex.ext
  · simp only [E3, Complex.mk_mul_mk]
    rw [show Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 3 / 4 by
      rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num]
    norm_num
  · simp [E3, Complex.mk_mul_mk]
    ring

theorem E3_ne_neg_one : (E3 : ℂ) ≠ -1 := by
  intro h
  have him := congrArg Complex.im h
  simp [E3] at him

theorem E3_sq_ne_one : E3 ^ 2 ≠ 1 := by
  rw [E3_sq]
  intro h
  have him := congrArg Complex.im h
  simp at him

theorem neg_E3_sq_ne_neg_one : -E3 ^ 2 ≠ (-1 : ℂ) := by
  rw [E3_sq]
  intro h
  have him := congrArg Complex.im h
  simp at him

/-- First degree-eight irreducible character (GAP values, in GAP's
conjugacy-class order): nonzero exactly at positions 1, 2, 6, 7, 8, 18. -/
def degreeEightChar₁ : List ℂ :=
  [8, -1, 0, 0, 0, -8, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Second degree-eight irreducible character. -/
noncomputable def degreeEightChar₂ : List ℂ :=
  [8, -E3 ^ 2, 0, 0, 0, -8, -E3, E3 ^ 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, E3,
    0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Third degree-eight irreducible character. -/
noncomputable def degreeEightChar₃ : List ℂ :=
  [8, -E3, 0, 0, 0, -8, -E3 ^ 2, E3, 0, 0, 0, 0, 0, 0, 0, 0, 0, E3 ^ 2,
    0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem degreeEightChar₁_length : degreeEightChar₁.length = 27 := rfl

theorem degreeEightChar₂_length : degreeEightChar₂.length = 27 := rfl

theorem degreeEightChar₃_length : degreeEightChar₃.length = 27 := rfl

/-- The degree of each character: the value at the identity class
(first entry) is `8`. -/
theorem degreeEightChar₁_degree : degreeEightChar₁[0]'(by decide) = 8 := rfl

theorem degreeEightChar₂_degree : degreeEightChar₂[0]'(by decide) = 8 := rfl

theorem degreeEightChar₃_degree : degreeEightChar₃[0]'(by decide) = 8 := rfl

/-- The three degree-eight characters are pairwise distinct (they
already differ at the second class). -/
theorem degreeEightChar₁_ne_char₂ : degreeEightChar₁ ≠ degreeEightChar₂ := by
  intro h
  have h1 : degreeEightChar₁[1]? = degreeEightChar₂[1]? := by rw [h]
  simp [degreeEightChar₁, degreeEightChar₂] at h1
  exact E3_sq_ne_one h1.symm

theorem E3_ne_one : (E3 : ℂ) ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  simp [E3] at him

theorem degreeEightChar₁_ne_char₃ : degreeEightChar₁ ≠ degreeEightChar₃ := by
  intro h
  have h1 : degreeEightChar₁[1]? = degreeEightChar₃[1]? := by rw [h]
  simp [degreeEightChar₁, degreeEightChar₃] at h1
  exact E3_ne_one h1.symm

theorem degreeEightChar₂_ne_char₃ : degreeEightChar₂ ≠ degreeEightChar₃ := by
  intro h
  have h1 : degreeEightChar₂[1]? = degreeEightChar₃[1]? := by rw [h]
  simp [degreeEightChar₂, degreeEightChar₃] at h1
  -- h1 : -E3^2 = -E3, so E3^2 = E3, contradicting imaginary parts
  have h2 : E3 ^ 2 = E3 := by
    calc E3 ^ 2 = -(-E3 ^ 2) := by simp
    _ = -(-E3) := by rw [h1]
    _ = E3 := by simp
  rw [E3_sq] at h2
  have him := congrArg Complex.im h2
  simp [E3] at him
  have hpos : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

end SemiabelianNonMonomial
