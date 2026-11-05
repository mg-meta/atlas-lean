/-
Copyright (c) 2026 Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Milana Golich
-/
import Section_3_Solution.C_SameSwitchingDeck
import Section_3_Solution.D_NotIsomorphic
import Section_2_ProblemStatement.A_ProblemStatement

/-!
# Section 3 (Solution): Conclusion

Assembly of the paper's conclusion: the oriented graphs `D` (`matD`) and
`H` (`matH`) on `12` vertices have the same switching deck
(`sameSwitchingDeck_matD_matH`) but are not isomorphic
(`matD_not_iso_matH`). Therefore `D` is a switching non-reconstructible
oriented graph on `12` vertices, answering the Bondy–Mercier question:
such a digraph exists on twelve (hence on some `≥ 12`) vertices.

The paper's Further Questions Q1 and Q2 are open problems and are not
formalized.
-/

namespace SwitchingReconstruction

/-- **`D` is switching non-reconstructible** (paper, Conclusion): the
oriented graph `H`, obtained from `D` by switching at `v₀` and `v₁`, has
the same switching deck as `D` but is not isomorphic to `D`. -/
theorem switching_nonreconstructible_matD : IsSwitchingNonReconstructible matD :=
  ⟨matH, matH_isOrientedMat, sameSwitchingDeck_matD_matH, matD_not_iso_matH⟩

/-- **Main theorem, order 12**: there exist oriented graphs on `12`
vertices with the same switching deck that are not isomorphic. -/
theorem switchingQuestion12 : SwitchingQuestion12 :=
  ⟨matD, matH, matD_isOrientedMat, matH_isOrientedMat,
    sameSwitchingDeck_matD_matH, matD_not_iso_matH⟩

/-- **Main theorem** (paper, Abstract and Conclusion): there exists a
switching non-reconstructible oriented graph on `n ≥ 12` vertices —
namely on `n = 12` vertices. This answers the Bondy–Mercier question
(`SwitchingQuestion`) as posed in the paper. The stronger reading "for
every `n ≥ 12`" is not in the paper. -/
theorem exists_switching_nonreconstructible_ge_twelve : SwitchingQuestion :=
  ⟨12, le_refl 12, matD, matH, matD_isOrientedMat, matH_isOrientedMat,
    sameSwitchingDeck_matD_matH, matD_not_iso_matH⟩

end SwitchingReconstruction
