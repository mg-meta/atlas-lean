/-
Copyright (c) 2026 Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Milana Golich
-/
import Section_1_Introduction.A_OrientedGraphAndSwitching
import Section_1_Introduction.B_DegreeProfile
import Section_2_ProblemStatement.A_ProblemStatement
import Section_3_Solution.A_TheDigraphD
import Section_3_Solution.B_TheDigraphH
import Section_3_Solution.C_SameSwitchingDeck
import Section_3_Solution.D_NotIsomorphic
import Section_3_Solution.E_MainTheorem

/-! # Switching reconstruction of oriented graphs — library root

Imports every paper-facing module above. Paper correspondence and source
layout: see `../Readme.md`.

Build (from the repository root, with the pinned toolchain):

```
LEAN_PATH="SwitchingReconstruction/Formalization:$LEAN_PATH" \
  lake env lean SwitchingReconstruction/Formalization/SwitchingReconstruction.lean
```
-/
