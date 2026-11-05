/-
Copyright (c) 2026 Joseph Phillip Brennan and Milana Golich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Phillip Brennan, Milana Golich
-/
import Section_1_Introduction.A_SemiabelianDefinition
import Section_1_Introduction.B_MonomialDefinition
import Section_1_Introduction.C_KidaConjecture
import Section_2_Preliminaries.A_TrackedPreliminaries
import Section_3_SearchStrategy.A_IsoInvariance
import Section_3_SearchStrategy.B_PullbackLemma
import Section_3_SearchStrategy.C_ConjugationLemma
import Section_4_Counterexample.A_Counterexample
import Section_4_Counterexample.B_CharacterData
import Section_4_Counterexample.C_GapCertificateData
import Section_5_ComputationalModel.A_PolycyclicModel

/-! # Semiabelian groups need not be monomial — library root

Imports every paper-facing module above. Paper correspondence and source
layout: see `../Readme.md`; natural-language proof and audit:
`../PROOF_AUDIT.md`; gaps (in particular the tracked GAP preliminary,
G1): `../GAPS.md`; work log: `../LOG.md`.

The only `sorry`s in this formalization are the six tracked
preliminaries in `Section_2_Preliminaries/A_TrackedPreliminaries.lean`
(five results quoted from the literature and the paper's GAP
computation), each with its exact source. Everything else is proved.

Build (from the repository root, with the pinned toolchain):

```
F=Kourovka21.68/Papers/Formalization
LEAN_PATH="$F" lake env lean --root=$F \
  -o $F/SemiabelianNonMonomial.olean $F/SemiabelianNonMonomial.lean
```

(after compiling the imported modules in dependency order the same way).
-/
