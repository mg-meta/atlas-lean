# Section 1 / Problem Statement: definitions

Reading order:

1. `A_OrientedGraphAndSwitching.lean` — oriented graphs as signed
   adjacency matrices (`IsOrientedMat`, `Adj`), switching (`switchMat`,
   matrix form $S_v A S_v$), relabelling (`permMat`), isomorphism
   (`MatIso`), same switching deck (`SameSwitchingDeck`) and switching
   non-reconstructibility (`IsSwitchingNonReconstructible`).
2. `B_DegreeProfile.lean` — out-/in-degree and the degree profile
   $P_G(v)$ (`degreeProfile`), with its isomorphism invariance
   (`degreeProfile_eq_of_iso`), used to show $D \not\cong H$.
