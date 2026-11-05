# Section 5: Computational model (route to discharging G1)

1. `A_PolycyclicModel.lean` — the polycyclic collection action on
   `Fin 384` (`actWord`, `collectWord`/`insertOne`), with the 36
   presentation relators checked by the Lean kernel
   (`presentationAction_relators`). The group operation on `Fin 384`,
   the homomorphism from `CounterexampleGroup`, the order argument,
   and the character theory are not yet built on this action; see
   `../../GAPS.md`, G1.
