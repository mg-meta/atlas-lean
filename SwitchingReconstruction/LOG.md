# Work log — Switching Reconstruction formalization

## 2026-11-03 — Formalization created and verified

**Milestone report, in the order required by `AGENTS.md`:**

- **Proved (all verified in this session, no `sorry`, no `native_decide`,
  no extra axioms):** the full paper at $n=12$ —
  - Definitions: `IsOrientedMat`, `Adj`, `switchMat` (paper's $S_vAS_v$),
    `MatIso`, `SameSwitchingDeck`, `IsSwitchingNonReconstructible`,
    `degreeProfile` ($P_G(v)$) and its isomorphism invariance
    (`degreeProfile_eq_of_iso`).
  - `matD_isOrientedMat`, `matD_eq_zero_iff` (six non-adjacent pairs).
  - `matH_eq_matC` (switching $D$ at $0,1$ gives the printed $C$),
    `matH_isOrientedMat`, `matH_apply` (the exactly-one-in-$\{0,1\}$ rule).
  - `sameSwitchingDeck_matD_matH` ($\pi=(0\,1)(2\,5)(3\,4)(6\,7)(8\,11)(9\,10)$,
    the paper's $\psi_v$ table, deck identity checked entrywise).
  - `degreeProfile_matD_zero`, `degreeProfile_matH_two/four/six/nine`,
    `outdeg_matH_eq_four`, and `matD_not_iso_matH`.
  - Main results: `switching_nonreconstructible_matD`,
    `switchingQuestion12`, `exists_switching_nonreconstructible_ge_twelve`.
  - Axiom audit (`#print axioms` on the main theorems and components):
    only `propext`, `Classical.choice`, `Quot.sound`.
- **Still preliminary / `sorry`:** nothing in `Formalization/`. The only
  `sorry`s in this folder are the nine challenge-side placeholder proofs
  in `Comparator/switching_reconstruction_comparator.lean`, by design
  (identical to the Evolution Algebras comparator pattern); the comparator
  checks the solution against them.
- **Blocked:** nothing. Open items recorded in `GAPS.md` by decision:
  G1 (abstract's $n\ge12$ vs the $n=12$ proof — formalized as $n=12$ plus
  the existence corollary, per the user's decision), G2 (Further
  Questions Q1/Q2 are open problems in the paper), G3 (Kelly–Ulam is
  cited background, not formalized).

**Setup decisions (confirmed with the user before Lean):** folder
`SwitchingReconstruction/Formalization` mirroring
`Formalized Publications/Papers/EvolutionAlgebras/Formalization`; scope
= the paper as written ($n=12$); toolchain = install the pinned
Lean `v4.35.0` via elan and fetch the pinned Mathlib cache
(`lake exe cache get`) — pins unchanged, no `lake update`.

**Audit:** every finite claim of the paper was recomputed independently
in Python before Lean (skew-symmetry, entries, non-adjacent pairs,
out-neighbour lists, $C=\mathrm{switch}_{\{0,1\}}(A)$, bijectivity of
$\pi,\psi_v$, the deck identity for all $v,i,j$, $P_D(0)$, $H$'s
out-degree-4 vertices $\{2,4,6,9\}$ and their profiles). No discrepancy
found; see `PROOF_AUDIT.md`.

**Build:** all nine `Formalization` modules compiled in dependency order
with the pinned toolchain (commands in `Readme.md`); comparator file
elaborates with only its expected challenge-side `sorry` warnings.
Generated `.olean`s are gitignored build artifacts.

**Handoff:** to rebuild after edits, run the loop in `Readme.md`, then
re-run the axiom audit. Next step, if wanted: the comparator tool run
against `Comparator/switching_reconstruction_comparator.json`.

## 2026-11-03 — Interactive HTML created

- Created `switching_reconstruction_interactive.html`, modeled on
  `evolution_algebras_interactive.html`: same page/TOC/KaTeX layout,
  theorem-environment styling, Human margin regions and collapsible Lean
  boxes, with paper text and matrices from `Latex/main.tex`.
- Embedded 15 Lean boxes (23 source links) whose code is extracted from
  the verified files in `Formalization/`, covering the definitions, the
  question, $D$, $H$, the switching deck, the profile invariant,
  non-isomorphism and the main theorems.
- Validation in this session: HTML parser found balanced tags and no
  missing section anchors; all 32 local links resolve; the displayed
  matrices and all Lean theorem names were checked against the source
  files. A headless-Chrome screenshot could not be taken because macOS
  denied Chrome's sandbox bootstrap in this environment, so the rendered
  KaTeX layout has not been screenshot-verified here.
