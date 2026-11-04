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

## 2026-11-04 — Human + AI sidebar added to Problem Statement + Solution

**What was done (user's direct instruction; overrides AGENTS.md
"originals are read-only" for this paper source):** the `collabblock`
Human + AI sidebar from `Temp_Packages.zip` (both papers there —
`Ruel_Anderson_Second_Derivatve.tex` and
`Uniform_Real_Zero_Bounds_Constant.tex` — define it identically in the
paper preamble, not in `stylelibrary.tex`) was copied verbatim into
`Papers/Latex/main.tex`: teal `collabcolor` (HTML `129B8F`), breakable
`tcolorbox` with the same `linemargin`/`enhancebreak`/`footnoteformat`
mechanism as `humanblock`, vertical "Human + AI" label, plus
`\CollabLabel`. One continuous `collabblock` now spans the Problem
Statement and Solution sections (opens after `\section{Problem
Statement}`, `\section{Solution}` inside the box, closes after the
CONCLUSION, before Further Questions), matching the human sidebar
format. The Statement of AI Use sentence was extended to name the
joint marker. Only `main.tex` changed (27 insertions); `stylelibrary.tex`,
`flexart.sty`, and `bib.bib` untouched.
**Verified:** begin/end balance and brace balance checked;
`collabblock` body diffed identical to both example papers. **Not
verified:** no `pdflatex` exists on this machine (full-disk search
found none), so the rebuilt PDF was not produced or inspected here —
rebuild with `pdflatex` in `Papers/Latex/` and replace
`Switching_Reconstruction.pdf`.

## 2026-11-04 — PDF regenerated with the continuous Human + AI sidebar

**Build:** no `pdflatex` exists on this machine (full-disk search found
none; no Homebrew/cargo/docker). Installed Tectonic 0.17.0 (aarch64
macOS binary, user space, `/tmp/texinstall`) and built
`Papers/Latex/main.tex` with `tectonic -Z continue-on-errors` in a
scratch dir (`/tmp/switchbuild`); the output replaced
`Papers/Switching_Reconstruction.pdf` only after verification below.
**Pre-existing defect exposed by the sidebar, fixed:** `claim` was
used in the Solution but never declared (`\newtheorem{claim}` added
to `main.tex`). Outside a box the error was silently ignored; inside
the `collabblock` it broke tcolorbox capture. The claim now renders
as "Claim 3.1". The three remaining `flexart` author-note errors
(`orch`/`rev` undeclared, notes commented out) pre-date this work and
were left untouched; they are tolerated under continue-on-errors, as
in the original nonstopmode build.
**Verified on the rendered PDF (5 pages):** vector-geometry check
(teal `129B8F` fragments at one fixed left position on pages 1-5,
"Human + AI" label at each fragment) and visual inspection of pages
1, 2, 4, 5 — one continuous teal bar from Problem Statement through
the Conclusion, distinct green Human bars for Introduction and
Further Questions, all matrices, the psi table, profiles, and all 6
references intact. Engine note: this build is XeTeX/xdvipdfmx via
Tectonic, not the pdfTeX/TeX Live 2026 of the previous PDF, so fonts
differ slightly (80K vs 302K, same page count and content). Old PDF
kept at `/tmp/switchbuild/OLD_Switching_Reconstruction.pdf`.
