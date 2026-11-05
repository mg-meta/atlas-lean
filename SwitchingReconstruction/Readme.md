# Switching reconstruction of oriented graphs

A Lean 4 formalization of **Switching reconstruction of oriented graphs**
([Switching_Reconstruction.pdf](Papers/Switching_Reconstruction.pdf), LaTeX source
in [Latex/main.tex](Papers/Latex/main.tex)).

[Paper (PDF)](Papers/Switching_Reconstruction.pdf)
· [Interactive paper (HTML)](Papers/switching_reconstruction_interactive.html)

Please download the HTML file and open it in your browser. It presents the
paper with a Lean box for the definitions and results, following
`evolution_algebras_interactive.html`.

## About the paper

For a digraph $D$ and a vertex $v$, $\mathrm{switch}(D,v)$ reverses every
edge incident with $v$. Two digraphs have the *same switching deck* if some
bijection $\pi$ of vertices has $\mathrm{switch}(D,v) \cong
\mathrm{switch}(H,\pi(v))$ for all $v$, and $D$ is *switching
non-reconstructible* if some non-isomorphic $H$ has the same switching deck
as $D$. Bondy and Mercier (2011) asked whether a switching
non-reconstructible digraph exists on twelve or more vertices; the only
previously known examples had $4$ or $8$ vertices. This paper exhibits one
on $12$ vertices: an explicit oriented graph $D$ and the graph $H$ obtained
from it by switching at two vertices have the same switching deck but are
not isomorphic, distinguished by the degree profile invariant $P_G(v)$.

The table lists only the nine major results named in
[switching_reconstruction_comparator.json](Comparator/switching_reconstruction_comparator.json),
in that order — one row per theorem, with no other results listed.

| Result | Lean |
|---|---|
| $D$ is an oriented graph | `matD_isOrientedMat` in [A_TheDigraphD.lean](Formalization/Section_3_Solution/A_TheDigraphD.lean) |
| Switching $D$ at $0,1$ gives the printed matrix $C$ | `matH_eq_matC` in [B_TheDigraphH.lean](Formalization/Section_3_Solution/B_TheDigraphH.lean) |
| $H$ is an oriented graph | `matH_isOrientedMat` in [B_TheDigraphH.lean](Formalization/Section_3_Solution/B_TheDigraphH.lean) |
| Same switching deck, via $\pi$ and $\psi_v$ | `sameSwitchingDeck_matD_matH` in [C_SameSwitchingDeck.lean](Formalization/Section_3_Solution/C_SameSwitchingDeck.lean) |
| Degree profile $P_D(0) = (4, \{3, 6, 6, 6\}, \{4, 4, 4, 5, 5, 7\})$ | `degreeProfile_matD_zero` in [D_NotIsomorphic.lean](Formalization/Section_3_Solution/D_NotIsomorphic.lean) |
| $D \not\cong H$, via $P_D(0)$ vs $P_H$ at out-degree-$4$ vertices | `matD_not_iso_matH` in [D_NotIsomorphic.lean](Formalization/Section_3_Solution/D_NotIsomorphic.lean) |
| $D$ is switching non-reconstructible | `switching_nonreconstructible_matD` in [E_MainTheorem.lean](Formalization/Section_3_Solution/E_MainTheorem.lean) |
| Existence at $n=12$ | `switchingQuestion12` in [E_MainTheorem.lean](Formalization/Section_3_Solution/E_MainTheorem.lean) |
| Existence at some $n\ge12$ | `exists_switching_nonreconstructible_ge_twelve` in [E_MainTheorem.lean](Formalization/Section_3_Solution/E_MainTheorem.lean) |

## Layout

- [Formalization/](Formalization/) — the Lean formalization, organized by
  paper section in reading order, with the root module
  [SwitchingReconstruction.lean](Formalization/SwitchingReconstruction.lean).
- [Comparator/](Comparator/) — the comparator challenge
  ([switching_reconstruction_comparator.lean](Comparator/switching_reconstruction_comparator.lean)
  and its [JSON config](Comparator/switching_reconstruction_comparator.json)),
  restating the definitions independently of the solution, as in the
  Evolution Algebras formalization. Its placeholder proofs are the
  challenge side of the comparator, by design — the solution in
  `Formalization/` contains no placeholder proofs, no kernel-bypassing
  decision procedures, and only the standard axioms (checked with
  `#print axioms`).
- [Papers/](Papers/) — the paper, its LaTeX source, and the interactive
  HTML version.

## Building

With the pinned toolchain (Lean/Mathlib `v4.35.0`; do not run
`lake update`), from the repository root:

```sh
export PATH="$HOME/.elan/bin:$PATH"
F=SwitchingReconstruction/Formalization
export LEAN_PATH="$F"
for f in Section_1_Introduction/A_OrientedGraphAndSwitching \
         Section_1_Introduction/B_DegreeProfile \
         Section_2_ProblemStatement/A_ProblemStatement \
         Section_3_Solution/A_TheDigraphD \
         Section_3_Solution/B_TheDigraphH \
         Section_3_Solution/C_SameSwitchingDeck \
         Section_3_Solution/D_NotIsomorphic \
         Section_3_Solution/E_MainTheorem \
         SwitchingReconstruction; do
  lake env lean --root=$F -o $F/$f.olean $F/$f.lean
done
```

## Authorship

The paper was written by Milana Golich with Muse Spark and Watermelon via
meta.ai (see the paper's Statement of AI Use). The formalization was
orchestrated by Milana Golich with Muse Code, following
[AGENTS.md](../AGENTS.md).

## Versions

Lean `v4.35.0` and Mathlib `v4.35.0`, pinned at the top level of this
repository in [lean-toolchain](../lean-toolchain) and
[lakefile.toml](../lakefile.toml).
