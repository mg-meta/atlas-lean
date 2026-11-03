# Section 3: Solution

Reading order:

1. `A_TheDigraphD.lean` — the matrix $A$ of $D$ (`matD`), $D$ oriented,
   and the six non-adjacent pairs.
2. `B_TheDigraphH.lean` — $H$ (`matH`) as $D$ switched at $0$ and $1$;
   checked against the printed matrix $C$ (`matH_eq_matC`); $H$ oriented.
3. `C_SameSwitchingDeck.lean` — $\pi$ (`piFun`) and the table $\psi_v$
   (`psiFun`); the deck identity (`deckMatrixEq`) and
   `sameSwitchingDeck_matD_matH`.
4. `D_NotIsomorphic.lean` — $P_D(0)$, the profiles at $H$'s
   out-degree-$4$ vertices, and `matD_not_iso_matH`.
5. `E_MainTheorem.lean` — assembly: `switching_nonreconstructible_matD`,
   `switchingQuestion12`, and
   `exists_switching_nonreconstructible_ge_twelve`.
