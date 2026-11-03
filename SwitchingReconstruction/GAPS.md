# Error and gap ledger — Switching Reconstruction

Per `AGENTS.md`: every error, gap or ambiguity in the paper, with the
statement as written, why it is unclear, and the decision taken. The
corresponding workstream was not continued past the gap until decided.

## G1. Abstract says $n\ge 12$; the proof gives only $n=12$

- **As written.** Abstract: "We prove the existence of a switching,
  non-reconstructible digraph on $n \ge 12$ vertices." The Solution section
  exhibits a single pair on $12$ vertices. No construction for general
  $n\ge 12$ (e.g. by adding isolated or duplicated structure) is given, and
  switching decks do not obviously extend from $12$ to larger orders.
- **Why it matters.** Formalizing "for every $n\ge 12$ there exists …" would
  require new mathematics not in the paper.
- **Decision (user, 2026-11-03).** Formalize the paper as written: the
  $n=12$ example, plus the existence corollary "there is some $n\ge 12$ …"
  witnessed by $n=12$. The "for every $n\ge 12$" reading is *not* claimed in
  Lean. Status: decided, formalized accordingly.

## G2. Further Questions Q1 and Q2 are open problems

- **As written.** The paper ends with Q1 (characterize switching
  non-reconstructible digraphs) and Q2 (are they restricted to oriented
  graphs for $n\ge 12$, and which arise). Both are posed as questions.
- **Decision.** Recorded here as open; not formalized as theorems. No Lean
  statement asserts an answer. Status: open in the paper, out of scope.

## G3. Background conjectures are cited, not proved

- Kelly–Ulam graph reconstruction conjecture (Introduction) and the
  Bondy–Mercier / McKay–Schweitzer context are background citations. The
  Bondy–Mercier *question* ("does there exist a switching,
  non-reconstructible digraph on twelve or more vertices?") is formalized
  as a `Prop` (`Section_2_ProblemStatement`) and answered by the main
  theorem. The Kelly–Ulam conjecture itself is not a result of this paper
  and is not formalized; it is only mentioned in file documentation.
  Status: decided (scope confirmed with the user, 2026-11-03).

## No gaps found in the main argument

All finite claims were independently recomputed (see `PROOF_AUDIT.md`):
skew-symmetry and entries of $A$ and $C$; the six non-adjacent pairs; the
out-neighbour lists of $D$; $C=\mathrm{switch}_{\{0,1\}}(A)$; bijectivity of
$\pi$ and of every $\psi_v$; the deck identity
$[D_v]_{ij}=[H_{\pi(v)}]_{\psi_v(i),\psi_v(j)}$ for all $v,i,j$;
$P_D(0)$, the out-degree-$4$ vertices $\{2,4,6,9\}$ of $H$, and their
profiles. No discrepancy with the paper was found.
