# Error and gap ledger — Semiabelian Non-Monomial

Per `AGENTS.md`: every error, gap or ambiguity in the paper, why it
matters, and the decision taken.

## G1. The counterexample is a GAP computation, not a human proof (BLOCKING for a `sorry`-free main theorem)

- **As written.** $G=\texttt{SmallGroup}(384,20127)$ is asserted
  semiabelian and non-monomial on the basis of GAP output (Appendix
  A.2/A.3). The displayed isomorphism
  $((C_2\times((C_2\times Q_8)\rtimes C_2))\rtimes C_2)\rtimes C_3$ does
  not specify any of the semidirect-product actions, so it does not
  determine a group. No character-theoretic argument for
  non-monomiality is given; the irreducible degrees
  $[1,1,1,3,\dots,3,8,8,8]$ are GAP output.
- **Why it matters.** Lean (Mathlib v4.35.0) has no SmallGroups library
  and no `IsMonomial` decision procedure. Rebuilding $G$ in Lean would
  require (i) the actual actions/permutation representation of
  SmallGroup(384,20127), which the paper does not contain, and (ii) a
  from-scratch character-theoretic proof of non-monomiality for a group
  of order 384.
- **Decision (this session, per `AGENTS.md` preliminaries policy).**
  The single GAP-verified fact — *there exists a finite group of order
  384 that is semiabelian and not monomial* — is isolated as one tracked
  preliminary in
  `Formalization/Section_2_Preliminaries/A_TrackedPreliminaries.lean`.
  The main theorem (`¬ KidaConjecture`) is proved in Lean from it.
  Everything else in the paper is formalized and proved.
- **Update (generators/presentation supplied by the user).** The GAP
  presentation on generators $f_1,\dots,f_8$ with 36 relators was
  supplied and is now pinned in Lean as `counterexampleRelators` /
  `CounterexampleGroup` (`PresentedGroup` on `Fin 8`), token-for-token
  identical to the supplied data (checked mechanically). An independent
  Todd–Coxeter enumeration of this presentation (cosets of the trivial
  subgroup, implemented from scratch for this audit) closes with
  exactly **384** cosets, and the generator orders are
  $3,2,2,4,4,2,2,2$, consistent with the paper's group. The tracked
  preliminary is now `presentedGroup_counterexample` (order,
  semiabelianity and non-monomiality of this explicit presented group);
  `counterexample_exists` is proved from it.
- **Update (character data supplied).** The three degree-eight
  irreducible characters of $G$ were supplied (values on GAP's 27
  conjugacy classes) and are recorded in Lean in
  `Formalization/Section_4_Counterexample/B_CharacterData.lean`
  (with kernel-checked length, degree and pairwise distinctness).
  Independent audit from the presentation: the presented group has
  exactly 27 conjugacy classes, of sizes $[1,1,6^{21},64^4]$ with
  center of order 2, and the irreducibility equations for the first
  character have a *unique* size assignment (the $-8$ value on the
  nontrivial central class, the other nonzero values on the four
  64-element classes) — consistent with genuine irreducibles, but not
  a Lean proof.
- **Update (GAP accessed directly).** We built GAP 4.16.1 from source
  locally and re-verified every GAP claim of the paper ourselves:
  `IdGroup = [384, 20127]`, solvable, `IsMonomialGroup = false`, only
  the three degree-eight irreducibles non-monomial, the Dentzer chain
  (identical in shape to the paper's), and the subgroup orders
  $[1,2,3,4,6,8,12,16,24,32,64,96,128,384]$. The Dentzer chain
  subgroups and the 27 conjugacy-class representatives are now
  recorded in Lean as words in the $f_i$
  (`Formalization/Section_4_Counterexample/C_GapCertificateData.lean`),
  and GAP's `IsomorphismFpGroup` relators are exactly the supplied
  presentation, so the identification of `CounterexampleGroup` with
  `SmallGroup(384, 20127)` is GAP's own isomorphism. The
  non-monomiality certificate is now human-readable: a degree-eight
  irreducible induced from a linear character would need a subgroup
  of index 8, and $G$ has no subgroup of order 48 at all.
- **Update (computational model, kernel-verified).** A polycyclic
  collection model of the group now exists in Lean:
  `Formalization/Section_5_ComputationalModel/A_PolycyclicModel.lean`
  defines the normal-form action `actWord` on `Fin 384` (exponent
  ranges `[3,2,2,2,2,2,2,2]`, conjugation/power tables read off the
  presentation; the collector was validated in Python against the
  full Todd–Coxeter multiplication table: 0 mismatches) and proves
  all 36 relator identities (`presentationAction_relator_01` … `_36`,
  each `by decide`, depending only on `propext`). Two obstacles were
  found and fixed on the way: the fuel bound must cover the whole
  conjugation chain (measured maximum 84 collector steps; fuel 200),
  and one combined `decide` over all 36 relators does not finish in
  reasonable time (a single relator costs ~35s of kernel time), so
  the checks are split per relator (full file build: 5m36s).
- **Still blocked.** What remains is building, on top of this
  action: a group operation on `Fin 384` (or an equivalent
  permutation model) with a homomorphism from `CounterexampleGroup`
  (`PresentedGroup`), the order/cardinality argument, transport of
  `IsSemiabelian`/`IsMonomial` across the isomorphism, and the
  character-theoretic non-monomiality argument (degree-eight
  irreducibles, no index-8 subgroup) — or acceptance of the GAP
  verdict as a permanent tracked preliminary. Until then
  `presentedGroup_counterexample` stays a tracked `sorry`. Status:
  **blocked on that build/decision; the computational model is done
  and kernel-verified.**

## G2. Cited theorems are used as black boxes in the paper

Dentzer's characterization (Thm 2.3), Dornhoff's theorem (Thm 2.6),
Kida's Theorem 1.4, Kida's Lemma 2.5 and van der Waall's Theorem 2 are
quoted from the literature, not proved in the paper. Their *statements*
are formalized; their proofs are tracked preliminaries in the same file
as G1 (standard `AGENTS.md` treatment of external results). The two
lemmas the paper *does* prove (pullback, conjugation) are proved in
Lean — pullback modulo Dentzer (as in the paper), conjugation from the
definitions. Status: decided, tracked.

## G3. Minor textual issues (recorded, not silently fixed)

- Lemma (conjugation) in the paper says "let $A\lhd G$ be a normal
  abelian group" (should be *subgroup*); the Lean statement uses
  subgroups throughout.
- The pullback proof ends "…which implies that $M$ is semiabelian"
  without naming that this is Dentzer's criterion applied inside $M$;
  the Lean proof makes that step explicit.
- `Latex/code/IsNAM.tex`, `IsWAM.tex`, `HilbertBasisMonomial.tex` are
  not included by the paper and are not formalized (see audit).
