# Semiabelian groups need not be monomial — natural-language proof and audit

Paper: `Semiabelian_NonMonomial.pdf`, source `Latex/main with muse.tex`
(Brennan–Golich, with Muse Spark, October 2026; Kourovka Notebook
Problem 21.68). Literature in `Latex/bib.bib`; Kida's paper is in
`../References/KidaPaper.pdf`. This file is the natural-language proof in
dependency order, written before the Lean (per `AGENTS.md`).

## What the paper proves, and how

**Definitions.** A finite group $G$ is *semiabelian* if there is a chain
$G_0=1\le\cdots\le G_n=G$ with $G_{i+1}$ a quotient of $G_i\ltimes A_i$,
$A_i$ finite abelian (Definition 1). A group is *monomial* if every
irreducible complex representation is induced from a one-dimensional
representation of a subgroup.

**Kida's conjecture.** Every semiabelian group is monomial.

**Main theorem.** Semiabelian groups need not be monomial.

**Proof as given in the paper.** The proof is computational:
1. Dentzer's characterization (cited, Theorem 2.3 of Dentzer 1995): a
   nontrivial finite group is semiabelian iff $G=AM$ for some abelian
   normal $A\lhd G$ and a proper semiabelian subgroup $M$.
2. Two lemmas proved in the paper reduce the semiabelian check to maximal
   subgroups: (a) *pullback* — if $G=AU$ with $U$ semiabelian and
   $U\le M$ maximal, then $G=AM$ and $M$ is semiabelian (proof: Dedekind's
   modular law gives $M=(M\cap A)U$, and $M\cap A\lhd M$ is abelian, so
   $M$ is semiabelian by Dentzer's criterion applied inside $M$);
   (b) *conjugation* — semiabelianity is conjugation-invariant and
   $G=AM$ implies $G=AM^g$ (proof: $G=G^g=(AM)^g=A^gM^g=AM^g$ since
   $A\lhd G$).
3. GAP's `IsMonomialGroup` decides non-monomiality; a GAP search over the
   SmallGroups library finds $G=\texttt{SmallGroup}(384,20127)$, reported
   as $((C_2\times((C_2\times Q_8)\rtimes C_2))\rtimes C_2)\rtimes C_3$,
   semiabelian and non-monomial (Appendix output: order 384, solvable,
   `IsMonomialGroup: false`, `IsSemiabelian: true`, Irr degrees
   $[1,1,1,3,\dots,3,8,8,8]$).
4. A final GAP check exhibits the Dentzer chain
   $G=A_0M_0$, $M_0=A_1M_1$, $M_1=A_2M_2$, $M_2=A_3M_3$, $M_3=C_3$ with
   $A_0=A_1=A_2=C_2^3$, $A_3=C_2^2$, $M_0=((C_2^3\rtimes C_2^2)\rtimes C_3)$,
   $M_1=C_2\times A_4$, $M_2=A_4$. Each $A_i$ is abelian and $M_3=C_3$ is
   abelian, hence semiabelian; applying Dentzer's criterion backwards up
   the chain gives $G$ semiabelian. With (3), $G$ refutes the conjecture.

**Background formalized as statements only** (cited, not used in the
proof): modular $p$-groups, quaternion-free 2-groups, Dornhoff's theorem,
isoclinism, Kida's Theorem 1.4, and the direct-product lemmas of Kida
(Lemma 2.5) and van der Waall (Theorem 2) used in the paper's remark
about building more examples. The closing question (must a semiabelian
non-monomial group have a Sylow 2-subgroup containing $Q_8$?) is open.

## Audit findings

- The mathematical (non-computational) content — Dentzer-based pullback
  and conjugation lemmas — is correct; the pullback proof's last step is
  Dentzer's criterion inside $M$, which the paper leaves implicit.
- Steps (3)–(4) are GAP computations, not human proofs. The paper does
  not specify the semidirect-product actions in the displayed structure
  description of $G$, and gives no character-theoretic reason for
  non-monomiality beyond GAP's `IsMonomialGroup` output. Lean has no
  SmallGroups library. See `GAPS.md` (G1) for the resulting tracked
  preliminary; everything else is formalized and proved. (The GAP
  presentation on $f_1,\dots,f_8$ has since been supplied and is pinned
  in Lean as `CounterexampleGroup`; an independent Todd–Coxeter
  enumeration confirms its order is 384. Its semiabelianity and
  non-monomiality in Lean remain the tracked GAP preliminary.)
- The GAP listings in `Latex/code/` (`IsNAM`, `IsWAM`,
  `HilbertBasisMonomial`) are not input by `main with muse.tex` (only
  `algorithm.tex` is); they are unrelated almost-monomial test code and
  are not results of the paper.
- Edge cases: Dentzer's criterion needs $G$ nontrivial (the trivial
  group is semiabelian by the empty chain); in the pullback lemma the
  case $U=M$ is immediate, and $M$ trivial forces $U=M$.
