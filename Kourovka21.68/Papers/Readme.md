# Semiabelian groups need not be monomial

A Lean 4 formalization of **Semiabelian groups need not be monomial**
([Semiabelian_NonMonomial.pdf](Semiabelian_NonMonomial.pdf), LaTeX source
in [Latex/main with muse.tex](Latex/main%20with%20muse.tex)), Kourovka
Notebook Problem 21.68.

## About the paper

A finite group $G$ is *semiabelian* if it has a chain
$G_0 = 1 \le \cdots \le G_n = G$ with each $G_{i+1}$ a quotient of
$G_i \ltimes A_i$ for a finite abelian group $A_i$. A group is *monomial*
if every irreducible complex representation is induced from a
one-dimensional representation of a subgroup. Kida conjectured that
every semiabelian group is monomial. The paper disproves this with a GAP
search: $G = \texttt{SmallGroup}(384, 20127)$ of order $384$ is
semiabelian (certified by an explicit Dentzer chain) but not monomial.

| Result | Lean |
|---|---|
| Semiabelian groups (Definition 1) | `IsSemiabelian`, `IsSemiabelianStep` in [A_SemiabelianDefinition.lean](Formalization/Section_1_Introduction/A_SemiabelianDefinition.lean) |
| Monomial groups | `IsMonomial`, `IsMonomialRepresentation` in [B_MonomialDefinition.lean](Formalization/Section_1_Introduction/B_MonomialDefinition.lean) |
| Kida's conjecture; main-theorem statement | `KidaConjecture`, `ExistsSemiabelianNonMonomial` in [C_KidaConjecture.lean](Formalization/Section_1_Introduction/C_KidaConjecture.lean) |
| Pullback lemma (§3.1), modulo Dentzer | `semiabelian_pullback` in [B_PullbackLemma.lean](Formalization/Section_3_SearchStrategy/B_PullbackLemma.lean) |
| Conjugation lemma (§3.1) | `conjugation_lemma` in [C_ConjugationLemma.lean](Formalization/Section_3_SearchStrategy/C_ConjugationLemma.lean) |
| Main theorem: semiabelian need not be monomial | `semiabelian_need_not_be_monomial`, `not_kidaConjecture` in [A_Counterexample.lean](Formalization/Section_4_Counterexample/A_Counterexample.lean) |

## Honesty note — tracked preliminaries

Unlike the Switching Reconstruction formalization, this one is **not**
`sorry`-free yet, by necessity: the paper's counterexample is a GAP
computation (see [GAPS.md](GAPS.md), G1). The six results the paper
quotes or computes rather than proves — Dentzer's characterization,
Dornhoff's theorem, Kida's Theorem 1.4, the two direct-product lemmas,
and the GAP fact `presentedGroup_counterexample` (the explicitly
presented group `CounterexampleGroup` on $f_1,\dots,f_8$ — order 384,
independently Todd–Coxeter-verified — is semiabelian and non-monomial;
`counterexample_exists` is proved from it) — are isolated as tracked
`sorry`s in
[Section_2_Preliminaries/A_TrackedPreliminaries.lean](Formalization/Section_2_Preliminaries/A_TrackedPreliminaries.lean),
each with its exact source. Everything else, including both lemmas the
paper proves and the main theorem's derivation from the GAP fact, is
fully proved. The axiom audit is in [LOG.md](LOG.md).

## Layout

- [Formalization/](Formalization/) — the Lean formalization, by paper
  section in reading order, rooted at
  [SemiabelianNonMonomial.lean](Formalization/SemiabelianNonMonomial.lean).
- [Formalization/Section_5_ComputationalModel/](Formalization/Section_5_ComputationalModel/) — kernel-verified polycyclic action model (`actWord`), with all 36 presentation relators checked by `decide`. See [GAPS.md](GAPS.md), G1, for what remains to be built on it.
- [Comparator/](Comparator/) — comparator challenge
  ([semiabelian_nonmonomial_comparator.lean](Comparator/semiabelian_nonmonomial_comparator.lean),
  [JSON config](Comparator/semiabelian_nonmonomial_comparator.json)),
  restating definitions independently of the solution. Its placeholder
  proofs are challenge-side, by design; the tracked preliminaries are
  not comparator theorems (see the comparator file's header).
- [PROOF_AUDIT.md](PROOF_AUDIT.md) — natural-language proof and audit.
- [GAPS.md](GAPS.md) — gap ledger (G1 is blocking; see above).
- [LOG.md](LOG.md) — work log.

## Building

With the pinned toolchain (Lean/Mathlib `v4.35.0`; do not run
`lake update`), from the repository root, compile the modules in
dependency order:

```sh
export PATH="$HOME/.elan/bin:$PATH"
F=Kourovka21.68/Papers/Formalization
export LEAN_PATH="$F"
for f in Section_1_Introduction/A_SemiabelianDefinition \
         Section_1_Introduction/B_MonomialDefinition \
         Section_1_Introduction/C_KidaConjecture \
         Section_2_Preliminaries/A_TrackedPreliminaries \
         Section_3_SearchStrategy/A_IsoInvariance \
         Section_3_SearchStrategy/B_PullbackLemma \
         Section_3_SearchStrategy/C_ConjugationLemma \
         Section_4_Counterexample/A_Counterexample \
         Section_5_ComputationalModel/A_PolycyclicModel \
         SemiabelianNonMonomial; do
  lake env lean --root=$F -o $F/$f.olean $F/$f.lean
done
```

## Authorship

The paper was written by Joseph Phillip Brennan and Milana Golich with
Muse Spark via meta.ai, and reviewed by Andres Barei and John Portin
(see the paper's Statement of AI Use). The formalization was produced
with Muse Code, following [AGENTS.md](../../AGENTS.md).

## Versions

Lean `v4.35.0` and Mathlib `v4.35.0`, pinned at the top level of this
repository in [lean-toolchain](../../lean-toolchain) and
[lakefile.toml](../../lakefile.toml).
