# Work log — Semiabelian Non-Monomial formalization

## 2026-11-03 — Formalization created; main theorem proved modulo tracked preliminaries

**Milestone report, in the order required by `AGENTS.md`:**

- **Proved (verified in this session):**
  - Definitions matching the paper: `IsSemiabelian`/`IsSemiabelianStep`
    (Definition 1, subgroup-chain form), `IsMonomial` via Mathlib's
    induced representations and linear characters, `KidaConjecture`,
    background definitions (`IsModularGroup`, `IsQuaternionGroup` by
    its order-8 characterization, `IsQuaternionFreeGroup`, `Isoclinic`).
  - `isSemiabelian_of_subsingleton`, `isSemiabelian_of_commGroup`
    (abelian groups are semiabelian, from the definition).
  - `IsSemiabelian.of_mulEquiv` (isomorphism invariance, with step
    transport `IsSemiabelianStep.of_equiv`).
  - `dedekind_modular` (Dedekind's law for subgroups, elementwise) and
    `semiabelian_pullback` — the paper's §3.1 pullback lemma, modulo
    Dentzer's characterization exactly as in the paper.
  - `conjugation_lemma` and `isSemiabelian_conjSubgroup` — the paper's
    §3.1 conjugation lemma, proved from the definitions.
  - `not_kidaConjecture`, `semiabelian_need_not_be_monomial` (the main
    theorem) and `counterexample_product` (the direct-product remark)
    — proved from the tracked preliminaries.
  - Axiom audit (`#print axioms`): the definition-level lemmas,
    `dedekind_modular`, `conjugation_lemma` and
    `IsSemiabelian.of_mulEquiv` depend only on `propext`,
    `Classical.choice`, `Quot.sound`. `semiabelian_pullback` and the
    Section 4 theorems additionally depend on `sorryAx`, inherited
    from the tracked preliminaries they use (Dentzer / the GAP fact) —
    no other axioms, no `native_decide` anywhere.
- **Still preliminary / `sorry` (tracked, all in
  `Formalization/Section_2_Preliminaries/A_TrackedPreliminaries.lean`):**
  `dentzer_characterization` (Dentzer Thm 2.3), `dornhoff_theorem`
  (Dornhoff Thm 2.6), `kida_theorem_1_4` (Kida Thm 1.4),
  `semiabelian_product` (Kida Lemma 2.5), `monomial_product_iff`
  (van der Waall Thm 2) — results the paper quotes, not proves — and
  `counterexample_exists`, the paper's GAP computation (G1). The
  comparator file's placeholders are challenge-side, by design.
- **Blocked:** G1 (see `GAPS.md`): discharging `counterexample_exists`
  needs data the paper does not contain (the actual actions /
  permutation generators of SmallGroup(384,20127) and a human
  non-monomiality argument), or a decision to keep the GAP fact as a
  permanent tracked preliminary. All unblocked work is done.

**Setup decisions (confirmed with the user):** folders
`Kourovka21.68/Papers/Formalization` and `Kourovka21.68/Papers/Comparator`,
mirroring `SwitchingReconstruction/`; scope = full paper as written;
pinned Lean/Mathlib v4.35.0 toolchain reused, no `lake update`.

**Audit:** the paper's two proved lemmas check out; its last pullback
step is Dentzer inside $M$ (made explicit). Steps relying on GAP
(`IsMonomialGroup: false`, the SmallGroup identification, Irr degrees)
have no human proof in the paper. `Latex/code/IsNAM|IsWAM|Hilbert…`
are not input by the paper and were not formalized.

**Build:** all nine `Formalization` modules compiled in dependency
order with the pinned toolchain (commands in `Readme.md`); comparator
elaborates with only its expected challenge-side `sorry` warnings.
Generated `.olean`s are gitignored build artifacts.

**Handoff:** to discharge G1 later, replace the `sorry` in
`counterexample_exists` with an explicit Lean construction and proof;
everything downstream is already formalized. Next steps if wanted: an
interactive HTML like the switching one, and a `citation.bib`.

## 2026-11-03 (later) — GAP presentation supplied and pinned; order independently verified

- The user supplied the GAP presentation of the counterexample group
  on generators $f_1,\dots,f_8$ with 36 relators. It is now in the
  formalization as `counterexampleRelators` and
  `CounterexampleGroup := PresentedGroup counterexampleRelators`
  (in `A_TrackedPreliminaries.lean`), and in the comparator as
  challenge definitions. A mechanical token-by-token check confirms
  the Lean relators are exactly the supplied presentation.
- Independent verification (not Lean, not GAP): a from-scratch
  Todd–Coxeter enumeration over this presentation (cosets of the
  trivial subgroup) closes with exactly 384 cosets, all relators act
  trivially, and the generator orders are $3,2,2,4,4,2,2,2$ — the
  presented group has order 384, as the paper claims.
- The tracked preliminary is now `presentedGroup_counterexample`
  (this explicit group has order 384, is semiabelian and is not
  monomial); `counterexample_exists` is *proved* from it. The
  semiabelian/non-monomial content remains a GAP verdict — a Lean
  proof for the presented group is still blocked (G1): it would need
  the Dentzer chain as words in the $f_i$ and a character-theoretic
  non-monomiality argument. Axiom picture unchanged: proved lemmas
  depend only on the standard axioms; everything downstream of the
  preliminaries additionally carries `sorryAx`.
- Rebuilt the full module chain and the comparator with the pinned
  toolchain: all pass. To fully discharge G1, the useful next data
  from GAP would be the chain subgroups $A_i, M_i$ as words in
  $f_1,\dots,f_8$ and the irreducible character / induced-character
  data behind `IsMonomialGroup: false`.

## 2026-11-03 (later) — Degree-eight characters supplied, recorded, and audited

- The user supplied the three degree-eight irreducible characters of
  $G$ (values on GAP's 27 conjugacy classes, with `E(3) = e^{2πi/3}`).
  Recorded in Lean as `degreeEightChar₁/₂/₃` with `E3` in
  `Formalization/Section_4_Counterexample/B_CharacterData.lean`;
  kernel-checked: length 27, first entry (degree) 8, pairwise
  distinct, standard axioms only.
- Independent audit from the presented group (regular action on the
  384 Todd–Coxeter cosets): exactly 27 conjugacy classes, sizes
  $[1,1,6^{21},64^4]$, center of order 2 (the paper's remark that $G$
  is a stem group is consistent: $27$ classes match the $27$
  irreducible degrees $[1,1,1,3^{21},8,8,8]$, whose squares sum to
  $384$). For the first degree-eight character, the norm and
  trivial-orthogonality equations have a unique consistent assignment
  of class sizes: $-8$ on the nontrivial central class and the four
  other nonzero values on the four 64-element classes.
- Still not a Lean proof of non-monomiality: GAP's class ordering /
  representatives as words in the $f_i$ and an induced-character
  argument are still needed (G1). The lists are Lean *data* for now.

## 2026-11-04 — GAP accessed directly; full certificate obtained

- Asked whether we can access GAP ourselves: no local GAP, no
  Homebrew/conda/Docker, and SageCell was down (HTTP 520), so we
  downloaded GAP 4.16.1 core + required packages from the official
  GitHub release and built them with the system clang in
  `/tmp/gapbuild/gap-4.16.1` (outside the repo; nothing installed
  system-wide). `SmallGroup(384, 20127)` loads from the bundled
  SmallGroups library.
- GAP re-verified the paper end-to-end: `IdGroup = [384, 20127]`,
  order 384, solvable, `IsMonomialGroup = false`, irreducible degrees
  $[1,1,1,3^{21},8,8,8]$, 27 conjugacy classes with sizes in GAP order
  $[1,64,6^5,1,64,64,6^9,64,6^9]$ (as a multiset
  $[1,1,6^{21},64^4]$, matching our Todd–Coxeter audit), center of
  order 2, and `TestMonomial` false for exactly the three degree-eight
  irreducibles. GAP's `IsomorphismFpGroup` has the *same* 36 relators
  as the supplied presentation, so its $f_1,\dots,f_8$ are our
  presentation generators.
- Extracted the complete certificate, now recorded in Lean in
  `Formalization/Section_4_Counterexample/C_GapCertificateData.lean`:
  the 27 conjugacy-class representatives as words in the $f_i$ (in
  GAP's order, matching `degreeEightChar₁/₂/₃`; e.g. the central
  class is $f_8$, where all three characters take $-8$), and the
  Dentzer chain $G=A_0M_0$, $M_0=A_1M_1$, $M_1=A_2M_2$, $M_2=A_3M_3$
  with subgroup generators as $f$-words ($A$ orders $8,8,8,4$;
  $M$ orders $96,24,12,3$; structures as in the paper).
- Non-monomiality certificate made human-readable: subgroup orders
  of $G$ are $[1,2,3,4,6,8,12,16,24,32,64,96,128,384]$ — there is no
  subgroup of order 48, hence no index-8 subgroup from which a
  degree-eight irreducible could be induced from a linear character.
- Full module chain (now 11 modules) rebuilt clean. Remaining
  blocker unchanged in kind but now precisely scoped (G1): Lean
  proofs of the chain and subgroup-absence inside `PresentedGroup`
  need coset-enumeration-scale kernel computation; the practical
  route is a computational (Todd–Coxeter permutation) model of the
  group in Lean plus transport across the presentation isomorphism.

## 2026-11-04 (later) — Polycyclic computational model kernel-verified

- Built `Formalization/Section_5_ComputationalModel/A_PolycyclicModel.lean`:
  the polycyclic collection action `actWord` on `Fin 384` (normal form
  `f1^e1 ⋯ f8^e8`, exponent ranges `[3,2,2,2,2,2,2,2]`, conjugation and
  power-carry tables read off the GAP presentation). The Python
  collector was validated against the full Todd–Coxeter multiplication
  table first (0 mismatches on all 384×384 products), after fixing two
  bugs found in validation: relative orders are 2 (not 4) for `f4, f5`
  with `f4² = f5² = f8` as a power carry, and conjugated factors in a
  collection step must be accumulated in increasing generator order.
- All 36 relator identities are proved in Lean
  (`presentationAction_relator_01` … `presentationAction_relator_36`),
  each by kernel `decide`; axiom audit: `presentationAction_relator_02`
  depends only on `propext`. Build cost found empirically: one relator
  costs ~35s of kernel time, so the 36 checks are split per relator
  (a single combined `decide` timed out twice, at 30min and 240s);
  per-relator fuel was tightened from 10000 to 200 after measuring a
  maximum of 84 collector steps per word action. Full Section 5 build:
  5m36s. The root module imports Section 5 and rebuilds clean; the main
  theorem still carries `sorryAx` only through the tracked
  preliminaries.
- Remaining (G1): group operation on `Fin 384`, homomorphism from
  `CounterexampleGroup`, order argument, transport of semiabelianity /
  monomiality, and the induced-character argument. The verified action
  is the foundation for those.

## 2026-11-05 — `C_PermHom` rewrite: inverse-action convention, slow build diagnosed

- Rewrote `Formalization/Section_5_ComputationalModel/C_PermHom.lean`
  with the inverse-action convention (`genPerm i` is right multiplication
  by `fᵢ⁻¹`; `wordPerm = FreeGroup.lift genPerm`; `actWordFin` reads a
  `Fin 8` word reversed with identity Bool map) and `actWordAt` at fuel
  30000, `invWord`, `wordBound_invWord_le`, `actWordAt_invWord`, and
  `wordPerm_apply`. `PresentedGroup.toGroup` in pinned Mathlib takes
  `FreeGroup.lift f` relator conditions, matching `wordPerm` directly.
- A full build of the rewritten file ran 39 minutes with no terminal
  output and was terminated. Its (block-buffered) log, recovered after
  the kill, showed four real errors in `actWordAt_invWord`, all fixed:
  (1) nil case `rfl` failed — `actWordAt 30000 [] x = x` needs the
  `encode_decode` roundtrip (now proved like `actWord_nil`); (2) the
  `hb1` omega bound was 10 short — sharpened with `as.length ≤ 8` and
  the exact `wordBound_cons` relation; (3) `congr 1` peeled one layer
  too few in the calc step — replaced by rewriting with the append
  identity; (4) `rw [actWordAt_cancel]` could not match `[a]` against
  `[(a.1, a.2)]` — replaced by a `show` (Prod eta) plus `exact`.
  Also removed two dead `<;> decide`s flagged by the unused-tactic
  linter in `atomBound_le`.
- Measured evidence: a single-pair `∀ x : Fin 384` cancel check at fuel
  30000 (`decide`, correct file-level `maxRecDepth 10000`) passes in
  27s; a single evaluation passes in 34s including imports. The
  truncated build (through `actWordAt_invWord`, i.e. the `decide`s in
  `actWord_cancel`, `actWord_cancel'`, `actWordAt_cancel`: 3072 + 3072
  + 6144 kernel evaluations) exceeded a 280s timeout with no flushed
  output — consistent with the per-check costs above under the
  observed machine load average ~13.9, not with a hang: Lean's
  redirected output is block-buffered (the killed log was exactly one
  4096-byte block). Verification of the truncated and full file is
  pending a long-timeout build; nothing in `C_PermHom` is claimed
  verified yet.
