# Section 4: the GAP counterexample and the main theorem

1. `A_Counterexample.lean` — `not_kidaConjecture`,
   `semiabelian_need_not_be_monomial` (main theorem) and
   `counterexample_product` (the paper's direct-product remark),
   all proved from the tracked GAP preliminary
   `counterexample_exists`. See `../../GAPS.md`, G1.
2. `B_CharacterData.lean` — the three degree-eight irreducible
   characters supplied from GAP (`degreeEightChar₁/₂/₃`, `E3`),
   recorded as data with kernel-checked length/degree/distinctness;
   the conjugacy-class audit is in the file header. They are not yet
   Lean characters of `CounterexampleGroup` (see `../../GAPS.md`, G1).
3. `C_GapCertificateData.lean` — conjugacy-class representatives and
   Dentzer-chain subgroup generators as words in `f1, …, f8`, obtained
   from GAP 4.16.1 (built locally), with the no-index-8-subgroup
   non-monomiality certificate. Still GAP data, not Lean proofs.
