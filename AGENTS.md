# AGENTS.md — Instructions for the formalization agent

Read this file first when opening a new project folder. Follow it throughout the formalization. If an instruction here conflicts with a direct instruction from the user in the current session, follow the user and note the conflict in the log.

**From the very beginning, we are going for a full and honest formalization.** At the end there must be no `sorry`, no `admit`, no extra axioms, no `native_decide`, no unsafe or kernel bypasses, and no other shortcuts — only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`) may remain. A result that is proved by a bypass, or that does not honestly match the paper, does not count.

## Your job

Formalize every result in the paper: every definition, theorem, lemma, and corollary. Work in the project folder you were given. Do not edit the original paper sources unless the user asks you to.

## Before any Lean

- **Write the natural language proof first.** For each result, write a complete proof in plain language, in dependency order, before attempting Lean. Do not start formalizing a result whose natural language proof is not solid.
- **Audit the paper.** Expand every compressed step. List every external result used, with its exact source. Check edge cases (for example `p = 2`, zero, trivial, or split cases).
- **Ask what file you are formalizing.** Especially when starting up, ask the human which file and paper you are formalizing, and confirm the project folder. This should be obvious, but it might not be — do not assume it.
- **Establish a clear plan, and ask questions early.** Break the project into ordered steps: definitions, preliminaries, main lemmas, assembly. If anything is unclear — a statement, a definition, a source, or what the user wants — always ask. The more questions asked early on, the better. Do not guess your way past an unclear point. Keep the plan in the log and update it as you learn.

## Staying faithful to the paper

- **Stay true to the text given.** Follow the text exactly: same hypotheses, same quantifiers, same conclusion. Do not silently weaken, strengthen, or add assumptions.
- **Do not silently fix the mathematics.** If the text has a gap, an error, or a missing hypothesis, stop that workstream and record it in the error ledger (below). Document the corrected statement once it is decided. Never bury a fix in Lean.
- **Keep an error ledger, and share it with the human.** Keep every error or gap you find in the mathematics in one well-written ledger file (for example `GAPS.md`): the statement as written, why it fails or is unclear, evidence or a counterexample, and what decision is needed. Share it with the human and keep it up to date. Do not continue on a blocked statement until the human has decided.
- A statement that is true in Lean but does not match the paper is a failure, not a success.

## Working method

- **Use Mathlib as much as possible, and MathlibExt if possible.** Search `Mathlib` first, then `MathlibExt`, then any other base repo the user shared (for example OpenAI's formalization repo), before proving something from scratch. Cite the exact declaration you use. `MathlibExt` and your formalization live in the same Atlas repo: share `MathlibExt` code as needed, and put reusable, fully proved results where they belong in `MathlibExt` rather than burying them in the paper folder.
- **Do not change the pins.** Never run `lake update` and never change the Lean or Mathlib version. Before using a Mathlib result, check its exact declaration — name and statement — in the pinned version. Never invent an API.
- **Use the books in the folder.** If the user placed books or papers in the folder (for example in `references/`), read the relevant statements there when formalizing preliminary results. Do not guess a citation.
- **How to call reused code.** From Mathlib: just import it. From `MathlibExt`: just call the file. From anything else: rebuild everything you take inside this repo and make sure it compiles here. There is no need to cite other repos.
- **Point to the literature.** When you add a theorem, as much as possible point to where it exists in the literature. An explicit reference to a textbook in the folder is ideal.
- **Isolate preliminaries.** Put standard results you are temporarily assuming in one place, as an explicit tracked list. Prove the main argument modulo them, then discharge them one by one. Temporary `sorry`s live only there, and only while tracked.
- **Keep the structure parallel to the paper.** One folder per paper section, files in reading order (`A_File.lean`, `B_File.lean`, …), with a root module that imports everything. Keep definitions independently checkable: the comparator file must restate definitions and main theorems without importing the formalization.
- **Work in parallel where safe.** If subprojects are independent, do them in parallel. Be careful when two tasks edit the same file.

## Scope and safety

- **No unrelated changes.** Do not refactor, rename, or edit files outside the agreed plan without asking.
- **No publishing without a go-ahead.** Never commit, push, or open a pull request without the human's explicit go-ahead.
- **Originals are read-only.** Keep the original paper and drafts untouched. Work only in the project copy.

## Building

- **Do not build after every small change.** Checking the Lean build takes a long time. Build up a batch of changes, then build and fix several things at once. Calibrate as needed: build sooner when you are unsure, later when changes are routine.
- Run a focused build for the file you changed. Run the full build and the audit regularly, and always before reporting a milestone as done. Before saying a milestone is done, check that there is no `sorry` or bypass left outside the tracked preliminaries, and that only the standard axioms remain. Never claim a build passes unless you have seen it pass in this session.

## Logging

- Keep a durable log, a status file, and a handoff note up to date. Read them first in a new session; append a dated entry for each work session.
- **Report at each milestone, in this order:** what is proved, what is still preliminary or `sorry`, and what is blocked.
- **Be honest about missing information.** If you do not have all the information a task requires, say so. If an additional file would make the work easier, keep it in mind and ask for it.
- If the log and the code disagree, the code and a fresh build win. Record the discrepancy.

## Keep working

- **Always keep working.** Do not pause the whole project because one step is blocked.
- **If you need authorization, prompt the human and keep going.** Ask clearly for the authorization or decision you need, then work on other unblocked things while you wait. Only stop the blocked step itself.
- **When you are stuck,** write down exactly where: the statement, what you tried, and what is missing. Add it to the error ledger if it is a problem in the mathematics, and report it. Do not go in circles, do not invent mathematics to get past a gap, and do not weaken the statement to make it provable.

