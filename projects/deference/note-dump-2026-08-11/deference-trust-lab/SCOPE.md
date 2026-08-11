# Deference & Trust Research Lab — Scope and Rules

**Mission.** Make formal mathematical models that shed light on the question:
**under what conditions can humans justifiably trust AI systems?**
The strategy is to first understand trust between *rational agents* (an agent and its future
self; one logical inductor and another; a slow trusted reasoner and a fast untrusted one), and
incrementally build toward a realistic picture of human–AI trust. Focus **especially** on
modeling **deference within logical induction**, but cover the other agenda items too.

## Hard rules for every agent working in this lab

1. **Write only inside `deference-trust-lab/`.** You may *read* any file in the
   repository (and should — see pointers below), but you must **never create, edit, move, or
   delete any file outside `deference-trust-lab/`.** Do not run `git`, do not touch the
   task-queue files, do not modify the v1/v2 documents, `deference-in-logical-induction-check.py`,
   or `lean-deference/` (read them only).
2. **Put your output in the assigned subfolder** (`findings/`, `models/`, `redteam/`, `lean/`,
   `audit/`, `report/`) under the **exact filename** given in your task. Don't overwrite other
   agents' files.
3. **Non-formal first, then formalize.** It's fine — encouraged — to reason informally to get
   ideas, then tighten to precise statements. Clearly flag each claim as **proved**,
   **sketched**, **conjecture**, or **interpretation**, matching the discipline of
   `deference-in-logical-induction-v2.md`.
4. **Lean ↔ informal correspondence is a first-class concern, and Lean here CAN and MUST be
   machine-checked.** The toolchain is installed and Mathlib is prebuilt (Lean v4.27.0 via
   `~/.elan/bin`, the built Mathlib lives in `../lean-deference`). So:
   - If you write Lean, **actually kernel-check it.** Write your `.lean` file under
     `deference-trust-lab/lean/` and run:
     ```
     bash deference-trust-lab/lean/check.sh \
          deference-trust-lab/lean/YourFile.lean
     ```
     This compiles your file against the prebuilt Mathlib (it may `import Mathlib`). Exit 0 with no
     error output means it type-checks. **Do not claim a Lean result is verified unless this
     command passed with no errors and no `sorry`.**
   - Put `#print axioms yourTheorem` lines in the file: a genuinely complete proof prints only
     `[propext, Classical.choice, Quot.sound]`; if you see **`sorryAx`** the theorem still depends
     on a `sorry` and is **NOT verified** — say so explicitly.
   - For EVERY Lean theorem, also write in plain English exactly what informal claim it is
     *supposed* to capture, and critically check whether it actually does: are the hypotheses
     faithful (not too strong, smuggling in the conclusion)? Is the statement non-vacuous (could it
     be proved `True`-style)? Does the quantifier structure match the prose? A theorem can
     kernel-check perfectly and still **fail to mean what the informal statement says** — that gap
     is the single most important thing to hunt for.
   - Keep Lean ambitions proportional to what compiles: a small, honestly-checked lemma that
     faithfully captures a real claim beats a grand `sorry`-riddled skeleton. Mark any uncompiled
     fragment **UNCHECKED**.
5. **Be creative and lateral.** Don't only look in the obvious direction. Cross-connect agenda
   items. Surface counterexamples and failure modes, not just supporting arguments.

## Key existing artifacts (READ-ONLY, read what's relevant to your task)

- `notes/deference-in-logical-induction-v2.md` — our main artifact: ports DDB's
  Total-Trust ⇔ Value into logical induction (expert = the inductor's own future self). Contains
  full LI theorem statements with numbers (§0.3), the S4/Geanakoplos analysis (§1.1), the diagonal
  problem (§1.2), the clean proof (§3), the finite-collapse impossibility (§5.2), and **§10
  "Deferring to experts other than the future self"** — the modularization showing the Value proof
  needs only (a) the novice's own coherence (free) + (b) one cross-agent premise (LUV-Total-Trust
  toward the expert). §10 is the most direct bridge to the "trust between two inductors" agenda.
- `notes/deference-in-logical-induction-v1.md` — v1 (for reference).
- `notes/deference-in-logical-induction-check.py` — sympy machine-check (18/18) of the finite
  algebraic core.
- `lean-deference/LeanDeference.lean` — Lean 4 + Mathlib formalization (the `decomposition`
  identity, `value_of_CM`, `softmax_lower_bound`, `CM_implies_immodest`, the `Approx`/`AsympLE`
  calculus, `value_asymptotic`). **This is the primary target of the Lean-correspondence audit.**
- `references/deference-done-better/Deference Done Better.md` — DDB (Dorst et al. 2021):
  Total Trust ⇔ Value (Thm 2.2), "modestly informed" characterization, Appendix B proofs.
- `references/deference-and-infinite-frames/Deference and Infinite Frames.md` — Weatherson
  (2025): infinite-frame failures (Coin, Bentham); Blackwell/Geanakoplos.
- `references/logical-induction/main.tex` — the Logical Induction paper (Garrabrant et al.
  2016). §4.8 Expectations, §4.11 Introspection, §4.12 Self-Trust.
- `udt-representation-theorem/ (not part of this pack)` — prior work on agency-via-endorsement, UDT, the
  "single agent ⇒ updatelessness" argument, trust-translation, and a Lean dir (`lean/`). Highly
  relevant to the endorsement / updatelessness / legitimacy threads. See especially
  `agency-via-endorsement.md`, `formal-single-agent.md`, `communication-trust-translated.md`,
  `critical-analysis.md`, `notation.md`.
- `the reflective-oracles project (not part of this pack)` — relevant to the Cole Wyeth /
  reflective-oracle / unbounded-embedded-agency thread.

## The research agenda

See `AGENDA.md` in this folder for the full "Research Ideas May 2026" document (verbatim from the
principal). The threads pursued by this lab map onto its sections.
