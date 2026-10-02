# faf-cleanroom standards

Binding for every agent in the clean-room formalization run (begun 2026-09-29). Where a mandate or prompt conflicts with this file, this file wins; flag the conflict in your report.

## The failure this run exists to prevent

A theorem that is kernel-clean, sorry-free and axiom-clean, yet tests something **weaker than, or beside,** the claim it is named for. The author has repeatedly found Lean formalizations that were "fake" in this sense. The postmortem that names the patterns is `AUDIT` (`research/lean-deference/AUDIT.md`, §0.2 and §3): read §0.2 and §3 once before your first Lean work. The kernel checks proofs; it does not check that the statement is the claim. Every rule below is about the statement.

## 1. State over FAF's objects

- Where [Formalized Agent Foundations](https://github.com/A-M-Berns/Formalized-Agent-Foundations) (FAF, pinned at `159ec3f`, read-only under `.lake/packages/agentFoundations/`) has an object — markets, traders, prices, the logical induction criterion, the LI construction, provability logic, modal agents, Cartesian frames, finite factored sets, condensation, safe Pareto improvements, Shannon information — **use FAF's object**. A local stand-in for an FAF object is a *modelling substitution*: remove it, or disclose it in the docstring and the ledger as `(c)`.
- FAF is never patched. A lemma FAF lacks is proved here. A lemma FAF has but keeps `private` is re-proved here (and noted as an FAF API request).
- Never `import Mathlib` wholesale: FAF's vendored PFR defines `MeasureTheory.Measure.support`, which clashes. Import the specific Mathlib and FAF modules you need; narrow imports also keep Lean's memory down.

## 2. The trust holes (mechanically gated)

`scripts/wp-audit` (the per-package wrapper around `scripts/audit.sh`) must PASS on every module you own before you claim anything. It fails on: `sorry` not listed in `OPEN.txt`, any axiom beyond `propext`/`Classical.choice`/`Quot.sound`, `native_decide` and friends, `implemented_by`/`extern`/`unsafe`/`opaque`, custom syntax/macros/elaborators, environment hacking, `debug.skipKernelTC`. Kernel replay (`leanchecker`) runs at consolidation. The gate cannot see anything in §3–§5; those are what audits are for.

Each package's `run/wp/<key>/<key>-open.txt` (same format as the root `OPEN.txt`) lists its deliberately open statements (a precise Lean statement of a conjecture or an unproved step, with `sorry`, a reason, and a pointer). An open statement is a legitimate, valuable output. A "proved" theorem that rests on an open one is itself open and must be listed.

## 3. Statement fidelity (audited, not gated)

- **No squeezes.** If a hypothesis is equivalent to (or trivially implies) the conclusion, the theorem is worthless as a check of the claim. Hypotheses that are LI-paper theorems or FAF theorems should be *derived from FAF*, not assumed, whenever FAF proves them.
- **Hypothesis provenance.** Classify every hypothesis of every headline: **(a)** derived here or in FAF / no hypothesis; **(b)** a published theorem taken as stated because FAF lacks it (name the paper and theorem); **(c)** a modelling substitution — an identification that puts a weaker or different object in place of the intended one (e.g. "the criterion applied to this unmodeled trader yields this inequality"). (c) must be disclosed; the ambition is to convert (c) and (b) to (a).
- **Non-vacuity.** Every headline whose hypotheses are not trivially satisfiable ships a witness that inhabits its *full* hypothesis package. Grade it **N+** (non-degenerate: exercises the content — not constant sequences, not an empty type, not a trivial market) or **N−** (degenerate; say why that's the best available). Use the real construction (e.g. FAF's LI construction) where possible. Impossibility results get a check that the impossibility isn't an artifact of the encoding (e.g. an over-strong definition that nothing satisfies).
- **Definitions mean what the prose word means.** Watch junk values (division by zero, `Classical.choice` defaults, `sSup` of unbounded sets, `ℝ≥0` truncation, `Nat` subtraction), filters (`atTop` vs `cofinite`), and quantifier order. A definition that makes the headline trivially true is the worst failure.
- **Names and docstrings don't oversell.** A theorem proving "two points in an interval" is not `underdetermination_off_G`. When the Lean is weaker than the note's claim, the name and docstring say so.
- **Conclusion renders the claim.** If the note says "forced", the conclusion must carry the forcing, not a hypothesis.

## 4. Provenance docstrings

Every top-level `theorem`/`lemma`/`def`/`structure`/`abbrev` carries a docstring with at least these lines:

```
/-- <one-sentence plain statement>
Source: `note-name` §n (or paper + theorem number, or "none: infrastructure")
Kind: P | C | S | T | N+ | N- | L | D | OPEN   (see §6)
Fidelity: exact | stronger | weaker: <how> | variant: <how> | n/a
Hyps: (a)… (b)… (c)…   (headlines only; one clause per non-(a) hypothesis) -/
```

The gate lints for `Source:` and `Kind:`; auditors read the rest.

## 5. Findings about the research are first-class output

The notes contain errors, ill-posed claims and gaps; finding them is as valuable as proving theorems. When a claim is false, prove the refutation in Lean if you can. When it is ill-posed, formalize the nearest well-posed versions and say which the note needs. **Failure to prove is not evidence of falsity**: record what was tried and why it stalled. Findings go in `<key>-findings.md` with a severity (blocking the note's conclusion / local error / imprecision / presentation) and a pointer.

Push the agenda: when a note stops at a conjecture, try to prove it; when a result has an obvious strengthening or a natural next question, attempt it and state it as `OPEN` if it resists.

## 6. The ledger

Every headline gets one row in its package's `<key>-ledger.md` table:

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |

Kinds: **P** proved outright (real content) · **C** composition (real multi-step chaining of cited facts) · **S** squeeze over hypotheses equivalent to the conclusion (should not be a headline) · **T** trivial stub (should not be a headline) · **N+/N−** non-vacuity witness · **L** propositional plumbing · **D** definition of record · **OPEN** stated, not proved. Status: `proved` / `refuted` (the note's claim is false, refutation proved) / `open` / `partial: <what>`. A "headline" is a declaration that answers a claim in a source or a target in the mandate; supporting lemmas need no row.

## 7. Audit and repair

Every package gets fresh-context adversarial audits by agents that did not write it, against §1–§6. Blocking issues are repaired and re-audited. An issue that survives the final round is recorded as such in the ledger's Status column (`flagged: <issue>`), never silently dropped. Audits are written to be read: an auditor who finds nothing wrong says what it checked and how.
