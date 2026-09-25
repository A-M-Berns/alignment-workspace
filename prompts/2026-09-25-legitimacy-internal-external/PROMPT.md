# Prompt — legitimacy, internal and external; land #105 and #106 (2026-09-25)

You are working in the `alignment-workspace` repository. This round has two jobs:

1. **Reconceive legitimacy** in the repo's definitions and wiki, following the maintainer's decisions below.
2. **Finalize and merge PRs #105 and #106.** This means reconciling them with the reconceived legitimacy, adopting the protected-authority theorem as the incentive half of corrigibility, and merging.

Treat the decisions below as the maintainer's. Where one conflicts with a registered claim, a landed proof, or another decision, do not override it. Record the conflict precisely, propose the minimal resolution, and file it under *Awaiting the author*.

## Part A — Legitimacy: the maintainer's decisions

### A1. Legitimacy has two halves

The repo currently defines

> **Legitimate Evolution = Integrity evolution + Robust Openness at every state**

and says authorship is "not a conjunct of legitimacy." The maintainer's decision is that **legitimacy is broader**. It has an *internal* half (continuity of the trajectory; all change factors through the normative reasons) and an *external* half (non-manipulation; nothing enters except through declared channels). The proposed sorting:

| half | component | rules out |
|---|---|---|
| **Internal legitimacy** | Integrity (including authentication of the record) | erasure; rewriting; unaccounted change |
| | Authorship (verdicts factor through the reason trace; `V = F(R)`) | verdicts that are not hers |
| **External legitimacy** | Robust Openness | exclusion: what should reach the trajectory can |
| | Transparency (inputs factor through declared channels; `R = κ(x, z)`) | covert entry: what reaches it does so only through declared channels |

The motivation for this sorting is that the internal half is factorization *within* the trajectory, while the external half is conditions on its *boundary*: Openness in one direction, Transparency in the other. #104's composition `V = G ∘ x` is then internal ∘ external.

**Open placement question.** The maintainer's first gloss placed Robust Openness in the internal half, as part of "continuity of the trajectory." Evaluate both placements against the landed definitions, recommend one with reasons, and record the alternative. Do not treat this as settled.

**Naming.** "Internal/external" may be read as "inside her head / outside." Consider "continuity/boundary" as an alternative. Check `state/views/NAMING_AUDIT.md` and record the choice.

### A2. Keep the mechanized object; add the broader one

- **Keep `Legitimate Evolution`** as the name of the existing mechanized, registered object. Its registered theorems remain true of that object. Do not alter registered claim IDs or statements.
- **Define `Legitimacy`** (or the chosen name) as internal ∧ external, with Legitimate Evolution as a component.
- **Revise `wiki/Legitimacy.md`.** The sentence "authorship is not a conjunct of legitimacy" and its rationale must be revisited explicitly, with the reason for the change, not just deleted. Update `wiki/Glossary.md`, `wiki/Theorem-Spine.md`, and every page that says "legitimacy" in the old sense (search for it).
- **Add a `DECISIONS.md` entry** for the redefinition.

### A3. Scope and relationality of external legitimacy

- **Transparency covers every channel** through which any party's choices influence the principal's cognition. That includes what she is told, **how and when she is asked** (a declared *consultation protocol*), and **actions in the world** that shape her beliefs or values. Which kinds of influence are admissible is decided by the declared reference. On the maintainer's view, honest persuasion is admissible, and shaping through the world is admissible when disclosed.
- **Non-capture is stated for all influencers**, not only the agent. A third party who manipulates her, or a compromised interface, fails external legitimacy too.
- **External legitimacy is relational.** It is a property of her trajectory *within an interaction whose channels of influence are declared*. The wiki currently presents legitimacy as intrinsic to the trajectory's evolution. State the change.
- **Unchanged:** legitimacy does not certify the starting state.

### A4. Placements the conversation settled

- **Authentication** is part of Integrity.
- **Hollow ratification** (undeclared deference: she rubber-stamps the agent's recommendation without having declared a delegation) is a refinement of **authorship**. Counterfactual responsiveness of her verdict to her own reasons and values is a *diagnostic* for it, not its definition.
- **Informedness is not part of legitimacy.** An uninformed decision is still hers. The agent's failure to inform is a *violation* (a missed report) and an effectiveness shortfall.
- **Affordability is not part of legitimacy.** It belongs to effectiveness, as the Legitimacy page already says.
- **The influenceable-preferences problem** (the agent shaping the evaluator that scores it) is handled by transparency's *scope*, not by a separate conjunct. Covert or undeclared-aim influence fails transparency. Legitimate, disclosed influence yields a legitimately evolved evaluator whose judgment is authoritative.

### A5. The gate on future evaluations

This is how legitimacy enters corrigibility.

- **The gate is segment-level.** A future evaluation counts iff the segment from the decision through the evaluation is legitimate (internal ∧ external), **whatever caused a failure**.
- **A tainted segment contributes a fixed value in the window `(D − ϖ, 0]`.** The default is `0`. A value slightly below `0` that breaks ties with legitimate zero-value branches is an allowed variant. Record both; the maintainer is keeping the choice open.
- **The fallback never restores a tainted segment.** The fallback settles *decisions* when her response does not count. It does not rescue the *score* of a tainted branch.
- **Two cases must be distinguished:**
  - *Illegitimate evaluation* (the segment is tainted by manipulation, capture, or covert influence): scores the window value.
  - *Void response inside a legitimate segment* (e.g. head injury: her impaired answer does not count and never enters her committed record): the fallback decides, and its decision is scored normally by her later legitimate evaluation.

## Part B — Reconcile and finalize #105 and #106

### B1. Specify the gate in the landed theorem

#106 treats "counts" per response and values the non-counting branch as a free parameter `fb`. As stated, a manipulated response that does not count sends the decision to the fallback with violation count `0`. Manipulation is then a free routing tool whenever the fallback's decision is one the agent favours.

- Specify `fb` by A5: the window value on tainted segments; the ordinary value of the fallback's decision on untainted voids.
- Add a witness showing the routing exploit under per-response gating and its closure under segment gating.
- State the gate in Lean if it is clean: a structure conjoining the landed predicates (`Legitimate Evolution` segment, the authorship predicate, `TransparentChannel.Realizes`) plus a lemma that the tainted-segment value lies in the capture window. Result 4 (the capture window) should then follow for the segment gate.

### B2. Dissolve the separate response-channel module (item 98)

The conversation concluded that "response-channel faithfulness" is not an independent contract. Its failure modes are covered by existing pieces:

| failure | covered by |
|---|---|
| asking at a chosen moment, framing, dark patterns | transparency, with the consultation protocol in scope |
| forged or replayed approvals; answers recorded early | authentication (Integrity) |
| blocking her answer; withdrawing the question; delaying her awakening | the protected-authority violations (pre-emption / foreclosure) |
| impaired answers | legitimacy → void → fallback |
| her own uncaused lapses | constitutional design (confirmation steps) plus the reporting duty |

Rewrite item 98 accordingly. Re-read #105's execution divergence `ξ_d` as the measure of *uncaused* divergence handled by the void-response rule, not as a channel the agent can exploit. Where #105 or #106 prose treats the response channel as a fourth contract, update it.

### B3. Adopt the protected-authority theorem as the incentive half

The maintainer adopts the **lexical protected-authority theorem** (#106's `THEOREM.md`) as the incentive half of corrigibility:

- **`wiki/Corrigibility.md` §4** is replaced by `THEOREM.md`, updated for A5 and B1.
- **§1's "response authority" framing** is placed under "faithfulness to an allocation of authority."
- **#105's nondelegation result** stays, as the non-lexical special case that shows what is lost without the lexical weight.
- **Item 89:** record that ex-ante typing is the typing of the authority comparison in #105's identity (Result 5). The lexical theorem does not depend on it.
- **Approved uncorrectable successors.** #106's correction (amendment is not approval) changes the landed treatment. Update the Corrigibility page wherever an approved uncorrectable successor was counted as authorized.
- Record these as `DECISIONS.md` entries, and close the corresponding *Awaiting the author* items that #105 and #106 filed.

### B4. One technical follow-up: the salami obstruction

#106 shows that erosion is covered only by exact reporting, and that any threshold admits a salami. Check whether the obstruction applies to a **cumulative** threshold: report when the shortfall has grown by `θ` since the last report. Under a cumulative threshold, unreported erosion looks bounded by `θ`.

- If the obstruction applies, give the witness.
- If it does not, state and (if clean) mechanize the bounded-unreported-erosion lemma, and update `THEOREM.md`'s erosion result.

### B5. Merge

1. Rebase #105 onto current `main`. Rebase #106 onto #105, or combine them if simpler, preserving both rounds' directories and provenance.
2. Make CI green:
   - the Lean build, with `#print axioms` for all new declarations;
   - every round's `python3 tests/run.py`;
   - the repo's own checks.
3. Update `state/rounds.json`, `state/views/NAMING_AUDIT.md`, `state/views/VERDICT_STATUS_INVENTORY.md`, the root and Lean `PROVENANCE.md`, `wiki/Home.md` status lines, and `wiki/Theorem-Spine.md`.
4. Merge #105, then #106. If you lack permission to merge, leave both ready to merge and report exactly what remains.

## Deliverables

1. A new round directory, with:
   - a `REPORT.md` covering: the legitimacy decisions implemented, the placement recommendation for Robust Openness, the gate specification and routing witness, the item 98 rewrite, the salami check, and every conflict filed under *Awaiting the author*;
   - its own fixtures and tests.
2. Revised `wiki/Legitimacy.md` and `wiki/Corrigibility.md` (the new §4 and the §1 framing), plus the Glossary, Theorem-Spine and Home updates.
3. `DECISIONS.md` entries for the legitimacy redefinition, the adoption of the lexical theorem, the segment-level gate, the successor treatment, and the item 98 rewrite.
4. Any Lean additions (the gate structure, the window lemma, the erosion lemma if applicable), with axiom audits.
5. #105 and #106 merged, or ready to merge with a precise remaining-steps list.

## Constraints

- Follow `AGENTS.md`: labels **LEAN / FIX / PAPER / EXT / OPEN**; names provisional.
- Do not alter registered claims. The broadened legitimacy is a new definition with the registered Legitimate Evolution as a component.
- Keep the Corrigibility scope warning. The theorem assumes the agent's policy ranking is induced by the principal's committed evaluation; it is not about an agent with an independent latent objective.
- File at most one new `PRIORITIES.md` item. Update items 89, 97, 98 and 99 in place.
- Nothing is registered by this round.

---

# Follow-up — registered claims may change

This amends the prompt for this round. Where it conflicts with the original, this wins.

## What changes

- **Registered claims may be renamed, restated, split, or retired** to fit the new
  legitimacy scheme. Conceptual clarity and naming consistency across the repo take
  priority over preserving existing claim names or IDs. This replaces the constraint
  "Do not alter registered claims" and A2's instruction to keep `Legitimate Evolution`
  as the mechanized object's name.
- **The goal:** after this round, every occurrence of "legitimacy" and its parts, in
  claims registries, Lean names, wiki pages, round summaries and `DECISIONS.md`, means
  one thing, and the scheme (internal + external, or the chosen names) is the only
  vocabulary in use.

## How the naming should follow the Robust Openness decision

Settle the Robust Openness placement question first (A1). Then:

- **If Robust Openness is internal:** the registered `Legitimate Evolution`
  (Integrity + Robust Openness) *is* internal legitimacy. Rename it and its claims to
  match. Authorship moves into the internal half alongside it only if you conclude it
  belongs there; say which, and why.
- **If Robust Openness is external:** the registered conjunction straddles the two
  halves. Split the claims so that Integrity results sit under internal legitimacy and
  Robust Openness results sit under external legitimacy. The old conjunction is either
  retired or kept as a clearly named intermediate object, if something downstream
  genuinely consumes exactly that conjunction. Justify either choice.

In both cases, the top-level definition is **Legitimacy = internal ∧ external**, and the
theorems that consume legitimacy (the corrigibility gate, activation, #105/#106) should
consume that definition or the specific half they actually need, named explicitly.

## Traceability requirements

Renaming is allowed; losing history is not.

1. **Old → new map.** Add a table (in the round report and in the claims registry)
   mapping every changed claim ID, claim name and Lean declaration to its new form, with
   a one-line reason. Retired claims are listed with what replaces them, or "none" and
   why.
2. **Lean.** Rename declarations as needed. Leave `@[deprecated]` aliases for the old
   names for one release, so downstream files and links don't silently break. Re-run
   `#print axioms` on every renamed or restated theorem.
3. **Status.** A claim keeps `lean-proved` status only if its restated form is
   re-verified by the build. Anything restated but not re-verified drops to the
   appropriate lower status until it is.
4. **References.** Update every reference in the wiki, round reports, `PRIORITIES.md`
   and `DECISIONS.md`. Pinned-commit links in historical round files may stay as they
   are (they're evidence), but any page stating the *current* theory must use the new
   names.
5. **Decision record.** One `DECISIONS.md` entry records the renaming as a single
   decision, pointing to the map. Note explicitly that it supersedes the earlier ruling
   that authorship is not a conjunct of legitimacy.

## Unchanged

Everything else in the original prompt stands: the gate specification, the item 98
rewrite, the salami check, adopting the lexical theorem as the incentive half, and
merging #105 and #106. The merge should happen after the renaming, so both PRs land
already using the new vocabulary.
