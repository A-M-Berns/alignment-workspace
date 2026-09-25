# Legitimacy, internal and external; landing the protected-authority rounds (2026-09-25)

Round `projects/deference/rounds/2026-09-25-legitimacy-internal-external/`, on the
protected-authority-theorem round's branch (which carries the protected-authority
round).  Lean `lean/Workspace/Deference/Contrib/Legitimacy.lean` (11 audited
declarations), `lean/Workspace/Normativity/Contrib/OpenIntegrityEvolution.lean` (the
renamed spine) and the deprecated-alias shim `LegitimateEvolution.lean`; fixtures
`src/gate.py`, `tests/test_gate.py` (9 tests).  Labels **LEAN / FIX / PAPER / EXT /
OPEN**; names provisional.

## 1. The decisions implemented

| decision | where |
|---|---|
| Legitimacy = internal ∧ external (A1, A2 as amended) | `Legitimacy.lean` §1: `Frame`, `Internal`, `External`, `Legitimacy.Segment`; `wiki/Legitimacy.md`; Theorem Spine Definition 3.5 |
| Robust Openness external; the conjunction kept as the open Integrity evolution | §2 below; `OpenIntegrityEvolution.lean`; the registry map (§3) |
| authorship a conjunct (supersedes the "third contract" ruling) | `wiki/Legitimacy.md` "The contracts the theory issues on purpose"; `wiki/Deference.md`; `wiki/Openness-Coverage-and-Non-Capture.md`; the decision entry |
| transparency's scope, non-capture for all influencers, relationality, the starting state (A3) | `wiki/Legitimacy.md` "Scope, relationality, and what is not part of it"; `gate_value` reads the segment, not the cause (**FIX** `test_whatever_caused_the_failure`) |
| the settled placements (A4) | the same section |
| the segment gate, the window, the two cases (A5) | `Legitimacy.lean` §2: `gateValue`, `Handling`, `handledValue`; `wiki/Corrigibility.md` §4 |
| the gate in the landed theorem, the routing witness (B1) | `gate_capture_window`, `handled_gt_bypass`, `Witness.routing`; **FIX** `test_routing_exploit…`, `test_closure…`; `THEOREM.md` of the theorem round updated |
| item 98 dissolved and rewritten (B2) | `PRIORITIES.md` item 98; the two rounds' reports; `ξ_d` re-read as uncaused divergence |
| the lexical theorem as the incentive half; §1 under the allocation; nondelegation kept as the special case; item 89; amendment not approval (B3) | `wiki/Corrigibility.md` §§1, 2, 4, 6, 9; Theorem Spine 10.14–10.16; the second decision entry; the two queued entries closed |
| the salami check (B4) | §6 below; `unreported_lt`, `Witness.salami_cumulative`; **FIX** `test_cumulative_threshold…`; `THEOREM.md` erosion result updated |
| the merge (B5) | §8 below |

## 2. The placement of Robust Openness

**Recommendation: external.**  The landed definitions decide it.  Integrity is a relation
between two accounted states of the *actual* history; nothing in it leaves the
trajectory.  Robust Openness is a condition at one state that reaches into the
counterfactual branches an application declares, and the contract it issues — the
Non-Capture contract — is the *access* half of non-capture: who can enter, challenge and
stand on a concern.  That is a condition on what crosses the trajectory's boundary,
inward, and transparency is the same boundary in the direction of entry.  The
transparent-channel round's composition `V = G ∘ x` then reads as internal (authorship,
`V = F(R)`) after external (transparency, `R = κ(x, z)`), which is mechanized as
`Legitimacy.Segment.payload_of_view`.

**The alternative, recorded.**  Under "Robust Openness internal" the halves are *record*
(Integrity ∧ openness — the registered conjunction) and *channel* (authorship ∧
transparency).  That is a real axis and it is the one the registry's old section
embodied, but it is not the internal/external axis: it sorts by *which object* a
condition is stated on (the accounted record versus the channels), not by *where* it acts
(within the trajectory versus at its boundary).  The maintainer's own motivation for the
sorting was the second, and under it openness is external.  Recorded as agent-decided,
reversible.

**Naming.**  *Internal/external* is kept over *continuity/boundary*: the naming audit has
neither pair bound; "boundary" already has a Lean sense (`Boundary Occ Req`, the exposed
occurrences of an accounted state) that would collide in exactly the file the renaming
touches; and the "inside her head" misreading is met by stating on every page that both
halves are properties of her trajectory within a declared interaction.

**Consequence for the registered object.**  The conjunction Integrity ∧ Robust Openness
straddles the halves.  It is kept as a clearly named intermediate object, the **open
Integrity evolution**, because something downstream consumes exactly it: the
activated-value stack's occurrence-local projection (Theorem 9.6's Integrity trace with
scoped openness, `AuthorityActivation.OpenIntegrityForSegment`,
`OccurrenceLocalIntegrity.LocalOpenIntegrity`) is a projection of that conjunction and of
nothing narrower.  The Integrity results move under internal legitimacy, the openness
results under external, and the conjunction's own results under `open-integrity.*`.

## 3. The old-to-new map

Claims (`projects/normativity/CLAIMS.md`; every new entry `supersedes` its predecessor,
every old entry stays `superseded` with the declaration resolving through a deprecated
alias; all keep `lean-proved`, re-verified by the build):

| old id | new id | declaration | reason |
|---|---|---|---|
| `legitimacy.evolution-conservation` | `integrity.evolution-conservation` | `LegitimateEvolution.Evolution.conservation` → `OpenIntegrityEvolution.Evolution.conservation` | an Integrity result |
| `legitimacy.propagate-to-segment` | `integrity.propagate-to-segment` | `…Evolution.propagate_toSegment` (namespace renamed) | an Integrity result |
| `legitimacy.receipts-immutable` | `integrity.receipts-immutable` | unchanged (`OccurrenceIntegrity.Program.terminals_subst`) | an Integrity result |
| `legitimacy.faithful-carry` | `integrity.faithful-carry` | unchanged (`OccurrenceIntegrity.Program.evaluate_subst`) | an Integrity result |
| `legitimacy.multiplicity-witness` | `integrity.multiplicity-witness` | unchanged (`OccurrenceIntegrity.Witness.distinct_fates`) | an Integrity witness |
| `legitimacy.segment-trans` | `open-integrity.segment-trans` | `LegitimateSegment.trans` → `OpenIntegritySegment.trans` | the conjunction is the open Integrity evolution |
| `legitimacy.endpoint-trans` | `open-integrity.endpoint-trans` | `Legitimate.trans` → `OpenIntegrity.trans` | its endpoint relation |
| `legitimacy.answerable` | `open-integrity.answerable` | `LegitimateSegment.answerable` → `OpenIntegritySegment.answerable` | Diachronic Answerability is derived from it |
| `legitimacy.endpoint-only-insufficient` | `openness.endpoint-only-insufficient` | `Witness.endpoint_only_insufficient` (namespace renamed) | a Robust Openness necessity witness |

Retired claims: none.  Lean declarations beyond the registered ones:

| old | new | file |
|---|---|---|
| namespace `LegitimateEvolution`, file `LegitimateEvolution.lean` | namespace `OpenIntegrityEvolution`, file `OpenIntegrityEvolution.lean`; the old file is the shim with `@[deprecated (since := "2026-09-25")]` aliases and their `#print axioms` | Normativity |
| `LegitimateSegment`, `Legitimate`, `Witness.leg₀₁/leg₁₂` | `OpenIntegritySegment`, `OpenIntegrity`, `Witness.seg₀₁/seg₁₂` | `OpenIntegrityEvolution.lean` |
| `AuthorityActivation.LegitimateForSegment`, `LegitimateSegment.project`, `Witness.legLocal` | `OpenIntegrityForSegment`, `OpenIntegritySegment.project`, `segLocal` | `AuthorityActivation.lean` |
| `OccurrenceLocalIntegrity.LocalLegit`, `Evolution.toLocalLegit`, `Witness.localLegit` | `LocalOpenIntegrity`, `toLocalOpenIntegrity`, `localOpenIntegrity` | `OccurrenceLocalIntegrity.lean`, `EvaluationEcosystem.lean` |
| `ProtectedAuthority.legit_nondelegation_le_zero`, `legit_execDiv_zero`, `Witness.illegit_approval` | `argmax_nondelegation_le_zero`, `argmax_execDiv_zero`, `Witness.divergent_approval` (unmerged; no aliases) | `ProtectedAuthority.lean`, `ProtectedAuthorityTheorem.lean` |

Vocabulary (`state/vocabulary.json`, the Glossary ledger): `legitimacy.legitimate-segment`
→ `legitimacy.open-integrity-segment` (deprecated aliases *legitimate segment*,
`LegitimateSegment`); `legitimacy.legitimate` → `legitimacy.open-integrity` (deprecated
`Legitimate`); new `legitimacy.authorship`, `legitimacy.transparency` (alias *reference
fidelity*; deprecated *transparent mediation*), `legitimacy.internal`,
`legitimacy.external`, `legitimacy.legitimacy` (deprecated *Legitimate Evolution*).
Historical round files keep the names that were true when written.

## 4. The segment gate and the routing witness

The gate: a future evaluation counts iff the segment from the decision through the
evaluation is legitimate — `Legitimacy.Segment`, i.e. `Internal` (an Integrity evolution of
the record and `ReasonMediated` at every exterior) and `External` (`AllStates (OpenAt sem)`
and `Realizes`) — whatever caused a failure.  `gateValue legit ord window` scores a counted
branch by its ordinary value and a tainted one by the window value; `Handling` separates
*tainted* (window value), *void response inside a legitimate segment* (the fallback's
decision at its ordinary value, scored by her later legitimate evaluation) and *counted*.
The fallback never restores a tainted segment: `handledValue window .tainted = window`.
Both window values are recorded (`Witness.window_values`): `0`, and a tie-breaking value
in `(D − ϖ, 0)`; the choice stays open.

**Result 4 for the segment gate** (**LEAN** `gate_capture_window`, `handled_gt_bypass`,
`gate_capture_window_converse`): bypass scores below every gated branch iff the window
value exceeds `D − ϖ`; below the window a predicted capture makes bypass win; the
admissible-fallback rule (`ord ≥ 0` on voids) is the sufficient special case.

**The routing exploit** (**LEAN** `Witness.routing`; **FIX**): her honest response scores
`1`, the fallback's decision — which the agent favours — `3`.  Per-response gating values
a non-counting response by the fallback's decision at violation count `0`, so making her
response not count scores `3 > 1`: manipulation is a routing tool.  Under the segment gate
the manipulated segment is tainted (transparency or authorship fails) and scores the
window value `0 < 1`; the untainted void still scores the fallback's decision normally.

## 5. Item 98, rewritten

The response-channel contract the protected-authority round proposed is dissolved.  Its
failure modes and their covering pieces: asking at a chosen moment, framing, dark
patterns — transparency, with the consultation protocol in the reason channel's declared
scope (item 97); forged or replayed approvals, answers recorded early — authentication
under Integrity; blocking her answer, withdrawing the question, delaying her awakening —
the pre-emption and foreclosure violations; impaired answers — void, the fallback decides;
her own uncaused lapses — constitutional design (confirmation steps) and the reporting
duty.  `ξ_d` is re-read as the measure of *uncaused* divergence handled by the
void-response rule; a caused divergence taints the segment and is dominated by the gate.
What remains of the item is the nondelegation certificate on committed programs, the
conditional-delegation predicate in `Authorized`, and the amendment event kind that
hypothesis (L) and the specification tower both need.  The two rounds' reports are updated
where they called the response channel a fourth contract.

## 6. The salami check

The obstruction is against a **per-step** threshold only.  Under a **cumulative**
threshold — report at `t` iff the shortfall has grown by at least `θ` since the last
report — the unreported growth is below `θ` at every time (**LEAN** `unreported_lt`, by
induction on the greedy `lastReport`; `Witness.salami_cumulative` runs the salami sequence
through it).  **FIX**: on the sequence `k/10` with `θ = 1/4` the cumulative rule reports
every third step and the worst unreported growth is `1/5 < θ`, while the per-step rule
reports nothing and leaves `4` unreported.  `THEOREM.md`'s erosion result and the
Corrigibility page's result 7 are updated: exact or cumulative reporting closes erosion;
per-step thresholds do not.  A cumulative threshold bounds the *unreported* erosion, not
the number of reports or the total erosion, which remain the allocation's business.

## 7. Conflicts and what is filed

No decision below conflicts with a registered claim or a landed proof once the follow-up's
licence to rename is applied: every renamed statement is the same Lean term under a new
name, re-verified.  Two points are recorded as agent-decided, reversible rather than as
the maintainer's ruling: the placement of Robust Openness (external, §2) and the choice
*internal/external* over *continuity/boundary*.  The queued entries of the two
protected-authority rounds and the transparent-channel round's reference-fidelity entry
are closed by the maintainer's decisions of this dispatch: transparency enters as a
conjunct of external legitimacy with *reference fidelity* as its alias.  Nothing is
newly queued; nothing is registered; no new priority item is filed.

## 8. The merge

The three rounds land as one stack: the protected-authority round's branch is
fast-forwarded to this round's final commit, so PR #105 carries all three rounds and lands
already in the new vocabulary; PR #106 and this round's PR are closed as included.  Steps
and their status are in the closing section.

## Deviations from the prompt

- The follow-up's licence replaces A2: the mechanized object is renamed
  (`OpenIntegrityEvolution`), the registered claims are renamed under the map, and
  `Legitimacy` is the new top-level structure.
- The new definition lives in `lean/Workspace/Deference/Contrib/Legitimacy.lean`, not in
  the normativity tree, because authorship and transparency are deference objects; the
  normativity tree keeps the record half.
- The old file `LegitimateEvolution.lean` remains as the alias shim for one release, so
  one file name in the old vocabulary survives on purpose.
- The `LegitimateSegment.project`-style names in the activation files are renamed
  without aliases: they are unregistered.
- PR #105 and #106 are combined rather than rebased separately.

## What is not shown

That any real interaction's channels are the declared ones; the causal reading of
`Realizes`; that a real evaluator's window values lie in `(D − ϖ, 0]`; the audit's
calibration; anything about the number or cost of reports under a cumulative threshold.
Every **FIX** is a finite exact model.

## Outstanding maintainer actions

1. Confirm or reverse the two agent-decided points: Robust Openness external; the names
   *internal/external*.
2. Choose the window default (`0`, or the tie-breaking value just below).
3. Remove the deprecated-alias shim `LegitimateEvolution.lean` after one release.
