# Report — Cartesian frames × deference exploratory bridge

**Round:** `prompts/2026-08-12-cartesian-frames/`
**Prompt-author model:** GPT-5.6 Sol (OpenAI)
**Executor model:** Claude Opus 5 (Anthropic)
**Dates:** dispatched 2026-08-11, executed 2026-08-12
**Write scope:** granted by the dispatch (§XIII, §XVII, §XXI).

**Verdict: mixed.** Positive on the static control separation and on representing
foreclosure in two distinguishable forms; **negative** on delegation versus accurate
simulation; untouched on authorisation, computational futurity, competence and leakage.
Within the positive half nothing but representation follows — no corrigibility or deference
inequality.

**The round was first written up as representation-positive, and its own adversarial review
refuted the argument that carried the headline.** `REPORT-red-team.md` lists thirteen
findings, all accepted, and what each changed. The two that moved the verdict are that
`≃ᵇ`-invariance does not exclude labels, and that a process accurately predicting the
principal is not separated from delegation.

The consolidated result is `projects/deference/notes/CARTESIAN_FRAMES_DEFERENCE_BRIDGE.md`
and its human register beside it. This report carries what those documents are not for:
the deviations, the reasoning behind the build decision, what was not shown, and the
outstanding actions.

## 1. What was produced

| deliverable | path |
|---|---|
| verification register | `projects/deference/notes/CARTESIAN_FRAMES_DEFERENCE_BRIDGE.md` |
| human register | `projects/deference/notes/CARTESIAN_FRAMES_DEFERENCE_FOR_HUMANS.md` |
| in-repo Lean | `lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean` — 46 declarations |
| authoritative-surface cross-check | `prompts/2026-08-12-cartesian-frames/artifacts/CFCrossCheck.lean` — 35 declarations |
| red team | `prompts/2026-08-12-cartesian-frames/REPORT-red-team.md` |

## 2. Answers to the stopping rule (§XX)

1. **Equal realized behaviour, distinct control structure?** Yes.
   `pin_delegated_eq_pin_simulated` (equality by `rfl`) with
   `delegated_not_biextEquiv_simulated`. What makes this more than a relabelling is
   weaker than first claimed — see §4b of the bridge document.
2. **Delegation from simulation?** **No**, for the case the dispatch posed. A process
   accurately predicting the principal has output depending on the principal's
   disposition, and Cartesian frames identify that with delegation; the invariant is
   crude enough that a process executing the principal's *opposite* is also equivalent to
   delegation (`simRead_not_biextEquiv_delegated`). Separated only when the other process
   supplies a **fixed** value that happens to coincide.
3. **Preservation versus foreclosure of future corrective agency?** Yes, in two distinct
   forms, proved not to be interchangeable. What is represented is *what is lost*, not how
   a present act loses it, and not who holds a transferred coordinate.
4. **Which relation or operation carries each distinction?** `≃ᵇ` (Definition 7) carries
   the static separation; `Commit` with proper `◁₊` (Definitions 18/28, Claim 30) carries
   restriction; `External^{/}` with `◁ₓ` (Definitions 19/32, Claim 34/45) carries
   transfer; `image` separates the two. The subagency halves are universal schemas — the
   content is the `≃ᵇ` identifications and the properness.
5. **Which Stage III–V negatives are repaired?** None. The diagnosis is sharpened; no
   earlier statement is refuted or weakened. §6 of the bridge document classifies each
   obstruction.
6. **Which remain untouched?** Computational futurity (Q4), competence/calibration,
   near-indifference leakage (item 25), capability/admissibility conflation, and — as of
   the review — delegation versus accurate simulation.
7. **Are finite factored sets needed next?** No, and escalating now would be premature —
   the missing structure identified is an agent-side counterfactual coordinate in the
   deference signature, which Cartesian frames already supply. The dispatchable next
   target is a signature change, not a second formalism.

## 3. Deviations from the prompt, and why

**§XIII, round location.** The dispatch suggests
`projects/deference/rounds/2026-08-12-cartesian-frames-bridge/` "or repository-conventional
equivalent". Both conventions exist and they are not interchangeable: `projects/<line>/rounds/`
holds round trees that ship their own `src/` and `tests/run.py`, as the four leverage rounds
do, while a round whose code is Lean puts its dual register in the line's `notes/` and its
declarations under `lean/Workspace/`. This round produces no runner, and the Stage-V round is
its exact precedent, so the two deliverables sit beside `LI_NATIVE_DEFERENCE.md`, which they
extend. The round record is `prompts/2026-08-12-cartesian-frames/` either way.

**§XIII, dependency handling — the substantive one.** The dispatch prefers "referencing or
pinning the FAF branch". The branch is not pinned, and repinning `lean/lakefile.toml` is a
**trust-chain change** (`AGENTS.md`, *The trust chain*, item 2), which is a maintainer
decision with a dated `DECISIONS.md` entry, not a round's to take. Repinning to an
unmerged feature branch would additionally make this repository's entire verification stack
depend on a branch that can be rebased — and that risk was not hypothetical: the branch
advanced twice during the round and then merged to upstream `main`, invalidating the commit
this report first recorded. Every reference now names `e13dc5b`, where the cross-check is
verified. Because the library is now on `main`, the objection to repinning has dissolved;
that is in the `DECISIONS.md` entry.

The round therefore mirrored the fragment of the library the constructions need, which
§XIII explicitly permits, **and then removed the risk that a mirror introduces** by
compiling every result a second time against the authoritative definitions in
Formalized-Agent-Foundations. Both surfaces are axiom-clean. This is stronger than either
option the dispatch anticipated: the in-repo file is gated, and the cross-check shows the
mirror did not weaken anything.

**§VI, `commit` first.** Followed. `Commit` was tried first and works; externalization was
then tested as the dispatch's "second possible model" and also works, on a genuinely
different case. The dispatch's guess that externalization is "more interesting" is
half-right — the two model different things, and §4e of the bridge document gives the
invariant that tells them apart.

**§XII, "do not re-formalize the CF paper".** The mirror is ~200 lines covering fourteen
definitions and three claims — Claim 39 in one direction, Claim 30, and Claim 34/45 at
the one-cell partition — plus the unnumbered `image` invariance the paper uses silently. It
is written to make the exploratory model executable, not to reproduce the library. The
correspondence table is in the file header.

**Correction to the dispatch.** §II lists the branch contents "at the time of dispatch".
`assume` (Definition 29) and `internal` (Definition 33) are present but were not needed;
Claim 35 is formalized only in its Commit/Assume half, by ruling, because its
External/Internal half is ill-typed as printed. Nothing this round used depends on the
excluded half.

## 4. What this round does not establish

Stated fully in §7 of the bridge document. The four that matter most:

- **Control is not authorisation.** `AgentInert` measures counterfactual power. A frame
  where an unauthorised process holds the agent coordinate is indistinguishable from one
  where a rightful principal does. The deference line's jurisdiction object is not
  supplied.
- **Cartesian frames do not derive who the agent is.** The agent/environment split is
  written down by the modeller. The improvement over item 28's `jurisdiction : Bool` is
  that the split determines a whole counterfactual structure checked by a `≃ᵇ`-invariant,
  rather than being a payload no formula reads. That is a bounded improvement, not a
  derived object.
- **The separation needs a coordinate the current signature lacks.** Every witness lives in
  the counterfactual column where the principal's disposition differs from the one held.
  The realisation map has already quotiented that away.
- **Structural futurity only.** Every frame here is finite and presently computable.
  "Later" is stipulated, there is no transition, and Q4 is untouched.
- **Delegation versus accurate simulation fails**, and the neighbouring case that succeeds
  is not the one the obstruction was about. The review's C2 and C3.

## 5. Structural defect found

**The trust chain cannot express a dependency on an unmerged upstream branch.** This
repository pins one Formalized-Agent-Foundations commit and inherits its solver stack. A
round that needs a formalization living on an upstream *feature* branch has no route to it
that is not a trust-chain edit, and a trust-chain edit is a maintainer decision. The
available moves are all bad in different ways: repin to a rebaseable branch commit, vendor,
mirror, or drop the dependency.

This round mirrored and cross-checked, which is the honest version and cost real work. The
defect is filed under `PRIORITIES.md` *Workspace friction* as
*Upstream work on a feature branch is unreachable without a trust-chain edit*. Whether to
change anything is the maintainer's; the report is the obligation.

Separately, the results here are unregistered, which is the already-filed friction entry
*The deference line has no claims registry*, not a new defect.

## 5b. The review's effect on this round

`REPORT-red-team.md` carries all thirteen findings and their disposition. Four changed what
this round claims rather than how it says it: the "not a label" argument was refuted and
replaced by a weaker world-map argument; the delegation-versus-simulation row went from
*partial* to *no*; the externalization arm was shown not to represent a second agent at
all; and the dispatch's H1, as literally stated, was shown to **fail** on this pair.

Two of those became new Lean, on both surfaces: the label adversary
(`labelledHuman_not_biextEquiv_labelledAgent`, `mapWorlds_forgetLabel`) and the
dependence-not-agreement family (`simRead_not_biextEquiv_delegated`). A round that reports
a negative control as passed when it does not is the failure this repository's adversarial
norm exists to catch, and it caught one here.

## 6. Gate status

| gate | status |
|---|---|
| `lake build Workspace` | green, 2634 jobs |
| `#print axioms` on the new file | 46 declarations, all within `[propext, Classical.choice, Quot.sound]` |
| sorry-free | yes |
| `tests/run.py` | green |
| cross-check compile | green in Formalized-Agent-Foundations at `e13dc5b`, 35 declarations, all within the allowed three |

The cross-check file lives under `prompts/` and is deliberately outside `lean/Workspace/`,
so it is not in the `lean` gate: it cannot be, since it imports a library this repository
does not pin. Re-verify it by copying it to the root of a Formalized-Agent-Foundations
checkout on branch `cartesian-frames-formalization` and running
`lake env lean CFCrossCheck.lean`.

## 7. New names introduced, all provisional

| name | what it is |
|---|---|
| `AgentInert` | the agent coordinate does not move the world; the separating property |
| `pin` | restriction of the agent coordinate to the choice actually taken; proved `≃ᵇ Commit^{a}` |
| `World`, `delegated`, `simulated`, `preserve`, `foreclose`, `transfer` | the world type and the four frames it names |
| `PresentAction`, `presentStage`, `futureFrame` | the two-stage model: the present action type, the present frame, and the map to the induced corrective frame |
| `simRead` | the family of processes executing a function of the principal's disposition |
| `LabelledWorld`, `labelledHuman`, `labelledAgent` | the negative-control adversary: a controller label that passes the invariance test |
| `commitment view` | prose name for `mapWorlds p ∘ pin`, the projection under which the architectures agree |
| `totalSetoid`, `constSection` | the one-cell partition and its constant sections |

The mirrored names (`Frame`, `Hom`, `Homotopic`, `HomotopyEquiv`, `collapse`, `BiextEquiv`,
`commit`, `mapWorlds`, `externalQuot`, `partitionSections`, `AddSubagent`, `MultSubagent`,
`image`) are the authoritative library's and are not this round's to name.

## 8. Outstanding maintainer actions

1. **Rule on whether to pin the Cartesian Frames library.** Decide whether
   `lean/lakefile.toml` should move from `1fffea44eece253cda1722568a3adfe34e822f03` to a
   commit carrying `CartesianFrames/` — now available on
   `main`, at `e13dc5bd0117486b1947fbb5643045e14743e98d`. The library reached the upstream
   default branch during this round, so the objection that made repinning unattractive is
   gone. Doing it would put the cross-check's results inside the `lean` gate and retire the
   mirror. Waiting costs the mirror's maintenance. Nothing is blocked either way — both Lean
   surfaces are green today. Appended to `DECISIONS.md`.
2. **Rule on graduating Q3.** `PRIORITIES.md` Q3 asks how foreclosure is expressible and
   says what is missing is "the object, and possibly the depth". This round supplies a
   candidate object for *what is lost*, with a Lean witness, and closes neither of the two
   holes Q3 actually names — no operation reassigns anything at a later index, and the
   interface is still one index deep. Whether that is enough to graduate is the ruling.
   Graduating a Q-entry is a maintainer act; this round updated Q3's text and did not file
   the item. Appended to `DECISIONS.md`.
3. **Rule on the next target.** §9 of the bridge document proposes restating the Stage-V
   factorization theorem over a signature carrying a frame and the choice actually taken.
   It is dispatchable, and it is a re-instantiation of an existing theorem with a better
   inhabitation witness rather than a new theorem — worth filing for the witness or not at
   all. Filing it is a maintainer act. Appended to `DECISIONS.md`.

## 9. Cross-pollination noted, not pursued

The dispatch's §XIX asks for obvious future questions only. One: the leverage line's
answerability and lawful-repair scopes are currently indexed by the learner. If control
structure turns out to be the right index for jurisdiction here, the same question — whose
frame is a repair scope defined relative to — arises there. Not pursued, and no connection
was forced.
