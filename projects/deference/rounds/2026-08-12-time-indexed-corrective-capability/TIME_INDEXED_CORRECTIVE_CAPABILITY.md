# A cut-time family of effective-control states

**Status:** `ci-only`; verification register for
`prompts/2026-08-12-time-indexed-corrective-capability/`.
Human register: `TIME_INDEXED_CORRECTIVE_CAPABILITY_FOR_HUMANS.md` beside this file.
Names introduced here are provisional (`AGENTS.md` standard 6).

## Verdict: `Mixed`

**Foreclosure is not yet expressible, and the round now knows why.** The construction
was built, adversarially reviewed, and the review broke two of its three headline claims.
The refutations are folded in as machine-checked theorems rather than answered, because
they are the round's most valuable output: they identify a single missing primitive that
everything else traces to.

| earned | not earned |
|---|---|
| endpoint/capability orthogonality, on this model, as two exact finite witnesses | genuine temporal depth — the cut is a **freeze**, not a counterfactual sibling |
| irreversibility propagating along a fold and across the family | same-immediate/different-future — the difference is immediate, under a stipulated observable |
| a non-vacuous, causally-attributing foreclosure predicate with a unique event time | simulation resistance — stipulated, not shown |
| shared history genuinely enforced by the definitions | no-hidden-label — the certification passes for the designated inert label |

**The missing primitive, stated exactly:** for a cut to produce a *continuation* rather
than a *freeze*, the state must have dynamics that run without the advisor —
`step .idle ≠ id`. Every failure below traces to its absence.

This is a representation round. Nothing here bears on corrigibility, jurisdiction,
competence, or the value of retained correction, in any direction.

## 1. What was built

`lean/Workspace/Deference/Contrib/TimeIndexedCapability.lean`: 18 audited declarations,
`sorry`-free, each auditing to `propext` alone — a proper subset of the allowed three.

A run is a fold of advisor actions over a state. `cut π n` silences the advisor from time
`n`; `cutRun π n k s` is the state at time `k` in the continuation cut at `n`;
`corrFrame s` is the principal's corrective situation as a Cartesian frame whose agent
carrier is the corrective choice; `HasCorr s := ¬ AgentInert (corrFrame s)`.

```lean
def Forecloses (π : Policy) (m : ℕ) (s : St) : Prop :=
  (∀ k, k ≤ m → HasCorr (cutRun π m k s)) ∧
    (∀ n k, m < n → m < k → ¬ HasCorr (cutRun π n k s))
```

## 2. The adversarial review, and its disposition

An independent review ran in a separate context with the file and the dispatch's fourteen
attacks, and without this round's reasoning. Every finding below was **accepted**; none
was argued down. Each is now a theorem in §10 of the Lean file or a correction to a
docstring.

| # | finding | disposition |
|---|---|---|
| 1 | `step .idle = id`, so the cut freezes the run rather than continuing it. `cutRun π n k s = run π (min n k) s` — the "family of siblings" is the family of prefixes | accepted; `cutRun_eq_run_min` added |
| 2 | `Forecloses` therefore has no family content: it says the actual run is coupled at `m` and severed at `m+1` | accepted; `forecloses_iff_one_step` added; the definition's docstring corrected, which had claimed the opposite in terms |
| 3 | clause 1 of `Forecloses` never observes the cut, being quantified exactly where `cutRun_shared_history` says the cut is inert | accepted; recorded in the docstring |
| 4 | `cut_before_sever_preserves` does not prove that an early cut prevents anything — same range problem — and its hypothesis needlessly forbids `shift` | accepted; `honest_prevention` added with the correct quantifier and the weakened hypothesis; the original's docstring now warns |
| 5 | "the outcome function reads it" certifies nothing: the same construction works for `St.spurious`, the designated inert label | accepted; `spurFrame`, `spurFrame_agentInert_iff`, `spur_cardinality_control` added; the bridge docstring corrected |
| 6 | `HasCorr` is definitionally `coupled = true`; the frame import is eliminable | accepted; already partly conceded in the header, now stated plainly |
| 7 | `cardinality_is_not_capability` is a decoy — a free-floating frame unconnected to the model, and it passes for the label too | accepted; `spur_cardinality_control` records it |
| 8 | `exercise` is not a transition, is read by nothing, and `prediction_does_not_confer` is `false = false` with the predictor never applied | accepted; docstrings rewritten to call it a stipulation |
| 9 | `Actor` is the `authorization : Bool` the file claimed to avoid | accepted; §5 |
| 10 | the ratchet is stipulated in `step`, and the docstring denied this while stating it; `coupled_antitone` was cited and does not exist | accepted; docstring rewritten, dangling reference removed |
| 11 | five internal section references off by one | accepted; corrected |
| 12 | T3's difference is immediate, not future, and the witness has no cut content | accepted; docstring corrected |
| 13 | T5's endpoint clause is `rfl`-true because the endpoint never moves in either run | accepted; §4 |
| 14 | the corrective capability corrects nothing — `CWorld` is causally disconnected from `St` | accepted; §5 |

The review also confirmed four things in the construction's favour, which are kept:
causation is derivable rather than assumed (`Forecloses π m s` entails the advisor acted);
the foreclosure time is unique; the boundary conventions are forced; and shared history is
genuinely enforced by `run_congr` and `cutRun_shared_history` rather than stipulated.

## 3. Test results, after the review

| test | verdict | why |
|---|---|---|
| **T1** genuine temporal depth | **fail** | `cutRun_eq_run_min`. The index is not an arbitrary numeral — it is worse than decorative, it is *derivable from time*. Shared history is real; the continuation is not |
| **T2** effective corrective capability | **partial** | genuinely two-valued, genuinely not cardinality, not faked by duplicate actions — but a `Bool` field wrapper whose frame certification excludes nothing (`spurFrame_agentInert_iff`), and which corrects nothing in the model |
| **T3** same immediate, different future | **fail as stated** | the capability differs at the *next* state; the cut indices carry nothing; `executed` is a stipulated projection nothing consults. What is shown is observational coarseness |
| **T4** ratchet / non-restoration | **partial** | propagation along the fold is proved; irreversibility is stipulated in `step`; the cut half is free by finding 1. Prevention required `honest_prevention` to state properly |
| **T5** endpoint preserved, capability lost | **pass, degenerate** | `rfl`-true because `endpt` never moves in either run |
| **T6** endpoint moved, capability kept | **pass** | genuinely informative |
| **T7** accurate-simulation control | **fail** | a stipulated channel monopoly, proved by `rfl`, in a function no run reads |
| **T8** no hidden-label cheat | **fail** | the certification passes for the file's own designated label |

Per the dispatch's §XII this is `Mixed`: T5 and T6 pass and establish the orthogonality,
T2 and T4 pass in weakened form, and T1, T3, T7, T8 fail — informatively, and all for one
reason.

## 4. What is genuinely established

**Endpoint preservation and capability preservation are independent.**
`endpoint_capability_independent` carries two exact finite witnesses, one in each
direction. This is the one result that survives the review intact, and it is the round's
positive contribution.

Its scope, stated exactly. `endpt` is a two-valued coordinate with no belief dynamics, no
market and no inductor; and the T5 half is `rfl`-true because the endpoint never moves in
either run rather than because a nontrivial dynamic returns it to the same place. The
witnesses separate the two *notions* on this model. They are **not** a theorem about the
source corpus's influence-defect construction, and nothing here confirms or refutes
anything in it.

**Shared history is real.** `run_congr`, `cutRun_shared_history` and `cutRun_agree_below`
are facts about the fold, proved by induction rather than stipulated. The review attacked
this and failed. It is the one piece of the temporal apparatus that works, and it is
reusable by a successor.

**Foreclosure attributes causally, and to a unique time.** The review verified that
`Forecloses π m s` entails the advisor performed a severing action at `m`, and that `m` is
unique — the state cannot lose coupling exogenously. That is the right shape for a
foreclosure predicate. The problem is what it is a predicate *of*.

## 5. Does authorization disappear into capability gating?

The dispatch's optional question. **No, and the round's attempt at it failed.**

`exercise` was intended as a capability-gated transition separating exercise from accurate
prediction. It is not a transition — its type is `Actor → Bool → St → Bool`, it produces
no state, and nothing in `step`, `run`, `cutRun` or `Forecloses` reads it.
`prediction_does_not_confer` is `false = false`; the quantified predictor is never applied.
So the model *asserts* that the advisor has no channel to the corrective effect rather
than showing it, and `Actor` is exactly the `authorization : Bool` the round set out to
avoid — a tag read by one function nothing else calls.

The honest answer to the dispatch's four sub-questions:

1. *Does it separate exercise from accurate prediction?* Not as built. A stipulated
   monopoly is formally indistinguishable from an authorization predicate.
2. *Does it capture the theorem-relevant meaning of jurisdiction?* No. `Actor` records
   who acts, not who is entitled to.
3. *Is a further provenance relation mathematically necessary?* **Unknown** — the round
   did not reach the point where the question is well-posed.
4. *Can the advisor forge, seize or bypass?* Not modelled at all, which is weaker than the
   roadmap's requirement that such lapses sit in a theorem's hypotheses.

A further defect the review named: **the corrective capability corrects nothing.**
`CWorld` is causally disconnected from `St`, so exercising the correction flips a bit that
no step, no run, no endpoint and no coupling reads — it cannot restore the coupling, undo
the advisor's act, or move the endpoint. "Corrective" is carried by naming.

## 6. The standing obstructions

No row is marked repaired because a new field names it.

| obstruction | repaired? | how, or why not |
|---|---|---|
| same realization, different jurisdiction collapses | **no** | the witness shows coarseness of a stipulated observable that nothing consults, at the immediately following state. A restatement of the static-view factorization, not a temporal separation |
| accurate simulation substitutes for delegation | **no** | §5. Stipulated, not shown; the Cartesian-frames round's negative is cited in prose and never engaged formally |
| future corrective agency absent from the model | **partial** | the corrective situation is a first-class object at every state and `HasCorr` is a property of it — but it is causally disconnected from the run |
| foreclosure not expressible | **no** | `Forecloses` is well-formed, non-vacuous and causally attributing, and `forecloses_iff_one_step` shows it is a two-frame statement on one trajectory. That is a coupling-flip predicate, not foreclosure |
| interface only one decision index deep | **no** | the run has many steps, but the family collapses onto it, and nothing connects any of it to the finite model skeleton's execution layer or any `V`-register |
| authorization/capability conflation | **no** | §5 |
| computational futurity | **no** | no resource-indexed process state; Q4 untouched |
| competence / near-indifference leakage | **no** | no competence hypothesis appears; items 24 and 25 untouched |
| endpoint legitimacy vs authority conflation | **yes, on this model** | §4, with the scope stated there |

## 7. Evidence classes

| statement | class |
|---|---|
| every declaration in `TimeIndexedCapability.lean` | Lean-established, `propext` only, **unregistered** |
| `AgentInert` and the frames it is applied to | source-theorem fact via the in-repo mirror |
| the eight test verdicts | exact finite witnesses |
| `cutRun_eq_run_min`, `forecloses_iff_one_step`, `spurFrame_agentInert_iff` | **negative results**, machine-checked |
| the endpoint/capability orthogonality | exact finite witness, on a deliberately degenerate model |
| `Forecloses` as a definition of foreclosure | architectural interpretation, and §6 records it as not earning the name |
| `coupled` as "the principal's corrective channel", `endpt` as "a deliberative endpoint" | architectural interpretation |
| the missing primitive `step .idle ≠ id` | structural argument, from the machine-checked collapse |
| that a model with autonomous dynamics *would* pass T1 | **conjecture** — not built, not tested |
| that the advisor cannot forge or seize the capability | **not established** — not modelled |
| anything about the value of retained correction, or about jurisdiction | **not established** — no normative premise is added |

**Nothing here is registered.** The deference line has no claims registry, so by this
repository's standard the line still establishes nothing.

## 8. What this does not establish

- **No corrigibility theorem, and no progress toward one this round.** The representation
  gap the round set out to close is still open.
- **The next theorem's shape is not recorded.** The dispatch permits it only if T1–T8
  substantially pass. They do not, so it is omitted deliberately.
- **No claim that the approach is wrong.** The collapse is a property of *this* model's
  dynamics. Whether a model with autonomous dynamics passes T1 is untested.
- **No claim about the source corpus.** Its sealed-sibling construction is a family of
  *continuing* deliberations; this model's cut produces a frozen prefix. That the two are
  different is precisely the finding — a fact about this model, not a criticism of the
  source.
- **Nothing about forging, seizure or bypass**; nothing about computational futurity;
  nothing about competence.
- **The Cartesian-frames round is not weakened.** Its results stand; this round shows that
  one intended *use* of `AgentInert` does not carry what was hoped, which is a fact about
  the use.

## 9. What a successor needs

One thing, and the round is confident about it because the collapse is machine-checked:

**Give the state dynamics that run without the advisor.** `step` must take a step even on
`idle` — an environment process, a principal who acts, or a deliberation that continues.
Then `cut π n` produces a genuine sibling: a continuation sharing history up to `n` and
diverging after it, which is what the source corpus's construction has and this model does
not. `cutRun_eq_run_min` fails immediately, and T1, T3 and the family content of
`Forecloses` become live questions rather than settled negatives.

Two further requirements the review exposed, both cheap once the first is fixed:

- **Wire the corrective capability into the run.** Exercising it must change something the
  run reads, or "corrective" is naming.
- **Either make the simulation control a theorem or drop it.** A gate nothing reads is a
  stipulation. The honest alternatives are to make `exercise` a real transition on `St`
  and prove the separation, or to state the monopoly as a modelling assumption in the
  hypotheses of whatever theorem consumes it.

`honest_prevention`, `cutRun_shared_history` and `cutRun_agree_below` are reusable as they
stand.
