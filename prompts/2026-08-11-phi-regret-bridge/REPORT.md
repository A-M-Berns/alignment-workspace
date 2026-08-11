# Report — fixed-action Φ-regret bridge

**Prompt author:** GPT-5.6 Sol (OpenAI) · **Executor:** GPT-5 Codex
(OpenAI) · **Dispatched and executed:** 2026-08-11 · **Branch:**
`agent/phi-regret-bridge` from `fd844d8`

Start state: `origin/main` was `fd844d8`; the isolated worktree was clean on
creation. The controlling frontier was item 29's fixed-action and non-capture
debt. The preparation runner had 25 tests and the applicability runner had 10.

## Verdict

**Repaired for the frozen item-30 environment.** A fixed eight-label action type
decodes bijectively to each occasion's canonical response set. All nine declared
lawful programs factor through it, and exact charge and regret are preserved.
The finite class has a non-capturing declarative representation. Blum--Mansour
Theorem 18 therefore instantiates with `N=8`, `M=1`, `K=9` and gives a
horizon-tuned learner with expected mixed-action charge regret
`O(ell_max sqrt(8 T log 9))`.

Item 29 is closed-positive. Item 30 is ready and unachieved. Item 31 and F4 are
unchanged. No deference artifact or `DECISIONS.md` was edited.

## Construction

`Lambda` contains two merits directions, default, and decline tolling zero
through four dates. `decode_action` supplies the bound verdict string and derives
the occasion's decision-obligation ledger effect. `encode_response` is its
inverse on the eight canonical responses. It rejects abnormal ledger effects,
so the bridge does not identify repository responses whose future bookkeeping
behavior differs.

The nine programs are immutable records interpreted against a strict public
reason context. Identity, three interval repairs, three toll rules,
`default_declines`, and `withdraw_merits` are executable. The last two have
admitted witnesses. Certificate rejection is an identity branch, including an
already tolled decline whose toll coordinate a ripeness ground does not license
removing.

The commuting equation was checked for every program, label, occasion, and
declared horizon. Pointwise equality lifts to actual, counterfactual, mixed, and
cumulative charge equality. The generic finite-horizon regret-preservation
argument and recurrent-failure inequality are Lean-proved with witnesses.

## Non-capture

The program record has no callable field. Its context has no charge, tariff,
account, balance, future, horizon, saving, or profit field. Legacy replay
callbacks capture only the immutable program. The finite audit also pins the
five default policy functions and rejects policy closures capturing environment
objects. This result covers exactly the nine programs and default policy; it is
not a sandbox for arbitrary Python callbacks.

## Source theorem and consequence

The source fact is Blum and Mansour (2007), §7, Theorem 18. Its fixed finite
actions, finite rules and selectors, predictable history-indexed maps, bounded
full-information loss, row-conditioned weights, and stationary distribution all
have explicit frozen-environment counterparts. Scaling `[0,2]` charge to
`[0,1]` and back gives the displayed bound. The source controls mixed-action
loss. Expected sampled charge follows from sampling that mixture; no pathwise or
high-probability trajectory claim is made. The source proof optimizes `beta`;
this round adds no anytime tuning for one infinite run.

If the learner assigns total mixed-action mass at least `rho*T` to source labels
where a fixed audited program saves at least `delta>0`, with distortion at most a
horizon-independent `B`, then expected regret is at least
`rho*delta*T-B`. This contradicts `o(T)`. The conclusion retires expected mass on
recurrent certified failures represented in the nine-program class; a realized
sample-path conclusion needs the separate sampling result not supplied here.

## Evidence classes

- **Lean-proved, unregistered:** eight-element cardinality, generic
  regret-preservation lemma, recurrent-failure lower bound, and inhabitation
  witnesses.
- **Exact test-supported:** encode/decode, canonical adequacy, all commuting map
  entries, closure, charge/regret preservation, expected mixed preservation, and
  the additive-boundary checks.
- **Finite audited:** nine data programs, legacy-adapter captures, and default
  policy captures.
- **Derived from a primary source:** the `N=8`, `M=1`, `K=9` Theorem 18
  instantiation and expected-regret bound.
- **Open:** item-30 implementation, measured curves, sampled-path concentration,
  comparator coverage, and answerability/integration of the learner.

## Deviations

1. `origin/main` did not yet contain the controlling applicability round because
   draft PR #19 was unmerged. The isolated branch was created from current
   `origin/main` at `fd844d8`, then the two PR #19 commits were cherry-picked so
   the requested artifacts and Near-miss verdict were explicit inputs. The final
   PR therefore contains both the audit and its repair.
2. The prompt allowed either a finite audit or a capability-safe representation.
   The result uses a small data-only program representation plus a finite audit
   of the remaining default policy functions; no general DSL was built.
3. Item 30 was not run. The round stops after the applicability theorem and
   recurrent-failure consequence.

## What was not shown

The Blum--Mansour proof was cited, not re-formalized. The Python-specific decoder,
certificate checker, and finite program audit are not kernel proofs or registered
claims. No learner, empirical regret rate, exact big-O constant, realized-path
bound, high-probability bound, rule-coverage theorem, moral-correctness theorem,
anytime tuning, or answerability proof for an adaptive learner was established.
The result does not cover endogenous filings, replay-prefix guards, suspension, solvency
coupling, altered service windows, noncanonical responses, multiple same-date
occasions requiring post-hoc affordability filtering, or arbitrary callbacks.

## Verification

- Fixed-action bridge runner: 21 tests passed.
- Applicability and preparation runners: 10 and 25 tests passed.
- House suite: all gates and all five discovered project runners passed; the
  suite's optional Lean phase was followed by an explicit `lake build` below.
- `lake build`: passed (2,634 jobs). The axiom audit accepted 182 printed
  results across 13 files, all within `propext`, `Classical.choice`, and
  `Quot.sound`.
- `git diff --check`: passed.

## New provisional names

`SemanticAction`, `LawfulProgram`, `RuleContext`, the `PB-` evidence identifiers,
and “Frozen Lawful Φ-Regret Theorem” are provisional pending maintainer naming.

## Maintainer handoff

1. **Verdict:** repaired within the frozen environment.
2. **Fixed representation:** yes, exactly eight labels.
3. **Encode/decode:** occasion-local canonical-response bijection; ledger effects
   derived only at decode.
4. **Comparator factorization:** yes for every entry of all nine maps.
5. **Charge/regret preservation:** exact, pointwise through cumulative and mixed
   loss.
6. **Nine programs:** all materialized; all eight nonidentity rules inhabited.
7. **Non-capture:** established for the finite data class and default policy;
   arbitrary callbacks excluded.
8. **Theorem mapping:** fixed `N=8`, always-on `M=1`, audited `K=9`, predictable
   maps, bounded full information, stationary `8 x 8` matrix.
9. **Bound:** `O(ell_max sqrt(8 T log 9))` expected mixed charge regret for the
   horizon-tuned source learner.
10. **Sampling:** expectation only; no pathwise/high-probability statement.
11. **Corollary:** positive-density expected mixed mass with uniform certified
    saving forces linear regret modulo bounded `B`, contradicting `o(T)`.
12. **Philosophy:** the theorem learner cannot retain positive expected mass on
    represented recurring lawful charge failures.
13. **Unjustified:** global normative adequacy, coverage, convergence, and
    answerability of the item-30 learner.
14. **Verification:** all project, house, Lean-build, axiom, and whitespace
    checks recorded above passed.
15. **Files:** new bridge round, one Lean module/provenance file, prompt/report,
    and leverage state/index/provenance reconciliation.
16. **Research state:** item 29 closed-positive; item 30 open-ready; item 31 and
    F4 unchanged; no decision added.
17. **Commit and PR:** recorded after publication.

## Outstanding maintainer actions

None created by this round.
