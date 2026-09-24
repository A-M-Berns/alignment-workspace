# The transparent channel realized in the evaluation ecosystem

Second pass of the round; dispatch in `../../../../prompts/2026-09-24-transparent-channel/PROMPT.md`
(second dispatch).  Lean: `lean/Workspace/Deference/Contrib/TransparentEcosystem.lean` (22
audited declarations) and `TransparentChain.lean` (6), both `[propext, Classical.choice,
Quot.sound]` only, importing the landed `EvaluationEcosystem`, `TransparentChannel` and
`ReasonDiscovery`.  Fixtures: `tests/test_ecosystem_views.py` (the candidate views run in
the committed-principal-program simulator), 33 tests in all.  Labels **LEAN**, **FIX**,
**EXT**, **OPEN** as before.

## A. Verdict

1. **Does the abstraction simplify the concrete ecosystem?**  Yes, for two of its four
   channels, and by making hypotheses explicit rather than by removing them.  The
   activation channel's reference is realized by the landed architecture for *every* log
   (`payload_take`: the answering process reads only the prefix through the commit), so
   item 89's "sealed comparison" becomes one checkable log condition, *the candidates'
   logs agree through the commit event*.  The reason channel's reference is the admitted
   part of the advisor's permitted view plus the advisor's declared program on that view;
   it is realized exactly when the advisor's admitted contribution is that program's output
   (`realizes_reason`), the upstream twin of `reasonMediated_of_reexecution`, and clause 6
   follows from it plus a selection-blind view (`selectionBlind_ecosystem`).  The
   specification channel has depth zero (no amendment event exists) and the
   inquiry/supplier channels are not this ecosystem's to realize.
2. **Does it eliminate an open item?**  No item closes.  Item 89 loses its architecture
   question inside the single-log model: sequenced settlement *is* shared-prefix
   activation, proved; an isolated hindsight evaluator is not expressible in one log and
   stays EXT.  Item 87 clause 6 loses its prose: two log conditions and one missing event
   kind (an advisor mandate) remain.  Items 68 and 72 are as the first pass left them.
3. **Does the quantitative theorem become cleaner?**  Yes.  `li_noncapture_chain3` is
   `li_noncapture` three times with shared middles, and the first link's certified quantity
   is the content defect `τ_R` (`tauR`, the sensitivity mass of the symmetric difference
   between actual and reference content), which is `0` under `realizes_reason`.  Manipulation
   is charged in a link of its own, separately from the reference's service and discovery
   limits.
4. **Should the concept become canonical?**  Not yet, and not under the first pass's
   name.  The existential `Transparent` is the wrong export: on the reason channel it is
   vacuous with the whole log as input, false with the empty input, and across different
   advisors it fails *for honest persuasion* unless the advisor's declaration is part of the
   input (`test_class_relative_needs_the_declaration`).  The contract with content is
   `Realizes κ`, faithfulness to a declared reference.  Canonicalize after item 97 lands the
   advisor-mandate event; until then, promote one lemma (§F).

## B. Theorem spine, in dependency order

| # | Lean | statement | status |
|---|---|---|---|
| 0 | `EvaluationEcosystem.reasonMediated_of_reexecution` | payload factors through the trace at commitment | landed |
| 1 | `TransparentChannel.Realizes`, `Transparent`, `transparent_iff_realizes` | the primitive and its class/reference equivalence | first pass |
| 2 | `TransparentEcosystem.view`, `content`, `content_eq` | the permitted view; the trace as a multiset splits into the view's admitted part and the advisor's part | **LEAN**, new |
| 3 | `evalTerm_perm`, `evalProg_perm` | every trace program is extensional on the multiset | **LEAN**, new |
| 4 | `reasonMediated_content` | (0) strengthened to the multiset trace | **LEAN**, new |
| 5 | `κR`, `realizes_reason` | the reason channel realizes `admitted view + declared program (view)` iff the advisor's contribution is its declared program's output | **LEAN**, new; the hypothesis is the committed-advisor condition |
| 6 | `selectionBlind_ecosystem` | (5) + selection-blind `(view, declaration)` + shared activated mandate ⇒ `SelectionBlind payload` | **LEAN**, new — item 87 clause 6 on the concrete frame |
| 7 | `validAnswer_take`, `firstResolver_take`, `payload_take`, `activated_take` | activation and payload are readings of the prefix through the commit | **LEAN**, new — a theorem about the landed architecture, no hypothesis |
| 8 | `realizes_activation`, `activation_eq_of_shared_prefix`, `mismatch_zero_sequenced` | the activation channel realizes "the answering process on the pre-commitment record" for every log; shared prefix ⇒ common activation ⇒ `M = 0` | **LEAN**, new — item 89 |
| 9 | `xSpec`, `realizes_spec` | the mandated program is a reading of the issue events; the tower has depth 0 | **LEAN**, new (trivial by design) |
| 10 | `TransparentChain.tauR`, `abs_sub_le_tauR`, `omission_le_adverse`, `tauR_le_disagree` | the content defect; verdicts move by at most it (`sensitive_symmDiff`); omission form (`adverse_union`); bounded by total mass × disagreement | **LEAN**, new |
| 11 | `li_noncapture_chain3` | `𝔼ₙ(U_actual) − 𝔼ₙ(U_full) ≲ₙ L·(τ_R + (α + β))` | **LEAN**, new — `li_noncapture` ×3 |

Witnesses (**LEAN**, kernel-checked on `Instance.w1` and its variants): `leak_not_transparent`
(same view, different content), `view_overRich` (whole log: the leak realizes the identity),
`persuasion_realizes` (honest and silent both realize their declared programs; the payload
moves), `view_underRich` (empty view: persuasion opaque), `market_view_not_blind` (a
pre-commit `S` event carrying the selection breaks the view's blindness, not transparency),
`sequenced_common` / `sequenced_mismatch_zero` (candidate acts after the commit: `M = 0`
by theorem), `sameBranch_mismatch` (raw commits in time, the gated commit lands after the
session closes: prefixes differ, `M = 1`), `secret_evaluator_not_realized` (the committed
vector is not the program's output; `miscomputation_void` voids it), `spec_w1`.

## C. The ecosystem, edge by edge

```
 advisor q, exterior z ──β──► log
                               │
   view(log, commit) ──────────┤  [defn: the non-advisor pre-commitment events]
   declared program a ─────────┤  [reference-design hypothesis: bound as public data;
                               │   an advisor-mandate event kind is item 97]
                               ▼
        κR (view, a) = admitted(view) + a(view)         ═══ content(log, commit)
                       [realizes_reason: LEAN, under hA "the advisor's admitted
                        contribution is a(view)" — the committed-advisor condition,
                        checkable by re-execution once a is in the log]
                               │
        content ──── evalProg π_P ────► payload            [reasonMediated_content: LEAN;
                                                            re-execution: landed]
   selection σ ──▶ view?   only through a pre-commit S event (market)
                           [market_view_not_blind: a design fact about the world]

 activation:   prefixThroughCommit(log) ──── answering process ────► activated(log)
               [payload_take: LEAN, every log; candidate identity enters only through
                pre-commit events; shared prefix ⇒ M = 0: mismatch_zero_sequenced]
               [same-branch: prefixes differ, M attained: sameBranch_mismatch]
               [log authenticity, the author field: EXT — the ecosystem's one assumption]

 specification: issue events ──── getD o ────► progOf(log, o)    [realizes_spec: LEAN;
                no amendment kind: floor only; secret change voids: landed]

 inquiry/supplier: world, T raises, S routes ──► the view    [α: suffix cut, β: cell gap —
                properties of the reference; evidence soundness, engine ownership of
                selection/stopping: EXT or item 97's declaration; not this ecosystem's channel]
```

## D. The three-link chain

`li_noncapture_chain3` takes the compiled pairs (actual, reference), (reference,
discovered), (discovered, full), each with its content bound, extensionality and sealed
audit, the middle families shared, and concludes

```
E_n(U_actual) − E_n(U_full)  ≲_n  L · ( τ_R + (α + β) )
```

- `τ_R = a₁/b₁`: the certified bound on the first pair's content discrepancy.  Its
  quantity is `tauR L (content_actual) (content_ref)`, the sensitivity mass of the symmetric
  difference; `abs_sub_le_tauR` is the certificate for any `Sensitive` program;
  `omission_le_adverse` is the one-sided form when the actual content omits from the
  reference; under `realizes_reason` the two contents coincide and `τ_R = 0`
  (`tauR_eq_zero_of_eq`), so the chain reduces to the landed `L·(α + β)`.
- `α`, `β`: unchanged, properties of the reference supplier and repertoire.
- The form residual and the audit mismatch are the landed hypotheses `hext`, `hsealed` on
  each pair.  The approximate item-89 charge `D·E[M] ≤ D·(τ_C^raw + τ_C^corr)` is
  world-wise **LEAN** (`TransparentChannel.mismatch_le_disagree`) but not transferred to
  the inductor: that needs a compiled constraint `G_M ≤ G_τ` with its own generability
  certificate, and this pass does not build it.  Under sequenced settlement `M ≡ 0`
  (`mismatch_zero_sequenced`) and the term is absent.

Separation, as asked: manipulation (`τ_R`) ≠ bounded discovery (`β`) ≠ bounded service
(`α`), each in its own link, none baked into another.  A bounded but honest reference is
transparent: `realizes_reason` says nothing about how much the view contains.

## E. Countermodels

| attack | fixture | verdict | classification |
|---|---|---|---|
| leak (selection read off an undeclared source) | `Witness.leak_not_transparent`; `test_permitted_view_separates_the_leaks` (quiet world) | view equal, content differs: **not transparent** | transparency |
| selection read off a declared publication | `market_view_not_blind`; `view_prog` in the market world | transparent, view **not selection-blind** | reference design: what the world publishes before commit |
| marginal-refuted activation | `LICorrigibility.Witness.marginal_refuted`; `sameBranch_mismatch` | marginals equal / mismatch attained; prefixes differ | activation transparency; needs the shared prefix |
| sequenced settlement | `sequenced_common`, `sequenced_mismatch_zero` | `M = 0` by theorem | — |
| secret evaluator change | `secret_evaluator_not_realized`; `test_secret_evaluator_change_is_void` (`miscompute` principal) | the vector is not the program's output; void | transparency of the evaluation channel, closed by re-execution |
| public evaluator amendment | no amendment kind in the ecosystem | not representable; the floor is the mandate | integrity/amendment: a design item, not a transparency failure |
| cherry-picker | first pass, fixture 2 | realizes the reference declaring its selection rule, not the supply reference | reference design / supply (`α`), charged in link 2 not link 1 |
| honest bounded inquiry | discovery rows 2, 14, 17 | transparent; `β > 0` | discovery, link 3 |
| `ShopK` | first pass | no authorized substitute; only silence normalizes | alphabet completeness |
| prohibited channel (direct write) | `covert`; `test_prohibited_channels_are_not_view_failures` | trace transparent to the view; the strict clause voids | authorship / clause 6 strict reading, not transparency |
| over-rich view | `view_overRich`; `test_over_rich_view_certifies_nothing` | everything realizes the identity | representation (the vacuous end) |
| under-rich view | `view_underRich`; `test_under_rich_view_refuses_persuasion` | honest persuasion opaque | representation (the isolated end) |

## F. Vocabulary and canonicalization

Against the five candidates: *transparent mediation* and *transparent influence* fail on
the concrete reason channel, where the existential notion is vacuous, false, or fails
honest persuasion depending on the input; *transparent reason mediation* names the wrong
half (mediation is landed and is not what this adds); *declared-channel fidelity* and
*reference fidelity* name the right thing, `Realizes κ`, and the second is shorter.
Recommendation: `Transparent` stays a class-relative mathematical notion; the exported
contract, if one is exported, is **reference fidelity** of a named channel to a declared
reference, with `Realizes` as its Lean form.  Do not canonicalize now.  Promote one lemma:
`payload_take` / `activation_eq_of_shared_prefix` as the item-89 row of
`wiki/Corrigibility.md` §9, "sealed comparison = the candidates' logs agree through the
commit event (**LEAN** for the landed ecosystem); an isolated hindsight evaluator is not
expressible in one log".  The rest waits on item 97's advisor-mandate event, after which
`realizes_reason`'s hypothesis is a log check and clause 6 is a theorem with two named
log conditions.

## 7. Independence, decomposed

| assumption | reduces to `Realizes`? | what remains |
|---|---|---|
| engine-owned inquiry selection, stopping, candidate generation | yes, once the inquiry policy is a declared program on the evidence (the same pattern as `realizes_reason`); the ecosystem has no such declaration yet | the declaration (item 97); adequacy of the declared repertoire (`β`) |
| evidence-sound outcomes (outcome functions are world-determined) | no | adequacy of the reference as a model of the experiment: EXT |
| exogenous inquiry and service costs | partly: costs are declared inputs in the view, not advisor-writable — a condition on which variables are in `x` | that the *world's* costs are what the view records: authentication, EXT |
| advisor-proof capacity | partly, as above: the registrar's capacity is `S`'s and enters the view | the reference's robustness to flooding is `α`'s theorem, not fidelity |
| adversarial scheduling / releases | no | the suffix-cut theorem is a property of the reference (`α`) |
| availability `η_n → 0` | no | independent (item 87 clause 7) |
| the design of the reference (coverage, cell gap, protected scope) | no | reference design, charged as `α`, `β` |

## 9. Loose ends, stricter

| item | status after realization | the remaining obligation |
|---|---|---|
| 68 provenance adequacy | given a precise interface, still externally assumed | the variation class must contain world counterfactuals (excision, re-simulation); a log carries one member |
| 72 CM2 | clarified only | an exposure-adequacy clause on the reference is a design choice |
| 72 CM5 | secret half discharged by re-execution (`miscomputation_void`, `secret_evaluator_not_realized`); public half clarified only | a trigger rule reading amendment events; no amendment kind exists |
| 87 clause 6 | reduced to a clean system-design condition | (i) an advisor-mandate event so `hA` is a re-execution check, (ii) no pre-commit event carries the selection; then `selectionBlind_ecosystem` closes it |
| 89 | reduced to a clean system-design condition, with the theorem for the landed ecosystem | the two candidates' logs agree through the commit event (sequenced settlement, its ex-ante price unchanged); an isolated hindsight evaluator needs a second log, EXT |
| inquiry causal faithfulness | given a precise interface, still externally assumed | `K_E` as an object; `A = K_E` a fidelity hypothesis; adequacy EXT |
| trigger integrity | the log-model half is a theorem (`payload_take`: activation is a reading of the pre-commit prefix; nothing later writes it) | log authenticity, EXT |
| free amendment | clarified only | no amendment channel; the floor is the mandate |
| provenance normalization | clarified only (first pass) | the substitution's matter map; `ShopK` |
| independent inquiry/supplier | decomposed (table above) | ownership clauses reduce once declared; soundness, availability, design do not |

## What this does not establish

That the advisor's declaration is in the log (it is public data the frame carries; the
event kind is item 97); that the ecosystem's view is selection-blind in any given world
(the market fixture is the counterexample and the condition is a world fact); the
Logical-Induction transfer of the activation defect indicators; anything about the
inquiry and supplier channels beyond naming which of their independence clauses have the
shape of `Realizes`.  `payload_take` is a theorem about the Lean ecosystem's `payload`; the
Python simulator's activation adds the strict prohibited-event clause and the barrier, which
read the same prefix but are not re-proved here.

## Deviations from the second dispatch

- §2A asks for the supplier docket and inquiry outcomes inside `κ_R`; in the ecosystem
  they enter the view as `S` and `T` events and are not a separate channel of this log, so
  `κ_R` takes them as inputs rather than reproducing them.
- §2B's "isolated / factored evaluator" is not realizable in a single-log model and is
  reported as EXT rather than formalized.
- §6's `D·(τ_C^raw + τ_C^corr)` term is world-wise **LEAN** but not in the inductor form;
  `li_noncapture_chain3` carries the landed Boolean sealing hypothesis on each link.
