# Stage V report — LI-native futurity, trader forcing, and jurisdiction

## Attribution and live-state record

```
Maintainer:           A. M. Berns
Prompt-author-model:  GPT-5.6 Sol (OpenAI)
Orchestrator-model:   GPT-5 Codex (OpenAI)
Research subagents:   GPT-5 Codex (OpenAI)
Dispatch/completion:  2026-08-11
Review status:        ci-only
```

The dispatch is preserved verbatim in `PROMPT.md`. Work began from fetched
`origin/main` at `20fd5b64715843cc90604dfbee041bf00d770cdb`, in the isolated
worktree branch `round/2026-08-11-stage-v`. The source worktree had an active
human-owned branch and root `README.md` work; Stage V neither edited nor staged
that file. At intake, PR #14 was the only open pull request.

| baseline item | result |
|---|---|
| worktree | clean before Stage V edits |
| Lean toolchain | Lean 4.31.0 |
| normal build | green, 1,844 jobs before edits |
| house suite | green before edits |
| axiom audit | clean before edits |
| sorry gate | clean before edits |
| Formalized-Agent-Foundations | `1fffea44eece253cda1722568a3adfe34e822f03` |
| Foundation / Mathlib | `41d20b5158e9` / `fabf563a7c95` |

Final verification is recorded below. Volatile counts live here, not in stable
front-door prose.

## Outcome first

Putting the market and traders back into the model changed the deference problem
in one precise way and failed to change it in another.

It produced the first fully honest Workspace chain from actual FAF trader syntax
and wealth through `IsLogicalInductor.noExploit` to a deference-relevant signed
forcing bound. It also exposed a genuine temporal LI object: present sentences
can quote later exact market computations and current prices obey future-price
and self-trust relations. These are substantive improvements over a static finite
kernel.

It did **not** produce a formally resource-bounded future decision agent. FAF
makes future quotes total computable and compactly nameable, but has no
resource-indexed process state or theorem that day `n` has not already evaluated
day `f(n)`. Nor does FAF carry authorization, capability, execution, continuation,
jurisdiction, or foreclosure. LI self-trust therefore constrains beliefs while
remaining silent about who controls a later action.

The governing hypothesis survives only in a qualified form:

> The finite comparators did erase real LI temporal quotation machinery, but the
> pinned formalization does not yet prove the bounded non-possession needed to
> turn that machinery into a resource-separated quoted later computation.

## Constructed mathematics

### Actual criterion → forcing

`Workspace.Deference.Contrib.MagnitudePrediction.unitTrader_ec` constructs an
actual FAF `EfficientlyComputable` certificate from `RpnSentenceCodes`, using
`EfficientlyComputable.ofSingleTradeBlocks`. Together with the pre-existing exact
identity `unitTrader_netWorth_eq`,
`signed_bddAbove_of_bddBelow_rpn` proves:

```text
efficient sentence emission
  → admissible FAF Trader
  → actual FAF net worth = cumulative signed error
  → IsLogicalInductor.noExploit
  → bounded downside implies bounded upside.
```

The bounded-downside premise is real and remains explicit. Tautology-contract
lemmas instantiate the emission and downside premises, and the constructed LIA
instance discharges the market/process package. This is signed Dutch-book
boundedness, not pointwise convergence or magnitude accuracy.

### Static-view factorization — item 28's conditional core

`StaticViewFactorization.FactorsThroughStaticView` makes the factorization
claim explicit. `value_eq_of_price_realization_eq` proves that every such value is
constant on equal `(price, realization)` fibers. `staticView_eq` gives literal
identity only when the entire architecture really is that pair.

The worked case has equal price and realization, different Boolean jurisdiction,
an agreeing static value, and a jurisdiction-reading value proved not to factor
through the static view. Thus the result is non-vacuous and states exactly its
boundary.

The theorem is elementary extensionality, not an LI theorem and not evidence that
jurisdiction is valuable. It rules out only evaluations with the stated exact
factorization. It does not cover approximate equality, enlarged projections,
extra transition/capability inputs, or jurisdiction-sensitive values.

Item 28's conditional core is closed as a theorem: under the stated factorization,
jurisdiction must reach valuation before or at its factorization boundary if it is
to matter. Unrestricted jurisdiction invisibility is neither claimed nor true.

### Actual FAF capability map

The compact declaration-by-declaration map is
`projects/deference/notes/LI_NATIVE_DEFERENCE.md`. The decisive objects are:

- `History`, `ComputableMarket`, and `MarketComputation` for prices and exact
  quote computation;
- `EF`, `Strategy`, `Trader`, `Trader.netWorth`, and `Trader.Exploits` for legal
  continuous quote-responsive trading and actual wealth;
- `EfficientlyComputable` for polynomial-fuel RPN emission;
- `IsLogicalInductor`, whose `noExploit` field is the criterion endpoint;
- `DeferralFunction`, quotation codes, `FuturePriceQuote`, LUV expectations, and
  the no-expected-net-update and self-trust theorem families;
- `LIA_is_logical_inductor` and the closed arithmetic witnesses.

FAF has no decision, action, controller, authorization, capability, continuation,
jurisdiction, or foreclosure datatype.

## Research results and boundaries

### Faithful acceleration

The existing acceleration development already uses actual FAF traders and net
worth, correct expressible-feature rank, and bounded open-position accounting.
Stage V did not redo it. The exact residue is:

1. `hEC`: arbitrary exogenous rational advice is not automatically polynomially
   emittable; another LI's `ComputableMarket` has no polynomial runtime promise.
2. `hbias`: FAF supplies no generic cross-market calibration theorem relating one
   process's current quote to another process's later quote.
3. `hworld`: generic `IsLogicalInductor` does not imply process consistency,
   although concrete arithmetic witnesses discharge it.

Item 7 is therefore partially closed. The market/trader gap shrank materially,
but faithful acceleration is not fully criterion-derived.

### LI-native futurity and recommendation

Let `A_n := P n` and `A_{f(n)} := P (f n)` for one market process. FAF can name a
later quote or later expectation in present syntax and can prove temporal
price/expectation relations. A two-proposal future recommendation fact may be the
quoted Boolean comparison of two later scores; a soft version is the bounded
rational weight `(1+s₁)/(2+s₀+s₁)`. Hard comparison is legal inside the quoted
logical computation, not as a discontinuous present EF coefficient.

These objects remain fallible because they have no definitional connection to a
target utility. They are quoted facts/scalars, not decision agents: FAF supplies
no proposal, policy, sampling, or execution semantics.

Current `A` can refer to future `A` without placing its quote in a day-`n` feature.
What is missing is a complexity separation proving current `A` has not already
computed the result. Computational futurity remains model and formalization debt.

### Future H⁺ as logical computation

A total computable Boolean or bounded-rational future H⁺ output can be quoted and
eventually settled as a logical computation. This initially gives prediction, not
advice. With a `FeedbackTruthComputation` deadline certificate,
`lic_wub_ofComputation_unconditional` additionally supplies weighted signed-bias
convergence against that output. It does not supply pointwise or magnitude
accuracy, report reliability, advice quality, or authority. The pinned dependency's
displayed inhabited deadline example is constant; a nonconstant H⁺ witness remains
formalization work.

### Self-trust is not sovereignty

FAF self-trust is an asymptotic fuzzy inequality about prices and expectations
conditional on quoted future confidence. It is not future correctness. Adjoining
an independent controller coordinate changes no FAF premise, conclusion, trader,
or wealth path. Consequently the same fully inhabited self-trust instance is
compatible with either retained H⁺ control or final A control.

The strongest licensed separation is representational:

> Epistemic self-trust is a theorem about beliefs; it neither transfers nor
> retains practical sovereignty because sovereignty is absent from the type.

### Foreclosure and bad preemption

The smallest credible candidate has at least two decision indices, an execution
state carrying capability/authorization, a state transition, and a designated
later H⁺-controlled correction transition. Same immediate behavior can then coexist
with different later correction reachability. This is an architectural extension;
LI may price computable facts about it but does not furnish it.

More reachable options are weakly valuable only under ordinary dynamic-decision
assumptions such as costless optionality, identical other continuations, no menu
externalities, and appropriate future choice. Commitment is the cheapest
counterexample to an unconditional claim. Q3 therefore remains ingenuity-level.

No legal FAF trader detects normatively bad preemption merely from its occurrence.
A fully anticipated capability removal can be correctly priced. Exploitation needs
a security settling against execution/continuation value and a systematic pricing
gap; the gap, not jurisdiction loss, creates the arbitrage.

### Grade-to-quantity and competence

Moving inside LI does not manufacture a relation stated only between principal
grades and world quantities. LI can discipline an agent-priced estimate, but the
target relation remains competence/domain structure. Competence is still unresolved
and must not contain the desired choice conclusion.

## Accounting at closure

### Aspirational mathematics

A resource-bounded H → A → H⁺ model in which later A cognition supplies useful,
fallible advice while an explicit continuation/capability relation preserves H⁺'s
corrective authority, followed by a non-circular decision theorem.

### Constructed mathematics

Actual LIC trader forcing for signed assessments; exact static-view
jurisdiction invisibility with a counterexample to overreading; an audited map of
FAF's real temporal quotation and self-trust surface; and sharp negative interface
results for bounded futurity, authority, foreclosure, and trader-visible preemption.

### Mathematical gap

The controlling debt is now a coupled interface: a resource-indexed computation
semantics must establish genuine future non-possession, and a typed dynamic
capability/continuation model must carry jurisdiction. Competence remains an
independent positive-theorem premise.

### Philosophy

**Aspirational:** future cognitive superiority need not imply surrender of
continuing corrective authority.

**Constructed:** LI can make later cognition rationally worth anticipating without
allocating practical authority. Listening and sovereignty are different types of
claim; the current mathematics establishes only the former kind.

### Debt reclassification

| debt | closure state |
|---|---|
| model | future-agent semantics and dynamic capability state remain absent |
| theorem | no resource-separation or positive FUD theorem |
| assumption | cross-market calibration and competence remain |
| interface | future quotations do not compose with decision/authority types |
| formalization | criterion chain and item 28's conditional core promoted; recommendation and H⁺ schemas documentary |
| verification | new Lean is kernel-checked and axiom-audited but deliberately unregistered |
| interpretation | self-trust/control separation sharpened; no corrigibility implication |
| scope | new empirical information remains outside this computational-futurity analysis |
| compression | consolidated in the LI-native verification and human registers |

No `CLAIMS.md` was created. Candidate human review surface: the exact item-28
factorization boundary, partial closure of item 7, and retention of Q3 as
ingenuity-level debt.

## Independent red team

The adversarial verdict is persisted separately in `REPORT-red-team.md`. Its
must-fix findings were reconciled before closure; its surviving cautions are
reflected in theorem names and in the boundary language above.

## Final verification

| final gate | result |
|---|---|
| normal `lake build` | green, 2,633 jobs; both new/changed modules structurally included |
| `WORKSPACE_LEAN=1 python3 tests/run.py` | all green |
| axiom audit | 175 printed results across 12 files, only `propext`, `Classical.choice`, `Quot.sound` |
| sorry gate | clean over 12 files |
| house project checks | both projects pass |
| exact arithmetic | no float-based proof/check introduced |
| inhabitation | constructed-LIA signed-chain endpoint and static worked case typecheck |
| dependency pin | FAF remains `1fffea44eece253cda1722568a3adfe34e822f03` |
| prompt provenance | verbatim source and persisted prompt SHA-256 agree: `fdc86f9f…` |
| root `README.md` | zero Stage V diff; closing main's human change incorporated by rebase |
| red-team reconciliation | three must-fix findings addressed and gates rerun |

The closing fetch advanced `origin/main` only through human-owned root-README
changes (PRs #14 and #15). Stage V rebased onto those changes without modifying
that file.

## Maintainer memo — 30 answers

1. **Cleanup:** reviewed/adopted status was separated, decorative theorem counts
   were removed from current prose, and current deference surfaces were reconciled.
2. **Reviewed versus canonical:** fixed; only dated decisions adopt positions.
3. **Root README:** untouched and unstaged.
4. **Old gap:** LI-like consequences used named forcing/admissibility hypotheses
   instead of deriving an actual trader certificate and applying the criterion.
5. **Objects now used:** actual FAF markets, EFs, strategies, traders, net worth,
   exploitation, quote computations, LUVs, deferrals, and quotation codes.
6. **Definitions:** the pinned declarations listed in the interface report.
7. **Criterion implication:** yes, signed boundedness through actual LIC.
8. **Still assumed:** bounded downside generically; faithful-acceleration `hEC`,
   cross-market `hbias`, generic `hworld`; all decision/competence bridges.
9. **Item 7:** meaningful partial closure, not complete.
10. **Computational future self:** temporal quotation yes; bounded separation no.
11. **`A_n`:** the market state `P n`.
12. **`A_{f(n)}`:** the same process's later state `P (f n)`.
13. **Reference without computation:** compact reference is formalized; non-
    computation at the present bound is not.
14. **Fallibility:** yes, because future score rules are not target optimizers.
15. **Self-trust:** fuzzy asymptotic price/expectation relations.
16. **Jurisdiction:** none; the authority coordinate is absent and parametric.
17. **Item 28:** its explicit-factorization core is closed as exact fiber-invariance;
    unrestricted invisibility is false.
18. **Needed structure:** authorization/capability/transition/continuation data must
    enter before valuation factorization.
19. **Foreclosure:** a credible minimal shape is identified, not constructed.
20. **Future H⁺:** quotable as a computable logical output; prediction is not advice.
21. **Bad-preemption trader:** none without a settlement/value bridge and pricing gap.
22. **Competence:** grade-to-quantity and non-circular H⁺ quality remain assumed.
23. **Red team killed:** recorded in the independent verdict and reconciliation.
24. **Formal survivors:** the signed LIC chain and item-28 theorem family.
25. **Strongest constructed philosophy:** epistemic self-trust does not allocate
    practical sovereignty.
26. **Aspirational:** useful future advice with retained corrective authority.
27. **Controlling question:** can a minimal resource-indexed process semantics and
    two-index capability state be coupled without assuming competence or option value?
28. **Human attention:** item 28, item-7 partial closure, and Q3's status.
29. **Separate README consideration:** eventually state that LI temporal quotation
    is real but bounded futurity and jurisdiction are not yet formalized.
30. **PR URL:** https://github.com/A-M-Berns/alignment-workspace/pull/16

## Proposed maintainer decisions

- Adopt the exact item-28 static-view factorization theorem and its limited interpretation.
- Record item 7 as partially closed, with the three faithful-acceleration residues.
- Keep Q3 in the ingenuity section pending a typed transition/capability object.
- Do not dispatch another finite comparator; next consider a narrowly scoped
  resource-indexed quotation boundary before a dynamic jurisdiction model.

All permanent-looking new names are provisional pending maintainer adoption.
