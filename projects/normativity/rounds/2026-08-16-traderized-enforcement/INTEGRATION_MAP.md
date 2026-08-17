# Integration map

Which existing objects this round touches, which it leaves alone, and what the
status of each proposed arrow is. Nothing below is an edit to an existing
interface; the arrows are proposals with their evidence class attached.

## 1. Objects touched

| object | where it lives | how touched |
|---|---|---|
| `DeductiveProcess`, `Trader`, `Exploits`, `MarketMaker`, `TradingFirm`, `Budgeter` | pinned `Formalized-Agent-Foundations` | read only; audited in `SOURCE_AUDIT.md`, not modified |
| settlement interface, enforcement column (`P1`, `P2`) | `consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` | related to, by a distinction argued in `DEDUCTION_SPECIAL_CASE.md` §5. The frozen tree is not edited |
| open sub-problem `D3` | same, §7 | a candidate route is named, not taken |
| `Workspace.Normativity.Contrib` | `lean/` | one new file, additive |

## 2. Objects untouched

`Due`, `Licensed`, `Loss`, `A`, the surgical repair compiler,
`CertifiedSurgicalRepair`, the Blum–Mansour engine, `δ_g`, `coverage(Due)`,
compiler loss-blindness — every object of `normativity.learning.current`. The
current normative-response-learning theorem is not reopened, rewritten, or
reinterpreted, and no arrow below feeds into it.

The relational-answerability substrate, the legitimacy conditions and the
procedural-sufficiency result. The deference line's authorization, corrective
control and futurity objects. `PRIORITIES.md` item 7's Lean chain.

## 3. Vocabulary, kept apart

Four collisions were live and all four are avoided by construction. **These are
not identifications and the round does not propose any.**

| existing object | this round's object | why they are not the same |
|---|---|---|
| `coverage(Due)` — a quantitative property of `Due` along the actual trajectory, consumed by the response-learning theorem | **world-inclusive region** — a per-date containment of `PC(D_n)` in `K_n` | different types: one is a rate over occasions in a response space, the other is a set containment in a price space. No map between them is exhibited |
| **liabilities** in the answerability theory | **enforcement liability** — a bound on one trader's cumulative plausible loss | different bearers and different ledgers |
| **authority**, **authorization** in Deference | **privileged trader**, **enforcement trader** | the deference senses concern who may act; here the privilege is unit weight, no budget cap, and exemption from efficient computability |
| **downside limit** `-B` in the settlement interface `P2`, a worldwise guarantee against the book's holdings | **enforcement liability** `B` | different holdings, different quantifier, different respondent. The shape coincides and nothing else does |

## 4. Relation to the normative-response-learning interface

The dispatch offers four possibilities. The verdict is **A, orthogonal**, with
`B` open and `C` and `D` refused.

**A — orthogonal mechanisms: adopted.** `Due/Licensed/Loss` govern learning among
responses in a finite response space `A`. Traderized enforcement governs which
price vectors in `[0,1]^{Φ_n}` are displayable. There is no shared object, no
shared quantifier, and no shared trajectory index. The two mechanisms could both
run on one agent without interacting.

**B — traderization implements Normativity's statics: open, and blocked on a
missing object.** For a normative record to generate `K_t` there must be a map

    normative record  ⟶  admissible region in price space ,

and no such object exists in the workspace. `Due` is a burden on an occasion;
`Licensed` is a permission on a response; neither is a constraint on a credal
state. Constructing that map is a research item, filed. Until it exists, B is a
hypothesis with no arrow in it.

**C — traderization instantiates a current open interface: refused.** The
tempting reading is that world-inclusivity instantiates the coverage requirement.
It does not, per §3: there is no map of objects and no matching quantifier
structure, and asserting one would be exactly the vocabulary collision the
dispatch warns about.

**D — the current interface is at the wrong level: refused.** No incompatibility
was found. The round produces nothing the response-learning theorem cannot
accommodate, and aesthetics are not grounds.

## 5. Proposed arrows, with theorem status

| arrow | direction | status |
|---|---|---|
| row presentation of `K_n` ⟶ day-`n` trading strategy | compiler | **constructed**; expressibility argued, legality argued, `test-supported` |
| market-maker contract at slack `0` + `K_n ≠ ∅` ⟶ `P_n ∈ K_n` | enforcement | **`lean-proved`, unregistered** (`le_pair_of_contract_zero`) |
| contract at slack `ε_n` + volume `M_n` ⟶ `∑_j β_j g_j² ≤ ε_n + M_n` | enforcement | **`lean-proved`, unregistered** (`weighted_square_le_slack_add_volume`) |
| world-inclusive `K_n` ⟶ enforcement liability `0` | safety | **`lean-proved`, unregistered** (`pair_nonneg_of_mem`) |
| bounded enforcement liability ⟶ the modified market satisfies the criterion | safety | **derived**, from two source lemmas taken as hypotheses; not in Lean, not registered |
| unbounded enforcement liability ⟶ an exploiting trader | necessity | **witness only**, one fixture, `test-supported` |
| deductive stage ⟶ world-inclusive presentation | constraint source | **constructed** (`support_rows`), `test-supported` |
| traderized coherence ⟶ `THEORY_11` `D3(a)` | upstream | **candidate route**; the incoherence bridge of `FORCE_INTERFACE.md` §1 closes the measure gap, the presentation cost remains |
| endorsement + `theta_min` ⟶ row ⟶ trader (`P1`) | force | **constructed**, `test-supported`; agrees with `NL-SI-A5`'s closed form and with the core condition pointwise |
| `NL-SI-A3` feasibility program ⟶ compiler precondition | upstream | **identified**, not implemented here: the adapter already exists and is what the compiler needs |
| exclusion depth `d_t` ⟶ cumulative liability ⟶ criterion | safety | **`lean-proved`** for the per-date bound (`weighted_square_sub_deficit_le_pair`); the ceiling and the summability condition are `test-supported` |
| normative record ⟶ `K_t` | constraint source | **absent**; filed as a research item |

## 6. Where the round would sit

Under Normativity, as the **force layer** beneath the statics rather than beside
the learning theorem. This is stronger than the first pass's placement, and the
reason is `FORCE_INTERFACE.md` §2: the alternative implementation of the same
contract — a market maker constrained to display a price inside the region — is
not known to be a total function, and there is a date where it demonstrably is
not. An implementation that inherits Brouwer dominates one with no existence
theorem, so traderization is the **preferred** implementation of the enforcement
column rather than a second engine to audit alongside it.

What it is not is a replacement for the settlement interface. That distinction is
the whole of this round's second pass: the constrained *market maker* is what is
retired; reports, timing, persistence, grounding, feasibility, breach and
answerability are untouched and stay upstream. `FORCE_INTERFACE.md` §3 assigns
each of them.

```text
constraint source  →  K_t  →  constraint-to-trade compiler  →  enforcement trader  →  P_t ∈ K_t
```

The diagram survives the constructions with one amendment the research forced: the
arrow from a constraint source to `K_t` is not free. It must deliver a **row
presentation**, and if the source is deduction the honest presentation is the
facet system of the coherence polytope, whose cost is stated in
`DEDUCTION_SPECIAL_CASE.md` §4. A source that delivers a set without a
presentation delivers nothing the compiler can consume.

The second amendment: the diagram is safe exactly when the source's rows do not
exclude a still-plausible world. That is a condition on the *source*, expressible
in the diagram's own vocabulary, and it is what makes deduction the well-behaved
special case rather than one instance among equals.

## 7. Legitimacy and Deference

Traderized enforcement is **not** offered as a fifth procedural conjunct. The
procedural-sufficiency prosecution refutes four-condition sufficiency against an
independently stated target, and adding a mechanism that makes a constraint
effective does not address a target about which constraints are the right ones.

**The separation, stated as an architectural finding.** Legitimacy of a
constraint source and operative force of that constraint are independent. Force
is cheap: any nonempty region with a computable rational row presentation gets it
at any positive intensity, and the mechanism will hold a singleton region exactly
as readily as a defensible one. So a constraint being operative is no evidence
that it is legitimate, and this round supplies no legitimacy result.

**Does the mechanism make manipulation easier?** Yes, and the answer is sharp
rather than hedged. Whoever writes the rows sets the displayed price: at slack
zero a singleton region determines `P_n` exactly (`PROSECUTION.md` W11). Control
of the constraint source is therefore complete control of the credal state, and
traderized enforcement is a *steering channel* before it is anything else.

**What the market itself checks about a source.** Exactly one thing: deductive
consistency. A source that persistently excludes a still-plausible world makes
the market exploitable, with an explicit exploiting trader
(`FUNDING_AND_SAFETY.md` §4). That is a real constraint on sources and it is not
legitimacy — it rules out sources that contradict what deduction has settled, and
says nothing about sources that are merely wrong, partial, or captured.

**Deference.** A future-human or trusted-process constraint can be made operative
this way whenever it is presentable as a computable rational row system at date
`n`. It supplies none of authorization, principal-exclusive corrective control,
or advisor-robust futurity, and the workspace's own result says why it cannot:
the enforcement trader reads only prices and its effect is only on prices, so its
whole action factors through the static view, and
`StaticViewFactorization.value_eq_of_price_realization_eq` proves such a
functional cannot distinguish two instances differing only in jurisdiction
(`projects/deference/notes/LI_NATIVE_DEFERENCE.md` §8). Authorization must enter
before that factorization boundary. Traderized enforcement is therefore
**downstream** of the deference problem, not a solution to it, and no
corrigibility claim is made.
