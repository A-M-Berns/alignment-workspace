# WITNESS AUDIT — budgeted LI against the Settlement Interface

*Audit of `SETTLEMENT_INTERFACE.md` draft 2.1 (§10 witness row 1) against
Garrabrant et al., "Logical Induction" (arXiv:1609.03543v5). Register:
internal. Citations are to that paper by definition/theorem label and to the
frozen corpus by claim ID.*

*Housed beside the interface rather than in `normative-learner/`: §8's central
term ("kernel") is on the corpus's retired-vocabulary list, so this document
would fail that tree's naming gate. No repository file was modified by this
audit.*

---

## 0. The central mapping decision

**"Budgeted LI" is not one object at the interface boundary. It is a pair, and
the pair straddles the boundary.**

The interface asks for an engine supplying a pen, a clock, and a purse (§0).
LI's construction has two separable parts:

| LI object | paper | interface role |
|---|---|---|
| deductive process **D** | `def:dedproc` — a *computable nested sequence* `D₁ ⊆ D₂ ⊆ …` of finite sentence sets | **the pen and the clock** |
| market **P** = (P₁, P₂, …) | `def:marketprocess` — a computable sequence of pricings `S → ℚ ∩ [0,1]` | **the purse, the tolerance, the certificate type** |

This matters because the alternatives are worse. One could try to make the
market the pen (pins = prices hitting 1), but prices reaching 1 is not an event
LI guarantees at any finite time — only `P_∞` is coherent (`thm:lc`) — so the
write-once clause J2 would have no well-defined trigger. One could try to make
D the whole engine, but then P1–P4 and T1 have no referent at all: D has no
prices, no budget, and no tolerance. The split above is the only assignment
under which every clause has a candidate inhabitant.

Three consequences run through the whole ledger:

1. **The [E] pen/clock clauses (J1, J2, C1, §8-logical, §9) are clauses on D,
   not on the market.** Several are then near-trivial, because `def:dedproc` is
   deliberately barren — and one (§8-logical) fails for exactly that reason.
2. **The [M] purse clauses are clauses on the market**, and P2 is the audit's
   cleanest hit because LI's `Budgeter` *is* a downside floor.
3. **B3 as currently worded — "budgeted, finite-trader LI satisfies the J/C/P/T
   clauses" — attributes to one object what two objects jointly supply.** The
   revised statement in §4 says so.

A note on the paper's own hedge, which frames the sharpest finding below: the
authors write that "there is ample room to disagree about how well our
algorithm achieves certain desiderata, e.g. when the desiderata is met only in
the asymptote, or with error terms that vanish only slowly" (§1, following the
desiderata list). T1 is where that bites.

---

## 1. The clause ledger

### J1 — Declared settleable class · [E] · **INHABITS**

**Mapping.** The engine declares D (a specific computable enumeration relative
to a theory T) together with the question set it claims. A *procedure* is the
pair `(D, φ)` — "decide φ using D". The outcome space is `O = {proved,
refuted}`. The report variable is `X_{(D,φ)}`; its date is the stage at which D
first resolves φ, so the date is *determined*, not chosen — unlike the empirical
channel, where a procedure is executed at a date of the funder's choosing.

*Alternative considered and rejected:* indexing report variables as `X_{D,n}`
("what D emitted at stage n", outcome space = finite sentence sets). This is
faithful to `def:dedproc` but makes pins carry sets rather than values, which
breaks §1's "fixes the variable's whole propositional family at once" and makes
J2 write-once trivially true but contentless. The `(D, φ)` mapping is the one
that gives J2 real work to do.

**Argument.** D is computable by `def:dedproc`, so the class is effectively
declarable. The only substantive constraint is that the declared logical
jurisdiction must lie inside the D-decidable fragment — see C1, where this is
discharged. No modification to LI. Cost: a declaration.

---

### J2 — Write-once, owner-only · [E] · **INHABITS** (with a lawful breach path)

**Mapping.** As J1. "Owner" = the engine owning D; the LIC is defined relative
to a single fixed D ("a logical inductor over **D**", §3), so one market has one
deductive process, and multiple procedures bearing on one world claim are
multiple engines — exactly J2's thermometer-A/thermometer-B provision.

**Argument.** D is *nested* (`def:dedproc`), so once φ enters `D_n` it is in
every later `D_m`: nothing is retracted, and the first entry is the unique pin.
Write-once holds.

**The interesting case.** If T is inconsistent, both φ and ¬φ eventually enter
`D_∞`, producing two pins on `X_{(D,φ)}` with conflicting values. `def:dedproc`
imposes *no* consistency requirement, and the paper is explicit that worlds
"are not necessarily consistent" (`def:world`), so this is not excluded by the
framework. It is, however, exactly what §7 classifies as a jurisdiction
violation ("a second pin on a variable") — detectable, and routed to
toll → quarantine → escalate. So an inconsistent T does not falsify J2; it
triggers the interface's own breach stack, and permanent inconsistency becomes
"lawful revolution rather than silent rot" (§7.3).

This is a genuine point in the interface's favour: the one case where LI's pen
can violate write-once is precisely the case the breach clause was built for.
It should not be read as an LI guarantee, because consistency of T is not
provable in T.

---

### J3 — Migration transport: bridge, never re-settle · [M] · **INHABITS**

**Mapping.** Adapter-side entirely. Pins are historical record; translated
content reaches the new ontology through migration cells.

**Argument.** The corpus already carries this: `CM-J0` (administrative
continuity — the only permitted edit between migrations is a declared grant, so
a re-settlement between certified migrations is structurally impossible), and
`AM-J3` conclusion 6 (exact outstanding meaning on the common carrier, or an
explicit legacy disposition, never silent substitution). LI requires nothing:
D's output is append-only by `def:dedproc`, which is the same shape as the
answerability ledger's append-only log. No LI modification.

---

### C1 — Completeness, split by channel · [E] · **INHABITS**, mapping refined

**Mapping — and a correction to the draft's operationalization.** §3 defines
`D∞ = {φ : the declared deductive process eventually proves or refutes φ}`. LI
writes `D_∞ = ⋃ₙ Dₙ` for the union of what is *proven* (`def:dedproc`). These
are **not the same set**:

```
interface D∞  =  { φ : φ ∈ D_∞  or  ¬φ ∈ D_∞ }   ⊊   D_∞ ∪ ¬D_∞
```

The interface's D∞ is the **D-decidable fragment**. For T = PA this is a proper
subset of the language by Gödel, and the gap is not small. So π3's "the mapping
is the identity" is **not** correct as stated; the mapping is the identity only
after restricting to the decidable fragment.

**Argument.** With that reading, C1's logical conjunct — "D∞ contains the
declared logical jurisdiction" — is satisfiable, but only by a J1 *declaration
discipline*: the engine must declare a jurisdiction inside the decidable
fragment. The interface anticipates this in its own parenthetical
("Completeness is relative to the declared process; nothing here claims
settlement of mathematical truth as such"), so this is a clarification, not a
defect.

**Ratelessness is an exact match.** `def:dedproc` supplies no rate and the
paper's theorems are asymptotic; C1's "with no rate promised … downstream
machinery must not assume one" is precisely what LI can honour. This is the
clause LI fits best on the pen side.

*Empirical conjunct:* not applicable to D as such. LI's empirical channel is an
observation stream entering D (per §10's table), so funding-responsive
completeness is a property of the observation apparatus, not of LI. Audited
under §9's third requirement, where it fails.

---

### C2 — Ripeness and tolling · [M] · **INHABITS**

**Mapping.** Adapter-side; the mechanism's existing clock machinery.

**Argument.** C2 requires that dependence on the rateless logical channel tolls
refusal clocks. The corpus supplies the clock: `CD-J8` derives refusal liability
as `(horizon − filed) × tariff` from an explicit clock, so tolling is
subtraction on a quantity that already exists, and `CS-J1` bounds dates in
arrears by accumulated liability over the tariff. A tolled query accrues
nothing, which is exactly `CD-J8`'s snapshot case (`horizon == filed`, zero
charge). "Permanently unripe" maps to a query never admitted, which `CS-N2`
shows is precisely what admission control exists to bound.

No LI modification. This is the clause where LI's ratelessness is *absorbed*
rather than resisted.

---

### C3 — Adequacy · [M] · **INHABITS** on the logical channel, **vacuously**

**Mapping.** Adapter-side inequality relating downstream deadlines to upstream
horizons.

**Argument.** On the logical channel there *are* no horizons (C1 promises none),
so the adequacy inequality has no upstream term and is vacuously satisfied. The
work is carried entirely by C2's tolling. This is coherent design rather than a
gap — but it means C3 constrains only the empirical channel, and the interface
should not be read as getting adequacy for logical settlement.

**Citation-integrity flag.** C3 cites "the A0 witness and its CA/MSR-A repair".
Grepping both trees, no identifiers `A0`, `CA-*`, or `MSR-A` occur in
`normative-learner/LEDGER.md` or in the consolidation's markdown. The latency
material exists upstream under other names (starvation-by-latency; the
quadratic latency law in `consolidation_aug8/DEVIATIONS.md` §6). **Unresolved
citation** — either the IDs are from a tree not present here, or they need
remapping before the interface goes external.

---

### P1 — Enforcement floor (θ) · [M] · **INHABITS as a declaration**, with a residual

**Mapping.** θ is a coefficient of the *mechanism's compiler over the engine's
prices*, not an intrinsic property of the market. LI has no native θ — as §4's
own preamble concedes ("a conformal predictor possesses no 'conviction
coefficient', nor need it"). The adapter declares θ_min.

**Argument.** Declaring θ_min is free. Whether the declaration remains
*satisfiable* is not, and nothing in LI guarantees it: as deduction proceeds
`Dₙ` grows, the feasible region contracts (§9's own partial-closure
requirement), and a contracting region can drive the core coefficient toward 0
— which is exactly the condition P1 says voids the operative-force cap. The
paper offers no lower bound on core width; `thm:lc` gives convergence of prices
but says nothing about the geometry of the induced region.

Verdict is INHABITS because the clause as written asks for a certified
declaration and LI can make one. The residual — *is a declared θ_min stably
satisfiable under LI?* — is logged as **Δ₁**.

---

### P2 — Downside establishment · [M] · **INHABITS** — the cleanest hit

**Mapping.** The market may not refuse trades, so P2's second named means
applies: bounded aggregate trader budgets.

**Argument.** This is not an analogy; LI implements it literally.
`defprop:Budgeter` defines a computable `Budgeter^D` which, given a budget
`b`, zeroes a trader's strategy as soon as its value reaches `−b` in *any*
propositionally-consistent world consistent with `D_m`:

> if `W(Σ_{i≤m} T_i(P_{≤i})) ≤ −b` for some `m < n` and `W ∈ pcworlds(D_m)`,
> then `Budgeter^D_n(…) = 0`.

That quantifier — "for some world consistent with `D_m`" — is a **worldwise**
floor, which is precisely P2's requirement, not merely an expected-value
constraint. `TradingFirm` then combines the infinite sequence of e.c. traders
*through* `Budgeter` with a summable budget schedule, so the aggregate exposure
is bounded, and `thm:lia` certifies the resulting market satisfies the LIC.

The interface's phrase "bounded aggregate trader budgets where it may not
[refuse]" reads as though written with this construction in view. It is
inhabited exactly.

---

### P3 — Finite gating · [M] · **INHABITS**

**Mapping.** Adapter-side gating over engine-facing instruments; the corpus's
FIFO world slots.

**Argument.** Two independent finiteness sources agree. On the LI side,
`def:belstate` requires belief states to have **finite support** — "0 for all
but finitely many φ" — so LIA prices only finitely many sentences per day; the
instrument space facing the mechanism is finite at every date without any
adapter work. On the mechanism side, `CS-J3` gives the fairness property
(finite-overtaking admission defers nothing forever) and `CS-N2` shows admission
is what keeps live state finite under an adversarial arrival stream.

No LI modification. P3's "universality-to-finiteness adapter" has less to do
here than the clause anticipates, because LIA is already finite per date.

---

### P4 — Declared certificate type · [E] · **INHABITS**

**Mapping.** Declared type = *market non-exploitation*. `Cert_LI(H, C)` = "no
efficiently computable trader exploits the market on H", with exploitation as
`def:exploitation`: the set of values `{W(Σ_{i≤n} T_i(P)) : n ∈ ℕ⁺, W ∈
pcworlds(Dₙ)}` is bounded below but not above.

**Argument.** The LIC is stated exactly as a declared-type guarantee (§3: "a
market M satisfies the LIC relative to D if there is no e.c. trader that
exploits M"), and `thm:lia` establishes LIA meets it. P4's formalization target
`Cert_e(H, C)` is therefore instantiable for LI without further work.

**But note the shape**, which bites at F2: the LIC is a property of the *entire
market sequence*, quantified over all n and all e.c. traders. It is not a
per-history, per-request certificate that can be issued and checked at a date.

---

### T1 — ε-schedule · [E] · **OPEN** — the sharpest finding

**Mapping.** ε_t is the finite-time incoherence tolerance of the market's
prices.

**The situation.** LI's coherence is a *limit* property. `thm:lc` states that
`P_∞` — the limit — is coherent and induces a probability measure on worlds
consistent with T. Nothing is claimed about `P_n`. The paper is unusually
direct about the consequence, in the discussion of Desideratum 4 (Approximate
Coherence):

> Limit coherence does not guarantee this: a reasoner could assign bad
> probabilities (say, 100% to both claims) right up until they can evaluate
> `prg(7)`, at which point they start assigning the correct probabilities.

LI does better than that — it satisfies approximate coherence in the
timely-learning sense of §4 — but every such theorem is asymptotic, of the form
"for every e.c. sequence, the defect → 0", with **no modulus**. The authors flag
this themselves ("met only in the asymptote, or with error terms that vanish
only slowly").

**Why the verdict is OPEN and not CLAUSE-TOO-STRONG.** T1 as written *is*
satisfiable by LI — vacuously. Prices lie in `ℚ ∩ [0,1]` (`def:pricing`), so any
coherence defect is bounded by a constant, and the engine may honestly declare
`ε_t ≡ 1`. It will never breach. But at `ε ≡ 1` the ε-robust interval is `[0,1]`
at every date, so no merits certificate ever clears a threshold (the computed
interval degenerates exactly as in `CD-L2`'s empty-book case), and the
ε-robust sure-loss objection never fires.

So the finding is not that LI fails T1. It is that **T1 lacks a non-vacuity
condition**, and soundness and usefulness come apart for LI:

- a *sound* declaration LI provably honours: available (`ε_t ≡ 1`), and useless;
- a *non-vacuous* declaration — tight enough for the robust merits certificate
  to ever certify — would be a computable modulus of approximate coherence for
  LIA, and no such modulus appears in the paper.

**The open problem, sharply.** *Does LIA admit a computable `ε_t → 0` such that
`P_n` is provably `ε_n`-coherent at every finite n?* I did not find one, and I
did not find an impossibility proof either. The adjacent negative result — the
Sawin–Demski incompatibility cited in §1 (computable + non-dogmatic + Gaifman +
weak coherence are jointly unsatisfiable) — is *not* this statement and should
not be cited as though it were.

**The candidate weakening** (π2's) is available and cheap in the interface's own
terms: an eventually-coherent, rateless tolerance whose breach semantics is
quarantine-on-detected-excess rather than schedule conformance. §7 already
carries quarantine as clause 2, so the weakening reuses existing machinery. What
it costs downstream: the ε-robust merits certificate loses its *a priori*
guarantee and becomes a *posteriori* — the docket certifies, and a later Farkas
check may quarantine the channel retroactively. Anything leaning on the merits
certificate being sound-at-issue-time (the `CD-J2` recomputation discipline, and
`CD-L1`'s "merits iff leverage" biconditional) would need restating against the
weaker guarantee. That is a real cost and it should be paid deliberately.

---

### T2 — Certification layering · [E/M] · **INHABITS** — and it partly rescues T1

**Mapping.** Engine certifies floors; the book may declare tighter working
tolerances and bears the breach.

**Argument.** T2 is satisfied trivially by LI (it certifies `ε_t ≡ 1` as its
floor). The interesting content is the interaction the audit surfaces:

**T2 supplies a lawful route around T1's vacuity.** LI declares the vacuous but
honest floor; the *book* voluntarily declares a tighter working ε and, per T2,
"breach of a self-declared tighter bound is the *book's*, and chargeable — it
assumed the risk." So the mechanism can operate on a useful tolerance without
the engine ever certifying one, at the cost of the book carrying an
epistemic bet as a priced liability.

This is squarely the corpus's idiom — an unpayable epistemic gap converted into
accounted liability rather than assumed away — and it means T1's OPEN status is
*less* damaging to the composite than it first appears. It does not close the
open problem; it prices it.

---

### F2 engine-side hook — Stopping neutrality · [P] · **INHABITS via one witness only**

**Mapping.** F2 names two witnesses: a precommitted stopping rule, or an
optional-stopping-safe (anytime-valid) certificate. Only the second needs an
engine hook.

**Argument.** LI issues no per-request certificate. As noted at P4, the LIC is a
global asymptotic property of the whole market sequence — quantified over all n
and all e.c. traders — not an object emitted per settlement request and
checkable at a date. There is no anytime-validity result in the paper, and the
natural candidate (a Ville-style supermartingale bound) is not what
`def:exploitation` provides: exploitation is *unbounded-above value*, not a
tail-probability bound, and the two do not interconvert.

So for LI-backed probes the **precommitted-rule witness carries the whole
load**, exactly as π4 predicts. That is a live constraint on the surrounding
institution, not a defect in LI: fixed-horizon deduction requests are perfectly
expressible. But it means F2's second witness is unavailable to this engine and
the interface's "two named witnesses" reads as one for row 1 of §10.

---

### §8 logical channel — proof-carrying pins + checker trust · [E, axioms] · **LI-MODIFICATION**

**Mapping.** §8 requires that "logical pins are **proof-carrying**: a pin on a
theorem-question ships a derivation certificate checkable by a fixed proof
checker."

**Argument — this is a real gap.** `def:dedproc` defines D as a computable
nested sequence of *finite sets of sentences*. It emits **sentences, not
derivations**. Nothing in the LI framework ships a certificate with a theorem,
and nothing needs to: the market never inspects proofs, only membership in
`Dₙ`. So LI's pen does not natively satisfy §8's logical residue.

**The modification, and its cost.** Instantiate D as a proof-enumerator emitting
pairs `(φ, π)` with π a derivation, and define `Dₙ` as the projection to first
coordinates. Cost: essentially nil in practice — every concrete deductive
process *is* a proof search, so the certificate is already computed and merely
discarded — and the LIC is undisturbed, because the market reads only the
projection and the extra output is invisible to `def:exploitation`. But it is a
strengthening of `def:dedproc` that the paper does not make, and it must be
stated rather than assumed. Logged as **Δ₂**.

The checker-trust half is inherited, not new: §8 correctly observes that the
corpus's meta-challenge machinery already bottoms out at a mechanical checker.

*Empirical faithfulness axiom:* not audited against LI, because LI writes no
empirical pins — it prices them. The axiom constrains the observation apparatus
feeding D. LI cannot violate it, and cannot help discharge it.

---

### §9 — the three adopted requirements · [E] · **partial**

*Per the audit's terms of reference, §9's marked hole is not touched. What
follows checks only whether budgeted LI meets the three requirements as
stated.*

**(i) Partial-closure soundness — MET, natively and exactly.** The requirement
is that nothing downstream assume a consequence the engine has not yet pinned,
and that the feasible region contract as deduction proceeds. LI's exploitation
definition quantifies over `pcworlds(Dₙ)` — the propositionally-consistent
worlds consistent with the deductive state *at stage n* — so the plausible-world
set *is* the partial closure, and it contracts monotonically because D is
nested. This is not an adapter obligation; it is how the LIC is defined.

**(ii) Fundable deduction — NOT MET as stated.** The requirement is that a
settlement request may target a theorem-question. Nothing in LI forbids
*expressing* such a request, but see (iii): there is no mechanism by which the
request changes what D does.

**(iii) Budgets buy progress — NOT MET.** `def:dedproc` makes D a **fixed
computable function of n**. It is not a parameter of funding, and there is no
family `{D^b}` indexed by budget. "Deduction funding accelerates the stream" has
no referent in the LI framework: the stream is what it is. Every theorem in the
paper — the LIC itself, `thm:lia`, `thm:lc` — is stated relative to one fixed D,
and the plausible-world sets in `def:exploitation` are indexed by that D's
states.

I record this as a check result and stop, per the terms of reference. Making D
funding-responsive is not a small edit — it makes the plausible-world set
endogenous to the funder — and whether the LIA construction survives it is
precisely the territory §9 reserves.

---

## 2. SI⁻ — the maximal inhabited sub-interface

Under the §0 mapping, budgeted LI (as the pair `⟨D, P⟩`) inhabits:

> **SI⁻ = { J1, J2, J3, C1, C2, C3, P1*, P2, P3, P4, T2, F2-via-precommitment,
> §9(i) }**

with:

- **P1\*** = P1 discharged as a declaration only; stable satisfiability is Δ₁.
- **C3** vacuous on the logical channel (no upstream horizons to be adequate to).
- **F2** by the precommitted-rule witness only; the anytime-valid witness is
  unavailable.
- **J2** guaranteed only while T is consistent; inconsistency routes to §7's
  breach stack rather than falsifying the clause.

Outside SI⁻: **T1** (OPEN), **§8-logical** (LI-MODIFICATION), **§9(ii)–(iii)**
(not met).

---

## 3. The delta list

Minimal additional conditions jointly sufficient for the full interface, each
classified as modification (to LI) or weakening (of a clause):

| Δ | statement | class | cost |
|---|---|---|---|
| **Δ₁** | A lower bound on the mechanism's core coefficient over LI's price sequence: a declared θ_min that remains satisfiable as `Dₙ` grows and the region contracts. | *open sub-problem* — neither a modification nor a weakening until someone determines which it is | Unknown. Nothing in the paper bounds the induced region's geometry. |
| **Δ₂** | Instantiate D as a proof-enumerator emitting `(φ, π)` pairs; define `Dₙ` as the first projection. | **modification** to `def:dedproc` | Near nil: concrete deductive processes already compute π. LIC undisturbed — the market reads only the projection. |
| **Δ₃** | Either (a) a computable `ε_t → 0` with `P_n` provably `ε_n`-coherent — currently unknown to exist; or (b) weaken T1 to eventually-coherent-rateless with quarantine-on-detected-excess breach semantics. | (a) **modification**, existence open · (b) **weakening** | (a) unknown. (b) the merits certificate becomes *a posteriori*; `CD-J2`'s recomputation discipline and `CD-L1`'s biconditional need restating against the weaker guarantee. |
| **Δ₄** | Funding-responsive deduction: a budget-indexed family `{D^b}` with the LIC restated relative to the realized process. | **modification**, substantial | Reserved — this is §9's marked hole and the audit does not cost it. |

**Order two, as forecast — but only if Δ₂ is priced at its true (negligible)
cost and Δ₄ is set aside as reserved.** The two that carry weight are Δ₁ and Δ₃.

---

## 4. Revised B3

> **B3 (revised).** Let `⟨D, P⟩` be budgeted, finite-trader LI, with D a
> declared deductive process and P a market satisfying the logical induction
> criterion relative to D (`thm:lia`). Then `⟨D, P⟩` inhabits **SI⁻** — the
> settlement interface less T1, the §8 logical-pin certificate requirement, and
> §9's funding requirements — under the pen/purse split of §0, with P1
> discharged as a declaration and F2 discharged by the precommitted-stopping
> witness.
>
> Conditions **Δ₁** (stable core floor), **Δ₂** (proof-carrying D), and **Δ₃**
> (tolerance: either a computable coherence modulus, or the rateless weakening)
> are jointly sufficient for the full interface **excluding §9**, whose
> requirements (ii)–(iii) additionally need **Δ₄**.

Note what changed from the original wording beyond the subset: B3 as written
ascribes the property to "budgeted LI" as a single engine. It should ascribe it
to the pair, because the J/C clauses and the P/T clauses are satisfied by
different objects, and a reader who conflates them will think LI's market
supplies the pen.

---

## 5. Prediction scores

**π1 — [M] clauses all discharge adapter-side, no LI modification. CONFIRMED,
with one qualification.** J3, C2, C3, P2, P3 discharge cleanly; P1 discharges as
a declaration but leaves Δ₁ behind, so "the mechanism's existing machinery does
the rest" is true of the declaration and not yet known to be true of its
satisfiability. No [M] clause required an LI modification — correct as
predicted. (Both modifications the audit found, Δ₂ and Δ₄, are on [E] clauses.)

**π2 — T1 is the sharpest finding. CONFIRMED, and sharpened.** It is the
sharpest finding. But the predicted verdict ("CLAUSE-TOO-STRONG or OPEN") needs
refining: T1 is not too strong, because LI *can* satisfy it — vacuously, at
`ε ≡ 1`. The defect is that **T1 has no non-vacuity condition**, so soundness
and usefulness come apart. Verdict OPEN, with the open problem stated precisely
(§1, T1). The predicted weakening is right and is cheap in the interface's own
terms, since §7 already carries quarantine.

**π3 — C1 clean under D∞, mapping is the identity. PARTIALLY CONFIRMED.** C1 is
clean and ratelessness matches LI exactly — that half is right, and it is the
clause LI fits best. But the mapping is **not** the identity: the interface's
D∞ (proves-*or-refutes*) is the D-decidable fragment, a proper subset of LI's
`D_∞ = ⋃ₙ Dₙ` (proven). The clause survives via a J1 declaration discipline, but
the draft's operationalization should be corrected before it goes external.

**π4 — F2 needs real mapping work; precommitted rule carries the load.
CONFIRMED.** LI issues no per-request certificate; the LIC is global and
asymptotic. The anytime-valid witness is unavailable and the precommitted rule
carries it entirely.

**π5 — B3 comes out as SI⁻ plus a delta list of order two. CONFIRMED with a
caveat.** The shape is right. "Order two" holds if Δ₂ is priced at its
negligible true cost and Δ₄ is set aside as §9-reserved; counting all four
deltas flat gives four. The two *substantive* unknowns are Δ₁ and Δ₃, which
matches the reviewer's forecast.

---

## 6. What this audit does NOT show

- **Inhabitation is not the witness theorem.** This is a clause-by-clause
  reading audit. Producing SI⁻ is not proving B3; B3 remains to be *proved*,
  and this document only says what its statement should be and which clauses it
  can hope to cover.
- **Nothing here proves the composite guarantee.** §11's conditional visibility
  guarantee is untouched. Establishing that an engine satisfies the interface is
  the antecedent of that conditional, not the conditional.
- **§9's hole is untouched**, by the terms of reference. I checked the three
  adopted requirements and found (i) met natively, (ii)–(iii) not met, and
  stopped. No formal content is proposed for the budget structure or the
  non-exploitability condition under incomplete deduction.
- **T1's open problem is genuinely open in both directions.** I found neither a
  computable coherence modulus for LIA nor a proof that none exists. The
  Sawin–Demski incompatibility is adjacent and must not be cited as settling it.
- **Δ₁ is unaudited beyond its statement.** Whether a declared θ_min survives
  region contraction is a question about the geometry of the region induced by
  LI's prices, which I did not investigate; it may be easy or it may be the
  hardest item on the list.
- **No verdict rests on empirical behaviour of any implementation.** Every
  citation is to a definition or theorem in the paper, a corpus claim ID, or an
  explicit derivation above. Where I could not find a result, I said so rather
  than inferring one.
- **C3's citations are unresolved** (`A0`, `CA`, `MSR-A` occur in neither tree).
  That is a documentation defect in the interface, not a substantive finding
  about LI, but it blocks checking C3 against its stated corpus basis.
