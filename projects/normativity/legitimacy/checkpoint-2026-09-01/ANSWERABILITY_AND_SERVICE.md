# Answerability and the service mathematics

**The question.** What does *"an inherited reason has a claim on future normative
capacity"* mean now that there is a mathematical service theory?

**The sources.** The conceptual theory is *Diachronic Answerability Under
Self-Revision* (31 August 2026), whose repository counterparts are the
`2026-08-30-answerability-carriers`, `2026-08-30-anchored-slices-auth-transfer`
and `2026-08-31-faithful-semantic-preservation` rounds. The mathematics is the
`2026-08-31-normative-affordability` round. This document reconciles them.

The note is a **working mathematical synthesis; paper proofs, not Lean-verified**,
by its own statement, and is treated here at exactly that strength.

---

## 1. The two vocabularies, aligned

| conceptual object | mathematical object | fit |
|---|---|---|
| matter `m` — the continuing case | the reason `r` whose rows are enforced | good |
| answerability slice `alpha` — one increment of incurred burden, with birth stage and fixed anchored content `c_alpha` | one arrival in the claim stream — the mass `c^r_t` owed at date `t` | **exact**, and the alignment is the key one |
| `Remaining_n(alpha)` — content still owed | unserved claim mass at horizon `n` | good |
| `Satisfied_n(alpha)` | claim mass that has been transported to a service date and discharged | good |
| `Disposed_n(alpha)` — content that legitimately ceased to be owed without being answered | **nothing** | **the largest gap** |
| carriers `Carriers_n(alpha)` — the issues currently representing the content | no analogue; the mathematics has no representation layer | structural gap |
| service attention `a_n(m)`, `Attention_N(m)` | allocated authority `a^r_t`, `A^r_N` | **exact in form, different in economics** — see §3 |
| service opportunity `Work_n(m) != {}` | a date at which the reason's row is priceable and its region nonempty | good |
| anchored interpretation `J_alpha : Rep_alpha -> V_alpha` | *candidate mechanism* for the temporal-stability constants `eps(t,s)` — see §5 | promising, unproved |
| `Ready`, `Discharged`, prerequisites, routes | no analogue; scheduling in the mathematics has no dependency structure | structural gap |

Two objects the mathematics has and the note does not: the **defect** `d_t` (how
badly the reason is answered, as opposed to whether it was attended to), and
**liability** (what attending costs).

---

## 2. What the note names as open, and the mathematics now supplies

The note's §11 lists its own boundaries. Two of them are now answered.

**"Progress and learning."** The note says: *"Unbounded attention is not
improvement. A progress theorem needs an additional reason-to-response structure
identifying feasible responses that a live reason favors over recognizable
nonresponse, together with a dynamic uptake condition ensuring that persistent
comparisons cannot remain behaviorally inert."*

That is **exactly** Actionability plus Uptake, and both now exist. The
reason-to-response structure is the coercivity modulus `phi` with the feasible
repair `Phi_n` and the admissible region `K_n`; the dynamic uptake condition is the
MarketMaker cumulative cap. Theorem F1 then converts unbounded attention into
vanishing defect, and F2 gives the rate `A_N^{-1/2}`.

> The note's Answerability–Service Dichotomy ends at *"attention diverges"*. The
> mathematics starts there and turns divergent attention into vanishing defect.
> The two documents meet exactly at `A_N -> infinity`.

**"Normative affordability and liability."** The note says the theory *"does not
show that many simultaneous normative demands can exert sustained behavioral
pressure while preserving the viability of the underlying reasoning or decision
process"*, and it types the relationship correctly in advance: *"bounded cumulative
liability is one concrete certificate of affordability; the mathematical liability
theory should therefore be treated as a realization of the broader schematic
concept, not as its definition."*

That typing is **adopted here unchanged**. Affordability is the schematic concept;
bounded cumulative enforcement liability is the traderized realization of it. The
affordability round answers the multi-demand question in three parts: persistence
does *not* compete across reasons and needs no Hall condition; timely service
*does* compete and the joint condition is a single sum; and preservation is exactly
what the liability floor buys.

---

## 3. The one place the two theories genuinely disagree

**The note's attention budget is renewable; the mathematics' budget is
consumable.**

The note's Definition 8.15 imposes `sum_m a_n(m) <= 1` **at every stage** — a
per-stage share of a renewable resource. Proposition 8.17 then witnesses
feasibility by weights `w_j` with `sum_j w_j <= 1`: give matter `m_j` a fixed
`w_j` share whenever it has available work, and every matter with infinitely many
service opportunities gets unbounded cumulative attention.

Under that budget non-starvation is nearly free. Under the affordability round's
budget it is not, because there the constraint is a **lifetime** one,
`sum_t L_t(a^r_t) <= B_r`: authority is bought out of a stock that does not
replenish, and its price `L_t` varies with the date.

This is the same distinction `CAUSAL_CAPACITY.md` §1 drew when it withdrew the
rate-region picture: *time-sharing convexifies a renewable per-date flow; the
liability budget is a consumable stock.*

**The reconciliation is Theorem EV1, and it is favourable.** Under the consumable
budget, a persistent affordable schedule exists **iff** an affordable plan
discharging every claim exists, both iff `liminf_t L_t(1) = 0`; and the witness is
a diagonal on geometric tranches `B 2^{-(t+1)}` — structurally the *same*
construction as Proposition 8.17's summable weights, with the tranches now paying
for cost rather than dividing a share.

> **EV1 is the liability-priced version of Proposition 8.17.** Non-starvation
> survives the move from a renewable share to a consumable stock, at the exact price
> `liminf L_t(1) = 0` and no more.

So the note's service theorems are not invalidated by liability. What liability
adds is a **criterion**: there are norms for which no schedule discharges the
demand at any budget, and the note's framework cannot express that failure because
its budget is always spendable.

---

## 4. What Answerability actually exports

> **Answerability exports admissible claim / service / transfer obligations;
> affordability determines which of those traces the learner can safely realize.**

The export has five components. Only the first two are currently consumed by the
mathematics.

1. **A claim stream `c^r_t >= 0`** with provenance — which slice, which matter,
   which admission witness, which birth stage. Consumed.
2. **A set of admissible service traces.** Consumed, but only in the thin forms the
   mathematics can price: a per-window service floor
   (`SERVICE_ADMISSIBLE_EXISTENCE.md`), a uniform deadline `H`, or unbounded
   deferral. The note's own admissibility is richer — `Ready`, only-ready closure,
   idle non-expansion — and none of that is priced.
3. **A transfer law.** The note's one-step conservative transfer component
   `Pre/Post/sat/disp` says how content may move, split, merge, and terminate. The
   mathematics has a transport plan `T(t,s)` which is the *timing* half of this and
   none of the *content* half.
4. **A disposition licence `MayDispose_n(alpha, d)`.** No analogue at all. See §6.
5. **A semantic authentication obligation** — that a claimed satisfaction really
   is satisfaction on the slice's anchored terms. This is where the (T) constants
   should come from. See §5.

**Answerability is not bounded-delay scheduling.** Scheduling is what component 2
looks like *after* the semantics has been discarded. The correct reading is that
bounded-delay scheduling is the currently-priceable shadow of a richer
admissibility notion, and the round's own result — that unlimited deferral makes
eventual answering no harder than persistence — is precisely the statement that
**the shadow is trivial unless delay matters**. Which is a reason to expect the
substantive content of Answerability to live in components 3, 4 and 5, not 2.

---

## 5. Where the conceptual language now has a mathematical realization

| conceptual claim | mathematical realization | strength |
|---|---|---|
| "incurred content cannot silently disappear" | `Remaining` is the residual mass of `mu^r`; T3's residual-density term `D R_N/C_N` is exactly the unserved fraction and must vanish | **realized** |
| "a matter that stays live gets unbounded attention" | `A^r_N -> infinity`, hypothesis (S) of STS | **realized** (as a hypothesis, discharged by S1's criterion) |
| "unbounded attention is not improvement" | F1/F2: attention plus coercivity plus Uptake gives vanishing defect at rate `A_N^{-1/2}` | **realized, and this is the note's own named gap closed** |
| "a burden is owed on the terms it was incurred on" | the claim measure `mu^r_N` weights by *arrival*, not by service; claim-weighted Progress is the statement that the arrival-time weighting is what converges | **realized** |
| "revision must not rewrite what was already owed" | anchored content `c_alpha` fixed at admission; in the mathematics, `c^r_t` is `F_{t-1}`-measurable and never revised | **realized structurally**, unpriced |
| "semantic content survives representation change" | hypothesis (T): `d_t <= L_r d_s + eps_r(t,s)` | **named, not realized** — see below |
| "answering may be deferred" | transport `T(t,s)`, delay `H`, temporal modulus `omega_r(H)` | **realized** |
| "an unanswerable demand should be visible as such" | deadline insolvency `ReqCost > B_remaining` | **realized**, for arrived claims only |
| "content may legitimately cease to be owed" | — | **not realized** |
| "a later reason may defeat an earlier one" | — | **not realized** |

### The (T) constants, and the note's candidate mechanism

Hypothesis (T) is the last symbol in Sharp Timely Service without a construction.
The note supplies a **candidate**: the anchored interpretation
`J_alpha : Rep_alpha -> V_alpha`, together with the representation-fidelity
preorder `x ⊑ y` and slice faithfulness (order-reflection). Crucially `J_alpha` is
*anchored to the slice* — it is not "what the current evaluator says the old
representation means" — which is precisely the property a stability constant needs
if it is not to be rewritten by the revision it is supposed to audit.

**What would have to be shown.** `J_alpha` and `⊑` are ordinal; `eps_r(t,s)` is
metric. Turning one into the other needs a quantitative fidelity measure on
`Rep_alpha` whose failure bounds the defect discrepancy — i.e. a modulus for
"how much answerability-relevant distinction did this representation change lose".
Nothing in either body of work supplies it. Filed as `PRIORITIES.md` item 76, and
this is the most concrete route to it currently visible.

---

## 6. Disposition: the gap that matters most

In the service mathematics, claim mass has exactly two fates: it is served, or it
remains. There is no third.

In the note there is a third — `disp(t)`, content *"claimed to have legitimately
ceased to be owed without being answered"*, licensed by `MayDispose_n(alpha, d)`
and authenticated like everything else.

This is not a cosmetic difference.

- **It changes the affordability question.** `C^r_N -> infinity` is a hypothesis of
  EV1 and drives the whole persistence analysis. If claim mass can be legitimately
  disposed of, the relevant divergence is of *undisposed* claim mass, and a norm
  that looks insolvent may be affordable after authorized disposition.
- **It is the obvious laundering channel**, and the note knows it: disposition is
  the term Theorem 7.5 has to authenticate to make no-laundering true. An
  unaudited `disp` makes every insolvency disappear.
- **It is where defeat lives.** "Reason `r'` defeats reason `r`" is, in this
  vocabulary, a licence to dispose of `r`'s remaining content. So the open Layer II
  question *when may one reason defeat another* is exactly the question *what
  licenses `MayDispose`*, and neither body of work answers it.

> **The single most valuable Layer II result would be a theory of authorized
> disposition** — because it simultaneously supplies defeat, closes the laundering
> channel, and repairs the affordability question's hypothesis.

---

## 7. What this reconciliation does not establish

That the note's objects and the round's objects are formally the same objects; the
alignment in §1 is a reading, and no map has been constructed. That the note's
service assumptions (idle non-expansion, wait responsiveness, non-starvation) are
satisfiable jointly with a consumable liability budget in any concrete instance —
EV1 says the *criterion* transfers, not that any particular reasoner meets it. That
disposition can be given a theory at all. That `J_alpha` yields a metric modulus.
