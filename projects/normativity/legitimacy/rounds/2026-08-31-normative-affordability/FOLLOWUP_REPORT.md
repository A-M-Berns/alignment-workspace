# Follow-up audit: does the realization map survive contact?

This pass keeps the round's schematic mathematics and audits its realization.
Three of the round's claims are withdrawn, one is repaired, and the rest stand.
`CORRECTED_STACK.md` states what replaces them.

## A. What Progress should mean

**Verdict: the two-stage decomposition, and the question the round reserved to
the author dissolves.**

The two candidate architectures differ in what each theorem's premise list
contains, and that is the whole of the argument.

*Merged.* One theorem consuming Actionability, Uptake, persistent relevance, a
transport plan `T^r`, a parsimony cap `K_r` and the stability constants
`(L_r, eps_r)`, concluding `limsup E_{mu^r}[d^r] <= eps_r`.

*Staged.*

    (P1)  Actionability + Uptake + persistent relevance
              ==>  E_{nu^r_N}[d^r] -> 0                       [service-weighted]

    (P2)  E_{nu^r_N}[d^r] -> 0 + transport (T1)-(T3) + parsimony
              ==>  limsup_N E_{mu^r_N}[d^r] <= eps_r          [claim-weighted]

Three things separate them, and all three favour the staged form.

**Premise locality.** `(P1)` mentions no scheduler and no claim measure; `(P2)`
mentions no engine, no gain, no margin and no Uptake. The merged theorem mentions
all of it, so a change to either side reopens the whole statement. The round's own
countermodels are already sorted this way: the rotation countermodel is entirely a
`(P2)` failure and says nothing about any engine, while the vanishing-share
countermodel is entirely a `(P1)` failure and says nothing about transport.

**Interface arity.** `(P2)` is a statement about two measures, a plan and a
bounded array. It has no engine parameter at all, so it composes with *any*
engine-side guarantee of the form `E_{nu}[d] -> 0` — including the merged Progress
schematic exactly as that round settled it, and including the LI realization of §B
below, which reaches `E_{nu}[d] -> 0` by a completely different route and shares no
premise with the schematic `(P1)`.

**Where the residual lives.** In the merged form `eps_r` appears in a theorem whose
other premises are semantic and learner-side, so a reader cannot tell which premise
it is charged to. In the staged form it appears only in `(P2)`, next to the plan it
is a property of.

So the base Progress theorem should not be modified. The round's reserved question
— claim-weighted or service-weighted — had a false disjunct: the answer is
service-weighted *base* plus a claim-weighted *layer*, and no settled statement
needs to change. The `DECISIONS.md` queue entry is withdrawn and replaced by a
dated entry adopting the staging.

### The contiguity wording is wrong, and the repair is not cosmetic

`SERVICE_TRANSFER.md` §4 said "contiguity is derived, not assumed." That is false
of the pair the theory is about.

What Theorem T3 proves is `mu~_N <= K nu_N` pointwise, where

    mu~_N(s) = ( sum_t T(t,s) ) / C_N

is the **transported** claim measure — claim mass pushed forward onto the dates
where it was serviced. Nothing is proved about `mu_N` against `nu_N`, and on the
round's own repaired-rotation trajectory the original pair is *not* contiguous:
the odd dates carry `nu_N` mass exactly `0` and `mu_N` mass exactly `1/2`, at every
horizon, while T3's hypotheses hold and its conclusion is true.
`tests/test_transfer.py::DeferredTransfer::test_transport_does_not_derive_contiguity_of_the_original_pair`
pins both halves.

The corrected relation is that **T1/T2 and T3 are incomparable routes to the same
conclusion.** T1 needs a measure-theoretic hypothesis relating `mu` and `nu` and no
hypothesis about the defect. T3 needs no relation between `mu` and `nu` and a
semantic hypothesis about the defect, `(T3)`. Neither implies the other: T1's
route fails on any bounded-delay schedule, and T3's route fails when the defect is
not stable across the deferral. The round's verdict overstated this and is
corrected in place.

The four objects keep the roles the round gave them: `nu^r_N` is where force was
actually spent, `mu^r_N` is where it was owed, `T^r(t,s)` is the matching between
them, and `eps_r` is the only quantity charged to the matching rather than to
either measure.

## B. The Logical Induction realization, rebuilt

### B0. Two sets, and they are not the same set

    K_t     the normative admissible region, presented as rational rows
    A_t     the live assessment set, `PC(D_t)` in the deductive case

`K_t` is a set of **price vectors**; `A_t` is a set of **worlds**, which are cube
vertices. The source's model keeps a third and a fourth object apart from both —
the semantic credal constraint `C_t` of which `K_t = pi_t(C_t)` is the price
image, and the credences over worlds — and records that reading a credence as a
price vector is the error that cost that round a conclusion. Nothing below
identifies any two of them.

The four questions, answered separately.

**1. Against what set is normative force scored?** `K_t`, and pointwise at a
single world. The liability identity gives, at displayed price `P` and world `W`,

    <zeta_E(P), W - P>  =  sum_j beta_j g_j(P) [ (<c_j, W> - r_j) + g_j(P) ]
                        >=  work(P) - charge(P, W) ,

    work(P) = sum_j beta_j g_j(P)^2 ,   charge(P, W) = sum_j beta_j g_j(P) d_j(W) ,

with equality when every violated row also excludes `W`. `g_j` is measured against
`K_t`; `d_j` is measured against the *same* rows but evaluated at a world. So the
force certificate is `K_t`-relative and the charge is the interaction of `K_t` with
`A_t`. `tests/test_li_account.py::ValueIdentity`.

**2. Against what set is liability scored?** `A_t`, worldwise and cumulatively:
`B` is the least bound with `W(sum_{i<=n} E_i) >= -B` for every date and every
`W ∈ A_n`. Not `K_t`, and not per-date.

**3. What produces Uptake?** The market maker's contract, and its cumulative
form. The maker's fixed point bounds the **combined** aggregate at every world and
date, `omega(sum_{i<=n}(TF_i + E_i)) <= sum_i 2^-i < 1`; subtracting the ordinary
trading firm's own floor `-B_F` leaves

    omega( sum_{i<=n} E_i )  <=  U := 1 + B_F        for every date, every omega ∈ A_n .

That constant is the entire source of Uptake. It is a fixed-point/variational
property of the price-setting step, per date and cumulative, and it is not an
asymptotic learning statement.

**4. What does the LIC preservation theorem establish?** That the *substrate*
survives: given `inf_{n, omega} omega(sum_{t<=n} E_t) >= -B`, no efficiently
computable trader exploits the modified market and each has assessed net worth at
most `1 + B`. It is a statement about the **ordinary** trader class, not about the
enforcement position, and it delivers no bound on the enforcement position's own
value.

### B1. Withdrawn: per-reason Uptake is not free from the criterion

The round claimed that the Logical Induction criterion quantifies over each
enforcement trader individually and therefore supplies per-reason Uptake at no
cost. **This is refuted by the construction the round claims to realize.** The
enforcement position is placed in the price-setting aggregate, not in the class the
criterion quantifies over, and the source states the exemption and says it is
load-bearing: for a coherence-polytope presentation the row count is exponential in
the fragment, so the enforcement trader is *not* efficiently computable and is not
required to be. A criterion quantifying over efficiently computable traders says
nothing about it.

The claim is also structurally the wrong shape. Even where the enforcement position
happens to be efficiently computable, the criterion that would have to apply is the
criterion of the **modified** market, which is exactly what the preservation
theorem is for — so the claim, at best, presupposes its own conclusion's hypothesis
and then delivers a bound that the maker's contract already delivers directly and
unconditionally.

Corrected in `JOINT_ACTIONABILITY.md` §5, `REALIZATION_MAP.md` §1, `SAFECERT.md` §4
and `REPORT.md` §2.

### B2. The conjectured factorization, verified with one amendment

    Actionability          <->  projection force against K_t              CONFIRMED
    Uptake                 <->  MarketMaker / fixed-point cumulative cap  CONFIRMED
    Affordability account  <->  worldwise cumulative value over A_t       CONFIRMED
    SafeCert preservation  <->  bounded liability preserves ordinary LIC  CONFIRMED,
                                but this is substrate preservation and not Uptake

The amendment is the whole of B1: LIC belongs on the *preservation* line and
nowhere else. Progress comes from the maker; LIC keeps the epistemic guarantee
the reasoner had before the norm was installed.

### B3. The Progress inequality, derived from the two theorems

Write, over date-and-row pairs `(t, j)`,

    w_{t,j} = beta_{t,j} g_{t,j}(P_t)      the intensity actually spent
    W_N     = sum_{t<N, j} w_{t,j}
    nu_N    = w / W_N                      the service measure
    d_{t,j} = g_{t,j}(P_t)                 the displayed defect
    s_{t,j}(omega) = r_j - <c_j, omega>    the row's **signed** misfit at a world

The clipped deficit `d_j(omega) = max(0, s_j(omega))` is what bounds liability;
the *signed* misfit is what makes the account an identity, at every world and with
no exclusion hypothesis:

    V_N(omega)  =  sum_{t,j} w_{t,j} ( d_{t,j} - s_{t,j}(omega) ) .

Getting this wrong in the clipped direction is a real trap: at a world the row
admits, the clipped form understates the account, and
`tests/test_li_account.py::ProgressInequality` pins both the identity and the
clipped version's failure. The two inequalities are now one line each.

**Progress.** From the maker's cap, `V_N(omega) <= U` for every live `omega`, so

    E_{nu_N}[d]  <=  U / W_N  +  inf_{omega ∈ A_N} E_{nu_N}[s(omega)] .

**Safety.** From the account floor, `V_N(omega) >= -B` for every live `omega`, so

    sup_{omega ∈ A_N} E_{nu_N}[s(omega)]  <=  B / W_N  +  E_{nu_N}[d] .

Subtracting, `sup_omega E_{nu_N}[s] - inf_omega E_{nu_N}[s] <= (U + B)/W_N`, and
`E_{nu_N}[d]` sits within `O(1/W_N)` of both. Since `s <= d(omega)` pointwise, the
Progress bound also holds with the clipped deficit. So, on a safely enforced
trajectory with `W_N -> infinity`:

> **The service-weighted displayed defect converges to the service-weighted misfit
> between the norm and the still-live worlds, and the misfit is asymptotically the
> same at every live world.**

Force drives conformance down exactly to the level at which the norm disagrees with
what can still be true, and no further. `tests/test_li_account.py::ProgressInequality`
checks the identity form and the sandwich exactly.

Three corollaries worth having.

*One compatible world is enough for Progress.* If some `omega_0 ∈ A_N` satisfies
every row enforced so far, its signed misfit is at most `0` on every row, so the
`inf` term is at most `0` and `sum_{t,j} w d <= U`: the cumulative force work is
bounded by a constant, and `E_{nu_N}[d] = O(1/W_N)`.

*One compatible world is not enough for safety.* Liability takes a supremum, and
the same trajectory can be unboundedly loss-making at a different live world.
`tests/test_li_account.py::ProgressAndLiabilityUseOppositeQuantifiers` exhibits
both halves on one trajectory.

*Loss needs a live violation and an excluded world on the same row, and is
extremal in between.* The per-row contribution is `beta g (g - d)`, which is zero
at `g = 0` and at `g = d` and minimal at `g = d/2`. Full conformance and complete
non-conformance are both free; partial conformance is what costs.

### B4. The nonemptiness ladder

`A_t ∩ intersect_r K_t^r != empty` is asked about at four different strengths, and
they do four different jobs.

| condition | what it buys |
|---|---|
| `intersect_r K^r_t != empty` | the force inequality has a region point to evaluate at; without it there is no `work >= 0` term at all |
| some `omega_0 ∈ A_N` in `intersect_{t<N} K_t` | Progress: `sum w d <= U`, cumulative force work bounded |
| a `theta`-covered mixture over `A_N` whose barycenter lies in every active `K_k` | bounded liability, by the Common-Mixture bound `E_N(omega) >= -U(1-theta)/theta` |
| every `omega ∈ A_t` satisfies every row | zero liability, and the account is a sum of nonnegative terms |

The first is the round's T4 hypothesis and involves no assessment set. The second
is what Progress needs and is an `inf`. The third and fourth are what safety needs
and are a `sup`. **Conflating any two of them conflates the Progress quantifier
with the liability quantifier**, which is the specific error B1 corrects.

### B5. What becomes of T4

T4 is correct and **unused in the LI realization.** Positions add, the account is
additive over rows, and the position is recomputed at whatever price the aggregate
produced, so there is no aggregation step at which a per-reason certificate could be
invalidated: the interference countermodel J1 needs a control fixed before the joint
state is known, and the compiler's position is a continuous function of the current
price. The round's stated reason — that LI supplies a common scoring set — is the
wrong reason, and is corrected: the operative fact is **reactivity**, not commonality.

Interference does not vanish in LI; it moves to the budget. Isolating one reason's
account from the maker's combined cap costs the other reasons' floors:

    omega( sum_{i<=n} E^j_i )  <=  1 + B_F + sum_{k != j} B_k ,

so per-reason Progress needs the other reasons' liability budgets to be summable.
That is the correct replacement for the round's "share persistence" condition, and
it is a condition on the *safety* budgets rather than on the scheduler.

T4 keeps its abstract job: an engine whose control is open-loop, or whose gain
certificate is genuinely reason-relative, needs it. Its LI status is "true, not
required".

### B6. The intensity variable

The round asked whether one variable `w^r_t` can be both service allocation and
normative control intensity. It can, but **not** as the position magnitude
`beta_{t,j} g_{t,j}`, which this section proposed and which a later pass withdrew:
that quantity is a function of the fixed-point price, so it is not available at the
date the control is chosen, it is zero exactly when the reason is perfectly
satisfied, and it counts a date as better served because the reasoner did worse on
it. The service variable is the multiplier `beta` itself, and the price of that is
the Cauchy–Schwarz step noted below rather than a defect that enters linearly.
`SERVICE_FORCE_TYPING.md` and `LI_PROGRESS_FROM_SERVICE.md` carry the audit and the
replacement theorem; the account algebra of B3 is unchanged and is simply read
against a different measure.

The source's own warning stands and is not contradicted: intensity is a position
size, not funding, and in the adversarial fixture the realized position size is set
by the opposing ordinary volume rather than by `beta`. Under an exact contract the
realized `w` is not a free variable at all, which is a real limit on how much of the
schematic's scheduling freedom survives — see §"What actually remains".

## C. Affordability is a signed account: Observation E2 is withdrawn

**Verdict: E2 is false as stated, its conclusion is the wrong quantity, and
"persistent service must be self-financing" is refuted.**

E2 said: if every admissible control servicing `r` has robust liability increment
at least `delta > 0`, the total mass ever served is at most `B/delta`.

**The defect is an interchange of supremum and sum.** The account is
`Risk_N = sup_omega ( - sum_{t<N} v_t(omega) )`. E2's hypothesis bounds
`sup_omega ( -v_t(omega) )` at each `t` separately. Since
`sup of a sum <= sum of sups` and never the reverse, per-date robust losses do not
accumulate into a cumulative robust loss: different worlds may be worst at
different dates.

**The counterexample is one sentence and two worlds.** Hold the price at `1/2` and
alternate the row between `P >= 3/4`, which excludes the world `0`, and `P <= 1/4`,
which excludes the world `1`. At `beta = 8` every date has robust loss exactly `1`,
so E2's hypothesis holds at `delta = 1`; the account in each world oscillates and
the liability is exactly `1` at every horizon; and the total force applied is
`2N`, unbounded. `tests/test_li_account.py::PointwiseSelfFinancingIsNotNecessary`
pins all three at horizons up to 128, and also pins the gap: the per-date
certificate charge is exactly `N` where the account is exactly `1`.

**Even the corrected worldwise form does not give self-financing.** A norm may
exclude the sole live world at *every* date, be enforced forever, lose money at
every date, and remain affordable, provided the exclusion depth decays fast enough
for the charge to be summable. The workspace already carries that result and its
exact fixture; this round reproduces the shape independently as
`li_account.decaying_depth`, against `li_account.fixed_depth`, whose account
diverges linearly. So pointwise self-financing is **sufficient and not necessary**,
which is what the source's own corollary says of the world-inclusive case.

**What the conclusion actually bounds.** The corrected limitative statement in the
source bounds the number of *dates* that can carry a positive charge, not the total
service mass: with floors on the exclusion depth and on the ordinary pressure and a
ceiling on the tolerance, at most `B·delta_bar/(cd)` such dates fit. To bound the
total service **mass** the charge must be proportional to the mass, and in these
coordinates it is: the per-date charge is `w_t · e_t(omega)`, so

> **E2′.** If some `omega` is live at every date and `e_t(omega) - d_t >= eta > 0`
> whenever `w_t > 0`, then `sum_t w_t <= B / eta`.

That is the honest form. Its hypothesis is not "each round loses money robustly"
but "one persistently live world is charged more than the displayed defect returns",
and it is exactly the negation of the account inequality of B3.

**This is a re-instance of a mistake the source had already withdrawn.** The
traderized round retracted a theorem claiming that persistent positive exclusion
depth exhausts any finite account, with a counterexample; and its horizon
proposition explicitly records that the per-date-supremum certificate is
conservative because "the criterion follows one world, the certificate takes a
supremum at each date independently". PR75 reintroduced both errors. The corrected
picture is the one the conceptual schematic already stated: **affordability is not a
sum of nonnegative costs; it is the viability of a signed, persistent underwriting
account under the exercise of normative force.**

**The correct necessary notion** is the account condition itself — for every world
live at the horizon, the cumulative value stays above the floor — and it is not
usefully replaced by anything simpler. What the theory should carry instead is the
existing four-way taxonomy of *sufficient* certificates: world-compatible
(zero liability), exposure-bounded (summable inventory), common-underwritten
(a covered mixture), and drift-underwritten (bounded switching debt). "Self-
financing" was a fifth name for the first of these, stated as though it were
necessary. It is deleted.

**T7 survives, restated.** Its hypothesis is pointwise self-financing slack — a
control in the self-financing set outpacing the arrival rate at every reachable
state — and under it max-weight scheduling keeps the backlog bounded and the
account non-decreasing. That is a strong sufficient theorem and this pass leaves it
standing, with the necessity gloss around it removed and the observation that its
budget is `B = 0`, which is why it never had to reason about a signed account at
all.

One open question the alternating counterexample raises and does not answer: it
finances each swing against the world the previous swing punished, which is
available only because the norm sequence is permitted to vary arbitrarily. The
source's model records that arbitrary variation of `K_n` is allowed by every
enforcement statement and by no safety statement. Whether a coherence condition on
the norm sequence — one that would exclude oscillation — recovers something like
E2's intuition is not settled here and is filed.

## D. The SafeCert abstraction

**Verdict: the measurability argument is sound and proves less than the round
claimed.**

What predictability forces is that the safety certificate be a **functional of the
history at which the control is chosen**. A predicate whose truth value depends on
settlements that have not occurred cannot gate a control chosen from `F_{t-1}`.
That much is schematic and survives.

Worst-case-over-live-continuations is *one* such functional and the round treated
it as the only one. It is not. An engine carrying a probability measure over
continuations can certify an expectation, a quantile, an almost-sure bound, or a
supermartingale condition, and each of those is a predictable functional of the
history. The generic interface therefore requires:

- a functional `rho_h` of the control history, evaluable at `h`;
- prefix closure of the induced safe class;
- a consistency property linking `rho_h` to `rho_{h'}` for `h' ⊒ h`, strong enough
  that a certificate issued at `h` is not revoked at `h'`;
- the preservation implication `SafeCert_D(kappa) ==> PreservedUptake(D^kappa)`.

**What is specific to LI** is which consistency property is available. The
assessment structure there is *set-valued* — `PC(D_n)` is a nested family of sets
with no measure on it — so the only monotone predictable functional in sight is the
supremum, and monotone nesting then gives non-revocation for free. That is why the
robust reading is right in the traderized realization, and it is a fact about that
realization's assessment structure rather than a theorem about controlled learners.

Consequently **T5 is realization-shaped as stated.** Its proof consumes
`Assess(h') ⊆ Assess(h)` and the fact that `rho` is a supremum over that set. For a
measure-carrying engine the corresponding statement is a tower or supermartingale
property, which is a genuinely different hypothesis and is not implied by anything
here. T5 is retained with its hypothesis made explicit rather than presented as a
general consequence of predictability.

The round's other SafeCert conclusions stand: the minimal interface is a
prefix-closed class with a consistency property, an account is a presentation
rather than interface content, and an ordered monoid buys nothing over `R` or `R^k`.

## Causal overload, and where Priority 74 now sits

**Verdict: 74 is well-posed and is no longer the highest-value next target.**

The quantifier gap is real and is stated correctly in the round: a certificate on
one settlement-consistent path refutes affordability, and per-path feasibility
everywhere does not deliver a causal policy. What the corrected account picture
changes is the shape of the object a complete certificate would have to be.

The primal is not a scheduling program over a horizon with a scalar budget. It is:
does there exist an adapted intensity schedule whose **worldwise cumulative signed
account** stays above a floor at every horizon, simultaneously for every world the
settlement process keeps live? A per-path Farkas pair separates points of one
path's feasible set. What has to be separated is a *policy* from a family of
adversary responses, and the account is cumulative and signed, so the natural dual
object is a **potential/supermartingale over the assessment family** — a function
of the history that upper-bounds the account slack still achievable, decreases
along every admissible control, and starts below what is owed — rather than a flow
or a cut. Flow/cut duality recovers the per-path relaxation and, on the evidence of
the alternating counterexample, cannot see cross-period financing at all, since a
cut is a sum of per-date capacities and the account is not.

The higher-value target is the **converse of the preservation theorem**, already
filed: whether unbounded cumulative enforcement liability implies that some
efficiently computable trader exploits the modified market. Until that is settled
or refuted, affordability has a sufficient condition and no necessity direction,
every "unaffordable" verdict in this line is really "our route to safety no longer
applies", and an overload certificate for the causal problem would be certifying
the failure of a hypothesis whose necessity is unknown. Sharpening 74's dual object
is worth doing after that, not before, and item 74 is amended to say so rather than
being withdrawn.

## Corrections applied to the round

1. `SERVICE_TRANSFER.md` §4 and §5 — "contiguity is derived" replaced by the
   incomparability statement of §A, with the new fixture cited.
2. `JOINT_ACTIONABILITY.md` §5 — the per-reason-Uptake claim withdrawn and
   replaced by B1 and B5; the "common scoring set" reason replaced by reactivity.
3. `SAFECERT.md` §2 and §4 — the forcing argument narrowed to predictability, the
   set-valued assessment structure named as what makes the supremum the available
   functional, and the preservation row relabelled substrate preservation.
4. `EXISTENCE_AND_DUALITY.md` §2 — Observation E2 withdrawn and replaced by E2′.
5. `REALIZATION_MAP.md` §1 — the mapping table's Uptake row corrected to the
   maker's cumulative cap; a preservation row added.
6. `AFFORDABILITY.md` §2 — the Actionability premise annotated with the friction
   form the realization actually supplies.
7. `README.md` verdict and `state/rounds.json` — updated to the corrected verdict.
8. `REPORT.md` §2 — the "what LI gets for free" answer corrected.

## What actually remains before an end-to-end LI legitimacy theorem?

**Genuinely missing mathematics.**

1. *Necessity of bounded liability* — `PRIORITIES.md` item 40. Without it the whole
   affordability layer is one-directional.
2. *The generalized live-world TradingFirm lift's transcription obligation.* The
   preservation theorem is `lean-proved` only against the pinned dependency's types
   under stated hypotheses; the modified market's computability is recorded as a
   transcription debt, and the deductive instance is unconditional while the
   generalized one is not.
3. *Whether normative statics produce a credal constraint or only a price demand* —
   item 39. The force layer consumes `K_t`; the semantics is `C_t`; the projection
   is not injective. Every claim about what force means depends on which is
   primitive.
4. *A certificate for transport stability across an era boundary.* `(T3)`'s
   constants have no candidate mechanism when the two defects belong to different
   representations of the reason. This is the one obligation in the stack with
   nothing proposed for it.
5. *Whether the realized intensity is a free variable.* **Settled by a later
   pass, in the negative for the realized quantity and the positive for the
   allocated one.** The multiplier is predictable and freely schedulable inside a
   per-date capacity box; the realized position size is not, and is set at the
   fixed point. `SERVICE_FORCE_TYPING.md`.
6. *A causal overload certificate*, in the potential form described above — after
   item 40.

**Terminology and interface cleanup, carrying no mathematics.**

- The staging of §A: no new theorem, a re-partition of premises already proved.
- Deleting "self-financing" in favour of the existing liability regime taxonomy.
- Relabelling LIC preservation as substrate preservation throughout.
- Naming `w` as the position magnitude rather than the multiplier.
- Retiring `J_t`'s third coordinate, which the round already did.

The line between the two lists is the useful output of this pass: five of the six
open items are about *what force costs and whether the cost is necessary*, and none
of them is about Progress, Actionability, transport or scheduling. The schematic
side of the affordability theory is in better shape than the realization side, and
the realization side is blocked on a single missing converse.
