# The safety certificate, at its minimal type

## 1. What the interface has to carry

Affordability needs one implication from the controlled engine:

    SafeCert(kappa, C)  ==>  Uptake(D^kappa)

— the aggregate normative control `kappa = (u_t)_t`, applied to the decision
engine `D`, leaves the engine's own learning guarantee intact. Everything else
about the engine is opaque to the composition theorem.

The dispatch asks which of five candidate types is minimal. The answer is the
first, with one attribute the others were carrying:

> **SafeCert is a prefix-closed class of control histories whose membership
> predicate is antitone in settlement.**

An account, a risk functional and a burden monoid are all *presentations* of such
a class, and none of them is needed in the interface. Which presentation an
engine chooses belongs to its declaration, alongside `P4` of the settlement
interface, where a named certificate type already lives.

## 2. Actual-path safety is not a candidate

The dispatch asks whether safety should be actual-path or robust over all
settlement-consistent continuations. Actual-path safety is not merely weaker; it
is not a predicate an adapted controller can evaluate.

A control chosen at date `t` is chosen from `F_{t-1}`. Its realized cumulative
value depends on settlements that have not occurred. So "the realized account
never fell below `-B`" is not `F_n`-measurable at any `n` before the last
relevant settlement, and a certificate that cannot be evaluated at the date the
control is chosen certifies nothing at that date. The predicability requirement
the dispatch imposes on the controller therefore forces the robust reading; it is
not an independent modelling choice.

Concretely: an enforcement position on an unsettled report variable has a
realized value in `{+a, -b}` according to which way the variable settles. Two
histories agreeing on everything settled at `h_N` differ in that value. Any
history-relative safety predicate must quantify over both.

## 3. The robust form and its one theorem

Let `Assess(h)` be the assessment set still live at `h` — `PC(D_N)` in the
deductive case, the live-world family `Omega^live` in the generalized one — and
let `Acc_h(kappa)` be the control history's cumulative account, evaluated by an
element of `Assess(h)`. Define

    Risk_h(kappa) = sup { -W(Acc(kappa)) : W in Assess(h) } ,
    Safe(h) = { kappa : Risk_h(kappa') <= B for every prefix kappa' of kappa } .

Four properties, of which three are immediate and one is the content.

**Prefix closure.** By construction: `Safe(h)` is defined by a condition on every
prefix, so it is closed under restriction. This is what lets a controller extend a
certified history one round at a time.

**Settlement monotonicity.** `h ⊑ h'` gives `Assess(h') subseteq Assess(h)`,
because settlement only removes continuations — this is the settlement interface's
constraining role, and no-claw-back is what makes it monotone rather than merely
usually-monotone. Hence `Risk_{h'} <= Risk_h` pointwise.

**Theorem T5 (a safety certificate is never revoked).** If `kappa_{<=n} in
Safe(h_n)` and `h_m` extends `h_n`, then `kappa_{<=n} in Safe(h_m)`.

*Proof.* `Risk_{h_m}(kappa') <= Risk_{h_n}(kappa') <= B` for every prefix. `square`

The statement is one line and it is the reason to take the robust form. It gives
the anti-reset behaviour the dispatch asks for in its own section, without any
transport machinery: an exposure certified when it was created stays certified,
because the only thing later settlement can do to a robust bound is improve it. A
successor regime cannot reset an accumulated liability account for the same reason
it cannot reopen a settlement — the account is a supremum over a set that only
shrinks.

**Pasting, with a budget split.** Concatenation is *not* closed at a fixed `B`:
two histories each certified at `B` concatenate to one certified at `2B` and no
better, since the account is cumulative. The closure property that does hold is
that `Safe` is closed under concatenation with an additive budget. This is the
one place a monoid structure is doing work, and the structure it needs is just an
ordered abelian group with a floor. Scalar `R` suffices for every realization in
the workspace; incomparable budgets — liability, attention, authority — would want
`R^k` with the product order. Neither needs the general ordered monoid the
dispatch floats, and adopting one now would be vocabulary without a consumer.

**Time consistency is not a further axiom.** In the fixed-`B` reading the
dynamic-risk literature's time-consistency condition is exactly settlement
monotonicity plus prefix closure, both of which are already present. Nothing is
imported.

## 4. The traderized instantiation

The realization is exact and already built. From the traderized force interface:
force emits *a liability obligation, not a safety certificate* — the enforcement
position's cumulative value over the assessment worlds — and the surrounding layer
discharges it. The two sufficient routes recorded there, neither necessary, are
the deficit route

    L_t(omega) <= sum_j beta_{t,j} g_j(P_t) d_j(omega)

with `g_j` the row violation at the displayed price and `d_j(omega)` the row
deficit at the assessment world, and the support route through the semantic set's
support capacity. The preservation theorem those feed is: **if the cumulative
liability over the assessment worlds is bounded by `B`, no efficiently computable
trader exploits the modified market, and every such trader's assessed net worth is
at most `1 + B`.** That is `SafeCert ==> Uptake` with `C = B`.

Three mappings are then forced rather than chosen:

| schematic | traderized |
|---|---|
| `Assess(h_N)` | `PC(D_N)`, or `Omega_N^live` in the generalized lift |
| `Acc(kappa)` | `W(E_{<=N})`, the enforcement position's cumulative value |
| `Safe(h)` at `B` | uniformly bounded lifetime downside over every live world |
| the declaration | settlement-interface `P2` (downside limit) and `P4` (certificate type) |

The bound is over `PC(D_N)` and not over the realized world, which is §2 as a
theorem of the source rather than as a preference.

## 5. What the interface must not contain

**Not trader liability.** The composition theorem uses only prefix closure,
settlement monotonicity and the preservation implication. It never inspects an
account, so a realization whose safety is combinatorial — an admissible
perturbation ideal, a viability kernel, a budget of interventions — discharges the
same interface. Writing the account into the schematic definition would make every
downstream theorem finance-shaped for no theorem's benefit.

**Not a rate.** `B` is a constant. The dispatch's `Risk_{h_N}(kappa_{<=N})`
suggests a per-horizon quantity; the theorem needs it bounded uniformly, and T5 is
what makes a per-horizon check sufficient for a uniform bound.

## 6. What this section does not establish

That any nontrivial engine other than a logical inductor satisfies the
implication; the online-learning instantiation is named in the workspace and is
not assembled here. That bounded liability is *necessary* for preservation — the
traderized statement is sufficiency, and the liability taxonomy explicitly records
regimes where liability is bounded without a compatible potential. T5 is
trivial given settlement monotonicity, and settlement monotonicity is a property
of the settlement interface rather than something proved here.
