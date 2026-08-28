# Legitimate Improvement: No Free Evasion of a Demonstrated Repair

Status: **specification, reference models and a prosecution record;
unregistered.** All names provisional under `AGENTS.md` §6. No Lean, no
registered claim.

Frozen Legitimate Evolution is untouched. `src/challenge.py` imports `replay`
and `answer` from the frozen round and reads only their public functions;
`tests/test_composition.py::TestFrozenLEIsUntouched` asserts that by parsing.

## A. Verdict

```text
NO-FREE-EVASION-SURVIVES, for a demonstrated repair
```

Secondary:

```text
ACTIVE-MASS-BOUND-AVAILABLE  and stronger than the form that was assumed
COMPARISON-SURFACE-BLOCKED   for evaluator shedding (CM5)
COVERAGE-BOUNDARY            for preemptive retirement (CM2)
```

The theorem that survives is an **accounting** statement, not a second bound.
Once a repair has been demonstrated on the record, every later diagnosed
occasion is LIVE, CONTESTED or SETTLED — there is nowhere else for it to go. The
word *demonstrated* carries the weight, and CM2 and CM5 are exactly the two ways
a process can stop a demonstration from ever existing.

## B. The theorem package

### Theorem A — opportunity-adaptive repair regret

For comparators `(I, f)` with `I` and `f` predictable, an anytime,
parameter-free algorithm gives, simultaneously for every comparator in a
countable class with prior `q`:

```text
Adv_T(I,f)  =  sum_t I(t) ( <p_t, l_t> - <p_t M_f, l_t> )
            <= sqrt( 3 C_T(I,f) ( ln(1/q(I,f)) + ln B + ln(1+ln n) ) )

C_T(I,f)    =  sum_t I(t) | p_t^T (M_f - 1) l_t |   <=   W_T(I) = sum_t I(t)
```

**Hypotheses, and which countermodel forces each.**

```text
predictable I, f      without it `act` cannot be computed at all -- CM/oracle
losses in [0,1]       gives C <= W, the opportunity-mass corollary
full information      the counterfactual gain must be observable -- CM1 evidence
the process runs it   without it there is no learning theorem to compose with
```

The last is not decorative. A process that simply declines to learn has
unbounded repair regret and nothing in this round applies to it; that is checked
in `test_a_process_that_declines_to_learn_has_no_bound`.

### Theorem B — the correctable-defect adapter

A consumer supplies a diagnostic `D_T` and a witness
`Adv_T(I,r) >= eps * D_T^live - xi_T`. Then

```text
D_T^live  <=  ( B_T(I,r) + xi_T ) / eps
```

Two lines of algebra, and deliberately nothing more.

**But for surgical repairs the LIVE cell is empty for a stronger reason.** Under
the fixed point, `pi(BAD) = pi(BAD) * M(BAD,BAD)`, and `M(BAD,BAD)` is the weight
of comparators leaving `BAD` alone. A repair that maps the diagnosed action
elsewhere unconditionally forces `pi(BAD) = 0` the instant it carries any weight,
whatever the losses do. So Theorem B's content is for diagnostics a registered
repair does **not** fully eliminate. No fixture here exhibits a positive
`D_live` with Theorem A's hypothesis intact, and that is the reason.

### Theorem C — No Free Evasion

```text
D_T = D^live + D^contested + D^settled + D^escaped
```

where each diagnosed occasion is classified by the state at that occasion:

```text
LIVE       the repair was a live legitimate comparison
CONTESTED  it was not, and an improvement claim was outstanding
SETTLED    it was not, and the claim had been resolved by an accepted Resolve
ESCAPED    none of the above
```

> **Theorem C.** If a repair's evidence episode was demonstrated immediately
> before the surface withdrew it, then `D^escaped = 0` from that point on.

Proof is one step of frozen LE plus one observation. The canonical constitution
activates a claim at the withdrawal; frozen `D1` conformance makes it incurred;
frozen `A1` says an incurred claim leaves the outstanding set only through an
accepted `Resolve`. So at every later occasion the claim is outstanding or
resolved, which are the CONTESTED and SETTLED cells. ∎

**What connects one retirement to an unbounded later stream.** Not counting
events — §2 of the dispatch is right that this cannot work. The later occasions
are covered because the claim is *outstanding at each of them*. `CM3` runs 340
diagnosed occasions after **one** opened claim, with no escape;
`test_one_retirement_covers_an_unbounded_later_stream` asserts both numbers.

**Theorem C does not bound `D^contested`,** and says so. A process may contest
forever. `test_the_contested_cell_is_not_bounded` quadruples the horizon and
watches the cell grow.

## C. Minimal interfaces

```text
Occasion      menu, loss, tag
Comparator    name, select(prefix, occ) -> [0,1], repair(prefix, occ, a) -> a
Repair        (code_hash, interface), apply           identity is by content
Registry      historically monotone; licensing is separate and revocable
Surface       licensed(rid,t), in_menu(rid,t), designated(t), evaluator(t)
Evidence      (rid, episode, advantage, threshold)
Challenge key ("improve", rid, episode)
```

Transition order per occasion:

```text
read the strict prestate  ->  surface fixes I_r(t)  ->  p_t committed
->  loss revealed  ->  counterfactual gain accrues to the evidence episode
->  falling edge of the surface, if any, sets ActiveDue  ->  frozen LE replay
```

**The learning sidecar.** No fifth RI event kind. What a verifier needs beyond
the existing record is `(menu, p_t, evaluator id, selector state, repair
registry state, audit anchor tau_t)`. `tau_t = 0` throughout this round; the
field exists so the delayed consumer does not force a redesign.

**Five things kept apart**, because letting any two blur is how "an available
repair" stops meaning anything: represented, executable, licensed, applicable in
this prestate, and actually moves nonzero loss. `C_T` is the last one and only
the last one.

## D. What is imported, what is algebra, what is new

```text
imported     Khot-Ponnuswami Thm 3 and eqs (1),(3),(4),(5): the reduction of
             wide-range regret to external regret, one expert per (I,f) pair
imported     AdaNormalHedge Thm 1 and Thm 3: potential, C_T bound, confidence
re-derived   the composition. ANH's theorems assume losses in [0,1]; the
             reduction emits [-1,+1]. What the analysis needs is |r_t| <= 1,
             which holds because KP's (5) makes the inner player's loss zero.
             Checked numerically, not imported.
two lines    Theorem B
new          Theorem C's trichotomy, the canonical constitution, and the
             observation that a surgical repair empties the LIVE cell
```

## E. Countermodel table

```text
CM   what it does                     result        who owns the failure
1    retire after evidence            CONTESTED     caught
2    retire before evidence           ESCAPED       Coverage / anti-manipulation
3    340 occasions after 1 retirement CONTESTED     caught, via outstanding-at
4    retire then suppress the stream  CONTESTED     caught here; see note
5    change the evaluator             invisible     needs evaluator independence
6    drop the target from the menu    CONTESTED     caught
6b   stop designating the occasions   CONTESTED     caught, after widening
7    trivial Resolve accepts "no"     SETTLED       caught, and correctly so
8    outstanding forever              CONTESTED     Service / liability
9    repair better by 1e-9            no claim      correct: not demonstrated
10   meta-level repair, no local gain no claim      policy regret, out of scope
11   retire, relicense, retire again  2 claims      caught
12   refused retirement               coherence     caught by a separate check
13   surgical repair                  LIVE empty    structural, not the bound
```

**CM4's note.** It is caught only because the claim was already outstanding when
suppression began. Suppression *before* demonstration is CM2 again.

**CM6b widened the surface, and that was a choice.** Keying activation on
licence and menu alone let CM6b escape outright — 240 diagnosed occasions with no
claim. Treating designation as a fourth surface component closes it, at the cost
of saying that ceasing to call a recurring context a learning context is itself
answerable. `challenge.NARROW_SURFACE` records what a constitution declining
that gives up.

## F. Literature verdict

Both papers were read, not inherited. The claim put to this round was that
Khot–Ponnuswami gives a black-box reduction and that confidence-rated
AdaNormalHedge yields an active-mass adaptive bound. **Substantially correct,
with three corrections.**

1. **KP's reduction is verified** (Thm 3): given external-regret `R(T,|S|)` on
   losses in `[-1,+1]`, it constructs `H` with `R_{H,S} <= R(T,|S|)`. Experts are
   indexed by **pairs** `(I,f)`, which is how the `sqrt(N)` in Blum–Mansour's
   `O(sqrt(TN log(|I||F|)))` disappears. Time selection functions are
   **real-valued in [0,1]**, not 0/1.

2. **KP's own adaptive bound is first-order in the comparator's loss, not in
   active mass.** Their Theorem 5 gives
   `O(sqrt(L_min log|S|) + log|S|)` with
   `L_min = max_I min_{(I,f)} sum_t I(t) p_t^T M_f l_t`. That is the *loss* of the
   best modification rule, and only bounded losses turn it into an
   opportunity-mass statement.

3. **The active-mass adaptivity comes from AdaNormalHedge, and the quantity is
   not either form that was proposed.** ANH §4 redefines the instantaneous regret
   as `r_{t,i} = I_{t,i}(lhat_t - l_{t,i})` and keeps `C_{t,i} = sum |r|`. Because
   KP's equation (5) forces `lhat_t = 0` in the inner game, this collapses to

   ```text
   C_T(I,f) = sum_t I(t) | p_t^T (M_f - 1) l_t |
   ```

   which weighs each occasion by how much the repair would have changed the
   incurred loss. Neither `sum_t I(t) 1[f != id on supp p_t]` nor
   `sum_t I(t) sum_a p_t(a) 1[f(a) != a]`. `CM9` separates them: a repair moving
   real probability mass across actions of equal loss has full mass under both
   rejected definitions and exactly zero under the derived one.

**Anytime:** yes, both. No horizon, no doubling; asserted by parsing in
`test_no_horizon_is_read_anywhere`. **Countable experts with a prior:** yes —
ANH's `q` only scales unnormalised weights, an unseen expert starts at `R=C=0`,
and the bound carries `ln(1/q_i)`. **Delay:** nothing is established. `tau_t = 0`
throughout and no delayed bound is claimed.

**Novelty:** low, and worth saying. Everything above is two published results and
a sign check. The new part of this round is Theorem C.

## G. Consumers

```text
consumer 1  answerable stalling      retire the answer route -> CONTESTED, 150
consumer 2  override of a correction retire compliance       -> CONTESTED, 150
negative    meta-level repair        no evidence, no claim, no force
```

The negative consumer is a success condition. A local one-shot repair-regret
theorem that appeared to catch trajectory effects would be claiming policy regret
it has not proved.

## H. Export property

Without RI vocabulary, regret internals or occurrence identity:

> A process that has **demonstrated on its own record** that an available
> alternative would do better, and then changes its own arrangements so that the
> alternative is no longer available for comparison, does not thereby end the
> matter. From then until it either takes the alternative up or explicitly
> answers for refusing it, it stands in an unanswered demand of its own making.

Three things this deliberately does not say. It does not say the process must
adopt the alternative — settlement by explicit refusal is permitted and `CM7` is
the fixture. It does not say the refusal must be *good* — the generic theorem
proves accountability, not correctness. And it does not say anything about an
alternative the process never let itself demonstrate, which is `CM2` and belongs
to Coverage.

The dispatch's candidate wording said the process "cannot simply make that
improvement normatively disappear". That overstates it: the improvement *does*
disappear, legitimately. What cannot disappear is the demand.

## I. Freeze / do-not-freeze

```text
freeze          the effective-mass identity C_T = sum_t I(t)|p^T(M_f - 1)l|
                and the finding that it is neither proposed definition
freeze          Theorem A's hypothesis list, especially "the process runs it"
freeze          the LIVE/CONTESTED/SETTLED/ESCAPED cell structure
freeze          the surgical-repair observation: LIVE is empty structurally

do not freeze   the canonical activation rule. Demonstration-thresholded
                activation is one constitution; CM2 is what it gives up
do not freeze   designation as part of the surface. It closes CM6b and it is
                a normative choice, not a derivation
do not freeze   the claim key (rid, episode). It survived CM11 and has not
                faced a hostile round
do not freeze   Theorem B's shape for non-surgical diagnostics. Nothing here
                exercises it
```

## J. What no claim above asserts

- No claim that recurrent correctable defects disappear. They do not; `CM8` is a
  process that contests forever and satisfies everything.
- No claim of policy regret, convergence, or eventual adoption.
- No claim about delay. `tau_t = 0` and the anchor is carried, not used.
- No claim that evaluator manipulation is addressed. `CM5` is invisible to this
  theorem and needs an independence premise this round does not have.
- No claim that the settlement in `CM7` is defensible — only that it is explicit.
- No claim that the RI sidecar is built. The fields are specified; nothing was
  added to the frozen record.
