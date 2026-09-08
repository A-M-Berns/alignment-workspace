# Composition with the constitutional architecture

Labels as in `FIXED_HORIZON.md`.

## 1. The constitution supplies the wrapper, and nothing else is asked of it

```
A. CONSTITUTION       Legitimate Evolution + Robust Openness + authorization semantics
                      + static gate (GatedChoice.lean)
                      ⟹  Exec^G : primitive step = proposal → gate → executed action or ⊥
```

The BRIA layer consumes `Exec^G_m(H, q)` as a black box with two properties: it always
returns a block average, and it executes only admitted proposals.  It does not know what
adequacy is, what the slow lane is, or who the principal is.  Legitimacy is not re-proved
inside it, and the transparency lemma (`trajGated_eq_traj_of_admitted`) is the only
statement about the gate the layer uses: for a controller the gate never refuses, the
wrapper is invisible.

## 2. Dynamic bounded competence

```
B. CONTINUATION-BRIA over Exec^G, schedule (m_k) non-dominant
   ⟹  the learner cannot asymptotically underperform, in m-weighted primitive-time
       average, any e.c. continuation hypothesis whose contextual promises are sound on
       the leases it is granted from the learner's actual histories
       (GROWING_HORIZON.md §1; construction WEIGHTED_BRIA.md §3–4)
```

Legitimacy enters B twice, both by typing and not by theorem: the leases run through the
gate, so every test is constitutionally executed; and the comparator class contains every
legitimate controller with a sound promise, because for such a controller the gated block
average is the ungated one.  Illegitimate controllers are in the operational domain and
lose their tests through the gate; they are not in the comparator class because their
promises are about trajectories the wrapper does not produce.

## 3. Testability / recoverability

```
C. UNIFORM BLOCK RECOVERY for π, S_K/K → ∞
   ⟹  actual-history continuation tests approximate own-trajectory performance:
       Δ_T(π) = o(T)                                     (POLICY_REGRET_FRONTIER.md §4)
```
External to B.  For the corrigibility line the relevant instance is *recoverable
endogenous admissibility*: an amendment `π` would have requested can still be requested
from the learner's history, at a cost bounded by the investment length.  An
**irreversible** amendment is exactly the case C fails, and then no theorem of the
competence kind reaches `π`'s own trajectory.

## 4. The optional external corollary

```
D.  B + C + vanishing promise slack for π   ⟹   V_T(π) − V_T(α) ≤ o(T)
```
`POLICY_REGRET_FRONTIER.md` §4.  Every term is typed; none is registered.

## 5. The interface into item 86

Item 86 asks for a bounded learner that keeps current soft-gate adequacy, alters the
admissibility process only under the slow-lane relation, and has bounded task regret
against `Π_leg`, the computable continuation policies that choose adequately and alter
admissibility only through authorized transitions along their own trajectories — or a
proof that no learner of the BRIA shape can.

What the round supplies, exactly:

1. **Keeps adequacy and the slow lane by typing.**  The learner acts only through
   `Exec^G`; every executed action is gate-admitted; admissibility-changing acts are typed
   into the slow lane by the gate's domain (the decision-theory-bill round's (A)).  Nothing
   new.
2. **Bounded competence against a class that contains `Π_leg`'s promise-bearing part.**
   For `π ∈ Π_leg` and any e.c. sound contextual promise `L` for `π` on the learner's
   histories, the learner's `m`-weighted average is asymptotically at least the
   `m`-weighted average of `L`.  This is B.  It is competence against *hypotheses*, not
   against policies: `Π_leg` members without an e.c. sound promise are not reached, and
   the round's §4 of `GROWING_HORIZON.md` argues that is the right class.
3. **Not task regret against `Π_leg` on its own trajectories.**  The irreversible-branch
   fixture is in `Π_leg` on both branches and defeats every learner.  Item 86's "bounded
   task regret against `Π_leg`" is therefore **false as stated** for the unrestricted
   class, by fixture L, and true in the form D under C.  The refinement of item 86 in
   `PRIORITIES.md` records this: the item now asks for the recoverability certificate
   that would let B compose to D on the round's two-state process, and for the promise
   class.
4. **The two-state process.**  On the item's own fixture (`d = 1`, persistent) the
   one-step auction is already competent (`FIXED_HORIZON.md` §4A); the myopic learner it
   cites is not a BRIA.  The witness the item asks for exists at `m = 2` and at every
   growing schedule.  For the process to defeat a bounded inductive learner one needs a
   multi-step or renewable amendment, and then the weighted construction with a growing
   schedule learns it (Corollary B).

## 6. What a future corrigibility theorem would consume

- From A: `Exec^G` with the domain typing of authority-changing acts; nothing about the
  value.
- From B: the competence statement with `G_k` a generic bounded realized return.  When
  the deference line supplies a return — the activated value `C_n · V_n(a)` of the
  legitimate-deference stack, settled on the principal side — it enters as `G_k`, and B
  applies verbatim provided the return is realized per block and bounded.  Authorship and
  value semantics are not entangled with the learning theorem; that is the point of
  stating B for a generic return.
- From C: a recoverability certificate for the amendment structure, which is a property
  of the constitution (reversibility of the slow lane) and not of the learner.
- The sealed-arm and trigger-integrity preconditions of the incentive rounds are
  unchanged: B is a statement about realized returns and inherits whatever the return's
  settlement provenance is.

## 7. What is not bought

Any bound on a provenance or mediation failure; any incentive statement; any finite-time
bound; any claim about how a hypothesis's promise is *produced* from the constitution; the
policy-regret theorem itself.
