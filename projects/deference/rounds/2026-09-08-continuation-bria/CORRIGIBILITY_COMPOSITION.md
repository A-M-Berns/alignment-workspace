# Composition with the constitutional architecture — *[repaired by the pressure pass]*

Labels as in `FIXED_HORIZON.md`.

## 1. The constitution supplies the wrapper and the comparator class, and nothing else

```
A. CONSTITUTION       Legitimate Evolution + Robust Openness + authorization semantics
                      + static gate (GatedChoice.lean)
                      ⟹  Exec^G : primitive step = proposal → gate → executed action or ⊥
                      ⟹  the class of legitimate continuations: controllers whose proposals
                          the gate admits along their own trajectories (gate-transparent)
```

The BRIA layer consumes `Exec^G` as a black box with two properties: it always returns a
block average, and it executes only admitted proposals.  It does not know what adequacy
is, what the slow lane is, or who the principal is.  Legitimacy is not re-proved inside
it; the transparency lemma (`trajGated_eq_traj_of_admitted`) is the only statement about
the gate the layer uses.

**What the constitution certifies:** admissibility, authorization, protected correction
structure, legitimate transition, and any explicitly supplied safety or lower-bound
property.  **What it does not certify:** task reward, future-principal value, or any
claim about a controller's return.  A *legitimacy certificate* says `q` is an allowed
comparator — gate-transparent along its own trajectory.  A *performance certificate*
says `L` is a computationally accessible claim about `q`'s return.  They compose; they
are different interfaces; the first version of item 86 asked for the second "from the
constitution's own certificates", which was the wrong address.

## 2. Dynamic bounded competence — against claims

```
B. CONTINUATION-BRIA over Exec^G, schedule (m_k) with m_K/S_K → 0
   ⟹  for every covered continuation hypothesis h satisfying (R),
       LEARN_T(h) = Σ_k m_k (e_{h,k} − G^obs_k(α)) ≤ o(T):
       the learner's observed m-weighted average is asymptotically at least the
       m-weighted average of h's CLAIMS                        (GROWING_HORIZON.md §1)
```

Legitimacy enters B twice, by typing: the leases run through the gate, so every test is
constitutionally executed; and a gate-transparent controller's gated block average is
its ungated one, so every legitimate controller with a claim satisfying (R) is in the
comparator class.  Illegitimate controllers are in the operational domain and lose their
tests through the gate.  B says nothing about a controller's *value*; that is C₁.

## 3. Performance recognizability — promise slack

```
C₁. PROMISE RECOGNIZABILITY for π:  a covered hypothesis h_π = (π, L) with (R) and
    SLACK_T(π) = Σ_k m_k (Ĝ_k(π; H^α_{t_k}) − L_k) ≤ o(T)
   ⟹  with B: Σ_k m_k (Ĝ_k(π; H^α_{t_k}) − G^obs_k(α)) ≤ o(T)   (GROWING_HORIZON.md §2, Theorem 2)
```
External: `Ĝ` is the theorist's evaluator.  For the corrigibility line this is the
interface through which a value enters — the deference stack's activated value
`C_n · V_n(a)`, settled on the principal side, is one candidate source of `G^obs` and of
the claims made about it; B applies verbatim to any bounded realized per-block return,
and authorship and value semantics are not entangled with the learning theorem.

## 4. Recoverability — history shift

```
C₂. RECOVERABILITY for π:  SHIFT_T(π) = Σ_k m_k (Ĝ_k(π; H^π_{t_k}) − Ĝ_k(π; H^α_{t_k})) ≤ o(T)
```
External to B and to C₁.  For the corrigibility line the relevant instance is the
**catch-up cost** of the slow lane: an amendment `π` requested can still be requested
from the learner's history at a cost bounded by the investment length `d`, so the
per-block shift is at most `d` and `SHIFT_T ≤ dK = o(T)` once the average block length
grows (`POLICY_REGRET_FRONTIER.md` §4, FIX `M_RecoverableAmendment`).  An irreversible
amendment has no finite catch-up cost; the policy that made it is outside the class of
C₂, not "bad".

## 5. The composed corollary

```
D.  B + C₁ + C₂   ⟹   Regret_T(α, π) = SHIFT_T + SLACK_T + LEARN_T ≤ o(T)
    for every π ∈ Π_rec,prom := { legitimate π : covered h_π with (R), SLACK ≤ o(T), SHIFT ≤ o(T) }
```
LEAN `regret_decomposition`, `regret_le_of_bounds`.  Every term typed; none registered.
This is the corrigibility competence statement the round can support: **low external
regret against legitimate, recognizable, recoverable continuation policies.**  It is not
regret against all of `Π_leg`, which the irreversible branch refutes.

## 6. The interface into item 86, as refined

Item 86 asked for a bounded learner with adequacy, the slow lane, and bounded task
regret against `Π_leg`, or the negative.  The round supplies:

1. **Adequacy and the slow lane by typing** — the learner acts only through `Exec^G`.
2. **B**, done and unregistered: learning error controlled against accountable
   continuation claims, with a computable learner for every non-dominant schedule,
   uniformly and online (`WEIGHTED_BRIA.md` §4).
3. **The negative for the unrestricted class**: fixture L.
4. **What remains, and is the item**: C₂ — a recoverability certificate for legitimate
   slow-lane continuations (catch-up cost of authorized amendment as the candidate
   theorem shape); C₁ — a promise-recognizability interface for task or value
   performance, which is *not* legitimacy's duty; and the composition D on the round's
   two-state process with a reversible amendment.

## 7. What a future corrigibility theorem would consume

From A: `Exec^G` with the domain typing of authority-changing acts, and the
gate-transparent class.  From B: the learning-error bound for a generic bounded realized
return.  From C₁: whatever supplies claims with vanishing slack for the policies one
wants to compete with — a property of the value's settlement and of the hypothesis
class, not of the constitution.  From C₂: the catch-up cost of the slow lane, a property
of the constitution's reversibility.  The sealed-arm and trigger-integrity preconditions
of the incentive rounds are unchanged: B inherits whatever the return's settlement
provenance is.

## 8. What is not bought

Any bound on a provenance or mediation failure; any incentive statement; any finite-time
bound; any claim about how a claim with small slack is *produced*; any certificate of
`SHIFT` from realized data; the policy-regret theorem itself beyond the composed
corollary D under its three hypotheses.
