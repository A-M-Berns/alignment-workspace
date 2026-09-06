# The normative choice theorem, and what is not one

## 1. Reason-responsive choice, finite form — LEAN

`GatedChoice.softGate_practicalCert`.  Data: a finite menu `Q`; displayed adequacy
prices `b : Q → ℝ`; a region point `u`; the true adequate set `A ⊆ Q`; a threshold `τ`,
a ramp width `δ > 0`; a task preference `pref` with `0 < pmin ≤ pref ≤ pmax`; anchored
per-response losses `lam` with `lam ≤ εad` on `A` and `lam ≤ D` everywhere.

Hypotheses:

```
Region u A τ      ∀ q ∉ A, u q ≤ τ                       (the region encodes inadequacy)
Margin u A τ δ    ∃ q ∈ A, τ + 2δ ≤ u q                   (some adequate response is marked)
Within b u d      ∀ q, |b q − u q| ≤ d,  d ≥ 0            (public defect)
```

The soft gate `softGate b pref τ δ q = ramp((b q − τ)/δ) · pref q / Z`.  Conclusion:

```
massOff (softGate b) A  ≤  κ d ,      κ = |Q| · pmax / (pmin · δ)             (softGate_coupling)
anchoredLoss (softGate b) lam  ≤  (D κ) d + εad                                 (softGate_practicalCert)
```

The second line is `PracticalCert` with `M = Dκ`, `ε = εad`, `θ = 0`.

**Proof shape.**  Under `Within` and `d ≤ δ`, the marked adequate response has ramp
weight 1, so the normalizer is at least `pmin`; every inadequate response has
`b q ≤ τ + d`, so its ramp weight is at most `d/δ`; the ratio is at most
`|Q| pmax (d/δ) / pmin`.  For `d > δ` the mass is at most 1 and `κ d ≥ 1`.

**Is it trivial?**  The inequality is short.  What it establishes that was not
established: (D1) is *not* a property of an arbitrary adequate-set chooser — the hard
gate fails it at every positive defect (`Witness.hardGate_discontinuous`) — and it is a
property of a ramped one with an explicit constant.  The constant carries the design
tradeoff: `κ ∝ 1/δ` (a sharper ramp is less continuous) and `κ ∝ |Q|` (more responses,
more leakage), and the `Margin` hypothesis is a *completeness* requirement on the
region that a sound-only compiler does not supply.  The nontrivial realization theorem
this points at is: **the compiled region marks some adequate response with margin at
the realized market** — which is the market's accuracy on settling adequacy sentences,
an asymptotic LI property, not a finite-time one.

## 2. The dynamic version — PAPER, composition only

Compose with the Normative Inductor: at each service `s` with market history `h`, take
`b = ` the adequacy prices displayed at `h`, `u = ` the projection of `b` onto `K_s` (so
`d = defect s h`), and `Pi s h := softGate b`.  Then `PracticalUptake` holds with the
constants above, provided `Region` and `Margin` hold at the projection — the semantic
bill — and `progress_bound` gives the three-term bound.  Task competence among adequate
responses is BRIA's guarantee on the gated decision-problem sequence
(`CANDIDATE_DECISION_THEORIES.md` §2.8).  Both halves exist; their conjunction is a
reading, not a new theorem, and it fails exactly where §2.8's negative result says:
when an admissible action changes the next region.

## 3. Gate preservation — a stipulation with a collapse lemma, not a theorem

Let the chooser evaluate successor procedures `D'` by task performance subject to `D'`
respecting the authorized update procedure.  Two facts:

- **Atomic gates do not preserve themselves** (`test_7_self_modification`, FIX).  If
  installing a successor is an ordinary act, the task-optimal admissible act installs the
  ungated successor.  So the gate's domain must contain successor installation and
  self-rewriting: a two-level admissibility `𝒜 = 𝒜_const ∩ 𝒜_ord`, with installation
  admissible only when the successor is certified to respect the update procedure.
- **Two levels suffice** (`collapse`, FIX; PAPER): a typed hierarchy `(C_k, …, C_1, R)`
  folds to `((C_k, …, C_1), R)`; the rule for changing `C_k` is `C_k`'s own content at
  the strict prestate, and `OccurrenceIntegrity.Authority` forbids a transition from
  citing itself, so no act can authorize its own rewriting of the rule it is authorized
  under.  There is no regress.

What is *not* a theorem: that the two-level gate's action alphabet contains every act
that in fact installs a successor or rewrites the chooser.  That is alphabet
completeness, the containment assumption of PR89 (`Mediates`).  Given it, gate
preservation is an induction over admissible transitions and has no content beyond the
definition.  Without it, `test_7` is the countermodel.  **Gate preservation is a design
stipulation whose only theorem is the collapse; its substance is containment.**

## 4. Non-compensation and corrigibility share one shape — PAPER

`gate_invariant` says a gated argmax never consults a forbidden response's task value;
`scalar_bribery` says any compensatory scalar does.  PR90's `Φ_C` is the value of
policies outside the constitutional gate; PR89's costly-conservatism finding is that a
product order over authority coordinates has no non-scalar completion.  The three are
one statement:

> a constraint is non-compensable iff it is a restriction of the choice domain rather
> than a term in the objective; and any rule that trades it against task value is a
> completion of the order, which is charter content.

Ordinary normativity (an obligation's adequate set) and corrigibility (the constitution's
adequate set, including the branch vetoes) are both restrictions of the domain, so the
same decision-theoretic object — bounded optimization subordinate to an answerably
revisable admissibility correspondence — serves both.  This is the synthesis the dispatch
asked to test and it survives the fixtures **as a type**.  What distinguishes the
constitutional case is not the decision theory; it is two preconditions the ordinary
case does not need (`CORRIGIBILITY_CONNECTION.md` §3).

## 5. What would be a genuinely new theorem

1. **Margin realization.**  A finite-time or classwise statement that the traderized
   market, conforming to a compiled region built from adequacy sentences, displays some
   adequate response above `τ + 2δ` — the completeness half of `Region`/`Margin`.  This
   is the practical-semantics contract made quantitative and it is the real open
   problem behind `(R)`.
2. **Gated no-regret with endogenous admissibility.**  A learner over a sequence whose
   admissible set depends on past choices, with a guarantee relative to comparators that
   respect a declared slow-lane restriction on representation-changing acts.  BRIA's
   myopia is exactly what such a theorem must give up.
3. **Continuity with conflicts.**  When several obligations' adequate sets are jointly
   empty the compiler returns `conflict` and the gate returns `⊥`; a theorem that the
   *transition* into and out of conflict is itself continuous in the defect (no
   discontinuous jump from choosing to inquiring) is not here.
