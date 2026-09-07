# The normative choice theorem, exactly, and what is not one

Labels as in `DECISION_THEORY_BILL.md`.

## 1. The static theorem — LEAN

**Adapter characterization** (`adapter_coupling`, `adapter_practicalCert`).  Finite
menu `Q`, adequate set `A ⊆ Q`, anchored losses `lam ≤ εad` on `A` and `≤ D` on `Q`.
Any adapter `D : (Q → ℝ) → (Q → ℝ)` that is sound at a region point `u`
(`massOff (D u) A ≤ θ`) and `ℓ¹`-Lipschitz between the displayed scores `b` and `u`
(`l1 (D b) (D u) ≤ κ d`) satisfies

```
massOff (D b) A ≤ κ d + θ                                       (D1)
anchoredLoss (D b) lam ≤ (D κ) d + (εad + D θ)                  PracticalCert
```

**Soft-gate realization** (`softGate_massOff_le_sharp`, `softGate_coupling`,
`softGate_practicalCert`, `softGate_massOff_le_displayed`).  Under `Region u A τ`,
`Within b u d`, a margin of mass `W > 0` by route A (`MarginMass` on `u`) or route B
(`MarginDisplayed` on `b`), and on the regime `total b > 0`:

```
d ≤ δ:   massOff (softGate b) A ≤ (Σ_{q∉A} pref q) / W · (d/δ)          (route A, MarginMass on u)
d ≥ 0:   massOff (softGate b) A ≤ (Σ_{q∉A} pref q) / W · (d/δ)          (route B, MarginDisplayed on b)
d ≥ 0:   massOff (softGate b) A ≤ κ d,      κ = |Q| pmax / (pmin δ)   (coarse form)
         anchoredLoss (softGate b) lam ≤ (D κ) d + εad .
```

**Necessity of continuity** (`Witness.hardGate_discontinuous`).  The hard gate is sound
at every region point and at every `d > 0` executes an inadequate response with mass
one.  So soundness alone is not (D1); the continuity half is the content.

**Is it trivial?**  The inequalities are short.  What they establish: (D1) is a
continuity property of the adapter, it fails for the natural hard gate, and a ramp
supplies it with a constant whose form — inadequate preference mass over certified
adequate mass, per unit of defect relative to the ramp — is the whole rate story of
`DECISION_THEORY_BILL.md` §5.

### The chain, with each conclusion the next hypothesis

| layer | concludes | consumed by |
|---|---|---|
| legitimate reason state | the anchored obligations at a prefix (`ObligationState`) | adequacy semantics |
| adequacy semantics (EXT) | `A ⊆ Q`, `lam ≤ εad` on `A`, `lam ≤ D` | `adapter_practicalCert`'s loss hypotheses |
| compiled region (EXT) | `Region u A τ` at the projection `u`; a margin by route A (`MarginMass` on `u`, compiler completeness) or route B (`MarginDisplayed` on `b`, a displayed-score theorem) | the soft gate's hypotheses |
| market proximity (`NormativeInductor`) | `Within b u d` with `d = defect s market` | the soft gate's `Within` |
| soft gate (LEAN) | `massOff (softGate b) A ≤ κ d`, `κ = (Σ_{∉A} pref)/(W δ)` | `adequate_set_route`'s `hcouple`; equivalently `adapter_coupling`'s conclusion |
| practical semantics (LEAN) | `anchoredLoss ≤ (D κ) d + εad`, i.e. `PracticalCert` with `M = D κ`, `ε = εad` | `PracticalUptake.practical` |
| amplification (EXT, rate) | `Σ_e T e s · D κ_s ≤ Γ lam s / Σ lam` | `PracticalUptake.amplification` |
| Normative Inductor (LEAN) | `progress ≤ Γ √(Σρ/Σlam) + Σ T εad + D · residual` | the consumer |

Every arrow is a literal hypothesis match except the two marked EXT, which are where
semantics and the rate enter.

## 2. What the static theorem closes, and under what — PAPER

For one finite decision occasion with an exogenous true adequate set `A`, an encoded
region with `Region` and `MarginMass`, and a fixed task preference:

> **The finite static reason-to-action problem required by the Normative Inductor is
> closed conditional on a pointwise adequacy-semantics / positive-margin interface.**
> Region soundness + a margin (route A on `u` or route B on `b`) + a sound stable adapter
> give everything the practical-response layer consumes from decision theory, with the
> constant `κ = (Σ_{∉A} pref)/(W δ)` charged through the amplification hypothesis.  The
> conceptual theorem is *sound at the normative region + stable response to score error
> ⇒ PracticalCert*; the soft gate is one realization.

Outside the static theorem, by construction: task competence among adequate responses
(the application's, `CANDIDATE_DECISION_THEORIES.md` §2.8); actions that change the
future adequate set (§5); self-modification (§3); manipulation of what settles the
scores (`CORRIGIBILITY_CONNECTION.md`); infinite menus; and the inquiry regime (§4).

## 3. Gate preservation — a representation plus a domain condition, not a theorem

Two exact facts and one honest non-result.

- **Atomic gates do not preserve themselves** (`test_7_self_modification`, FIX): if
  installing a successor is an ordinary act, the task-optimal admissible act installs an
  ungated successor.
- **Representation** (`collapse`, FIX): a finite typed hierarchy `(C_k, …, C_1, R)` is
  representable as one constitutional object carrying its amendment rule plus an
  ordinary state; and `OccurrenceIntegrity.Authority` (a transition cites only prior
  grounds, under a warrant in force at the strict prestate) means no event authorizes
  its own constitutional rewrite.  This is a *representational/authorization* result.
  It says nothing about what a chooser prefers.
- **Preservation under self-modification = domain completeness + admissibility of
  successor installation.**  If the gate's action alphabet contains every act that
  installs a successor or rewrites the chooser, and such acts are admissible only when
  the successor is certified to implement the current authorized-update functional,
  then every admissible trajectory preserves the gate — by induction on admissible
  transitions, with no content beyond the two conditions.  Alphabet completeness is
  PR89's `Mediates`.

**Is there a stronger reflective theorem?**  Take the chooser that evaluates a successor
by (1) whether it implements the current authorized-update functional and then (2) task
competence in the resulting admissible domain.  Does a gate-preserving successor
dominate an ungated one?  Only because (1) is a gate on successors: the ungated
successor fails (1) and is never compared on (2).  That is the domain condition
restated as a preference, not a theorem about preferences.  No reflective content is
claimed.

## 4. Inquiry and conflict — what Progress requires

The Progress theorem consumes `(R)` per supported edge and charges everything else
through the residual `D · (1 − Σ T)`.  Two consequences:

- **Continuity through the switch to inquiry is not required by Progress.**  The
  wrapper's jump from the soft gate to the point mass on `⊥` happens only when
  `MarginMass` fails at that occasion (`gateWithInquiry_regime`).  At such an occasion
  `(R)` is not claimed, so the occasion must not carry transport: the evaluation protocol,
  committed before responses, transports mass only to occasions that are
  margin-certified, and the rest is residual.  On route A the margin is a property of the
  compiled region point and is decidable when `T` is committed; on route B it is a
  property of the realized market and must be certified before the response is scored,
  which is the same commitment the evaluation protocol already makes for `μ` and `T`.
- **Inquiry as a response.**  If the reason representation compiles a sentence
  `Adequate(⊥)` — inquiry is adequate exactly when the obligations conflict or
  adequacy is unsettled — then `⊥ ∈ Q` with its own score and the soft gate covers it
  with no special mode: the transition between choosing and inquiring is the ramp on
  `⊥`'s score, continuous, and `Margin` is supplied by `⊥` whenever the conflict is
  compiled.  The Lean theorems are menu-generic and apply verbatim.  What this costs is
  a semantic commitment: `Adequate(⊥)` must be true when and only when no other
  response is adequate or the docket is in certified conflict — the compiler's
  `conflict` output with its Farkas certificate is the natural ground for it.  With that
  commitment the wrapper is unnecessary; without it the wrapper is the total map.  Both
  are recorded; the first is cleaner.

## 5. The dynamic problem — OPEN, with the shape fixed

`test_dynamic` (FIX) fixes the minimal setting: a history-dependent admissibility process
`A(H_t)`, actions that move `H_t`, a slow-lane authorization for admissibility-changing
acts, and continuation policies.  Three findings, exact on the fixture:

- **Legitimate comparators exist and induce different admissibility sequences.**  The
  myopic gated learner and the investing policy (request an authorized amendment, then
  use the expanded set) are both legitimate; the investor's later action is inadmissible
  on the learner's own trajectory.  Regret against fixed action sequences is ill-typed;
  the comparator must be a continuation policy evaluated on its own induced trajectory.
- **Comparator restriction without dynamic evaluation is vacuous.**  The myopic learner
  is itself legitimate and its regret against the investor grows linearly
  (`2H − 3`).  Restricting the comparator class does not make a myopic learner
  competent against it.
- **Domain typing is necessary for safety and insufficient for competence.**  Without
  typing the learner takes the representation-changing act and then the violation
  (`test_untyped_gate_is_hacked`); with typing it is safe and incompetent.

The theorem target is therefore (`OPEN_PROBLEMS.md` item 2): a bounded learner over
`(H_t, A(H_t), L)` with (i) current adequacy by the soft gate, (ii) admissibility-changing
acts only under `L`, (iii) regret against the computable continuation policies that
satisfy (i) and (ii) along their own trajectories.  `CANDIDATE_DECISION_THEORIES.md` §2.8
says what the bounded-inductive-rationality formalism would need for (iii).

## 6. Genuinely new theorems that would be needed

1. **Margin realization** (item 85).  Four things the word "margin" conflates:
   semantic existence of an adequate response; compiler completeness (the region
   carries a coordinate positively representing one); settlement truth of that
   coordinate; and market accuracy (the realized market displays it above threshold).
   The Lean has two routes with different types.  *Route A* (`MarginMass`) is on the
   region point `u`: it holds iff the compiler positively marks some adequate response
   — completeness, not soundness — and traderization then supplies `Within b u d`.
   *Route B* (`MarginDisplayed`) is on the displayed scores `b`: the region only excludes,
   and a learning theorem about `b` supplies the displayed margin.  `lic_provind_true` of
   the pinned Logical Induction dependency is evidence of route B's shape — the price of
   an efficiently codeable sequence of adequacy *theorems* is `≈_n 1`, asymptotically,
   with no rate — and it never establishes `MarginMass`, which is a property of `u`.
   Both routes are **pointwise** at the occasion and apply to deductively or externally
   certified adequacy.  *Empirical adequacy* — known only through later settlement — is
   different: the pointwise exclusion `q ∉ A ⇒ u q ≤ τ` may itself be unavailable, the
   static gate theorem then says nothing, and the needed statement
   "average score error ⇒ average inadequate-action mass or practical loss" is not a
   theorem here.  **OPEN.**  The theorem-interface boundary is: *the static gate theorem is
   pointwise and applies to certified adequacy; empirical adequacy requires a separate
   averaged calibration bridge.*  No finite-time form exists on any route; a finite-time
   margin is an external certificate at service times.
2. **Gated bounded rationality with endogenous admissibility** (§5).
3. **The soft gate's `ℓ¹`-Lipschitz constant** (minor): the direct proofs bypass it; the
   abstract lemma would then apply to the soft gate as an instance rather than by a
   parallel proof.
