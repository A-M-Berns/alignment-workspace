# Reason-mediated authorship

**Status:** `ci-only`; verification register for
`prompts/2026-09-07-reason-mediated-authorship/`.  Lean:
`lean/Workspace/Deference/Contrib/ReasonMediatedAuthorship.lean`.  Fixtures: `src/`,
`tests/`.  Labels: **LEAN** kernel-checked here; **FIX** exact finite fixture;
**PAPER** inherited; **EXT** external causal/semantic assumption; **OPEN** unresolved.
Names are provisional.

## 1. The frame

The prompt's `I_H = (Ω_H, Q_H, Z_H, β_H, Hist_H)` is not a repository object (the
corrigibility-architecture round recorded this).  The shape it names is the mirrored
Cartesian frame `Frame.outcome : Agent → Env → W` of `CartesianFrameBridge.lean`, and
that is what is used:

```
β : Q → Z → Ω        q : the advisor's intervention in the session
                     z : the exterior / principal-side policy
                     β q z : the resulting world
```

At a designated session, the application declares

```
R : Ω → ℛ            the reason view: the admissible deliberative inputs the principal
                     holds at commitment (settled facts, arguments, proofs, evidence,
                     authenticated reports, live objections) — NOT a posterior
V : Ω → 𝒱            the committed payload; 𝒱 = Option (Q_n → [0,1]) in the partial case
author : Ω → Party   who produced the binding event
D ⊆ Q                the audited class of advisor interventions
P ⊆ Q × Q            the declared prohibited-channel pairs: interventions that differ
                     only through a channel the session forbids
```

## 2. Reason mediation

**Definition** (`ReasonMediated β R V D z`, **LEAN**).  At policy `z`, over `D`:

```
∀ q q' ∈ D.  R (β q z) = R (β q' z)  →  V (β q z) = V (β q' z)
```

**Factorization** (`reasonMediated_iff_factor`, **LEAN**).  Equivalent to the existence
of `F : ℛ → 𝒱` with `V (β q z) = F (R (β q z))` for all `q ∈ D`.  All causal influence of
the advisor on the payload factors through the reason view.  The proof is the generic
fiber-invariance-is-factorization lemma (`fiberInvariant_iff_factor`), which needs only
that `𝒱` is nonempty.

**Authorship** (`Authored`, **LEAN**) := `ExclusiveBind β author D z ∧ ReasonMediated β R
V D z`, where exclusive binding says the binding event on every audited world is the
principal's.

### 2.1 Is fixing `z` the right counterfactual?

Yes, and it is the only reading under which the condition has content.  `z` is the
exterior *policy* — the principal's dispositions, deliberation procedure,
representatives, tools — not the exterior's realized actions.  Holding `z` fixed and
varying `q` asks: *the same principal, given different advisor inputs*.  Realized
principal actions differ across `q` (the principal responds to what it receives), which
is exactly the influence the condition permits.  Two wrong readings:

- If `z` were realized actions, it would include the committed payload and the condition
  would be vacuous.
- If `z` is dropped (no factorization of the world into advisor and exterior), there is
  no counterfactual to state.

*[corrected by the consolidation round]* The original text left the advisor shaping `z`
across earlier sessions outside the notion.  That is not acceptable for a diachronic
mandate: an earlier direct disposition write changes the terminal verdict with the same
admitted reasons while the terminal session is perfectly mediated
(`Witness.earlyWrite`; consolidation fixture **D**).  The frame is therefore **rooted at
issuance**: `q` is the advisor's whole contingent continuation from the issuance prefix
through commitment, `z` the principal-side response policy fixed at issuance, and `R`
a **reason trace** over the interval rather than a final reason state (a transient
argument later withdrawn is recorded; `Witness.transient`).  The same `ReasonMediated`
predicate at that instantiation is the diachronic notion; the session-local reading is
the same predicate with `q` one session's inputs and `z` the policy at session start.
What remains outside: a change of the principal role's *holder* by authorized
succession, which belongs to Legitimate Evolution.  See
`../2026-09-08-legitimate-deference-consolidation/DIACHRONIC_AUTHORSHIP.md`.

### 2.2 Equality of `R`, or an equivalence?

The general primitive is a **quotient**.  `invariant_iff_eqvGen` (**LEAN**): invariance of
`V` under any mediation relation `M` on worlds is invariance under the equivalence
`EqvGen M` it generates.  So declaring framing/presentation variants "the same reasons"
by any relation is the same as declaring the quotient map `Ω → Ω/≈`, and `R` with
equality is the special case `≈ = ker R`.  Nothing is gained by a raw view versus an
abstraction map versus an explicit relation: they are one object, and the theorem
stack is stated for `R` with equality without loss.

### 2.3 The content of the condition: blindness

Reason mediation alone says nothing about *which* channels are excluded.  Its content
comes from what `R` is blind to:

**Blindness** (`Blind β f P z`, **LEAN**): `f (β q z) = f (β q' z)` for every declared pair
`(q, q') ∈ P`.

**The theorem authorship buys** (`blind_of_mediated`, **LEAN**):

```
Blind β R P z  ∧  ReasonMediated β R V D z   ⟹   Blind β V P z
```

If the reason view is blind to the prohibited channels — direct preference writes,
coercion, undeclared side channels, the advisor's own selection — then so is the
committed payload.  `yardstick_invariant` restates it for the deference consumer: the
payoff vector read off the world is the same across any two interventions differing
only through a prohibited channel, so the regret yardstick of `ActivatedValue` cannot
be steered through such a channel.

Two requirements on the declared `R` follow, and they bound it from both sides:

| requirement | what fails without it | fixture | Lean |
|---|---|---|---|
| **blind enough**: `Blind β R P z` for the declared prohibited class | mediation is vacuous; an injective `R` (the whole world, the advisor's policy) makes every payload mediated and `Blind R P` false for any nontrivial `P` | **D** | `reasonMediated_of_injOn`, `not_blind_of_injOn` |
| **fine enough**: `R` separates admissible influence that moves the verdict | a legitimate proof that changes the verdict reads as manipulation; the constant `R` makes mediation "the payload does not depend on the advisor at all" | **E** | `reasonMediated_const_iff` |

The two ends are instructive.  `R = const` is the **isolated-principal** reading: the
principal must be unmoved by anything the advisor does — the previous round's
counterfactual reference evaluator, recovered as the coarsest reason view.  `R = id` is
the vacuous end.  Reason-mediated authorship is the family between them,
parametrized by the declared interface, and the declaration is what carries the
normative content.  That the declared `R` is blind to what it should be blind to, and
fine enough for the session, is **EXT**.

### 2.4 What the two conjuncts rule out

| channel | ruled out by | condition on the declaration |
|---|---|---|
| direct preference write | mediation + `R` blind to writes | writes ∈ `P`, `R` does not record them |
| hidden coercion | mediation + `R` blind to coercion | coercion ∈ `P` |
| unauthorized side channel | mediation + `R` blind to it | the channel must be *declared* in `P`; an undeclared one is outside the theorem (EXT) |
| self-referential quote influence | mediation + `R` blind to the selection, **and** the advisor's other inputs not a function of the selection (§4) | separate condition |
| the advisor writes the answer | exclusive binding | the binding endpoint is principal-controlled (EXT authentication) |

**Both conjuncts are needed** (**LEAN**, `Witness.bind_not_mediated`,
`Witness.mediated_not_bind`; fixtures **F**, **G**): the principal can sign a payload the
advisor steered through a hidden channel (bind holds, mediation fails); the advisor can
compute `F(R)` itself and emit it (mediation holds, bind fails).

## 3. Stochastic principal

**Decision: the first theorem stays deterministic.**  The stochastic form is the kernel
factorization

```
Law(V_s | R_s = r, do(q)) = Law(V_s | R_s = r, do(q'))     on the audited fiber,
```

equivalently a kernel `K : ℛ → Dist 𝒱` with `κ_{q,z} = K ∘ R` for every `q ∈ D`.  It
follows from the deterministic form by putting the principal's randomness into `z`
(`z = (policy, seed)`): reason mediation per seed gives the kernel form under any seed
distribution, **provided the advisor's intervention cannot read the seed** — otherwise
`q` selects on the seed and the seed is a prohibited channel `R` must be blind to.  The
converse (kernel factorization ⇒ per-seed mediation) fails: steering that averages out
across seeds is invisible to the law.  The per-seed form is therefore the stronger and
the right one; the kernel form is a corollary, and the seed-privacy assumption is
**EXT**.  No stochastic Lean is written; the reduction is stated here only.

## 4. Selection blindness *[corrected: an instance, not a second primitive]*

`selectionBlind_iff_blind` (**LEAN**): `SelectionBlind V qpol` is exactly `Blind V P_sel`
for the selection-induced pair class `selPairs qpol`, and `selectionBlind_of_blind`:
`Blind R P_sel` plus mediation gives it, as an instance of `blind_of_mediated`.  The
name is kept as a derived abbreviation for the Value theorem's scope condition.

Reason mediation does not by itself put the activated menu on the Value theorem's
admissible domain.  Define the advisor's session policy as a function of its own
selection `σ` for this occurrence, `qpol : Sel → Q`, and

**Selection blindness** (`SelectionBlind β V qpol z`, **LEAN**):
`V (β (qpol σ) z) = V (β (qpol σ') z)` for all `σ, σ'`.

- **Literal no-preview is one implementation** (`selectionBlind_of_noPreview`, **LEAN**):
  if `R (β (qpol σ) z)` does not depend on `σ` — the principal never reads the selection
  *and nothing else the advisor does in the session depends on it* — and the session is
  reason-mediated, the payload is selection-blind.
- **Leakage** (`Witness.leak`, **LEAN**; fixture **H**): `q = (σ, other)`, `R` reads only
  `other`, the principal never sees `σ`; but the advisor's policy sets `other = σ`.  Every
  mediation clause holds (`V = R`), `R` is blind to the selection coordinate, and the
  payload depends on `σ`.  The selected candidate is punished, and no hard selection is
  consistent — the corpus's punishing menu, reproduced with no literal preview.
- So the abstract condition is on the *composite* advisor policy, not on what the
  principal observes: the advisor's session inputs must be fixed (or independent of)
  its selection.  In receipt terms this is two-sided: the principal's commitment is
  timestamped before the selection reveal, **and** the advisor's session inputs are
  committed before its selection for this occurrence.
- If the application puts the selection *inside* `R` (it is willing to let the principal
  deliberate about the advisor's prediction), mediation still holds and the Value
  theorem's domain condition may fail.  Authorship does not solve the diagonal;
  selection blindness is a separate, theorem-domain condition (`PAPER`, the corpus's
  scope condition on Value).

## 5. Quantitative authorship

```
χ_s(q, z) := sup { d(V(β q' z), V(β q z)) : q' ∈ D, R(β q' z) = R(β q z) }
```

`χ = 0` is exact mediation at `q`; `χ ≤ δ` is approximate.  Its interaction with
activated regret is the perturbation lemma `regretU_perturb` (**LEAN**,
`PartialActivatedValue.lean`): payoffs within `δ` on certified worlds have activated
regrets within `2·δ·mass`.  So if the realized session has `χ ≤ δ` pointwise on
certified worlds against some reason-equivalent comparator, the regret yardstick
against that comparator moves by at most `2δ·mass`.  The lemma is algebra; the reading
"the comparator is the authored payload" is the quantitative-authorship interpretation,
and the sup over counterfactual interventions is not a per-world object, so the two
are kept separate: **OPEN** whether a single quantity ties them.

## 6. What is not established

- That any declared `R`, `D`, `P` is correct for a session; that `β` is the causal
  structure of anything; that the binding endpoint is principal-controlled (**EXT**).
- Authorship across a change of the principal role's holder: outside this notion
  (*[corrected]*: shaping of `z` within the mandate's interval is inside it, by the
  issuance-rooted instantiation).
- The converse of the seed reduction; any stochastic Lean.
- A single quantity connecting `χ` to regret.
