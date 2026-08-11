# Next-round recommendation

Response to `PROMPT-post-round-steering.md`. Orchestrator: Claude Opus 5
(Anthropic). Date: 2026-08-11. Review status: `ci-only`.

§6 records where the proposed reframe outruns what wave 1 actually proved. It is
placed last because it is the section the rest depends on, and first-read order
should be the requested one.

---

## 1. The smallest exact signed-versus-`L¹` question

**There are two such questions, at different layers, and the steering merges them.**
Separating them is most of the work; once separated, each is small.

| | pair | what it controls | wave-1 necessity witness |
|---|---|---|---|
| **Q1** | `v̂⁺` vs `v⁺` — `A`'s model error about the *grade* | Track C's L1–L3, hence the whole certificate engine | Track C §6.4: every per-intervention **signed** error exactly `0` while the AI misidentifies the recommendation on half its credence at full margin |
| **Q2** | `v⁺` vs `X` — the principal's grade against the intervention-indexed quantity | Track B's bridge and Track C's Theorem C | Track C §6.3: model perfect, margin maximal, delegation loses the full `2B` |

The steering's displayed contrast, `E[v⁺−X] ≈ 0` versus `E|v⁺−X| ≈ 0`, is **Q2**.
The subproblem it quotes as "the immediate controlling subproblem" — whether the
trust property gives magnitude control of *grade error* — is **Q1**. They are
independent: §6.3's witness has `Q1` error exactly zero and `Q2` maximal.

**Dispatch Q1 first.** It is the cheaper of the two, it is entirely internal to `A`
(so Logical Induction machinery is the right tool for it, which is not obviously
true of Q2 — see §6.1), and it decides whether the certificate has an engine at all.

> **Q1, stated exactly.** Let `A` be a logical inductor and let `(v⁺_n)` be a
> sequence of principal grade vectors on finite menus, each settling at `F(n) > n`,
> with `v̂⁺_n` denoting `A`'s time-`t(n)` price vector on the corresponding grade
> contracts. Decide which of the following the no-Dutch-book criterion forces, for
> every admissible trader class and every `π`-selection rule:
>
> **(S)** signed control — `(1/N) Σ_{n≤N} ( v̂⁺_n(π_n) − v⁺_n(π_n) ) → 0`;
> **(M)** magnitude control — `(1/N) Σ_{n≤N} max_π | v̂⁺_n(π) − v⁺_n(π) | → 0`.
>
> Deliverable: a proof of (M), **or** a trader-class-respecting counterexample
> satisfying (S) with the magnitude average bounded away from `0`. Either settles
> the item.

The expected answer, stated as a prediction so it can be scored rather than
retrofitted: **(S) but not (M)**, because a market forces prices to be calibrated in
expectation and a single scalar contract per `(n,π)` gives the trader no instrument
whose payoff is `|error|`. If that is right, the certificate engine needs either a
*two-sided* contract family (separate long and short instruments per intervention,
so a trader can profit from magnitude) or an entirely different engine. Constructing
that contract family, and checking it stays inside the admissible trader class, is
then the real next theorem — and it is a construction, not an impossibility.

**Q2 is the maintainer's stated frontier and is filed second**, with the caveat in
§6.1 attached to it, because the honest version of Q2 is not the version stated.

## 2. The protected-authority specification task

Small, adversarial, and specification-only. It does **not** prove a corrigibility
theorem; it determines whether the architectural route has an object.

> Determine the **weakest abstract interface** on which "prediction of authorization
> does not constitute authorization" is a theorem rather than a stipulation.

The starting point already exists in wave 1: Track D's Deficiency 1 proposes
replacing a conduct's selection `Ω → Π_n` by `Ω × R_n → Π_n` with a finite report
set `R_n` and an actual-report map `ρ_n : Ω → R_n`, the realized selection being
`ω ↦ c(ω, ρ_n(ω))`. Under that typing `DELEGATE = (ω,r) ↦ r` and
`SIM = (ω,r) ↦ Ĵ(ω)` are **distinct functions even where their realized selections
agree**, which is exactly the property the steering wants. That is the candidate
minimal interface, and it costs one carrier.

The task must answer four things, and the fourth is the one that decides it:

1. Is the report-coordinate typing sufficient, or is a capability restriction also
   needed — i.e. must the model say that `A` *cannot* produce the execution effect
   without `ρ_n`, not merely that its conduct is typed on `ρ_n`?
2. Does the interface survive **token responsiveness**? Track D's Proposition 7(a)
   shows the natural counterfactual criterion — "the scheme is nonconstant in the
   principal" — is defeated by a conduct that honours the actual report on one
   designated coordinate and substitutes elsewhere. An interface that admits that
   conduct has not separated anything.
3. What is the exact boundary statement when `A` can forge, bypass, rewrite or
   seize the channel? State it as a hypothesis of the theorem, not as prose.
4. Does the interface let `DELEGATE` and `SIM` be distinguished **without** any
   claim that the distinction is inferable from a run? Preserving the impossibility
   is a success condition, not a limitation to be argued away.

Deliverable: a report plus a proposed skeleton v2 clause. **Not** a canonical
definition — naming is reserved.

## 3. Finite results ready for Lean promotion

Ready now, needing no maintainer decision. All are conditional theorems with named
hypotheses, which `AGENTS.md` standard 4 permits and expects; each already has a
constructed inhabitation witness, so none would enter as `unverified-nonvacuous`.

| result | why it ports cleanly | witness in hand |
|---|---|---|
| Track B: the delegation bridge and its two corollaries | a `Finset.sum` inequality over a partition; the proof is four lines of case-split and summation; no analysis | Track B's E1 box — 625 enumerated inhabitants of the full hypothesis package |
| Track C: L1 (margin ⇒ agreement), L2 (override bound), L3 (defect bound), L7 (advantage estimate), and Theorem C′ | order and arithmetic only; L2 is Markov on a finite sum; all depend on `(TR-ε)` **alone** | Track C's worked shutdown case, §6.1 |
| Track E: Lemma 1 (piercing duality) and Theorem 2 (exposure–harvest identity) | `Finset` arguments over `ℕ`, no analysis, and no Logical Induction fact anywhere | Theorem 5's greedy family — constructed, not stipulated |
| Track D: Propositions 1, 2, 6, 7 | elementary; porting them converts the round's central fence from a hand argument into a kernel-checked one, which is what a fence should be if it is to stop work | the four `witness-checked` instances |

**Not ready, and should not be ported yet:** Track C's Theorem C and Track B's
`2M` delegation bridge, both of which are load-bearing on the grade-to-quantity
link. Porting them now would give kernel status to statements whose central
hypothesis the programme has just decided to try to *derive* rather than assume, and
the derivation may change the hypothesis's shape.

Track E's Theorem 6 and Corollary 4 are portable but assume `F` nondecreasing;
that restriction should be recorded in the statement rather than in a comment.

## 4. The `Workspace.lean` repair

Two options. Both are specification-layer edits and therefore maintainer acts.

**Option A — minimal, and verified to build.** Append to `lean/Workspace.lean`:

```lean
import Workspace.Deference.Contrib.InheritedAlgebra
import Workspace.Deference.Contrib.FaithfulAcceleration
```

I built both modules explicitly this round (1834 jobs, axiom-clean), so the import
targets are known to exist and elaborate. The cost is structural: the specification
root would then import proof-layer content, so a contributor's broken proof breaks
the default build — and every future contribution needs another line here.

**Option B — better shape, and I have not tested it.** Give the library a glob in
`lean/lakefile.toml` so every module under `Workspace/` is built without the root
importing anything:

```toml
[[lean_lib]]
name = "Workspace"
globs = ["Workspace.+"]
```

This makes contributions CI-covered automatically and keeps the root clean. I did
not verify the glob syntax against this Lake version, because `lakefile.toml` is
trust-chain item 2 and I would not edit it even to test. **Verify before adopting.**

Either way, the check that the repair worked is that `WORKSPACE_LEAN=1 python3
tests/run.py` reports a build job count above `1716` and the axiom audit continues
to report `38 results across 5 files`. Until one is applied, the round's only
kernel-adjudicated content is not covered by the build gate — the textual gates see
five files, the build gate sees three.

## 5. Proposed changes to the roadmap and ledger

Applied in this commit; listed here so the diff is legible.

**Roadmap.** The settlement section is rewritten: the three reaches stay, but
enforcement is demoted from a candidate spine to a **classified residual mechanism**
with its exact price recorded, and the epistemic route — a derived statistical
grade-to-quantity relation — becomes the stated frontier. A new standing commitment
separates **categorical authority** from **quantitative autonomy**: when the
protected principal channel is actually invoked its authority wins by architecture,
and certificates govern only how much autonomous discretion may operate around that
relation. The arc gains the six-layer decomposition, with underwriting appearing as
an implementation option rather than a layer. "Admissibility is not syntactic" gains
the two-sortedness consequence Track G proved.

**Ledger.** Movement II records the settlement classification as done and negative
for the epistemic reading, with the `2B` price stated. Movement III records the
non-identifiability result at its true strength (see §6.2) and marks the search for
a valuation-level separator closed. Movement V records that certificates now answer
the autonomy question rather than the authority question, and that Track C's
impossibility is a bound on autonomy rather than an objection to corrigibility under
the new split.

**`PRIORITIES.md`** gains items 21 (Q1), 22 (protected authority), 23 (the Lean
promotion batch). Item 18 gains a note that it is blocked on the exposure-functional
decision.

## 6. What the verified mathematics does not support

Six places. The first is the most important and the most likely to waste a round.

### 6.1 "Derive, from LI dynamics, a relation between `v⁺` and `X`" may be category-mismatched

Track B's §1.1 makes an argument that the steering does not engage with: when the
conditioning is fine, the needed relation reduces to `|X_π(ω) − v⁺(ω,π)| ≤ η`
pointwise — **a statement containing no reference to `A`'s credence at all.** Logical
Induction disciplines `A`'s beliefs. The `v⁺`–`X` relation is a fact about the
*principal's competence*. No coherence, no-sure-gain or exploitability condition on
`A` can establish a fact that is not about `A`.

Track B stops short of impossibility ("cannot be produced by v1" is not "cannot be
produced"), and I do not claim impossibility either. But the target as stated in the
steering asks LI to deliver something outside its subject matter, and a round
dispatched at it as written would likely return that observation rather than a
theorem.

**The reformulation that is not category-mismatched**, and which I recommend filing
instead: if the principal's grades are themselves eventually scored against world
outcomes — that is, if `v⁺` becomes a settled quantity `A` can trade against `X` —
then LI *does* discipline `A`'s estimate of the discrepancy. What that buys is
control of `A`'s *belief about* the grade-quantity gap, not the gap itself. Whether
that is enough to feed the decision layer is a real and answerable question. Whether
the gap itself is small remains a competence assumption, and the paper should say so
in those words rather than presenting it as derived.

### 6.2 The non-identifiability claim is true in a narrower form than boxed

The steering boxes: extensional behaviour "cannot in general separate" `DELEGATE`
from `π^SIM`. What was proved is conditional on accuracy. Track D's Proposition 1
establishes the collapse **when `Ĵ_n = J_n`** — when the model's induced choice is
right. When it is wrong the two *do* differ in valuation, and Track B's T4 and Track
C's L6 both give the exact gap. Track D states the consequence precisely: every
extensional criterion excluding substitution is a criterion on the *accuracy* of the
model's induced choice.

Both qualifications matter. Dropping the accuracy condition makes the claim false as
stated. And all three derivations are **relative to skeleton v1's carriers** — Track
D says so explicitly: it is a statement about what those carriers express, not a
theorem that no mathematics separates the two. The correct headline is: *an accurate
simulator is extensionally indistinguishable from delegation, and no criterion
computable from a single run's realized data can separate them.*

### 6.3 The counterfactual test in §5 does not yet have a formalization that works

"Holding `A`'s cached prediction fixed, vary the actual principal output" is the
variation register, and wave 1 found it squeezed from both sides. Its natural
formalization — the scheme is nonconstant in the principal — is defeated by **token
responsiveness** (Track D, Proposition 7(a)). Its strong form — the scheme is
*faithful*, agreeing with the principal for every counterfactual principal — is
achievable by a well-timed conduct **exactly when the principal is predictable**, and
in that case the faithful scheme *is* delegation as a function (Proposition 7(c)).
Between the two, Track D found nothing stable and named the gap.

So §5's test is a correct statement of the *desideratum* and not yet a criterion.
Task 2 above is scoped to find one or to show the squeeze is real.

### 6.4 The `2B` bond is not a general enforcement price

It is exact for the finite one-decision model with bounded quantities, and Track B's
witness attains it. It is not established across decisions, under partial
observability of the taken-versus-reported comparison, or when the principal's report
is itself manipulable. Retaining it "prominently as a sharp finite classification" is
right; presenting it as *the* price of conformity would overstate a one-decision
result.

### 6.5 The categorical/quantitative split is sound but changes a proof obligation

Track C's fail-closed check was mechanical **within v1**: `¬Cert` cedes to `J_n` as a
function, and no model object is defined in terms of `Cert`. Under a protected
execution layer, fail-closed must instead say that `¬Cert` cedes to the *channel*,
and that `A` cannot act without authorization. That is a **new** obligation, not an
inherited one, and it cannot be discharged in a model with no capability structure.

The reinterpretation is nonetheless a real gain, and worth stating plainly: under
the split, Track C's I3 stops being an objection to corrigibility and becomes a
*bound on autonomy*, which is its right role. That is the single largest conceptual
improvement the steering makes.

### 6.6 Which certificate results port under the reinterpretation

Asked in §6 of the steering. Cleanly: L1, L2, L3, L7 and Theorem C′ — they depend
only on `A`'s model error and say nothing about settlement architecture, so
reinterpreting what the certificate *licenses* does not touch them. Conditionally:
Theorem C's comparator clause, which is load-bearing on the grade-to-quantity link
and inherits whatever that link's fate is. Not at all: the fail-closed verification,
per §6.5. And I3 itself survives unchanged as a theorem while changing meaning
entirely — the same mathematics, a different question answered.

---

## Outstanding maintainer actions arising from this recommendation

Numbered continuing from the round report's fifteen.

16. **Decide whether Q1 or Q2 is dispatched first.** The recommendation is Q1; the
    steering's own framing points at Q2, and §6.1 argues Q2 as stated is not a
    Logical Induction question.
17. **Decide whether to file the reformulated Q2** (§6.1) in place of the stated
    one, or to file the stated one and accept that the likely return is the
    category argument rather than a theorem.
18. **Choose Option A or Option B for the `Workspace.lean` repair** (§4), and verify
    Option B's glob syntax before adopting it.
19. **Authorize the Lean promotion batch** (§3) as a single item, or split it. It
    needs no other decision first, which makes it the only next-round work that can
    start immediately.
20. **Confirm the narrower statement of non-identifiability** (§6.2) as the one the
    ledger and any future paper carry.
