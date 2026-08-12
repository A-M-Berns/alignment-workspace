# Brainstorm — angle "lateral-foundations" (Round 2)

*Agent: lateral-foundations brainstormer. Bias: the foundational/lateral items round 1 under-served —
the dependent-typed decision problem & "why ain'cha rich" (beyond re-skinning `value_of_CM`), Vingean
agency × abstraction as a finite value-of-information lemma, Christiano's reflective-probability
framework as an ALTERNATIVE setting, legitimacy non-transitivity / trust-laundering, and the
value/factual updateless asymmetry (Geometric UDT). Looking for SHARED CONSTRUCTIONS, not puns.*

Every claim flagged PROVED / SKETCHED / CONJECTURE / INTERPRETATION. All validation-modality tags are
honest: if the real content needs LI/asymptotic machinery, the item is **not** LEAN-CORE.

---

## Orientation: what is OFF-LIMITS (do not re-skin)

Confirmed already-established (read-only), which several round-1 threads duplicated:

- **`LeanDeference.lean`** — `value_of_CM` / `value_of_defects` / `decomposition` (finite δ=0 Value
  backbone); `value_asymptotic` (Value modulo the 5 LI theorems-as-hypotheses); `softmax_lower_bound`;
  `CM_implies_immodest` (the §5.2 *tail*, soft⇒hard step left as prose); the whole
  `DeferenceConverse` (Value ⟺ Total Trust on two-option witness menus, **incl. the AntiExpert
  Fin 2 non-vacuity frame** `π=(½,½)`, `P=⅕/⅘`, `TT=−¼`); `DeferenceFold` (ccee→cee collapse under
  expert-known weights); `DeferenceConverseAsymp`; `DeferenceTrader` (round-profit ≥ gap).
- **v2 §10** — the generalized expert reduction; §10.3(a) future-self = Blackwell-join of observable
  experts; §10.3(b) modest external expert must be infinite; §10.4 cross-agent LUV-Total-Trust is the
  open object D3.
- **Round-1 `lateral.md`** — `lateral-dtype.lean` (`WAR_of_argmax` = `value_of_CM` re-skin, δ=0);
  Vingean-as-quantified-Blackwell (SKETCHED, no Lean); "coarsen-then-trust" W4 (INTERPRETATION, no
  shared construction); germ-UDT sheaf (CONJECTURE, one paragraph).
- The CRITIQUE's named **skipped low-hanging fruit**: the finite "Aumann-fails-under-modesty" example
  (D9, never built), legitimacy non-transitivity / trust-laundering (D12, one table row), Christiano's
  framework (never engaged), the value/factual *asymmetry* (the interesting half conjectured).

So the round-2 lateral lane must produce things that are (a) NOT a `value_of_CM`/`CM_implies_immodest`
re-skin, (b) genuinely new vs. round-1's own INTERPRETATION-level bridges, and (c) routed to the
right tool.

---

## A discovery from adversarial probing (the most important thing I learned)

The round-1 ideate (`weak-endorsement-deference-ideate.md` Idea 3) asserted the Aumann-under-modesty
finite example is "**easy and LEAN-friendly** (a 3-world frame)." **I executed it and that claim is
wrong / over-sold.** Two findings (Python, `/tmp/aumann_*.py`):

1. Under **Geanakoplos's nested S4** (reflexive+transitive+*nested* — the hypothesis v2 §1.1 actually
   loads), requiring each agent to *know* its own posterior (posterior constant on its cells) pushes
   the nested chains back toward **agreement or triviality**. The naive "modest ⇒ agree to disagree"
   does *not* drop out of a generic nested frame.
2. Genuine persistent disagreement-at-common-knowledge needs **overlapping (non-nested) S4 cells**
   (negative-introspection fails but the cells genuinely overlap). I built a 4-world common-prior
   frame `E1={0:{0,1},1:{1},2:{2,3},3:{3}}`, `E2={0:{0},1:{0,1},2:{2},3:{2,3}}`, both reflexive+
   transitive, **neither a partition**, with self-evident (common-knowledge) events `{0,1},{2,3},W`.
   On the public event `C={0,1}`, agent-1's distinct cells `{0,1}` and `{1}` **overlap at world 1 and
   do NOT tile `C`** — so the averaging identity `π(A∣C) = the common known posterior q`, the literal
   step Aumann's proof uses, **fails with an explicit witness**: `π(A∣cell@1)=1`, `π(A∣cell@0)=½`,
   `π(A∣C)=½`, no single `q`.

This reframes D9 honestly. The *real*, non-vacuous, decidable, LEAN-CORE fact is **not** "modest
agents agree to disagree" (which under nesting is false/subtle) but **"the partition-tiling /
sure-thing averaging step that Aumann's agreement theorem relies on is exactly the step that fails for
non-partitional (modest/S4) information, witnessed by a finite overlapping-cell frame."** That is a
clean limitative theorem about *why* Aumann needs S5, it is finite/decidable, and the LI machinery
appears nowhere. Round 1 would have shipped the wrong (fake-easy) version; this is the corrected one.

---

## The candidate items

### C1 — Aumann's averaging step fails under modesty (LEAN-CORE)

**Claim (PROVED-target).** There is a finite common-prior frame and a self-evident (common-knowledge)
event `C` such that one agent's S4 (reflexive+transitive, non-partitional) possibility cells **cover
`C` but do not partition it** (two distinct cells overlap), and consequently the conditional-
expectation averaging identity that Aumann's proof invokes — "if the posterior of `A` is common
knowledge and equal to `q` on every cell tiling `C`, then `π(A∣C)=q`" — **fails**: there is `A` with
the per-cell posteriors not reconcilable to `π(A∣C)`. Conversely (the COMPILED near-miss) if the cells
*do* partition `C` (S5/immodest), the identity holds (`π(A∣C)` = the common posterior). The target
object — any LI theorem — is absent; this is finite rational arithmetic + a tiling/overlap predicate.

**Why this is not a `value_of_CM` re-skin.** `value_of_CM` and `CM_implies_immodest` are about the
*Value/martingale* decomposition and the fiber-indicator collapse. This is about the **knowledge-
operator / common-knowledge meet and the sure-thing averaging lemma** — a different finite object
(possibility correspondences, self-evident events), and it formalizes the *converse direction* of why
S5 is needed, which `CM_implies_immodest` (which only proves immodesty *from* a CM hypothesis) does
not touch.

**Pre-registered FAKE to avoid.** (i) Stating "agents disagree" as a hypothesis and concluding a
triviality. (ii) Encoding "common knowledge" via the *novice's* `π` in a way that makes the
disagreement an artifact of the chosen prior (the red-team warning in the round-1 ideate). (iii)
Shipping the naive nested-frame "3-world" version — I showed it is false/subtle, so a clean compile of
it would be checking the wrong claim. Faithfulness gate: the witness must be an *overlapping*
(genuinely non-partition) S4 frame, and the near-miss must show the identity *holds* under partition.

**Tractability: medium.** The arithmetic is `Fin 4` rationals; the work is encoding "self-evident
event," "cells tile C," and the averaging identity faithfully. Witness verified in Python
(`/tmp/aumann_real.py`, `/tmp/aumann_final.py`).

---

### C2 — Trust-laundering: Total Trust is not transitive, with a finite witness (EXEC)

**Claim (PROVED by witness search).** There exist three finite frames/priors `(π_H,P_A)`, `(π_A,P_B)`,
`(π_H,P_B)` such that `π_H` Total-Trusts `P_A` **and** `π_A` Total-Trusts `P_B` **but** `π_H` does NOT
Total-Trust `P_B` — using the *actual* DDB/LeanDeference Total-Trust inequality (the conditional-mass
form that `value_witness_iff_totalTrust_mass` certifies), searched exhaustively/randomly over small
integer test variables and rational thresholds. A delegated/laundered trust chain breaks. The recovery
condition (transitivity holds iff `B` is `H`-observable / weight-class-shared) is the v2 §10.3(a)
"future-self is the join" statement seen from the delegation side.

**Why new / not a re-skin.** `DeferenceConverse` proves Value ⟺ Total Trust *for one fixed pair*. It
says nothing about *composition* across three agents. Non-transitivity is a statement about the
**delegation closure** of the trust relation — a multi-agent safety property ("alignment is not closed
under delegation") with no analogue in LeanDeference, which is entirely two-party.

**Modality EXEC (not LEAN-CORE), honestly.** The clean *characterization* ("transitive iff
weight-class shared") is the LI cross-agent object D3 and is PROOF-ONLY. But the **negative existence**
("not transitive in general") is validated by searching the real inequality over actual finite frames
— that is EXEC done right (search the real objects, exhaustive over a decidable test family). Witness
already found (`/tmp/transit.py`): `H→B` fails at `X=1[world 2]`, `t=⅓`. A LEAN-CORE version of *one
specific* witness frame is possible as a bonus, but the *content* (it can fail for some chain) is an
existential best certified by search; pinning it in Lean adds little and risks a one-frame shadow.

**Pre-registered FAKE to avoid.** (i) Proving non-transitivity by *assuming* the weight-class mismatch
that causes it (laundering the obstruction into a hypothesis). (ii) A Lean file that hard-codes three
distributions and checks one inequality fails — that certifies "this specific tuple breaks," dressed
as "trust is not transitive," with the search (the real evidence) done off-stage. The EXEC search over
the test family is the faithful validation.

**Tractability: easy** (witness found in minutes; the recovery-condition characterization is hard and
explicitly PROOF-ONLY).

---

### C3 — The value/factual updateless asymmetry as a finite value-of-information SIGN FLIP (LEAN-CORE)

**Claim (PROVED-target).** Geometric-UDT's conjecture ("updateful about values, updateless about
facts") has a finite, decidable *core* distinct from the broken `node_value`-argmax wrapper the round-1
updateless thread shipped (which the CRITIQUE re-rated as a tautology). Model a two-coordinate world
`W = F × V` (a *factual* coordinate the agent should learn, a *value* coordinate it should not let the
environment move). An information structure `E` and a menu are **factual** if the abstraction
`α_fact : W → F` is Blackwell-monotone for the payoff (more info never hurts) and **value-laden** if
`α_val : W → V` is Blackwell-*anti*-monotone (more "info" of the manipulative kind lowers true value —
the wirehead pattern). The crisp Lean-able fact: **value-of-information is `≥ 0` along the factual
abstraction and can be `< 0` along the value abstraction in the *same* frame** — i.e. updating is
warranted on `α_fact` and *unwarranted* on `α_val`, and this is a *sign* statement provable by exact
finite arithmetic. This grounds "be updateful about facts, updateless about values" in
Blackwell/Geanakoplos rather than in a hand-chosen `node_value`.

**Why not a re-skin / not the round-1 broken relation.** The round-1 updateless relation was
`U(π_u)=max U` (argmax wrapper, CRITIQUE §3: blind to process). This instead is a **value-of-
information inequality with a sign that flips between two abstractions of the same world** — it never
mentions argmax-optimality, and it *derives* the asymmetry from the monotonicity structure rather than
supplying it by hand. It also is *not* `value_of_CM` (that is monotonicity of one payoff; this is the
*contrast* of two payoffs' VoI signs).

**Pre-registered FAKE to avoid.** (i) Hand-picking `node_value` so the sign comes out — exactly the
round-1 failure; the sign must come from the *frame's* refinement structure, not a free input. (ii)
Making `α_val` anti-monotone by *fiat* (declaring VoI negative) — the near-miss must show that for a
*partitional* refinement VoI is forced `≥ 0` on BOTH abstractions (Blackwell), so the negative sign
genuinely requires the non-partitional/menu-restricted structure. (iii) Smuggling "updateless" as a
hypothesis. Faithfulness gate: ship a COMPILED non-vacuity witness (a frame with strictly negative VoI
on `α_val`, strictly positive on `α_fact`) and the COMPILED partition near-miss (both `≥ 0`).

**Tractability: medium.** This is the finite value-of-information lemma the CRITIQUE says round 1
*should have* produced (it would also discharge orientation Q6 / Vingean-abstraction). The negative-VoI
witness needs a non-partitional experiment (cf. Weatherson's §2 tightness example, v2 §1.1) — small
but must be built and checked, not asserted.

---

### C4 — A finite value-of-information ≥ 0 lemma for the Vingean / intentional-stance abstraction (LEAN-CORE)

**Claim (PROVED-target).** The Part-2 "Vingean agency = quantified Blackwell dominance" thesis
(round-1 SKETCHED, no Lean) has a genuinely formalizable **finite kernel** that is NOT
`value_of_CM`: on a finite world set with a *reflexive-transitive-nested* experiment `E` (Geanakoplos
S4) and an abstraction `α : Act → Out`, the `α`-recommended strategy's expected `α`-value **dominates
every fixed action's `α`-value** — the value-of-information-≥0 inequality *restricted to the abstracted
payoff*. The non-vacuity witness: the same inequality is **FALSE if `E` is not transitive** (drop
positive-introspection) — a compiled near-miss exhibiting a non-transitive experiment where more
"information" lowers the recommended `α`-value. This is "predict the win, not the move; trust on the
general principle that information has nonnegative value for the coarse variable" made into a checkable
finite theorem with its tightness witness.

**Why distinct from `value_of_CM` and from C3.** `value_of_CM` proves Value from a *martingale defect =
0* hypothesis (the LI route). This proves the *value-of-information* form directly from the
**Geanakoplos reflexive-transitive-nested structure** (the DDB §1.1 route v2 explicitly says it
*skips*), and crucially ships the **near-miss certifying transitivity is load-bearing** — which neither
LeanDeference nor `lateral-dtype.lean` does. C3 contrasts *two* abstractions' VoI signs; C4 establishes
the *positive* VoI for *one* abstraction *and pins which S4 axiom it needs*. They share the Blackwell
backbone but prove different statements.

**Pre-registered FAKE to avoid.** (i) The `lateral-dtype` trap: stating "recommended dominates fixed"
with both the recommendation and the dominance as hypotheses (a relabeled `Finset.sum` monotonicity).
The hypothesis must be *only* the structural reflexive-transitive-nested predicate on `E`, and the
conclusion the inequality. (ii) Encoding `α` so the inequality is `x ≤ x`. (iii) Shipping only the
positive direction with no near-miss — then "transitivity ⇒ VoI≥0" looks like it might hold for *all*
`E`, and the result is non-falsifiable-shaped. The compiled non-transitive counterexample is mandatory.

**Tractability: medium-hard.** Formalizing reflexive/transitive/nested as predicates on `W → Finset W`
and the conditional-expectation recommendation is more than the existing files carry; the near-miss
(a non-transitive frame with VoI < 0) is the delicate part and must be searched first in Python.

---

### C5 — Christiano's reflective-probability framework as an ALTERNATIVE setting: the no-hard-certificate liar (PROOF-ONLY)

**Claim (SKETCHED).** AGENDA names Christiano's *Definability of Truth* / reflective-probability
framework as an alternative setting, and round 1 **never engaged it**. The lateral payoff: Christiano's
`P` is a *coherent reflective* probability with `P(⌜P(φ) ∈ (a,b)⌝) ≈` the truth of `P(φ) ∈ (a,b)` —
the **soft** reflection that LI's Self-Trust (4.12.4) also delivers, but obtained *statically* (a fixed
point of a reflection operator) rather than *dynamically* (a limit of a market). The claim worth
stating: **the deference picture is setting-robust** — the "no *hard* legitimacy certificate" result
(L5 in round 1; the liar `χ = "P_A(χ) < ½"` kills any in-advance certain trust) is **not** an artifact
of LI's market dynamics; it recurs in Christiano's static reflective `P` for the *same* diagonal
reason, and the *soft* certificate (`δ`-band reflection) survives in both. So "clean modest deference
needs an infinite self-referential frame" (v2 §5.2 / §10.3(b)) is **framework-independent**: Christiano's
reflective `P` is a *second* concrete infinite self-referential reasoner occupying v2's "impossible
corner," distinct from LI.

**Why PROOF-ONLY (honest tag).** The content is a cross-framework *correspondence* (LI Self-Trust ↔
Christiano reflective coherence) plus a diagonal-lemma argument that the hard certificate fails in
both. The objects — a coherent reflective probability over an arithmetic language, the Hamkins–Lawvere/
diagonal fixed point — are not finite/decidable and need real reflection machinery. Any Lean here would
be a finite shadow (e.g. a 2×2 "liar" matrix) that smuggles the reflection as a hypothesis — exactly
the banned move. The honest deliverable is a rigorous sketch + "**NOT Lean-tractable because the
reflective fixed point and the definability-of-truth obstruction are infinitary**."

**Pre-registered FAKE to avoid.** A `Fin 2` "liar" Lean file with `χ`-self-reference encoded as a real
number `x` satisfying `x = if x < ½ then …` and concluding "no certificate" — that certifies a fixed-
point arithmetic fact, not the truth-definability obstruction, and would be a shadow. Tag it PROOF-ONLY
and *do not* produce it.

**Tractability: medium** as a sketch (the diagonal argument is standard); genuinely **not** Lean.

---

### C6 — The dependent-typed decision problem & "why ain'cha rich": the genuinely new content is the FIXED-POINT existence obstruction, and it is PROOF-ONLY (PROOF-ONLY)

**Claim (SKETCHED).** Round 1 gave the Π-type `D : (s : State) → Act s` (PROVED-trivial) and re-skinned
`value_of_CM` as "WAR" (CRITIQUE §4: a second copy of an existing fact). The *genuinely* new lateral
content — which round 1 flagged but did not pursue — is: once `Act s` is allowed to **depend on the
agent's own belief/decision state** (the dependent index appears in its own fiber, as self-reference
requires; round-1 §3.1), "systematized winning / why-ain'cha-rich = a self-endorsing fixed point of `D`"
becomes an **existence question with a Gödel/Lawvere obstruction**: a decision procedure that is its own
control-endorsement fixed point on a *self-referential* `State` family need not exist (the same
diagonal that makes hard Self-Trust false). So "why ain'cha rich" has a **principled exception**: when
the optimum is a fixed point the family forbids, no procedure is rich, and that is *not* a defect of any
particular `D` — it dissolves "rich by whose measure?" from the *other* side (sometimes there is no
richest one, by diagonalization, not by yardstick-choice). This is the `value/factual` and `size-
problem` threads' shared root: **self-reference in the action family.**

**Why PROOF-ONLY.** The trivial Π-type fact is already shipped (off-limits). The new content is a
*non-existence-of-fixed-point* claim over a self-referential type family — a Lawvere/diagonal argument,
not finite arithmetic. A Lean formalization would either (a) prove a Π-type exists (trivial, already
done) or (b) need a genuine diagonal-lemma encoding (infinitary; any finite version is a shadow). Honest
tag: **NOT Lean-tractable; the load-bearing step is the diagonal non-existence.**

**Pre-registered FAKE to avoid.** Re-shipping `lateral-dtype.lean` / `WAR_of_argmax` (a `value_of_CM`
re-skin) and calling it "the dependent-type result." That is precisely the round-1 duplication. Also
avoid a Lean `Π`-existence lemma dressed as "decision procedures are well-typed" — true and empty.

**Tractability: medium** as a sketch; **not** Lean. Shares the diagonal root with C5.

---

### C7 — The two trust knobs (temperature δ, deferral horizon f) as a quantitative finite trade-off (LEAN-CORE, bounded)

**Claim (PROVED-target, modest scope).** Round-1 W2 conjectured a `(δ_n, f(n))` joint schedule for a
*quantitative* Vingean trust bound but produced no theorem. There is a **finite, non-asymptotic** core
that is honestly Lean-able and is NOT `softmax_lower_bound` alone: the softmax-selection Value gap at
temperature `δ` over a `k`-option menu, *with an explicit competence-gap margin* `m` between the
future-self's best and second-best estimate, satisfies a **two-sided** bound — the realized soft-
diagonal return is within `[m − k·δ, m]` of the argmax return — so the *product* structure "sharper
selection (small δ) recovers more of the competence gap m" is a finite inequality. The new content over
`softmax_lower_bound` (which gives the one-sided `≥ max − card·δ`) is the **margin-dependent two-sided
control** that exposes the `δ`-vs-`m` trade-off quantitatively, plus a **near-miss**: with `δ ≥ m/k`
the bound is vacuous (no trust recovered), certifying the trade-off is real.

**Why not just `softmax_lower_bound`.** That lemma is the lower bound only and has no margin parameter;
it cannot express "how much of the competence gap is recovered." The trade-off requires introducing the
margin `m` and bounding the *recovered fraction* — a different (and tighter, margin-aware) statement.

**Pre-registered FAKE to avoid.** (i) Re-deriving `softmax_lower_bound` with a renamed constant. (ii)
Stating the trade-off with `m` and `δ` as free reals and concluding an inequality that holds for all of
them (no margin structure) — the bound must *degrade to vacuous* at `δ ≥ m/k` and that near-miss must
compile. (iii) Importing any asymptotic `≂ₙ` content — this is purely finite/real.

**Tractability: medium.** Builds on the confirmed `softmax_lower_bound` proof technique
(`Real.add_one_le_exp`) but with a margin hypothesis; the two-sided/upper direction and the vacuity
near-miss are the new work. Honest caveat: this is the *finite per-round* gap only — it does **not**
touch the asymptotic schedule (CRITIQUE §2: the framework is asymptotic-average only); I bill it as a
per-round building block, not the asymptotic trust bound.

---

## Cross-connections that are SHARED CONSTRUCTIONS (not puns)

- **C3 ↔ C4 ↔ Vingean/legitimacy** share *one* construction: the **Blackwell value-of-information sign
  on an abstraction `α`**. C4 = VoI ≥ 0 on the coarse `α` (positive trust / intentional stance); C3 =
  VoI sign *flips* between `α_fact` (≥0) and `α_val` (<0) (the Geometric-UDT asymmetry); round-1 W1's
  "legitimacy = Blackwell-monotone abstraction; wireheading = anti-monotone" is the *same* sign object.
  This is a genuine shared finite construction, not the "coarsen-then-trust" pun (CRITIQUE §7) — it is
  a single inequality (`VoI_α ≷ 0`) instantiated at different `α`. **The whole legitimacy/Vingean/
  Geometric-UDT cluster is one finite value-of-information sign lemma at different abstractions.**

- **C5 ↔ C6 ↔ size-problem** share the **diagonal/Lawvere fixed-point obstruction**: the hard
  certificate (C5), the self-referential decision family (C6), and the round-1 size-problem (mutual
  hard trust = 2×2 liar) are the *same* non-existence-of-hard-fixed-point, in three settings
  (Christiano reflective `P`, dependent action family, two-inductor pair). All three are honestly
  PROOF-ONLY for the same reason: the obstruction is infinitary.

- **C2 ↔ v2 §10.3(a)**: trust-laundering non-transitivity and "future-self = Blackwell-join of
  observable experts" are *the same observability/weight-class condition* read forwards (recovery) and
  backwards (attack). Shared construction: the generability/weight-class horizon.

---

## Honest self-assessment (adversarial about my own ideas)

- **C1** is the corrected version of a round-1 fruit that was *advertised as easier than it is*. The
  value is partly in having *caught* the over-sell (the nested-vs-overlapping subtlety). Risk: the
  "Aumann fails under modesty" headline may be **already known** in the Geanakoplos / non-partitional
  literature (CRITIQUE §9 flags this) — but the *specific finite witness of the averaging-step failure*
  as a Lean object is new to this lab and is what discharges the CRITIQUE's "build it" demand. Net: real
  LEAN-CORE, must check prior art in the write-up.
- **C2** is the cleanest genuinely-new EXEC item (witness already found). Low risk.
- **C3, C4** are the finite value-of-information lemmas the CRITIQUE explicitly says round 1 *owed* and
  skipped. Highest payoff, medium risk (the negative-VoI witness must be built, not asserted — that is
  exactly where a shadow could creep in, so I pre-registered the partition near-miss).
- **C5, C6** I am tagging PROOF-ONLY *on purpose* — per the round-2 rules an honest "no Lean here" is a
  success and a fake `Fin 2` liar is a failure. I expect the faithfulness gate to *reward* the honest
  tag. Risk: these are sketches, not results; I bill them as such.
- **C7** is the most likely to collapse toward `softmax_lower_bound`; I kept it only because the
  margin-dependent two-sided bound + vacuity near-miss is a real delta. If on attempt it reduces to the
  existing lemma, it should be dropped, not dressed up.

**What I deliberately did NOT propose:** anything routing through `value_of_CM` / the merge discharge /
the cross-agent martingale as a *hypothesis* (banned); any "corrigibility sign-flip" variant (round-1
already has the pointwise-encoding version and the CRITIQUE showed it only buys weak preference); any
re-skin of the converse `value_iff_totalTrust`.
