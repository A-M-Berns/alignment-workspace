# Round-2 CRITIQUE — Harsh referee, pre-report

*Stance: the faithfulness gate already did the per-file hypothesis-inertness/laundering work and I
mostly endorse it (I re-read every Lean file, every work writeup, every verdict, the trust-laundering
Python, and v2 §1.1). My job is the **next layer**: which "REAL" verdicts are over-generous as
research content, which results are consolidation rather than new, residual shadow/vacuity the gate
under-weighted, spec-drift, and the single thing the principal must not believe. Severity tags:
**[BLOCKER]** principal might act on it and it is unearned · **[MAJOR]** real gap the writeups
under-weight · **[MINOR]** labelling.*

Net scoreboard going in: gate says 4 REAL (`aumann-modesty`, `negative-voi`, `averaging-hides-spikes`,
`edt-node-value`) + 1 SHADOW (`trust-laundering`). I do not overturn any verdict. But two of the four
REALs carry a research over-claim the report would inherit, one near-miss is weaker than its billing,
and the SHADOW is being quietly treated as a moral win. Details below.

---

## 0. The single thing the principal should NOT believe without more work

> **"The lab produced four kernel-checked results about deference/trust between agents."**

It produced four kernel-checked **finite single-frame facts**, of which **exactly one is even a
two-party object** (`trust-laundering`, and that one is the SHADOW). Concretely:

- `aumann-modesty` — **single agent**, one information correspondence, one prior. Not two agents, no
  communication, no disagreement-between-parties. (The slogan "the AI disagrees with me even after we
  share credences" is INTERPRETATION pasted onto a one-agent posterior-averaging fact.)
- `negative-voi` — **single decision-maker** choosing from a menu under one of two information
  structures. No trust, no second agent.
- `averaging-hides-spikes` — pure real-analysis (a spike sequence; avg→0, sup↛0). Zero agents. The
  trader/budget reading is explicitly INTERPRETATION.
- `edt-node-value` — **single agent's** self-prediction kernel κ; UDT/EDT, not human↔AI trust.

So the honest headline is: **the lab kernel-checked four finite facts about
information/decision/averaging structure that BEAR on trust by interpretation; it did not check a
single cross-agent trust claim, and its one genuine cross-agent search is a shadow.** This is the same
boundary round-1's CRITIQUE §4/§10 flagged ("no LI/asymptotic/cross-agent statement is machine-checked
anywhere") — round 2 did not cross it, and should not be read as having crossed it. That is fine and
expected (the OFF-LIMITS list and PROOF-ONLY routing forced it) — but the report must say it in the
first sentence, not bury it.

---

## 1. [MAJOR] `aumann-modesty` (REAL — correct verdict) is over-titled: it is a one-agent averaging fact, not "Aumann's agreement step."

The gate verdict is right that the Lean is faithful, non-vacuous, and `hdisj` is load-bearing (I
re-read the proof: `hdisj` is used at the numerator AND denominator `sum_add_distrib` splits, lines
204–205/221–222 — delete it and the by_cases collapses, exactly as the attack found). **I do not
contest REAL.** But three over-reads would migrate into the report:

- **(a) "Aumann's agreement" is the wrong name for a single-agent object.** Aumann's theorem and its
  averaging step are about **two agents with a common prior** reaching a **common-knowledge posterior**
  and being forced to agree. This file has **one** correspondence `E`. What is actually shown is:
  *one agent's two overlapping non-partitional cells that cover a self-evident event carry different
  conditional expectations of X, so the law-of-total-probability/tower identity over a cover fails when
  the cover is not a partition.* That is **the tower property failing on a non-partition** — a true and
  clean fact, and the genuine load-bearing *step* inside Aumann — but calling the headline "Aumann's
  averaging step fails under modesty" lets a reader hear "two rational agents fail to agree," which is
  **not** what is built. *Honest restatement:* "**The tower/averaging identity `E[X|C] = q` fails for a
  single modest (non-partitional, S4) agent whose self-evident event `C` is covered by overlapping
  cells with distinct posteriors; partitionality restores it.** This is the averaging *step* Aumann's
  agreement theorem relies on, exhibited in isolation; it is not the two-agent agreement theorem."

- **(b) The `C = whole space` caveat is bigger than "a simplicity choice."** The gate disclosed it
  (verdict §8) but kept it cosmetic. With `C := fun _ => true`, `C_self_evident`,
  `C_is_knowledge_fixed_point`, and `C_is_union_of_cells` are **trivially true in any S4 frame** — the
  whole space is always common knowledge. So the file's "C is genuine common knowledge, not a free
  label" defense is technically true but **vacuously instantiated**: the discriminating power of the
  `knows` operator is never exercised on `C` itself (only on a throwaway `{0}` in attack2, which did
  not reach a kernel exit during the gate — verdict's own "not independently kernel-confirmed"
  admission). The cover `E0 ∪ E3 = C` is then just "`E0 ∪ E3 = everything`," which is far less
  surprising than "two overlapping cells exactly tile a *proper* self-evident sub-event." *This does
  not break REAL* (the overlap, the distinct posteriors, the averaging failure are all genuine), but
  the report must not advertise "self-evident common-knowledge event" as if a non-trivial fixed point
  were exhibited. *Honest restatement:* "C is the whole space; the self-evidence checks are true but
  trivial; a proper self-evident sub-event is left to future work."

- **(c) The modesty≡non-partition tie is INTERPRETATION (correctly flagged) AND the phenomenon is
  classical (Geanakoplos, correctly cited).** So the *novel* content is precisely: the kernel-checked
  instance + partitional near-miss + the 355-frame exhaustive boundary. That is a real and worthwhile
  lab artifact — but it is an **illustration**, not a theorem about logical inductors or about
  human↔AI disagreement. Keep the WHY modest.

**Net:** REAL stands; demote the title from "Aumann's agreement step" to "the averaging/tower step,
single-agent," disclose the whole-space triviality of the self-evidence checks inline, and bill the
contribution as an instantiation of a classical fact.

---

## 2. [MAJOR] `negative-voi` (REAL — correct verdict, on-spec) — but the mandatory near-miss is an EQUALITY, and "negative value of information" should be stated precisely.

I checked spec faithfulness against the source: v2 line 244 (the line the TODO cites as "241") asks for
Weatherson tightness #1 — "a 3-world example where **both** experiments are reflexive-transitive-nested
(with E₂ non-partitional) and the *less* informative one has higher expected return." The build
delivers **exactly that**: E1 finer, E2 coarser & non-partitional, `E1_refines_E2`, `Value E1 = 4/9 <
5/9 = Value E2`, `recOpt` is the genuine data-driven argmax-of-own-posterior (the attack's adversarial
menus flip it, A1/A2 — this defeats the "hand-tuned constant" shadow decisively). **This is the
cleanest, most on-spec deliverable in the run. REAL is correct and I add no doubt to it.**

Two precision points the report must carry:

- **(a) The mandatory near-miss `near_miss_partitional : Value Q ≤ Value E1` is `4/9 ≤ 4/9` — an
  equality, proved by `rw` with no `norm_num` strict step.** The TODO's near-miss asked the partitional
  anchor to give `Value E1 ≥ Value Q` (✓, non-strictly) and to "flip the inequality back." It does not
  *flip* anything to a strict win for the refined expert; it merely fails to be strictly negative. The
  strict separation that actually "tracks partitionality" is carried by the **separate**
  `partitional_anchor_strictly_dominated : Value Q < Value E2` (4/9 < 5/9) and by the attack's
  `A4_partitional_destroys_gap : ¬(Value E1 < Value Q)`. The verdict disclosed this; the report must
  not gloss "near-miss restores Geanakoplos monotonicity" into "the refined expert wins" — it does not
  win, it ties. *Honest restatement:* "Replacing E2 by the partitional anchor Q makes the negative gap
  **vanish** (4/9 = 4/9), and Q is itself strictly beaten by the non-partitional E2 — so the negative
  sign is caused by E2's non-partitionality, not the payoffs. The refined expert does not gain value;
  it stops losing it."

- **(b) "Negative value of information" is decision-rule-relative.** The phenomenon is: a
  **non-partitional** agent using **argmax-of-its-own-(miscalibrated)-posterior** can do worse with a
  finer information structure. It is NOT "more information is bad for an optimal Bayesian" (that is
  impossible). The driver is that a non-partitional E's posterior is not a genuine conditional
  expectation over a partition, so its argmax is not a Blackwell-admissible strategy. The writeup says
  this ("the extra information changes the argmax to a locally-rational choice that realizes worse") but
  the slogan "value of information is NEGATIVE" needs the qualifier **"for a non-partitionally-informed
  argmax decider"** every time it appears, or a safety reader will over-generalize to "deferring to a
  more capable system can be worse" without the load-bearing non-partitionality clause.

**Net:** REAL, on-spec, the run's best. Just two qualifiers: near-miss is a tie not a flip; negative-VoI
is non-partitional-argmax-relative.

---

## 3. [MAJOR] `averaging-hides-spikes` (REAL — correct verdict) — but the mandatory near-miss as specified is FALSE, and the substitute does not bind the vulnerable family. The principal should read this as "1.5 of 2 pieces."

The gate's own §4 is the honest core and I fully endorse it; I am elevating its consequence because the
"REAL" tag will otherwise carry more than it earned.

- **Existence direction (i): genuinely REAL.** `a B k i = if i=k then B else 0`; avg = B/T → 0 (real
  `Tendsto`, not the pre-registered `avg ≤ sup` fake), running sup = B ↛ 0. Both limits proved,
  hypotheses load-bearing, target objects absent. This makes CRITIQUE §2b precise and is worth keeping.

- **Near-miss (ii): the SPEC near-miss is false; the SHIPPED one is true but does not exclude the
  vulnerable family.** The TODO mandated `(∀i, a_i ≤ c_i) → c_i→0 → Tendsto(max)→0` with `max` = the
  **running sup** of (i). That statement is **FALSE** (a single early fixed spike pins the running sup
  at B forever), and the executor honestly **proved it false** (`running_sup_near_miss_false`) and
  shipped a TRUE substitute about a **different** quantity — the **per-round swing** `a n → 0`. The
  gate's probe `existence_family_SATISFIES_nearmiss` compiles: **the vulnerable existence family itself
  satisfies the substitute near-miss's hypotheses AND conclusion**. So the substitute does **not**
  certify "the cause of (i) is single-round concentration" — it pins only *persistent/recurring*
  spikes, leaving the single-spike running-sup vulnerability (the actual safety worry: one catastrophic
  round) **un-excluded**. The clause "the vulnerability is EXACTLY unbounded single-round budget
  concentration" is therefore **only half-substantiated**.

This is the right call to leave at REAL (the executor laundered nothing, faked nothing, and disclosed
the gap with a false-witness theorem — textbook honest negative). **But the report must not write "(ii)
certifies the cause of (i)."** *Honest restatement:* "(i) is fully proved. (ii) The natural near-miss
(o(1) per-round budget ⇒ running sup → 0) is **false** and proved false; forbidding per-round
concentration kills only the *per-round* swing, not the running-sup spike — so 'the cause is single
round concentration' is established for *recurring* spikes only, not for the single catastrophic round.
The single-round vulnerability is exhibited but its 'exact cause' is not fully isolated."

---

## 4. [MINOR→MAJOR] `edt-node-value` (REAL — correct verdict, the run's most substantive new Lean) — two residual over-reads.

The gate's settling attack (`A1_hDec_load_bearing`: a separable U with a non-decoupled deceiving κ
satisfies every other hypothesis yet drives the EDT argmax to the wrong action) is genuinely decisive
and shows κ's *decoupling structure* — not just κ's presence — is load-bearing. The self-caught
disguised shadow (the earlier separable-U-with-diagonal-by-fiat) was genuinely removed and replaced by
a proven-non-separable U. **REAL is correct; this is the only file that checks a non-trivial NEW lemma
(`vNode_decoupled_eq`, the κ-collapse) rather than a re-skin or a pure-arithmetic fact.** Caveats:

- **(a) "gap = exactly the acausal payoff" is loose and the writeup knows it.** The policy-value gap is
  9900; the raw acausal reward is 10000; they differ by the 100 own-cost. Both numbers are exposed in
  `gap_is_acausal_payoff`, so this is disclosure not laundering — but the report should write "gap = the
  acausal payoff **net of the own-cost the optimum also pays** (9900 = 10000 − 100)", never the bare
  "gap = the acausal payoff."

- **(b) The result is entirely conditional on κ, and κ is a free modeling input.** This is the honest
  reframing (round-1's free `node_value` is replaced by `U∘κ` with κ explicit and inspectable), and it
  is a real advance. BUT it means the file does **not** answer "should the agent defer?" — it answers
  "deference reduces to whether the agent's self-model κ severs the acausal coupling." A principal must
  not read `mugging_edt_misses` as "EDT agents fail to defer"; it is "**given a severing κ**, the
  EDT-argmax misses the UDT optimum." The locus of the open problem moved from `node_value` to κ; it was
  not closed. The writeup says this in §6; keep it foregrounded.

---

## 5. [BLOCKER as stated] `trust-laundering` — the gate's SHADOW is CORRECT, and the work writeup is still asserting the refuted claim. This must not be silently upgraded to a win.

I independently confirmed the SHADOW. `trust-laundering.py` `link_holds` (L92–99) iterates `test_grid`
over `x_values=(0,1)` only — the `{0,1}^W` indicator grid, 32 points for |W|=3 — whereas the DDB/Lean
property `value_iff_totalTrust` (LeanDeference L446–454) and v2 §0.2 L77 quantify over **all real-valued
X**. The gate's settling attack stands: re-running the headline `WITNESS` against a rich rational grid,
**both** short links fail (L1 at X=(0,7/8,5/8), s=2/3; L2 at X=(3/4,0,1/4), s=1/3). So the printed
non-vacuity witness is a **vacuous chain** (pre-registered shadow case (c)), and *every* downstream
statistic — the 41% genericity number, the `NESTED_WITNESS` refutation, the 343/0 recovery sweep — is
computed with the shadow predicate `link_holds` and **does not transfer** to genuine Total Trust.

Two things the gate got exactly right and the report must preserve:
- The **claim is true** (the gate found 6 honest faithful witnesses, fine-grid-verified one). So this
  is SHADOW, not BROKEN. But "the claim is true" ≠ "the work established it." **The submitted artifact
  establishes nothing it reports**; a fresh real-grid search would be needed to reissue any witness,
  genericity number, or recovery characterization.
- **`work/trust-laundering.md` still states the falsehood as fact** ("L1: HOLDS over full grid. L2:
  HOLDS over full grid", lines 47/118) and presents the recovery characterization as a finding. The
  report must flag that the work writeup is **stale/wrong as written**, not merely "shadow but morally
  fine." *Honest restatement of the entire TODO's status:* "Non-transitivity of genuine DDB Total Trust
  is **plausibly true** (6 unverified-by-original faithful witnesses located by the gate, one
  fine-grid-checked by the gate), but **the executor's search, witness, genericity statistic, and
  recovery characterization are all computed on a 32-point indicator shadow of the ∀X:W→ℝ quantifier and
  none is validated**. Re-run required before any number is cited."

---

## 6. Consolidation / re-skin audit (is anything a relabel of v2 or LeanDeference?)

I checked each headline object against the GLOBAL OFF-LIMITS list. **None of the four REALs is a
re-skin** — this is a genuine improvement over round 1 (where `WAR_of_argmax`, `weak-endorsement`,
`stag_hunt_select` were `value_of_CM`/`CM_implies_immodest` duplicates):

- `partition_averaging` is a fresh law-of-total-probability lemma, not `value_of_CM` (which is a
  CM-defect→Value identity); different statement, different proof. ✓ new.
- `negative-voi` is a two-expert Value comparison; `Value` here is a bespoke menu-argmax object, NOT
  `DeferenceArgmax.value_of_argmax` (that is the single-expert positive route). The OFF-LIMITS
  `AntiExpert` frame is untouched. ✓ new (and it builds the explicitly *unbuilt* v2 §1.1 example).
- `averaging-hides-spikes` is pure Mathlib analysis; it imports none of `DeferenceAsymp`/`DeferenceTrader`
  and is the **dual** of `round_profit_ge_gap` (an upper-bound *failure*, not the lower bound). ✓ new.
- `edt-node-value` genuinely replaces the off-limits free `node_value` with `U∘κ` and proves a new
  collapse lemma; the verdict's round-1-vs-run-2 diff (coupled type `U:(S→A)→ℝ` vs round-1's separable
  `U:S→A→ℝ`, derived vs hand-fed local argmax) confirms it is not a renamed `split_eq_global`. ✓ new.

**The one consolidation-flavored caveat:** `aumann-modesty` and `negative-voi` are both
"non-partitional S4 frame breaks a partitional guarantee" objects. They are disjoint as the
CONSOLIDATION step intended (averaging-tower vs menu-VoI), so this is **not** the round-1 duplication —
but the report should note they are **two faces of one structural fact** (drop Euclidean → the
partition guarantee fails), lest "two independent results" oversell what is one phenomenon witnessed
twice. (The dropped Geometric-UDT candidate was correctly folded for exactly this reason.)

---

## 7. Spec-drift check

- `aumann-modesty`: **mild drift** — TODO said "self-evident event `C` that the cells COVER but do not
  PARTITION"; the build used `C = whole space`, which satisfies the letter but makes the self-evidence
  non-trivially-checked clause vacuous (see §1b). On-spec on overlap/cover/posteriors; under-delivers on
  "genuine self-evident sub-event."
- `negative-voi`: **on-spec.** Near-miss is the weaker (equality) form the TODO permits (`≥`), with
  strictness carried separately. No drift.
- `averaging-hides-spikes`: **partial drift forced by mathematics** — the spec's near-miss is false; the
  executor correctly reported this rather than faking it. Honest, but the deliverable is narrower than
  the TODO imagined.
- `edt-node-value`: **on-spec**, including the harder coupled near-miss on a genuinely non-separable U.
- `trust-laundering`: **on-spec in intent, shadow in execution** — it did search the real inequality
  per-(X,s), but over a grid too coarse to be the real property; the recovery contrast drifted into a
  refuted conjecture (honestly reported) plus a trivial identity (honestly reported).

---

## 8. The single thing to fix before the report ships

If the report is to be born honest, its **first** sentence about results must be:

> "Round 2 kernel-checked four finite single-frame facts (a single-agent averaging-tower failure, a
> single-decider negative-VoI menu example, a real-analysis avg-vs-sup separation, and a single-agent
> EDT/UDT κ-collapse) and ran one cross-agent EXEC search whose submitted artifact is a shadow. **No
> cross-agent or asymptotic trust statement is machine-checked anywhere; the four REAL results bear on
> trust by INTERPRETATION, not derivation.** The genuine new content is: `edt-node-value`'s κ-collapse
> lemma (the one substantive new theorem), `negative-voi`'s faithful build of v2 §1.1's previously
> unbuilt Weatherson example, and `aumann-modesty`'s instantiated averaging-failure + partitional
> near-miss. `trust-laundering`'s true claim awaits a real-grid re-run."

Everything else (the agreement slogan, "value of information is negative", "the cause is single-round
concentration", "alignment is not closed under delegation [established]") is a gloss that outruns the
kernel and must travel with its qualifier.

---

### Verdict-by-verdict bottom line

| id | gate | my call | over-claim to fix |
|---|---|---|---|
| `aumann-modesty` | REAL | **REAL, over-titled** | "Aumann agreement"→"averaging/tower step, single-agent"; `C`=whole-space self-evidence is trivial |
| `negative-voi` | REAL | **REAL, on-spec (best)** | near-miss is a tie (4/9=4/9) not a flip; "neg VoI" is non-partitional-argmax-relative |
| `averaging-hides-spikes` | REAL | **REAL, ½ near-miss** | spec near-miss is FALSE; substitute doesn't bind the vulnerable family — drop "(ii) certifies cause of (i)" |
| `edt-node-value` | REAL | **REAL (most substantive)** | "gap = acausal payoff" is net-of-own-cost; result is conditional on free κ |
| `trust-laundering` | SHADOW | **SHADOW (concur)** | claim true but artifact establishes nothing; work writeup still states the falsehood — re-run on a real grid before citing any number |
