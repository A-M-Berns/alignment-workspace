# Brainstorm — angle "tractable-wins" (Round 2)

Goal: genuinely-NEW results that are actually validatable this summer, biased hard toward
LEAN-CORE finite/decidable facts and EXEC counterexample-searchable claims. Mining round 1's
CRITIQUE.md for the cheapest real skipped result and similar low-hanging fruit. Each item
pre-registers the SHADOW (fake validation) to avoid.

Author stance: adversarial about my own ideas. Every item below is checked against the
OFF-LIMITS list (the LeanDeference.lean cores + v2 establishments) so it is not a re-skin.

## OFF-LIMITS inventory (do not re-prove / re-skin)

From `lean-deference/LeanDeference.lean` (confirmed sorry-free):
- `Deference.decomposition`, `value_of_defects`, `soft_nonneg`, `value_of_CM` — the §3 Value backbone.
- `DeferenceExtra.softmax_lower_bound` — softmax within card·δ of max.
- `DeferenceExtra.CM_implies_immodest` — instantiate CM identity at the fiber indicator ⇒ P_w(fiber)=1.
- `DeferenceAsymp.{Approx, AsympLE, approx_sum, value_asymptotic}` — the ≂ₙ/≲ calculus + Value-mod-LI.
- `DeferenceArgmax.*` (value_of_argmax, payoff_gap_le_l1, value_argmax_via_softmax).
- `DeferenceConverse.*` — witness_identity, value_iff_totalTrust, the **AntiExpert** Fin-2 frame
  (π=½, P=⅕ diagonal, stationary πP=π, TT_negative=−¼, value_fails). The converse Value⟺TotalTrust.
- `DeferenceFold.*` — fold_pointwise/fold_sum (ccee collapses to cee under expert-known weight),
  fold_hypothesis_fails on AntiExpert.
- `DeferenceTrader.*` — round_profit_ge_gap, gap_pos_imp_profit_pos (no-Dutch-book arithmetic core).

From round-1 lab Lean (confirmed shadows, do not duplicate): legitimacy.lean (`defect`,
`drug_defect_sign`), legitimacy-corrigibility.lean (`comply_iff_endorsed`, `endorsed_signal_complies`,
`adversarial_signal_resists` — the corrigibility sign-flip), weak-endorsement*.lean, lateral-dtype.lean
(= value_of_CM re-skin), merging-inductors.lean (orthogonal selector monotonicity).

From v2 (established prose / interpretation, off-limits to "re-derive"): the S4/S5 dichotomy;
"Euclidean ⇒ partition ⇒ immodest"; Geanakoplos value-of-information ≥ 0 for reflexive+transitive+nested
vs partitional; the Coin/Bentham infinite-frame failures; §10 composition (Value-given-LUV-Total-Trust).

The CRITIQUE's verdict on what is genuinely-new-this-run: {corrigibility sign-flip, legitimacy sign,
R1-vs-R2 dichotomy, the merge *reduction*}. Everything else is consolidation/conjecture/interpretation.
The single cheapest real NEW result that was **skipped**: the finite Aumann-agreement-fails-under-modesty
example (CRITIQUE §8 + §9). That is candidate #1.

---

## Candidate 1 (FLAGSHIP) — Finite Aumann-disagreement-under-modesty 3-world example. [LEAN-CORE]

**Claim.** There is an explicit finite probability frame (a common prior π on a small W, two
information structures E_A, E_B for two agents, at least one of which is NON-partitional / S4-but-not-S5,
i.e. *modest*) and an event/random variable X such that: (i) the two agents have COMMON KNOWLEDGE of
each other's posterior expectation of X, yet (ii) those posteriors DIFFER. This is a concrete,
machine-checkable counterexample to Aumann's agreement theorem when the partition (S5/Euclidean)
hypothesis is dropped to mere modesty (S4) — exactly the regime v2 §1.1/§5.2 says LI lives in.

The Lean content is purely finite arithmetic: pin down W (3 or 4 worlds), the common prior π, the two
accessibility relations (as W→W→Bool or as explicit cells), define posterior_A(X|cell), posterior_B,
the "both posteriors are common knowledge" event (the meet/iterated-knowledge of the two posterior
values is the whole support — decidable), and prove `posterior_A ≠ posterior_B` on it by `decide`/`norm_num`.

**Setting.** Finite common-prior frame, two non-partitional information correspondences (Geanakoplos
"game theory without partitions" setting), one of them modest. NOT logical induction — but it is the
*finite reflection* of "the AI disagrees with me even after we share our credences," the principal's
most directly-relevant framing.

**Off-limits adjacency.** v2 §1.1 STATES "drop Euclidean ⇒ modesty allowed" and §5.2 STATES that the
clean Value proof forces immodesty on finite frames. CM_implies_immodest proves "CM identity at fiber
⇒ immodest." NONE of these build a two-agent disagreement example, and none formalize Aumann at all.
The AntiExpert frame is a ONE-agent expert/novice frame about Value, not two-agent common-knowledge
disagreement. So this is new: it is the *common-knowledge / two-agent* face, never built.

**Modality: LEAN-CORE.** Genuinely finite/decidable. The target object (modest disagreement) is the
CONCLUSION, computed from π and the relations; it is NOT a hypothesis. Ship: (a) non-vacuity witness =
the disagreement is strict and common-knowledge holds (both `decide`-checked); (b) near-miss = if BOTH
structures are partitional (S5/Euclidean), the SAME construction forces agreement (posteriors equal on
the common-knowledge event) — i.e. restoring the dropped hypothesis makes the disagreement FALSE. That
near-miss is the honest Aumann theorem on the finite frame, and it is what certifies the example is
about *modesty*, not about an arithmetic typo.

**PRE-REGISTERED FAKE.** The shadow: (i) assume `posterior_A ≠ posterior_B` as a hypothesis and "prove"
common knowledge can't force agreement — laundering. (ii) Build a frame where common knowledge of
posteriors simply FAILS (so Aumann is vacuously not contradicted) and call it disagreement — that is
not Aumann-disagreement, it's no-common-knowledge. (iii) Use a non-common prior and pretend it is
Aumann — Aumann needs a common prior. The faithfulness gate: I must EXHIBIT, by `decide`, that the
event "A's posterior = a AND B's posterior = b" is common 1-knowledge (in the iterated-meet sense) on a
nonempty set, AND that a≠b there, AND that the partitional version of the very same π forces a=b.

**Tractability: medium.** The arithmetic is trivial; the work is encoding "common knowledge of the
posterior value" decidably (meet of the two correspondences / iterated knowledge operator on a 3-4
world frame) so that the near-miss (partitional ⇒ agreement) is also a clean `decide`. Risk: getting
the common-knowledge operator faithful rather than a weaker shadow. This is THE item.

---

## Candidate 2 — Modesty is NECESSARY for disagreement: finite converse / sharp threshold. [LEAN-CORE]

**Claim.** On the SAME small finite frames, prove the positive direction as a genuine theorem (not just
the near-miss of C1): *if both agents' information correspondences are partitional (equivalence
relations / S5) and the prior is common, then common knowledge of the two posterior expectations of any
X forces them EQUAL.* This is finite Aumann proper. Then the pair {C1 counterexample, C2 theorem}
brackets exactly the Euclidean property: agreement ⟺ (no modesty), on the finite frame.

**Setting.** Same as C1. This is the finite-Aumann theorem itself, stated for two agents with general
finite partitions, decidably or by a short structural proof.

**Off-limits adjacency.** v2 §1.1 states the S4→S5 = +Euclidean story for ONE agent's Total Trust.
Aumann for TWO agents sharing a prior is a different theorem (about the MEET of two partitions) and is
not in v2 or LeanDeference. CM_implies_immodest is one-agent. So new.

**Modality: LEAN-CORE.** The Euclidean/partition hypothesis is a hypothesis ON THE FRAME (legitimate —
it is the structural assumption Aumann needs), NOT on the conclusion. Conclusion = equality of
posteriors. Non-vacuity: instantiate on a concrete frame where common knowledge holds and posteriors
are computed and shown equal (and where, without it, C1 shows they'd differ). Near-miss IS Candidate 1.

**PRE-REGISTERED FAKE.** Shadow: prove "if posteriors are equal then they're equal" (trivial), or
assume the meet is trivial (single cell = full common knowledge of everything) so agreement is forced
for boring reasons. Must use a frame where the meet partition is NON-trivial (more than one common-
knowledge cell) so the theorem has content. Also must NOT assume a single common partition for both
agents — they get DIFFERENT partitions, agreement comes from the meet.

**Tractability: medium-hard.** Either fully general (Aumann's meet argument in Lean — real but standard
Mathlib-able finite measure work, possibly heavy) OR concrete-frame `decide` (easy but weaker). I'd ship
the concrete-frame version first as the honest non-vacuity companion to C1, and flag the general theorem
as a stretch. Honestly: the general version may be more than a summer's Lean; the concrete version is a day.

---

## Candidate 3 — Two-expert Value-comparison: a finite frame where the LESS-informed expert has strictly higher Value (Weatherson's "E₂ partitional is essential", instantiated for deference). [LEAN-CORE]

**Claim.** Exhibit an explicit finite frame with two experts E₁, E₂, both reflexive-transitive-nested
(S4), E₂ NON-partitional, a menu/payoff O, such that the recommended-strategy Value under the MORE
refined E₁ is STRICTLY LESS than under E₂ — i.e. value of information goes NEGATIVE when the coarser
experiment is non-partitional. This is the deference reading of Weatherson's tightness result (his §2,
result 1, which v2 §1.1 cites as "a 3-world example" but does NOT build).

**Setting.** Finite prior frame, two non-partitional info structures, explicit O. Decidable arithmetic.

**Off-limits adjacency.** v2 §1.1 STATES Geanakoplos requires "E₂ partitional" and CITES Weatherson's
3-world tightness example *in prose* (line 241), but it is NOT formalized and NO frame is given. The
AntiExpert frame is about ONE expert vs the unconditional martingale (Total Trust failing), a different
phenomenon. Geanakoplos VoI≥0 is "established prose" but its TIGHTNESS (the negative VoI witness) is not.
So building the explicit negative-VoI frame and `decide`-checking it is new and directly load-bearing:
it is the witness that "the future self dominates only because it's the maximal/partitional refinement"
(v2 §10 (a)) genuinely NEEDS the partitional anchor.

**Modality: LEAN-CORE.** Pure finite arithmetic comparing two expected returns. Target (negative VoI)
is the conclusion, computed. Non-vacuity: the strict inequality `Value(E₁) < Value(E₂)` by `norm_num`.
Near-miss: if E₂ is made partitional (refine it to the meet), the SAME O gives `Value(E₁) ≥ Value(E₂)`
(Blackwell restored). That near-miss certifies the example isolates non-partitionality.

**PRE-REGISTERED FAKE.** Shadow: pick payoffs so the inequality holds for a trivial reason unrelated to
information (e.g. E₁'s "recommended strategy" defined adversarially). Must use the genuine
recommended-strategy = argmax-of-posterior definition for BOTH experts, so the gap is purely the
information structure. Also must not smuggle "E₂ better" as a hypothesis.

**Tractability: easy-medium.** Weatherson's example is 3 worlds; transcribing it and checking two sums
is a `decide`/`norm_num` job. The near-miss is the only fiddly part. Strong candidate — concrete,
cited-but-unbuilt, sharp.

---

## Candidate 4 — EXEC: exhaustive search confirming the merge premise "B is a logical inductor" FAILS off the good-feedback subsequence, in a concrete finite mock-market. [EXEC]

**Claim.** Implement the Eisenstat construction `B_t = 𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)` in a small *executable*
mock LI market (finite trader pool, finite sentence set, explicit price-update like the LI paper's toy
markets used in `deference-in-logical-induction-check.py` style), and SEARCH for a trader against B that
exploits B (a Dutch book / unbounded-value bounded-risk exploit) on a subsequence WITHOUT good feedback
— demonstrating, by execution on the real construction, that B is NOT an inductor unrestricted (CRITIQUE
§1a: "B is at best behaviorally inductor-like on a good-feedback subsequence; AGENDA conjecture (i) is
not addressed"). Contrast: on the good-feedback subsequence the same search finds NO exploit (positive case).

**Setting.** A small finite logical-induction-like market simulator (the actual B construction, A's
prices feeding B), not a shadow. Counterexample search = the EXEC modality the rules want.

**Off-limits adjacency.** merging-inductors.lean proves only an orthogonal selector-monotonicity fact;
the model docs ASSERT B is non-inductor off good feedback but give no executable witness. So an actual
exploit-search over the real construction is new and directly answers the CRITIQUE's "double conjecture"
complaint with evidence rather than prose.

**Modality: EXEC** (NOT Lean — the LI machinery cannot be honestly formalized; building a fake Lean that
assumes "A is an inductor" would be exactly the laundering the rules forbid). The honest move is to
SEARCH the real (finite, executable) object.

**PRE-REGISTERED FAKE.** Shadow #1: a Lean file `IF A is an inductor and feedback is good THEN B endorsed`
— pure hypothesis-laundering, banned. Shadow #2: a "market" so degenerate B is trivially fine (no
treacherous trader in the pool) — must include adversarial traders. Shadow #3: declaring victory on a
single hand-built exploit without an exhaustive/randomized search establishing it's not a coding bug.
The gate: the exploit must move B's price by a *bounded-risk unbounded-value* pattern over the simulated
horizon, and the SAME pool must fail to exploit on the good-feedback subsequence (both shown by the run).

**Tractability: medium-hard.** Writing a faithful-enough finite LI mock is the cost; it risks being a
caricature that proves nothing. Mitigation: keep claims modest — "in THIS executable family, off
good-feedback B admits an exploit a real inductor would not" is an illustrative EXEC finding, explicitly
NOT a theorem about all inductors. Honest scoping is the success criterion here.

---

## Candidate 5 — EXEC/LEAN-CORE: the "one big lie" single-round vulnerability, made concrete and quantified. [EXEC then LEAN-CORE non-vacuity]

**Claim.** CRITIQUE §2b: every endorsement/Value result is a ≂_w AVERAGE; it is silent on individual
high-stakes rounds; a treacherous trader can dump its budget into one decision. Make this PRECISE and
checkable: construct an explicit finite sequence of (price, payoff) rounds where the asymptotic-average
Value gap → 0 (Value "holds") YET a single designated round has an arbitrarily large adverse swing
financed by a bounded-budget trader. EXEC: search/parameterize the worst single-round damage subject to
"average gap ≤ ε". LEAN-CORE companion: prove the exact finite identity that a bounded total budget B
permits a single-round swing of size up to B while contributing only O(B/T) to the T-round average —
so average-smallness gives NO single-round bound. (This is a clean discrete inequality, fully finite.)

**Setting.** Finite sequence of rounds; a budget-constrained adversarial contribution; average vs sup.
The LEAN-CORE part is `∑/T → 0` compatible with `max_round` large — a real, faithful, non-LI inequality.

**Off-limits adjacency.** v2/CRITIQUE STATE this gap in prose (open-problem #4). DeferenceTrader proves
per-round profit ≥ gap (a LOWER bound favoring the truster); nobody formalizes the UPPER-bound failure
(adversary's single-round freedom). The averaging-hides-spikes inequality is not anywhere. New.

**Modality: LEAN-CORE for the inequality** (it is genuinely finite and the target — "average small ⇏
sup small" — is the conclusion, with the budget as an honest hypothesis, not the LI theorems). EXEC for
the worst-case parameter sweep illustrating it on the real Value sequence.

**PRE-REGISTERED FAKE.** Shadow: prove `(∑ a_i)/T ≤ max a_i` (true, trivial, WRONG DIRECTION) and dress
it as the vulnerability. The real content is the EXISTENCE direction: a family with average→0 and a
single coordinate = budget B (constant), so `max` does NOT → 0 while `avg` → 0. Must exhibit the family
and prove BOTH limits. Near-miss: if the trader budget per round is also forced o(1), then max → 0 too
(so the vulnerability is exactly the unbounded-single-round-budget). That near-miss certifies the
result is about budget concentration, not arithmetic.

**Tractability: easy (Lean inequality), medium (EXEC sweep).** The Lean inequality is a half-day. Genuinely
new framing of the safety-relevant limit the CRITIQUE wanted foregrounded. Good cheap win.

---

## Candidate 6 — Legitimacy is NON-TRANSITIVE: a finite endorsement-laundering 3-agent example. [LEAN-CORE]

**Claim.** CRITIQUE §8 flags "Legitimacy non-transitivity (D12) / trust-laundering — CONJECTURE, not
developed." Build the finite witness: three agents A, B, C with explicit credences such that A endorses
B and B endorses C (van-Fraassen reflection / the finite `defect=0` endorsement relation holds for both
pairs) YET A does NOT endorse C. I.e. the finite endorsement relation is NOT transitive. This is the
"trust laundering" safety concern (multi-agent delegation chains) made into a concrete decidable example.

**Setting.** Finite frame, three credence functions, the endorsement relation defined exactly as in v2
(A endorses B iff A's conditional on B's stated credence equals that credence, the finite/exact form).
Decidable.

**Off-limits adjacency.** v2 establishes endorsement⟺deference for the present↔future self and the §10
expert composition. It does NOT study transitivity / chains. legitimacy.lean's `defect` is a one-pair
object. CM_implies_immodest is one-agent. So a 3-agent non-transitivity witness is new, and it directly
bears on "can you trust an AI that was vetted by another AI?" — a real human-AI-trust concern.

**Modality: LEAN-CORE.** Finite, decidable. Target (non-transitivity) is the conclusion: `endorses A B`,
`endorses B C`, `¬ endorses A C`, all by `decide`/`norm_num` on explicit numbers. Non-vacuity is built
in (all three facts are exhibited). Near-miss: identify the EXTRA hypothesis that DOES make endorsement
transitive (e.g. a common-prior / nestedness condition) and show that on a frame satisfying it,
transitivity holds — certifying the counterexample exploits exactly the missing structure, not a typo.

**PRE-REGISTERED FAKE.** Shadow: pick credences where `endorses A B` actually FAILS (so the chain is
vacuous) and call it non-transitivity — must verify BOTH links hold and the long edge fails, all three
by computation. Shadow: define endorsement non-faithfully (e.g. just "A's mean = B's mean") so the
example is about means not reflection. Must use the genuine conditional-reflection definition matching v2.

**Tractability: medium.** The hunt for explicit numbers making two reflection-links hold while the third
fails is the real work — likely needs a small EXEC search FIRST to find the numbers, then a LEAN-CORE
`decide` to certify them. The conditional-reflection definition on probability-zero events needs the
careful `>y` form. Worth it: trust-laundering is a crisp, principal-relevant, unbuilt target.

---

## Candidate 7 — EXEC: counterexample-search over the v2 §10 premise to find a frame where LUV-Total-Trust toward an expert holds but Value FAILS (testing whether the §10 composition is tight). [EXEC]

**Claim.** v2 §10 says Value follows from (a) novice's own coherence + (b) LUV-Total-Trust toward the
expert. The composition is claimed exact. EXEC test of FAITHFULNESS: exhaustively/randomly search finite
frames + experts for a counterexample where premise (b) holds (numerically) but the §10 conclusion
(Value) fails — which, if found, would mean a HIDDEN premise the CRITIQUE §0 warned about ("the
reduction itself ... that there is no second hidden premise for distinct inductors is SKETCHED"). The
expected/positive outcome is NO counterexample on the finite-exact fragment (confirming the finite
composition is tight), with any failure flagged as a hidden-premise discovery.

**Setting.** Finite frames (the DeferenceConverse exact-fragment lives here), random/exhaustive search
over π, P, expert E, menus. Pure sympy/numpy arithmetic on the REAL composition identity, not a shadow.

**Off-limits adjacency.** DeferenceConverse PROVES value_iff_totalTrust for the two-option WITNESS menu.
§10 is the general expert composition. The check.py (18/18) checks the algebraic identities but does NOT
adversarially search for premise-holds-but-Value-fails over many frames. So a counterexample HUNT over
the §10 premise across random frames is new — it is the empirical faithfulness test the CRITIQUE §0
asked for ("the reduction is the contribution; verify there's no hidden second premise").

**Modality: EXEC.** This is a search-for-counterexample over the real finite objects — exactly EXEC. A
Lean theorem here would just re-prove value_iff_totalTrust (off-limits) or launder the general §10
(which needs the LI side). The honest validatable thing is the search.

**PRE-REGISTERED FAKE.** Shadow: only search frames where the premise is checked via the SAME identity
that yields the conclusion (circular — finds nothing by construction and proves nothing). Must compute
premise (b) and conclusion (Value) by INDEPENDENT routes (b from the expert's conditional martingale
mass; Value from the realized diagonal return) so a gap is detectable. Shadow: search only the
two-option menu (where DeferenceConverse already settles it) — must search GENERAL finite menus where
§10's generality is actually tested.

**Tractability: medium.** Implementing two independent computations of premise and conclusion over random
finite frames is doable in sympy/numpy. Outcome is likely "tight, no hidden premise on the finite
fragment" — a genuine (if negative-flavored) confirmation that strengthens the lab's one real
contribution (the reduction). If it FINDS a hidden premise, that is a major result. Either way honest.

---

## Self-critique / ranking

- **Most clearly a genuine NEW win + most validatable + most principal-relevant:** C1 (finite Aumann-
  under-modesty) — the explicitly-skipped cheapest result. C3 (negative-VoI / Weatherson tightness) is
  a close second: cited-in-prose-but-unbuilt, 3 worlds, sharp near-miss. C6 (legitimacy non-transitivity)
  is the freshest *safety* angle (trust-laundering) and clean once the numbers are found.
- **C2** is really the honest non-vacuity companion to C1 (ship the concrete-frame version; the general
  Aumann-meet theorem in Lean is a stretch — flagged).
- **C5** (averaging-hides-spikes) is the cheapest LEAN-CORE inequality and foregrounds the safety limit
  the CRITIQUE wanted in the exec summary; low risk.
- **C4, C7** are the EXEC items — honestly tagged EXEC precisely because writing Lean for them would be
  laundering (C4 assumes A-is-inductor; C7's general §10 needs the LI side). C4 is the riskiest (mock-LI
  fidelity); C7 is a clean faithfulness search.
- **No item is PROOF-ONLY** in this batch by design (the angle is tractable-wins); if forced to name the
  PROOF-ONLY sibling, it is "soft mutual-trust with a shared δ_n schedule" (lateral §3.2) — genuinely
  needs the LI machinery and must NOT be faked. I deliberately did not include it here.

All seven avoid the round-1 traps: none assumes its target object as a hypothesis (the LI theorems / the
cross-agent martingale / the asymptotic layer never appear as hypotheses in any headline result above),
each LEAN-CORE item ships a non-vacuity witness AND a near-miss, and each EXEC item searches the REAL
finite object rather than a pointwise shadow.
