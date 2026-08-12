# 00 — Orientation Map for the Deference & Trust Lab

*A compact, load-bearing map of what is already established and where the formalizable open
questions are. Other agents build on this. Every claim is flagged **PROVED** (machine- or
paper-checked) / **SKETCHED** (LI-paper-level rigor, not fully formal) / **CONJECTURE** /
**INTERPRETATION**. Citations point into the v2 artifact and the LI paper by theorem number.*

Source artifacts read for this map: `deference-in-logical-induction-v2.md` (esp. §0, §3, §5.2,
§10), `deference-in-logical-induction-check.py`, `lean-deference/LeanDeference.lean`, the LI paper
`references/logical-induction/main.tex` §4.12 (lines 2045–2114), DDB, Weatherson, and the
`udt-representation-theorem/` endorsement work.

---

## 1. The existing LI-deference result (one tight paragraph)

**SKETCHED (proof) / PROVED (its finite algebraic core + the asymptotic-calculus composition).**
Take a single logical inductor and read DDB's "expert" as *its own more-thought-out future self*,
the day-`f(n)` market (`f` a deferral function, `f(n)>n`). The novice is the present operator
`𝔼_n`; the expert's estimate is the LUV `𝔼_{f(n)}(X)`, a logically uncertain quantity the present
self cannot read off. **Value (LI form)** — *"in a timely manner the present self would rather hand
any bounded decision to its future self than commit now to a fixed bet,"*
`𝔼_n(Ŝ_n) ≳ₙ 𝔼_n(O^i_n)` where `Ŝ_n = Σ_j α^j_n O^j_n` and `α^j_n` is the softmax (temperature
`δ_n↓0`) of the future estimates `𝔼_{f(n)}(O^j_n)` — has a five-line proof (v2 §3). The **single
premise that drives it** is the *conditional martingale* **No Expected Net Update under
Conditionals** (Thm 4.12.3, `thm:ccee`): for any market-generable weight `w_{f(n)}∈[0,1]`,
`𝔼_n(X·w_{f(n)}) ≂ₙ 𝔼_n(𝔼_{f(n)}(X)·w_{f(n)})`. Taking `w=α^j` keeps each bet paired with its own
selection weight and swaps the bet for the future self's verdict — exactly the **diagonal↔row-wise
bridge** that DDB must reconstruct by hand via convex geometry (their Lemmas 7.2.4 "transitivity" /
7.2.5 "reflexivity" / "modestly informed"). The other four lines use only the novice's *own*
coherence (Linearity 4.8.4; Provability-Induction monotonicity 4.8.10 on a purely-algebraic
softmax gap; unconditional martingale 4.12.1). **§10 modularization (interpretation, well-argued):**
auditing the five lines, lines 2/4/5 are *free* (novice's own coherence, expert-agnostic); only
lines 3 and 6 use self-trust, and line 6 is line 3 at weight `w≡1`. So there is exactly **one
expert-specific premise** — the *cross-agent* LUV-Total-Trust `𝔼_n(X·w) ≂ₙ 𝔼_n(𝔼_exp(X)·w)` — and
deferring to a *generic* observable, bounded expert reduces to assuming that one martingale. The LI
"win" over DDB: the no-Dutch-book criterion supplies the coherence *dynamically* and for free, so
none of the simplex / convex-hull / tie-breaking machinery is needed.

---

## 2. Glossary of the load-bearing formal objects an LI-trust model needs

| object | precise content / definition | role |
|---|---|---|
| **logical inductor** `(ℙ_n)` | a market price sequence over a theory `Γ` (representing computable functions), `ℙ_n(φ)∈[0,1]` = day-`n` credence in sentence `φ` | the reasoner; "novice" and "expert" are both inductors |
| **market / trader** | the price sequence is the *market*; a **trader** is an efficiently-computable strategy buying/selling shares in sentences at the posted prices | the LI **criterion**: *no efficiently-computable trader exploits the market for unbounded profit against every consistent world* `𝒫𝒞(Γ)`. This is a **no-Dutch-book** condition and is the sole hypothesis behind every theorem below. (DDB *extract* coherence from Total Trust by convex geometry; LI *bakes it in*.) |
| **`𝔼_n`** | day-`n` expectation of a `[0,1]`-LUV: `𝔼_n(X)=Σ_{i=0}^{n-1}(1/n)ℙ_n(⌜X>i/n⌝)` (LI Def 4.8.2) | the present self's estimate operator = DDB's novice `π` |
| **LUV** | logically uncertain variable: a formula `Γ` proves names a unique real; `[0,1]`-LUV if provably in `[0,1]` (Def 4.8.1) | LI's bounded random variable; bets/options are `[0,1]`-LUVs |
| **corner quotes `⌜·⌝`** | Gödel code: `𝔼_{f(n)}(X)` is a *real*, `⌜𝔼_{f(n)}(X)⌝` is the *LUV naming it* | makes "present estimate of future estimate" `𝔼_n(⌜𝔼_{f(n)}(X)⌝)` type-correct |
| **`≂ₙ` / `≳ₙ` / `≲ₙ`** | `x≂ₙy :⇔ lim(x_n−y_n)=0`; `x≳ₙy :⇔ liminf(x_n−y_n)≥0`; `≲ₙ` dual | the *only* sense of "=" / "≥" in LI; everything holds up to vanishing error "in a timely manner" |
| **deferral function `f`** | `f:ℕ⁺→ℕ⁺`, `f(n)>n`, computable in time poly in `f(n)` (Def 4.2.3-ish) | indexes the more-thought-out future self / the "speed gap" |
| **market-generable (`ℙ`-generable)** weights | a real sequence computable in poly time from the day-`n` (or future) market prices | what makes selection weights querying the future market *legal inputs* to 4.12.3; **observability** of an external expert means its estimates are `ℙ`-generable from the novice |
| **continuous indicator `Ind_δ`** | Lipschitz ramp of width `δ` softening `𝟙[x>y]` (Def 4.3.x) | **soft** conditioning on a fact about the *future* market; hard conditioning is paradox-prone (liar sentence). The soft/hard split is the home of modesty (see §5.2). |
| **deferral function `f` ⇒ martingales** | 4.12.1 `cee` (unconditional, LUV): `𝔼_n(X)≂ₙ𝔼_n(𝔼_{f(n)}X)`; 4.12.3 `ccee` (conditional, weighted): `𝔼_n(X·w)≂ₙ𝔼_n(𝔼_{f(n)}(X)·w)` | `cee` = "I expect today what I'll expect tomorrow"; **`ccee` is the engine of Value** (conditional version is what discriminates — v2 §1.3 shows the unconditional one is neither necessary nor sufficient) |
| **Self-Trust (4.12.4 `thm:st`)** | `𝔼_n(⌜𝟙(φ)·Ind_δ(ℙ_{f(n)}(φ)>p)⌝) ≳ₙ p·𝔼_n(⌜Ind_δ(ℙ_{f(n)}(φ)>p)⌝)`, squinting `𝔼_now(φ∣ℙ_later(φ)>p)≳p` | the LI form of DDB **Simple Trust**; **hard** version is *false* (liar `φ="ℙ_{f(n)}(φ)<½"`), soft version true — the canonical false-hard/true-soft asymmetry |
| **deferral function `f` self vs external expert** `𝔼_{exp}` | replace `𝔼_{f(n)}` by an external inductor's estimate | §10: the only premise that must be *re-assumed* (not free) is LUV-Total-Trust toward `𝔼_exp` |
| **market-generable softmax** `α^j_n` | `softmax(𝔼_{f(n)}(O·)/δ_n)`, `Σα^j=1` | the soft "recommended strategy"; legal weight in `ccee`; softening also removes DDB's Weak-Value↔Value tie-breaking |
| **finite-collapse impossibility (§5.2)** | **PROVED (finite core).** On a *finite* frame, soft conditional martingale ⇒ **immodesty** `P_w(P=P_w)=1` (Reflection / S5 partition). A reasoner both *modest* and *conditional-martingale-coherent* needs estimates ranging over a **continuum without spectral gap** → an infinite, self-referential frame. LI is the first concrete inhabitant. | explains *why* the clean theorem cannot live on finite frames; the hard conditional martingale stays *permanently false* and that gap is the home of modesty |
| **modestly informed** (DDB) | `P_i ∈ CH({P̂_i}∪C_i^−)`: expert's credence is a mixture of its confident hunch and the other candidates it leaves open | the credence-level S4 (reflexive+transitive, **non-Euclidean**) structure DDB's hard direction reconstructs; LI gets it dynamically |
| **endorsement / Reflection** | `P_A(X∣P_B(X)=y)=y` (van Fraassen); "A endorses B" | the radical-probabilist root concept; Total Trust is its decision-theoretic strengthening; LI's Self-Trust is the *weakened* endorsement that survives self-reference |

---

## 3. What the existing Lean (`lean-deference/LeanDeference.lean`) actually contains

**Confirmed sorry-free, axioms `[propext, Classical.choice, Quot.sound]` only (established; do NOT
recompile).** Three namespaces. For each: name → informal meaning → fidelity note.

**`Deference` (finite exact algebraic backbone, defects = 0):**
- **`decomposition`** — over any `CommRing`, any finite `W,J`, *for all* `π,P,O,α`:
  `gap_i = D_CM + D_UM_i + soft_i` where `gap_i = 𝔼_π(Σ α^j O^j) − 𝔼_π(O^i)`,
  `D_CM = Σ_w π_w Σ_j α^j_w(O^j_w − Σ_v P_{wv}O^j_v)`,
  `D_UM_i = 𝔼_π(E O^i) − 𝔼_π(O^i)`, `soft_i = 𝔼_π(Σ_j α^j E O^j − E O^i)`. *Pure linearity, no frame
  hypothesis* — universalizes sympy check A. **Fidelity: faithful and strong** (universal in the
  ring and the finite types).
- **`value_of_defects`** / **`value_of_CM`** — *conditional martingale (`D_CM=0`) + unconditional
  (`D_UM=0`) + argmax-nonneg soft term ⇒ Value gap ≥ 0*, exact finite. **Fidelity: faithful** to
  the `δ=0` shadow; `hCM`/`hUM` are taken as hypotheses (correct — they are the LI theorems).

**`DeferenceAsymp` (the actual §3 chain, in honest asymptotics):**
- `Approx a b := (a_n−b_n)→0` (= `≂ₙ`); `AsympLE a b := ∀ε>0 eventually a_n≤b_n+ε` (so `≳ₙ`).
  Reflexivity/symmetry/transitivity, `≂ₙ`-refines-`≲`, finite-sums-respect-`≂ₙ` proved from
  Mathlib `Filter`/`Tendsto`.
- **`value_asymptotic`** — the **five LI results enter as named hypotheses** (`hAdd1/hAdd2`=4.8.4,
  `hCcee`=4.12.3, `hCee`=4.12.1, `hδ/hSoft`=4.8.10∘softmax), conclusion `AsympLE (Eo i) ES`
  = Value. **Fidelity: this is the honest claim** — it verifies *the composition of the LI
  theorems is valid*, NOT the LI theorems themselves. The premises are exactly the trusted
  black-boxes; nothing smuggled.

**`DeferenceExtra` (two supporting facts, now proved not assumed):**
- **`softmax_lower_bound`** — softmax-weighted mean `≥ m_i − (card J)·δ`, from `Real.add_one_le_exp`.
  Discharges the analytic half of `hSoft`. (Cruder constant than the note's `δ·log(card J)`; fine
  for `δ→0`.) **Fidelity: faithful**, slightly weaker constant.
- **`CM_implies_immodest`** — the §5.2 core: if `E_w(X)=E_π(X∣fiber w)` for all `X` at world `w`,
  then `P_w(fiber w)=1` (immodesty), by instantiating at the fiber indicator. **Fidelity:
  faithful but partial** — it formalizes only the *algebraic* one-line step; the soft⇒hard "no
  spectral gap" reduction (the part that genuinely needs an infinite frame) is **left as prose**.

**What the Lean does NOT cover (the honest boundary):**
1. LUVs, the market/trader construction, the LI criterion — none formalized.
2. The genuine theorems 4.12.3/4.12.1/4.8.4/4.8.10 are **never proved**, only assumed.
3. The `≂ₙ` bookkeeping linking the asymptotic layer to the finite core (that `ccee`/`cee` actually
   force `D_CM,D_UM→0`) is **not** machine-checked — out of scope without formalizing LI.
4. The soft⇒hard / no-spectral-gap step of §5.2 (the load-bearing infinite-frame move).
5. **Everything in §10 (cross-agent / external-expert)** — no Lean at all.
6. Weatherson's Coin/Bentham, the DDB↔LI dictionary, Total-Trust⇒Value converse.

---

## 4. Ranked open questions (most-formalizable first)

Each is phrased as a candidate proposition/definition with the best formal setting. "Formalizable"
ranks by *proximity to existing machine-checked scaffolding*, not importance.

**Q1 (very high formalizability; LEAN-READY). Local / question-relative Value.** *Candidate:*
restrict the menu's LUVs to a fixed subclass `𝒳` (DDB §5 "local" deference); since `ccee` is
already local in `X`, the §3 chain should go through verbatim, giving *local Total Trust ⇔ local
Value*. **Setting: logical induction.** The finite Lean (`value_of_CM`) already proves the
algebra for *arbitrary* menus, so a local-restriction Lean lemma is a near-trivial specialization —
this is the cleanest first Lean target, and it settles a DDB *open conjecture*.

**Q2 (high; LEAN-READY). The §10 generalized Value as a standalone Lean theorem.** *Candidate:*
re-prove `value_asymptotic` with `Ee`/`Eo` interpreted as an **external** expert's estimates and
the *only* premise being cross-agent LUV-Total-Trust (`hCcee` toward `𝔼_exp`) — drop nothing else.
The existing `value_asymptotic` is *already expert-agnostic in its hypotheses* (it never mentions
"future self"), so the work is purely *interpretational*: write the plain-English claim, confirm
no premise secretly requires expert=self. **Setting: logical induction.** Pin down: is `hCee`
(line 6) genuinely needed for an external expert, or absorbed into `hCcee` at `w≡1`? (v2 §10 says
the latter — verify in Lean that the two-premise version collapses to one.)

**Q3 (high; algebraic). Soft⇒hard no-spectral-gap, finitely.** *Candidate proposition:* on a
finite frame, *soft* conditional martingale for all `δ<` (spectral gap) implies the *hard*
conditional martingale, hence (by `CM_implies_immodest`) immodesty. This is the one §5.2 step left
as prose. **Setting: probability frames (finite).** It is elementary real analysis (a gap argument
on finitely many values) and would *complete* the finite-collapse impossibility in Lean — pairing
with the existing `CM_implies_immodest` to close §5.2 entirely.

**Q4 (medium-high; CONJECTURE, the headline cross-agent question). Fast-Student/Slow-Teacher
merge (Eisenstat).** *[Attribution note, 2026-08-10: the lab's renderings of this conjecture do not
match the information structure Sam Eisenstat intended — AI reads human beliefs immediately, humans
see AI beliefs only at a delay; see `wiki/eisenstat-conjecture-attribution.md`.]* *Candidate
proposition (Sam's conjecture, AGENDA "Fast Student, Slow
Teacher"):* given a *slow trusted* inductor `H_t` and a *fast untrusted* `A_t`, define
`B_t := A_t`'s estimate of `H_{f(t)}`. *If* `A` has good feedback about `H` *and* `f` grows fast
enough, then (i) `B_t` is itself a logical inductor and (ii) `H_t` endorses `B_t` (LI-weak sense).
**Setting: logical induction (two inductors + a deferral schedule).** This is the constructive
payoff the whole agenda points at. Sub-questions to pin: what *is* "good feedback" (a market-
generability + a `≂ₙ`-convergence-of-`A`'s-`H`-estimates condition?); does (i) need the LI
criterion for `B` or follow from `A`'s? **This is the central CONJECTURE; reduce it to a precise
hypothesis set before any Lean.**

**Q5 (medium-high; the real characterization gap). When does inductor `N` LUV-Total-Trust inductor
`M`?** *Candidate definition-to-pin-down:* the LI analog of DDB's "`π∈CH(C_π)` and every `P_i`
modestly informed." For self (`M`=future self) it is *free* (`ccee`); for distinct inductors it is
**not** free (v2 §10.4). *Candidate:* `N` LUV-Total-Trusts `M` iff `M`'s estimates are
`N`-generable AND on every market-generable weight the cross defect `→0`; conjecture this holds on
subsequences with good feedback. **Setting: logical induction.** This is the single most important
*open* formal object in the whole note — name it precisely so Q4 can use it.

**Q6 (medium; INTERPRETATION→theorem). "Future self = join of all observable experts."** *Candidate
proposition:* if expert `E` is `N`-observable then `N`'s own day-`f(n)` self is a Blackwell
refinement of `E`, so deferring to the future self dominates deferring to `E`. **Setting:
probability frames / Blackwell–Geanakoplos, then ported to LI.** v2 §10.3(a) states it as
interpretation; making it a theorem needs a clean LI notion of "refinement" — plausibly: `E`'s
estimates are `𝔼_{f(n)}`-measurable. A finite-frame Blackwell version is fully formalizable now.

**Q7 (medium; bridges to legitimacy thread). Trust only on subsequences with feedback, and trust
*without* feedback.** *Candidate:* formalize "one inductor trusts another on subsequences with good
feedback" (AGENDA: stated as believed-true) vs. the *harder* unobservable case (human flourishing,
values, ethics — no feedback). **Setting: logical induction.** Pin the feedback-indexed
subsequence as a market-generable selector; the no-feedback case is where the "basin of
corrigibility" bootstrapping (AGENDA) must substitute for feedback — likely CONJECTURE-only for now.

**Q8 (medium; updatelessness, lateral). What "updates" will UDT defer to?** *Candidate definition:*
a generalized endorsement characterizing the improvements an *updateless* agent accepts (AGENDA
"Updatelessness" under DDBDB). Endorsement is neither necessary nor sufficient updatelessly
(counterfactual mugging, transparent Newcomb). **Setting: radical probabilism / UDT
(udt-representation-theorem/).** Connect to the existing **control-endorsement** definition
(`agency-via-endorsement.md`: "UDT agent is control-endorsed by its own prior") — candidate:
*UDT defers to update `u` iff `u` is control-endorsed by the prior*. Formalizable in the existing
endorsement Lean dir; high payoff for "open-minded updatelessness."

**Q9 (medium-low; reflective-oracles thread, Cole Wyeth). Belief-that-you're-UDT1.1 ⇒ ε-optimal.**
*Candidate proposition (AGENDA "Updatelessness"/Unbounded Embedded Agency):* if a UDT1.0 agent
`(1−δ)`-believes its policy is UDT1.1, then it is `ε(δ)`-optimal — replacing Cole's hand-built
oracle with the self-belief hypothesis. **Setting: reflective oracles
(`internal-fixpoint/reflective-oracles-project/`).** Less formalizable here (needs the rOSI /
reflective-oracle apparatus, not the LI scaffolding), and the AGENDA flags the self-knowledge
assumption itself as suspect (rules out self-modification). Pin first: a clean statement separating
*self-knowledge* from *environmental* modification.

**Q10 (low formalizability; foundational, high value). Diagonalization vs. the random-variable
trick.** *Candidate proposition:* DDB's beliefs-about-beliefs-as-random-variables is consistent
with full self-knowledge; Gödel's diagonal lemma makes that inconsistent under modest conditions
(AGENDA "Representational Issues"). *Candidate:* exhibit a self-referential `G="P_A(G)<½"` and show
the DDB frame must either drop perfect self-knowledge or the equivalence weakens — and that LI's
Self-Trust (4.12.4, soft) is *exactly* the surviving weakening. **Setting: logical induction
(self-reference is native) vs. probability frames.** This is the deepest agenda item; LI already
*answers* it (the soft/hard split), so the formal task is the *correspondence theorem*: LI
Self-Trust = the diagonal-robust weakening of Reflection.

**Q11 (low; corrigibility/legitimacy, mostly conceptual). Legitimacy as endorsement of a
process.** *Candidate definition:* a belief-formation process is *legitimate* for `A` iff `A`
endorses its outputs (`A` thinks it is truth-tracking); corrigibility = AI sees human
shutdown/modification as legitimate (AGENDA "Modeling Legitimacy"). **Setting: radical probabilism
/ endorsement, then LI.** Needs a process-level (not just belief-level) endorsement operator —
candidate: lift control-endorsement to endorsing the *training/deliberation map*. Formal payoff:
distinguish wireheading (illegitimate process) from genuine learning. Conceptually rich, far from
current Lean.

**Q12 (low; Vingean agency / intentional stance). Trust the chess-master without predicting them.**
*Candidate definition:* characterize "I can't predict the move but predict the win" — Vingean
agency — via a theory of abstraction (AGENDA "Agency & Abstraction"). **Setting: bespoke
(condensation / abstraction; `udt-representation-theorem/agency-as-condensation.md`).** Most
exploratory; least proximate to existing scaffolding, but it is the conceptual root of *why* the
deferral function `f` (Vingean future self) is the right model of trust at all.

---

### Quick triage for follow-on agents

- **Lean-first, low-risk:** Q1 (local Value), Q2 (external-expert Value re-statement), Q3
  (soft⇒hard finite). All sit directly on top of the confirmed `LeanDeference.lean` scaffolding.
- **Modeling-first, high-payoff:** Q4 (Eisenstat merge) + Q5 (cross-agent LUV-Total-Trust
  characterization) — these are the agenda's center of gravity; Q5 is a *prerequisite* for Q4.
- **Red-team targets:** the soft/hard split (Q3, Q10) and the §10 "future self = join of all
  observable experts" claim (Q6) are where a hidden immodesty assumption or a vacuity could lurk.
- **Cross-agenda bridges:** Q8 (UDT endorsement) and Q11 (legitimacy) reuse the existing
  `udt-representation-theorem/` endorsement Lean; Q9 lives in the reflective-oracles project.
