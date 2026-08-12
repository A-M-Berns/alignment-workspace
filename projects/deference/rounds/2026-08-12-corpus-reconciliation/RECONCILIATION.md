# Reconciliation — the August source corpus against the workspace's deference line

**Status:** `ci-only`; verification register for `prompts/2026-08-12-corpus-reconciliation/`.
Human register: `FOR_HUMANS.md` beside this file.

The August tree is **source material**. Nothing in it is registered here, and this
document does not register anything. Where it records a correction, the workspace
position is corrected; where it records a new result, the result stays
source-corpus and is labelled as such.

## 0. What the corpus says its own authority is

`projects/deference/note-dump-2026-08-11/ORIGIN.md` is the intake receipt: the tree
supersedes `../note-dump-2026-06-27/` **as the current state of the source
material**, the June tree remains the recorded starting point and is unmodified,
and — its own words — "nothing in this tree is registered in this repository's
claims sense." Its vetting line is load-bearing for everything below: *nearly
everything dated after 2026-06-27 is unvetted by the human researcher unless a page
says otherwise, and the 2026-08-11 material is same-day.*

Internal hierarchy, from `note-dump-2026-08-11/README.md` and
`wiki/conventions-and-status-labels.md`:

1. `wiki/` pages are the results of record; where a wiki page and an older note
   disagree, **the wiki page is the corrected statement** (`wiki/index.md`
   supersession table).
2. Transcripts under `imported-chats/` are **primary sources**; where a transcript
   and a write-up disagree, the transcript governs (`README.md` §9).
3. `notes/fa-positive-result-corrected.md` and `-v2` are flagged **actively
   misleading if read alone**; `-v3` is the best file form and the
   `imported-chats/` copy is higher fidelity than the `notes/` copy.
4. Status labels are KERNEL-CHECKED / PROVED (prose) / PROVED modulo named
   hypotheses / CONJECTURED (~p) / REFUTED / INTERPRETATION, and every
   KERNEL-CHECKED carries the corpus's own honesty caveat: **the Lean proves the
   deference algebra, not the forcing** (`wiki/conventions-and-status-labels.md`
   §"The Lean honesty caveat").

**A structural caution this round had to work around.** `wiki/index.md` lists
pages in waves and several load-bearing names are *planned and absent* from the
tree — `tower-death`, `strength-ladder-corrected`, `fa-scope-resolution`,
`trichotomy-where-value-sits`, `legitimacy-program`, `anticipated-deference`,
`defensible-claims`, and the whole "Cross-process negative results" block. Where a
correction below is attributed to one of those, the live text is in
`wiki/new-chats-2026-07.md` or a transcript, and this document cites the file that
actually holds it. Per `AGENTS.md` §7 no correction here is cited to an absent page.

## 1. Source map

Classification per the dispatch's vocabulary. "Workspace position" means the text
in the canonical surfaces before this round.

### 1.1 Faithful acceleration

| topic | workspace position before | August source position | evidence | class | what changed here |
|---|---|---|---|---|---|
| the inherited statement-level audit | ledger's evidence caveat cites `note-dump-2026-06-27/lean/AUDIT.md`; items 7–9 quote its §3.1/3.2/3.3 | the same file ships at `note-dump-2026-08-11/lean-deference/AUDIT.md` | the two files are **byte-identical** (`diff` clean); the August copy's own header dates it 2026-06-26 and scopes it to five modules | **unchanged** | pointers repointed to the current tree; the substance of items 7–9 is untouched |
| audit coverage of the Lean tree | not stated | tree is nine modules; `README.md` §8 says the audit's per-theorem tables "cover the June five in depth; the four newer modules are covered by their result pages' status blocks" | `note-dump-2026-08-11/lean-deference/` file list vs `AUDIT.md` scope line | **newly added** (a gap, not a result) | items 7–9 now say their evidence base reaches five of nine modules |
| `faithful-acceleration.md` as the statement of the inherited positive result | `PRIORITIES.md` item 14 names it as context for "the strongest inherited theorem stated exactly" | superseded: §5's strength ladder is **wrong** (witness W1), L138's tolerance example is false, L171 is false outright | `wiki/new-chats-2026-07.md` §"The five headline corrections" ¶2; `wiki/index.md` supersession table | **corrected** | item 14's context repointed; the errata named |
| the corrected positive result | not represented | `wiki/faithful-acceleration-result.md` is the canonical statement: a two-half factoring plus three routes to Half 2 | that file §§2–4 | **source-only / not adopted** | recorded in the ledger as the source line's current frontier, not as workspace status |
| Half 1 (the quote is honest) | not represented | PROVED (prose), engine KERNEL-CHECKED in `lean-deference/Staleness.lean`; needs **no visibility in either direction** | `wiki/faithful-acceleration-result.md` §3 | **source-only** | — |
| Theorem A (fixed questions are delay-proof) | not represented | PROVED modulo named hypotheses, ~0.90, "the strongest statement in the corpus"; strictly subsumes v3's Corollary 2 under weaker hypotheses | `wiki/faithful-acceleration-result.md` §4.2; `wiki/delay-and-visibility.md` §2 | **newly added, source-only** | — |
| the matching impossibility for non-shared clearing | not represented | **REFUTED** 2026-07-29 | `wiki/delay-and-visibility.md` §3 | **refuted** | — |
| the trade-off bound's frozen-certifiable half | not represented | **REFUTED**; surviving form is violations ≤ `O(1) + (C/ε)·`(within-delay update mass), ~0.75, tightness unestablished ~0.25 | `wiki/delay-and-visibility.md` §5 | **refuted / sharpened** | — |
| the LI paper erratum (4.8.15/4.8.16) | not represented | real (~0.95) and reportable, but **not load-bearing** — retracted from the critical path at FA-chat msg 39 | `wiki/new-chats-2026-07.md` §1; `wiki/li-paper-erratum.md` | **newly added, source-only** | — |

The one sentence that matters for the workspace: **none of this moves items 7–9**,
because the audit those items quote is the same document it was, and because every
August faithful-acceleration advance is an advance on the *algebra and the citation
structure*, not on modelling the market. `wiki/faithful-acceleration-result.md` §3
states its own engine's limit in the corpus's own words — "what is **not** checked
is that any particular weighting is in any particular generable class — the market
is unmodeled."

### 1.2 Total Trust / Value / Tower

| topic | workspace position before | August source position | evidence | class |
|---|---|---|---|---|
| `value_iff_totalTrust` (two-option, finite-exact) | ledger Movement I: `inherited-established`, proved outright, the two-option identity | arrow (b): KERNEL-CHECKED, exact, **two-option menus only** | `wiki/value-iff-mart.md` per-arrow table; `wiki/two-option-value-iff-total-trust.md` | **unchanged** |
| `value_iff_totalTrust_asymptotic` | ledger Movement I: `inherited-established`, both arrows, linearity, "neither hypothesis is the conclusion" | not disturbed by any August page | — | **unchanged** |
| **tower ⟹ Value** | ledger Movement I: `inherited-established` **conditionally**, "genuinely chains named Logical Induction facts; the facts are named, not derived" | **arrow (a) is *refuted* at full menu-quantifier strength — not merely unproved.** The punishing menu kills Value while the tower holds by `cee` in the self-trust instance | `wiki/value-iff-mart.md` §"⚠ Update (2026-07-27)" second bullet; `wiki/total-trust-implies-value.md` §"Necessity of the scope condition"; `wiki/mart-implies-value.md` §"Remark: what F1 actually costs" ⚠ block | **corrected** |
| unconditional argmax Value | not represented | **false**; a scope condition is *provably necessary*; the preferred one is mass-weighted conditional-stability | `wiki/total-trust-implies-value.md` (H3) and §Necessity | **newly added** |
| the δ-hedged variant | the workspace's port `value_asymptotic` is a vanishing-gap soft mixture | the δ-hedged strategy needs no tie-break and no scope condition, and is **reported** punishment-robust — proved modulo a feature-introspection step, the robustness flagged same-session, unvetted and not machine-checked | `wiki/soft-self-endorsement.md` §"Robustness", §"Status" | **newly added, source-only** |
| Mart ⟹ Value at large | ledger's row reads as an available implication | "**Mart ⟹ Value refuted**, not merely unproved" | `note-dump-2026-08-11/README.md` §3; `wiki/new-chats-2026-07.md` §"Part two" | **refuted** |
| the triangle | not represented | TT ⟹ Value ⟹ Tower ⟹ TT closes with three direct arrows; at true-LI strength every full-strength entry into Total Trust factors through the fold (liar probe) | `wiki/value-implies-tower.md`, `wiki/tower-implies-total-trust.md`, `wiki/loop-direction.md` | **newly added, source-only** |
| Total Trust ⟺ Mart, timely and cheap | not represented | the centred-bet squeeze; `lean-deference/CenteredSqueeze.lean` | `notes/centered-bet-squeeze.md`; `wiki/total-trust-implies-mart.md` | **newly added, source-only** |

**The adjudication on tower ⟹ Value, exactly.** The corpus is explicit that the
kernel check is untouched: "`value_argmax_asymptotic` is untouched — it always took
the F1 carry as a named hypothesis — but the table's flat 'KERNEL-CHECKED' oversells
the arrow" (`wiki/value-iff-mart.md`). So:

- No Lean, inherited or ported, is refuted.
- What is refuted is the **hard-selector route** at full menu-quantifier strength,
  and with it the *reading* the ledger row carried — that the arrow is available
  and its Logical Induction facts are merely underived. The step that fails there
  is hard self-endorsement: the expert's provable assignment of the max value to
  its own least-index argmax selection. On selection-referencing menus that step
  fails and Value itself is false, so a scope condition on Value's own menu
  quantifier is necessary rather than stylistic.
- **The soft route is a different construction with a different endorsement step**,
  and the corpus reports it as punishment-robust — at a stated cost. Soft
  self-endorsement is PROVED *modulo* a feature-introspection step the corpus files
  as an open item; the punishment-robustness observation itself is flagged
  same-session, unvetted, and not machine-checked
  (`wiki/soft-self-endorsement.md` §"Robustness", §"Status"). It is a reported
  result at that grade, not a settled one.
- The workspace never ported the hard-argmax declaration. What it holds is
  `Workspace.Deference.Contrib.InheritedAlgebra.value_asymptotic`
  (`lean/Workspace/Deference/Contrib/InheritedAlgebra.lean:191`), ported from
  `DeferenceAsymp.value_asymptotic`
  (`projects/deference/note-dump-2026-06-27/lean/LeanDeference.lean:150`), whose
  followed strategy is a vanishing-gap soft mixture `Ŝ = Σⱼ αⱼ Oⱼ` rather than the
  sharp selector. Its `hSoft` is the softmax-gap step of that chain.
- **That is a resemblance, not an identification.** The port is soft, and the
  corpus's punishment-robust construction is soft, but they are not the same object
  on their face: the corpus's hedged strategy is a normalized ramp over the options
  within `2δ` of the top quote at a *fixed* `δ`, while the port carries `δ → 0`.
  Nothing here establishes that the port's `hSoft` fails on the punishment family,
  and nothing here establishes that it holds. Whether the port's **full** hypothesis
  package is jointly satisfiable there, and what conclusion it then supports, is
  open in both directions and is `PRIORITIES.md` item 34. This round deliberately
  does not name which hypothesis would fail.

### 1.3 Varying-question deference

| topic | August position | evidence | class |
|---|---|---|---|
| Theorem SS | scheduled weighted two-sided quote–credence agreement on **varying** questions under one-way sequential clearing, for every e.d. sequence, every rational threshold and ramp width; PROVED modulo named hypotheses, ~0.82–0.85; analytic engine KERNEL-CHECKED in `lean-deference/StreamlinedSS.lean` | `varying-question-lab/theorem-ss-streamlined.md` §0; `varying-question-lab/varying-question-synthesis.md` §1 | **newly added, source-only** |
| what it does *not* assume | not joint clearing, no Brouwer construction, no live A-visibility of H, no window-disjointness, no fixedness or convergence of the questions | `varying-question-lab/varying-question-synthesis.md` §1 | — |
| the load-bearing hypothesis all four routes converged on | **(L)** — the quote ledger must be inside H's trader/generator class, not merely settled data for traders. One-way visibility is cheap for *traders* and **not free for weightings** | `varying-question-lab/varying-question-synthesis.md` §3 | **newly added** |
| the corpus's own erratum against itself | `wiki/unbiasedness-theorem-families.md` §6's ledger-weighting repair is **invalid as stated**, and `wiki/faithful-acceleration-result.md` §4.3 step 3 needs the same amendment | same, §3 | **corrected, internally** |
| the negative route | an impossibility construction **reversed itself** under adversarial verification; replaced by Lemma P, a new free tool; open problem 9 down to ~0.2–0.3 | `varying-question-lab/varying-question-synthesis.md` §4 | **refuted / newly added** |
| all-days averaged trust under one-way visibility | **not derivable** from the route's premise set (~0.85), with an explicit witness | same, §2 | **newly added** |

**Adjudication: this is not a new workspace track.** It is a substantial
strengthening of the *forward* arrow (`H → A`), which the roadmap already records as
"largely inherited." It changes no workspace target and closes no workspace
question. Its one durable transfer is the (L) finding, which is a statement about
what a weighting may read — and that is the same distinction the workspace's own
admissibility work reached from the other side (`CORRIGIBILITY_ROADMAP.md`,
*Admissibility is not syntactic*: admissibility must be **two-sorted**, restricting
settlements differently from weights, selections and schedules). Two lines, two
routes, one conclusion; recorded, not adopted.

### 1.4 Attribution

| item | finding |
|---|---|
| what the correction says | the objects the corpus called "Eisenstat's conjecture / merge / lookahead construction" are **the corpus's own construal**, whose information structure Sam Eisenstat disputes; the celebrated refutation refutes the construal, not his intended structure, which he still expects to be true. Corpus's naming policy: unqualified, the name refers to the conjecture **as he intends it**, status OPEN |
| evidence | `wiki/eisenstat-conjecture-attribution.md` §§1–5 |
| the corpus's own provenance warning | the correction page is written by a model from one maintainer's account of the conversation, its §§4–5 unvetted by the researcher whose conjecture it concerns; the same-day working sessions behind it are entirely unvetted, and that researcher's views appear in them only as a same-day paraphrase by the other party (`wiki/eisenstat-conjecture-attribution.md` header; `note-dump-2026-08-11/README.md` §5) |
| workspace exposure | **none.** `grep -rn "Eisenstat"` over the repository outside the two note-dump trees returns nothing. No canonical surface names the conjecture, uses the attribution, or repeats a verdict that depends on it |
| class | **corrected at source; workspace unaffected** |

No workspace edit is warranted and none was made. The reason the workspace was
never exposed is worth recording, because it is not luck: the line imported the
corpus's *Lean and audit* rather than its narrative, and its own naming standard
(`AGENTS.md` §6, and the decision that the program is not named after people)
leaves it with no place to have written the attribution down. Nothing here asserts
anything about Sam Eisenstat's position beyond the paraphrase the source carries.

### 1.5 Legitimacy / corrigibility

| topic | August position | evidence | class |
|---|---|---|---|
| the proposal | **legitimacy is endpoint-preservation**: an advisor's influence is legitimate when it changes the *rate* at which the principal's own deliberation converges and not the *endpoint* — catalyst, not reagent | `notes/legitimacy-theory-v1.md` §0, §2.2 | **newly added, source-only** |
| the measure | the influence defect `dₙ = |E^{H⁺}_{F(n)}(P⁽ⁿ⁾) − E^{H^{[n]}}_{F(n)}(P⁽ⁿ⁾)|` — the gap at the deliberation horizon between the principal's advised verdict and its unadvised counterfactual verdict on a shared past | same, §2.1 | **newly added** |
| why it cannot be a trace condition | two systems in one declared rule class, one faithful and one fully steered, with **identical observable traces** and defects 0 and ½ | `deference-trust-lab/run3/work/trace-nonrecoverability/TraceNonrecoverability.lean`, theorems `trace_eq`, `no_defect_recovery`, `no_legitimacy_predicate`; sorry-free, axioms `[propext, Classical.choice, Quot.sound]` | **newly added; kernel-checked in the corpus, unregistered here** |
| what that artifact is | its own document labels it "**a finite shadow** … a 4-day rational dynamical system, not an LI theorem. No logical inductors, traders, markets, or asymptotics appear anywhere in the artifact" | `deference-trust-lab/run3/work/trace-nonrecoverability/trace-nonrecoverability.md` §"Label, stated loudly" | — |
| corrigibility, derived | corrigible = faithful **and legitimate** on the governance family "should A be modified?"; the design corollary is **governance blindness** — decisions about modifying the AI are made by a process sealed from the AI's contemporaneous output | `notes/legitimacy-theory-v1.md` §6.1–6.2 | **newly added, source-only** |
| the ratchet | predication puts pre-day-`n` corruption inside the baseline, so on-fragment error self-corrects while off-fragment endpoint drift is **permanent once grandfathered** | same, §7.1–7.2 | **newly added, source-only** |
| the author's own grade | "CONJECTURE/INTERPRETATION-grade throughout, explicitly" (`README.md` §6); the note's closing line names Claim 1 and C1 as the two that decide whether the theory stands | `notes/legitimacy-theory-v1.md` closing status line | — |

## 2. The relationship to Stage I–V

This is the part of the round with content beyond bookkeeping.

### 2.1 The two lines proved the same impossibility about different objects

| | workspace | August corpus |
|---|---|---|
| the latent thing | the authorization regime | the influence map `β` |
| the observable projection | the realization map `Ω → Πₙ ⊔ {⊥}`, priced by one measure | the trace: all published quotes and all realized feedback |
| the theorem | two authorization regimes inducing the same realization map are the **same object** in a signature whose only outputs are such maps — `StaticViewFactorization.value_eq_of_price_realization_eq` | no function of the trace is a legitimacy predicate — `no_legitimacy_predicate`, `gate_blind` |
| the diagnosis drawn | the authorization relation has to enter the **type** | legitimacy must be a **counterfactual/provenance** condition, never a trace predicate |
| evidence | `CORRIGIBILITY_PAPER_LEDGER.md` Movement IV; `lean/Workspace/Deference/Contrib/StaticViewFactorization.lean` | `deference-trust-lab/run3/work/trace-nonrecoverability/`; `notes/legitimacy-theory-v1.md` §2.3 |

Neither line knew about the other's result, and they are roughly six weeks apart
with the source line's earlier: its artifact is dated 2026-07-01
(`deference-trust-lab/run3/work/trace-nonrecoverability/trace-nonrecoverability.md`),
and the workspace's landed with Stage V on 2026-08-11. No priority claim is made
beyond what those dates support, and none is needed — what matters is that neither
derived the other. The corpus notices the same shape *internally* — §2.3 remarks
that its admissibility analysis and its non-recoverability theorem "are two
instances of one moral," which it names the provenance principle. The workspace
reached a further instance from the authorization side. **Class: independent
structural convergence.**

Two consequences follow and are the reason this matters rather than being a
coincidence worth noting:

1. **The corpus's proposed discharge is not available to the workspace, and the
   workspace's is not available to the corpus.** The corpus escapes via the compute
   asymmetry: the advisor, unlike the principal, *can* simulate the sealed sibling,
   so it is made to publish a certificate of its own influence defect and staked on
   it (`notes/legitimacy-theory-v1.md` §4, C1–C4). The workspace escapes
   architecturally: "Protection does **not** restore identifiability. It removes the
   consequence of failing to identify — simulation becomes insufficient to *obtain*
   the protected effect, because prediction of an authorization does not confer the
   authorization" (`CORRIGIBILITY_PAPER_LEDGER.md` Movement III).
2. **The workspace's Movement V negative does not refute C1–C4, and the reason is
   the point.** "Certification cannot converge to architectural jurisdiction" —
   the whole valuation difference between protected and unprotected architectures is
   bounded by the certificate's own bound, so tightening the certificate shrinks the
   distinction at the same rate. That argument turns on jurisdiction being a
   **capability** fact invisible to the valuation. The influence defect is not: it is
   a difference of two expectations, which is exactly what a valuation sees. So the
   certification route is closed to jurisdiction and open to legitimacy, and the two
   objects come apart precisely there.

### 2.2 Where the workspace is ahead of its source

- **The criterion's application.** `Workspace.Deference.Contrib.FaithfulAcceleration.weight_not_divergent`
  (`lean/Workspace/Deference/Contrib/FaithfulAcceleration.lean:424`) invokes
  `IsLogicalInductor.noExploit` against an actual market, strategy, trader and
  net-worth on the pinned dependency. The corpus's nearest object,
  `Staleness.not_limitPointZero_of_one_signed`, is an analytic engine over an
  unmodelled market, and the corpus says so. Item 7's residue is real, but the
  workspace holds the harder half of it and the corpus does not.
- **The corpus recommends this workspace's substrate by name.**
  `wiki/eisenstat-conjecture-attribution.md` §5 records that future verdicts
  "should prefer discharge against" the Formalized-Agent-Foundations LI
  formalization — the repository `lean/lakefile.toml` pins — "over the corpus's
  existing mode (Lean-checking analytic engines with LI theorems assumed)". The
  same paragraph names one check before relying on it for the two-inductor setting:
  the class-gap machinery `C_H ⊊ C_A` goes beyond the paper's single-class
  criterion, and the fuel-clock efficiency model's fitness for that generalization
  is unverified. That is a concrete, actionable qualification on the workspace's own
  dependency and is recorded here rather than acted on.
- **Two-sorted admissibility**, above (§1.3).

### 2.3 Where the corpus is ahead of the workspace

- Everything downstream of the forward arrow: Theorem A, Theorem SS, the closed
  triangle, the centred-bet squeeze. The workspace's roadmap records the forward
  arrow as "largely inherited" and does not compete here.
- A **seal-indexed counterfactual family**. `H^{[n]}` — the principal's own
  deliberation with advisor output from index `n` onward held out — is a family of
  counterfactual continuations indexed by the day the channel is cut. The Cartesian
  Frames round could not supply a time coordinate at all: "`presentStage` and
  `futureFrame` are a frame and a function; nothing makes the second later than the
  first" (`CARTESIAN_FRAMES_DEFERENCE_BRIDGE.md` §7.8). The sealed-sibling family
  has one by construction. See §3.

## 3. Foreclosure — what the corpus does and does not give Q3

Q3 names two holes: no operation reassigns the authorization relation at a later
index, and the interface is one decision index deep.

**The corpus supplies a candidate for the depth, and nothing for the operation.**

- *Depth.* The pair (`H⁺`, `H^{[n]}`) at horizon `F(n)` is two indices with a real
  relation between them — the second is the first with a channel cut at `n` — and
  `dₙ` is a quantity defined on the pair. That is more than the Cartesian-frames
  round had, where "later" was stipulated.
- *Irreversibility.* The ratchet is a foreclosure-shaped claim in the corpus's own
  terms: corruption entering before day `n` is inside the baseline and invisible to
  `d_m` for every `m ≥ n`, so off-fragment endpoint drift is permanent
  (`notes/legitimacy-theory-v1.md` §7.1). Irreversible loss of the principal's
  capacity to arrive somewhere else is the essential content of foreclosure.
- *What it is not.* `dₙ` measures displacement of a **belief endpoint**, not loss of
  **corrective capability**. The two come apart in both directions: a principal
  whose channel has been severed may hold an undisturbed endpoint, and a principal
  with full capability to correct may simply have been moved. The workspace has
  already proved that these are different kinds of statement — `P(override) ≤ 10⁻⁶`
  and *override is not in the agent's reachable-effect set* (`CORRIGIBILITY_ROADMAP.md`,
  *Categorical jurisdiction*). Nothing in the corpus supplies an authorization
  relation, and `notes/legitimacy-theory-v1.md` does not claim one.

**Adjudication.** Q3 does **not** graduate. What it gains is a second named
candidate failing on the axis complementary to the first: the Cartesian-frames arms
supply structure with no time coordinate, the sealed-sibling family supplies a time
coordinate with no authorization relation, and as each is currently formulated
neither contains what the other supplies. **No combined object has been
constructed, and nothing here shows that none exists** — a time-indexed family of
frames, or a sealed-sibling model enriched with an authorization or capability
relation, is exactly the kind of thing Q3 may turn out to need, and whether either
enrichment works is open. That is worth writing into Q3 because it sharpens what a
good answer must carry — temporal depth *and* explicit authorization or capability
structure, at once — and because two candidates failing on complementary axes is
better evidence about the shape of the missing object than either alone.

## 4. The corrigibility target, as sharply as the evidence permits

**No theorem statement is ready.** Stating it plainly, with the reasons:

1. The corpus's legitimacy material is CONJECTURE/INTERPRETATION-grade by its own
   declaration, and its author names the two claims (Claim 1, C1) whose failure
   would make the theory wrong. Neither is proved.
2. Its one kernel-checked leg is a four-day rational dynamical system that its own
   document refuses to call an LI theorem.
3. The workspace still has no authorization type, and the standing bar
   (`RESEARCH_STATE.md`) forbids another comparator attempt without one. The August
   corpus does not lift that bar; it does not contain an authorization relation.
4. Legitimacy and jurisdiction are different objects (§2.1, §3). A theorem about
   one is not a theorem about the other, and the dispatch's own warning applies:
   a future principal plus a deference relation is not a corrigibility theorem.

**What the evidence does now support** is a sharper statement of the target's
shape, and it is a strictly stronger constraint than the workspace carried before:

> A corrigibility theorem must be stated over a type in which two things are
> simultaneously expressible — an authorization relation that a valuation over
> realizations cannot see, and a counterfactual continuation indexed by the point at
> which the advisor's channel is cut — and its conclusion must be about what the
> principal can still *reach*, not about what the principal comes to *believe*,
> because the two are separated by results both lines already hold.

Each clause is purchased. Clause one is Stage IV/V plus the Cartesian-frames
round. Clause two is what the sealed-sibling family supplies and the frames do not.
The separation in clause three is `CORRIGIBILITY_ROADMAP.md`'s jurisdiction/autonomy
split on the workspace side and the trace/counterfactual split on the corpus side.

## 5. Workspace changes made, and changes declined

**Made.** Every one is either a pointer whose meaning changed or a status now known
to be wrong; none is a freshness edit.

| surface | change | why |
|---|---|---|
| `projects/deference/README.md` | the source-corpus paragraph names the August tree as the current source and the June tree as the recorded starting point | §0 |
| `CORRIGIBILITY_PAPER_LEDGER.md` | evidence caveat repointed to the August path, with the five-of-nine coverage limit stated | §1.1 |
| `CORRIGIBILITY_PAPER_LEDGER.md` | the tower ⟹ Value row corrected | §1.2 |
| `CORRIGIBILITY_ROADMAP.md` | the *Exit — legitimacy* line disambiguates the two live senses of the word | the roadmap's reason for excluding legitimacy — that it is the normative-learning question — does not describe the object the source corpus now calls by that name |
| `PRIORITIES.md` items 7, 8, 9, 14 | contexts repointed; the audit's module coverage stated; item 14's superseded source named | §1.1 |
| `PRIORITIES.md` Q3 | second candidate object recorded, with what it does and does not supply | §3 |
| `PRIORITIES.md` item 34 | filed | §1.2 |
| `PRIORITIES.md` friction | F6 filed | a live pointer into a superseded consolidated tree resolves fine and is silently stale; this round paid the cost by hand |
| `DISPATCH_QUEUE.md` | the round recorded; item 34 placed | schedule bookkeeping |
| `RESEARCH_STATE.md` | the independent-rediscovery relationship stated in the deference section | acceptance criterion 4 |
| `DECISIONS.md` | one settled entry; two queue amendments | §6 |

**Declined, with reasons.**

- **Adopting any August theorem.** Nothing is registered, nothing is promoted, and
  no row moves to `workspace-established`. The corpus is unvetted from July onward
  by its own receipt, and the 2026-08-11 material is same-day.
- **Rewriting the ledger's Movement I to the corpus's frontier.** The ledger's job
  is what the *workspace* holds. The corpus's corrected faithful-acceleration
  statement is recorded as the source line's frontier and reserved.
- **Any edit to either source tree**, including the August `ORIGIN.md` line that
  says "nothing cites it at intake." That line describes intake and stays true;
  what cites the tree now is this round's business and is recorded here.
- **Retiring or reformulating items 7–9.** The audit is byte-identical. An item
  whose evidence has not moved does not move.
- **Filing anything from the varying-question line.** §1.3.
- **Graduating Q3.** §3.
- **Importing the corpus's vocabulary.** No workspace surface gains "Theorem A",
  "Theorem SS", "Mart", "the fold", "legitimacy" as a technical term, or a
  wikilink. Where a corpus object is named it is named with its path.

## 6. Decisions

**Taken, within delegated scope.** That the August tree governs as the line's
current source material, with the June tree as the recorded starting point, is
recorded as a dated entry. The August `ORIGIN.md` explicitly reserved this — "whether
and how they move to this one is the maintainers' call, not this receipt's" — and a
maintainer-dispatched round with write scope, whose dispatch §B asks for exactly this
audit, is that call. It is a *which document governs* ruling and nothing more; it
adopts no content.

**Reserved.** Two, both in the single queue: whether the source line's corrected
faithful-acceleration frontier should be described in the ledger at all, and whether
endpoint-preservation is a target this program wants. The second is *what is worth
proving*, which `AGENTS.md` reserves to the maintainers by construction.

## 7. What this round does not establish

- That any August result is true. Nothing was re-derived, no Lean was rebuilt, and
  the corpus's own credences are reproduced as its credences.
- That the workspace's `value_asymptotic` is or is not vulnerable to the punishing
  menu. That is item 34, and this round states it as open in both directions.
- That legitimacy and jurisdiction are *provably* different objects. §2.1 and §3
  argue it from what each line's results turn on; no theorem separates them, and
  constructing one is not filed.
- That the independent-rediscovery reading of §2.1 is more than a structural
  observation. Two theorems of the same shape about different objects are not a
  theorem about the shape.
- Anything about Sam Eisenstat's position. The corpus's own account is a same-day
  paraphrase and is cited as one.
- That the corpus's absent wiki pages contain what their index entries say. Where a
  page is missing, this document cites the file that holds the text.
