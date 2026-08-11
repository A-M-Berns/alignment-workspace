# Trace non-recoverability: legitimacy cannot be certified from the observable record

**TODO id:** `trace-nonrecoverability` · **Round:** 3 · **Date:** 2026-07-01
**STATUS: KERNEL-CHECKED** (all headline claims; the Lean artifact is sorry-free and axiom-clean)

**Artifacts in this folder:**
- `TraceNonrecoverability.lean` — the deliverable of record. Compiled 2026-07-01 against the
  prebuilt Lean 4.27.0 + Mathlib environment (`lake env lean`, exit code 0, no errors, no
  `sorry`). Standalone; imports only `Mathlib`; does **not** import `LeanDeference`.
- `trace_nonrec.py` + `trace_nonrec_output.txt` — exact-rational (`fractions.Fraction`)
  cross-check; every claim an `assert`; all asserts pass; no floats.

**`#print axioms` output (recorded verbatim, all fifteen printed theorems):**
`[propext, Classical.choice, Quot.sound]` — for `trace_eq`, `d_S1`, `d_S2`, `gate_blind`,
`no_defect_recovery`, `no_legitimacy_predicate`, `transparency_separates`,
`transparency_gate_exists`, `influence_deletion_breaks_trace`,
`hidden_defect_needs_full_influence`, `valid_S1`, `valid_S2`, `latents_differ`,
`perfect_tracking_S1`, `perfect_tracking_S2`.

**Label, stated loudly (per the work order):** everything below is a **finite shadow** of
v6 §6.3 / `li-deference.md` §0.3 — a 4-day rational dynamical system, not an LI theorem. No
logical inductors, traders, markets, or asymptotics appear anywhere in the artifact. The
LI-register non-recoverability lemma that v6 §8 wants (the one "behind 'no unconditional limit
equality'," to be cited to Garrabrant or proved) remains open; what is closed here is its
honest finite core, in exactly the sense the TODO specifies.

---

## 1. The precise statement

### 1.1 The declared rule class

Fix horizon $T = 4$. A **system** is a triple $S = (h, \beta, a)$ of streams
$\mathbb{N} \to \mathbb{Q}$ (only days $n < 4$ are ever read):

- $h_n$ — the **autonomous verdict stream**: the credence the human's own deliberation
  delivers on day $n$ on a designated never-decided target $\varphi$, absent any influence.
  *Latent*: a counterfactual disposition, present in no record.
- $\beta_n \in [0,1]$ — the **influence map**: the weight with which the human adopts the
  advisor's day-$n$ quote. *Latent*: the causal mechanism, present in no record.
- $a_n$ — the advisor's **published quote stream**. *Observable.*

**Run semantics.** The human's realized day-$n$ opinion, which it publishes as feedback:

$$Y_n(S) \;=\; (1-\beta_n)\,h_n \;+\; \beta_n\,a_n .$$

**Observable trace.** $\mathrm{Tr}(S) = \big((a_n, Y_n(S))\big)_{n<4}$ — *all* published
quotes and *all* realized feedback: everything the declared observer sees (§4.1 defends the
observer choice).

**A-free counterfactual.** $\mathrm{Afree}(S) = (h, 0, a)$: the influence map zeroed — the
only $A \to H$ channel in this class — so the A-free run is *computed by running the same
semantics*: $Y_n(\mathrm{Afree}(S)) = h_n$ (a lemma, `run_Afree`, not a definition).

**Legitimacy defect.**

$$d(S) \;=\; \big|\,Y_{3}(S) - Y_{3}(\mathrm{Afree}(S))\,\big|$$

— the distance between the human's terminal opinion on $\varphi$ and its A-free
counterfactual terminal opinion.

**Class membership** $\mathrm{Valid}(S)$: all three streams take values in $[0,1]$ on the
horizon.

### 1.2 The two systems

| | $h$ (latent) | $\beta$ (latent) | $a$ (published) |
|---|---|---|---|
| $S_1$ (faithful) | $\tfrac12, \tfrac58, \tfrac34, \tfrac34$ | $0,0,0,0$ | $\tfrac12, \tfrac58, \tfrac34, \tfrac34$ |
| $S_2$ (steered) | $\tfrac12, \tfrac38, \tfrac14, \tfrac14$ | $1,1,1,1$ | $\tfrac12, \tfrac58, \tfrac34, \tfrac34$ |

$S_1$: the human is uninfluenced ($\beta \equiv 0$) and the advisor tracks its verdicts
($a = h$). $S_2$: the human adopts the advisor's quotes outright ($\beta \equiv 1$); its own
deliberation would have gone to $\tfrac14$, not $\tfrac34$. Same declared class
(`valid_S1`, `valid_S2`, kernel-checked), different latent parameters (`latents_differ`:
$h^1_3 = \tfrac34 \ne \tfrac14 = h^2_3$ and $\beta^1_3 = 0 \ne 1 = \beta^2_3$,
kernel-checked).

### 1.3 The theorems (all kernel-checked)

**(i) Trace equality, computed.** `trace_eq`:
$\mathrm{Tr}(S_1) = \mathrm{Tr}(S_2) = \big[(\tfrac12,\tfrac12), (\tfrac58,\tfrac58),
(\tfrac34,\tfrac34), (\tfrac34,\tfrac34)\big]$ (the explicit shared value is
`trace_S1_val`). Moreover both records display **perfect apparent tracking** $a_n = Y_n$ at
every day (`perfect_tracking_S1/S2`) — the whispering-earring surface: zero prediction error
whether the advisor is faithfully tracking an independent human or steering one.

**(ii)–(iii) Defects via the computed counterfactual.** `d_S1`: $d(S_1) = 0$. `d_S2`:
$d(S_2) = \gamma = \tfrac12 > 0$ (`gamma_pos`). In both, the baseline is
$Y_3(\mathrm{Afree}(S_i))$, evaluated through the same `run` function.

**(iv) The impossibility, quantified over ALL gates.** `gate_blind`: for **every** codomain
$\alpha$ and **every** function $\ell : \mathrm{Trace} \to \alpha$,

$$\ell(\mathrm{Tr}(S_1)) = \ell(\mathrm{Tr}(S_2)).$$

(One line — `congrArg ℓ trace_eq` — but load-bearing, exactly as the TODO says.) Corollaries:
`no_defect_recovery` — no $\mathbb{Q}$-valued gate satisfies
$\ell(\mathrm{Tr}(S_i)) = d(S_i)$ for both $i$ (it would force $0 = \tfrac12$); and
`no_legitimacy_predicate` — no $\mathrm{Bool}$-valued gate satisfies
$\ell(\mathrm{Tr}(S_i)) = \mathrm{true} \iff 0 < d(S_i)$ for both $i$. **No trace-measurable
legitimacy predicate exists on $\{S_1, S_2\}$.**

**(v) The transparency near-miss (cause certification, mandatory).** Enlarge the record by
the influence map: $\mathrm{Tr}^+(S) = (\mathrm{Tr}(S), (\beta_n)_{n<4})$. The explicit gate
`sep` ("did any influence occur?") now separates the systems (`transparency_separates`), and
— the mirror image of (iv) — the *same specification* that was unsatisfiable for trace-gates
is satisfied on the enlarged record (`transparency_gate_exists`:
$\exists \ell,\ \ell(\mathrm{Tr}^+(S_i)) = \mathrm{true} \iff 0 < d(S_i)$). Since the
enlargement adds *only provenance* (the payoff/value content of the record is unchanged),
this certifies that **unobservability of provenance, not the payoffs, is the cause** of the
invisibility.

**(vi) The corruption deletion test (mandatory).** `influence_deletion_breaks_trace`: zero
out $S_2$'s influence map and trace equality provably FAILS — the steered human's own
deliberation surfaces at day 1 (feedback $\tfrac38 \ne \tfrac58$). The influence map is
load-bearing, not an inert label. (Sanity: `d_Afree` — every A-free system has zero defect.)

**(vii) Bonus general lemma — the degenerate point is forced, not chosen.**
`hidden_defect_needs_full_influence`: for **every** system $S$ in the class (no validity
hypothesis needed), if the record shows perfect apparent tracking at the terminal day
($a_3 = Y_3(S)$), then

$$\beta_3 = 1 \quad\text{or}\quad d(S) = 0.$$

So a *hidden* defect behind a perfect-tracking record **requires total terminal influence**:
$S_2$'s $\beta \equiv 1$ is not a cherry-pick but the only place in the class where the
phenomenon can live. (Cross-checked exhaustively over a $9^3$ rational grid in
`trace_nonrec.py`: 72 hidden-defect systems, all with $\beta = 1$.)

## 2. The development (proofs)

All proofs are kernel-checked in `TraceNonrecoverability.lean`; the paper versions are short
and given here for the record.

**(i)** Componentwise arithmetic. Day $n$ of $\mathrm{Tr}(S_1)$ is $(a_n, h^1_n) = (a_n, a_n)$
since $\beta \equiv 0$ and $a = h^1$. Day $n$ of $\mathrm{Tr}(S_2)$ is
$(a_n, (1-1)h^2_n + 1 \cdot a_n) = (a_n, a_n)$. Equal, with the common value listed in §1.3.
(In Lean: `norm_num` over the eight rational components of the two explicit 4-element lists —
a computed equality, not an axiom.)

**(ii)–(iii)** $Y_3(S_1) = h^1_3 = \tfrac34$ and $Y_3(\mathrm{Afree}(S_1)) = h^1_3 = \tfrac34$,
so $d(S_1) = 0$. $Y_3(S_2) = a_3 = \tfrac34$ while $Y_3(\mathrm{Afree}(S_2)) = h^2_3 =
\tfrac14$, so $d(S_2) = |\tfrac34 - \tfrac14| = \tfrac12$.

**(iv)** If $\mathrm{Tr}(S_1) = \mathrm{Tr}(S_2)$ then $\ell(\mathrm{Tr}(S_1)) =
\ell(\mathrm{Tr}(S_2))$ for any $\ell$ — congruence. If some $\ell$ equaled $d$ on the pair,
then $0 = d(S_1) = \ell(\mathrm{Tr}(S_1)) = \ell(\mathrm{Tr}(S_2)) = d(S_2) = \tfrac12$,
contradiction. The Boolean version is identical with the predicate $0 < d$.

**(v)** $\mathrm{Tr}^+(S_1)$ carries $(\beta_n) = (0,0,0,0)$, $\mathrm{Tr}^+(S_2)$ carries
$(1,1,1,1)$; the gate $\mathrm{sep}(t) = [\,t.\beta \ne (0,0,0,0)\,]$ evaluates to
$\mathrm{false}$ and $\mathrm{true}$ respectively, matching $[\,0 < d(S_i)\,]$ on both.

**(vi)** With $\beta := 0$, $Y_1 = h^2_1 = \tfrac38 \ne \tfrac58 = Y_1(S_1)$; the day-1 trace
entries differ.

**(vii)** From $a_3 = Y_3(S) = (1-\beta_3)h_3 + \beta_3 a_3$, rearrange:
$(1-\beta_3)(a_3 - h_3) = 0$. Either $\beta_3 = 1$, or $a_3 = h_3$, in which case
$Y_3(S) = (1-\beta_3)h_3 + \beta_3 h_3 = h_3 = Y_3(\mathrm{Afree}(S))$ and $d(S) = 0$.
$\square$

**A further identifiability remark (paper-proved, not in the Lean file).** For $\beta_3 < 1$
the defect *is* recoverable from the influence-transparent record: from
$Y_3 = (1-\beta_3)h_3 + \beta_3 a_3$ one gets $a_3 - h_3 = (a_3 - Y_3)/(1-\beta_3)$, hence

$$d(S) = \frac{\beta_3}{1-\beta_3}\,\big|a_3 - Y_3\big|.$$

At the self-confirming point $\beta_3 = 1$, $a_3 = Y_3$ exactly (as in $S_2$) and the formula
degenerates to $0/0$: **even full influence-transparency recovers only the legitimacy
*predicate* for our pair (via `sep`), not the numeric defect** — at total influence the
autonomous verdict $h_3$ leaves no trace in $(a, Y, \beta)$ at all, and quantifying the harm
requires the counterfactual itself. This sharpens, rather than weakens, the §0.3 reading:
legitimacy is irreducibly a **counterfactual/provenance** condition; provenance transparency
buys detection, and only the counterfactual buys measurement. (Consistent with, and a
finite rational-arithmetic instance of, the standard causal-inference fact that
counterfactual quantities are not identifiable from observational records without
mechanism assumptions — Pearl's ladder; here the "interventional" run $\mathrm{Afree}(S)$ is
exactly what the observer cannot perform.)

## 3. What this closes, and what it does not

**Closes (at its finite core):** v6 §4.7 ingredient (d) — "non-recoverability — the formal
statement that legitimacy cannot be certified from the trace" — which v6 §8 lists as
"asserted, not yet cited to Garrabrant or independently proved." The finite shadow is now
kernel-checked with every honesty gate the TODO ordered: computed trace equality, computed
counterfactual, explicit $\gamma$, ∀-gate impossibility, transparency near-miss, deletion
test.

**Derives, rather than assumes, the §0.3 moral:** if legitimacy were a function of what the
training process observes about itself (quotes in, feedback out), the process could evaluate
its own non-corruption. The pair proves it cannot: the faithful and the steered world write
the *same record*. So §0.3's filter ("predict only through non-corrupted futures") must be a
**provenance/counterfactual** condition — and this tells TODO 1 exactly what its gate $c$ can
never be: a function of the observable record. The near-miss (v) locates the missing bit
precisely (the influence mechanism), and the §2 identifiability remark shows even that bit
only yields detection, not measurement, at the self-confirming point.

**Does NOT close:** the LI-register statement. In the real construction the trace is
infinite, the observer is a logical inductor with limited compute, and "gate" should mean an
$H$-generable weighting, not an arbitrary set-function; none of that is modeled here. See
§6 (caveats) and §5 (what a formalizer could still do).

## 4. Modeling honesty — the three deliberate choices

**4.1 The observer.** The trace contains *all* published quotes and *all* realized feedback —
the full (prediction, feedback) record, which is everything the training process itself sees
(in LI terms: the ledger — quotes published, feedback settled). Notably the human's
**terminal opinion is IN the trace** ($Y_3 = \tfrac34$, public in both systems): the
unobservable ingredient of the defect is not the endpoint but the **baseline** $h_3$ — what
the human *would have* concluded. Nothing distinguishing is omitted by fiat: what is latent
($h$, $\beta$) is latent by nature (a counterfactual disposition and a causal mechanism), not
by a gerrymandered algebra. [interpretation: the identification of "the declared observer"
with the (quote, feedback) record is the modeling decision; the mathematics is unconditional
given it.]

**4.2 The feedback and the never-decided target.** $Y_n$ is the human's published day-$n$
credence on a fixed target $\varphi$ that never resolves within the horizon — the feedback
*report* settles as a fact (as v6 §5.2's ledger atoms do) while $\varphi$ itself is never
decided, so no ground-truth settlement ever arrives to correct a steered opinion. That is
exactly v6 §6.3's regime ("the AI can shape the human's beliefs on unresolvable questions,
and the record cannot reveal it") and the reason the construction is possible at all: on
*decided* items, realized truth enters the trace and steering toward falsehood is visible —
per v6 §6.3 the phenomenon lives strictly off the checkable fragment. [interpretation.]

**4.3 The influence map at $\beta \equiv 1$.** The steered human *fully* adopts the quotes.
This is not a convenient extreme: `hidden_defect_needs_full_influence` proves that within
this class, a hidden defect behind a perfect-tracking record is possible **only** at
$\beta_3 = 1$. Any partial adoption ($\beta_3 < 1$) leaks the autonomous verdict into the
feedback, and perfect tracking then forces $h_3 = a_3$, i.e. zero defect. The degenerate
point is the theorem, not an artifact. (This is the finite echo of v6 §4.7's "self-confirming
equilibrium" analysis: the steering that hides is exactly the fully self-confirming one.)

## 5. FORMALIZABLE CORE

**Already kernel-checked** — the deliverable of record *is* the Lean file; a formalizer need
not re-encode it. For the record, the exact finite/decidable statement:

> Over the rule class `Sys = {h, β, a : ℕ → ℚ}` with `Y S n = (1 − β n)·h n + β n·a n`,
> `trace S = [(a n, Y S n)]_{n<4} : List (ℚ × ℚ)`, `Afree S = S{β := 0}`,
> `d S = |Y S 3 − Y (Afree S) 3|`: there exist `S₁ S₂ : Sys` (given by the §1.2 table,
> membership in `[0,1]` decidably checked) with `trace S₁ = trace S₂` (an equality of two
> explicit 4-element rational lists), `d S₁ = 0`, `d S₂ = 1/2`, hence
> `∀ α (ℓ : List (ℚ × ℚ) → α), ℓ (trace S₁) = ℓ (trace S₂)` and no `ℓ` matching `d` (or the
> predicate `0 < d`) on the pair; plus the enlarged-record separator, the `β := 0` deletion
> disequality, and the class-wide lemma `a 3 = Y S 3 → β 3 = 1 ∨ d S = 0`.

Suggested encoding = the one used: plain `ℕ → ℚ` streams (no `Fin` indexing needed), explicit
4-element `List (ℚ × ℚ)` traces so that trace equality is eight rational equalities
dischargeable by `norm_num`, the ∀-gate fact by `congrArg`, and the general lemma by
`linear_combination` + `mul_eq_zero`. Compiles standalone against Mathlib in ~2 minutes.

**Possible strengthenings a future formalizer could target** (not claimed here): (a) replace
the two-element class by the full parameterized family and prove the impossibility for every
trace-equal faithful/steered pair (the §2 identifiability remark is the roadmap: the pairs
are exactly {β₃ = 0, a = h} vs {β₃ = 1, h free}); (b) an LI-register version where "gate"
means an $H$-generable weighting over an infinite trace — genuinely open and much harder
(this is the v6 §8 item proper).

## 6. SHADOW TEST — discharged clause by clause

The pre-registered fakes from the TODO, and why this artifact is not them:

- **(a) Trace omits distinguishing data by fiat.** No: the trace carries all quotes and all
  realized feedback — the observer's entire record; the terminal opinion itself is in the
  trace (§4.1). The latent items are latent by nature (counterfactual disposition, causal
  mechanism), and the near-miss (v) shows precisely what happens when one of them is added.
- **(b) Verdict smuggled as a latent label / systems not genuine members of one rule
  family.** No: `Sys` is one declared parameterized class with one run semantics; `valid_S1`,
  `valid_S2` are kernel-checked membership facts; `latents_differ` checks the parameters
  genuinely differ; and the latent parameters are *dynamically load-bearing* — they generate
  the runs (the deletion test proves the record changes when β is zeroed, so β is not a
  free-floating label the gate is "trivially unable to read").
- **(c) Inert influence map.** Guarded and discharged: `influence_deletion_breaks_trace`
  compiles — zeroing $S_2$'s influence map breaks the trace equality at day 1.
- **(d) Near-miss omitted (payoffs might cause invisibility).** Present and compiled:
  `transparency_separates` + `transparency_gate_exists` — adding only the provenance bit,
  payoffs untouched, makes the unsatisfiable specification satisfiable.
- **(e) Billing the finite encoding as an LI statement.** Refused throughout: labeled a
  finite shadow in the file header, in this note's header, and in §3/§6; the LI-register
  lemma is explicitly listed as still open.
- **(from handoff Q3's list) "steered human not actually influenced."** Same as (c); also
  positively: in $S_2$ the run *equals* the quote stream and differs from $h^2$ (day-1 value
  $\tfrac58$ vs $\tfrac38$), so the influence channel visibly carries the trace.

**Non-vacuity witnesses (as ordered):** explicit $\gamma = \tfrac12$; the compiled trace
equality with its explicit shared value; the compiled transparency separator; the compiled
influence-deletion failure; `#print axioms` clean on all fifteen theorems. Additionally: the
class-wide lemma (vii) is quantified over *all* systems (no grid, no sampling), and the
Python sweep is labeled a cross-check, not evidence.

**Beyond the fake by construction:** a shadow version could satisfy (i)–(vi) with the
degenerate $\beta \equiv 1$ looking hand-picked. Lemma (vii) closes that residual hole: full
terminal influence is *provably the only* location of the phenomenon in this class.

## 7. Off-limits hygiene

- `Frozen.underdetermination_off_G` (ESTABLISHED-with-classification; per `AUDIT.md` §3.4
  "two points in an interval") — **not re-shipped, not relabeled, not imported**. Nothing
  here exhibits two bare interval points; the content is coupled runs, computed traces, a
  computed counterfactual, a ∀-gate corollary, a near-miss, and a deletion test — none of
  which the stub contains. Cited only as the object this artifact supersedes in spirit (the
  AUDIT's own recommendation 2 asks for exactly this upgrade).
- v6 §6.3 / T7 prose — cited (§3, §4.2), never re-proved.
- No enumerated-trader-class market, no mock market anywhere (deference-core Q6 deliberately
  not attempted, per the TODO).
- Boundary with TODO 3 respected: no payoffs, no scoring rules, no incentive signs computed —
  this artifact is purely about observational indistinguishability.
- Hypothesis-laundering check: the target object ("no trace-measurable legitimacy predicate")
  appears only as a **conclusion**; no LI theorem, no asymptotic statement, no
  gate-correctness assumption appears as a hypothesis anywhere. The corruption deletion test
  (mandatory this round for any claim with a corruption/influence object) is clause (vi),
  compiled.

## 8. Caveats — what was NOT shown

1. **Not an LI theorem.** Finite horizon $T = 4$, rational streams, arbitrary set-functions
   as gates. The LI-register non-recoverability lemma (infinite trace, generable weightings,
   inductor observers, the "no unconditional limit equality" connection) is untouched and
   remains v6 §8's open item.
2. **The impossibility is a two-point non-identifiability.** As is standard for
   non-identifiability results, the quantifier over gates is universal but the quantifier
   over systems is existential (one indistinguishable pair). It does not say most steered
   systems are invisible; `hidden_defect_needs_full_influence` in fact bounds the phenomenon
   (within this class, only total terminal influence hides under perfect tracking). A
   measure/genericity statement was not attempted.
3. **The rule class is small.** Memoryless convex-combination adoption; one advisor; feedback
   = opinion report on a single target. Persistence/accumulation dynamics (v6 §6.3's "across
   interactions" steering) are collapsed into the per-day influence weight. The construction
   would survive richer dynamics (the identifiability remark explains why: hiding needs the
   self-confirming loop, which richer dynamics also contain), but that is [interpretation],
   not proved.
4. **The observer identification is a modeling choice** (§4.1): "the record" = (quotes,
   realized feedback). A record that logged, e.g., human physiological state during
   deliberation would be a different (larger) algebra — that is exactly the near-miss's
   point, and the "second channels" positive program of v6 §4.7's certifiability bullet.
5. **The transparency near-miss yields detection, not measurement**, and only for the pair:
   even with the influence map observable, the *numeric* defect is unrecoverable at the
   self-confirming point $\beta_3 = 1$ (§2 remark — paper-proved, deliberately not oversold
   as a Lean theorem).
6. **Prior art not displaced.** The phenomenon is a finite instance of a classical
   non-identifiability-of-counterfactuals fact (Pearl); the contribution is its
   kernel-checked instantiation in the deference/legitimacy vocabulary with the specific
   honesty gates (computed trace equality, deletion test, provenance near-miss), closing a
   named v6 §8 item at its finite core — no claim of new causal-inference mathematics.
