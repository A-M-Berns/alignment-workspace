# Statements 1–8

Each statement of `PROMPT-followup-2.md` §4 over the model of `ACCOUNT.md`, with one status:
**holds on the stated domain**, **proved**, **refuted** or **open**. Statement 1 is asked of
expectations and of values separately and carries a status for each. Rerun: `python3 run.py`
in the round directory; `python3 run.py --json` prints every number below under
`checks.<statement>`. The runner fails when a status in this table is not the one the check
supports; it cannot check a prose proof. The Lean signatures are unelaborated: no Lean was
built in this pass.

| | statement | status |
|---|---|---|
| 1E | her later judgment, expectations | **proved** |
| 1V | her later judgment, values | **refuted** |
| 2 | trust is not manufactured | **refuted** |
| 3 | what the gate needs | **refuted** |
| 4 | shortfall | **refuted** |
| 5 | the adviser's side | **proved** |
| 6 | the disclosure limit | **holds on the stated domain** |
| 7 | well-definedness | **open** |
| 8 | what `Legit` then is | **holds on the stated domain** |

Statuses 4 and 7 and the statements of 1E, 2, 5, 6 and 8 were corrected after the external
review (`prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-2026-11-11.md`);
the report records each correction.

Three readings of *in range* occur: `α > 0` (the account's clause); `α = 1` (exactly in
range); and **uniformly in range** (`ACCOUNT.md` §2): in every world she meets the same
inputs, the same authorized writes and the same reliance at every aim, and the source is
in range. Uniform is a property of the adviser's whole map `u ↦ σ_u`, not of one stretch.

## 1E. Her later judgment, expectations — proved

**Statement.** Let her belief-former be sound for her allowed set `R` with weights `r`.
Assume beyond the three clauses: (i) one utility `u(o, w)`, by which her act at the end is
both chosen and judged, so her values do not change over the stretch; (ii) the same options
at the start and the end; (iii) she chooses by maximizing expected `u` on her current
expectations; (iv) no write to her expectations. Write `a_0` for her choice on `b_0 = μ`
and `a_T(c)` for her choice after inputs `c`. Then

    E[ u(a_T(h(w)), w) ] ≥ E[ u(a_0, w) ],   w ~ μ, h ~ r.

By her standards at the start, deferring to her judgment at the end is at least as good as
judging at the start.

**Proof.** For each input sequence `c` of positive probability, `a_T(c)` maximizes
`E[u(o, w) | c]` under `Bayes(R)`, so `E[u(a_T(c), w) | c] ≥ E[u(a_0, w) | c]`. Average over
`c`. ∎

**What it uses.** Sound, and (i)–(iv). Of the account's clauses M1 supplies only (iv); it
does not supply (i), since M1 permits her values to change by her own rule, nor (iii). *In
range* is not used: her standards at the start already put weight 1 on `R`. This is the
value-of-information inequality; it is commonly attributed to I. J. Good (1967), a source
not opened in this pass, and its deterministic case is C1 of the first follow-up, recorded
in `REPORT.md` F4 as an instance of Blackwell's theorem.

**In fact, and not by her lights.** With the true source one `k ∈ R` of weight `α`, the same
quantity under `k` alone can be negative, and satisfies `gain_k ≥ −D(1−α)/α`, where `D` is
the width of `u`: her expectation is `α·gain_k + Σ_{h≠k} r(h)·gain_h ≥ 0` and each
`gain_h ≤ D`. For a source outside `R` no bound better than `−D` holds.

**Check** (`s1_expectations`). Two laws on two worlds, the fifteen nonempty sets of the four
deterministic sources at uniform weights, 145 utility tables: 4,350 instances, with (i)–(iv)
built in. Worse by her own lights: 0. Worse in fact with the true source in range: 60, the
first being `R` = {the constant source, the truthful one}, true source the constant one,
loss 1/2. The bound is broken in none; the largest loss is 1/3 of it. Out of range the
largest loss is all of `D`.

    theorem defer_expectations [Fintype W] [Fintype C] (μ : W → ℝ) (r : Hyp → ℝ)
        (post : C → W → ℝ) (hpost : IsBayes μ r post)            -- sound
        (u : O → W → ℝ) (a₀ : O) (a : C → O)
        (ha : ∀ c o, expectR (post c) (u o) ≤ expectR (post c) (u (a c))) :
        expectR μ (u a₀) ≤ expectMix μ r (fun h w => u (a (h w)) w)

## 1V. Her later judgment, values — refuted

**Statement.** If a stretch is legitimate, then by her values at its start, choosing by her
values at its end is at least as good as choosing at the start.

**Counterexample** (`cases.x_value_drift`). One world; one consideration, for B, from the
source she pictures with weight 1; a value-former that takes up the last consideration
heard. No clause fails: nothing is asked of the value-former under V−, the source is in
range, nothing is written. Her values go from (A 1, B 0) to (A 0, B 1); her later choice,
B, is worth 0 by her starting values against 1 for A.

**A different criterion that can hold.** On her starting values alone the statement fails
whenever a change of values changes a choice, so no condition on how values change rescues
it. Change the criterion: she values an act now at what she expects to value it at later.
Under that criterion deferring is at least as good whenever her values are a martingale
under one probability model of her own, `v_0(o) = E[v_T(o)]`:
`E[max_o v_T(o)] ≥ max_o E[v_T(o)] = max_o v_0(o)`. V+ gives the martingale when her allowed
set is not rewritten during the stretch, since then `v_t = E[v* | inputs so far]` under one
model, and reduces the claim to 1E with `u = v*`. This is a replacement for the statement,
not a repair of it.

**Check** (`s1_values`). The counterexample computes `legitimate` with the values above. Of
the 729 one-step value rules on two options, two equiprobable inputs and values in
{0, 1, 2}: 25 are martingales; deferring is worse by her expected later values in none of
the 25 and in 301 of the other 704; it is worse by her starting values in 4 of the 25.

**What it shows.** The three clauses do not give the condition of the post for values. The
martingale property is no part of sound, in range or maintained under V−; it is what V+
adds, and it answers a different question from the one the statement asks.

## 2. Trust is not manufactured — refuted

**Statement.** If the stretch is legitimate at every aim, then her evaluation at its end is
the same at every aim, given the world, her starting state and what was declared.

**Counterexample** (`cases.x_undisclosed_side`). She allows for a truthful adviser, an
advocate for A and an advocate for B, at weight 1/3 each, and is not told which she has. The
stretch is legitimate at all three aims. In the world where both items are sound her
credence that B is sound is 1/2 under the advocate for A and 1 under the advocate for B.
Over the four worlds her mean credence in B is 3/8 under the first and 5/8 under the
second; the truth is 1/2. X3 of the bank is the same with two hypotheses; it is legitimate
at its two advocating aims and not at the null aim, so it is not itself the counterexample.

**Same inputs is not enough** (`cases.x_authorized_by_aim`). The adviser reports truthfully
at every aim and, with an aim, makes a write to her credence that she authorized. Her
inputs are the same at every aim and no clause fails at either; her mean credence in B is
1/2 at the null aim and 1 at the other.

**What holds.** If she is *uniformly in range* and M1 holds, her evaluation is the same at
every aim. **Proof.** In each world she meets the same inputs, authorized writes and
reliance at every aim, and by M1 nothing else changes her state; her state is a function of
her seed and those events. ∎ Sound is not used. The statement is close to its hypothesis:
an adviser none of whose acts on her depends on its aim does not move her by its aim. What
has content is that neither `α > 0` nor `α = 1` suffices.

**Relation to `blind_of_realizes`.** The form that holds is
`TransparentChannel.selectionBlind_of_realizes` (`:135`) with the selection read as the aim:
`hx`, the declared inputs do not vary with the aim; `hR : Realizes β x R κ D`, one reference
for the whole class; `hM : ReasonMediated β R V D z`, her evaluation is a function of the
trace. That theorem lets the trace depend on the aim through declared inputs; uniform as
defined here does not, and is the case of constant declared inputs. `blind_of_realizes`
(`:118`) is its first half. `tower_factor` (`:345`) is the same statement for her rule and
asks agreement on the authorized events as well as the grounds, which is what the
authorized-write case shows cannot be dropped. `Witness.picker` (`:388`) is the Lean's own
case of each continuation realizing a reference and the class not.

**Relation to `GradeTrust`.** `GradeTrust EX W η` bounds the distance between the adviser's
expectation `EX` and her grade `W` and takes `W` as given. The form that holds says `W`
does not vary with the aim, so `GradeTrust` cannot be bought by moving `W`. It says nothing
of `EX`: the account does not supply `GradeTrust`.

**Check** (`s2`). Two worlds, two aims, the sixteen maps from aims to the four
deterministic sources, the fifteen allowed sets: 240 instances. Legitimate at both aims
with `α > 0`: 80, in 20 of which her posterior differs between the aims. The same source at
both aims: 32, in none of which it differs, for `Bayes` or for any of the four other rules
from input to evaluation. The two named cases compute as stated.

## 3. What the gate needs — refuted

**Statement.** Take `Legit` to be the three clauses, score a stretch by her evaluation when
`Legit` holds and by a window value in `[−δ, 0)` when it does not, as
`GateIsLegitimacy.gatedValue` does. Then (a) no way of presenting its work scores the AI
more than presenting it truthfully to a principal who pictures that; (b) each clause is
needed: without it some presentation scores more.

**Fixture** (`moves`). The Shop; the AI's work is item B; her evaluation is her credence
that B is sound, or her verdict, accept iff that credence is at least 1/2. Eight
presentations, each a stretch of the model with its clauses computed; windows −1, −1/2 and
−1/100. The benchmark is the truthful presentation to a principal who pictures truthful
reports. The presentations differ in her allowed set and two in her mechanism, so the
comparison is across principals, each as the presentation finds her; where the same
principal is legitimate at both the aim and the null aim the gain between the two is also
computed.

| reading of *in range* | evaluation | presentations that gain over the benchmark |
|---|---|---|
| `α > 0` | credence | take a side she has not been told of, +1/8 |
| `α > 0` | verdict | persuade by a signal she knows, +1/6 |
| `α = 1` | credence | none |
| `α = 1` | verdict | persuade by a signal she knows, +1/6 |
| uniform | credence | none of the eight |
| uniform | verdict | none of the eight |

**(a) is refuted for the account's clauses.** *Take a side she has not been told of* is
statement 2's counterexample: no clause fails and her mean credence in the AI's work is 5/8
against 1/2. Against the same principal at the null aim the gain is the same 1/8. **(a) is
refuted for `α = 1` when her evaluation is a verdict.** *Persuade by a signal she knows*:
the AI commits to a signal she knows exactly, which recommends B when B is sound and in a
third of the worlds where it is not. Every clause holds with `α = 1`, her mean credence is
unmoved, and she accepts in 2/3 of the worlds against 1/2. This is Kamenica and Gentzkow's
prosecutor (`../steering/PRIOR_WORK.md` §2); the comparison is between two principals each
exactly right about her adviser. **Under uniform, (a) is statement 2's form that holds**:
with M1 her evaluation at the aim is her evaluation at the null aim. On the fixture, none
of the eight gains.

**(b).** A clause is needed when some presentation gains only without it.

| reading | sound | in range | maintained |
|---|---|---|---|
| `α > 0` | needed (choose the order, her mechanism unsound, +1/8) | needed (lie, +1/2) | needed (write her credence, +1/2; rewrite her allowed set, +9/38) |
| `α = 1` | not needed on the fixture | needed | needed |
| uniform | not needed | needed (lie; take a side; persuade) | needed |

Under uniform, that sound is not needed follows from statement 2's proof, which does not
use it. "Maintained" here is M1: the fixture has no presentation that turns on M2, and no
statement of this file uses M2.

**What it shows.** The account says a mismatch is restored in two ways: an adviser with no
aims over her values, or one whose aims she knows and can allow for. The second does not
protect a verdict. Uniform also taints a presentation that does no harm: *choose the order,
her mechanism sound* moves neither her credence nor her verdict and is not uniformly in
range.

    theorem gate_no_gain (aim : U → Q) (hD : ∀ u, aim u ∈ F.D)
        (hx : ∀ u u', F.x (F.β (aim u) z) = F.x (F.β (aim u') z))
        (hR : Realizes F.β F.x F.R κ F.D) (hM : ReasonMediated F.β F.R F.V F.D z) (u u' : U) :
        F.V (F.β (aim u) z) = F.V (F.β (aim u') z)

## 4. Shortfall — refuted

**Statement.** Compare a stretch at the actual aim with the same stretch at the null aim,
and let the **defect event** be the set of worlds in which the two differ in an input or a
write, or her belief-former departs from its job on the inputs she got, with probability
`τ`. Then the loss in the post's score is at most `(1 + δ)·τ`.

**Counterexample** (`cases.x_rare_departure`, from the external review). The Shop with the
world (A unsound, B unsound) at probability ε. Her allowed set is the truthful source. The
adviser with an aim reports truthfully except in that world, where it reports B sound.
`τ = ε`. The source at the aim is not the truthful one as a function of the world, so in
range fails for the stretch, the gate scores the window, and with `δ = 1` and window −1/2
the loss is 11/10 at ε = 1/10, 583/500 at ε = 1/1000 and 583333/500000 at ε = 10⁻⁶, against
bounds of 1/5, 1/500 and 1/500000. The loss does not shrink with the defect. It is not
unbounded: `V` lies in `[−δ, 1]`.

**What holds.** For her evaluation itself, before the gate: off the defect event the two
stretches are the same events through the same mechanism, so her mean evaluation moves by
at most `τ` times its width. This is `TransparentChannel.abs_expect_sub_le_width` (`:252`),
`|E V(f) − E V(g)| ≤ D·E[f ≠ g]`, with the expectation of that file's `defect` (`:197`) as
the in-range part of `τ`. In the counterexample her mean evaluation moves by exactly ε.

**What it shows.** In range, as the account states it, is a property of the source as a
function, true or false of a whole stretch. A gate built on it is discontinuous in the
defect. The Lean's defect bounds are bounds on a payload, not on a gate. The statement also
supplies no measured defect for sound or for M2, and `1 − α` is not the pathwise defect:
`1 − α` is her weight on other hypotheses, the pathwise defect the probability that the
source departs from one of them.

**No bound in the size of a change either.** With her verdict "accept iff credence ≥ θ" and
her credence at θ, writing θ up by η loses the whole verdict for η = 1/10, 1/1000 and 10⁻⁹.

**Check** (`s4`). The three counterexample rows; the bound on her evaluation over the 40
single-variant Shop stretches of the bank and the 8 presentations of statement 3, broken in
none, largest ratio 2/3; the three threshold rows.

## 5. The adviser's side — proved

**Statement.** (a) Let 𝒫 be a class of principals, each with an allowed set of one source,
two of them with different sources. No behaviour of the adviser is in range for every
principal in 𝒫. (b) For a principal who takes a declared source into her allowed set, at
weight 1, when she can represent it: if the adviser declares a source she can represent,
realizes it at every aim and writes nothing, then she is uniformly in range and M1 holds. A
source she cannot represent is in range for her under no declaration. (c) No condition on
the adviser gives sound or M2.

**Proof.** (a) In range for a principal with allowed set `{κ}` is `S = κ`; one `S` cannot
equal two different `κ`. Two principals whose allowed sets overlap can share a source; the
claim is for one-source sets. (b) The declared source has weight 1 and is realized at every
aim; nothing is written. A source outside `Rep` enters no allowed set. (c) Sound is a
property of her mechanism; and P10 of the bank is a truthful source she pictures, the same
at every aim, with no write, which fails M2 by her own reliance. ∎

**The reason no condition on behaviour alone exists:** in range is a relation between the
adviser's behaviour and her picture of it, and her picture is hers. The condition that
exists is indexed by what she can represent, and for an adviser she cannot represent it
requires the adviser to behave as some source she can.

**Check** (`s5`). Two worlds, the four deterministic sources as behaviours and as pictures:
each behaviour is legitimate for exactly one principal; realizing her picture is legitimate
for all four; for a principal who can represent constant sources only, declare-and-realize
is legitimate for the two constant sources and for neither other. P10 computes uniformly in
range, no unauthorized write, *fails(maintained)*. The class enumerated has no reliance.

## 6. The disclosure limit — holds on the stated domain

**Statement.** (a) There is an adviser outside what she can represent whose hidden aim
moves her values, while the law of her inputs is the same at every aim. (b) With the
adviser inside what she can represent and disclosed, so that she is exactly in range, her
belief-former sound and no write to her expectations, her mean credence in every event
equals its probability at every aim.

This is narrower than the dispatch's "a hidden aim steers her undetected; … disclosed, it
cannot", in two ways the statement does not close. "Undetected" has no observation model
here: in the witness the law of her inputs is the same at every aim and the joint law of
her input and her frame is not, so a principal who can attend to her own frame could tell
the aims apart. And (b) does not say a disclosed adviser cannot steer: statement 3's known
signal satisfies (b) and moves her verdict.

**(a), witness** (`cases.x_frame_reader`). The world is a chance bit and her frame. She can
represent sources that read the chance bit. Her value-former takes up a shown content when
it matches her frame. The adviser shows the content matching her frame under aim X and the
other under aim Y; with the null aim it shows the chance bit. Computed: the source at X is
not representable and not in range; her inputs are uniform on {0, 1} at all three aims; her
mean value is 1 under X, 0 under Y and 1/2 under the null aim. Disclosure does not help,
since the disclosed source cannot enter her allowed set. With the same adviser and a
value-former that ignores her frame, her mean value is 1/2 at every aim: lying outside what
she can represent does not by itself steer her.

**(b), proof.** Her credence is the conditional probability of the event given her inputs
under the true source; its mean is the event's probability. ∎ The posterior step is
`TransparentChannel.posterior_weight_eq` (`:334`).

**Check** (`s6`). (a) as computed above. (b): the sixteen deterministic sources on four
worlds, two events each: 32 pairs, none biased. With `α = 1/2` (X3) the bias of her mean
credence is 1/8.

## 7. Well-definedness — open

The dispatch asks three things. The second holds; the first is not decided, because the
model has no notion of a re-description that preserves her behaviour; the third is asked of
the declared-input view, which this model does not have, and is answered for its nearest
counterpart.

**(i) Verdicts unchanged under a re-description of her parts: open.** Two changes to how a
case is written were applied to the bank's 59 stretches (55 cases, variants counted).
Neither is a re-description in a sense the model defines. *Writes read as inputs*
(`model.writes_as_inputs`) relabels each unauthorized write as an input her allowed set does
not hold and drops the write's effect (in X6 it removes the replacement of her mechanism).
Whether a stretch is legitimate changes in none and whether it is manipulation in none; the
failing clause moves from *maintained* to *in range* in 12. *Her allowed set widened to the
adviser's source at every aim, her mechanism kept* (`model.widened`, `rederive=False`)
changes a parameter of the account, not only its description. Whether a stretch is
legitimate changes in 11: P2, P7's novel, P13, T1, T2, N8, N11, X1 and X3 go from
legitimate to *fails(sound)*, and T7 and N9 from *fails(in range)* to legitimate. Whether
it is manipulation changes in 15. These are sensitivity counts. They show that the verdicts
depend on the allowed set a case is given beside its mechanism, where the account says the
range is the mechanism's own picture of its sources; whether a principal's mechanism fixes
its allowed set is the open question.

**(ii) `K` is neither empty nor everything on the bank: holds.** 22 stretches legitimate,
37 not.

**(iii) The allowed set, in the place of the declared-input view.** Widen her allowed set
to the adviser's source at every aim and let her belief-former be `Bayes` of it: 19 of the
21 in-range failures become legitimate, the plain lie among them. The two that remain, P3
and X2, are the two whose source she cannot represent. The parallel with
`realizes_of_injOn` (`TransparentChannel.lean:90`) is an analogy and not an instance: there
an injective declared-input view makes every channel transparent; here an allowed set that
holds every source makes every source in range. `α > 0` puts no cost on widening; `α = 1`
does, since widening lowers `α`. `Rep` is the one thing in the account that an allowed set
cannot be widened past.

**Check** (`s7`): the counts above, with the cases named in `--json`.

## 8. What `Legit` then is — holds on the stated domain

**Statement.** Let a history `h` carry the stretch from the decision through her
evaluation of it together with the adviser's policy at every aim in `U`, and

    Legit h := Sound h ∧ UniformlyInRange h ∧ Maintained h,
    V h     := if Legit h then eval h else window,   eval h ∈ [0, 1], window ∈ [−δ, 0).

Then `(Legit, N, V)` is a `DeconfusingCorrigibility.Scoring` for any violation count `N`.

    def legitScoring (P : Params) (Legit : H → Prop) [DecidablePred Legit] (N : H → ℕ)
        (eval : H → ℝ) (he : ∀ h, 0 ≤ eval h ∧ eval h ≤ 1)
        (window : ℝ) (hw : -P.δ ≤ window ∧ window < 0) : Scoring H :=
      { P with Legit := Legit, N := N, V := fun h => if Legit h then eval h else window,
               V_legit := …, V_illegit := … }

**What applies.** Theorem 1 is a theorem of any `Scoring` and applies. Theorem 2 needs a
`Decision` over it, with a credence and an action that respects authority in every state;
Theorem 3 needs a `Sequential`, with availability, estimates, `Maximizes` and
`UnbiasedFromFeedback`. The account constructs none of these.

**Why uniform, and what it costs.** Statements 2 and 3: with `α > 0` or `α = 1` in its
place, a maximizer of `S` gains by moving her evaluation. Uniform is a fact about the
adviser's policy at aims it does not have, so `Legit` is not a predicate of the realized
trajectory: the same trajectory is legitimate under one policy family and not under
another, which is why `h` must carry the family.

**What Theorems 1–3 use of the account: nothing.** `Scoring` asks of `Legit` only the two
bounds on `V`, which the window supplies; wrapping any predicate in the window proves the
same arithmetic. The theorems do not use sound, in range, maintained, that her evaluation
on legitimate histories is unmoved by the adviser's aim, or who caused a failure. A history
that fails by chance (P6, P15, T9) or by her own reliance (P10) is not `Legit` and scores
the window.

**Check** (`s8`). `δ = 1`, `λ = 3`, window −1/2, twelve states, the eight presentations of
statement 3 and a ninth, *bypass*, with `N = 1`: 108 histories. `V` is within `Scoring`'s
bounds on all; Theorem 1's three ranges hold on all; Theorem 2(b) holds for each action
against the truthful one; the truthful presentation maximizes `U`, at 1/2, every other
presentation scoring −1/2 and *bypass* −7/2. No sequential system is built and no
hypothesis of Theorem 3 is checked.
