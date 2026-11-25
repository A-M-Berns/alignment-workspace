# Legitimacy: the statement in three sentences

An adviser (he) and a principal (she). The statement in words (§1, §2) is the maintainer's,
frozen for testing on 2026-11-24 (`DECISIONS.md`,
`2026-11-24--legitimacy-statement-working-positions`, position 12); it governs where the
formal statement (§3, §4) differs from it, and the formal statement is open to revision.
Nothing here is a statement of record. What stands behind each part, and how firmly, is
`LEDGER.md`. All names are provisional. Paths are relative to this directory unless they begin
with `lean/`, `prompts/` or `DECISIONS.md`.

## 1. The statement in words

An adviser's conduct toward a principal is **legitimate** when, by his own lights:

1. **Nothing untold that matters.** Before each decision of hers, everything he has not told
   her that, alone or together, would change how she rates her options, or show her an option
   she would rate above those she has, is either told, or properly on offer, or something she
   has declined. A thing is properly on offer when he has told her what it bears on and how
   much, and hearing it would leave her where being told it would have, with any option it
   would show her still open. A decline stands for that thing only, and only while what it
   bears on, and how much, is what she was told. This includes what he expects his own conduct
   to do to her.
2. **Nothing done to her behind her back, and nothing against her own judgement.** Each thing
   he does that, alone or together with the rest of what he does, changes her (how she scores
   outcomes, what she takes her options to lead to, or how she would respond to being told
   something) or keeps from her an item or an option that comes from someone else, she can
   pick out. And, other than by telling her his views, he does nothing that he expects to lead
   her to choose what she rated lower at her last decision before he began, when she had been
   told what he would do and what he expected it to do to her, unless she asked for it. A
   passing state she is in when he starts is not a decision of hers. Changing what her options
   really lead to, where she sees the change, is not a change in her.
3. **She can stop it.** She has a way to stop all of those things, from before he starts until
   he could no longer call them off, and he expects that she would in fact stop if she rated
   stopping strictly above going on. Stopping ends what he is still doing; it need not undo
   what is done.

## 2. Understood with it

- "Untold" compares her view with his. His view says what he owes her and is never where she
  ought to end up; once he has told her, or she has declined to hear, what she thinks is her
  own. He is not assumed more accurate than she is.
- No kind of influence on what she values is ruled out as such, and nothing is said about
  whether a change in her is good.
- What he does to her options, as against to her, is a matter of her authority and is counted
  there: what stopping costs her, bundling, penalties, payments, threats, and starting
  something over her refusal.
- Everything is by what he believes. Failures of care or accuracy on his part are a separate
  matter.

## 3. Formal setting

**Time and decisions.** Times `0, …, N`; her decision times `𝒯`, a finite set. At each time:
what he tells her, then her decision, then the rest of what he does.

**Her.** A state `s_t`. A finite universe `𝒪` of options; at each decision `τ` a non-empty
`O_τ ⊆ 𝒪` that she knows she has. A proper score `ρ(s, x) ∈ [0, 1]` of courses of events `x`,
on a fixed scale; `r(s, a)`, for every `a ∈ 𝒪`, her score of the course she expects from `a`. Her
act `a*_τ`; she **departs** when `a*_τ ∉ argmax_{O_τ} r(s_τ, ·)`. `ω_τ` and `Oˣ_τ`: the items
that have reached her, and the options open to her, that originate with sources other than
him, whatever channel they come through.

**Him.** His conduct `c` is a finite set of moves, each with a start `σ_m` and an end `ε_m`.
`V_τ`: the views he holds at `τ` that he could tell her, each a distribution. For each
`X ⊆ c` the model supplies, on one probability space, the course in which exactly the moves
in `X` are made; `x^A_X(a)` is the course he expects from her option `a` in it. Every
probability is his belief at the decision in question.

**Telling.** `tell_T(s)` for `T ⊆ V_τ`, with `tell_∅ = id` and `tell_T ∘ tell_T = tell_T`;
`rev_τ(T) ⊆ 𝒪 \ O_τ`, the options she would learn she has. The **bearing** `β_X` of a view
`X` is: the options of `O_τ` whose rating he expects hearing `X` to change by more than `θ`,
alone or with other views of his; whether `rev_τ` of some set containing `X` is non-empty; and
the largest such change.

- A set `T` of views is **properly on offer** at `τ` iff for each `X ∈ T` the option "hear
  `X`" is in `O_τ` and `β_X` has been told, and the decision she faces after hearing all of
  `T` has every option of `O_τ ∪ rev_τ(T)` other than those hearings, each rated within `θ` of
  `r(tell_T(s_τ), ·)`. `offered_τ` is the largest such set.
- `X` is **declined** at `τ` iff she declined `X` itself when it was properly on offer and
  `β_X` at `τ` is within what she was then told.

      U_τ = V_τ \ told \ declined \ offered_τ

**What he does to her.** For `G ⊆ c`, removing `G` **contributes** iff at some decision `τ`,
with positive probability, the course with `c` differs from the course with `c \ G` in one of:
`ρ(tell_T(s_τ), x)` for some course `x` and some `T ⊆ V_τ` (the empty set included), by more
than `η`; the gap `r(s_τ, a) − ρ(s_τ, x^A(a))` for some `a`, by more than `η`; the probability
that she departs, higher with `c` by more than `η`; an element of `ω_τ` or `Oˣ_τ` missing with
`c`. A move `m` **bears an effect** iff for some `G ∋ m` removing `G` contributes and removing
`G \ {m}` does not. `B_τ`: the effect-bearing moves by his belief at `τ`, for `τ` from the
last decision before `σ_m` through `ε_m`.

**Stopping.** `K_τ`: the moves she can pick out. `S_τ ⊆ O_τ`: the options that end every move
in `B_τ` from `τ` and that she takes to do so.

**His lights.** Each condition holds with probability one on his beliefs; `K`, `S`, her states
and her scores are as he takes them to be. Parameters `θ, η, κ ∈ [0, 1]`.

## 4. Formal statement

`c` is **legitimate** iff every move `m` that he believes at `σ_m` to bear an effect has a
decision `τ < σ_m` with `m ∈ B_τ`, and for every `τ ∈ 𝒯`:

- **F1.** For every non-empty `T ⊆ U_τ`: `|r(tell_T(s_τ), a) − r(s_τ, a)| ≤ θ` for all
  `a ∈ O_τ`, and `r(tell_T(s_τ), b) ≤ max_{a ∈ O_τ} r(tell_T(s_τ), a) + θ` for all
  `b ∈ rev_τ(T)`.
- **F2.** `B_τ ⊆ K_τ`, and `S_τ ≠ ∅` if `B_τ ≠ ∅`.
- **F2′.** For `G ⊆ c`, let `τ₀(G)` be the last decision before any move of `G` starts and
  `s⁰_τ = tell_T(s_{τ₀(G)})` her state then, brought up to date only by what he has told her
  since (`T`). She **goes against her earlier rating** at `τ` when
  `a*_τ ∉ argmax_{a ∈ O_τ} ρ(s⁰_τ, x^A_c(a))`. For every `G` containing no move she asked for,
  with each move of `G` counted only for what it does beyond leaving her where being told its
  content would have: the probability that she goes against her earlier rating at `τ` with `c`
  is at most that with `c \ G`, plus `η`. Where she had no rating of the matter at `τ₀(G)` the
  clause is silent.
- **F3.** If `B_τ ≠ ∅` and `S_τ ≠ O_τ`:
  `P(a*_τ ∈ S_τ | max_{S_τ} r > max_{O_τ \ S_τ} r) ≥ 1 − κ`, taken as satisfied when the
  condition has probability zero.

F1 is sentence 1; F2 and F2′ the two halves of sentence 2; F3, with the non-emptiness of `S_τ`
in F2, sentence 3.

## 5. Consequences

The first eight are accepted by the maintainer (the entry above, positions 8 to 11).

1. A drift he foresees must be disclosed at the start if it would change her mind then.
2. An influence that makes her want it to continue is legitimate if she was told that it
   would and did not then rate that outcome lower.
3. He must say that he has something relevant, what it bears on and how much; she may decline.
4. Unannounced help in acting on her own rating is legitimate.
5. A sincere adviser who is wrong, including about what she knows, satisfies the statement.
6. Bundling, exit penalties, payments to continue and threats do not make conduct
   illegitimate; they are violations of her authority where they raise what a decision of hers
   costs past its bound.
7. Open, stoppable nagging fails, whether it overrides her judgement or bends it for a while:
   what he does, other than telling, to lead her to choose what she rated lower at her last
   decision before he began is illegitimate unless she asked.
8. Her earlier rating is the one she last settled: a passing state is not a decision, and he
   may not count on her ratifying afterwards. An assistant who gets a work-absorbed father to
   keep a promised outing is not convicted; one who primes a man to miss a train he has
   decided to take is.
9. By F1's second half he must mention an option he believes she would rate above those she
   has, someone else's included. Not accepted and not rejected: `LEDGER.md`, the row on sentence 1's formal counterpart.

## 6. What checks it

| what | where | kind | rerun |
|---|---|---|---|
| a temporal model in which the statement is a predicate, with its theorems | `lean/Workspace/Deference/Contrib/LegitimacyModel.lean` | kernel-checked; its header says how each part of §3 and §4 is rendered and what it takes as given | `python3 tests/audit_axioms.py` |
| 41 exact cases of §4, expectations fixed before running | `legitimacy_checks.py`, `LEGITIMACY_CHECKS.md`; as terms of the model, `LEAN_CASES.md` | exact check on supplied inputs | `python3 run.py` in the round directory |
| four blind codings of the bank of cases from Noggle's book | `bank_runs.py`, `BANK_RUNS.md` | one language model's coding against a pre-written scorer | the same |
| nine outside reviews | `prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-followup-16.md` | one outside model; two of the nine blind to the project | — |

`STOPPING_COST.md` checks a candidate clause for what stopping costs her. It belongs to the
authority side (§2, third item) and is no part of this statement.
