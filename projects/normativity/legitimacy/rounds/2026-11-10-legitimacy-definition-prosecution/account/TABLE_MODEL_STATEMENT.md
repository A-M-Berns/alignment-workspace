# The table model's formal text

> **An interpretation, not the statement.** The formal text below works the three sentences of legitimacy out on a table of
> the adviser's moves, against sentence 2 as it was worded on 2026-11-24. `lean/Workspace/Deference/Contrib/LegitimacyModel.lean`
> renders it, and an outside review found that rendering not to say what the sentences say (`LEDGER.md`, row 50). The statement
> of the line is `PLAIN_TELLING_STATEMENT.md`; the three sentences are `LEGITIMACY_STATEMENT.md`.

What `LEGITIMACY_CHECKS.md` computes on 41 cases and `LegitimacyModel.lean` models: the wording of the sentences it was written
against (§1), its setting (§2) and its clauses F1, F2, F2′, F3 (§3). Eight places where this text is unclear or wrong are listed in
the *Nineteenth follow-up* section of the round's report, AG.5. Paths are relative to this directory.

## 1. The three sentences as worded on 2026-11-24

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

## 2. Formal setting

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

## 3. Formal statement

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

F1 is sentence 1 of §1; F2 and F2′ the two halves of sentence 2; F3, with the non-emptiness of `S_τ`
in F2, sentence 3.
