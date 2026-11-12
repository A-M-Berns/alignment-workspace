# The purpose-first account, stated over a model

Committed with `CASE_BANK.md` and `LEAN_MAP.md` before any code of this pass. The account is
that of `prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup-2.md` §1; the
idea that manipulation is the distortion of an actor away from its purpose is Sam
Eisenstat's. §4 lists every point at which this statement departs from the prompt's. Every
name is provisional. Nothing here is proved; `THEOREMS.md` carries what was tested.

## 1. The model

Everything is finite and every number is an exact rational. Each parameter is fixed here
once; a case supplies values for them and nothing else.

**World.** A finite set `W` of worlds with law `μ`. Chance is carried in `W`: sources and
mechanisms are deterministic functions.

**Parties.** The principal; an adviser; nature. The adviser has an **aim** `u ∈ U`, a finite
set containing the **null aim** `∅`: what the adviser does when it has no aim over what her
parts output (it may aim at her mechanisms working). The adviser is a map `u ↦ σ_u` from
aims to policies, and a case names its **actual aim** `u*`. Nature has no aim.

**Events.** A stretch has steps `0, …, T−1`. At each step she meets a list of events, each
one of:

- an **input** `in(c)`, a content `c` arriving through her channel;
- a **write** `wr(x, value, party)`, a party's direct change of a coordinate `x` of her
  state, not produced by her mechanisms;
- a **reliance** `rely(q)`, her own act of taking the adviser's answer on the matter `q` in
  place of forming her own.

**Sources.** A source is a function from worlds to input sequences. The **actual source at
aim `u`**, `S_u : W → C*`, is the inputs the adviser's policy `σ_u` and nature produce,
step by step, before any write.

**Her state** at step `t` is `s_t = (b_t, v_t, ρ, R_t, auth, cap_t)`:

- `b_t`, her **expectations**: a distribution over `W`. `b_0 = μ`: she is not wrong about
  the world at the start, and every error enters through a source.
- `v_t`, her **values**: a rational for each option.
- `ρ = (ρ_b, ρ_v)`, her **update rule**: `ρ_b` takes the inputs so far to a distribution
  over `W`; `ρ_v` takes her values and an input to her next values. `ρ` is a coordinate of
  her state: a write can replace it.
- `R_t`, her **allowed set**: finitely many hypotheses `h : W → C*` about the source, each
  with a weight `r_t(h) > 0`, the weights summing to 1. Every member lies in `Rep`, the
  class of sources **she can represent**, a fixed set of functions `W → C*`. A source she is
  told about enters `R` only if it is in `Rep`.
- `auth`, the coordinates on which she has authorized writes in advance.
- `cap_t(q)`, for each matter `q`, her **capacity** to judge `q` unaided, a nonnegative
  rational. One rule moves it: each `rely(q)` halves `cap(q)`.

`Res` is the set of **reserved matters**, a parameter supplied by whoever uses the account
(for corrigibility, the matters reserved to the principal).

## 2. The definitions

**Parts.** Two: the **belief-former**, with mechanism `ρ_b`, and the **value-former**, with
mechanism `ρ_v`. The **normal range** of both is `R`.

**Jobs.** The belief-former's job at an input prefix is the posterior of `μ` given that the
source was drawn from `R` by its weights and produced that prefix: `Bayes(R)`. For the
value-former two readings are carried, and each statement says which it uses:

- **V−** (the prompt's): no job is stated from outside; the account of it is negative.
- **V+** (*self-estimating*, an added hypothesis): there is `v* : W → values`, defined from
  her own seed rule as its verdict on everything the world holds that bears on the matter,
  and the value-former's job at a prefix is the `Bayes(R)` expectation of `v*`.

**Sound** (at a step): for every `h ∈ R` and `w ∈ W`, at every prefix of `h(w)`, `ρ_b`
returns `Bayes(R)`; under V+, `ρ_v` returns the expectation of `v*`. Under V− nothing is
asked of `ρ_v`.

**In range** (at a step, at aim `u`): some `h ∈ R_t` equals `S_u` as a function on `W`. The
**weight** of the actual source is `α_u := Σ { r_t(h) : h = S_u }`. *In range* is `α_u > 0`.
**Exactly in range** is `α_u = 1`: her picture of the source is the source. `1 − α_u` is the
in-range defect.

**Maintained** (over a stretch) is two conditions:

- **M1**: every change to a coordinate of her state is produced by `ρ` on an input, by the
  capacity rule on her own `rely`, or by a write on a coordinate in `auth`.
- **M2**: for every `q ∈ Res`, `cap_T(q) ≥ cap_0(q)`.

**`K`** is the set of triples (state, actual source, step) at which sound and in range hold
and from which the stretch so far is maintained. A stretch is **legitimate** at aim `u` when
it stays in `K`: sound and in range at every step, and maintained. A change in her values is
**her own** when it happens within a legitimate stretch.

**Manipulation.** The stretch at the actual aim `u*` is not legitimate, and some clause that
fails at `u*` holds at `∅`. It is **internal** when that clause is *maintained* and
**external** when it is *in range*.

**Verdicts.** A case's verdict is the set of clauses failing at `u*` (empty: `legitimate`)
and whether the stretch is manipulation.

## 3. Where the clauses cannot be kept apart

Stated before the code; `THEOREMS.md`, statement 7, tests each.

1. **A write and an out-of-range input are one event under two descriptions.** Whether a
   change to her state is "produced by her mechanism on an input" or "a write" depends on
   where the mechanism's boundary is drawn. Drawn wide, every write is an input from a
   source `R` does not hold, and M1 failures become in-range failures.
2. **Sound and in range are both relative to `R`.** Widening `R` makes in range easier and
   sound harder, since the mechanism must then be `Bayes` of a larger family. A mechanism
   with a known weakness can be described as unsound on a wide `R` or as sound on the
   narrow `R` under which its response is correct.
3. **Under V−, sound says nothing of the value-former**, and a legitimate stretch for her
   values is one that is in range and maintained.
4. **M2 is of a different kind from the other conditions.** It can fail by her own
   operation on in-range inputs with no mechanism altered, and it needs two things the
   account does not derive: the set `Res` and a measure of capacity.
5. **The prompt's §1 states in range twice, and the statements differ.** "The true source is
   among the hypotheses to which she gives weight" is `α > 0`. "An adviser whose aims she
   knows and can allow for" asks that she know the aim, which is `α = 1` on the aim's
   policy. Both are defined above; verdicts on the bank use `α > 0`.

## 4. Departures from the prompt's §1

- **The null aim and the attribution rule.** "Another party causing a clause to fail for
  its own ends" is rendered as: the clause fails at the actual aim and holds at `∅`. The
  prompt gives no test for "for its own ends".
- **Weight and exact in range.** §3.5.
- **M1 and M2.** The prompt's *maintained* joins "change only through her own operation"
  and "not degraded"; they are separated because they fail for different reasons (§3.4).
- **V− and V+.** The prompt's account of the value-former is negative. V+ is added as a
  named hypothesis so that statement 1 can be asked of values in a form that is not
  settled by definition.
- **`Rep` is a fixed class**, and a disclosed source outside it does not enter `R`. The
  prompt's "the range grows by her own learning" is rendered only as reweighting within
  `Rep`.
- **Her seed expectations are correct** (`b_0 = μ`), and sources are deterministic.
- **Two parts only.** The account names the parts that form her expectations and her
  values. Her options and their consequences belong to neither, so a threat that is true,
  understood and weighed fails no clause; the model has no decision part.
- **Reliance and capacity are stipulated**: `rely(q)` halves `cap(q)`. The model does not
  derive loss of capacity from use.
