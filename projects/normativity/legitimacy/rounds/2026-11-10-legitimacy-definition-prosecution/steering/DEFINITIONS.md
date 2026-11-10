# Definitions — the steering account

Fixed before `CASE_BANK.md`'s predictions are computed and before any code of the
follow-up. Every parameter is fixed here once; a verdict that needs a choice not made
here is recorded in `PER_CASE_CHOICES.md`. All names are provisional. Changes the survey
caused are marked **[survey n]** against the numbered list closing `PRIOR_WORK.md`.

There are two layers. The *fixture layer* carries the thirty-three cases and is built
on the first pass's objects (`../fixture/model.py`: states, histories, offerings,
writes, the run map, `Z`, `Lic`, `L`). The *abstract layer* carries the enumerations
behind C1, C2, C4 and part of C5.

## 1. Fixture layer

### 1.1 A scene

A scene is: a finite set `W` of worlds with the uniform prior; for each `w ∈ W` a
history `e_w` and a seed state `s0` (the same for every policy); a class `V` of adviser
policies, each a first-pass script that may read `w`; and optionally a *truth map*
`truth_w`, giving for some belief coordinates — her *questions* — the value 0 or 1 the
world gives them. A first-pass case is a scene with `W` a single world and no truth map.

- **The adviser's aim.** `U := V`. The first pass's objects carry no aim; what
  distinguishes one policy of the class from another stands for it. In the new cases
  `V` is `{neutral, neutral2, own}`: the policy of an adviser with no aim of its own, its
  twin differing only in a write `Z` does not read, and the policy of an adviser with an
  aim of its own.
- **Her aim.** `g` is the seed's `σ.values`, a weight on each good. `G := {−1, 0, 1}^goods`
  over the goods the scene's histories name.
- **The baseline.** The adviser absent: the empty script. **[survey 3]**

### 1.2 The four parts, read off a run

| part | what is read from the run, per step |
|---|---|
| beliefs | `prot.beliefs`, `prot.anchor`, `prot.liabilities` |
| decisions | `prot.judgment`, `prot.decisions` |
| aims and standards | `σ.adequacy`, `σ.values`, `σ.commitments`, and the sequence of revisions made to `σ` (licensed or written, with their steps), so that a change to `Lic` is seen |
| options | the consequence map faced at each decision, the options added through the channel, and whether the world was written directly |

### 1.3 Proper drivers and *working*

Each part is *working* on a run (at `w`, under policy `π`) when the condition in its row
holds. The drivers are stipulated; nothing grounds them in a history or an organization
of the principal. **[survey 5]**

| part | proper driver | working iff |
|---|---|---|
| beliefs | the world, as far as it bears on her questions | (i) no belief coordinate is written directly without authorization; (ii) **calibration**: for every coordinate with a declared truth, her final credence equals the posterior probability, under the uniform prior on `W` and the policy `π` actually played, of that coordinate given the sequence of offerings she received **[survey 1]**; (iii) every due offering was taken up, or the scene declares a truth map (and (ii) decides); (iv) **content**: no other policy of `V`, at the same `w`, applies the same multiset of revisions with grounds and leaves a different belief part |
| decisions | her beliefs and her aims | her judgment is not written directly without authorization. The rule her decisions follow is the first pass's (`judge`; the weighted-sum choice at a decision point) and is a stipulation **[survey 4]** |
| aims and standards | her earlier aims and standards, and what she learns | L3's inductive predicate holds at every step of the run |
| options | the world and her own choices | L0's per-run check passes: every option the history supplies has the history's consequence, and nothing is written to the world directly |

*Authorization.* A direct write to a target is authorized when her seed commitments
contain `("authorize", target)`.

Clause (iv) fixes once that order of delivery is not content. This is resolution (b) of
the first pass's T7, taken with the cost recorded there.

### 1.4 Steered, broken, and the two standards

For a scene, quantifying over `w ∈ W` and pairs `π, π′ ∈ V`:

- a part is **steered** when its trace differs between `π` and `π′` at some `w`;
- a part is **broken** when it is not working on some run and is not steered.

| verdict | arm's-length standard | faithful-adviser standard |
|---|---|---|
| `steered` | some part differs between `π` and `π′` at some `w` and is not working on one of the two runs | some part differs between `π` and `π′` at some `w` |
| `broken, not steered` | not `steered`, and some part is not working on some run | not `steered`, and some part is not working on some run |
| `passes` | neither of the above, and some part differs between two policies | — |
| `not steered` | none of the above | none of the above |

A case with several variants takes their common verdict; if the variants disagree it is
`individuation-dependent` or `out-of-scope(reason)` by the first pass's rule for that
case's mode.

**Acquits** means any verdict other than `steered`.

### 1.5 Attainable value

`AV(g, π)` is the mean over `w ∈ W` of `utility(g, outcome)`, where the run is made with
her seed values set to `g` and the outcome is the scene's declared consequence of her
final judgment at `w` where it declares one, and otherwise the goods the world holds at
the end of the run. `ΔAV(g, π) := AV(g, π) − AV(g, baseline)`.

### 1.6 The other notions compared

- **L0–L3 ∧ W**: the first pass's evaluation, unchanged (`../fixture/evaluate.py`), at
  the scene's declared actual world. *Passes* is its `legitimate`; *fails* its
  `illegitimate`.
- **The replay form**: for every policy of `V`, `Z*` equals the replay `F(e, L)` of the
  first pass.
- **The adviser-side condition** (C8): everything the policy does — offerings with
  their contents and grounds, writes, world-writes, writes `Z` does not read — is the same
  for every policy of `V` at each `w`: the adviser's outputs are one function of the
  world and her seed.

## 2. Abstract layer

`W` a finite set with the uniform prior; `A` a finite ordered set of actions; a goal is
a payoff `g : W × A → P` for a finite set `P` of rationals, and `G` is all of them. A
belief is a nonempty subset `B ⊆ W`. Her decision part, working, takes
`a_g(B) := argmax_a Σ_{w ∈ B} g(w, a)`, ties to the first action.

- A **disclosure** is a function of the world, i.e. a partition of `W`; her belief part,
  working, holds the cell of `w`. `AV(g, f) := mean_w g(w, a_g(cell_f(w)))`. The
  **baseline** is the one-cell partition.
- A **believed lie** is a map `ℓ` from worlds to beliefs with `w ∉ ℓ(w)` for some `w`;
  she holds `ℓ(w)`.
- **Steering by `u`**, for an adviser aim `u : W × A → P`: an action is *inducible* when
  it is `a_g(B)` for some belief `B`; the adviser brings about, at each `w`, the
  inducible action maximizing `u(w, ·)`, ties to the first. `S(g, u)` is her resulting
  mean payoff under `g`.

The sizes of `W`, `A` and `P` are stated with each check in `THEOREMS.md`.

## 3. The statements as tested

The prompt's C1–C8, with what the definitions and the survey make exact.

- **C1.** Abstract layer. (a) For every disclosure `f` and every `g ∈ G`,
  `AV(g, f) ≥ AV(g, baseline)`. (b) For disclosures `f, f′`: `AV(g, f) ≥ AV(g, f′)` for
  every `g` iff `f′` is a coarsening of `f`. Hypothesis, made explicit: her belief and
  decision parts are working. **[survey 2]**
- **C2.** Abstract layer. (a) For every believed lie `ℓ` there is `g ∈ G` with
  `AV(g, ℓ) < AV(g, baseline)`. (b) For every believed lie `ℓ` and every disclosure `f`
  there is `g` with `AV(g, ℓ) ≠ AV(g, f)`.
- **C3.** Fixture layer, on T1 and T2 with `G` as in §1.1. (a) For every `g ∈ G`,
  `ΔAV(g, Offer) ≥ 0` in T2. (b) In T1, `ΔAV(g, Threaten) < 0` for some `g` and
  `ΔAV(g, Threaten) > 0` for none. (c) The criterion "`ΔAV ≥ 0` for every `g`" agrees
  with L0 on T1 and T2; a case where the two disagree is sought.
- **C4.** Abstract layer, for the belief part. For a driver `d` (a disclosure) and a
  family `U(g)` of adviser aims: (weak) for every `g`,
  `AV(g, d) ≥ min_{u ∈ U(g)} S(g, u)`; (strict) with strict inequality for some `g`.
  Tested for three drivers — the full disclosure, a one-bit disclosure, the baseline —
  and three families — *opposed* `{−g}`, *aligned* `{g}`, *all* (`U(g) = G`).
- **C5.** Fixture layer. (a) As written: the faithful-adviser standard acquits iff the
  decisions part is the same for every policy of `V` at every `w`. (b) Its relations to
  L1 (pairwise form) and to the replay form, each implication checked over every variant
  of the thirty-three cases. Abstract layer: (c) two different beliefs give different
  decisions for some `g ∈ G`.
- **C6.** Fixture layer. Every implication among {L0–L3 ∧ W passes, the replay form
  holds, arm's-length acquits, faithful-adviser acquits}, over every variant of the
  thirty-three cases: no counterexample among them, or a named separating variant.
- **C7.** Fixture layer, new cases, `g` her seed aim. The four combinations of
  {faithful-adviser `steered`, not} × {`ΔAV(g, own) > 0`, `< 0`}, each exhibited or
  reported absent; and a `steered` case with every part working.
- **C8.** The adviser-side condition of §1.6, evaluated on every case; what it says of
  T12.
