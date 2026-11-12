# The account against the existing Lean

Definitions and statements were read; proofs were not, and nothing was built. Paths are
under `lean/Workspace/`; a line number is where the declaration starts at commit `28ce3220`.
The account's notions are those of `ACCOUNT.md` §2. No Lean is written in this pass.

## 1. Notion by notion

**The frame.** `Deference/Contrib/Legitimacy.lean:65`

    structure Frame (Q Z Ω X ℛ 𝒱 : Type*) where
      β : Q → Z → Ω
      x : Ω → X
      R : Ω → ℛ
      V : Ω → 𝒱
      D : Set Q

`Q` is the adviser's continuations and `D` the audited class; `Z` is the exterior, which
"carries the principal's policy and nature's coordinate" (`TransparentChannel.lean:9–10`).
The account's `u ↦ σ_u` is a map `U → Q` with `D` its image; `W` and her seed state sit in
`Z`; `S_u(w)` is the reading `R` of `β (σ_u) z`. Difference: the frame has no reading of her
mechanism at a time. Her rule `ρ`, her allowed set `R_t` and `cap_t` have no counterpart.

**Sound.** Nearest: relational authorship at a step with the whole prefix as the grounds,
`LicensedWhole` (`GateIsLegitimacy.lean:253`), the selector-free case of `LicensedAt`
(`:246`):

    def LicensedAt (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
        (Lic : (Party → List E) → Set 𝒱) (h : List ℕ) (e : ℕ) (z : Z) : Prop :=
      ∃ sel : (Party → List E) → (Party → List E),
        (∀ f p, ∀ x ∈ sel f p, x ∈ f p) ∧
        ∀ q ∈ F.D, F.V (F.β q z) e ∈ Lic (sel (I.parts (F.R (F.β q z)) h))

    def LicensedWhole (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
        (Lic : (Party → List E) → Set 𝒱) (h : List ℕ) (e : ℕ) (z : Z) : Prop :=
      ∀ q ∈ F.D, F.V (F.β q z) e ∈ Lic (I.parts (F.R (F.β q z)) h)

With `Lic g := {Bayes(R)(g)}`, the singleton holding the job's output on the grounds `g`,
`LicensedWhole` at every step says her verdict is what the job returns on everything she
has received: *sound* on the runs of the audited class. Differences: (i) `LicensedAt`
itself is weaker: its selector may choose a part of the grounds, and with none chosen the
prior is licensed whatever she received; (ii) `Lic` is a fixed parameter, where the
account's job depends on `R_t`, a coordinate of her state; (iii) both constrain only the
runs of `D`, where *sound* quantifies over every source in `R`, including ones no audited
continuation produces; (iv) the extensional form `ReasonMediated`
(`ReasonMediatedAuthorship.lean:70`: equal reason traces give equal payloads), which
`Legitimacy.Internal.authored` asks (`Legitimacy.lean:74`), is not soundness: it says that
across the audited class her output is *a* function of the trace. The prompt's reading
"*sound* is authorship with integrity" holds for `LicensedWhole` with the job as license
and fails for `ReasonMediated`.

**In range.** `TransparentChannel.lean:63`

    def Realizes (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y) (D : Set Q) : Prop :=
      ∀ q ∈ D, ∀ z, f (β q z) = κ (x (β q z)) z

and at a step `TransparentAt` (`GateIsLegitimacy.lean:311`), `Realizes` for each
non-principal party's contributions. With `f` the input sequence and `κ` a hypothesis of
hers, `Realizes` over the one-element class `{σ_u}` with `x` constant is `h = S_u`.
Differences: (i) `External.transparent` (`Legitimacy.lean:81`) asks `Realizes` for **one**
declared `κ` over the **whole** class `D`. That is neither `α_u > 0` nor `α_u = 1` at one
aim; it is one reference realized at every aim, given the declared inputs. The Lean
already separates the two quantifier orders: `transparent_iff_realizes`
(`TransparentChannel.lean:77`) is the class-level form, and `Witness.picker`
(`TransparentChannel.lean:388`) exhibits two continuations each realizing a reference with
the two-element class not transparent. (ii) The Lean has no set of references with weights
and no `Rep`: there is no declaration for "a source she cannot represent". (iii) In the
consultation model the reference fixes the form of a presentation and not the truth of its
content: `Rows.r20` (`GateIsLegitimacy.lean:1552`) proves a false recommendation through the
declared channel `Counted`. The account's in range fails a believed lie when her allowed
set holds no lying source, so it needs a reference that fixes content from the world, as
`Witness.picker`'s `κfull` does. `Realizes` with one reference makes the trace the same
across aims only where the declared inputs are; it permits dependence through them.

**The adviser as a map from aims.** `GateIsLegitimacy.lean:867`

    def Policy.present (d : Decl) (pol : Policy) (w : Answer) : Presentation

A policy is a function of the wanted answer `w`, and `class_taint`
(`GateIsLegitimacy.lean:1283`) taints any model whose policy puts a reference-fixed
dimension off its declared value at some wanted answer. The account's `u ↦ σ_u` is this,
with `U = Answer`. Difference: the Lean has no null aim, and no attribution: a segment is
tainted or not, "whatever caused a failure" (`Legitimacy.lean:18–19`).

**Maintained, M1.** Two declarations each supply part.

`TransparentChannel.lean:345`

    theorem tower_factor {C G E : Type*} (β : Q → Z → Ω) (D : Set Q) (Amend : C → G → E → C)
        (spec : ℕ → Ω → C) (g : ℕ → Ω → G) (e : ℕ → Ω → E) (c₀ : C)
        (h0 : ∀ q ∈ D, ∀ z, spec 0 (β q z) = c₀)
        (hstep : ∀ t, ∀ q ∈ D, ∀ z,
          spec (t + 1) (β q z) = Amend (spec t (β q z)) (g t (β q z)) (e t (β q z))) :
        ∀ t, ∀ q ∈ D, ∀ q' ∈ D, ∀ z,
          (∀ s < t, g s (β q z) = g s (β q' z) ∧ e s (β q z) = e s (β q' z)) →
          spec t (β q z) = spec t (β q' z)

With `C` her rule and allowed set, `spec t` their reading at step `t`, `Amend` her own
transition, `g` the inputs and `e` the authorized writes, the hypotheses `h0` and `hstep`
are M1 for the coordinates `ρ` and `R`, and the conclusion is that her rule at `t` is the
same under two continuations that agree on the inputs **and the authorized events** so
far. So `tower_factor` already states what M1 buys for the rule, with the second agreement
that *uniformly in range* also has to ask (`THEOREMS.md`, statement 2).

`GateIsLegitimacy.lean:912`

    def evalAt {L : Type} : Prog → List (EventKind L) → Prog
      | p, [] => p
      | _, .amend _ p' :: ks => evalAt p' ks
      | p, _ :: ks => evalAt p ks

"The evaluator as a state: updated only by licensed amendments." This is the transition
M1 describes for her evaluator in the consultation model, with `auth` as the license slot
of `EventKind.amend` (`:903`). The slot is carried and not validated; that file
instantiates it trivially.

For her outputs `b_t` and `v_t`, M1 has no counterpart. `ReasonMediated` is a comparison
across the audited class, not a statement of where a change came from: an unauthorized
write that is the same in every audited continuation satisfies it, and an authorized write
that depends on the aim satisfies M1 and violates it.

**Maintained, M2.** Nearest: `Normativity/Contrib/OpenIntegrityEvolution.lean:217`

    def OpenAt (sem : OpennessSemantics S anchor Γ J R) (O : ObligationState S anchor) : Prop :=
      ∀ c, (sem O c).RobustOpenActual

asked at every state by `External.openAll`. `OpenAt` says every live concern has a route at
that state; `OpennessSemantics` is external data. Difference: it is a condition on the
record's routes, not on her capacity to judge, and holds or fails at a state, where M2
compares a quantity across a stretch. The prompt's "*maintained* is partly `OpenAt`" is
right only in that both are what the adviser must not disturb; no declaration measures
`cap`.

**Legitimate stretch; `K`.** `GateIsLegitimacy.lean:361` (`Segment`, internal ∧ external on
its own steps) and `:474`

    def Counted … : Prop := Nonempty (Segment I F Lic sem κ O₀ O₁)

A legitimate stretch is a `Segment` whose license is the job on the whole prefix (sound),
whose `κ` is a member of her allowed set (in range) and whose `spec` obeys `tower_factor`'s
`hstep` (M1). Difference:
`Segment` has no field for M1 on the rule or for M2. `Legitimacy.lean:35–38` records that
legitimacy does not certify a starting state; the account's stretch likewise starts from a
state it does not judge.

**Her own change.** No declaration. `Segment.trans` (`GateIsLegitimacy.lean:382`) composes
segments, which is what "within a legitimate stretch" needs.

**Manipulation, internal and external.** No declaration; the Lean has taint without
attribution. `Rows.r19` (`GateIsLegitimacy.lean:1540`) is external manipulation of a
tie-break: both verdicts licensed, the step not transparent.

**The defects.** `TransparentChannel.lean:197`

    noncomputable def defect (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y) (q : Q) :
        Z → ℝ :=
      disagree (fun z => f (β q z)) (fun z => κ (x (β q z)) z)

is the pathwise in-range defect: the indicator of the exteriors where the actual input
sequence differs from the reference's; its expectation is the probability of departure.
`abs_expect_sub_le_width` (`:252`) and `expect_disagree_le` (`:240`) bound what a payload of
bounded width moves by under it. Difference from `1 − α_u`: the expectation of `defect` is
the probability that the source departs from one reference; `1 − α_u` is the weight she
puts on other hypotheses. Neither determines the other. These bound a payload; a gate
that scores a stretch by whether the source *is* the reference is not bounded by them
(`THEOREMS.md`, statement 4).

**`posterior_weight_eq`** (`TransparentChannel.lean:334`): under `Realizes`, the posterior
weight computed with the actual likelihood equals the one computed with the reference
likelihood, for every prior. This is "exactly in range and sound together give the right
posterior", the step statements 1 and 6 need.

**`GradeTrust`** (`DelegationBridge.lean:52`)

    def GradeTrust (EX W : C → P → ℚ) (η : ℚ) : Prop :=
      ∀ x π, |EX x π - W x π| ≤ η

`W` is the principal's grade, and the declaration takes it as given. Manufactured trust
moves `W`. The account bears on `GradeTrust` only through M1: under M1, `W` is produced by
her own rule, so it is not a quantity the adviser sets.

**`Legit`** (`DeconfusingCorrigibility.lean:115`)

    structure Scoring (H : Type*) extends Params where
      Legit : H → Prop
      N : H → ℕ
      V : H → ℝ
      V_legit : ∀ h, Legit h → 0 ≤ V h ∧ V h ≤ 1
      V_illegit : ∀ h, ¬ Legit h → -δ ≤ V h ∧ V h < 0

Statement 8 of `THEOREMS.md` says what the account puts here.

## 2. What the frame needs for the principal's policy to evolve

The obstacle is narrower than "an adviser changing how she judges is not expressible". The
frame's outcome `β q z` depends on `q`, so any reading of it may: a write shows up as a
payload that does not factor through the reason trace, and `ReasonMediated` fails. What is
missing is a reading of *how she judges at step t*, against which a later verdict could be
called sound or a change of rule called her own. Three additions would supply it.

1. A reading `spec : ℕ → Ω → C` of her mechanism and allowed set at each step, with
   `tower_factor`'s `h0` and `hstep` as fields of the segment. `tower_factor` then gives M1's
   consequence without new proof. **Supplied in part**: the theorem exists; no `Segment`
   carries its hypotheses, and `evalAt` is the one instance.
2. A license indexed by that reading, `Lic : C → (Party → List E) → Set 𝒱`, with
   `LicensedWhole` asked at step `t` for `Lic (spec t ω)`. **No encoding supplied**:
   `LicensedAt` takes one `Lic` for the whole segment. A fixed `Lic` could rebuild the
   standards in force from an amendment history carried in the grounds, so the type does
   not forbid it; no declaration does it, or proves that a change of standards is itself a
   licensed verdict.
3. A family of references with weights in place of the single `κ`, and a predicate for the
   sources she can represent. **Not supplied.**

`cap` and `Res` (M2) need a fourth addition that nothing existing resembles.
