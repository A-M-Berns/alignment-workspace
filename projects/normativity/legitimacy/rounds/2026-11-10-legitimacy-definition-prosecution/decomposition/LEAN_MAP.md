# The account against the existing Lean

Definitions and statements were read; proofs were not, and nothing was built. Paths are
under `lean/Workspace/Deference/Contrib/`; a line number is where the declaration starts
at commit `79563886`. The account's notions are those of `ACCOUNT.md`. No Lean is written
in this pass. `../teleology/LEAN_MAP.md` maps the earlier statement of the account onto
the same files and is not repeated.

## 1. The frame

`Legitimacy.lean:65`

    structure Frame (Q Z Ω X ℛ 𝒱 : Type*) where
      β : Q → Z → Ω
      x : Ω → X
      R : Ω → ℛ
      V : Ω → 𝒱
      D : Set Q

`Q` is the adviser's continuations, `D` the audited class, `Z` the exterior, `β q z` the
outcome. In the account's model `Q` is the adviser's action sequences (or policies), `Z`
is the world, and `β q z` is the run of §1: every part's view and move at every step.
Difference: the frame names one reading `R` (the reason trace) and one payload `V`. The
account needs a reading pair per part, `see_p` and `move_p`, and a scoring `g_p` of the
outcome that no field of `Frame` or `TFrame` (`GateIsLegitimacy.lean:218`) carries. A
candidate is not an object of the Lean.

## 2. Mechanism running, and force

`ReasonMediatedAuthorship.lean:70`

    def ReasonMediated (β : Q → Z → Ω) (R : Ω → ℛ) (V : Ω → 𝒱) (D : Set Q) (z : Z) : Prop :=
      ∀ q ∈ D, ∀ q' ∈ D, R (β q z) = R (β q' z) → V (β q z) = V (β q' z)

With `R := see_p` and `V := move_p`, `ReasonMediated β see_p move_p D z` says that across
the audited class, at the world `z`, `p`'s move is a function of `p`'s view. That holds
when `p`'s mechanism is the same and running under every `q ∈ D`, and it fails when some
`q` forces `p`'s move or writes `p`'s mechanism and another does not. So *not forced, over
the class* is `ReasonMediated` for the pair (`see_p`, `move_p`). Difference: it is a
comparison across the class at one world, so a force applied by every `q ∈ D` satisfies
it; the account's force is a property of one action. `Legitimacy.Internal.authored`
(`Legitimacy.lean:74`) asks this for the one pair (`R`, `V`).

## 3. `Realizes`, fit, and the zero-gap condition

`TransparentChannel.lean:63`

    def Realizes (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y) (D : Set Q) : Prop :=
      ∀ q ∈ D, ∀ z, f (β q z) = κ (x (β q z)) z

Three instantiations, and what each is.

**(a) `x := see_p`, `f := move_p`, `κ` not reading `z`.** `Realizes` says `p`'s move is
`κ` of its view under every audited continuation at every world: `κ` is `p`'s mechanism.
This is **fit** for one part, not zero gap.

**(b) `f := move_p`, `κ(x, z) :=` the best move of `p` by `g_p`.** The best move depends on
the world, the adviser's action and the other parts' moves. Take `x` to be a view that
carries the adviser's action and the other moves, and let `κ` read the world through `z`.
Then `Realizes` says `p`'s move is the best move at every world under every audited
continuation: **zero gap for `p` on the class**, provided the best move is unique. So the
answer to the dispatch's question is: `Realizes` for a reference is the zero-gap condition
for one part when the reference is *the best-move selector of that part's goal function*
and the declared-input view is replaced by the facts that goal function reads. "Declared"
is replaced by "derived from the candidate": the reference is not announced by the
adviser, it is computed from `g_p`. Three exact differences remain. (i) A goal function's
best moves are a set; `Realizes` needs a function, so the condition is `move_p ∈ Best_p`,
a relation the declaration does not express. (ii) `Realizes` asks it at every world and
every continuation; the account asks that the adviser's action not *widen* the gap
against a comparison, which is a statement about two continuations at one world.
(iii) The account's reference depends on the candidate, and the adviser holds several.

**(c) As used in the workspace: `f :=` the adviser's contributions.** `External.transparent`
(`Legitimacy.lean:81`) and `TransparentAt` (`GateIsLegitimacy.lean:311`)

    def TransparentAt (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
        (κ : Party → X → Z → List E) (e : ℕ) : Prop :=
      ∀ p, p ≠ I.principal →
        Realizes F.β (fun ω => F.x ω e) (fun ω => sourced p (I.entriesAt (F.R ω) e)) (κ p) F.D

constrain what the adviser puts in, not what her part puts out. This is the account's
*declared reference* comparison action (statement 6 of the dispatch): the adviser's action
equals the reference's at every world. It implies no gap is widened against that reference
and says nothing about the gap the reference itself leaves.

`defect` (`TransparentChannel.lean:197`)

    noncomputable def defect (β : Q → Z → Ω) (x : Ω → X) (f : Ω → Y) (κ : X → Z → Y) (q : Q) :
        Z → ℝ :=
      disagree (fun z => f (β q z)) (fun z => κ (x (β q z)) z)

is, under (b), the indicator of the worlds where `p`'s gap is positive. The account's gap
is graded; `defect` is its support. `abs_expect_sub_le_width` (`:252`) then bounds the
expected loss of a payload of bounded width by the probability of a positive gap times the
width, which is the bound statement 5 of the dispatch asks for in its coarsest form.

## 4. The kinds of influence

No declaration. The Lean has taint without attribution: a segment is counted or not
"whatever caused a failure" (`Legitimacy.lean`, header §2). Help, harm and subversion each
compare two continuations at one world; the nearest declarations are the pair-class
notions `Blind` (`ReasonMediatedAuthorship.lean:123`)

    def Blind (β : Q → Z → Ω) {X : Type*} (f : Ω → X) (P : Set (Q × Q)) (z : Z) : Prop :=
      ∀ p ∈ P, f (β p.1 z) = f (β p.2 z)

and `SelectionBlind` (`:178`). With `P := {(a, a′)}` and `f := gap_p`, `Blind` says the
action and its comparison leave the same gap: neither help by narrowing nor subversion.
Difference: `Blind` is an equality; the account needs the order (`≤`) and a second reading
(`best_p`).

## 5. Admissibility

No declaration corresponds to *nothing left over*, *never opposed*, *mostly serving*,
*independent* or *carriable*. The nearest is the license of relational authorship,
`LicensedWhole` (`GateIsLegitimacy.lean:253`)

    def LicensedWhole (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
        (Lic : (Party → List E) → Set 𝒱) (h : List ℕ) (e : ℕ) (z : Z) : Prop :=
      ∀ q ∈ F.D, F.V (F.β q z) e ∈ Lic (I.parts (F.R (F.β q z)) h)

`Lic g` is a set of verdicts allowed on grounds `g`. An *input-scored* goal function is a
license: `Lic g := Best_p` computed from what the part was handed. A *world-scored* goal
function is not, since `Lic` reads the grounds and not the exterior `z`. So the Lean's
authorship is the input-scored reading of serving, and the account's "best is judged by
how things are" has no counterpart there.

## 6. Values and alterations

`tower_factor` (`TransparentChannel.lean:345`) and `evalAt` (`GateIsLegitimacy.lean:912`)
are quoted in `../teleology/LEAN_MAP.md` §1. With `C` the mechanisms in force, `spec t`
their reading at step `t` and `Amend` the effect of the step's alteration moves,
`tower_factor`'s `hstep` says the mechanisms change only by her parts' moves: no write by
the adviser. Its conclusion is that the mechanisms at `t` agree under two continuations
that agree on the inputs and events before `t`. Difference: it says the change came
through her parts; it does not say those parts were serving. *In order* (`ACCOUNT.md` §6)
is `hstep` together with no subversion of a producer, and the second half has no
declaration.

## 7. Drift and the cut-off

`Legitimacy.lean:191`, `:196`, `:236`

    noncomputable def lastReport (s : ℕ → ℝ) (θ : ℝ) : ℕ → ℕ
      | 0 => 0
      | t + 1 => if θ ≤ s (t + 1) - s (lastReport s θ t) then t + 1 else lastReport s θ t

    theorem unreported_lt (s : ℕ → ℝ) (θ : ℝ) (hθ : 0 < θ) (t : ℕ) :
        s t - s (lastReport s θ t) < θ

    theorem salami_cumulative (ε θ : ℝ) (hε : 0 < ε) (hθ : ε < θ) (t : ℕ) : …

With `s t` the gap of a part at step `t` under the adviser's actions less the gap under
the comparison, a per-step cut-off `θ` on `s (t+1) − s t` is passed by steps of size
`ε < θ` for ever, and the cumulative rule reports whenever the widening since the last
report reaches `θ`. The workspace already has the theorem a cumulative cut-off needs;
the account's gap supplies the sequence `s`.

## 8. `Legit`, `N`, `v`

`DeconfusingCorrigibility.lean:115`, `:242`, `:258`, `:261`, `:404`, `:451`

    structure Scoring (H : Type*) extends Params where
      Legit : H → Prop
      N : H → ℕ
      V : H → ℝ
      V_legit : ∀ h, Legit h → 0 ≤ V h ∧ V h ≤ 1
      V_illegit : ∀ h, ¬ Legit h → -δ ≤ V h ∧ V h < 0

    structure Decision (H Ω A : Type*) [Fintype Ω] extends Scoring H where
      μ : Ω → ℝ
      μ_nonneg : ∀ ω, 0 ≤ μ ω
      μ_sum : ∑ ω, μ ω = 1
      hist : A → Ω → H

    noncomputable def v (a : A) : ℝ := expectR D.μ fun ω => ind (1 ≤ D.N (D.hist a ω))
    def Respects (astar : A) : Prop := ∀ ω, D.N (D.hist astar ω) = 0
    def UnbiasedFromFeedback : Prop := ∀ γ > 0, ∃ N₀, ∀ K ≥ N₀, Q.excess Q.a K ≤ γ

`Legit` is any predicate on histories; Theorem 1 uses nothing else about it. The
account's shapes fit as follows; statement 6 of the dispatch gives the predicate.

- `H`: a history must determine the gaps, so it carries the world, the adviser's actions,
  the comparison actions and the candidate. A history of observed actions alone does not.
- `Ω` in `Decision`: worlds × admissible candidates, with `μ` the product of the adviser's
  credence and its weights. `hist a (w, c)` is the run of `c` at `w` under `a`. The
  account's weighted set is what makes `Decision` constructible; the second follow-up's
  account built none.
- `N`: not supplied by the account. The account supplies one ingredient of a definition:
  whether a verdict of hers is *standing* (`ACCOUNT.md` §7), which is what "settled
  without a legitimate judgment from its holder" needs. Which matters are reserved is the
  post's.
- `Respects`: an action under which no reserved matter is settled without a standing
  verdict at any `(w, c)`. The null action is one when silence forces nothing.
- `UnbiasedFromFeedback` compares estimates with realized scores; realized `V` depends on
  `Legit`, hence on the candidate, which no feedback reveals directly.
