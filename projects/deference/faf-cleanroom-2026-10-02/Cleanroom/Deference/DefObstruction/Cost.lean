import Cleanroom.Deference.DefObstruction.Fragment
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# `def-obstruction` · Cost: 2b's arithmetic skeleton, the schedule of record, no bridge axiom, pull (T9–T11)

**T9 — 2b stays arithmetic.** The cost regress (`regress`, `cost_circularity`), the
realizability of its non-cost hypotheses (`cost_setup_realizable`: the blame falls on the
timely-cost step `hcost`) and of the blind alternative (`blind_cost_realizable`: an `A`-free
target cost `R_H ∘ F` can be dominated by a strictly increasing `R_A`), ported over `ℕ → ℝ` with
FAF's `DeferralFunction` where the source has `F`. **The timely-cost step is ill-posed over FAF**
(findings F-2b): `IsLogicalInductor` has one trader class and no runtime; "`𝒞_H ⊊ 𝒞_A`" and
"`𝒞_A ∋ R ∘ F`" have no objects. Nothing here claims otherwise; these rows are kind `L`/`N`. The
**schedule of record** `(e, F, σ)` with `e(n) < F(n) < σ(n)` is a definition (`Schedule`), with
the inhabitant `Schedule.ofRecord` (`n+1 < n+2 < n+3`). The **horizon cap** is one line
(`horizon_cap`); the conflict between v6 §3 and chat 03 about what it buys is findings F-Horizon.

**T10 — no bridge axiom.** A stage containing `β`, the link `β → ψ` (NNF: `∼β ⋎ ψ`) and `∼ψ` has
no consistent world (`no_bridge_axiom`); likewise with a biconditional link
(`no_bridge_axiom_iff`). Consequence (recorded, not proved): what moves the advised reader's
credence toward the quote is learned deference, never an axiom; a ledger-to-credence
"reflection axiom" is either this inconsistency or unstated (findings F-ReflectionAxiom).

**T11 — pull.** Definitions of record: the deadline gap `gap` between the advised and the
autonomous reader, the resolved-late (`ResolvedLate`) and never-decided (`NeverDecided`) index
predicates; the triangle-inequality lemma (`pull_th4`, `pull_th4_gap`) and the split sum
(`pull_th9`). Six of the chat's twelve "theorems" are definitions (findings F-Pull).

Scope: real sequences and single processes; nothing here is a headline.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## A. T9: the arithmetic skeleton of 2b -/

/-- **The regress, bare**: a strictly increasing cost cannot dominate its own `F`-composition
when `F` strictly advances the stage.
Scope: real sequences.
Source: [[self-referential-settlement-target]] §3.2 (boxed chain; anson-004); `SelfReferentialTarget.lean:regress`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem regress (RA : ℕ → ℝ) (F : ℕ → ℕ) (hmono : StrictMono RA) (hF : ∀ n, n < F n) :
    ¬ (∀ n, RA (F n) ≤ RA n) := by
  intro h
  have : RA 0 < RA (F 0) := hmono (hF 0)
  linarith [h 0]

/-- **Cost-circularity, structured**: with `hshare` (total coupled cost dominates `A`'s share) and
the **timely-cost step** `hcost` (`A` pays, by stage `n`, the coupled cost through `F n`), a
strictly increasing `R_A` is contradictory. `hcost` is the source's ~75–80% soft joint; it is a
hypothesis here, and over FAF it has no object to be a theorem about (findings F-2b).
Scope: real sequences.
Source: [[self-referential-settlement-target]] §3.2 (anson-004, anson-005); `SelfReferentialTarget.lean:cost_circularity`
Kind: L
Fidelity: exact
Hyps: (c) `hcost` — the timely-cost step, ill-posed over FAF (no resource model); `hshare` the source's "total ≥ `A`'s share" -/
theorem cost_circularity (R RA : ℕ → ℝ) (F : ℕ → ℕ) (hmono : StrictMono RA) (hF : ∀ n, n < F n)
    (hshare : ∀ n, RA (F n) ≤ R (F n)) (hcost : ∀ n, R (F n) ≤ RA n) : False := by
  have h1 : RA 0 < RA (F 0) := hmono (hF 0)
  have h2 : RA (F 0) ≤ RA 0 := le_trans (hshare 0) (hcost 0)
  linarith

/-- **Cost-circularity with FAF's deferral function** in place of `F`.
Scope: real sequences; deferral `F`.
Source: anson-2-009 (`DeferralFunction` as the rendering of `F`)
Kind: L
Fidelity: exact
Hyps: (c) `hcost` as in `cost_circularity` -/
theorem cost_circularity_deferral (R RA : ℕ → ℝ) (F : DeferralFunction) (hmono : StrictMono RA)
    (hshare : ∀ n, RA (F n) ≤ R (F n)) (hcost : ∀ n, R (F n) ≤ RA n) : False :=
  cost_circularity R RA F.f hmono F.lt hshare hcost

/-- **The non-cost hypotheses are jointly realizable**, so the contradiction in
`cost_circularity` falls on the timely-cost step alone.
Scope: real sequences.
Source: [[self-referential-settlement-target]] §10 ("Non-vacuity"); `SelfReferentialTarget.lean:cost_setup_realizable`
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem cost_setup_realizable :
    ∃ (R RA : ℕ → ℝ) (F : ℕ → ℕ),
      StrictMono RA ∧ (∀ n, n < F n) ∧ (∀ n, RA (F n) ≤ R (F n)) ∧
      ¬ (∀ n, R (F n) ≤ RA n) := by
  refine ⟨fun n => (n : ℝ), fun n => (n : ℝ), fun n => n + 1, ?_, ?_, ?_, ?_⟩
  · intro a b h
    show (a : ℝ) < b
    exact_mod_cast h
  · intro n; show n < n + 1; omega
  · intro n; exact le_refl _
  · intro h
    have h0 := h 0
    norm_num at h0

/-- **The blind alternative is realizable**: an `A`-free target cost `R_H ∘ F` can be dominated by
a strictly increasing `R_A` with `F` strictly advancing — the structural contrast with
`cost_circularity` ([[AUDIT]] §3.6: the complexity content "P ⊊ EXP" is interpretation laid on
top of this; nothing here models a complexity class).
Scope: real sequences.
Source: [[frozen-deliberation-deference-v6]] §5; `FrozenDeliberation.lean:blind_cost_realizable`; lean-deference-018; root-deference-022
Kind: N−
Fidelity: exact (as abstract arithmetic; the complexity-class reading is not modelled)
Hyps: (a) none -/
theorem blind_cost_realizable :
    ∃ (RH RA : ℕ → ℝ) (F : ℕ → ℕ),
      StrictMono RA ∧ (∀ n, n < F n) ∧ ∀ n, RH (F n) ≤ RA n := by
  refine ⟨fun n => (n : ℝ), fun n => (n : ℝ) + 1, fun n => n + 1, ?_, ?_, ?_⟩
  · intro a b h
    show (a : ℝ) + 1 < (b : ℝ) + 1
    have : (a : ℝ) < b := by exact_mod_cast h
    linarith
  · intro n; show n < n + 1; omega
  · intro n
    show ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1
    push_cast
    exact le_refl _

/-! ## B. The schedule of record -/

/-- The deferral `n ↦ n + 2`: the one that leaves room for a next-day publication strictly
before the lookahead (`e(n) = n + 1 < F(n)`). Same construction as FAF's `succDeferral`.
Scope: schedule.
Source: anson-2-009 (`F(n) > n + 1`); [[self-referential-settlement-target]] §0.2
Kind: D
Fidelity: exact
Hyps: n/a -/
def plusTwoDeferral : DeferralFunction where
  f := fun n => n + 1 + 1
  lt n := by omega
  graph_fp :=
    ⟨fun z : List Bool =>
        List.replicate (if z.length.unpair.1 + 1 + 1 = z.length.unpair.2 then 1 else 0) false,
      UnaryRuler.eqFlag UnaryRuler.unpairFst.succ.succ UnaryRuler.unpairSnd,
      fun n m => by simp⟩

/-- **The schedule of record** `(e, F, σ)`: emission, deferral, settlement, ordered
`e(n) < F(n) < σ(n)`. `e` and `σ` are `li-quote-lane`'s publication schedules, `F` is FAF's
deferral function. (`def-frozen-sibling`'s carrier carries the same two inequalities as fields;
cited, not imported.)
Scope: schedule.
Source: anson-2-009 (chat 04: "minimal schedule = ordering `e(n) < F(n) < σ(n)`"); [[self-referential-settlement-target]] §0.2
Kind: D
Fidelity: exact (the efficiency clause and the power assumption of anson-2-009 are not part of the schedule; the power assumption has no FAF object)
Hyps: n/a -/
structure Schedule where
  /-- Emission: when `A`'s day-`n` quote is posted. -/
  e : PublicationSchedule
  /-- Deferral: the day the reader's credence is read. -/
  F : DeferralFunction
  /-- Settlement: when `A`'s contract settles. -/
  σ : PublicationSchedule
  /-- Emission precedes the lookahead. -/
  e_lt_F : ∀ n, e.e n < F.f n
  /-- The lookahead precedes settlement. -/
  F_lt_σ : ∀ n, F.f n < σ.e n

/-- The schedule `n+1 < n+2 < n+3` inhabits the schedule of record.
Scope: schedule.
Source: anson-2-009
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
def Schedule.ofRecord : Schedule where
  e := PublicationSchedule.succ
  F := plusTwoDeferral
  σ := ⟨fun n => n + 3, fun n => by omega⟩
  e_lt_F n := by show n + 1 < n + 1 + 1; omega
  F_lt_σ n := by show n + 1 + 1 < n + 3; omega

/-- **The horizon cap**: if `R_H(t) ≤ 2^{p(t)}` with `p` monotone and `F ≤ q`, then
`R_H(F(n)) ≤ 2^{p(q(n))}`. Elementary; what it does *not* say is that any particular class
affords `F = 2^n` — v6 §3's "EXP suffices for `F = 2^n`" and chat 03's estimate conflict on the
per-stage cost of the construction, which no theorem here settles (findings F-Horizon).
Scope: real sequences.
Source: anson-028 (chat 03 L4178–4188; [[frozen-deliberation-deference-v6]] §3)
Kind: L
Fidelity: exact (the cap arithmetic only)
Hyps: (a) none -/
theorem horizon_cap (R : ℕ → ℝ) (p q F : ℕ → ℕ) (hp : Monotone p)
    (hR : ∀ t, R t ≤ 2 ^ p t) (hF : ∀ n, F n ≤ q n) (n : ℕ) :
    R (F n) ≤ 2 ^ p (q n) :=
  (hR _).trans (pow_le_pow_right₀ (by norm_num) (hp (hF n)))

/-! ## C. T10: no bridge axiom -/

/-- **No bridge axiom**: a stage containing a ledger literal `β`, a link `β → ψ` (in NNF,
`∼β ⋎ ψ`) and the contrary decision `∼ψ` has no consistent world. So an axiom tying a ledger
profile to a contract's truth value is inconsistent with the process later deciding the contract
against it — and FAF's criterion over a process with an unsatisfiable stage is vacuous
(`isLogicalInductor_of_stage_unsatisfiable`), not informative.
Scope: one process.
Source: anson-2-015 (chat 05 L10920–10928, "pinning is not a separate lemma"); mandate T10
Kind: L
Fidelity: exact (NNF rendering of the implication)
Hyps: (a) none -/
theorem no_bridge_axiom (DP : DeductiveProcess) (s : ℕ) (β ψ : Sentence)
    (hβ : β ∈ DP.D s) (hlink : (∼ β ⋎ ψ) ∈ DP.D s) (hψ : (∼ ψ) ∈ DP.D s) :
    ¬ ∃ v : PCWorld, v.ConsistentWith (DP.D s) := by
  rintro ⟨v, hv⟩
  have h1 := hv β hβ
  have h2 := hv _ hlink
  have h3 := hv _ hψ
  rw [PCWorld.holds_or, PCWorld.holds_neg] at h2
  rw [PCWorld.holds_neg] at h3
  rcases h2 with h2 | h2
  · exact h2 h1
  · exact h3 h2

/-- **No bridge axiom, biconditional link**: with `β ↔ ψ` (NNF: `(∼β ⋎ ψ) ⋏ (∼ψ ⋎ β)`) in place
of the implication.
Scope: one process.
Source: anson-2-015; mandate T10 ("the biconditional link and the contrary decision")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem no_bridge_axiom_iff (DP : DeductiveProcess) (s : ℕ) (β ψ : Sentence)
    (hβ : β ∈ DP.D s) (hlink : ((∼ β ⋎ ψ) ⋏ (∼ ψ ⋎ β)) ∈ DP.D s) (hψ : (∼ ψ) ∈ DP.D s) :
    ¬ ∃ v : PCWorld, v.ConsistentWith (DP.D s) := by
  rintro ⟨v, hv⟩
  have h1 := hv β hβ
  have h2 := hv _ hlink
  have h3 := hv _ hψ
  rw [PCWorld.holds_and, PCWorld.holds_or, PCWorld.holds_neg] at h2
  rw [PCWorld.holds_neg] at h3
  rcases h2.1 with h2 | h2
  · exact h2 h1
  · exact h3 h2

/-! ## D. T11: pull — definitions of record and the two lemmas -/

/-- **The deadline gap** between the advised reader `H` and the autonomous reader `H₀` on the
day-`n` contract: `gap n := |𝔼^H_{F n}(X_n) − 𝔼^{H₀}_{F n}(X_n)|`.
Scope: two readers, one deferral.
Source: anson-2-016 (chat 05: `g^A_n`); mandate T11
Kind: D
Fidelity: exact (FAF's grid expectations at day `F n`)
Hyps: n/a -/
noncomputable def gap (H H₀ : History) (F : DeferralFunction) (X : ℕ → LUV) (n : ℕ) : ℝ :=
  |(X n).expect H (F n) - (X n).expect H₀ (F n)|

/-- **Resolved late**: the day-`n` contract is not decided (either way) by stage `F n`, but is
decided at some stage.
Scope: one process.
Source: anson-2-016 (`R`)
Kind: D
Fidelity: variant: semantic "decided"
Hyps: n/a -/
def ResolvedLate (DP : DeductiveProcess) (F : DeferralFunction) (X : ℕ → Sentence) (n : ℕ) :
    Prop :=
  (¬ (∀ v : PCWorld, v.ConsistentWith (DP.D (F n)) → v.Holds (X n)) ∧
    ¬ (∀ v : PCWorld, v.ConsistentWith (DP.D (F n)) → ¬ v.Holds (X n))) ∧
  Decided DP (X n)

/-- **Never decided**: the day-`n` contract is decided at no stage.
Scope: one process.
Source: anson-2-016 (`Φ`)
Kind: D
Fidelity: variant: semantic "decided"
Hyps: n/a -/
def NeverDecided (DP : DeductiveProcess) (X : ℕ → Sentence) (n : ℕ) : Prop :=
  ¬ Decided DP (X n)

/-- **Pull Th 4 (the triangle inequality)**: under Tracking `a_n − Y_n → 0`, the gap
`|Y_n − Y⁰_n|` and the quote's distance to the autonomous reader `|a_n − Y⁰_n|` agree in the
limit.
Scope: real sequences.
Source: anson-2-016 (pull Th 4)
Kind: L
Fidelity: exact
Hyps: (c) Tracking (`hT`), the mirror-target hypothesis 2a kills on the diagonal -/
theorem pull_th4 (a Y Y₀ : ℕ → ℝ) (hT : Tendsto (fun n => a n - Y n) atTop (𝓝 0)) :
    Tendsto (fun n => |Y n - Y₀ n| - |a n - Y₀ n|) atTop (𝓝 0) := by
  have hT' : Tendsto (fun n => |a n - Y n|) atTop (𝓝 0) := by simpa using hT.abs
  refine squeeze_zero_norm (fun n => ?_) hT'
  rw [Real.norm_eq_abs]
  calc |(|Y n - Y₀ n| - |a n - Y₀ n|)| ≤ |(Y n - Y₀ n) - (a n - Y₀ n)| :=
        abs_abs_sub_abs_le_abs_sub _ _
    _ = |a n - Y n| := by rw [abs_sub_comm]; congr 1; ring

/-- **Pull Th 4 over the carrier**: with `X` the contract family, `Y_n := 𝔼^H_{F n}(X_n)` and
the autonomous reader `H₀`.
Scope: one-way (advised reader) plus an autonomous reader.
Source: anson-2-016 (pull Th 4)
Kind: L
Fidelity: exact
Hyps: (c) Tracking (`hT`) -/
theorem pull_th4_gap (T : TablePair) (H₀ : History) (F : DeferralFunction) (X : ℕ → LUV)
    (hT : Tendsto (fun n => (T.a 0 n : ℝ) - (X n).expect T.H (F n)) atTop (𝓝 0)) :
    Tendsto (fun n => gap T.H H₀ F X n - |(T.a 0 n : ℝ) - (X n).expect H₀ (F n)|)
      atTop (𝓝 0) :=
  pull_th4 _ _ _ hT

/-- **Pull Th 9 (the split sum)**: a summable weighted gap splits over an index set and its
complement.
Scope: real sequences.
Source: anson-2-016 (pull Th 9: `Σ_n μ_n g_n = Σ_{n∈R} + Σ_{n∈Φ}`)
Kind: L
Fidelity: exact (`S` any index set; the source's `R`/`Φ` partition is the instance)
Hyps: (a) none (summability is the statement's own hypothesis) -/
theorem pull_th9 (f : ℕ → ℝ) (S : Set ℕ) (hf : Summable f) :
    ∑' n, f n = ∑' n, S.indicator f n + ∑' n, Sᶜ.indicator f n := by
  rw [← (hf.indicator S).tsum_add (hf.indicator Sᶜ)]
  congr 1
  funext n
  exact (Set.indicator_self_add_compl_apply S f n).symm

end Cleanroom.Deference.DefObstruction
