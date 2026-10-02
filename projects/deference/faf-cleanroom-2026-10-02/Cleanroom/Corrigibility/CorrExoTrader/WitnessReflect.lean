import Cleanroom.Corrigibility.CorrExoTrader.Reflect

/-!
# `corr-exo-trader` · WitnessReflect: the LI-level N+ for the wireheading identity (T4.3, T5.2)

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 10 of the
layout. Over `bli-found`'s atoms, no `Construction.*`.

`udt-bli-core`'s `pushPrior` (`Wirehead.lean`: `T_hi = 9/10`, `T_lo = 1/10`, `μ(T_hi | push) =
9/10`, `μ(T_hi | honest) = 1/10`) is the finite push-eliciting witness; it is **cited, not
duplicated**. The LI-level N+ here is a two-state `StateSystem` (`pushSystem`: candidate codes
`{0, 1}`, verdict `1/10` for state `0` and `9/10` for state `1`) and a history `pushHist` on
`Sentence` with the same numbers (action `0` = honest, `1` = push; each action has mass `1/2`;
`P(state 1 ⋏ push) = 9/20`, `P(state 1 ⋏ honest) = 1/20`), defined **uniformly by decoding the
sentence's shape** — a history is a function on all sentences, so "finitely many sentences" is
realized as finitely many *shapes*: state-and-action cells, their `φ`-refinements, action cells and
action atoms; every other sentence is priced `0`. It satisfies `E2xAct` and `E5Act`
(`pushHist_e2xAct`, `pushHist_e5Act`), so `wirehead_identity_li` is exercised with `S.val`
differing across states, and the α-value ranks push (`41/100`) above honest (`9/100`) while the
β-value is indifferent (`pushHist_alpha_push_gt_honest`, `pushHist_beta_indifferent`). The
decoders are inverted exactly (`eq_of_decodeState`), and a sentence in the faith scope
`Sminus (n+1) (n+1)` is never a day-`(n+1)` state atom (`atomDay`), which is what keeps the
`φ`-cells and the state cells from colliding.
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## Decoding the atoms -/

/-- Decode a day-`m` state atom code: `some q` iff the code is `stateAtom m q`'s.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def decodeState (m s : ℕ) : Option ℕ :=
  if s.unpair.1 = stateTag ∧ s.unpair.2.unpair.1 = m then some s.unpair.2.unpair.2 else none

/-- Decode a day-`n` action atom code: `some a` iff the code is `actionAt n a`'s.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def decodeAction (n t : ℕ) : Option ℕ :=
  if t.unpair.1 = actionTag ∧ t.unpair.2.unpair.1 = n then some t.unpair.2.unpair.2 else none

/-- `decodeState` inverts the state code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma decodeState_stateCode (m q : ℕ) :
    decodeState m (freshAtomCode stateFamily (Nat.pair m q)) = some q := by
  simp [decodeState, freshAtomCode, stateTag]

/-- `decodeAction` inverts the action code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma decodeAction_actionCode (n a : ℕ) :
    decodeAction n (freshAtomCode actionFamily (Nat.pair n a)) = some a := by
  simp [decodeAction, freshAtomCode, actionTag]

/-- A successful state decode identifies the code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eq_of_decodeState {m s q : ℕ} (h : decodeState m s = some q) :
    s = freshAtomCode stateFamily (Nat.pair m q) := by
  unfold decodeState at h
  split_ifs at h with hc
  obtain ⟨h1, h2⟩ := hc
  have hq : s.unpair.2.unpair.2 = q := Option.some.inj h
  show s = Nat.pair stateTag (Nat.pair m q)
  rw [← h1, ← h2, ← hq, Nat.pair_unpair, Nat.pair_unpair]

/-- A sentence atom in the faith scope `Sminus m m` is not a day-`m` state atom.
Source: none: infrastructure (`stateAtom_notMem_Sminus` at the code level)
Kind: L
Fidelity: n/a -/
lemma decodeState_eq_none_of_mem_Sminus {m s : ℕ} (h : Formula.atom s ∈ Sminus m m) :
    decodeState m s = none := by
  cases hd : decodeState m s with
  | none => rfl
  | some q =>
      exfalso
      have hs := eq_of_decodeState hd
      have hday := (mem_Sminus.mp h).2 s (by simp)
      rw [hs, atomDay_freshAtomCode] at hday
      exact lt_irrefl _ hday

/-! ## The two-state system and the history -/

/-- The two verdicts: state `1` prices the pushed sentence at `9/10`, state `0` at `1/10`.
Source: `udt-bli-core` `pushPrior` (`Thi`, `Tlo`); mandate T4.3
Kind: D
Fidelity: exact (same numbers) -/
noncomputable def pushVal (q : ℕ) : ℝ := if q = 1 then 9 / 10 else 1 / 10

/-- The cell weights `P(state q ⋏ action a)`: action `1` (push) reaches state `1` with `9/20` and
state `0` with `1/20`; action `0` (honest) the reverse. Each action has mass `1/2`.
Source: `udt-bli-core` `pushPrior` (`μ(T_hi | push) = 9/10`, `μ(T_hi | honest) = 1/10`); mandate T4.3
Kind: D
Fidelity: exact (same numbers) -/
noncomputable def pushW (q a : ℕ) : ℝ :=
  if a = 1 then (if q = 1 then 9 / 20 else 1 / 20) else (if q = 1 then 1 / 20 else 9 / 20)

/-- **The two-state system**: candidates `{0, 1}` every day, verdict `pushVal q` on every sentence,
actual state `0`.
Source: mandate T4.3
Kind: D
Fidelity: exact -/
noncomputable def pushSystem : StateSystem where
  states _ := {0, 1}
  val _ q _ := pushVal q
  actual _ := 0
  actual_mem _ := by simp

/-- **The history**, by the shape of the sentence on day `n`: a state-and-action cell
`⌜𝑸_{n+1} = q⌝ ⋏ A_n = a` is priced `w q a`; its `φ`-refinement `φ ⋏ (⌜𝑸_{n+1} = q⌝ ⋏ A_n = a)` is
priced `val q · w q a`; an action cell `φ ⋏ A_n = a` (with `φ` not a day-`(n+1)` state atom) is priced
`∑_q val q · w q a`; the action atom `A_n = a` is priced `∑_q w q a`; everything else `0`.
Source: mandate T4.3 ("a history `P` on finitely many sentences (exact rationals)")
Kind: D
Fidelity: exact -/
noncomputable def pushHist (w : ℕ → ℕ → ℝ) (val : ℕ → ℝ) (n : ℕ) : Sentence → ℝ
  | .and (.atom s) (.atom t) =>
      match decodeState (n + 1) s, decodeAction n t with
      | some q, some a => w q a
      | none, some a => ∑ q ∈ ({0, 1} : Finset ℕ), val q * w q a
      | _, none => 0
  | .and _ (.and (.atom s) (.atom t)) =>
      match decodeState (n + 1) s, decodeAction n t with
      | some q, some a => val q * w q a
      | _, _ => 0
  | .and _ (.atom t) =>
      match decodeAction n t with
      | some a => ∑ q ∈ ({0, 1} : Finset ℕ), val q * w q a
      | none => 0
  | .atom t =>
      match decodeAction n t with
      | some a => ∑ q ∈ ({0, 1} : Finset ℕ), w q a
      | none => 0
  | _ => 0

/-- The state-and-action cell is priced `w q a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pushHist_cell (w : ℕ → ℕ → ℝ) (val : ℕ → ℝ) (n q a : ℕ) :
    pushHist w val n (stateAtom (n + 1) q ⋏ actionAt n a) = w q a := by
  simp [pushHist, stateAtom, actionAt, freshAtom]

/-- The `φ`-refined cell is priced `val q · w q a`, for every `φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pushHist_refined (w : ℕ → ℕ → ℝ) (val : ℕ → ℝ) (n q a : ℕ) (φ : Sentence) :
    pushHist w val n (φ ⋏ (stateAtom (n + 1) q ⋏ actionAt n a)) = val q * w q a := by
  cases φ <;> simp [pushHist, stateAtom, actionAt, freshAtom]

/-- The action atom is priced `∑_q w q a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pushHist_action (w : ℕ → ℕ → ℝ) (val : ℕ → ℝ) (n a : ℕ) :
    pushHist w val n (actionAt n a) = ∑ q ∈ ({0, 1} : Finset ℕ), w q a := by
  simp [pushHist, actionAt, freshAtom]

/-- An action cell `φ ⋏ A_n = a` with `φ` in the faith scope is priced `∑_q val q · w q a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pushHist_actionCell (w : ℕ → ℕ → ℝ) (val : ℕ → ℝ) (n a : ℕ) (φ : Sentence)
    (hφ : φ ∈ Sminus (n + 1) (n + 1)) :
    pushHist w val n (φ ⋏ actionAt n a) = ∑ q ∈ ({0, 1} : Finset ℕ), val q * w q a := by
  cases φ with
  | atom s =>
      have hs := decodeState_eq_none_of_mem_Sminus hφ
      simp [pushHist, actionAt, freshAtom, hs]
  | _ => simp [pushHist, actionAt, freshAtom]

/-! ## The constraints hold -/

/-- **`pushHist` satisfies action-conditional faith** on `pushSystem`.
Source: mandate T4.3
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem pushHist_e2xAct : E2xAct pushSystem (pushHist pushW pushVal) := by
  intro n q _ a φ _
  rw [pushHist_refined, pushHist_cell]
  rfl

/-- **`pushHist` satisfies the partition** on `pushSystem`.
Source: mandate T4.3
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem pushHist_e5Act : E5Act pushSystem (pushHist pushW pushVal) := by
  intro n a
  refine ⟨?_, fun φ hφ => ?_⟩
  · rw [pushHist_action]
    exact Finset.sum_congr rfl fun q _ => pushHist_cell pushW pushVal n q a
  · rw [pushHist_actionCell pushW pushVal n a φ hφ]
    exact Finset.sum_congr rfl fun q _ => pushHist_refined pushW pushVal n q a φ

/-- **The α-value ranks push above honest**: `41/100 > 9/100` (conditional on the action's mass
`1/2`: `41/50` over `9/50`, `udt-bli-core`'s numbers), on every day and for every scoped sentence —
`S.val` differs across states and the weights differ across actions, so T4.2 is exercised
non-degenerately.
Source: `udt-bli-core` `pushPrior` ("ranks push `41/50` over honest `9/50`"); mandate T4.3, T5.2
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem pushHist_alpha_push_gt_honest (n : ℕ) (φ : Sentence) :
    valueAlpha pushSystem (pushHist pushW pushVal) n 0 φ = 9 / 100 ∧
    valueAlpha pushSystem (pushHist pushW pushVal) n 1 φ = 41 / 100 := by
  unfold valueAlpha
  simp only [pushSystem, pushHist_cell]
  rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  norm_num [pushW, pushVal]

/-- **The β-value is indifferent** between push and honest for a pure-`u` utility (`d = 0`): the
`u`-term is the current belief, the same under both actions. **N+ for the α/β *contrast* only**
(audit r1, N2 adversarial): at `d = 0` β-indifference holds *by definition for every history*
(`valueBeta_d0_action_independent`), so this exercises the `u`-cancellation of
`beta_no_manipulation_incentive` on the same table where α prefers push, and nothing about β's
world term; on this table with `d = 1` and the scoped world sentence `⊥`, β is *not* indifferent
(`pushHist_beta_not_indifferent_d1`), so the T4 table cannot witness (β)'s two-term form, and
`beta_no_voi` (kind S) has no witness.
Source: mandate T5.2 (N+: "α prefers push, β indifferent")
Kind: N+ (for the contrast; definitional in β)
Fidelity: exact
Hyps: (a) -/
theorem pushHist_beta_indifferent (n : ℕ) (c : ℝ) (φu ψ : Sentence) :
    valueBeta (pushHist pushW pushVal) n 1 c φu 0 ψ =
      valueBeta (pushHist pushW pushVal) n 0 c φu 0 ψ := by
  simp [valueBeta]

/-- At `d = 0` the β-value is action-independent for every history, by definition (audit r1, N2).
Source: audit r1 N2 (adversarial)
Kind: L
Fidelity: n/a -/
theorem valueBeta_d0_action_independent (P : History) (n a a' : ℕ) (c : ℝ) (φu ψ : Sentence) :
    valueBeta P n a c φu 0 ψ = valueBeta P n a' c φu 0 ψ := by
  simp [valueBeta]

/-- With `d = 1` and the scoped world sentence `⊥`, the witness table's β-value prefers push
(`41/50 > 9/50`): the T4 table does not witness (β)'s two-term form.
Source: audit r1 N2 (adversarial)
Kind: L
Fidelity: n/a -/
theorem pushHist_beta_not_indifferent_d1 (n : ℕ) (c : ℝ) (φu : Sentence) :
    valueBeta (pushHist pushW pushVal) n 0 c φu 1 ⊥ <
      valueBeta (pushHist pushW pushVal) n 1 c φu 1 ⊥ := by
  unfold valueBeta
  rw [pushHist_actionCell pushW pushVal n 1 ⊥ (scope_nonempty n),
    pushHist_actionCell pushW pushVal n 0 ⊥ (scope_nonempty n),
    pushHist_action, pushHist_action]
  rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1),
    Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  norm_num [pushW, pushVal]

/-- **The witness history is not coherent**: it prices the contradiction `⊥ ⋏ A = push` at `41/100`
(and `⊥ ⋏ (⌜𝑸 = 1⌝ ⋏ A = push)` at `81/200`). Irrelevant to the finite identity, which assumes only
`E2xAct ∧ E5Act`; relevant to how far the N+ reaches: it witnesses the *identity*, not "an inductor
wireheads" — no criterion accepts this history (audit r1, N2/N8).
Source: audit r1 N2 (adversarial), N8 (fidelity)
Kind: L
Fidelity: n/a -/
theorem pushHist_prices_falsum_action (n : ℕ) :
    pushHist pushW pushVal n (⊥ ⋏ actionAt n 1) = 41 / 100 := by
  rw [pushHist_actionCell pushW pushVal n 1 ⊥ (scope_nonempty n),
    Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  norm_num [pushW, pushVal]

/-- The witness is not the N− case: the two actions induce different state distributions.
Source: mandate T4.3 ("N− if the two actions give the same state distribution")
Kind: N+
Fidelity: exact -/
theorem pushHist_actions_differ (n : ℕ) :
    pushHist pushW pushVal n (stateAtom (n + 1) 1 ⋏ actionAt n 1) ≠
      pushHist pushW pushVal n (stateAtom (n + 1) 1 ⋏ actionAt n 0) := by
  rw [pushHist_cell, pushHist_cell]
  norm_num [pushW]

end Cleanroom.Corrigibility.CorrExoTrader
