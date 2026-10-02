import Cleanroom.Deference.DefLatticeArrows.Packages

/-!
# T2 — Tower ⟹ Value, the argmax four-liner, under self-endorsement

Package `def-lattice-arrows`, file 7. v6 §1.1 (root-deference-002) over `def-lattice`'s
objects, with its F1 step "`Γ ⊢ E*(Ŝ_n) = M_n`" replaced by the **self-endorsement
hypothesis** `hSE : E*(S_n) ≈ₙ M_n` in ε-slack form — the H3-laden step: the selection depends
on the expert's own day-`f n` quotes, and whether the expert's estimate of the followed
strategy is its maximal quote is exactly what conditional-stability (H3) buys
(`def-argmax-value`). The **unconditional** arrow (no `hSE`) is refuted on the punishing
menu (lean-deference-003's flag; [[deference-notions]] §Value ⚠ 2026-07-25) and is not stated.

The chain: `E^H_n(O^i_n) ≈ₙ E^H_n(⌜E*(O^i_n)⌝)` (Tower at `O^i`) `≲ₙ E^H_n(⌜E*(S_n)⌝)`
(`⌜E*(S_n)⌝ − ⌜E*(O^i_n)⌝` is valued at `E*(S_n) − E*(O^i_n)`, eventually `≥ −ε` by `hSE` and
`M_n ≥ m^i_n`, F2, `Menu.quote_le_maxQuote`) `≈ₙ E^H_n(S_n)` (Tower at `S`). At the instance
level neither `Follows` nor `Menu.Valued` is consumed: the selection enters only through
`hSE` — which is the point.
-/

namespace Cleanroom.Deference.DefLatticeArrows

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

variable {P : History} {DP : DeductiveProcess}

/-- **Tower ⟹ Value, per menu instance, under self-endorsement (T2).** For a menu `M`, a
followed strategy `S`, quotes `Y_S`, `Y_i` reflecting `E*(S)`, `E*(O^i)`, the two Tower
instances, and `hSE : E*(S_n) ≈ₙ M_n`: `E^H_n(S_n) ≳ₙ E^H_n(O^i_n)`.
Source: v6 §1.1 (root-deference-002), F1 in the asymptotic form; lean-deference-003 (its
flag); [[deference-notions]] §Value
Kind: C
Fidelity: variant: F1 asymptotic (`hSE`) rather than provable; hypothesis-level, not the
refuted unconditional arrow
Hyps: (a) the two Tower instances and the quotes (data); (c) `hSE` — self-endorsement, the
H3-laden step, for every expert (`def-argmax-value` derives it under conditional stability);
`hworld` -/
theorem value_instance_of_tower_of_selfEndorse [IsLogicalInductor P DP] {E : Expert DP}
    {k : ℕ} (M : Menu k) {S YS Yi : ℕ → LUV} (i : Fin (k + 1))
    (hYS : LUV.MachineThresholdCodeSeq YS) (hYi : LUV.MachineThresholdCodeSeq Yi)
    (hRS : Reflects DP E S YS) (hRi : Reflects DP E (M.O i) Yi)
    (hTS : (fun n => (S n).expect P n) ≈ₙ (fun n => (YS n).expect P n))
    (hTi : (fun n => (M.O i n).expect P n) ≈ₙ (fun n => (Yi n).expect P n))
    (hSE : (fun n => E.estimate S n) ≈ₙ (fun n => M.maxQuote E n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n) := by
  have h := expect_listComb_ge_of_eventually (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, YS), (-1, Yi)])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hYS
      · exact hYi)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact fun n v hv => ⟨_, hRS n v hv⟩
      · exact fun n v hv => ⟨_, hRi n v hv⟩))
    (0 : ℝ) (fun ε hε => by
      filter_upwards [asympEq_eventually_abs_le hSE hε] with n hn v hv ν hν
      have hSv := listComb_valuesAt_mem hν (p := (1, YS)) (by simp)
      have hiv := listComb_valuesAt_mem hν (p := (-1, Yi)) (by simp)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hSv.eq (hRS n v hv), hiv.eq (hRi n v hv)]
      have hmax := M.quote_le_maxQuote E i n
      simp only [Menu.quote] at hmax
      rw [abs_le] at hn
      push_cast
      linarith [hn.1]) hworld
  have h0 : (fun n => (Yi n).expect P n) ≲ₙ (fun n => (YS n).expect P n) := by
    intro ε hε
    filter_upwards [h ε hε] with n hn
    simp only [listComb_expect, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hn
    push_cast at hn
    linarith
  exact (hTi.trans_asympLE h0).trans_asympEq hTS.symm

/-- **Self-endorsement** (the H3-laden hypothesis, as a predicate): on every e.d. valued menu
and every e.d. follower of the expert's argmax, the expert's estimate of the follower is
asymptotically its maximal quote — v6's F1 "`Γ ⊢ E*(Ŝ_n) = M_n`" at the asymptotic grade, for
all menus. `(c)` for every expert: false on selection-punishing menus (lean-deference-003's
flag), derivable under conditional stability (`def-argmax-value`).
Source: v6 §1.1 (F1); [[total-trust-implies-value]] §Lemma 2 (self-endorsement)
Kind: D
Fidelity: variant: asymptotic; quantified over all valued menus (the corpus's scoped
predicate restricts the menus) -/
def SelfEndorses (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ (k : ℕ) (M : Menu k), M.Valued DP → ∀ S : ℕ → LUV, LUV.MachineThresholdCodeSeq S →
    Follows DP E M S → (fun n => E.estimate S n) ≈ₙ (fun n => M.maxQuote E n)

/-- **Every e.c. sequence has an e.c. quote** reflecting the expert's estimate — the
existence clause of the corpus's observability ("the ledger prices the whole closure").
`(c)` for a general expert (`li-quote-lane`); for the self-expert FAF's
`Construction/Quotation` supplies it.
Source: [[value-implies-tower]] §What the theorem costs ("Channel")
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def QuotesAvailable (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ X : ℕ → LUV, LUV.MachineThresholdCodeSeq X →
    ∃ Y : ℕ → LUV, LUV.MachineThresholdCodeSeq Y ∧ Reflects DP E X Y

/-- A follower of a valued menu is valued (it takes the selected option's value).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem follows_valued {E : Expert DP} {k : ℕ} {M : Menu k} (hM : M.Valued DP) {S : ℕ → LUV}
    (hF : Follows DP E M S) : Valued DP S := by
  intro n v hv
  obtain ⟨x, hx⟩ := hM (M.argmax E n) n v hv
  exact ⟨x, hF n v hv x hx⟩

/-- **Tower on valued sources ⟹ Value under self-endorsement** (predicate level, T2):
`Value P DP E` from `TowerValued`, the quotes, and `SelfEndorses` (menus and followers are
valued, so `TowerValued` suffices). Not `mart_implies_value`: the arrow without `SelfEndorses`
is refuted (lean-deference-003), and the name says what is proved.
Source: v6 §1.1; root-deference-002 (with its flag: F1 silently assumes exogenous menus)
Kind: L
Fidelity: variant: under the disclosed self-endorsement hypothesis
Hyps: (c) `QuotesAvailable` (existence), `SelfEndorses` (the H3-laden step); `TowerValued` is
the deference hypothesis; `hworld` -/
theorem value_of_towerValued_of_selfEndorse [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TowerValued P DP E) (hq : QuotesAvailable DP E) (hSE : SelfEndorses DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Value P DP E := by
  intro k M hM S hS hF i
  obtain ⟨YS, hYS, hRS⟩ := hq S hS
  obtain ⟨Yi, hYi, hRi⟩ := hq (M.O i) (M.codes i)
  exact value_instance_of_tower_of_selfEndorse M i hYS hYi hRS hRi
    (hT S YS hS hYS (follows_valued hM hF) hRS) (hT (M.O i) Yi (M.codes i) hYi (hM i) hRi)
    (hSE k M hM S hS hF) hworld

/-- **Tower ⟹ Value under self-endorsement** (from def-lattice's `Tower`).
Source: v6 §1.1; root-deference-002
Kind: L
Fidelity: variant: under the disclosed self-endorsement hypothesis
Hyps: as `value_of_towerValued_of_selfEndorse` with `Tower` -/
theorem value_of_tower_of_selfEndorse [IsLogicalInductor P DP] {E : Expert DP}
    (hT : Tower P DP E) (hq : QuotesAvailable DP E) (hSE : SelfEndorses DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Value P DP E :=
  value_of_towerValued_of_selfEndorse (towerValued_of_tower hT) hq hSE hworld

end

end Cleanroom.Deference.DefLatticeArrows
