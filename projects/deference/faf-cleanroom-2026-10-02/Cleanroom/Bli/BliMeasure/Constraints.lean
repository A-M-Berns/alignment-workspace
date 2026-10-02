import Cleanroom.Bli.BliMeasure.Bayes

/-!
# `bli-measure` · Constraints: Eisenstat's constraints over the coherent state system (target 2)

All rows here are **definitional of the construction** (Kind `L`/`C`; mandate §7 item 1 — no `P`
rows), over `S := b3StateSystem`, `P := b3History`, `Q := base.Q`.

**The scope finding (F2 of [[bli-measure-findings]]).** A day-`n` small sentence may mention a
*past* system state atom `⌜𝑸_m = q⌝` (`m < n`: large on day `m`, small later), and `bli-found`'s
scopes `smallSet n` (`E1r`, `E4`) and `Sminus m m` (`E2x`, `E3`) admit such sentences. On those
atoms the B3 world reads the **realized** state while the base's world measure and a
*candidate's* world vector read their own bits. So:

* `E1r`/`E1x`/`E4` hold on the **state-free** part of the scope unconditionally
  (`b3_E1r_stateFree`, `b3_E1x_denom_stateFree`, `b3_E4_stateFree` — the last two with the
  atom bound `B n` in place of smallness, stronger), and on the whole scope under
  `RespectsPast` (the base's rounded measure respects the realized past states;
  `b3_E1r_of_respectsPast`, `b3_E1x_denom_of_respectsPast`). `RespectsPast` is an assumption
  that is **refuted at the instantiation of record** (`Refuted.lean`:
  `paper_respectsPast_refuted` — the base of record is run over `DP`, never hears about realized
  states, and has full support on the stage's consistent worlds), so those two rows are vacuous
  there; a base satisfying it is the fixpoint base over `bliDP` (`bli-assemble`'s
  `Fixpoint.lean`), a different object, not constructed. `bli-found`'s `E1r`, `E1x` (on the
  denominator mesh) and `E4` on their full scopes are **refuted** for B3 of record
  (`paper_E1r_refuted`, `paper_E1x_refuted`, `paper_E4_refuted`).
* `E2x`/`E3` at `Sminus` scope: a Markov superbelief whose candidates have definite opinions
  about past states cannot honor them — **refuted** for B3 of record on a past state atom
  (`paper_E2x_refuted`); the future-atom case (`n < k < m`, a candidate reached from several
  predecessors) is argued in F2, not proved. The honest desideratum is the **state-free**
  scope, which B3 satisfies with the atom bound `B m` (`b3_E2x_stateFree`, `b3_E3_stateFree`,
  from the faith lemma `b3Mass_faith`).
* `E5` holds exactly (`b3_E5`); `FS` is the kernel's support (`b3_FS`).
* `IsBLI_B3` bundles the state-free forms with `E5` (a named `variant` of `bli-found`'s
  `IsBLI_AppB`, which is **refuted** for B3 of record — `paper_isBLI_AppB_refuted`).

"State-free" means `TagFreeSentence stateTag φ`: no state-**tagged** atom, candidate or not
(slightly narrower than "mentioning no system state atom"; `E1r` in fact holds on non-candidate
state-tagged atoms, which read the base world — `sysState`'s disclosed convention).
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

variable {DP : DeductiveProcess} (base : CoherentBase DP) (𝓜 : Mesh)

/-! ## Small sentences and their horizon -/

/-- An atom of a sentence is no larger than the sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tokenSize_atom_le_of_mem {φ : Sentence} {a : ℕ} (ha : a ∈ sentenceAtomCodes φ) :
    tokenSize (Formula.atom a) ≤ tokenSize φ := by
  induction φ using Formula.rec' with
  | hfalsum => simp at ha
  | hatom b => simp at ha; subst ha; exact le_rfl
  | himp φ ψ ihφ ihψ =>
      rw [sentenceAtomCodes_imp, Finset.mem_union] at ha
      rw [tokenSize_imp]
      rcases ha with h | h
      · have := ihφ h; omega
      · have := ihψ h; omega
  | hand φ ψ ihφ ihψ =>
      rw [sentenceAtomCodes_and, Finset.mem_union] at ha
      rw [tokenSize_and]
      rcases ha with h | h
      · have := ihφ h; omega
      · have := ihψ h; omega
  | hor φ ψ ihφ ihψ =>
      rw [sentenceAtomCodes_or, Finset.mem_union] at ha
      rw [tokenSize_or]
      rcases ha with h | h
      · have := ihφ h; omega
      · have := ihψ h; omega

/-- **A system state atom in a day-`n` small sentence is a past atom** (`m < n`): candidate codes
are large on their own day (`stateAtom_large`).
Source: [[bli-program]] §2.3; `bli-found` `stateAtom_large`
Kind: L
Fidelity: exact -/
lemma sysState_day_lt_of_small {n : ℕ} {φ : Sentence} (hφ : φ ∈ smallSet n) {a m q : ℕ}
    (ha : a ∈ sentenceAtomCodes φ) (hs : sysState base 𝓜 a = some (m, q)) : m < n := by
  by_contra hmn
  rw [not_lt] at hmn
  have hq := mem_wstates_of_sysState base 𝓜 hs
  have hlarge := stateAtom_large (large_of_mem_wstates base.𝔅 𝓜 hq) n hmn
  apply hlarge
  rw [mem_smallSet] at hφ
  unfold SmallOn at hφ ⊢
  have h1 := tokenSize_atom_le_of_mem ha
  rw [atom_eq_stateAtom_of_sysState base 𝓜 hs] at h1
  omega

/-- A day-`n` small sentence is covered at horizon `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma covers_zero_of_small {n : ℕ} {φ : Sentence} (hφ : φ ∈ smallSet n) : Covers base 𝓜 n 0 φ := by
  intro a ha
  constructor
  · intro m q hs
    have := sysState_day_lt_of_small base 𝓜 hφ ha hs
    omega
  · intro _
    exact lt_of_lt_of_le (lt_atomBound_of_mem ha) (base.𝔅.B_cover n φ hφ)

/-- A state-tag-free sentence within the day-`n` atom bound is covered at horizon `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma covers_zero_of_tagFree {n : ℕ} {φ : Sentence} (hφ : TagFreeSentence stateTag φ)
    (hB : atomBound φ ≤ base.𝔅.B n) : Covers base 𝓜 n 0 φ := by
  intro a ha
  constructor
  · intro m q hs
    rw [sysState_of_ne_tag base 𝓜 (hφ a ha)] at hs
    cases hs
  · intro _
    exact lt_of_lt_of_le (lt_atomBound_of_mem ha) hB

/-- A state-tag-free sentence within the atom bound of day `n+h` is covered at horizon `h`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma covers_of_tagFree {n h : ℕ} {φ : Sentence} (hφ : TagFreeSentence stateTag φ)
    (hB : atomBound φ ≤ base.𝔅.B (n + h)) : Covers base 𝓜 n h φ := by
  intro a ha
  constructor
  · intro m q hs
    rw [sysState_of_ne_tag base 𝓜 (hφ a ha)] at hs
    cases hs
  · intro _
    exact lt_of_lt_of_le (lt_atomBound_of_mem ha) hB

/-- Covering is closed under conjunction.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma covers_and {n h : ℕ} {φ ψ : Sentence} (h1 : Covers base 𝓜 n h φ) (h2 : Covers base 𝓜 n h ψ) :
    Covers base 𝓜 n h (φ ⋏ ψ) := by
  intro a ha
  rw [sentenceAtomCodes_and, Finset.mem_union] at ha
  rcases ha with ha | ha
  · exact h1 a ha
  · exact h2 a ha

/-- A candidate's state atom of a day within the horizon is covered.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma covers_stateAtom_at (n h : ℕ) {m q : ℕ} (hq : q ∈ wstates base.𝔅 𝓜 m) (hm : m ≤ n + h) :
    Covers base 𝓜 n h (stateAtom m q) := by
  intro a ha
  rw [stateAtom_eq_atom', sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  have hs := sysState_of_mem base 𝓜 hq
  constructor
  · intro m' q' h'
    rw [hs] at h'
    have := Option.some.inj h'
    rw [Prod.mk.injEq] at this
    omega
  · intro h'; rw [hs] at h'; cases h'

/-- **`𝐏_n` of a state-tag-free sentence within the atom bound is the rounded measure's marginal.**
Source: [[bli-measure-mandate]] target 2 (`E1r`, definitional)
Kind: L
Fidelity: exact -/
theorem b3History_of_tagFree {n : ℕ} {φ : Sentence} (hφ : TagFreeSentence stateTag φ)
    (hB : atomBound φ ≤ base.𝔅.B n) :
    b3History base 𝓜 n φ = (wMarginal (measureRound base 𝓜 n) φ : ℝ) := by
  rw [b3History_eq base 𝓜 (covers_zero_of_tagFree base 𝓜 hφ hB), b3Mass_zero]
  congr 1
  unfold wMarginal
  apply Finset.sum_congr rfl
  intro u _
  rw [eval_b3Bits_of_tagFree base 𝓜 _ _ hφ]
  rfl

/-! ## E1r and E1x -/

/-- **E1r on state-free small sentences** (definitional): `𝐏_n φ` is the realized state's value.
Source: [[bli-measure-mandate]] target 2 (`E1r`); bli-paper-034
Kind: L
Fidelity: weaker: scope — the state-free part of `smallSet n`, on which it is the same statement
as `bli-found`'s `E1r` (finding F2; the whole scope under `RespectsPast`, and refuted at the
instantiation of record: `paper_E1r_refuted`) -/
theorem b3_E1r_stateFree : ∀ n, ∀ φ ∈ smallSet n, TagFreeSentence stateTag φ →
    b3History base 𝓜 n φ = (b3StateSystem base 𝓜).val n ((b3StateSystem base 𝓜).actual n) φ := by
  intro n φ hφ hfr
  rw [b3StateSystem_actual, b3StateSystem_val_actual,
    b3History_of_tagFree base 𝓜 hfr (base.𝔅.B_cover n φ hφ)]

/-- **E1r with the rounding error**: on state-free small sentences `|𝐏_n φ − 𝐐_n φ| ≤ 2^(B n)/d n`.
Source: [[bli-measure-mandate]] target 2 (`E1r` with the error)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem b3_E1r_err (n : ℕ) {φ : Sentence} (hφ : φ ∈ smallSet n) (hfr : TagFreeSentence stateTag φ) :
    |b3History base 𝓜 n φ - (base.Q n φ : ℝ)| ≤ (((2 : ℚ) ^ base.𝔅.B n / 𝓜.d n : ℚ) : ℝ) := by
  rw [b3History_of_tagFree base 𝓜 hfr (base.𝔅.B_cover n φ hφ), ← Rat.cast_sub, ← Rat.cast_abs]
  exact_mod_cast roundedTable_err base 𝓜 n hφ

/-- **`RespectsPast`**: every world charged by the day-`n` rounded measure reads every candidate's
state atom of an earlier day `m < n` as the realized state. An assumption, derived nowhere:
**refuted at the instantiation of record** (`paper_respectsPast_refuted` — the base of record is
run over `DP`, not over `bliDP`, and charges a consistent world with a past candidate's atom
flipped); a base satisfying it would be the fixpoint base over `bliDP` (the base run over
`bliDP` of its own realized states — `bli-assemble` `Fixpoint.lean`'s shape), not constructed.
Source: [[bli-measure-findings]] F2; `bli-assemble` `StateLearns`
Kind: D
Fidelity: exact -/
def RespectsPast : Prop :=
  ∀ n (u : FiniteWorld (base.𝔅.B n)), measureRound base 𝓜 n u ≠ 0 →
    ∀ m < n, ∀ q ∈ wstates base.𝔅 𝓜 m,
      u.toBoolPCWorld (freshAtomCode stateFamily (Nat.pair m q)) = decide (q = b3Actual base 𝓜 m)

/-- Under `RespectsPast`, the day-`n` B3 world at horizon `0` agrees with its base world on every
day-`n` small sentence (for charged base worlds).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eval_b3Bits_zero_of_respectsPast (hr : RespectsPast base 𝓜) {n : ℕ}
    {u : FiniteWorld (base.𝔅.B n)} (hu : measureRound base 𝓜 n u ≠ 0) {φ : Sentence}
    (hφ : φ ∈ smallSet n) :
    eval (b3Bits base 𝓜 n 0 PUnit.unit u.toBoolPCWorld) φ = eval u.toBoolPCWorld φ := by
  apply eval_congr_atomCodes
  intro a ha
  cases hs : sysState base 𝓜 a with
  | none => exact b3Bits_of_none base 𝓜 hs
  | some p =>
      obtain ⟨m, q⟩ := p
      have hm := sysState_day_lt_of_small base 𝓜 hφ ha hs
      rw [b3Bits_past base 𝓜 hs hm.le]
      have ha' : a = freshAtomCode stateFamily (Nat.pair m q) :=
        Formula.atom.inj (atom_eq_stateAtom_of_sysState base 𝓜 hs)
      rw [ha', hr n u hu m hm q (mem_wstates_of_sysState base 𝓜 hs)]

/-- **E1r under `RespectsPast`**: `bli-found`'s `E1r` on all of `smallSet n`. Vacuous at the
instantiation of record (`paper_respectsPast_refuted`); the unconditional row is
`b3_E1r_stateFree`.
Source: [[bli-measure-mandate]] target 2 (`E1r`)
Kind: C
Fidelity: exact
Hyps: (c) `hr` (`RespectsPast` — assumed, derived nowhere; refuted at the instantiation of
record; would hold only for the fixpoint base over `bliDP`, not constructed; see F2) -/
theorem b3_E1r_of_respectsPast (hr : RespectsPast base 𝓜) :
    E1r (b3StateSystem base 𝓜) (b3History base 𝓜) := by
  intro n φ hφ
  rw [b3StateSystem_actual, b3StateSystem_val_actual,
    b3History_eq base 𝓜 (covers_zero_of_small base 𝓜 hφ), b3Mass_zero]
  congr 1
  unfold wMarginal
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : measureRound base 𝓜 n u = 0
  · rw [hu, zero_mul, zero_mul]
  · rw [eval_b3Bits_zero_of_respectsPast base 𝓜 hr hu hφ]
    rfl

/-- **E1x on the denominator mesh, state-free part**: on the mesh of the base's denominators the
rounding is the identity, so `𝐏_n φ = 𝐐_n φ` exactly on state-free day-`n` small sentences.
Source: [[bli-measure-mandate]] target 2 (`E1x` on the denominator mesh)
Kind: C
Fidelity: weaker: scope — the state-free part of `smallSet n` (the whole scope under
`RespectsPast`, and refuted at the instantiation of record: `paper_E1x_refuted`)
Hyps: (a) none -/
theorem b3_E1x_denom_stateFree : ∀ n, ∀ φ ∈ smallSet n, TagFreeSentence stateTag φ →
    b3History base (denomMesh base) n φ = ratHistory base.Q n φ := by
  intro n φ hφ hfr
  rw [b3History_of_tagFree base (denomMesh base) hfr (base.𝔅.B_cover n φ hφ),
    measureRound_denomMesh, ← base.Q_eq n φ hφ]
  rfl

/-- **E1x on the denominator mesh under `RespectsPast`**: `bli-found`'s `E1x (ratHistory Q) P`.
Vacuous at the instantiation of record (`paper_respectsPast_refuted` is this theorem's
contrapositive at `paper_E1x_refuted`); the unconditional row is `b3_E1x_denom_stateFree`.
Source: [[bli-measure-mandate]] target 2 (`E1x`)
Kind: C
Fidelity: exact
Hyps: (c) `hr` (`RespectsPast` — assumed; refuted at the instantiation of record; see F2) -/
theorem b3_E1x_denom_of_respectsPast (hr : RespectsPast base (denomMesh base)) :
    E1x (ratHistory base.Q) (b3History base (denomMesh base)) := by
  intro n φ hφ
  have h := b3_E1r_of_respectsPast base (denomMesh base) hr n φ hφ
  rw [b3StateSystem_actual, b3StateSystem_val_actual, measureRound_denomMesh,
    ← base.Q_eq n φ hφ] at h
  exact h

/-! ## The faith lemma -/

/-- The B3 world's bits on a system state atom do not depend on the base world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma b3Bits_sys_indep {n h : ℕ} (τ : Traj (wIndex base.𝔅.B) n h) (v v' : BoolPCWorld) {a : ℕ}
    (hs : sysState base 𝓜 a ≠ none) : b3Bits base 𝓜 n h τ v a = b3Bits base 𝓜 n h τ v' a := by
  cases hs' : sysState base 𝓜 a with
  | none => exact absurd hs' hs
  | some p =>
      obtain ⟨m, q⟩ := p
      by_cases h1 : m ≤ n
      · rw [b3Bits_past base 𝓜 hs' h1, b3Bits_past base 𝓜 hs' h1]
      · by_cases h2 : m ≤ n + h
        · rw [b3Bits_future base 𝓜 hs' (by omega) h2, b3Bits_future base 𝓜 hs' (by omega) h2]
        · rw [b3Bits_beyond base 𝓜 hs' (by omega), b3Bits_beyond base 𝓜 hs' (by omega)]

/-- A sentence over system state atoms only is evaluated independently of the base world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eval_b3Bits_sysOnly {n h : ℕ} (τ : Traj (wIndex base.𝔅.B) n h) (v v' : BoolPCWorld)
    {ξ : Sentence} (hξ : ∀ a ∈ sentenceAtomCodes ξ, sysState base 𝓜 a ≠ none) :
    eval (b3Bits base 𝓜 n h τ v) ξ = eval (b3Bits base 𝓜 n h τ v') ξ :=
  eval_congr_atomCodes ξ fun a ha => b3Bits_sys_indep base 𝓜 τ v v' (hξ a ha)

/-- The B3 world's verdict on a candidate's **last-day** state atom: the trajectory's last table
codes to it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eval_b3Bits_stateAtom_last (n : ℕ) :
    ∀ (h : ℕ) (τ : Traj (wIndex base.𝔅.B) n h) (v : BoolPCWorld) {q : ℕ}
      (hq : q ∈ wstates base.𝔅 𝓜 (n + h)),
      eval (b3Bits base 𝓜 n h τ v) (stateAtom (n + h) q) =
        decide (q = wcode base.𝔅 𝓜 (n + h) (τ.last (roundedTable base 𝓜 n)))
  | 0, _, v, q, hq => by
      rw [eval_b3Bits_stateAtom, b3Bits_past base 𝓜 (sysState_of_mem base 𝓜 hq) (Nat.add_zero n).le]
      rfl
  | h + 1, (τ₀, Q), v, q, hq => by
      rw [eval_b3Bits_stateAtom,
        b3Bits_future base 𝓜 (sysState_of_mem base 𝓜 hq) (by omega) le_rfl]
      show decide (q = wcode base.𝔅 𝓜 (n + (h + 1))
        ((show Traj (wIndex base.𝔅.B) n (h + 1) from (τ₀, Q)).day (n + h + 1) (by omega) (by omega))) = _
      rw [Traj.day_last]
      rfl

/-- The world-weighted payout sum of a trajectory.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_b3Weight_payoutRat {n h : ℕ} {τ : Traj (wIndex base.𝔅.B) n h} (φ : Sentence) :
    ∑ u : FiniteWorld (base.𝔅.B (n + h)), b3Weight base 𝓜 n h τ u * u.payoutRat φ =
      ctrajLaw (faceSkeleton base.𝔅 𝓜) n h (roundedTable base 𝓜 n) τ *
        wMarginal (vecOf (τ.last (roundedTable base 𝓜 n))) φ := by
  unfold b3Weight wMarginal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  show _ = _ * ((τ.last (roundedTable base 𝓜 n)) (wcSelf (n + h) u) * u.payoutRat φ)
  ring

/-- **The faith lemma**: for a state-tag-free `φ` within the atom bound and a sentence `ξ` over
system state atoms that forces the last-day candidate `q`, `𝐏_n(φ ⋏ ξ) = Q̂_q[φ] · 𝐏_n(ξ)` at the
horizon of `q`'s day — the B3 world factors into the trajectory (which decides `ξ`) and the
last table's world vector (which prices `φ`), and `ξ` pins the last table to `decode q`.
Source: [[bli-measure-mandate]] target 2 (`E2x`, `E3`); Appendix B constraints 2–3
Kind: C
Fidelity: exact
Hyps: (a) none beyond the scope (state-free `φ`, `ξ` over system state atoms forcing `q`; no atom
bound is needed for the identity itself — the covering horizon needs it for `b3History_eq`) -/
theorem b3Mass_faith (n h : ℕ) {q : ℕ} (hq : q ∈ wstates base.𝔅 𝓜 (n + h)) {φ : Sentence}
    (hφ : TagFreeSentence stateTag φ) {ξ : Sentence}
    (hξ : ∀ a ∈ sentenceAtomCodes ξ, sysState base 𝓜 a ≠ none)
    (hent : ∀ (τ : Traj (wIndex base.𝔅.B) n h) (v : BoolPCWorld),
      eval (b3Bits base 𝓜 n h τ v) ξ = true → eval (b3Bits base 𝓜 n h τ v) (stateAtom (n + h) q) = true) :
    b3Mass base 𝓜 n h (φ ⋏ ξ) =
      wMarginal (vecOf (wdecode base.𝔅 𝓜 (n + h) q)) φ * b3Mass base 𝓜 n h ξ := by
  unfold b3Mass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  have hlast := Traj.last_mem (roundedTable_mem_cgrid base 𝓜 n) hτ
  set v₀ : BoolPCWorld := fun _ => false
  set c : ℚ := if eval (b3Bits base 𝓜 n h τ v₀) ξ then 1 else 0 with hcdef
  have hc : ∀ v : BoolPCWorld, (if eval (b3Bits base 𝓜 n h τ v) ξ then (1 : ℚ) else 0) = c := by
    intro v
    rw [hcdef, eval_b3Bits_sysOnly base 𝓜 τ v v₀ hξ]
  have hsplit : ∀ u : FiniteWorld (base.𝔅.B (n + h)),
      (if eval (b3Bits base 𝓜 n h τ u.toBoolPCWorld) (φ ⋏ ξ) then (1 : ℚ) else 0) =
        u.payoutRat φ * c := by
    intro u
    show (if (eval _ φ && eval _ ξ) = true then (1 : ℚ) else 0) = _
    rw [eval_b3Bits_of_tagFree base 𝓜 τ _ hφ, ← hc u.toBoolPCWorld]
    unfold FiniteWorld.payoutRat
    cases eval u.toBoolPCWorld φ <;> cases eval (b3Bits base 𝓜 n h τ u.toBoolPCWorld) ξ <;> simp
  simp only [hsplit, hc]
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hc1 : c = 1 := by
      rw [hcdef] at hc0 ⊢
      split_ifs at hc0 ⊢ with h'
      · rfl
      · exact absurd rfl hc0
    have hξt : eval (b3Bits base 𝓜 n h τ v₀) ξ = true := by
      rw [hcdef] at hc0
      by_contra hne
      rw [if_neg hne] at hc0
      exact hc0 rfl
    have hσ := hent τ v₀ hξt
    rw [eval_b3Bits_stateAtom_last base 𝓜 n h τ v₀ hq] at hσ
    have hq' : q = wcode base.𝔅 𝓜 (n + h) (τ.last (roundedTable base 𝓜 n)) := of_decide_eq_true hσ
    have hlasteq : wdecode base.𝔅 𝓜 (n + h) q = τ.last (roundedTable base 𝓜 n) := by
      rw [hq', wdecode_wcode base.𝔅 𝓜 hlast]
    rw [hlasteq, hc1]
    simp only [mul_one]
    calc ∑ u : FiniteWorld (base.𝔅.B (n + h)), b3Weight base 𝓜 n h τ u * u.payoutRat φ
        = ctrajLaw (faceSkeleton base.𝔅 𝓜) n h (roundedTable base 𝓜 n) τ *
            wMarginal (vecOf (τ.last (roundedTable base 𝓜 n))) φ := sum_b3Weight_payoutRat base 𝓜 φ
      _ = wMarginal (vecOf (τ.last (roundedTable base 𝓜 n))) φ *
            ∑ u : FiniteWorld (base.𝔅.B (n + h)), b3Weight base 𝓜 n h τ u := by
          have := sum_b3Weight_payoutRat base 𝓜 (n := n) (h := h) (τ := τ) ⊤
          rw [wMarginal_top, vecOf_sum base.𝔅 𝓜 hlast, mul_one] at this
          have h2 : ∑ u : FiniteWorld (base.𝔅.B (n + h)), b3Weight base 𝓜 n h τ u =
              ∑ u : FiniteWorld (base.𝔅.B (n + h)), b3Weight base 𝓜 n h τ u * u.payoutRat ⊤ := by
            apply Finset.sum_congr rfl; intro u _
            rw [payoutRat_of_holds (PCWorld.holds_top _), mul_one]
          rw [h2, this, mul_comm]

/-! ## E2x, E3 (state-free scope) -/

/-- **E2x on state-free sentences within the atom bound**: for `n < m`, every candidate
`q ∈ states m` and every state-tag-free `φ` with `atomBound φ ≤ B m`,
`𝐏_n(φ ⋏ ⌜𝑸_m = q⌝) = Q̂_q[φ] · 𝐏_n(⌜𝑸_m = q⌝)` — stronger than `bli-found`'s `E2x` in the atom
bound (every base sentence the day-`m` world measure prices, not only small ones), narrower in
excluding state atoms (finding F2).
Source: [[bli-measure-mandate]] target 2 (`E2x` "for every sentence within the atom bound");
bli-paper-035
Kind: C
Fidelity: variant: state-free scope with the atom bound (see F2)
Hyps: (a) none -/
theorem b3_E2x_stateFree : ∀ n m, n < m → ∀ q ∈ (b3StateSystem base 𝓜).states m, ∀ φ,
    TagFreeSentence stateTag φ → atomBound φ ≤ base.𝔅.B m →
      b3History base 𝓜 n (φ ⋏ stateAtom m q) =
        (b3StateSystem base 𝓜).val m q φ * b3History base 𝓜 n (stateAtom m q) := by
  intro n m hnm q hq φ hφ hB
  rw [b3StateSystem_states] at hq
  obtain ⟨h, rfl⟩ : ∃ h, m = n + h := ⟨m - n, by omega⟩
  have hcσ : Covers base 𝓜 n h (stateAtom (n + h) q) := covers_stateAtom_at base 𝓜 n h hq le_rfl
  have hcφ : Covers base 𝓜 n h φ := covers_of_tagFree base 𝓜 hφ hB
  rw [b3History_eq base 𝓜 (covers_and base 𝓜 hcφ hcσ), b3History_eq base 𝓜 hcσ, b3StateSystem_val,
    ← Rat.cast_mul]
  congr 1
  exact b3Mass_faith base 𝓜 n h hq hφ
    (fun a ha => by
      rw [stateAtom_eq_atom', sentenceAtomCodes_atom, Finset.mem_singleton] at ha
      subst ha
      rw [sysState_of_mem base 𝓜 hq]
      exact Option.some_ne_none _)
    (fun _ _ h => h)

/-- **E3 on state-free sentences within the atom bound** (latest state wins): for `n < m < o`,
candidates `q₁ ∈ states m`, `q₂ ∈ states o`, and state-tag-free `φ` with `atomBound φ ≤ B o`,
`𝐏_n(φ ⋏ (σ_m ⋏ σ_o)) = Q̂_{q₂}[φ] · 𝐏_n(σ_m ⋏ σ_o)` — from the Markov structure (the faith lemma),
not by listing.
Source: [[bli-measure-mandate]] target 2 (`E3`); bli-paper-036
Kind: C
Fidelity: variant: state-free scope with the atom bound (see F2)
Hyps: (a) none -/
theorem b3_E3_stateFree : ∀ n m o, n < m → m < o → ∀ q₁ ∈ (b3StateSystem base 𝓜).states m,
    ∀ q₂ ∈ (b3StateSystem base 𝓜).states o, ∀ φ,
      TagFreeSentence stateTag φ → atomBound φ ≤ base.𝔅.B o →
        b3History base 𝓜 n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) =
          (b3StateSystem base 𝓜).val o q₂ φ *
            b3History base 𝓜 n (stateAtom m q₁ ⋏ stateAtom o q₂) := by
  intro n m o hnm hmo q₁ hq₁ q₂ hq₂ φ hφ hB
  rw [b3StateSystem_states] at hq₁ hq₂
  obtain ⟨h, rfl⟩ : ∃ h, o = n + h := ⟨o - n, by omega⟩
  have hc1 : Covers base 𝓜 n h (stateAtom m q₁) := covers_stateAtom_at base 𝓜 n h hq₁ (by omega)
  have hc2 : Covers base 𝓜 n h (stateAtom (n + h) q₂) := covers_stateAtom_at base 𝓜 n h hq₂ le_rfl
  have hcφ : Covers base 𝓜 n h φ := covers_of_tagFree base 𝓜 hφ hB
  rw [b3History_eq base 𝓜 (covers_and base 𝓜 hcφ (covers_and base 𝓜 hc1 hc2)),
    b3History_eq base 𝓜 (covers_and base 𝓜 hc1 hc2), b3StateSystem_val, ← Rat.cast_mul]
  congr 1
  exact b3Mass_faith base 𝓜 n h hq₂ hφ
    (fun a ha => by
      rw [sentenceAtomCodes_and, Finset.mem_union] at ha
      rcases ha with ha | ha
      · rw [stateAtom_eq_atom', sentenceAtomCodes_atom, Finset.mem_singleton] at ha
        subst ha
        rw [sysState_of_mem base 𝓜 hq₁]
        exact Option.some_ne_none _
      · rw [stateAtom_eq_atom', sentenceAtomCodes_atom, Finset.mem_singleton] at ha
        subst ha
        rw [sysState_of_mem base 𝓜 hq₂]
        exact Option.some_ne_none _)
    (fun τ v hτv => by
      change (eval _ (stateAtom m q₁) && eval _ (stateAtom (n + h) q₂)) = true at hτv
      exact (Bool.and_eq_true _ _).mp hτv |>.2)

/-! ## E4, E5, FS -/

/-- **Balance on sentence marginals**: for a grid table `t` and any `φ` within the day-`m` atom
bound, the kernel's mixture of the next tables' marginals of `φ` is `t`'s marginal of `φ`.
Source: [[bli-measure-mandate]] target 2 (`E4` from `faceKernel`'s `balanced`)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem balance_wMarginal {m : ℕ} {t : Table (wIndex base.𝔅.B) m} (ht : t ∈ cgrid base.𝔅 𝓜 m)
    {φ : Sentence} (hB : atomBound φ ≤ base.𝔅.B m) :
    ∑ Q ∈ cgrid base.𝔅 𝓜 (m + 1), ((faceSkeleton base.𝔅 𝓜).κ m).law t Q * wMarginal (vecOf Q) φ =
      wMarginal (vecOf t) φ := by
  have hfib : ∀ Q ∈ cgrid base.𝔅 𝓜 (m + 1), wMarginal (vecOf Q) φ =
      ∑ u : FiniteWorld (base.𝔅.B m), Q (wcAt (Nat.le_succ m) u) * u.payoutRat φ := by
    intro Q hQ
    unfold wMarginal
    rw [← Finset.sum_fiberwise (univ : Finset (FiniteWorld (base.𝔅.B (m + 1))))
      (restrFW (base.𝔅.B_mono m))]
    apply Finset.sum_congr rfl
    intro u _
    rw [cgrid_apply_wcAt base.𝔅 𝓜 hQ (Nat.le_succ m) u, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u' hu'
    rw [Finset.mem_filter] at hu'
    rw [← hu'.2, payoutRat_restrFW (base.𝔅.B_mono m) u' hB]
  calc ∑ Q ∈ cgrid base.𝔅 𝓜 (m + 1), ((faceSkeleton base.𝔅 𝓜).κ m).law t Q * wMarginal (vecOf Q) φ
      = ∑ Q ∈ cgrid base.𝔅 𝓜 (m + 1), ∑ u : FiniteWorld (base.𝔅.B m),
          ((faceSkeleton base.𝔅 𝓜).κ m).law t Q * Q (wcAt (Nat.le_succ m) u) * u.payoutRat φ := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [hfib Q hQ, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        ring
    _ = ∑ u : FiniteWorld (base.𝔅.B m),
          (∑ Q ∈ cgrid base.𝔅 𝓜 (m + 1), ((faceSkeleton base.𝔅 𝓜).κ m).law t Q *
            Q (wcAt (Nat.le_succ m) u)) * u.payoutRat φ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_mul]
    _ = wMarginal (vecOf t) φ := by
        unfold wMarginal
        apply Finset.sum_congr rfl
        intro u _
        show (∑ Q ∈ cgrid base.𝔅 𝓜 (m + 1), ((faceSkeleton base.𝔅 𝓜).κ m).law t Q *
            Q (wcAt (Nat.le_succ m) u)) * u.payoutRat φ = t (wcSelf m u) * u.payoutRat φ
        congr 1
        exact ((faceSkeleton base.𝔅 𝓜).κ m).sum_law_mul ht (wcSelf m u)

/-- **The balance identity on every sentence within the atom bound**: the superbelief-weighted sum
of the candidates' values of `φ` — the right-hand side of `E4` — is the rounded measure's marginal
of `φ`, for *every* `φ` with `atomBound φ ≤ B n` (state atoms included), from the face kernel's
balance on world conjunctions (`balance_wMarginal`). The left-hand side of `E4` equals it when `φ`
is state-tag-free (`b3History_of_tagFree`, so `b3_E4_stateFree`); on a past candidate's state
atom it does not (`paper_E4_refuted`).
Source: [[bli-measure-mandate]] target 2 (`E4`); bli-paper-037
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem sum_superbelief_val_eq (n : ℕ) {φ : Sentence} (hB : atomBound φ ≤ base.𝔅.B n) :
    ∑ q ∈ (b3StateSystem base 𝓜).states (n + 1),
      b3History base 𝓜 n (stateAtom (n + 1) q) * (b3StateSystem base 𝓜).val (n + 1) q φ =
      (wMarginal (measureRound base 𝓜 n) φ : ℝ) := by
  rw [b3StateSystem_states]
  simp only [b3StateSystem_val]
  rw [sum_wstates_real]
  have hterm : ∀ Q ∈ cgrid base.𝔅 𝓜 (n + 1),
      b3History base 𝓜 n (stateAtom (n + 1) (wcode base.𝔅 𝓜 (n + 1) Q)) *
        (wMarginal (vecOf (wdecode base.𝔅 𝓜 (n + 1) (wcode base.𝔅 𝓜 (n + 1) Q))) φ : ℝ) =
      ((((faceSkeleton base.𝔅 𝓜).κ n).law (roundedTable base 𝓜 n) Q * wMarginal (vecOf Q) φ : ℚ) : ℝ) := by
    intro Q hQ
    rw [b3History_stateAtom_succ base 𝓜 n (wcode_mem_wstates base.𝔅 𝓜 hQ), wdecode_wcode base.𝔅 𝓜 hQ]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hterm, ← Rat.cast_sum,
    balance_wMarginal base 𝓜 (roundedTable_mem_cgrid base 𝓜 n) hB, vecOf_roundedTable]

/-- **E4 on state-free sentences within the atom bound** (balance): `𝐏_n φ = ∑_q 𝐏_n(σ_q) · Q̂_q[φ]`
over the day-`(n+1)` candidates, for every state-tag-free `φ` with `atomBound φ ≤ B n` — from
the face kernel's balance on world conjunctions, which needs the extension lemma; stronger than
`bli-found`'s `E4` in the atom bound, narrower in excluding state atoms (F2; the full scope is
refuted at the instantiation of record, `paper_E4_refuted`).
Source: [[bli-measure-mandate]] target 2 (`E4`); bli-paper-037
Kind: C
Fidelity: variant: state-free scope with the atom bound (see F2)
Hyps: (a) none -/
theorem b3_E4_stateFree (n : ℕ) {φ : Sentence} (hφ : TagFreeSentence stateTag φ)
    (hB : atomBound φ ≤ base.𝔅.B n) :
    b3History base 𝓜 n φ = ∑ q ∈ (b3StateSystem base 𝓜).states (n + 1),
      b3History base 𝓜 n (stateAtom (n + 1) q) * (b3StateSystem base 𝓜).val (n + 1) q φ := by
  rw [b3History_of_tagFree base 𝓜 hφ hB, sum_superbelief_val_eq base 𝓜 n hB]

/-- **E5 — partition**: the superbeliefs over the day-`(n+1)` candidates sum to `1`, and distinct
candidates are exclusive. `bli-found`'s `E5`, exactly.
Source: [[bli-measure-mandate]] target 2 (`E5`); bli-slides-017 (5)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem b3_E5 : E5 (b3StateSystem base 𝓜) (b3History base 𝓜) := by
  intro n
  simp only [b3StateSystem_states]
  constructor
  · rw [sum_wstates_real]
    have hterm : ∀ Q ∈ cgrid base.𝔅 𝓜 (n + 1),
        b3History base 𝓜 n (stateAtom (n + 1) (wcode base.𝔅 𝓜 (n + 1) Q)) =
          ((((faceSkeleton base.𝔅 𝓜).κ n).law (roundedTable base 𝓜 n) Q : ℚ) : ℝ) := by
      intro Q hQ
      rw [b3History_stateAtom_succ base 𝓜 n (wcode_mem_wstates base.𝔅 𝓜 hQ), wdecode_wcode base.𝔅 𝓜 hQ]
    rw [Finset.sum_congr rfl hterm, ← Rat.cast_sum,
      ((faceSkeleton base.𝔅 𝓜).κ n).sum_law (roundedTable_mem_cgrid base 𝓜 n), Rat.cast_one]
  · intro q₁ hq₁ q₂ hq₂ hne
    rw [b3History_eq base 𝓜 (covers_and base 𝓜 (covers_stateAtom_succ base 𝓜 n hq₁)
      (covers_stateAtom_succ base 𝓜 n hq₂))]
    have hzero : b3Mass base 𝓜 n 1 (stateAtom (n + 1) q₁ ⋏ stateAtom (n + 1) q₂) = 0 := by
      unfold b3Mass
      rw [sum_ctrajGrid_cons n 0]
      simp only [sum_ctrajGrid_zero]
      apply Finset.sum_eq_zero
      intro Q hQ
      apply Finset.sum_eq_zero
      intro u _
      have hf : eval (b3Bits base 𝓜 n (0 + 1) (Traj.cons Q PUnit.unit) u.toBoolPCWorld)
          (stateAtom (n + 1) q₁ ⋏ stateAtom (n + 1) q₂) = false := by
        show (eval _ _ && eval _ _) = false
        rw [eval_b3Bits_one_stateAtom base 𝓜 n hQ _ hq₁, eval_b3Bits_one_stateAtom base 𝓜 n hQ _ hq₂]
        by_cases h1 : Q = wdecode base.𝔅 𝓜 (n + 1) q₁
        · rw [decide_eq_true h1, decide_eq_false]
          · rfl
          · intro h2
            apply hne
            rw [← wcode_wdecode base.𝔅 𝓜 hq₁, ← wcode_wdecode base.𝔅 𝓜 hq₂, ← h1, ← h2]
        · rw [decide_eq_false h1]; rfl
      rw [hf]
      simp
    rw [hzero, Rat.cast_zero]

/-- **FS — the superbelief's support is the face**: a day-`(n+1)` candidate is charged iff its
decoded table lies in `faceGen (cgrid (n+1)) (roundedTable n)` (by construction of the face
average; the content is target 4).
Source: [[bli-measure-mandate]] target 2 (`FS`)
Kind: L
Fidelity: exact -/
theorem b3_FS (n : ℕ) {q : ℕ} (hq : q ∈ wstates base.𝔅 𝓜 (n + 1)) :
    0 < superbelief (b3History base 𝓜) n q ↔
      wdecode base.𝔅 𝓜 (n + 1) q ∈ faceGen (cgrid base.𝔅 𝓜 (n + 1)) (roundedTable base 𝓜 n) := by
  unfold superbelief
  rw [b3History_stateAtom_succ base 𝓜 n hq, Rat.cast_pos,
    faceKernel_pos_iff base.𝔅 𝓜 (roundedTable_mem_cgrid base 𝓜 n)]

/-! ## The bundle of record -/

/-- `E1r` on the state-free small sentences.
Source: [[bli-measure-findings]] F2
Kind: D
Fidelity: variant: state-free scope -/
def E1rSF (S : StateSystem) (P : History) : Prop :=
  ∀ n, ∀ φ ∈ smallSet n, TagFreeSentence stateTag φ → P n φ = S.val n (S.actual n) φ

/-- `E2x` on state-free sentences within the atom bound `B m`.
Source: [[bli-measure-findings]] F2
Kind: D
Fidelity: variant: state-free scope with the atom bound -/
def E2xSF (B : ℕ → ℕ) (S : StateSystem) (P : History) : Prop :=
  ∀ n m, n < m → ∀ q ∈ S.states m, ∀ φ, TagFreeSentence stateTag φ → atomBound φ ≤ B m →
    P n (φ ⋏ stateAtom m q) = S.val m q φ * P n (stateAtom m q)

/-- `E3` on state-free sentences within the atom bound `B o`.
Source: [[bli-measure-findings]] F2
Kind: D
Fidelity: variant: state-free scope with the atom bound -/
def E3SF (B : ℕ → ℕ) (S : StateSystem) (P : History) : Prop :=
  ∀ n m o, n < m → m < o → ∀ q₁ ∈ S.states m, ∀ q₂ ∈ S.states o, ∀ φ,
    TagFreeSentence stateTag φ → atomBound φ ≤ B o →
      P n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) =
        S.val o q₂ φ * P n (stateAtom m q₁ ⋏ stateAtom o q₂)

/-- `E4` on state-free sentences within the atom bound `B n`.
Source: [[bli-measure-findings]] F2
Kind: D
Fidelity: variant: state-free scope with the atom bound -/
def E4SF (B : ℕ → ℕ) (S : StateSystem) (P : History) : Prop :=
  ∀ n φ, TagFreeSentence stateTag φ → atomBound φ ≤ B n →
    P n φ = ∑ q ∈ S.states (n + 1), P n (stateAtom (n + 1) q) * S.val (n + 1) q φ

/-- **The B3 bundle**: `E1rSF ∧ E2xSF ∧ E3SF ∧ E4SF ∧ E5` — `bli-found`'s `IsBLI_AppB` with the
faith/balance constraints on the state-free scope (no state-tagged atom) with the atom bound
(finding F2: at `bli-found`'s scopes the bundle is **refuted** for B3 of record,
`paper_isBLI_AppB_refuted`).
Source: [[bli-measure-mandate]] target 2 (`IsBLI_AppB` "with the `variant` scope of faith recorded")
Kind: D
Fidelity: variant: scopes as in F2 -/
def IsBLI_B3 (B : ℕ → ℕ) (S : StateSystem) (P : History) : Prop :=
  E1rSF S P ∧ E2xSF B S P ∧ E3SF B S P ∧ E4SF B S P ∧ E5 S P

/-- **B3 satisfies its bundle.**
Source: [[bli-measure-mandate]] target 2 (the conjunction)
Kind: C
Fidelity: variant: as `IsBLI_B3`
Hyps: (a) none -/
theorem b3_isBLI_B3 : IsBLI_B3 base.𝔅.B (b3StateSystem base 𝓜) (b3History base 𝓜) :=
  ⟨b3_E1r_stateFree base 𝓜, b3_E2x_stateFree base 𝓜, b3_E3_stateFree base 𝓜,
    fun n _ hφ hB => b3_E4_stateFree base 𝓜 n hφ hB, b3_E5 base 𝓜⟩

end Cleanroom.Bli.BliMeasure
