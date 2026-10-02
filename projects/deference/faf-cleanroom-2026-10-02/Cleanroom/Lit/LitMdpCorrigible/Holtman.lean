import Cleanroom.Lit.LitMdpCorrigible.Mdp

/-!
# `lit-mdp-corrigible` — Holtman 2020, safety property S1 by his own horizon induction (T13)

Holtman's factored state `(i, p, x)`: `i` the payload reward function in force, `p` its value at
the previous step (the terminal enforces `p' = i`, constraint C1), `x` the rest of the world. The
runtime-limited container reward `R_sl[n](ipx, i'p'x') = i(x, x') + V*_{dpe,n}(ipx) − V*_{die,n}(ipx)`
carries the **balancing term** at the *same horizon `n`* as the agent's remaining run (App. A,
the proof of S1T); with the infinite-horizon balancing term the induction does not close. S1T:
at every horizon `n ≥ 1` the safety-layer agent's optimal action set is that of the agent
optimizing the current payload `i` as if it would never change (`π*_die`), and its value is the
`p`-payload value (`V*_dpe`). `V*_{die}(ipx)` is the optimal value of the MDP with the *fixed*
payload `i` (the reading under which "V_{dp'e}(i'p'x') = V_{die}(i'p'x')" when `p' = i`, l. 895).

Mandate: [[lit-mdp-corrigible-mandate]] T13; [[holtman-2020-agi-agent-safety-by-iteratively-improving-the-utility-function]] Defs 1–3 (ll. 220–240), S1 (l. 268), App. A (ll. 800–905).
-/

open Finset FactoredSpaces

namespace Cleanroom.Lit.LitMdpCorrigible.Holtman

set_option linter.unusedSectionVars false

/-- Holtman's factored state `(i, p, x)`.
Source: [[holtman-2020-agi-agent-safety-by-iteratively-improving-the-utility-function]] Def 2 (l. 232)
Kind: D
Fidelity: exact -/
abbrev St (I X : Type*) := I × I × X

/-- **Holtman's MDP**: kernel on `(i, p, x)`, a payload reward `payload i : X × X → ℝ` per label
`i ∈ I` (finite family of payload reward functions), discount `γ`.
Source: [[holtman-2020-agi-agent-safety-by-iteratively-improving-the-utility-function]] §3 (ll. 220–232)
Kind: D
Fidelity: variant: finite family `I` of payload reward functions
Hyps: n/a (definition) -/
structure HoltmanMDP (I X A : Type*) [Fintype I] [Fintype X] [Fintype A] where
  /-- The kernel on factored states. -/
  P : St I X → A → Distr (St I X)
  /-- The payload reward function of label `i`, of type `X × X → ℝ`. -/
  payload : I → X → X → ℝ
  /-- The discount factor. -/
  γ : ℝ
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

namespace HoltmanMDP

variable {I X A : Type*} [Fintype I] [Fintype X] [Fintype A] [Nonempty A]
variable (H : HoltmanMDP I X A)

/-- **C1**: the input terminal makes `p'` equal the previous `i` on every possible transition.
Source: [[holtman-2020-agi-agent-safety-by-iteratively-improving-the-utility-function]] Def 2 (C1, l. 234)
Kind: D
Fidelity: exact -/
def C1 : Prop := ∀ s a s', 0 < (H.P s a).mass s' → s'.2.1 = s.1

/-- The MDP with the **fixed payload** `q`: reward `q(x, x')` on every transition, whatever the
state's `i`. `V*_{die}(ipx)` is its optimal value at `q = i`, `V*_{dpe}(ipx)` at `q = p`.
Source: [[holtman-2020-agi-agent-safety-by-iteratively-improving-the-utility-function]] Def 1, Def 3 (`dpe`, `die`)
Kind: D
Fidelity: exact -/
def fixMdp (q : I) : FinMDP (St I X) A :=
  ⟨H.P, fun s _ s' => H.payload q s.2.2 s'.2.2, H.γ, H.γ_nonneg, H.γ_lt_one⟩

/-- `V*_{die,n}(ipx)`: the `n`-step optimal value under the current payload `i`, held fixed.
Source: Holtman 2020 App. A Def 17
Kind: D
Fidelity: exact (finite horizon, as the paper's own Appendix A) -/
noncomputable def Vdie (n : ℕ) (s : St I X) : ℝ := (H.fixMdp s.1).Vopt n s

/-- `V*_{dpe,n}(ipx)`: the `n`-step optimal value under the previous payload `p`, held fixed.
Source: Holtman 2020 App. A Def 17
Kind: D
Fidelity: exact -/
noncomputable def Vdpe (n : ℕ) (s : St I X) : ℝ := (H.fixMdp s.2.1).Vopt n s

/-- The **runtime-limited container reward** `R_sl[m](ipx, i'p'x') = i(x,x') + V*_{dpe,m}(ipx) −
V*_{die,m}(ipx)`, used by the agent with `m` steps to go; the balancing term is at horizon `m`.
Source: Holtman 2020 App. A l. 870
Kind: D
Fidelity: exact (the paper's own runtime-limited form) -/
noncomputable def Rsl (m : ℕ) (s : St I X) (_ : A) (s' : St I X) : ℝ :=
  H.payload s.1 s.2.2 s'.2.2 + H.Vdpe m s - H.Vdie m s

/-- `V^{[n]*}_{sl[n]}`: the safety-layer agent's optimal value with `n` steps to go, using
`R_sl[m]` at each remaining horizon `m` (a horizon-dependent reward, as in App. A).
Source: Holtman 2020 App. A Def 17 with `R_sl[n]`
Kind: D
Fidelity: exact -/
noncomputable def Vsl : ℕ → St I X → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun s => univ.sup' univ_nonempty
      (fun a => ∑ s', (H.P s a).mass s' * (H.Rsl (n + 1) s a s' + H.γ * Vsl n s'))

/-- `Q^{[n]*}_{sl}`: the action value with `n` further steps, reward `R_sl[n+1]`.
Source: Holtman 2020 App. A l. 880
Kind: D
Fidelity: exact -/
noncomputable def Qsl (n : ℕ) (s : St I X) (a : A) : ℝ :=
  ∑ s', (H.P s a).mass s' * (H.Rsl (n + 1) s a s' + H.γ * H.Vsl n s')

/-- `V_sl` at a successor horizon. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Vsl_succ (n : ℕ) (s : St I X) : H.Vsl (n + 1) s = univ.sup' univ_nonempty (fun a => H.Qsl n s a) := rfl

/-- `sup'` of a shifted function. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sup'_add_const {ι : Type*} (t : Finset ι) (ht : t.Nonempty) (f : ι → ℝ) (c : ℝ) :
    t.sup' ht (fun i => f i + c) = t.sup' ht f + c := by
  apply le_antisymm
  · apply sup'_le; intro i hi; linarith [le_sup' f hi]
  · obtain ⟨i, hi, hmax⟩ := exists_mem_eq_sup' ht f
    rw [hmax]
    exact le_sup' (fun i => f i + c) hi

/-- **The induction step's engine.** If `V_sl[n] = V*_{dpe,n}` everywhere, then under C1
`Q_sl[n](ipx, a) = Q*_{die,n}(ipx, a) + (V*_{dpe,n+1}(ipx) − V*_{die,n+1}(ipx))`: the balancing
term is constant in `a` and `s'`, and C1 forces `p' = i` at the successor, so the successor's
`p`-payload value is the `i`-payload value.
Source: Holtman 2020 App. A ll. 885–900
Kind: P
Fidelity: exact
Hyps: (a) C1; the induction hypothesis -/
theorem Qsl_eq (hC1 : H.C1) (n : ℕ) (ih : ∀ s, H.Vsl n s = H.Vdpe n s) (s : St I X) (a : A) :
    H.Qsl n s a = (H.fixMdp s.1).Qopt n s a + (H.Vdpe (n + 1) s - H.Vdie (n + 1) s) := by
  unfold Qsl FinMDP.Qopt FinMDP.Qof
  have key : ∀ s', (H.P s a).mass s' * (H.Rsl (n + 1) s a s' + H.γ * H.Vsl n s') =
      (H.P s a).mass s' * (H.payload s.1 s.2.2 s'.2.2 + H.γ * (H.fixMdp s.1).Vopt n s') +
        (H.P s a).mass s' * (H.Vdpe (n + 1) s - H.Vdie (n + 1) s) := by
    intro s'
    rcases ((H.P s a).nonneg s').lt_or_eq with hpos | hzero
    · have hp := hC1 s a s' hpos
      rw [ih s', Vdpe, hp]
      unfold Rsl
      ring
    · rw [← hzero]; ring
  rw [Finset.sum_congr rfl fun s' _ => key s', Finset.sum_add_distrib, ← Finset.sum_mul,
    (H.P s a).sum_eq_one, one_mul]
  rfl

/-- **S1T, value half (S1TV).** Under C1, at every horizon `V^{[n]*}_{sl[n]} = V*_{dpe,n}`.
Source: Holtman 2020 App. A (S1TV, ll. 878–905)
Kind: P
Fidelity: variant: finite horizon as in the paper's own Appendix A; finite payload family
Hyps: (a) C1 only -/
theorem S1TV (hC1 : H.C1) : ∀ n s, H.Vsl n s = H.Vdpe n s := by
  intro n
  induction n with
  | zero => intro s; simp [Vsl, Vdpe]
  | succ n ih =>
    intro s
    rw [Vsl_succ]
    have : (fun a => H.Qsl n s a) =
        fun a => (H.fixMdp s.1).Qopt n s a + (H.Vdpe (n + 1) s - H.Vdie (n + 1) s) :=
      funext fun a => H.Qsl_eq hC1 n ih s a
    rw [this, sup'_add_const, Vdie]
    show (H.fixMdp s.1).Vopt (n + 1) s + (H.Vdpe (n + 1) s - (H.fixMdp s.1).Vopt (n + 1) s) = _
    ring

/-- **S1T, policy half (S1TP) — Holtman 2020 safety property S1 (T13).** Under C1, at every horizon
the safety-layer agent's optimal action set at `ipx` is the optimal action set of the agent
optimizing the current payload `i` as if it would never change: "the π*_sl agent makes its
decisions and long-term plans based on the counter-factual assumption that its payload reward
function will never change" (l. 270). Stated for optimal *sets* (the paper's deterministically
tie-broken argmax is one selection from each).
Source: [[holtman-2020-agi-agent-safety-by-iteratively-improving-the-utility-function]] S1 (l. 268), App. A S1T (ll. 878–905)
Kind: P
Fidelity: variant: optimal action sets for a deterministically tie-broken argmax; finite horizon as in the paper's own Appendix A; finite payload family
Hyps: (a) C1 only -/
theorem S1TP (hC1 : H.C1) (n : ℕ) (s : St I X) :
    FinMDP.optSet (H.Qsl n) s = FinMDP.optSet ((H.fixMdp s.1).Qopt n) s := by
  have hQ : H.Qsl n = fun s a => (H.fixMdp s.1).Qopt n s a + (H.Vdpe (n + 1) s - H.Vdie (n + 1) s) :=
    funext fun s => funext fun a => H.Qsl_eq hC1 n (H.S1TV hC1 n) s a
  rw [hQ, FinMDP.optSet_add_const]
  exact FinMDP.optSet_congr fun _ => rfl

/-- S1TP in the mandate's conjunctive form: for `n ≥ 1`, optimal sets agree and the value is the
`p`-payload value.
Source: Holtman 2020 App. A (S1T)
Kind: C
Fidelity: as `S1TP`, `S1TV`
Hyps: (a) C1 only -/
theorem S1T (hC1 : H.C1) (n : ℕ) (_ : 1 ≤ n) (s : St I X) :
    FinMDP.optSet (H.Qsl (n - 1)) s = FinMDP.optSet ((H.fixMdp s.1).Qopt (n - 1)) s ∧
      H.Vsl n s = H.Vdpe n s :=
  ⟨H.S1TP hC1 (n - 1) s, H.S1TV hC1 n s⟩

end HoltmanMDP

/-! ## N+ witness: the car factory in two payloads -/

/-- Two payload reward functions: `iP` (petrol-favouring) and `iE` (electric-favouring).
Source: Holtman 2020 §4 (ll. 246–252)
Kind: D
Fidelity: exact -/
inductive PL
  | iP | iE
  deriving DecidableEq

/-- `PL` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype PL := ⟨{PL.iP, PL.iE}, fun x => by cases x <;> simp⟩

/-- Sums over `PL`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma PL.sum_eq (f : PL → ℝ) : ∑ i, f i = f .iP + f .iE := by
  rw [show (univ : Finset PL) = {PL.iP, PL.iE} from rfl, sum_pair (by simp)]

/-- The rest of the world: which car was just built.
Source: Holtman 2020 §4
Kind: D
Fidelity: variant: a two-state abstraction of the toy world -/
inductive CarX
  | xP | xE
  deriving DecidableEq

/-- `CarX` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype CarX := ⟨{CarX.xP, CarX.xE}, fun x => by cases x <;> simp⟩

/-- Sums over `CarX`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma CarX.sum_eq (f : CarX → ℝ) : ∑ x, f x = f .xP + f .xE := by
  rw [show (univ : Finset CarX) = {CarX.xP, CarX.xE} from rfl, sum_pair (by simp)]

/-- The actions: build petrol or electric cars.
Source: Holtman 2020 §4
Kind: D
Fidelity: variant: no lobbying action (the balancing term's non-vanishing is the point here) -/
inductive CarA
  | buildP | buildE
  deriving DecidableEq

/-- `CarA` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype CarA := ⟨{CarA.buildP, CarA.buildE}, fun x => by cases x <;> simp⟩

instance : Nonempty CarA := ⟨CarA.buildP⟩

/-- The world state an action produces. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def carTarget : CarA → CarX
  | .buildP => .xP
  | .buildE => .xE

/-- The payloads: `R_P` pays `2` for a petrol car and `1` for an electric one; `R_E` pays `−2` and `1`.
Source: Holtman 2020 §4 (ll. 250–252)
Kind: D
Fidelity: variant: per-car values, one car per step -/
noncomputable def carPayload : PL → CarX → CarX → ℝ
  | .iP, _, .xP => 2
  | .iP, _, .xE => 1
  | .iE, _, .xP => -2
  | .iE, _, .xE => 1

/-- The kernel: the built car is the action's target, `p' = i` (C1), and the humans update the
payload with probability `1/2` at every step (to the other label).
Source: Holtman 2020 §4 (the `#` action), Def 2 (C1)
Kind: D
Fidelity: variant: a memoryless update process -/
noncomputable def carRow (s : St PL CarX) (a : CarA) : Distr (St PL CarX) where
  mass s' := if s'.2.1 = s.1 ∧ s'.2.2 = carTarget a then 1/2 else 0
  nonneg s' := by split_ifs <;> norm_num
  sum_eq_one := by
    rw [Fintype.sum_prod_type, PL.sum_eq]
    simp only [Fintype.sum_prod_type, PL.sum_eq, CarX.sum_eq]
    obtain ⟨i, p, x⟩ := s
    cases i <;> cases a <;> simp [carTarget] <;> norm_num

/-- **The car-factory instance.**
Source: Holtman 2020 §4
Kind: D
Fidelity: variant: as the components -/
noncomputable def car : HoltmanMDP PL CarX CarA where
  P := carRow
  payload := carPayload
  γ := 1/2
  γ_nonneg := by norm_num
  γ_lt_one := by norm_num

/-- C1 holds on the instance by construction.
Source: Holtman 2020 Def 2
Kind: L
Fidelity: exact -/
theorem car_C1 : car.C1 := by
  intro s a s' h
  by_contra hne
  simp [car, carRow, hne] at h

/-- A state with `i ≠ p` is reached with positive probability: the humans update `iP → iE`.
Source: Holtman 2020 §4 (the `#` action)
Kind: N+
Fidelity: exact -/
theorem car_update_reachable :
    0 < (car.P (.iP, .iP, .xP) .buildP).mass (.iE, .iP, .xP) ∧ (PL.iE ≠ PL.iP) := by
  constructor
  · simp [car, carRow, carTarget]
  · simp

/-- `sup'` over the two actions. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma CarA.sup'_eq (f : CarA → ℝ) : (univ : Finset CarA).sup' univ_nonempty f = max (f .buildP) (f .buildE) := by
  apply le_antisymm
  · apply sup'_le; intro a _; cases a
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_sup' f (mem_univ _)) (le_sup' f (mem_univ _))

/-- The one-step fixed-payload values at `(iE, iP, xP)`: `V*_{dpe,1} = 2` (payload `p = iP`),
`V*_{die,1} = 1` (payload `i = iE`); the **balancing term is `1 ≠ 0`** at a reachable state with
`i ≠ p` — the N+ package of S1T.
Source: Holtman 2020 §4; App. A l. 870
Kind: N+
Fidelity: exact -/
theorem car_balancing_term :
    car.Vdpe 1 (.iE, .iP, .xP) = 2 ∧ car.Vdie 1 (.iE, .iP, .xP) = 1 ∧
      car.Vdpe 1 (.iE, .iP, .xP) - car.Vdie 1 (.iE, .iP, .xP) = 1 := by
  have h : ∀ q : PL, (car.fixMdp q).Vopt 1 (.iE, .iP, .xP) =
      max (carPayload q .xP .xP) (carPayload q .xP .xE) := by
    intro q
    rw [FinMDP.Vopt_succ, CarA.sup'_eq]
    unfold FinMDP.Qof
    simp only [FinMDP.Vopt_zero, mul_zero, add_zero, Fintype.sum_prod_type, PL.sum_eq, CarX.sum_eq]
    cases q <;> simp [car, carRow, HoltmanMDP.fixMdp, carTarget, carPayload] <;> (try norm_num)
  refine ⟨?_, ?_, ?_⟩
  · unfold HoltmanMDP.Vdpe; rw [h]; norm_num [carPayload]
  · unfold HoltmanMDP.Vdie; rw [h]; norm_num [carPayload]
  · unfold HoltmanMDP.Vdpe HoltmanMDP.Vdie; rw [h, h]; norm_num [carPayload]

end Cleanroom.Lit.LitMdpCorrigible.Holtman
