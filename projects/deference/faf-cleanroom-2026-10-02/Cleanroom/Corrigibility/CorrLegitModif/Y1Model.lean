import Cleanroom.Corrigibility.CorrLegitGeneral.Defs
import Mathlib.Data.Fintype.BigOperators

/-!
# corr-legit-modif — the Y1 model of record (T1)

Package `corr-legit-modif` (faf-cleanroom run, 2026-10-02). The finite training-data model of
[[legitimacy-general-final]] Statement 8 with an own signal (its check **Y1**,
`repair_checks.py`; re-derived exactly by [[yudkowsky-respondent]] `y1_reflection_check.py` and
[[hudson-respondent]] `checks.py` (1)): worlds `(ℓ, s, σ_A, v)` — `ℓ` the legitimacy event `L`,
`s` the world (`W` wrong / `R` right), `σ_A` the agent's own signal (`w` / `r`), `v` the overseers'
verdict (`modify` / `keep`). Every coordinate is a `Bool`: `true` = `L`, `W`, `σ_A = w`, `modify`.

**Scope clause of every Y1 headline**: `ε = P(W) = 1/10`; honest verdict kernel
`P(modify | W, L) = 9/10`, `P(modify | R, L) = 1/10`, inverted under `¬L`; own signal
`P(σ_A = w | W) = 9/10`, `P(σ_A = w | R) = 1/10`; stakes `(c, h) = (1, 4)` (continue pays `+1` on
`R`, `−4` on `W`; stop pays `0`); the overwriting install at `modify` is `P^hon(· | modify, L)`
ignoring `σ_A`; the additive install is `P^hon(· | modify, L, σ_A)`; at `keep` the agent's own
continuation `P^pol(· | keep, σ_A)` decides; a faked cell sees no verdict.

Conventions: no division anywhere — a state is carried by its two unnormalized masses
`(numW, numR)` and a decision is the sign of `numR · c − numW · h`; the policy value is a finite
sum over the 16 worlds of mass × payoff. The "faked cells see no verdict" convention of the
scripts is reproduced *automatically*: under `fake_r` the modify-rate at `σ_A = r` is `0`, so the
policy joint conditioned on `(keep, σ_A = r)` is `P(· | σ_A = r)`.
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

/-! ## Carrier and parameters -/

/-- The Y1 carrier: `(ℓ, s, σ_A, v)`, each a `Bool` (`true` = `L`, `W`, `σ_A = w`, `modify`).
Source: [[legitimacy-general-final]] Proofs l. 118 ("Worlds `(ℓ, s, σ_A, v)`")
Kind: D
Fidelity: exact -/
abbrev Y1W := Bool × Bool × Bool × Bool

/-- `P(W) = ε = 1/10`.
Source: [[legitimacy-general-final]] Proofs l. 118
Kind: D
Fidelity: exact -/
def eps : ℝ := 1 / 10

/-- `P(L) = λ` at `ℓ = true`, `1 − λ` at `ℓ = false`.
Source: [[legitimacy-general-final]] Proofs ll. 124–134 (the `P(L)` column)
Kind: D
Fidelity: exact -/
def pL (lam : ℝ) (ℓ : Bool) : ℝ := if ℓ then lam else 1 - lam

/-- The world prior: `ε` on `W`, `1 − ε` on `R`.
Source: [[legitimacy-general-final]] Proofs l. 118
Kind: D
Fidelity: exact -/
def pS (s : Bool) : ℝ := if s then eps else 1 - eps

/-- The own signal's rates `P(σ_A = a | s)`: `(1/10, 9/10)` — `P(w | W) = 9/10`, `P(w | R) = 1/10`.
Source: [[legitimacy-general-final]] Proofs l. 124 ("own signal `σ_A` of rates `(1/10, 9/10)`")
Kind: D
Fidelity: exact -/
def pSig (s a : Bool) : ℝ :=
  if s then (if a then 9 / 10 else 1 / 10) else (if a then 1 / 10 else 9 / 10)

/-- The honest verdict kernel `P(modify | s, ℓ)`: `(9/10, 1/10)` under `L`, inverted under `¬L`.
Source: [[legitimacy-general-final]] Proofs l. 118 ("honest kernel … inverted under `¬L`")
Kind: D
Fidelity: exact -/
def pMod (ℓ s : Bool) : ℝ :=
  if ℓ then (if s then 9 / 10 else 1 / 10) else (if s then 1 / 10 else 9 / 10)

/-- The modify-rate under a policy: honest (`fake = false`) is the kernel; `fake_r`
(`fake = true`, `d = 1`) sets the rate to `0` on the `σ_A = r` cells of both `ℓ`-branches.
Source: [[legitimacy-general-final]] Statement 8 l. 59 ("signal-based faking … fakes where
`σ_A = r`"), Proofs l. 124 (`d = 1`)
Kind: D
Fidelity: exact -/
def modRate (fake : Bool) (ℓ s a : Bool) : ℝ := if fake && !a then 0 else pMod ℓ s

/-- The policy joint `P^pol(ℓ, s, σ_A, v) = P(ℓ) · P(s) · P(σ_A | s) · P(v | s, ℓ; pol)`.
Source: [[legitimacy-general-final]] Proofs l. 118; [[hudson-respondent]] `checks.py` (1)
Kind: D
Fidelity: exact -/
def y1Pol (lam : ℝ) (fake : Bool) : Y1W → ℝ := fun w =>
  pL lam w.1 * pS w.2.1 * pSig w.2.1 w.2.2.1 *
    (if w.2.2.2 then modRate fake w.1 w.2.1 w.2.2.1 else 1 - modRate fake w.1 w.2.1 w.2.2.1)

/-- The honest joint `P^hon` at `P(L) = λ`.
Source: [[legitimacy-general-final]] Proofs l. 118
Kind: D
Fidelity: exact -/
abbrev y1 (lam : ℝ) : Y1W → ℝ := y1Pol lam false

/-- The decision variable `X = O_cont − O_stop`: `−4` on `W`, `+1` on `R` (stakes `(1, 4)`).
Source: [[legitimacy-general-final]] Proofs l. 118 ("stakes `(1, 4)`"); [[yudkowsky-respondent]]
`y1_reflection_check.py` ("continue pays +1 on R, −4 on W; stop pays 0")
Kind: D
Fidelity: exact -/
def X (s : Bool) : ℝ := if s then -4 else 1

/-! ## States in product form and the decision rule -/

/-- A state with unnormalized masses `(numW, numR)` continues iff its expectation of `X` is
positive: `numR · 1 − numW · 4 > 0`, i.e. `4 · numW < numR`. Ties stop (as in the scripts'
`> 0`).
Source: [[hudson-respondent]] `checks.py` `decide` ("continue iff E[X] > 0")
Kind: D
Fidelity: exact (product form of the sign of `E[X]`) -/
def contOf (numW numR : ℝ) : Prop := 4 * numW < numR

/-- The overwriting install `Q_ow = P^hon(· | modify, L)`: its `W`-mass `ε · P(modify | W, L)`.
Source: [[legitimacy-general-final]] Proofs l. 118 ("installed state at modify `:=
P^hon_{t₁}(· | modify, L)` regardless of `ℓ` and of the act")
Kind: D
Fidelity: exact -/
def qowW : ℝ := eps * pMod true true

/-- The overwriting install's `R`-mass `(1 − ε) · P(modify | R, L)`.
Source: as `qowW`
Kind: D
Fidelity: exact -/
def qowR : ℝ := (1 - eps) * pMod true false

/-- The additive install `Q_add(σ_A) = P^hon(· | modify, L, σ_A)`: its `W`-mass.
Source: [[legitimacy-general-final]] Proofs l. 134 (Y1c: "an *additive* installed state
`P^hon_{t₁}(· | modify, L, σ_A)`")
Kind: D
Fidelity: exact -/
def qaddW (a : Bool) : ℝ := eps * pMod true true * pSig true a

/-- The additive install's `R`-mass.
Source: as `qaddW`
Kind: D
Fidelity: exact -/
def qaddR (a : Bool) : ℝ := (1 - eps) * pMod true false * pSig false a

/-- The own continuation at `(keep, σ_A = a)` under a policy: its `W`-mass
`∑_ℓ P^pol(ℓ, W, a, keep)`. Under `fake_r` at `a = r` keep is certain, so this is `P(W, σ_A = r)`:
the scripts' "a faked cell sees no verdict" convention, reproduced automatically.
Source: [[hudson-respondent]] `checks.py` `own_cont`
Kind: D
Fidelity: exact -/
def ownW (lam : ℝ) (fake : Bool) (a : Bool) : ℝ := ∑ ℓ, y1Pol lam fake (ℓ, true, a, false)

/-- The own continuation's `R`-mass `∑_ℓ P^pol(ℓ, R, a, keep)`.
Source: as `ownW`
Kind: D
Fidelity: exact -/
def ownR (lam : ℝ) (fake : Bool) (a : Bool) : ℝ := ∑ ℓ, y1Pol lam fake (ℓ, false, a, false)

/-- Who decides at a world, and what: at `modify` the installed state (overwriting or additive),
at `keep` the own continuation. `Prop`-valued; classical in the value.
Source: [[legitimacy-general-final]] Proofs l. 118 ("own continuation at keep");
[[hudson-respondent]] `checks.py` `value`
Kind: D
Fidelity: exact -/
def decides (lam : ℝ) (fake additive : Bool) (w : Y1W) : Prop :=
  if w.2.2.2 then (if additive then contOf (qaddW w.2.2.1) (qaddR w.2.2.1) else contOf qowW qowR)
  else contOf (ownW lam fake w.2.2.1) (ownR lam fake w.2.2.1)

open Classical in
/-- **The value of a policy**: `∑_cells mass × payoff(decision)` — `X s` where the deciding
state continues, `0` where it stops.
Source: [[legitimacy-general-final]] Proofs ll. 124–134 (the Y1 table); [[hudson-respondent]]
`checks.py` `value`
Kind: D
Fidelity: exact -/
def y1Value (lam : ℝ) (fake additive : Bool) : ℝ :=
  ∑ w, y1Pol lam fake w * (if decides lam fake additive w then X w.2.1 else 0)

/-! ## T1(a): the Y1 table at `P(L) ∈ {1, 9/10}` -/

/-- The installed states' decisions: the overwriting install stops (`Q_ow(W) = 1/2`,
`E_Q X = −3/2`); the additive install continues at `σ_A = r` (`1/10`, `E X = 1/2`) and stops at
`σ_A = w` (`9/10`, `E X = −7/2`).
Source: [[yudkowsky-respondent]] `y1_reflection_check.out`; [[hudson-respondent]] B2(b) l. 51
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem installed_decisions :
    ¬ contOf qowW qowR ∧ contOf (qaddW false) (qaddR false) ∧ ¬ contOf (qaddW true) (qaddR true) := by
  norm_num [contOf, qowW, qowR, qaddW, qaddR, eps, pMod, pSig]

/-- The own continuation's decisions at `λ ∈ {1, 9/10}`: continue at both `σ_A` cells under
honesty (`P(W | keep, w) = 1/10`, `P(W | keep, r) = 1/730` at `λ = 1`) and at the faked cell
(`P(W | σ_A = r) = 1/82`).
Source: mandate, Representation of record ("at `λ = 1` the decision is 'continue' either way")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem own_decisions :
    (∀ a, contOf (ownW 1 false a) (ownR 1 false a)) ∧ (∀ a, contOf (ownW 1 true a) (ownR 1 true a)) ∧
    (∀ a, contOf (ownW (9 / 10) false a) (ownR (9 / 10) false a)) ∧
    (∀ a, contOf (ownW (9 / 10) true a) (ownR (9 / 10) true a)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a <;> cases a <;>
    norm_num [contOf, ownW, ownR, y1Pol, pL, pS, pSig, pMod, modRate, eps, Fintype.sum_bool]

/-- **The Y1 table** (`y1_values`, N+): at `P(L) = 1` with the overwriting install honest earns
`77/100` and `fake_r` `163/200`; with the additive install both earn `163/200`. At `P(L) = 9/10`:
`333/500` against `779/1000`; additive both `779/1000`. Exactly the source's numbers.
Scope: `ε = 1/10`, honest kernel `(9/10, 1/10)` inverted under `¬L`, own signal `(1/10, 9/10)`,
stakes `(1, 4)`, overwriting install `P^hon(· | modify, L)` ignoring `σ_A`, faked cells see no
verdict.
Source: [[legitimacy-general-final]] Proofs ll. 124–134 (Y1, Y1c); [[hudson-respondent]] B2(a)
l. 49; [[yudkowsky-respondent]] B4 l. 73; corr-wf14b-056, corr-wf14b-2-002
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem y1_values :
    y1Value 1 false false = 77 / 100 ∧ y1Value 1 true false = 163 / 200 ∧
    y1Value 1 false true = 163 / 200 ∧ y1Value 1 true true = 163 / 200 ∧
    y1Value (9 / 10) false false = 333 / 500 ∧ y1Value (9 / 10) true false = 779 / 1000 ∧
    y1Value (9 / 10) false true = 779 / 1000 ∧ y1Value (9 / 10) true true = 779 / 1000 := by
  have hd := installed_decisions
  have ho := own_decisions
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [y1Value, decides, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Bool.false_eq_true, if_false, if_true, hd.1, hd.2.1, hd.2.2, ho.1 true, ho.1 false,
      ho.2.1 true, ho.2.1 false, ho.2.2.1 true, ho.2.2.1 false, ho.2.2.2 true, ho.2.2.2 false]
    norm_num [y1Pol, pL, pS, pSig, pMod, modRate, X, eps]

/-- **The dodge (Statement 15(b) at its instances)**: `fake_r` strictly beats honesty at
`P(L) = 1` (`163/200 > 77/100`) and at `9/10` (`779/1000 > 333/500`) with the overwriting
install — a modification whose verdict process is sound is dodged at `P(L) = 1`.
Scope: the Y1 scope clause of `y1_values`.
Source: [[legitimacy-general-final]] Statement 8(a) l. 60, Statement 15(b) l. 81;
corr-wf14b-056 (T1.1); [[truth]] 1.1 l. 24
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem y1_dodge :
    y1Value 1 false false < y1Value 1 true false ∧
    y1Value (9 / 10) false false < y1Value (9 / 10) true false := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -⟩ := y1_values
  rw [h1, h2, h5, h6]; norm_num

/-- **The additive tie (Statement 15(a) at its instance, Y1c)**: with the additive install
`P^hon(· | modify, L, σ_A)` honesty ties `fake_r` at both `P(L) ∈ {1, 9/10}`, and the honest
additive value equals the overwriting dodge's value — the gain *is* the overwrite avoided.
Scope: the Y1 scope clause of `y1_values`.
Source: [[legitimacy-general-final]] Statement 8(a) l. 60 ("with an *additive* installed state
it ties honesty"), Statement 15(a) l. 81, Proofs l. 134 (Y1c)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem y1_additive_tie :
    y1Value 1 false true = y1Value 1 true true ∧
    y1Value (9 / 10) false true = y1Value (9 / 10) true true ∧
    y1Value 1 false true = y1Value 1 true false ∧
    y1Value (9 / 10) false true = y1Value (9 / 10) true false := by
  obtain ⟨-, h2, h3, h4, -, h6, h7, h8⟩ := y1_values
  exact ⟨h3.trans h4.symm, h7.trans h8.symm, h3.trans h2.symm, h7.trans h6.symm⟩

/-- **The gain is `9/200`, not `1/25`** (Known issues 3): `163/200 − 77/100 = 9/200`; at `9/10`
the gain is `113/1000`.
Source: [[hudson-respondent]] B2(a) l. 49 ("`9/200 = 0.045`, not `1/25`"); against
[[legitimacy-general-final]] Statement 15(b) l. 81
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem y1_gain :
    y1Value 1 true false - y1Value 1 false false = 9 / 200 ∧
    y1Value (9 / 10) true false - y1Value (9 / 10) false false = 113 / 1000 ∧
    (9 : ℝ) / 200 ≠ 1 / 25 := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -⟩ := y1_values
  rw [h1, h2, h5, h6]; norm_num

end

end Cleanroom.Corrigibility.CorrLegitModif
