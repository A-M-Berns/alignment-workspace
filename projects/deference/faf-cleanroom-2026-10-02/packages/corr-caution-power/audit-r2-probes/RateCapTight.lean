import Cleanroom.Corrigibility.CorrCautionPower.Reversibility

/-!
Audit round 2 (fidelity) probe for `corr-caution-power`, T7 / load-bearing 5.

`AUModel.rate_cap` proves the *upper* bound `AU (s 0) − AU (s T) ≤ lam · T`; the finding it carries
("a rate cap, not a guard", F-13) also needs the bound to be *attainable* — permanent loss can
really accumulate linearly while every action passes D9. The package ships no such witness. This
probe shows one costs six lines: a chain of states along which every action is `lam`-reversible and
attainable value drops by exactly `lam` per step. Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrCautionPower.AuditR2

/-- The chain: states `ℕ`, one action, `AU ω t = −lam · t`. -/
noncomputable def chainModel (lam : ℝ) : AUModel ℕ Unit Unit where
  succ t _ := t + 1
  AU _ t := -lam * t

/-- Every step of the chain is `lam`-reversible (it loses exactly `lam`). -/
theorem chain_reversible (lam : ℝ) (t : ℕ) : (chainModel lam).Reversible lam t () := by
  intro ω
  show -lam * (t : ℝ) - (-lam * ((t + 1 : ℕ) : ℝ)) ≤ lam
  push_cast
  linarith

/-- The trajectory `s t = t` satisfies `rate_cap`'s hypotheses. -/
theorem chain_traj (lam : ℝ) :
    ∀ t, (fun t : ℕ => t) (t + 1) = (chainModel lam).succ ((fun t : ℕ => t) t) () :=
  fun _ => rfl

/-- **`rate_cap` is tight:** along the chain, `AU (s 0) − AU (s T) = lam · T` exactly — so with
`lam > 0` the guard permits unbounded permanent loss, linear in `T`. -/
theorem rate_cap_tight (lam : ℝ) (T : ℕ) :
    (chainModel lam).AU () 0 - (chainModel lam).AU () T = lam * T := by
  show -lam * ((0 : ℕ) : ℝ) - (-lam * (T : ℝ)) = lam * T
  push_cast
  ring

/-- The upper bound from the library and the equality from the probe agree on the chain. -/
theorem rate_cap_attained (lam : ℝ) (T : ℕ) :
    (chainModel lam).AU () 0 - (chainModel lam).AU () T ≤ lam * T ∧
    (chainModel lam).AU () 0 - (chainModel lam).AU () T = lam * T :=
  ⟨(chainModel lam).rate_cap (fun t => t) (fun _ => ()) (chain_traj lam)
      (fun t => chain_reversible lam t) () T,
   rate_cap_tight lam T⟩

end Cleanroom.Corrigibility.CorrCautionPower.AuditR2
