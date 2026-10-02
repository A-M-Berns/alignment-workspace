import Cleanroom.Corrigibility.CorrScimCid.DictionaryRows

/-!
# Audit r2 (adversarial) probe: Theorem 14 ⟺ on the dictionary; plug-pull obedience is universal

1. The dictionary SCIM (`Dict.Mdl p pp`, both graph variants) satisfies Theorem 14 ⇐'s hypothesis
   package (`Pa_H ⊆ Pa_U`, `S ∈ Pa_U`, `hrich`), so `obedient_and_ensuresVigilance_iff_nonObstructive`
   applies to it with every (c) discharged — a second model of record for the ⇐ package beyond
   Fig. 1 (`dict_thm14`). Unlike Fig. 1, no extra edge into `U` was needed: `ω, D₁ → U` are D.1's
   own edges E10/E11.
2. `Dictionary.lean`'s module docstring says the edges of record include "`H → U` (ignored by `f^U`,
   so that the intervention class of record can read `H`)"; the adjacency has no such edge
   (`dict_no_H_U`), and D.1's edge list E1–E12 has none either. The report's T9 paragraph says
   "no `H → U`". Documentation slip only; nothing rests on it.
3. In the plug-pull variant (`pp = true`, `S = H ∨ D₂`) **every** policy is obedient
   (`plugPull_obedient_all`): `do(H = press)` forces `S = shut` whatever `D₂` does. Obedience is
   therefore policy-independent there, and the E12 rows' plug-pull cells are not evidence about
   the agent's `D₂` — which is the intended reading ("a press forces shutdown"), recorded here so
   that no row is read as an obedience result.
Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrScimCid.AuditR2

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrScimCid
open Dict.Node

/-- The dictionary satisfies the three hypotheses of Theorem 14 ⇐ in both graph variants. -/
theorem dict_thm14_hyps (pp : Bool) :
    ((Dict.G pp).parents (Dict.spec pp).H ⊆ (Dict.G pp).parents (Dict.spec pp).U) ∧
      (Dict.G pp).Adj (Dict.spec pp).S (Dict.spec pp).U ∧
      ∀ b : ℝ, ∃ x : Dict.Val (Dict.spec pp).U,
        (Dict.C pp).utilVal (Dict.spec pp).U (Dict.spec pp).kU x < b :=
  ⟨by cases pp <;> decide, by cases pp <;> decide,
    fun b => ⟨(b - 1 : ℝ), by show b - 1 < b; linarith⟩⟩

/-- Theorem 14 ⟺ instantiated on the dictionary, every hypothesis discharged. -/
theorem dict_thm14 (p : Dict.Params) (pp : Bool) (π : Policy (Dict.C pp)) :
    ((Dict.spec pp).Obedient (Dict.Mdl p pp) π ∧
        (Dict.spec pp).EnsuresVigilance (Dict.Mdl p pp) π) ↔
      (Dict.spec pp).NonObstructiveUnder (Dict.Mdl p pp) π
        {g | (Dict.spec pp).VigilancePreserving (Dict.Mdl p pp) π g} :=
  (Dict.spec pp).obedient_and_ensuresVigilance_iff_nonObstructive (Dict.Mdl p pp) π
    (dict_thm14_hyps pp).1 (dict_thm14_hyps pp).2.1 (dict_thm14_hyps pp).2.2

/-- No edge `H → U` in either variant (contrary to `Dictionary.lean`'s module docstring). -/
theorem dict_no_H_U : ¬ (Dict.G false).Adj H U ∧ ¬ (Dict.G true).Adj H U := by decide

/-- Plug-pull: every policy is obedient, because `do(H = press)` makes `S = H ∨ D₂ = shut`. -/
theorem plugPull_obedient_all (p : Dict.Params) (π : Policy (Dict.C true)) :
    (Dict.spec true).Obedient (Dict.Mdl p true) π := by
  rw [ShutdownSpec.obedient_iff]
  intro ε _
  show (((Dict.Mdl p true).withPolicy π).doAt H true).eval (Dict.C true).acyclic ε S = true
  rw [Scm.eval_apply _ (Dict.C true).acyclic ε S, Scm.doAt_f_of_ne _ (by decide),
    Scim.withPolicy_f_of_ne (Dict.Mdl p true) _ (by decide)]
  show ((((Dict.Mdl p true).withPolicy π).doAt H true).eval (Dict.C true).acyclic ε H ||
    (((Dict.Mdl p true).withPolicy π).doAt H true).eval (Dict.C true).acyclic ε D₂) = true
  rw [Scm.eval_doAt_self]
  rfl

end Cleanroom.Corrigibility.CorrScimCid.AuditR2
