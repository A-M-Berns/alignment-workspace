/-
# Smoke test — the dependency chain

This file exists to certify that the dependency chain compiles, not to do
mathematics. It reaches a real declaration from **Formalized-Agent-Foundations**
(pinned by commit in `lakefile.toml`), a real declaration from **Mathlib**, and —
through the first — the **Foundation** propositional substrate, and proves a
trivial lemma against each.

House discipline (see `CONVENTIONS.md`): every file ends with `#print axioms`
lines, and results must audit to `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import LogicalInduction.Framework.Asymptotics
import LogicalInduction.Framework.Foundations

namespace Workstudio.Smoke

open LogicalInduction

/-- Reaches FAF's asymptotic vocabulary: `AsympEq` and its reflexivity lemma. -/
theorem faf_asympEq_refl (f : ℕ → ℝ) : AsympEq f f :=
  AsympEq.refl f

/-- Reaches FAF's propositional substrate, and through it Foundation: the
sentence type carries the decidable equality and the encoding the downstream
computability development depends on. -/
theorem faf_substrate_is_encodable : Nonempty (Encodable Sentence) :=
  ⟨inferInstance⟩

/-- Reaches Mathlib: a standard limit. -/
theorem mathlib_one_div_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Both reached at once: the Mathlib limit above says exactly that the sequence
converges to zero in FAF's own vocabulary. -/
theorem chain_compiles :
    ConvergesTo (fun n : ℕ => (1 : ℝ) / (n + 1)) 0 :=
  mathlib_one_div_tendsto_zero

#print axioms faf_asympEq_refl
#print axioms faf_substrate_is_encodable
#print axioms mathlib_one_div_tendsto_zero
#print axioms chain_compiles

end Workstudio.Smoke
