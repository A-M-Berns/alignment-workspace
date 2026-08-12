/-
Fast-loading starter for lab Lean files.

Do NOT `import Mathlib` (that loads all ~7900 modules, ~10 min/check). Import only the
specific modules you need. The set below covers finite sums, real exp/log, filters/Tendsto,
and ordered-field algebra — enough for most LI/deference toy lemmas. Trim it further if you
can: fewer imports = faster checks.

Check with:
  bash deference-trust-lab/lean/check.sh \
       deference-trust-lab/lean/Template.lean
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

-- NOTE: Mathlib module paths drift between versions. If an import errors with
-- "object file ... does not exist", the module was renamed. Find the current name with:
--   find lean-deference/.lake/packages/mathlib/.lake/build/lib/lean \
--        -name '*.olean' | sed 's|.*/lib/lean/||; s|/|.|g; s|.olean||' | grep -i <keyword>

open Finset

-- A trivial sanity lemma (replace with your real content):
example (J : Type*) [Fintype J] (a b : J → ℝ) :
    ∑ j, (a j + b j) = (∑ j, a j) + ∑ j, b j := by
  simp [Finset.sum_add_distrib]

#print axioms Finset.sum_add_distrib
