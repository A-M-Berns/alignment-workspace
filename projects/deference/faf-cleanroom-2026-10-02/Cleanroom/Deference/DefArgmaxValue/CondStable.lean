import Cleanroom.Found.DefLattice.Menu
import Cleanroom.Deference.DefLatticeArrows.Packages

/-!
# `def-argmax-value` · CondStable: conditional-stability of record (target 4)

The scope condition (H3) of [[total-trust-implies-value]] §Hypotheses, in the 2026-07-26
mass-weighted, denominator-free, one-sided form — the PDF's *Regularity* (root-deference-015
slide 10) in the wiki's form:

* `SelectionPackage DP E M I Q` — the **selection-indicator LUVs** `I j n` valued
  `1[sel_n = j]` in every consistent world, and the **product LUVs** `Q j n` valued within a
  vanishing slack at `x_j · 1[sel_n = j]` whenever `O^j_n` is valued `x_j`, where
  `sel_n := M.argmax E n` is `def-lattice`'s least-index argmax. Existence is *not* part of the
  predicate: for the self-expert it is a theorem (`Witness.lean`, `selectionPackage_self`), for
  a distinct expert a disclosed `(c)` clause (`SelectionPackagesAvailable`).
* `CondStableOn M pkg` — the display
  `Σ_j P^A_n(sel=j)[E^A_n(O^j | sel=j) − E^A_n(O^j)] ≳ₙ 0` multiplied through by the mass:
  `Σ_j E*(Q^j_n) ≳ₙ Σ_j E*(I^j_n) · m^j_n`. One-sided; aggregated over `j`; no `ε`-proviso;
  no division anywhere (`Lemmas.lean` 5c is the junk-value lemma); the expert's `E^A_n` is
  `E.estimate`, i.e. `A` at the deferred day `f n` (def-lattice F1).
* `CondStable DP E` — the global form over all valued menus, **defined to be refuted**
  (`LiarProbe.lean`): the scoped theorem (`Theorem.lean`) takes the per-menu form.

The package is a parameter of `CondStableOn`, never an existential inside it (a package with a
junk `Q` would make an existential form vacuous — mandate target 4's trap list).
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows

noncomputable section

variable {DP : DeductiveProcess}

/-- **The selection package** of an expert on a menu: e.c. selection indicators `I j` valued
exactly `1[sel_n = j]` and e.c. products `Q j` valued within `slack n` of `x_j · 1[sel_n = j]`
(the `BlendQuote.reflected` shape; `slack ≡ 0` is allowed). The selection is
`def-lattice`'s `Menu.argmax E` — the expert's *own* argmax at its own day `f n`, never another
expert's or day's (mandate target 4 trap).
Source: [[total-trust-implies-value]] §Hypotheses (H3) ("`𝟙[sel_n = j]`", "`𝟙[sel_n = j]·O^j_n`");
lean-deference-067; mandate target 4a
Kind: D
Fidelity: exact (products within FAF's vanishing slack, as every quote package of the lattice) -/
structure SelectionPackage {k : ℕ} (DP : DeductiveProcess) (E : Expert DP) (M : Menu k)
    (I Q : Fin (k + 1) → ℕ → LUV) where
  /-- every selection indicator is efficiently describable -/
  codes_I : ∀ j, LUV.MachineThresholdCodeSeq (I j)
  /-- every product is efficiently describable -/
  codes_Q : ∀ j, LUV.MachineThresholdCodeSeq (Q j)
  /-- the per-day reflection slack of the products -/
  slack : ℕ → ℝ
  /-- the slack vanishes -/
  slack_tendsto : Tendsto slack atTop (𝓝 0)
  /-- `I j n` is valued `1[M.argmax E n = j]` in every completed-theory world -/
  reflected_I : ∀ j n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (I j n) (if M.argmax E n = j then 1 else 0)
  /-- `Q j n` is valued within `slack n` of `x · 1[M.argmax E n = j]` when `O^j_n` is valued `x` -/
  reflected_Q : ∀ j n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x,
    v.ValuesAt (M.O j n) x →
      ∃ z, v.ValuesAt (Q j n) z ∧ |z - x * (if M.argmax E n = j then 1 else 0)| ≤ slack n

/-- **Conditional-stability on a menu** (H3, the definition of record): *selection is not, on
average, bad news about the option selected* —
`Σ_j E*(Q^j_n) ≳ₙ Σ_j E*(I^j_n) · m^j_n`,
the page's `Σ_j P^A_n(sel=j)[E^A_n(O^j | sel=j) − E^A_n(O^j)] ≳ₙ 0` with each conditional
multiplied through by its own mass. Three load-bearing features: **no `ε`-proviso** (nothing is
divided by, so no mass threshold), **one-sided** (`≳ₙ`: selection as *good* news — the
clairvoyant tie-break — is admitted; a two-sided form would exclude it), **aggregated over `j`**
(per-index gaps may cancel, `Lemmas.lean` 5d). This is the PDF's Regularity (root-deference-015
slide 10; `def-squeeze-diamond`'s planned target 6b, never written) in the wiki's 2026-07-26
denominator-free form. The expert's "`E^A_n`" is `E.estimate`, at day `f n`.
Source: [[total-trust-implies-value]] §Hypotheses (H3), the denominator-free display;
lean-deference-067; vq-wiki-014; 2-022
Kind: D
Fidelity: exact (the denominator-free display; the package as data) -/
def CondStableOn {k : ℕ} {E : Expert DP} (M : Menu k) {I Q : Fin (k + 1) → ℕ → LUV}
    (_pkg : SelectionPackage DP E M I Q) : Prop :=
  (fun n => ∑ j, E.estimate (Q j) n) ≳ₙ (fun n => ∑ j, E.estimate (I j) n * M.quote E j n)

/-- **Global conditional-stability**: `CondStableOn` on every valued menu and every selection
package. **Defined to be refuted** (`LiarProbe.lean` `condStable_refuted`): the global form is
false for inductor-experts — the liar probe violates it by `−s(1−s)` — which is why the scoped
theorem takes the per-menu form and H3 is a condition on the *menu*, not a property of the pair.
Source: [[total-trust-implies-value]] §Necessity; mandate target 4b
Kind: D
Fidelity: exact (the page's "some scope condition is provably necessary") -/
def CondStable (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ (k : ℕ) (M : Menu k), M.Valued DP → ∀ (I Q : Fin (k + 1) → ℕ → LUV)
    (pkg : SelectionPackage DP E M I Q), CondStableOn M pkg

/-- **Selection packages exist for every valued menu** — the disclosed `(c)` existence clause
for a general expert (the analogue of the arrows' `QuotesAvailable`); for the self-expert it is
the theorem `selectionPackage_self` (`Witness.lean`).
Source: mandate target 4a ("for a distinct expert a `(c)` clause, stated and disclosed like
`QuotesAvailable`")
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def SelectionPackagesAvailable (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ (k : ℕ) (M : Menu k), M.Valued DP →
    ∃ I Q : Fin (k + 1) → ℕ → LUV, Nonempty (SelectionPackage DP E M I Q)

/-- The products of a selection package are world-valued on a valued menu.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem SelectionPackage.valued_Q {k : ℕ} {E : Expert DP} {M : Menu k} (hM : M.Valued DP)
    {I Q : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DP E M I Q) (j : Fin (k + 1)) :
    Valued DP (Q j) := by
  intro n v hv
  obtain ⟨x, hx⟩ := hM j n v hv
  obtain ⟨z, hz, -⟩ := pkg.reflected_Q j n v hv x hx
  exact ⟨z, hz⟩

/-- The selection indicators of a selection package are world-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem SelectionPackage.valued_I {k : ℕ} {E : Expert DP} {M : Menu k}
    {I Q : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DP E M I Q) (j : Fin (k + 1)) :
    Valued DP (I j) :=
  fun n v hv => ⟨_, pkg.reflected_I j n v hv⟩

/-- **Exactly one selection indicator is `1`**: the indicators' values sum to `1` in every
completed-theory world (the exclusivity/exhaustivity the mandate's target 6 trap asks to be
discharged rather than assumed — here it is forced by the reflection clause).
Source: mandate target 6 trap list ("`Σ_j E*(I j) = 1` assumed")
Kind: L
Fidelity: n/a -/
theorem SelectionPackage.sum_indicator {k : ℕ} {E : Expert DP} {M : Menu k}
    {I Q : Fin (k + 1) → ℕ → LUV} (_pkg : SelectionPackage DP E M I Q) (n : ℕ) :
    (∑ j, (if M.argmax E n = j then (1 : ℝ) else 0)) = 1 := by
  simp [Finset.sum_ite_eq]

end

end Cleanroom.Deference.DefArgmaxValue
