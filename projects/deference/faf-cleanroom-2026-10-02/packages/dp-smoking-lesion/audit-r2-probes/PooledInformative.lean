import Cleanroom.Decision.DpSmokingLesion.Pooled

/-!
# dp-smoking-lesion — audit round 2, fidelity lens: probe `PooledInformative`

Not imported by the library. dp-sl-2-008's sentence is "never 'label known, type inferred'".
The package renders "type inferred" as *certainty* (`pooled_no_label_alone`:
`P_s(type = t) = 1`), and separately shows the mandate's Bayes-posterior reading is satisfiable
when the labels agree (`pooled_bayes_reading_of_eq_labels`). This probe states the reading in
between, which is the natural one and needs no strengthening: at a pooled `⊤` point, a
clause-1 state that is **self-transparent** has a type-posterior given the label that is the
**prior** — the label carries no type information at all. It is one line from the two shipped
lemmas, so the package could state it as the impossibility of record instead of the certainty
form. Nothing in the library is contradicted; this is a recommendation's evidence.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

section pooled

variable (n : ℚ) (n0 : 0 ≤ n) (n1 : n ≤ 1) (U : Bool → Bool → Bool → ℚ) (κ : Bool → ℚ)
  (κ0 : ∀ t, 0 ≤ κ t) (κ1 : ∀ t, κ t ≤ 1)

local notation "TT" => twoType n n0 n1 U κ κ0 κ1

variable (C : Proc Bool (fun _ => Bool) ℚ) (s : Bool → State TickleW ℚ)

/-- **Self-transparency at a pooled point makes the label uninformative about the type**: for
`n ∈ (0,1)`, a clause-1 state at `d` under `C` with `P_s(m = a) = C(d)(a)` for both acts has
`P_s(type = t ∧ m = a) = n_t · P_s(m = a)` for every type and act — the posterior of the type
given the label is the prior. "Label known" forces "nothing inferred". -/
theorem pooled_selfTransparent_imp_type_uninformative (hn0 : 0 < n) (hn1 : n < 1) (d : Bool)
    (h1 : StrictClause1At s slObs C TT d) (hst : ∀ a, (s d).pr (evM a) = (C d).w a) :
    ∀ t a, (s d).pr (typeEv t ∩ evM a) = typeRate n t * (s d).pr (evM a) :=
  (pooled_bayes_reading_of_eq_labels n n0 n1 U κ κ0 κ1 C s hn0 hn1 d h1
    ((pooled_selfTransparent_iff n n0 n1 U κ κ0 κ1 C s hn0 hn1 d h1).mp hst)).2

end pooled

end Cleanroom.Decision.DpSmokingLesion
