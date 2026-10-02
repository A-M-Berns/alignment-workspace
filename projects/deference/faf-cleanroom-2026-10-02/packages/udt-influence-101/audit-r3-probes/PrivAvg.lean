import Cleanroom.Udt.UdtInfluence101.Priv

/-!
# Audit r3 (fidelity) probe: `privA` is its own time-`0` average, and the construal question

Not imported by the library. Two claims about the private-signal model of `Priv.lean`.

1. `play_avg_privA`: at every world reaching `hT`, `Ā_{hT,0}` plays exactly what `privA` plays —
   `privA` is constant on each time-`0` atom (`constOnAtom_privA`), so its time-`0` conditional average
   is itself. The docstring of `Priv.theorem1_fails` claims "`privA ≠ Ā_{hT,0}` on the support"; this
   is the opposite. (Consequence: Assumptions 3 and 4 hold for `privA` *trivially*, `𝕀(privA) =
   𝕀(privA)`; the whole load of the counterexample sits on Assumption 5's scope.)

2. `not_A3_abbrev`: Post 8's Assumption 5 passage offers a second construal of the influence of a
   mixed action — "treating `𝕀^ℙ(μ, h, o)` as an abbreviation for `E_{a∼μ}[𝕀^ℙ(a, h, o)]`". Under that
   construal Assumption 5 is definitional, and Post 6's Assumption 3 at `(0, ω₀, o = full)` reads
   `𝕀^ℙ_∅(privA, hT, full) = E_{a∼Ā_{hT,0}(hT,S̄)}[𝕀^ℙ_∅(a, hT, full)]`. It fails: `0 ≠ 1/2`. So the
   same three facts (`IP_privA`, `IP_ofAct_true`, `constOnAtom_privA`) refute Assumption 3 under the
   abbreviation construal and Assumption 5's extension under the algorithm construal; the gap is in
   the sources either way, but *where* it sits is construal-dependent, which F4 and the ledger's
   "refuted (Post 8 Theorem 1 as stated)" do not say.
-/

namespace Cleanroom.Udt.UdtInfluence101.AuditR3

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree
open Cleanroom.Udt.UdtInfluence101.Priv ProfileModel
open Cleanroom.Udt.UdtInfluence101.Home (hT)

noncomputable section

/-- `Ā_{hT,0}` plays what `privA` plays, at every world reaching `hT`. -/
theorem play_avg_privA (ω : PWorld Bool Bool Bool Unit 2) (hr : ω ∈ S.reach hT) :
    S.play (S.avg privA hT 0) hT ω = S.play privA hT ω := by
  apply FinDist.ext
  intro a
  rw [S.play_avg_w privA (Nat.zero_le _) (baseW_pos ω) hr a]
  have hpos : 0 < mass S.ℙ.w (S.atom 0 ω ∩ S.reach hT) := S.mass_atom_inter_pos (baseW_pos ω) hr
  exact condExpJunk_const_on
    (fun ω' hω' => by rw [constOnAtom_privA ω ω' (Finset.mem_inter.1 hω').1]) hpos

/-- Post 6's Assumption 3 (`IP` clause) under Post 8's abbreviation construal of `𝕀(Ā_{h,n}, h, o)`
fails at `(0, ω₀, full)` in the private-signal model: `0 ≠ 1/2`. -/
theorem not_A3_abbrev :
    S.IP 0 privA hT true ω₀ ≠
      ∑ a, (S.play (S.avg privA hT 0) hT ω₀).w a * S.IP 0 (ofAct a) hT true ω₀ := by
  rw [play_avg_privA ω₀ ω₀_reach, play_privA_ω₀, PlaySpace.sum_delta_mul, IP_ofAct_true, IP_privA]
  norm_num

end

end Cleanroom.Udt.UdtInfluence101.AuditR3
