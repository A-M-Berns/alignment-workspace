import Cleanroom.Bli.BliTransfer.Clamp

/-!
Audit r1 (fidelity) probe for `bli-transfer`: the source's clamp is stated **on the small
sentences** ([[bli-program]] §3.2(d): "`P_k(φ) := min(max(Q_k(φ), ε_k), 1 − ε_k)` on `S_k`"),
while the definition of record `clamp Q` applies it to every sentence and the refutation
`clamp_not_isLogicalInductor` is stated over that. The gap does not matter: `⊥` is small on every
day (`smallOn_falsum`), so any market satisfying the constraint-1 variant `E1c Q P` floors `⊥` at
`ε_n` and `floor_not_isLogicalInductor` applies verbatim. This is the literal §3.2(d) form
refuted; it should be a row in the package (a one-line corollary). Not imported by the library.
-/

namespace Cleanroom.Bli.BliTransfer.AuditR1

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliTransfer

/-- The program's literal L5 form: a market agreeing with the clamp on the small sentences only
(`E1c`), priced `≥ 0` on `⊥`, is not a logical inductor over any process with consistent worlds. -/
theorem e1c_not_isLogicalInductor (Q P : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hE : E1c Q P) (hP0 : ∀ n, 0 ≤ P n ⊥) :
    ¬ IsLogicalInductor P DP :=
  floor_not_isLogicalInductor P DP hworld hP0 (fun n => by
    rw [hE n ⊥ (mem_smallSet.mpr (smallOn_falsum n))]
    exact (clamp_mem_Icc Q n ⊥).1)

/-- The same without `hP0`: an inductor's own certificate prices in `[0,1]`. -/
theorem e1c_not_isLogicalInductor' (Q P : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (hE : E1c Q P) :
    ¬ IsLogicalInductor P DP :=
  fun h => e1c_not_isLogicalInductor Q P DP hworld hE
    (fun n => (h.marketComputable.1 n ⊥).1) h

end Cleanroom.Bli.BliTransfer.AuditR1
