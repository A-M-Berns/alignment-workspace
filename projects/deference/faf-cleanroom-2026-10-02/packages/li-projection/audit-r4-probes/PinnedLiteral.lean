import Cleanroom.Li.LiProjection.Church

/-!
# Audit r4 (adversarial) probe: the pinned T6.1 family carries a real literal, not `⊤`.

`paperU1U2_half_sameDay` pins `a ≡ 1/2`, same-day publication; `ledgerSeq_half_sameDay_literal`
says position `⟨ledgerPayload 0 0 ⌜1/2⌝, 0⟩` is `literalOf (ledgerEntry a 0 0 ⌜1/2⌝)`. Since
`1/2 < 1/2` is false, that literal is the *negated* fresh ledger atom — a genuine sentence, not
`⊤` (which `ledgerSeq` returns at every unpublished or ill-coded position). Sorry-free.
-/

open Cleanroom.Li.LiProjection Cleanroom.Found.LiQuoteLane Cleanroom.Bli.BliFound LO.Propositional

theorem pinned_literal_eq :
    ledgerSeq (fun _ _ => (1 / 2 : ℚ)) (fun _ => PublicationSchedule.sameDay)
        (Nat.pair (ledgerPayload 0 0 (Encodable.encode (1 / 2 : ℚ))) 0) =
      ∼freshAtom ledgerFamily (ledgerPayload 0 0 (Encodable.encode (1 / 2 : ℚ))) := by
  rw [ledgerSeq_half_sameDay_literal]
  simp [ledgerEntry]

theorem pinned_literal_ne_top :
    ledgerSeq (fun _ _ => (1 / 2 : ℚ)) (fun _ => PublicationSchedule.sameDay)
        (Nat.pair (ledgerPayload 0 0 (Encodable.encode (1 / 2 : ℚ))) 0) ≠ ⊤ := by
  rw [pinned_literal_eq]
  intro h
  change Formula.imp (freshAtom ledgerFamily _) Formula.falsum =
    Formula.imp Formula.falsum Formula.falsum at h
  exact absurd (Formula.imp.inj h).1 (by simp [freshAtom])

#print axioms pinned_literal_ne_top
