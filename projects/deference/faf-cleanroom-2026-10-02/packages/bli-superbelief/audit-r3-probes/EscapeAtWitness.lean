import Cleanroom.Bli.BliSuperbelief.Escape
import Cleanroom.Bli.BliSuperbelief.Witnesses

/-!
# Audit r3 (adversarial) probe — the escape stream at the package's own witness

Three checks on `Escape.lean` (repair round 2):

1. the hypothesis package of `tentExpr_escExpand_digitize_length_le` is inhabited at the worked
   witness (`witMesh`, day 0, `Q₁`) with an explicit `K = 4`, and the bound evaluates to `2663`
   digits (`5 · 3 · (88·2 + 1) + 8·1`);
2. the escape expansion is **not** the identity on the witness term's serialization (so
   `unRpn_escExpand_tentExpr` is not `unRpn s = s` in disguise);
3. the raw `pW` leaf `[0, ⌜pW⌝, 0] = [0, 3, 0]` of that term is misparsed by `unRpn` under
   **every** continuation — so the escape is load-bearing at the witness's own leaves, not only
   at the conjunction leaf of the round-2 probe.

Not imported by the library.
-/

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFinite Cleanroom.Bli.BliSuperbelief

namespace AuditR3

lemma card_S0 : (witIndex.S 0).card = 1 := by
  rw [witIndex_S_zero]; exact Finset.card_singleton _

lemma card_S1 : (witIndex.S (0 + 0 + 1)).card = 2 := by
  rw [show (0 + 0 + 1 : ℕ) = 0 + 1 from rfl, witIndex_S_succ]
  exact Finset.card_pair pW_ne_qW

/-- `⌜pW⌝ = 3` (`pW = atom 0`). -/
lemma encode_pW : Encodable.encode pW = 3 := by decide

/-- (1) The escape-stream bound at the witness, `K = 4`: `⌜pW⌝ = 3 < 256`, `0 < 256`,
`(2 · chainDen witMesh 0 0 + 2)² = 8² = 64 < 256`; the bound is `2663` digits. -/
theorem escape_bound_at_witness :
    (digitize (escExpand (tentExpr witMesh 0 0 Q₁).serialize)).length ≤ 2663 := by
  have h := tentExpr_escExpand_digitize_length_le (𝒮 := witIndex) witMesh 0 0 Q₁ 4
    (by
      intro φ hφ
      rw [witIndex_S_zero, Finset.mem_singleton] at hφ
      subst hφ
      rw [encode_pW]; norm_num)
    (by norm_num)
    (by
      rw [chainDen_zero]
      show (2 * (2 + 1) + 2) ^ 2 < 4 ^ 4
      norm_num)
  rw [card_S1, card_S0] at h
  norm_num at h
  exact h

/-- (2) The expansion changes the witness term's stream: it is `8` digits longer. -/
theorem escExpand_ne_at_witness :
    escExpand (tentExpr witMesh 0 0 Q₁).serialize ≠ (tentExpr witMesh 0 0 Q₁).serialize := by
  intro h
  have hlen := escExpand_tentExpr_digitize_length (𝒮 := witIndex) witMesh 0 0 Q₁
  rw [h, card_S0] at hlen
  omega

/-- (3) **The raw `pW` leaf is misparsed under every continuation.** `unRpn` reads the slot token
`3` as the `⋏` tag: a failed parse emits `[0, 0]` and stops; a successful one re-emits the code of
a conjunction, which is not `3 = ⌜atom 0⌝`. -/
theorem unRpn_raw_pW_leaf_ne (rest : List ℕ) :
    unRpn (0 :: 3 :: 0 :: rest) ≠ 0 :: 3 :: 0 :: rest := by
  intro h
  rw [unRpn, List.length_cons, unRpnTokens_cons, if_pos rfl, List.length_cons, List.length_cons,
    parseRpn_cons] at h
  simp only [show ¬ ((3 : ℕ) = 0) by norm_num, show ¬ ((3 : ℕ) = 1) by norm_num,
    show ¬ ((3 : ℕ) = 2) by norm_num, if_false, if_true, parseRpn_cons, Option.bind_some] at h
  rcases hp : parseRpn (rest.length + 1) rest with _ | ⟨q, r⟩
  · rw [hp] at h
    simp at h
  · rw [hp] at h
    rcases r with _ | ⟨d, r2⟩
    · simp at h
    · simp only [Option.bind_some, List.cons.injEq] at h
      have he : Encodable.encode (Formula.and Formula.falsum q : Sentence) =
          Encodable.encode (Formula.atom 0 : Sentence) := by
        rw [h.2.1]; exact (encode_pW).symm
      cases Encodable.encode_injective he

/-- The witness term's serialization starts its first price leaf with exactly `[0, 3, 0]`
(`EF.serialize (price pW 0) = [0, ⌜pW⌝, 0]`), so (3) applies to it. -/
theorem price_pW_serialize : (EF.price pW 0).serialize = [0, 3, 0] := by
  simp [EF.serialize, encode_pW]

end AuditR3
