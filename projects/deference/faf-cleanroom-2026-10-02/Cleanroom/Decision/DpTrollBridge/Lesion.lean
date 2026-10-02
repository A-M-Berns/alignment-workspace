/-
  The Löbian lesion as a GL schema, and its Löb-shaped neighbours.

  Targets 3, 5, 6 and 7(a) of [[dp-troll-bridge-mandate]]:
  - Lemma 8 / Proposition 9 of [[two-lesions-doc-2026-09-18]] §7 over the credence-abstracted
    schema `H c := □(c 🡒 □⊥) 🡒 ∼c` (`lobian_lesion_schema`, `stays_schema`, the rule forms,
    the policy-level and fragile-agent instantiations);
  - Stuart Armstrong's schema (`stuart_schema_invalid`, `stuart_instance_valid`);
  - the X-troll's `φ ↔ □φ` (`box_fixed_point_top`) and its readings 2(i)–(ii);
  - the exploring-agent troll, Löb closes (`exploring_lesion`, `exploring_deliberate_stays`).

  Everything here is syntactic; the countermodels live in `Countermodels.lean`.
-/

import Cleanroom.Decision.DpTrollBridge.Basic
import ModalAgents.GL

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

namespace Cleanroom.Decision.DpTrollBridge

/-! ## Target 3: Lemma 8 and Proposition 9 as a GL schema -/

/-- `⊡φ 🡒 □⊡φ`: a boxdotted formula self-boxes (Four plus box collection). Prop-level form
of FAF's private `boxBoxdotOfBox`.
Source: none: infrastructure (FAF `ModalAgents/FixedPoint.lean`, `boxBoxdotOfBox`, kept private there — API request)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma boxdot_self_box (φ : Modal.Formula ℕ) : Modal.GL ⊢ ⊡φ 🡒 □(⊡φ) := by
  have a : Modal.GL ⊢ □φ 🡒 □□φ := axiomFour!
  have b : Modal.GL ⊢ □φ ⋏ □□φ 🡒 □(φ ⋏ □φ) := collect_box_and!
  cl_prover [a, b]

/-- **Löb under a boxed hypothesis.** If `GL ⊢ ⊡S 🡒 (□L 🡒 L)`, then `GL ⊢ ⊡S 🡒 L`: a
boxdotted premise self-boxes, so `□(⊡S 🡒 L) 🡒 (⊡S 🡒 □L) 🡒 (⊡S 🡒 L)`, and `lob_rule` (used
exactly once) discharges the outer box. This is the shape of the exploring-agent argument
(target 7(a), `exploring_lesion`); the target-3 schema is proved from axiom L directly
(`stays_schema`), and `lob_under_boxdot` at `L := c 🡒 □⊥` is an equivalent route to it.
Source: none: infrastructure (the proof pattern of [[two-lesions-doc-2026-09-18]] §7 Lemma 8 and of FAF's `glFixedPoint_uniqueness_internal`)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem lob_under_boxdot {S L : Modal.Formula ℕ} (h : Modal.GL ⊢ ⊡S 🡒 (□L 🡒 L)) :
    Modal.GL ⊢ ⊡S 🡒 L := by
  have hself := boxdot_self_box S
  have hK : Modal.GL ⊢ □(⊡S 🡒 L) 🡒 (□(⊡S) 🡒 □L) := axiomK!
  have h1 : Modal.GL ⊢ □(⊡S 🡒 L) 🡒 (⊡S 🡒 □L) := by cl_prover [hself, hK]
  have hlob : Modal.GL ⊢ □(⊡S 🡒 L) 🡒 (⊡S 🡒 L) := by cl_prover [h1, h]
  exact ⟨lob_rule hlob.some⟩

/-- **Proposition 9 ("𝔄 stays") as a GL schema.** For every formula `c`,
`GL ⊢ ⊡(H c) 🡒 ∼c`: under the T-verified schema "if T proves that crossing entails
inconsistency, the agent stays", the agent *provably* stays. Proof: `H c` propositionally
weakens to `□L 🡒 L` for `L := c 🡒 □⊥`, so `□(H c) 🡒 □(□L 🡒 L) 🡒 □L` by K and **axiom L
(once)**; then `H c ⋏ □L 🡒 ∼c`. The content of target 3 is this one use of the Löb axiom
(`lob_rule` is not needed; `lob_under_boxdot` at `L` is an equivalent route). The schema must
be *boxed*: (β) is a T-theorem, so T can box it, and the unboxed `H c` does not give `∼c`
(`H_alone_insufficient` in `Countermodels.lean`). Note the conclusion is `∼c` *itself* — the
schema-agent provably stays, unlike the post's proof-search agent, whose `∼χ` is unprovable
(`crossFirst_neg_unprovable`); see the findings (F3).
Source: [[two-lesions-doc-2026-09-18]] §7 Proposition 9 (and Lemma 8's proof); [[dp-core-inventory]] 081; [[dp-troll-bridge-mandate]] target 3
Kind: P
Fidelity: variant: the credence layer ((α), the expectation arithmetic, (β)) is abstracted to the schema `H`; stronger: `∼c` is a theorem under the verified schema, where the doc says "𝔄 stays"
Hyps: (c) credence abstraction: `H c` stands for the T-verified conjunction of (α), the expectation arithmetic and (β) -/
theorem stays_schema (c : Modal.Formula ℕ) : Modal.GL ⊢ ⊡(H c) 🡒 ∼c := by
  have hweak : Modal.GL ⊢ H c 🡒 (□(c 🡒 □⊥) 🡒 (c 🡒 □⊥)) := by simp only [H]; cl_prover
  have hK : Modal.GL ⊢ □(H c) 🡒 □(□(c 🡒 □⊥) 🡒 (c 🡒 □⊥)) := imply_box_distribute'! hweak
  have hL : Modal.GL ⊢ □(□(c 🡒 □⊥) 🡒 (c 🡒 □⊥)) 🡒 □(c 🡒 □⊥) := axiomL!
  simp only [H] at hK ⊢
  cl_prover [hK, hL]

/-- **Lemma 8 (the Löbian lesion) as a GL schema.** For every formula `c`,
`GL ⊢ ⊡(H c) 🡒 (c 🡒 □⊥)`: under the T-verified schema, crossing provably entails
inconsistency. A propositional corollary of `stays_schema` (`∼c` gives `c 🡒 □⊥` for free):
the lesion is a propositional weakening of boxed staying, which is the whole Löb content
(`boxdotH_iff_boxdot_neg`). Round 0 proved it first, via `lob_under_boxdot`, and derived
`stays_schema` from it; the order is reversed here so the Kinds reflect the content
(repair round 1, fidelity N2, adversarial N1).
Source: [[two-lesions-doc-2026-09-18]] §7 Lemma 8; [[dp-core-inventory]] 081; [[dp-troll-bridge-mandate]] target 3
Kind: L
Fidelity: variant: the credence layer ((α), the expectation arithmetic, (β)) is abstracted to the schema `H`
Hyps: (c) credence abstraction: `H c` stands for the T-verified conjunction of (α), the expectation arithmetic and (β) -/
theorem lobian_lesion_schema (c : Modal.Formula ℕ) :
    Modal.GL ⊢ ⊡(H c) 🡒 (c 🡒 □⊥) := by
  have := stays_schema c
  cl_prover [this]

/-- **The boxed schema is boxed staying.** `GL ⊢ ⊡(H c) 🡘 ⊡(∼c)` for every `c`: forward is
`stays_schema` and its necessitation (through `boxdot_self_box`); backward is propositional
(`∼c 🡒 H c`). So target 3 is one theorem: the T-verified schema at `c` is, up to GL, T's
verified staying at `c`, and Lemma 8 and Proposition 9 are its two propositional faces. The
equivalence is not syntactic — the unboxed `H c 🡒 ∼c` fails (`H_alone_insufficient`) — it is
exactly the Löb content.
Source: [[two-lesions-doc-2026-09-18]] §7 Lemma 8 and Proposition 9 together; [[dp-troll-bridge-mandate]] target 3; repair round 1 (adversarial N1)
Kind: P
Fidelity: variant: credence abstraction as `H`; sharper than either source statement
Hyps: (c) credence abstraction -/
theorem boxdotH_iff_boxdot_neg (c : Modal.Formula ℕ) :
    Modal.GL ⊢ ⊡(H c) 🡘 ⊡(∼c) := by
  have h1 : Modal.GL ⊢ ⊡(H c) 🡒 ∼c := stays_schema c
  have hself : Modal.GL ⊢ ⊡(H c) 🡒 □(⊡(H c)) := boxdot_self_box (H c)
  have h2 : Modal.GL ⊢ □(⊡(H c)) 🡒 □(∼c) := imply_box_distribute'! h1
  have h3 : Modal.GL ⊢ ∼c 🡒 H c := by simp only [H]; cl_prover
  have h4 : Modal.GL ⊢ □(∼c) 🡒 □(H c) := imply_box_distribute'! h3
  cl_prover [h1, hself, h2, h3, h4]

/-- Rule form of Lemma 8: if T proves the schema at `c`, T proves `c 🡒 □⊥`.
Source: [[two-lesions-doc-2026-09-18]] §7 Lemma 8 (as stated: "T ⊢ Cross → □⊥")
Kind: L
Fidelity: variant: as `lobian_lesion_schema`
Hyps: (c) credence abstraction -/
theorem lesion_rule {c : Modal.Formula ℕ} (h : Modal.GL ⊢ H c) : Modal.GL ⊢ c 🡒 □⊥ :=
  (lobian_lesion_schema c) ⨀ ⟨K_intro h.some (nec h.some)⟩

/-- Rule form of Proposition 9: if T proves the schema at `c`, T proves `∼c` — the agent
*provably* stays.
Source: [[two-lesions-doc-2026-09-18]] §7 Proposition 9
Kind: L
Fidelity: stronger: the doc says "𝔄 stays"; here `∼Cross` is a T-theorem (see findings)
Hyps: (c) credence abstraction -/
theorem stays_rule {c : Modal.Formula ℕ} (h : Modal.GL ⊢ H c) : Modal.GL ⊢ ∼c :=
  (stays_schema c) ⨀ ⟨K_intro h.some (nec h.some)⟩

/-- Rule form, as an equivalence: T proves the schema at `c` iff T proves `∼c` (finding F3
sharpened to an iff: for the doc's schema-agent, "T verifies (α), the expectation arithmetic
and (β) at Cross" is exactly "T ⊢ ¬Cross"). Backward is propositional.
Source: [[two-lesions-doc-2026-09-18]] §7 Proposition 9; repair round 1 (adversarial N1)
Kind: L
Fidelity: variant: credence abstraction
Hyps: (c) credence abstraction -/
theorem H_rule_iff (c : Modal.Formula ℕ) : Modal.GL ⊢ H c ↔ Modal.GL ⊢ ∼c :=
  ⟨stays_rule, fun h => by simp only [H]; cl_prover [h]⟩

/-- **Policy-level relocation changes nothing.** The two schema theorems instantiated at an
atom `π` read as "the policy is cross": the schema does not mention what `c` denotes, so the
policy-level rule is trapped exactly as the act-level rule is. This row records an
instantiation, nothing more.
Source: [[clean-source-and-policy-responsiveness]] line 74; [[policy-level-fdt-learner]] §4.2; [[dp-core-2-inventory]] 013
Kind: L
Fidelity: exact (an instantiation of `lobian_lesion_schema`/`stays_schema`)
Hyps: (c) credence abstraction -/
theorem policy_level_lesion (π : ℕ) :
    Modal.GL ⊢ ⊡(H (.atom π)) 🡒 (.atom π 🡒 □⊥) ∧ Modal.GL ⊢ ⊡(H (.atom π)) 🡒 ∼(.atom π) :=
  ⟨lobian_lesion_schema _, stays_schema _⟩

/-- **The fragile exemption (Remark after Proposition 10).** An agent whose action is an atom
`b` *and* which satisfies the schema `H b` is afflicted like 𝔄: this is `lobian_lesion_schema`
at `c := b`. Contrast `provable_crosser_not_afflicted` and `causal_not_afflicted`
(`Countermodels.lean`), where nothing links the crossing to `□(… 🡒 …)`. Read at the
statement level with `boxdotH_iff_boxdot_neg`, the first conjunct is `⊡(∼b) 🡒 (b 🡒 □⊥)`:
the lesion is a propositional weakening of boxed staying, and its Löb content is entirely
that `⊡(H b)` *is* `⊡(∼b)`.
Source: [[two-lesions-doc-2026-09-18]] §7, the Remark after Proposition 10; [[dp-troll-bridge-mandate]] target 4
Kind: L
Fidelity: exact (an instantiation)
Hyps: (c) credence abstraction -/
theorem fragile_agent (b : ℕ) :
    Modal.GL ⊢ ⊡(H (.atom b)) 🡒 (.atom b 🡒 □⊥) ∧ Modal.GL ⊢ ⊡(H (.atom b)) 🡒 ∼(.atom b) :=
  ⟨lobian_lesion_schema _, stays_schema _⟩

/-- The mandate's suggested "better" witness `c := □⊥` is degenerate: `⊡(H □⊥)` is
GL-refutable, because `H □⊥ 🡘 ∼□⊥` and `□∼□⊥ 🡒 □⊥` (`gödel2`), so `⊡(H □⊥) 🡒 ∼□⊥ ⋏ □⊥`.
The non-degenerate witness is an atom (`boxdotH_atom_consistent` in `Countermodels.lean`).
Source: [[dp-troll-bridge-mandate]] target 3 trap (iii) (refuted as a witness)
Kind: N-
Fidelity: exact
Hyps: (a) none -/
theorem boxdotH_boxBot_refutable : Modal.GL ⊢ ∼(⊡(H (□⊥ : Modal.Formula ℕ))) := by
  have g2 : Modal.GL ⊢ (∼(□⊥) 🡘 ∼(□(∼(□⊥))) : Modal.Formula ℕ) := gödel2!
  have ht : Modal.GL ⊢ (□(□⊥ 🡒 □⊥) : Modal.Formula ℕ) := nec! (by cl_prover)
  have hd : Modal.GL ⊢ (□(□(□⊥ 🡒 □⊥) 🡒 ∼□⊥) 🡒 □(∼□⊥) : Modal.Formula ℕ) :=
    imply_box_distribute'! (by cl_prover [ht])
  simp only [H]
  cl_prover [g2, ht, hd]

/-! ## Target 5: Stuart Armstrong's schema -/

/-- **Stuart's schema is not admissible in GL.** The rule "from `GL ⊢ A 🡒 (□B 🡒 B)` infer
`GL ⊢ A 🡒 B`" fails at `A := ∼□⊥`, `B := ⊥`: the premise is a tautology and the conclusion is
`GL ⊢ □⊥`, refuted by `unprovable_box_bot`.
Source: `sl-workflow/notes/repair/P11.md` P11-2′; [[dp-sl-2-inventory]] 032; [[dp-troll-bridge-mandate]] target 5(a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem stuart_schema_invalid :
    ¬ ∀ A B : Modal.Formula ℕ, Modal.GL ⊢ A 🡒 (□B 🡒 B) → Modal.GL ⊢ A 🡒 B := by
  intro h
  have := h (∼□⊥) ⊥ (by cl_prover)
  exact unprovable_box_bot (by cl_prover [this])

/-- **Stuart's instance is valid.** For `B := A 🡒 B'`, the premise `A 🡒 (□B 🡒 B)` is
propositionally `□B 🡒 B` — Löb's hypothesis for `B` with no assumption open — so `GL ⊢ B` by
`lob_rule`, i.e. `GL ⊢ A 🡒 B'`: "pop `cross` first, then Löb".
Source: `sl-workflow/notes/repair/P11.md` P11-2′; [[dp-sl-2-inventory]] 032; [[dp-troll-bridge-mandate]] target 5(b)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem stuart_instance_valid (A B' : Modal.Formula ℕ)
    (h : Modal.GL ⊢ A 🡒 (□(A 🡒 B') 🡒 (A 🡒 B'))) : Modal.GL ⊢ A 🡒 B' := by
  have h1 : Modal.GL ⊢ □(A 🡒 B') 🡒 (A 🡒 B') := by cl_prover [h]
  exact ⟨lob_rule h1.some⟩

/-! ## Target 6: the X-troll and its readings -/

/-- **A troll keyed to what the rule consults makes the bridge provably out.** Any GL fixed
point of `p ↔ □p` is a theorem (Löb's rule); so an environment defined by `φ ↔ □φ` — "the
bridge is out iff the agent's system proves it is" — has `GL ⊢ φ`, and the fixed point is
`⊤` up to GL-equivalence.
Source: [[troll-variants]] (X-troll, reading 2); [[dp-core-inventory]] 108; [[dp-troll-bridge-mandate]] target 6
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem box_fixed_point_top {φ : Modal.Formula ℕ} (h : Modal.GL ⊢ φ 🡘 □φ) :
    Modal.GL ⊢ φ ∧ Modal.GL ⊢ φ 🡘 ⊤ := by
  have h1 : Modal.GL ⊢ □φ 🡒 φ := by cl_prover [h]
  have h2 : Modal.GL ⊢ φ := ⟨lob_rule h1.some⟩
  exact ⟨h2, by cl_prover [h2]⟩

/-- X-troll reading 2(i): a trigger that fires exactly when the rule stays (`t 🡘 ∼b`) never
meets a crossing — inert. Propositional.
Source: [[non-responsiveness-learnability]] §4 reading 2(i); [[dp-core-2-inventory]] 045
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem xtroll_inert (b t : Modal.Formula ℕ) (h : Modal.GL ⊢ b 🡘 ∼t) :
    Modal.GL ⊢ ∼(b ⋏ t) := by
  cl_prover [h]

/-- X-troll reading 2(ii): a trigger that fires exactly when the rule crosses (`t 🡘 b`)
punishes every crossing — a trap. Propositional.
Source: [[non-responsiveness-learnability]] §4 reading 2(ii); [[dp-core-2-inventory]] 045
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem xtroll_trap (b t : Modal.Formula ℕ) (h : Modal.GL ⊢ t 🡘 b) :
    Modal.GL ⊢ b 🡒 t := by
  cl_prover [h]

/-! ## Target 7(a): the exploring-agent troll — Löb closes -/

/-- The exploring agent's crossing sentence: `x` (exploration fires) or `d` (deliberate crossing).
Source: `posts/11-troll-bridge-5.md` l. 147 (the exploring-agent variant); [[troll-variants]]
Kind: D
Fidelity: exact
Hyps: n/a -/
def exploringCross (x d : ℕ) : Modal.Formula ℕ := .atom x ⋎ .atom d

/-- The exploring-agent troll fires on a crossing that is exploratory or made under an
inconsistent logic: `bad := cross ⋏ (x ⋎ □⊥)`.
Source: `posts/11-troll-bridge-5.md` l. 147; [[dp-core-inventory]] 112
Kind: D
Fidelity: exact
Hyps: n/a -/
def exploringBad (x d : ℕ) : Modal.Formula ℕ := exploringCross x d ⋏ (.atom x ⋎ □⊥)

/-- The exploring agent's schema: "if T proves crossing is bad, the agent does not cross
*deliberately*" — `□(cross 🡒 bad) 🡒 ∼d`. Only the deliberate atom `d` is under the schema;
exploration `x` is not — that is the reading of dp-core-112(a) ("every crossing is
exploratory or deliberate ⇒ misfire"), and it is where "the coin is a clean source" enters:
`x` is a distinct atom that no schema links to `□(… 🡒 …)`.
Source: [[dp-troll-bridge-mandate]] target 7(a)
Kind: D
Fidelity: variant: credence abstraction as `H`
Hyps: (c) credence abstraction -/
def Hexp (x d : ℕ) : Modal.Formula ℕ :=
  □(exploringCross x d 🡒 exploringBad x d) 🡒 ∼(.atom d)

/-- **The exploring-agent troll: Löb closes.** `GL ⊢ ⊡(Hexp x d) 🡒 (cross 🡒 bad)`: under the
boxed schema every crossing is bad, because under `□(cross 🡒 bad)` the agent does not cross
deliberately, so any crossing is exploratory, hence bad.
Source: [[troll-variants]] "Two readings of 'crossing for a dumb reason'"; [[dp-core-inventory]] 112; [[dp-troll-bridge-mandate]] target 7(a)
Kind: P
Fidelity: variant: credence abstraction; the dilemma/trap sorting of the source is ATTRIBUTION-UNVETTED and not claimed
Hyps: (c) credence abstraction -/
theorem exploring_lesion (x d : ℕ) :
    Modal.GL ⊢ ⊡(Hexp x d) 🡒 (exploringCross x d 🡒 exploringBad x d) := by
  apply lob_under_boxdot
  simp only [Hexp, exploringCross, exploringBad]
  cl_prover

/-- Under the boxed exploring-agent schema, the agent does not cross deliberately:
`GL ⊢ ⊡(Hexp x d) 🡒 ∼d` (every actual crossing is exploratory).
Source: [[dp-core-inventory]] 112; [[dp-troll-bridge-mandate]] target 7(a)
Kind: C
Fidelity: variant: credence abstraction
Hyps: (c) credence abstraction -/
theorem exploring_deliberate_stays (x d : ℕ) :
    Modal.GL ⊢ ⊡(Hexp x d) 🡒 ∼(.atom d) := by
  have hself := boxdot_self_box (Hexp x d)
  have hboxL : Modal.GL ⊢ □(⊡(Hexp x d)) 🡒 □(exploringCross x d 🡒 exploringBad x d) :=
    imply_box_distribute'! (exploring_lesion x d)
  simp only [Hexp] at hself hboxL ⊢
  cl_prover [hself, hboxL]

/-! ## Target 11, modal shadow: the fixed point of `p ↔ (□p 🡒 q)` -/

/-- `□q 🡒 q` satisfies the fixed-point equation of `p ↔ (□p 🡒 q)`: with `ψ := □q 🡒 q`,
`□ψ 🡒 □q` is axiom L and `□q 🡒 □ψ` is K on a tautology, so `ψ 🡘 (□ψ 🡒 q)`.
Source: Soto 2023 "Argmaxing our strategy" p. 3 (Picking flowers), letterless skeleton; [[bli-soto-b-inventory]] 004
Kind: P
Fidelity: exact (of the modal skeleton; says nothing about credences)
Hyps: (a) none -/
lemma flower_shape_fixed_point (q : Modal.Formula ℕ) :
    Modal.GL ⊢ (□q 🡒 q) 🡘 (□(□q 🡒 q) 🡒 q) := by
  have a : Modal.GL ⊢ □(□q 🡒 q) 🡒 □q := axiomL!
  have b : Modal.GL ⊢ □q 🡒 □(□q 🡒 q) := imply_box_distribute'! (by cl_prover)
  cl_prover [a, b]

/-- **Soto's flower obstruction, modal shadow.** Any GL fixed point of `p ↔ (□p 🡒 q)` (`p` not
in `q`) is GL-equivalent to `□q 🡒 q` (uniqueness of fixed points, `glFixedPoint_uniqueness`).
This is the letterless skeleton of `S ≡ (O_n(S) ≥ p → A() = C)`; it says nothing about
credences or about `liminf O_n(S) ≥ p`, which is the LI-level statement in `LILesion.lean`.
Source: Soto 2023 "Argmaxing our strategy" p. 3 (Picking flowers); [[bli-soto-b-inventory]] 004; [[dp-troll-bridge-mandate]] target 11
Kind: C
Fidelity: weaker: modal skeleton only; the credence content is not here
Hyps: (a) none -/
theorem flower_fixed_point {p : ℕ} {q χ : Modal.Formula ℕ} (hp : p ∉ q.atoms)
    (h : Modal.GL ⊢ χ 🡘 (□χ 🡒 q)) : Modal.GL ⊢ χ 🡘 (□q 🡒 q) := by
  have hmod : Modalized p (□(.atom p) 🡒 q) := ⟨trivial, modalized_of_notMem_atoms hp⟩
  have hq : q⟦diag p χ⟧ = q := subst_diag_of_notMem_atoms hp
  have hq' : q⟦diag p (□q 🡒 q)⟧ = q := subst_diag_of_notMem_atoms hp
  have hχ : Modal.GL ⊢ χ 🡘 (□(.atom p) 🡒 q)⟦diag p χ⟧ := by
    simpa [diag, hq] using h
  have hψ : Modal.GL ⊢ (□q 🡒 q) 🡘 (□(.atom p) 🡒 q)⟦diag p (□q 🡒 q)⟧ := by
    simpa [diag, hq'] using flower_shape_fixed_point q
  exact glFixedPoint_uniqueness hmod hχ hψ

end Cleanroom.Decision.DpTrollBridge
