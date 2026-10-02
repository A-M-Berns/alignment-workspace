/-
  Troll Bridge: the theorem in the single-□ idealization and the ordering classification.

  Targets 1 and 2 of [[dp-troll-bridge-mandate]]. Over the definitions of record in
  `Basic.lean`, every theorem quantifies over *any* GL fixed point `χ` of an ordering's rule,
  and the classification is proved structurally (by the shape of the ordering), not by
  enumerating the 24 permutations:

  - cross-first (12 orderings): `GL ⊢ χ 🡘 □⊥` — Löb, `crossFirst_iff_boxBot`;
  - escapers (3): `GL ⊢ χ 🡘 ∼□⊥` — `escaper_iff_con`;
  - dead (8): `GL ⊢ ∼χ` — `dead_stays`;
  - the odd one (1): `GL ⊢ χ 🡘 ∼□⊥ ⋏ □□⊥` and `GL ⊬ χ 🡒 □⊥` — `odd_iff`, `odd_lesion_unprovable`.

  Plus the dead-tail lemma and Stuart Armstrong's two rewrites as equalities of fixed points
  (target 2), and the 12/3/8/1 count as a `decide` over `List.permutations'`.

  Sources: `sl-workflow/notes/repair/P11.md` P11-1′, P11-4′, P11-6′; [[dp-sl-inventory]] 059;
  [[dp-sl-2-inventory]] 033.
-/

import Cleanroom.Decision.DpTrollBridge.Basic
import ModalAgents.GL

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

namespace Cleanroom.Decision.DpTrollBridge

/-! ## Generic facts about the nested-`if` rule -/

/-- "Some cross clause fires": if every cross clause's condition implies `X` and the default
implies `X`, the rule implies `X`.
Source: none: infrastructure (the "any firing cross clause" step of the mandate's proof route)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma ruleWith_imp_of_cross {cond : Clause → Modal.Formula ℕ → Modal.Formula ℕ}
    {d X c : Modal.Formula ℕ} (l : List Clause)
    (hcross : ∀ cl ∈ l, cl.isCross → Modal.GL ⊢ cond cl c 🡒 X) (hd : Modal.GL ⊢ d 🡒 X) :
    Modal.GL ⊢ ruleWith cond d l c 🡒 X := by
  induction l with
  | nil => simpa [ruleWith]
  | cons cl rest ih =>
    have ih' := ih (fun x hx => hcross x (by simp [hx]))
    simp only [ruleWith]
    rcases cl with ⟨a, u⟩
    cases a
    · have h1 := hcross (.cross, u) (by simp) rfl
      simp only [Clause.act]
      cl_prover [h1, ih']
    · simp only [Clause.act]
      cl_prover [ih']

/-- If the head clause is a cross clause, its condition implies the rule (the first disjunct).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma cond_imp_ruleWith_of_cross {cond : Clause → Modal.Formula ℕ → Modal.Formula ℕ}
    {d c : Modal.Formula ℕ} (cl : Clause) (hcl : cl.isCross) (rest : List Clause) :
    Modal.GL ⊢ cond cl c 🡒 ruleWith cond d (cl :: rest) c := by
  rcases cl with ⟨a, u⟩
  cases a
  · simp only [ruleWith, Clause.act]
    cl_prover
  · simp [Clause.isCross] at hcl

/-- **Dead-tail lemma.** Everything after a clause whose condition is a GL theorem — later
clauses and the default alike — is dead: the rules are GL-equivalent whatever follows.
Source: `sl-workflow/notes/repair/P11.md` P11-4′ (the `elif` "fires whenever reached"); [[dp-troll-bridge-mandate]] target 2(a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem ruleWith_dead_tail {cond : Clause → Modal.Formula ℕ → Modal.Formula ℕ}
    {d d' c : Modal.Formula ℕ} (l₁ : List Clause) (cl : Clause) (l₂ l₂' : List Clause)
    (hthm : Modal.GL ⊢ cond cl c) :
    Modal.GL ⊢ ruleWith cond d (l₁ ++ cl :: l₂) c 🡘 ruleWith cond d' (l₁ ++ cl :: l₂') c := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append, ruleWith]
    cl_prover [hthm]
  | cons x l₁ ih =>
    simp only [List.cons_append, ruleWith]
    cl_prover [ih]

/-- If the clauses up to some clause `cl` are all cross clauses and `cl`'s condition is a GL
theorem, the rule is a GL theorem (the agent provably crosses).
Source: none: infrastructure (the escaper's tail)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma ruleWith_of_cross_prefix {cond : Clause → Modal.Formula ℕ → Modal.Formula ℕ}
    {d c : Modal.Formula ℕ} (l₁ : List Clause) (h₁ : ∀ x ∈ l₁, x.isCross)
    (cl : Clause) (hcl : cl.isCross) (l₂ : List Clause) (hthm : Modal.GL ⊢ cond cl c) :
    Modal.GL ⊢ ruleWith cond d (l₁ ++ cl :: l₂) c := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append]
    exact (cond_imp_ruleWith_of_cross cl hcl l₂) ⨀ hthm
  | cons x l₁ ih =>
    have hx : x.isCross := h₁ x (by simp)
    have ih' := ih (fun y hy => h₁ y (by simp [hy]))
    simp only [List.cons_append, ruleWith]
    rcases x with ⟨a, u⟩
    cases a
    · simp only [Clause.act]
      cl_prover [ih']
    · simp [Clause.isCross] at hx

/-- If the clauses up to some stay clause `cl` are all stay clauses and `cl`'s condition is a
GL theorem, the rule is GL-refutable (the agent provably stays).
Source: none: infrastructure (the dead orderings)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma not_ruleWith_of_stay_prefix {cond : Clause → Modal.Formula ℕ → Modal.Formula ℕ}
    {d c : Modal.Formula ℕ} (l₁ : List Clause) (h₁ : ∀ x ∈ l₁, ¬ x.isCross)
    (cl : Clause) (hcl : ¬ cl.isCross) (l₂ : List Clause) (hthm : Modal.GL ⊢ cond cl c) :
    Modal.GL ⊢ ∼(ruleWith cond d (l₁ ++ cl :: l₂) c) := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append, ruleWith]
    rcases cl with ⟨a, u⟩
    cases a
    · exact absurd rfl hcl
    · simp only [Clause.act]
      cl_prover [hthm]
  | cons x l₁ ih =>
    have hx : ¬ x.isCross := h₁ x (by simp)
    have ih' := ih (fun y hy => h₁ y (by simp [hy]))
    simp only [List.cons_append, ruleWith]
    rcases x with ⟨a, u⟩
    cases a
    · exact absurd rfl hx
    · simp only [Clause.act]
      cl_prover [ih']

/-! ## Target 1(a): cross-first orderings — the Troll Bridge theorem -/

/-- **The Löb core of Troll Bridge**, abstracted: `χ` is a fixed point of `R`; the head
condition `A₁` implies `R`, self-boxes (`A₁ 🡒 □A₁`, it is a `□`-formula), is implied by
`□∼χ` and by `□⊥`; and `R` implies that some cross condition fires
(`□(χ 🡒 ∼□⊥) ⋎ □∼χ`). Then `GL ⊢ χ 🡘 □⊥`. The proof: under `□(χ 🡒 □⊥)` and `χ`, a cross
clause fires, so `□∼χ`, so `A₁`, so `□A₁`, so `□R`, so `□χ`, so `□⊥` — this is
`GL ⊢ □L 🡒 L` for `L := χ 🡒 □⊥`, and `lob_rule` closes; conversely `□⊥ 🡒 A₁ 🡒 R 🡒 χ`.
`□χ` is derived from the *boxed head clause*, never assumed (no Σ₁-completeness of `χ`).
Source: `sl-workflow/notes/repair/P11.md` P11-1′, P11-6′(b); [[dp-troll-bridge-mandate]] target 1 "Proof route for (a)"
Kind: P
Fidelity: exact
Hyps: (a) none (the six hypotheses are discharged by `crossFirst_iff_boxBot`) -/
theorem lob_core {χ R A₁ : Modal.Formula ℕ}
    (hfix : Modal.GL ⊢ χ 🡘 R) (hA₁R : Modal.GL ⊢ A₁ 🡒 R)
    (hfour : Modal.GL ⊢ A₁ 🡒 □A₁)
    (hN : Modal.GL ⊢ □(∼χ) 🡒 A₁) (hbot : Modal.GL ⊢ □⊥ 🡒 A₁)
    (hfire : Modal.GL ⊢ R 🡒 □(χ 🡒 ∼□⊥) ⋎ □(∼χ)) :
    Modal.GL ⊢ χ 🡘 □⊥ := by
  have hA₁χ : Modal.GL ⊢ A₁ 🡒 χ := by cl_prover [hA₁R, hfix]
  have hBR : Modal.GL ⊢ □A₁ 🡒 □χ := imply_box_distribute'! hA₁χ
  have hcollect : Modal.GL ⊢ □χ ⋏ □(∼χ) 🡒 □⊥ := by
    have h1 : Modal.GL ⊢ χ ⋏ ∼χ 🡒 ⊥ := by cl_prover
    exact C!_trans collect_box_and! (imply_box_distribute'! h1)
  have hQN : Modal.GL ⊢ □(χ 🡒 □⊥) ⋏ □(χ 🡒 ∼□⊥) 🡒 □(∼χ) := by
    have h1 : Modal.GL ⊢ (χ 🡒 □⊥) ⋏ (χ 🡒 ∼□⊥) 🡒 ∼χ := by cl_prover
    exact C!_trans collect_box_and! (imply_box_distribute'! h1)
  have hlob : Modal.GL ⊢ □(χ 🡒 □⊥) 🡒 (χ 🡒 □⊥) := by
    cl_prover [hfix, hfire, hQN, hN, hfour, hBR, hcollect]
  have hL : Modal.GL ⊢ χ 🡒 □⊥ := ⟨lob_rule hlob.some⟩
  have hconv : Modal.GL ⊢ □⊥ 🡒 χ := by cl_prover [hbot, hA₁χ]
  cl_prover [hL, hconv]

/-- **Troll Bridge, cross-first (P11-1′; 12 of the 24 orderings).** For any ordering whose
first clause is `(cross,10)` or `(cross,0)` and whose remaining clauses carry no `−10`
utility (any list of such clauses, duplicates and omissions allowed — in particular the post
clauses), any agent `χ` of the ordering satisfies `GL ⊢ χ 🡘 □⊥`: the agent crosses exactly
when its logic is inconsistent. Proved once, structurally, via `lob_core`; equivalently from
the witness `boxBot_isAgent_crossFirst` and `agent_unique`.
Source: `sl-workflow/notes/repair/P11.md` P11-1′ ("every one of the 12 orderings whose first clause is a `cross` clause"); [[dp-sl-inventory]] 059; [[dp-troll-bridge-mandate]] target 1(a)
Kind: P
Fidelity: exact (the P11 ledger's `⊢ c → U=−10`, `⊬ c → U=10`, `⊬ c`, `⊬ ¬c` follow as corollaries)
Hyps: (a) none -/
theorem crossFirst_iff_boxBot {cl : Clause} {rest : List Clause} {χ : Modal.Formula ℕ}
    (hcl : cl = cross10 ∨ cl = cross0) (hrest : ∀ x ∈ rest, x.2 ≠ Util.um10)
    (h : IsAgent (cl :: rest) χ) : Modal.GL ⊢ χ 🡘 □⊥ := by
  have hfix := h.fixS
  have hclc : cl.isCross := by rcases hcl with rfl | rfl <;> rfl
  unfold ruleS at hfix
  apply lob_core (A₁ := cl.condS χ) hfix
  · exact cond_imp_ruleWith_of_cross cl hclc rest
  · rcases hcl with rfl | rfl <;> simp only [cross10, cross0, Clause.condS] <;> exact axiomFour!
  · rcases hcl with rfl | rfl
    · simp only [cross10, Clause.condS]
      exact imply_box_distribute'! (by cl_prover)
    · simp only [cross0, Clause.condS]
      cl_prover
  · rcases hcl with rfl | rfl <;> simp only [cross10, cross0, Clause.condS] <;>
      exact ⟨C_box_of_boxBot⟩
  · apply ruleWith_imp_of_cross
    · intro x hx hxc
      have hx' : x.2 ≠ Util.um10 := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rcases hcl with rfl | rfl <;> simp [cross10, cross0]
        · exact hrest x hx
      rcases x with ⟨a, u⟩
      simp only [Clause.isCross] at hxc
      subst hxc
      cases u
      · simp only [Clause.condS]
        cl_prover
      · simp only [Clause.condS]
        cl_prover
      · exact absurd rfl hx'
    · cl_prover

/-- Corollary: the lesion `GL ⊢ χ 🡒 □⊥` ("T ⊢ c → U = −10").
Source: `sl-workflow/notes/repair/P11.md` P11-1′
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem crossFirst_lesion {cl : Clause} {rest : List Clause} {χ : Modal.Formula ℕ}
    (hcl : cl = cross10 ∨ cl = cross0) (hrest : ∀ x ∈ rest, x.2 ≠ Util.um10)
    (h : IsAgent (cl :: rest) χ) : Modal.GL ⊢ χ 🡒 □⊥ := by
  have := crossFirst_iff_boxBot hcl hrest h
  cl_prover [this]

/-- Corollary: `GL ⊬ χ` — the cross-first agent's crossing is not provable.
Source: `sl-workflow/notes/repair/P11.md` P11-1′ ("⊬ c")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem crossFirst_unprovable {cl : Clause} {rest : List Clause} {χ : Modal.Formula ℕ}
    (hcl : cl = cross10 ∨ cl = cross0) (hrest : ∀ x ∈ rest, x.2 ≠ Util.um10)
    (h : IsAgent (cl :: rest) χ) : Modal.GL ⊬ χ := fun hχ => by
  have := crossFirst_iff_boxBot hcl hrest h
  exact unprovable_box_bot (by cl_prover [hχ, this])

/-- Corollary: `GL ⊬ ∼χ` — "the agent stays" is **not** a GL theorem for the post's agent
(it is the consistency reading `χ 🡘 □⊥` plus `GL ⊬ ∼□⊥`). This is the mandate's Known issue 1
against the plan's "`GL ⊢ ¬cross` via Löb".
Source: `sl-workflow/notes/repair/P11.md` P11-1′ ("⊬ ¬c"); [[dp-troll-bridge-mandate]] Known issue 1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem crossFirst_neg_unprovable {cl : Clause} {rest : List Clause} {χ : Modal.Formula ℕ}
    (hcl : cl = cross10 ∨ cl = cross0) (hrest : ∀ x ∈ rest, x.2 ≠ Util.um10)
    (h : IsAgent (cl :: rest) χ) : Modal.GL ⊬ ∼χ := fun hn => by
  have := crossFirst_iff_boxBot hcl hrest h
  exact unprovable_neg_box_bot (by cl_prover [hn, this])

/-- Corollary: `GL ⊬ χ 🡒 ∼□⊥` — "⊬ c → U = 10": the agent cannot prove crossing safe.
Source: `sl-workflow/notes/repair/P11.md` P11-1′ ("⊬ c → U=10")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem crossFirst_not_safe {cl : Clause} {rest : List Clause} {χ : Modal.Formula ℕ}
    (hcl : cl = cross10 ∨ cl = cross0) (hrest : ∀ x ∈ rest, x.2 ≠ Util.um10)
    (h : IsAgent (cl :: rest) χ) : Modal.GL ⊬ χ 🡒 ∼□⊥ := fun hs => by
  have := crossFirst_iff_boxBot hcl hrest h
  exact unprovable_neg_box_bot (by cl_prover [hs, this])

/-- **N+ witness for cross-first orderings:** `□⊥` itself is an agent of every cross-first
ordering (the fixed-point equation holds with `χ := □⊥`), and it is neither `⊤` nor `⊥` in GL
(`unprovable_box_bot`, `unprovable_neg_box_bot`). Existence also follows from
`agent_exists`; this witness is explicit.
Source: [[dp-troll-bridge-mandate]] target 1 trap (iv)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem boxBot_isAgent_crossFirst {cl : Clause} {rest : List Clause}
    (hcl : cl = cross10 ∨ cl = cross0) (hrest : ∀ x ∈ rest, x.2 ≠ Util.um10) :
    IsAgent (cl :: rest) (□⊥) := by
  have hclc : cl.isCross := by rcases hcl with rfl | rfl <;> rfl
  have g2 : Modal.GL ⊢ (∼(□⊥) 🡘 ∼(□(∼(□⊥))) : Modal.Formula ℕ) := gödel2!
  have hb : Modal.GL ⊢ (□(□⊥ 🡒 ∼□⊥) 🡘 □(∼□⊥) : Modal.Formula ℕ) := box_iff! (by cl_prover)
  have hfire : Modal.GL ⊢ ruleS (cl :: rest) (□⊥) 🡒 □⊥ := by
    unfold ruleS
    apply ruleWith_imp_of_cross
    · intro x hx hxc
      have hx' : x.2 ≠ Util.um10 := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rcases hcl with rfl | rfl <;> simp [cross10, cross0]
        · exact hrest x hx
      rcases x with ⟨a, u⟩
      simp only [Clause.isCross] at hxc
      subst hxc
      cases u
      · simp only [Clause.condS]
        cl_prover [g2, hb]
      · simp only [Clause.condS]
        cl_prover [g2]
      · exact absurd rfl hx'
    · cl_prover
  have hhead : Modal.GL ⊢ □⊥ 🡒 ruleS (cl :: rest) (□⊥) := by
    have hbot : Modal.GL ⊢ □⊥ 🡒 cl.condS (□⊥) := by
      rcases hcl with rfl | rfl <;> simp only [cross10, cross0, Clause.condS] <;>
        exact ⟨C_box_of_boxBot⟩
    exact C!_trans hbot (cond_imp_ruleWith_of_cross cl hclc rest)
  unfold IsAgent
  refine E!_trans ?_ (E!_symm (rule_iff_ruleS _ _))
  cl_prover [hfire, hhead]

/-- The witness `□⊥` is neither `⊤` nor `⊥` in GL (Gödel's second theorem in modal form,
from FAF).
Source: FAF `ModalAgents/GL.lean` (`unprovable_box_bot`, `unprovable_neg_box_bot`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem boxBot_nondegenerate : Modal.GL ⊬ (□⊥ : Modal.Formula ℕ) ∧ Modal.GL ⊬ (∼□⊥ : Modal.Formula ℕ) :=
  ⟨unprovable_box_bot, unprovable_neg_box_bot⟩

/-! ## Target 1(b): the escapers -/

/-- **The escapers (P11-6′(a); 3 of the 24 orderings).** For any ordering of the form
`(not,10) :: l₁ ++ (cross,10) :: l₂` with every clause of `l₁` a cross clause — among
permutations of the four post clauses, exactly "(not,10) first and (cross,10) before (not,0)"
— any agent `χ` satisfies `GL ⊢ χ 🡘 ∼□⊥`: the agent crosses exactly when its logic is
consistent. Proof: the head gives `χ 🡒 ∼□χ`, so `□χ 🡒 □∼□χ ⋏ □□χ 🡒 □⊥`, so `χ 🡒 ∼□⊥`, so
`□(χ 🡒 ∼□⊥)` is a theorem and the `(cross,10)` clause provably fires; then
`χ 🡘 ∼□χ 🡘 ∼□⊥`. Löb finds no purchase: the step to `□χ` would need negative introspection.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(a),(c); [[dp-troll-bridge-mandate]] target 1(b)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem escaper_iff_con {l₁ l₂ : List Clause} {χ : Modal.Formula ℕ}
    (h₁ : ∀ x ∈ l₁, x.isCross) (h : IsAgent (not10 :: (l₁ ++ cross10 :: l₂)) χ) :
    Modal.GL ⊢ χ 🡘 ∼□⊥ := by
  have hfix := h.fixS
  simp only [ruleS, ruleWith, not10, Clause.condS, Clause.act] at hfix
  have h1 : Modal.GL ⊢ χ 🡒 ∼□χ := by cl_prover [hfix]
  have h2 : Modal.GL ⊢ □χ 🡒 □⊥ := by
    have a : Modal.GL ⊢ □χ 🡒 □(∼□χ) := imply_box_distribute'! h1
    have b : Modal.GL ⊢ □χ 🡒 □□χ := axiomFour!
    have c : Modal.GL ⊢ □□χ ⋏ □(∼□χ) 🡒 □⊥ := by
      have h0 : Modal.GL ⊢ □χ ⋏ ∼□χ 🡒 ⊥ := by cl_prover
      exact C!_trans collect_box_and! (imply_box_distribute'! h0)
    cl_prover [a, b, c]
  have hbot : Modal.GL ⊢ □⊥ 🡒 □χ := ⟨C_box_of_boxBot⟩
  have h3 : Modal.GL ⊢ χ 🡒 ∼□⊥ := by cl_prover [h1, hbot]
  have hQ : Modal.GL ⊢ □(χ 🡒 ∼□⊥) := nec! h3
  have hR : Modal.GL ⊢ ruleWith Clause.condS ⊥ (l₁ ++ cross10 :: l₂) χ :=
    ruleWith_of_cross_prefix l₁ h₁ cross10 rfl l₂ hQ
  have h4 : Modal.GL ⊢ ∼□χ 🡒 χ := by cl_prover [hfix, hR]
  cl_prover [h1, h4, h2, hbot]

/-- Corollary: `GL ⊢ χ 🡒 ∼□⊥` — "crossing is evidence of consistency"; hence
`GL ⊢ χ 🡒 (χ ⋏ ∼□⊥)`, i.e. "⊢ c → U = 10".
Source: `sl-workflow/notes/repair/P11.md` P11-6′(a)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem escaper_safe {l₁ l₂ : List Clause} {χ : Modal.Formula ℕ}
    (h₁ : ∀ x ∈ l₁, x.isCross) (h : IsAgent (not10 :: (l₁ ++ cross10 :: l₂)) χ) :
    Modal.GL ⊢ χ 🡒 (χ ⋏ ∼□⊥) := by
  have := escaper_iff_con h₁ h
  cl_prover [this]

/-- Corollary: `GL ⊬ ∼χ` (and `GL ⊬ χ`): the escaper's crossing is the consistency statement,
provable neither way.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(a)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem escaper_undecided {l₁ l₂ : List Clause} {χ : Modal.Formula ℕ}
    (h₁ : ∀ x ∈ l₁, x.isCross) (h : IsAgent (not10 :: (l₁ ++ cross10 :: l₂)) χ) :
    Modal.GL ⊬ ∼χ ∧ Modal.GL ⊬ χ := by
  have hiff := escaper_iff_con h₁ h
  constructor
  · intro hn
    exact unprovable_box_bot (by cl_prover [hn, hiff])
  · intro hc
    exact unprovable_neg_box_bot (by cl_prover [hc, hiff])

/-- **N+ witness for the escapers:** `∼□⊥` is an agent of every escaper ordering.
Source: [[dp-troll-bridge-mandate]] target 1 trap (iv)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem negBoxBot_isAgent_escaper {l₁ l₂ : List Clause} (h₁ : ∀ x ∈ l₁, x.isCross) :
    IsAgent (not10 :: (l₁ ++ cross10 :: l₂)) (∼□⊥) := by
  have hR : Modal.GL ⊢ ruleWith Clause.condS ⊥ (l₁ ++ cross10 :: l₂) (∼□⊥) :=
    ruleWith_of_cross_prefix l₁ h₁ cross10 rfl l₂ (nec! (by cl_prover))
  have g2 : Modal.GL ⊢ (∼(□⊥) 🡘 ∼(□(∼(□⊥))) : Modal.Formula ℕ) := gödel2!
  unfold IsAgent
  refine E!_trans ?_ (E!_symm (rule_iff_ruleS _ _))
  simp only [ruleS, ruleWith, not10, Clause.condS, Clause.act]
  cl_prover [hR, g2]

/-- The three escaper orderings among the 24 permutations of the post clauses.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c)
Kind: D
Fidelity: exact
Hyps: n/a -/
def escaperOrderings : List (List Clause) :=
  [[not10, cross10, cross0, not0], [not10, cross10, not0, cross0], [not10, cross0, cross10, not0]]

/-- Each of the three escaper orderings is covered by `escaper_iff_con`.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem escaperOrderings_iff_con {l : List Clause} (hl : l ∈ escaperOrderings)
    {χ : Modal.Formula ℕ} (h : IsAgent l χ) : Modal.GL ⊢ χ 🡘 ∼□⊥ := by
  simp only [escaperOrderings, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact escaper_iff_con (l₁ := []) (l₂ := [cross0, not0]) (by simp) h
  · exact escaper_iff_con (l₁ := []) (l₂ := [not0, cross0]) (by simp) h
  · exact escaper_iff_con (l₁ := [cross0]) (l₂ := [not0]) (by simp [cross0, Clause.isCross]) h

/-! ## Target 1(c): the dead orderings -/

/-- **The dead orderings (8 of 24).** If `(not,0)` is preceded only by stay clauses — for
permutations: `(not,0)` precedes both cross clauses — any agent provably stays: `GL ⊢ ∼χ`.
The rule is GL-equivalent to `⊥`; the Löb sentence `χ 🡒 □⊥` holds vacuously and the agent is
outside the Troll Bridge situation. Propositional after `not_ruleWith_of_stay_prefix` (no
Löb), equivalently `⊥` is a fixed point (`bot_isAgent_dead`) plus `agent_unique`.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c) ("8 provably never cross"); [[dp-troll-bridge-mandate]] target 1(c)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem dead_stays {l₁ l₂ : List Clause} {χ : Modal.Formula ℕ}
    (h₁ : ∀ x ∈ l₁, ¬ x.isCross) (h : IsAgent (l₁ ++ not0 :: l₂) χ) : Modal.GL ⊢ ∼χ := by
  have hfix := h.fixS
  have hnot : Modal.GL ⊢ ∼(ruleS (l₁ ++ not0 :: l₂) χ) :=
    not_ruleWith_of_stay_prefix l₁ h₁ not0 (by simp [not0, Clause.isCross]) l₂
      (by simp only [not0, Clause.condS]; cl_prover)
  cl_prover [hfix, hnot]

/-- **N− witness for the dead orderings:** `⊥` is an agent (degenerate by necessity: every
agent of a dead ordering is GL-equivalent to `⊥` by `dead_stays`).
Source: [[dp-troll-bridge-mandate]] target 1(c)
Kind: N-
Fidelity: exact
Hyps: (a) none -/
theorem bot_isAgent_dead {l₁ l₂ : List Clause} (h₁ : ∀ x ∈ l₁, ¬ x.isCross) :
    IsAgent (l₁ ++ not0 :: l₂) ⊥ := by
  have hnot : Modal.GL ⊢ ∼(ruleS (l₁ ++ not0 :: l₂) ⊥) :=
    not_ruleWith_of_stay_prefix l₁ h₁ not0 (by simp [not0, Clause.isCross]) l₂
      (by simp only [not0, Clause.condS]; cl_prover)
  unfold IsAgent
  refine E!_trans ?_ (E!_symm (rule_iff_ruleS _ _))
  cl_prover [hnot]

/-! ## Target 1(d): the odd one -/

/-- The one ordering that is neither cross-first, escaper nor dead:
`(not,10), (cross,0), (not,0), (cross,10)`.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c)
Kind: D
Fidelity: exact
Hyps: n/a -/
def oddOrdering : List Clause := [not10, cross0, not0, cross10]

/-- The odd ordering's rule is GL-equivalent to `∼□χ ⋏ □∼χ` at any `χ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma ruleS_odd (χ : Modal.Formula ℕ) : Modal.GL ⊢ ruleS oddOrdering χ 🡘 (∼□χ ⋏ □(∼χ)) := by
  simp only [ruleS, ruleWith, oddOrdering, not10, cross0, not0, cross10, Clause.condS, Clause.act]
  cl_prover

/-- `ψ := ∼□⊥ ⋏ □□⊥` ("the logic is consistent but proves its own inconsistency-provability";
true exactly at height-1 worlds) satisfies the odd fixed-point equation
`ψ 🡘 ∼□ψ ⋏ □∼ψ`: `□ψ 🡘 □⊥` (via `gödel2`) and `□∼ψ 🡘 □□⊥` (via axiom L at `□⊥`).
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c) ("crosses at world 1 only")
Kind: P
Fidelity: exact
Hyps: (a) none -/
lemma oddShape_fixed_point :
    Modal.GL ⊢ ((∼□⊥ ⋏ □□⊥) 🡘 (∼□(∼□⊥ ⋏ □□⊥) ⋏ □(∼(∼□⊥ ⋏ □□⊥))) : Modal.Formula ℕ) := by
  have g2 : Modal.GL ⊢ (∼(□⊥) 🡘 ∼(□(∼(□⊥))) : Modal.Formula ℕ) := gödel2!
  have a1 : Modal.GL ⊢ (□(∼□⊥ ⋏ □□⊥) 🡒 □(∼□⊥) : Modal.Formula ℕ) :=
    imply_box_distribute'! (by cl_prover)
  have a2 : Modal.GL ⊢ (□⊥ 🡒 □(∼□⊥ ⋏ □□⊥) : Modal.Formula ℕ) := ⟨C_box_of_boxBot⟩
  have b1 : Modal.GL ⊢ (□□⊥ 🡒 □(∼(∼□⊥ ⋏ □□⊥)) : Modal.Formula ℕ) :=
    imply_box_distribute'! (by cl_prover)
  have b2 : Modal.GL ⊢ (□(∼(∼□⊥ ⋏ □□⊥)) 🡘 □(□□⊥ 🡒 □⊥) : Modal.Formula ℕ) :=
    box_iff! (by cl_prover)
  have b3 : Modal.GL ⊢ (□(□□⊥ 🡒 □⊥) 🡒 □□⊥ : Modal.Formula ℕ) := axiomL!
  have hbox : Modal.GL ⊢ (□(∼□⊥ ⋏ □□⊥) 🡘 □⊥ : Modal.Formula ℕ) := by cl_prover [g2, a1, a2]
  have hnbox : Modal.GL ⊢ (□(∼(∼□⊥ ⋏ □□⊥)) 🡘 □□⊥ : Modal.Formula ℕ) := by cl_prover [b1, b2, b3]
  cl_prover [hbox, hnbox]

/-- **The odd one.** Any agent of `(not,10), (cross,0), (not,0), (cross,10)` satisfies
`GL ⊢ χ 🡘 (∼□⊥ ⋏ □□⊥)`: it crosses exactly at "height 1" (consistent, but the logic proves
`□⊥` is provable). Via fixed-point uniqueness against `oddShape_fixed_point`.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c); [[dp-troll-bridge-mandate]] target 1(d)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem odd_iff {χ : Modal.Formula ℕ} (h : IsAgent oddOrdering χ) :
    Modal.GL ⊢ χ 🡘 (∼□⊥ ⋏ □□⊥) := by
  have hfix : Modal.GL ⊢ χ 🡘 (∼□χ ⋏ □(∼χ)) := E!_trans h.fixS (ruleS_odd χ)
  have hmod : Modalized 0 ((∼□(.atom 0) ⋏ □(∼(.atom 0))) : Modal.Formula ℕ) := by
    simp [Modalized]
  have hχ : Modal.GL ⊢ χ 🡘 ((∼□(.atom 0) ⋏ □(∼(.atom 0))) : Modal.Formula ℕ)⟦diag 0 χ⟧ := by
    simpa [diag] using hfix
  have hψ : Modal.GL ⊢ (∼□⊥ ⋏ □□⊥ : Modal.Formula ℕ) 🡘
      ((∼□(.atom 0) ⋏ □(∼(.atom 0))) : Modal.Formula ℕ)⟦diag 0 (∼□⊥ ⋏ □□⊥)⟧ := by
    simpa [diag] using oddShape_fixed_point
  exact glFixedPoint_uniqueness hmod hχ hψ

/-- For the odd ordering, Löb's sentence `χ 🡒 □⊥` is unprovable, and so are `χ` and `∼χ`.
Syntactic route: `⊢ (∼□⊥ ⋏ □□⊥) 🡒 □⊥` would give `⊢ □□⊥ 🡒 □⊥`, hence `⊢ □⊥` by Löb's
rule; `⊢ ∼χ` likewise; `⊢ χ` would give `⊢ ∼□⊥`. (The mandate's height-1 countermodel is the
semantic form of the same fact.)
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c) ("1 does not cross with L unprovable"); [[dp-troll-bridge-mandate]] target 1(d)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem odd_lesion_unprovable {χ : Modal.Formula ℕ} (h : IsAgent oddOrdering χ) :
    Modal.GL ⊬ (χ 🡒 □⊥) ∧ Modal.GL ⊬ ∼χ ∧ Modal.GL ⊬ χ := by
  have hiff := odd_iff h
  refine ⟨?_, ?_, ?_⟩
  · intro hL
    have h1 : Modal.GL ⊢ (□□⊥ 🡒 □⊥ : Modal.Formula ℕ) := by cl_prover [hL, hiff]
    exact unprovable_box_bot ⟨lob_rule h1.some⟩
  · intro hn
    have h1 : Modal.GL ⊢ (□□⊥ 🡒 □⊥ : Modal.Formula ℕ) := by cl_prover [hn, hiff]
    exact unprovable_box_bot ⟨lob_rule h1.some⟩
  · intro hc
    exact unprovable_neg_box_bot (by cl_prover [hc, hiff])

/-- **N+ witness for the odd ordering:** `∼□⊥ ⋏ □□⊥` is an agent of it.
Source: [[dp-troll-bridge-mandate]] target 1(d)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem oddShape_isAgent : IsAgent oddOrdering (∼□⊥ ⋏ □□⊥) := by
  unfold IsAgent
  refine E!_trans ?_ (E!_symm (rule_iff_ruleS _ _))
  refine E!_trans oddShape_fixed_point (E!_symm (ruleS_odd _))

/-! ## Target 2: Stuart Armstrong's two rewrites as equalities of fixed points -/

/-- `(not,0)`'s condition is a GL theorem (it is `□(∼c 🡒 ∼c)`).
Source: `sl-workflow/notes/repair/P11.md` P11-4′ ("`□(¬c → U=0)` is a theorem")
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma not0_cond_provable (c : Modal.Formula ℕ) : Modal.GL ⊢ not0.cond c :=
  nec! (by simp only [not0, Act.sentence, Util.sentence]; cl_prover)

/-- The rule of record with default `cross` (`⊤`) instead of `not` (`⊥`).
Source: `sl-workflow/notes/repair/P11.md` P11-4′(a) (Stuart's first rewrite)
Kind: D
Fidelity: exact
Hyps: n/a -/
def ruleDefaultCross (l : List Clause) (c : Modal.Formula ℕ) : Modal.Formula ℕ :=
  ruleWith Clause.cond ⊤ l c

/-- **Stuart's first rewrite is vacuous (P11-4′(a)).** For any ordering containing `(not,0)`,
changing the default from `not` to `cross` changes no fixed point: the rules are
GL-equivalent at every `c`, so the agents are the same formulas (and GL-equivalent by
`agent_unique`).
Source: `sl-workflow/notes/repair/P11.md` P11-4′(a); [[dp-sl-2-inventory]] 033; [[dp-troll-bridge-mandate]] target 2(b)
Kind: L
Fidelity: exact (world-for-world = GL-equivalence of the rules at every `c`)
Hyps: (a) none -/
theorem default_cross_vacuous (l₁ l₂ : List Clause) (c : Modal.Formula ℕ) :
    Modal.GL ⊢ rule (l₁ ++ not0 :: l₂) c 🡘 ruleDefaultCross (l₁ ++ not0 :: l₂) c :=
  ruleWith_dead_tail l₁ not0 l₂ l₂ (not0_cond_provable c)

/-- Hence the agents coincide: `χ` is an agent under default `not` iff under default `cross`.
Source: `sl-workflow/notes/repair/P11.md` P11-4′(a)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem isAgent_default_cross_iff (l₁ l₂ : List Clause) (χ : Modal.Formula ℕ) :
    IsAgent (l₁ ++ not0 :: l₂) χ ↔ Modal.GL ⊢ χ 🡘 ruleDefaultCross (l₁ ++ not0 :: l₂) χ := by
  have := default_cross_vacuous l₁ l₂ χ
  unfold IsAgent
  constructor
  · intro h; cl_prover [h, this]
  · intro h; cl_prover [h, this]

/-- **Stuart's second rewrite is vacuous (P11-4′(b)).** Inserting `(cross,−10)` (condition
`□(c 🡒 c ⋏ □⊥)`) anywhere after `(not,0)` changes no fixed point.
Source: `sl-workflow/notes/repair/P11.md` P11-4′(b) ("never reached"); [[dp-sl-2-inventory]] 033; [[dp-troll-bridge-mandate]] target 2(b)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem insert_crossm10_vacuous (l₁ l₂ l₃ : List Clause) (c : Modal.Formula ℕ) :
    Modal.GL ⊢ rule (l₁ ++ not0 :: l₂) c 🡘 rule (l₁ ++ not0 :: (l₂ ++ crossm10 :: l₃)) c :=
  ruleWith_dead_tail l₁ not0 l₂ (l₂ ++ crossm10 :: l₃) (not0_cond_provable c)

/-- Hence the agents coincide.
Source: `sl-workflow/notes/repair/P11.md` P11-4′(b)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem isAgent_insert_crossm10_iff (l₁ l₂ l₃ : List Clause) (χ : Modal.Formula ℕ) :
    IsAgent (l₁ ++ not0 :: l₂) χ ↔ IsAgent (l₁ ++ not0 :: (l₂ ++ crossm10 :: l₃)) χ := by
  have := insert_crossm10_vacuous l₁ l₂ l₃ χ
  unfold IsAgent
  constructor
  · intro h; cl_prover [h, this]
  · intro h; cl_prover [h, this]

/-- The post's agent with Stuart's clause appended, `(cross,10),(not,10),(cross,0),(not,0),
(cross,−10)`, is the post's agent: `GL ⊢ χ 🡘 □⊥` for any fixed point (P11-4′'s V5).
Source: `sl-workflow/notes/repair/P11.md` P11-4′ (V5)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem stuart_V5_iff_boxBot {χ : Modal.Formula ℕ}
    (h : IsAgent [cross10, not10, cross0, not0, crossm10] χ) : Modal.GL ⊢ χ 🡘 □⊥ := by
  have h' : IsAgent postOrdering χ :=
    (isAgent_insert_crossm10_iff [cross10, not10, cross0] [] [] χ).mpr h
  exact crossFirst_iff_boxBot (Or.inl rfl) (by simp [not10, cross0, not0]) h'

/-! ## The count 12 / 3 / 8 / 1 -/

/-- All 24 orderings of the four post clauses.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c)
Kind: D
Fidelity: exact
Hyps: n/a -/
def allOrderings : List (List Clause) := postClauses.permutations'

/-- There are 24 orderings.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem allOrderings_length : allOrderings.length = 24 := by decide

/-- 12 orderings are cross-first.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem count_crossFirst :
    (allOrderings.filter fun l => l.head? = some cross10 ∨ l.head? = some cross0).length = 12 := by
  decide

/-- 3 orderings are escapers: `(not,10)` first and `(cross,10)` before `(not,0)`.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem count_escapers :
    (allOrderings.filter fun l =>
      l.head? = some not10 ∧ l.idxOf cross10 < l.idxOf not0).length = 3 := by
  decide

/-- The escaper orderings are exactly `escaperOrderings` (as sets of orderings).
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem escapers_mem :
    ∀ l ∈ allOrderings,
      (l.head? = some not10 ∧ l.idxOf cross10 < l.idxOf not0) ↔ l ∈ escaperOrderings := by
  decide

/-- 8 orderings are dead: `(not,0)` precedes both cross clauses.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem count_dead :
    (allOrderings.filter fun l =>
      l.idxOf not0 < l.idxOf cross10 ∧ l.idxOf not0 < l.idxOf cross0).length = 8 := by
  decide

/-- The remaining ordering is `oddOrdering`.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem odd_mem :
    ∀ l ∈ allOrderings,
      (¬ (l.head? = some cross10 ∨ l.head? = some cross0) ∧
       ¬ (l.head? = some not10 ∧ l.idxOf cross10 < l.idxOf not0) ∧
       ¬ (l.idxOf not0 < l.idxOf cross10 ∧ l.idxOf not0 < l.idxOf cross0)) ↔ l = oddOrdering := by
  decide

/-! ## The classification as one statement (repair round 1) -/

/-- The 24 orderings listed by class: 12 cross-first, 3 escapers, 1 odd, 8 dead.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c); repair round 1 (adversarial N3)
Kind: D
Fidelity: exact
Hyps: n/a -/
def byClass : List (List Clause) :=
  [ [cross10, not10, cross0, not0], [cross10, not10, not0, cross0],
    [cross10, cross0, not10, not0], [cross10, cross0, not0, not10],
    [cross10, not0, not10, cross0], [cross10, not0, cross0, not10],
    [cross0, cross10, not10, not0], [cross0, cross10, not0, not10],
    [cross0, not10, cross10, not0], [cross0, not10, not0, cross10],
    [cross0, not0, cross10, not10], [cross0, not0, not10, cross10],
    [not10, cross10, cross0, not0], [not10, cross10, not0, cross0], [not10, cross0, cross10, not0],
    [not10, cross0, not0, cross10],
    [not0, cross10, not10, cross0], [not0, cross10, cross0, not10],
    [not0, not10, cross10, cross0], [not0, not10, cross0, cross10],
    [not0, cross0, cross10, not10], [not0, cross0, not10, cross10],
    [not10, not0, cross10, cross0], [not10, not0, cross0, cross10] ]

/-- Every ordering is in the class list.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem allOrderings_sub_byClass : ∀ l ∈ allOrderings, l ∈ byClass := by decide

/-- **The classification is complete.** Every agent of every one of the 24 orderings falls
under one of the four theorems: `χ 🡘 □⊥` (cross-first), `χ 🡘 ∼□⊥` (escaper), `∼χ` (dead),
or `χ 🡘 ∼□⊥ ⋏ □□⊥` (the odd one). A 24-way split, each case one of the four theorems with
explicit `l₁`/`l₂`; the filter predicates of the counts are thereby tied to the theorems.
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c); repair round 1 (adversarial N3, fidelity N12)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem classification_complete :
    ∀ l ∈ allOrderings, ∀ χ : Modal.Formula ℕ, IsAgent l χ →
      (Modal.GL ⊢ χ 🡘 □⊥) ∨ (Modal.GL ⊢ χ 🡘 ∼□⊥) ∨ (Modal.GL ⊢ ∼χ) ∨
      (Modal.GL ⊢ χ 🡘 (∼□⊥ ⋏ □□⊥)) := by
  intro l hl χ h
  have hl' := allOrderings_sub_byClass l hl
  simp only [byClass, List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- 12 cross-first
  · exact Or.inl (crossFirst_iff_boxBot (Or.inl rfl) (by decide) h)
  · exact Or.inl (crossFirst_iff_boxBot (Or.inl rfl) (by decide) h)
  · exact Or.inl (crossFirst_iff_boxBot (Or.inl rfl) (by decide) h)
  · exact Or.inl (crossFirst_iff_boxBot (Or.inl rfl) (by decide) h)
  · exact Or.inl (crossFirst_iff_boxBot (Or.inl rfl) (by decide) h)
  · exact Or.inl (crossFirst_iff_boxBot (Or.inl rfl) (by decide) h)
  · exact Or.inl (crossFirst_iff_boxBot (Or.inr rfl) (by decide) h)
  · exact Or.inl (crossFirst_iff_boxBot (Or.inr rfl) (by decide) h)
  · exact Or.inl (crossFirst_iff_boxBot (Or.inr rfl) (by decide) h)
  · exact Or.inl (crossFirst_iff_boxBot (Or.inr rfl) (by decide) h)
  · exact Or.inl (crossFirst_iff_boxBot (Or.inr rfl) (by decide) h)
  · exact Or.inl (crossFirst_iff_boxBot (Or.inr rfl) (by decide) h)
  -- 3 escapers
  · exact Or.inr (Or.inl (escaper_iff_con (l₁ := []) (l₂ := [cross0, not0]) (by simp) h))
  · exact Or.inr (Or.inl (escaper_iff_con (l₁ := []) (l₂ := [not0, cross0]) (by simp) h))
  · exact Or.inr (Or.inl (escaper_iff_con (l₁ := [cross0]) (l₂ := [not0])
      (by simp [cross0, Clause.isCross]) h))
  -- the odd one
  · exact Or.inr (Or.inr (Or.inr (odd_iff h)))
  -- 8 dead
  · exact Or.inr (Or.inr (Or.inl (dead_stays (l₁ := []) (l₂ := [cross10, not10, cross0]) (by simp) h)))
  · exact Or.inr (Or.inr (Or.inl (dead_stays (l₁ := []) (l₂ := [cross10, cross0, not10]) (by simp) h)))
  · exact Or.inr (Or.inr (Or.inl (dead_stays (l₁ := []) (l₂ := [not10, cross10, cross0]) (by simp) h)))
  · exact Or.inr (Or.inr (Or.inl (dead_stays (l₁ := []) (l₂ := [not10, cross0, cross10]) (by simp) h)))
  · exact Or.inr (Or.inr (Or.inl (dead_stays (l₁ := []) (l₂ := [cross0, cross10, not10]) (by simp) h)))
  · exact Or.inr (Or.inr (Or.inl (dead_stays (l₁ := []) (l₂ := [cross0, not10, cross10]) (by simp) h)))
  · exact Or.inr (Or.inr (Or.inl (dead_stays (l₁ := [not10]) (l₂ := [cross10, cross0])
      (by simp [not10, Clause.isCross]) h)))
  · exact Or.inr (Or.inr (Or.inl (dead_stays (l₁ := [not10]) (l₂ := [cross0, cross10])
      (by simp [not10, Clause.isCross]) h)))

/-- The three counted classes are pairwise disjoint on the 24 orderings (with `odd_mem`, the
12/3/8/1 split is a partition).
Source: `sl-workflow/notes/repair/P11.md` P11-6′(c); repair round 1 (fidelity N12)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem classes_disjoint :
    ∀ l ∈ allOrderings,
      ¬ ((l.head? = some cross10 ∨ l.head? = some cross0) ∧
         (l.head? = some not10 ∧ l.idxOf cross10 < l.idxOf not0)) ∧
      ¬ ((l.head? = some cross10 ∨ l.head? = some cross0) ∧
         (l.idxOf not0 < l.idxOf cross10 ∧ l.idxOf not0 < l.idxOf cross0)) ∧
      ¬ ((l.head? = some not10 ∧ l.idxOf cross10 < l.idxOf not0) ∧
         (l.idxOf not0 < l.idxOf cross10 ∧ l.idxOf not0 < l.idxOf cross0)) := by
  decide

end Cleanroom.Decision.DpTrollBridge
