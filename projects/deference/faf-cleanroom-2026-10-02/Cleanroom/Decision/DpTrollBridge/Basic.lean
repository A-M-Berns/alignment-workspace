/-
  Troll Bridge over Foundation's GL: definitions of record.

  Package `dp-troll-bridge` of the faf-cleanroom run. The post's proof-search agent
  (`sl-workflow/posts/11-troll-bridge-5.md`) searches "action ⇒ utility" pairs in a fixed
  order and takes the action of the first pair it can prove; the troll fires iff the agent
  crosses and the logic is inconsistent (`□⊥`). Here the logic is Foundation's `Modal.GL`,
  the agent's action is a formula `c` ("cross"), and utilities are *encoded*, not atoms:
  `U = 10` is `c ⋏ ∼□⊥`, `U = −10` is `c ⋏ □⊥`, `U = 0` is `∼c`. A clause `(action, utility)`
  has the search condition `□(action-sentence 🡒 utility-sentence)`; the rule of an ordering
  is the nested `if` over its clauses; the agent of an ordering is any GL fixed point of the
  rule (existence and uniqueness from FAF's `glFixedPoint_thm42` / `glFixedPoint_uniqueness`).

  Sources: [[dp-troll-bridge-mandate]] "The modal idealization"; [[two-lesions-doc-2026-09-18]]
  §7 (the setting); `sl-workflow/notes/repair/P11.md` P11-1′/6′.
-/

import ModalAgents.FixedPoint

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

namespace Cleanroom.Decision.DpTrollBridge

/-! ## Clauses -/

/-- The agent's two actions. `stay` is the post's "not cross".
Source: `posts/11-troll-bridge-5.md` (the agent's pseudocode); [[dp-troll-bridge-mandate]] §"The modal idealization"
Kind: D
Fidelity: exact
Hyps: n/a -/
inductive Act
  | cross
  | stay
  deriving DecidableEq, Repr

/-- The three utility levels of the environment: `u10` (crossed, bridge intact), `u0`
(stayed), `um10` (crossed, troll fired).
Source: `posts/11-troll-bridge-5.md` (the environment); [[two-lesions-doc-2026-09-18]] §7 payoffs
Kind: D
Fidelity: exact
Hyps: n/a -/
inductive Util
  | u10
  | u0
  | um10
  deriving DecidableEq, Repr

/-- A clause of the proof-search agent: an (action, utility) pair it looks for a proof of.
Source: `posts/11-troll-bridge-5.md` (the agent's pseudocode)
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev Clause := Act × Util

/-- The action sentence in terms of the crossing formula `c`: `c` for cross, `∼c` for stay.
Source: [[two-lesions-doc-2026-09-18]] §7 ("Cross … and Stay its negation")
Kind: D
Fidelity: exact
Hyps: n/a -/
def Act.sentence : Act → Modal.Formula ℕ → Modal.Formula ℕ
  | .cross, c => c
  | .stay, c => ∼c

/-- The utility sentences, encoded from the troll's rule (fires iff crossing and `□⊥`):
`U = 10` is `c ⋏ ∼□⊥`, `U = −10` is `c ⋏ □⊥`, `U = 0` is `∼c`. Utilities are not atoms: an
agent over utility atoms would be an unrelated agent (the mandate's trap (iii)).
Source: [[two-lesions-doc-2026-09-18]] §7 (payoffs and the troll `Blow ↔ Cross ∧ □⊥`); [[dp-troll-bridge-mandate]] §"The modal idealization"
Kind: D
Fidelity: exact (the three payoff clauses and the troll's rule, read as definitions)
Hyps: n/a -/
def Util.sentence : Util → Modal.Formula ℕ → Modal.Formula ℕ
  | .u10, c => c ⋏ ∼□⊥
  | .um10, c => c ⋏ □⊥
  | .u0, c => ∼c

/-- The search condition of a clause: "the logic proves action ⇒ utility", i.e.
`□(action-sentence 🡒 utility-sentence)`. This is the raw reading of the post's
`A() = a ⊢ U() = u`; `Clause.condS` is its GL-simplified form, and `cond_iff_condS` is the
fidelity check between them.
Source: `posts/11-troll-bridge-5.md` (the agent's pseudocode); [[dp-troll-bridge-mandate]] §"The modal idealization"
Kind: D
Fidelity: exact
Hyps: n/a -/
def Clause.cond (cl : Clause) (c : Modal.Formula ℕ) : Modal.Formula ℕ :=
  □(cl.1.sentence c 🡒 cl.2.sentence c)

/-- The GL-simplified search conditions: `(cross,10) ↦ □(c 🡒 ∼□⊥)`, `(not,10) ↦ □c`,
`(cross,0) ↦ □∼c`, `(not,0) ↦ ⊤`, `(cross,−10) ↦ □(c 🡒 □⊥)`, `(not,−10) ↦ □c`.
Proofs are run over these; `cond_iff_condS` ties them to the raw conditions of record.
Source: [[dp-troll-bridge-mandate]] §"The modal idealization" (the four equivalences)
Kind: D
Fidelity: exact (GL-equivalent to `Clause.cond`, by `cond_iff_condS`)
Hyps: n/a -/
def Clause.condS : Clause → Modal.Formula ℕ → Modal.Formula ℕ
  | (.cross, .u10), c => □(c 🡒 ∼□⊥)
  | (.stay, .u10), c => □c
  | (.cross, .u0), c => □(∼c)
  | (.stay, .u0), _ => ⊤
  | (.cross, .um10), c => □(c 🡒 □⊥)
  | (.stay, .um10), c => □c

/-- What a firing clause outputs, as the truth value of "the agent crosses": `⊤` for a
cross clause, `⊥` for a stay clause.
Source: [[dp-troll-bridge-mandate]] §"The modal idealization" (`actᵢ := ⊤` / `⊥`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def Clause.act : Clause → Modal.Formula ℕ
  | (.cross, _) => ⊤
  | (.stay, _) => ⊥

/-- A clause is a cross clause iff its action is `cross`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Clause.isCross (cl : Clause) : Prop := cl.1 = .cross

/-! ## The rule of an ordering -/

/-- The nested-`if` rule over a list of clauses with a given condition function and default:
`if cond₁ then act₁ else if cond₂ then act₂ … else dflt`, rendered as
`(cond₁ ⋏ act₁) ⋎ (∼cond₁ ⋏ (…))`. The agent crosses iff the first clause whose condition
holds is a cross clause (or, if none holds, iff the default says so). Generic in the
condition function so that the raw rule and the simplified rule are both instances.
Source: [[dp-troll-bridge-mandate]] §"The modal idealization" (the rule as a nested `if`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def ruleWith (cond : Clause → Modal.Formula ℕ → Modal.Formula ℕ) (dflt : Modal.Formula ℕ) :
    List Clause → Modal.Formula ℕ → Modal.Formula ℕ
  | [], _ => dflt
  | cl :: rest, c => (cond cl c ⋏ cl.act) ⋎ (∼(cond cl c) ⋏ ruleWith cond dflt rest c)

/-- The rule of record of an ordering `l` (default `stay`): the nested `if` over the raw
conditions `Clause.cond`, in the crossing formula `c`. This is P11's world-by-world modal
fixed point, **not** literally unbounded proof search: the negative branches
`∼(cond cl c) ⋏ …` of `ruleWith` decide `¬□φ`, which an actual proof searcher cannot detect
to fall through an `elif` (`repair/P11.md`, standing hypothesis, line 39). A reader of the
Lean alone should see the idealization here (repair round 1, fidelity N8).
Source: `posts/11-troll-bridge-5.md` (the agent); `sl-workflow/notes/repair/P11.md` line 39 (the modal idealization); [[dp-troll-bridge-mandate]] §"The modal idealization"
Kind: D
Fidelity: variant: P11's world-by-world modal fixed point (default `not`, as in the post); the negative branches are not available to an actual proof searcher
Hyps: n/a -/
def rule (l : List Clause) (c : Modal.Formula ℕ) : Modal.Formula ℕ :=
  ruleWith Clause.cond ⊥ l c

/-- The simplified rule: the same nested `if` over `Clause.condS`. GL-equivalent to `rule`
(`rule_iff_ruleS`); proofs are run over it.
Source: [[dp-troll-bridge-mandate]] §"The modal idealization"
Kind: D
Fidelity: exact (GL-equivalent to `rule`)
Hyps: n/a -/
def ruleS (l : List Clause) (c : Modal.Formula ℕ) : Modal.Formula ℕ :=
  ruleWith Clause.condS ⊥ l c

/-- The agent of ordering `l` is any formula `χ` satisfying the fixed-point equation
`GL ⊢ χ 🡘 rule l χ` — "the agent crosses iff its search, run on its own crossing sentence,
lands on a cross clause". Existence: `agent_exists`; uniqueness up to GL-equivalence:
`agent_unique`. Stated for *any* fixed point, not FAF's Skolemized `glFixedPoint`, whose
equation is private.
Source: [[dp-troll-bridge-mandate]] §"The modal idealization" (the agent of ordering σ)
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsAgent (l : List Clause) (χ : Modal.Formula ℕ) : Prop :=
  Modal.GL ⊢ χ 🡘 rule l χ

/-! ## The post's clauses and ordering -/

/-- The clause `(cross, 10)`.
Source: `posts/11-troll-bridge-5.md`
Kind: D
Fidelity: exact
Hyps: n/a -/
def cross10 : Clause := (.cross, .u10)

/-- The clause `(not cross, 10)`.
Source: `posts/11-troll-bridge-5.md`
Kind: D
Fidelity: exact
Hyps: n/a -/
def not10 : Clause := (.stay, .u10)

/-- The clause `(cross, 0)`.
Source: `posts/11-troll-bridge-5.md`
Kind: D
Fidelity: exact
Hyps: n/a -/
def cross0 : Clause := (.cross, .u0)

/-- The clause `(not cross, 0)`.
Source: `posts/11-troll-bridge-5.md`
Kind: D
Fidelity: exact
Hyps: n/a -/
def not0 : Clause := (.stay, .u0)

/-- The clause `(cross, −10)` of Stuart Armstrong's second rewrite (P11-4′(b)).
Source: `sl-workflow/notes/repair/P11.md` P11-4′
Kind: D
Fidelity: exact
Hyps: n/a -/
def crossm10 : Clause := (.cross, .um10)

/-- The post's ordering: cross-first at each utility level, `(cross,10), (not,10), (cross,0),
(not,0)`, default `not`.
Source: `posts/11-troll-bridge-5.md`; `sl-workflow/notes/repair/P11.md` P11-1′ ("cross-first at each utility level, default `not`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def postOrdering : List Clause := [cross10, not10, cross0, not0]

/-- The four post clauses; a list over them is a "post-type" ordering (no `−10` clause).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def postClauses : List Clause := [cross10, not10, cross0, not0]

/-! ## The Löbian-lesion schema -/

/-- The credence-abstracted lesion schema `H c := □(c 🡒 □⊥) 🡒 ∼c`: "if the logic proves that
crossing entails inconsistency, the agent stays". It abstracts (α) (T-respect: `□φ → P(φ)=1`),
the expectation arithmetic `E[U | Cross] = 10 − 20·P(□⊥ | Cross)` with `E[U | Stay] = 0`, and
(β) (the agent crosses iff `E[U | Cross] > E[U | Stay]`) of [[two-lesions-doc-2026-09-18]] §7
into one T-verifiable schema. This is a `(c)` modelling substitution: the arithmetic layer
(a formalized credence over Foundation's PA) is not attempted in this package.
Source: [[two-lesions-doc-2026-09-18]] §7 ((α), (β), Lemma 8's proof); [[dp-troll-bridge-mandate]] target 3
Kind: D
Fidelity: variant: the three assumptions collapsed to one propositional-modal schema
Hyps: (c) credence abstraction -/
def H (c : Modal.Formula ℕ) : Modal.Formula ℕ :=
  □(c 🡒 □⊥) 🡒 ∼c

/-! ## The encoding check: raw conditions are GL-equivalent to the simplified ones -/

/-- The six clause conditions of record are GL-equivalent to their simplified forms:
`□(c 🡒 c ⋏ ∼□⊥) 🡘 □(c 🡒 ∼□⊥)`, `□(∼c 🡒 c ⋏ ∼□⊥) 🡘 □c`, `□(c 🡒 ∼c) 🡘 □∼c`,
`□(∼c 🡒 ∼c) 🡘 ⊤`, `□(c 🡒 c ⋏ □⊥) 🡘 □(c 🡒 □⊥)`, `□(∼c 🡒 c ⋏ □⊥) 🡘 □c`. This is where the
utility encoding is checked against the post's clauses.
Source: [[dp-troll-bridge-mandate]] §"The modal idealization" (the four equivalences)
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma cond_iff_condS (cl : Clause) (c : Modal.Formula ℕ) :
    Modal.GL ⊢ cl.cond c 🡘 cl.condS c := by
  rcases cl with ⟨a, u⟩
  cases a <;> cases u <;> simp only [Clause.cond, Clause.condS, Act.sentence, Util.sentence]
  · exact box_iff! (by cl_prover)
  · exact box_iff! (by cl_prover)
  · exact box_iff! (by cl_prover)
  · exact box_iff! (by cl_prover)
  · have h : Modal.GL ⊢ □(∼c 🡒 ∼c) := nec! (by cl_prover)
    cl_prover [h]
  · exact box_iff! (by cl_prover)

/-- Pointwise GL-equivalent condition functions give GL-equivalent rules (same default).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma ruleWith_congr {cond cond' : Clause → Modal.Formula ℕ → Modal.Formula ℕ}
    {d : Modal.Formula ℕ} (l : List Clause) (c : Modal.Formula ℕ)
    (h : ∀ cl ∈ l, Modal.GL ⊢ cond cl c 🡘 cond' cl c) :
    Modal.GL ⊢ ruleWith cond d l c 🡘 ruleWith cond' d l c := by
  induction l with
  | nil => exact E!_id
  | cons cl rest ih =>
    have h1 := h cl (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    simp only [ruleWith]
    cl_prover [h1, h2]

/-- The rule of record is GL-equivalent to the simplified rule, for every ordering and every
crossing formula.
Source: [[dp-troll-bridge-mandate]] §"The modal idealization"
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma rule_iff_ruleS (l : List Clause) (c : Modal.Formula ℕ) :
    Modal.GL ⊢ rule l c 🡘 ruleS l c :=
  ruleWith_congr l c (fun cl _ => cond_iff_condS cl c)

/-- An agent of `l` also satisfies the simplified fixed-point equation.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma IsAgent.fixS {l : List Clause} {χ : Modal.Formula ℕ} (h : IsAgent l χ) :
    Modal.GL ⊢ χ 🡘 ruleS l χ :=
  E!_trans h (rule_iff_ruleS l χ)

/-! ## Modalization and substitution: the fixed point exists and is unique -/

/-- Every raw clause condition is modalized in the diagonal atom (it is a `□`-formula).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma modalized_cond (cl : Clause) (p : ℕ) : Modalized p (cl.cond (.atom p)) := by
  simp [Clause.cond, Modalized]

/-- Every clause output (`⊤` or `⊥`) is modalized in any atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma modalized_act (cl : Clause) (p : ℕ) : Modalized p cl.act := by
  rcases cl with ⟨a, u⟩
  cases a <;> simp [Clause.act, Modalized]

/-- The nested-`if` rule is modalized in `p` whenever every condition and the default are.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma modalized_ruleWith {p : ℕ} (cond : Clause → Modal.Formula ℕ → Modal.Formula ℕ)
    (hcond : ∀ cl, Modalized p (cond cl (.atom p))) (d : Modal.Formula ℕ)
    (hd : Modalized p d) (l : List Clause) :
    Modalized p (ruleWith cond d l (.atom p)) := by
  induction l with
  | nil => simpa [ruleWith]
  | cons cl rest ih =>
    simp only [ruleWith]
    simp [Modalized, hcond, ih, modalized_act]

/-- The rule of record is modalized in its diagonal atom, so FAF's fixed-point theorem applies.
Source: [[dp-troll-bridge-mandate]] §"The modal idealization" ("`Modalized p (rule σ p)` holds")
Kind: L
Fidelity: exact
Hyps: (a) none -/
lemma modalized_rule (l : List Clause) (p : ℕ) : Modalized p (rule l (.atom p)) :=
  modalized_ruleWith Clause.cond (fun cl => modalized_cond cl p) ⊥ trivial l

/-- Substituting `χ` for the diagonal atom in a raw condition gives the condition at `χ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma subst_cond (cl : Clause) (p : ℕ) (χ : Modal.Formula ℕ) :
    (cl.cond (.atom p))⟦diag p χ⟧ = cl.cond χ := by
  rcases cl with ⟨a, u⟩
  cases a <;> cases u <;> simp [Clause.cond, Act.sentence, Util.sentence, diag]

/-- Clause outputs are closed, so substitution leaves them unchanged.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma subst_act (cl : Clause) (p : ℕ) (χ : Modal.Formula ℕ) :
    (cl.act)⟦diag p χ⟧ = cl.act := by
  rcases cl with ⟨a, u⟩
  cases a <;> rfl

/-- Substitution commutes with the nested-`if` rule when it commutes with the conditions and
fixes the default.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma subst_ruleWith {p : ℕ} {χ : Modal.Formula ℕ}
    (cond : Clause → Modal.Formula ℕ → Modal.Formula ℕ)
    (hc : ∀ cl, (cond cl (.atom p))⟦diag p χ⟧ = cond cl χ) (d : Modal.Formula ℕ)
    (hd : d⟦diag p χ⟧ = d) (l : List Clause) :
    (ruleWith cond d l (.atom p))⟦diag p χ⟧ = ruleWith cond d l χ := by
  induction l with
  | nil => simpa [ruleWith]
  | cons cl rest ih =>
    simp only [ruleWith]
    simp [hc, subst_act, ih]

/-- `(rule l p)⟦p ↦ χ⟧ = rule l χ`: the fixed-point equation of FAF's theorem is the
`IsAgent` equation.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma rule_subst (l : List Clause) (p : ℕ) (χ : Modal.Formula ℕ) :
    (rule l (.atom p))⟦diag p χ⟧ = rule l χ :=
  subst_ruleWith Clause.cond (fun cl => subst_cond cl p χ) ⊥ rfl l

/-- Every ordering has an agent: a GL fixed point of its rule exists (de Jongh–Sambin via
FAF's `glFixedPoint_thm42`).
Source: [[dp-troll-bridge-mandate]] §"The modal idealization"; FAF `ModalAgents/FixedPoint.lean` Thm 4.2
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem agent_exists (l : List Clause) : ∃ χ, IsAgent l χ := by
  obtain ⟨ψ, hψ, -⟩ := glFixedPoint_thm42 (modalized_rule l 0)
  refine ⟨ψ, ?_⟩
  unfold IsAgent
  rw [← rule_subst l 0 ψ]
  exact hψ

/-- Any two agents of the same ordering are GL-equivalent (uniqueness of modal fixed points,
FAF's `glFixedPoint_uniqueness`).
Source: [[dp-troll-bridge-mandate]] §"The modal idealization"; FAF `ModalAgents/FixedPoint.lean` Thm 4.3
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem agent_unique {l : List Clause} {χ χ' : Modal.Formula ℕ}
    (h : IsAgent l χ) (h' : IsAgent l χ') : Modal.GL ⊢ χ 🡘 χ' :=
  glFixedPoint_uniqueness (modalized_rule l 0)
    (by rw [rule_subst]; exact h) (by rw [rule_subst]; exact h')

end Cleanroom.Decision.DpTrollBridge
