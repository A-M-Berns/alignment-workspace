import Cleanroom.Decision.DpReferentsCdt.Defs

/-!
# Everitt–Leike–Hutter's sequential environment as a finite tree (T8)

The paper's finite-horizon environment with hidden state, rendered as a `dp-core-tree` tree: a
chance root draws the hidden state `s ∈ Fin ns`, then `m` rounds of a decision node at the point
`æ_{<t}` (the history, a `List (A × Fin ne)`) followed by a chance node drawing the percept
`e_t ∼ μ(· ∣ s, æ_{<t} a_t)`; the leaf-world is `(s, æ_{1:m})`, the payoff `∑_t u(e_t)`. Each history
is one node, so the tree is almost fair by construction; Definition 6 is the paper's independent
action draw — **with the disclosed variant** that the paper's action likelihood
`μ(a_t ∣ s, æ_{<t})` (its equation (2)) may depend on the hidden state, while a Definition-6 tree
draws the act from `C(æ_{<t})` independently of `s` (findings F13).

Definitions of record: the prefix mass `massPrefix C B p` (the run law of the trajectories with
prefix `p`); **SAEDT**'s belief `saedtBelief` (condition on the next action: the prefix
`æ_{<t} a_t e_t` over `æ_{<t} a_t`); **SPEDT**'s `spedtBelief` (condition moreover on the run event
"every later draw agrees with `π`"); **SCDT**'s `scdtBelief` (the deviation `C[d' ↦ π(d')]` at every
future point, conditioned on reaching `æ_{<t}`) — `do` is `dp-core-tree`'s deviation, not a new
primitive — and the one-step forcing `scdt1Belief` (the deviation at the point `æ_{<t}` alone).

Theorems: the recursion and boundary lemmas of `massPrefix` on the subtrees, the **congruence**
`massPrefix_congr` (the prefix mass depends on `C` only at the proper prefixes of `p`),
**Proposition 7** (`scdtBelief_eq_scdt1Belief`: the whole-future intervention and the single-act
intervention give the same next-percept belief — the percept's chance node sits between the
current decision and every later one), the **one-step coincidence** (`spedtBelief_eq_saedtBelief_last`:
at the last round the future-policy event is trivial), and **Proposition 10** (`massPrefix_eq_sum_state`,
`condChain_state`: the beliefs expand over the hidden state by the conditional chain rule).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

/-! ## The environment and its tree -/

section elh

variable {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] {ns ne : ℕ}

/-- Histories `æ_{<t}`: lists of (action, percept) pairs. Source: EL&H §3.1 ("`æ_{<t} ∈ (A × E)*`").
Kind: D -/
abbrev Hist (A : Type) (ne : ℕ) : Type := List (A × Fin ne)

/-- Leaf-worlds `(s, æ_{1:m})`: the hidden state and the full trajectory.
Source: EL&H §3.1 (the hidden state `s`, the history); mandate T8
Kind: D -/
abbrev ElhW (A : Type) (ns ne : ℕ) : Type := Fin ns × Hist A ne

/-- An environment model: a prior on the hidden state, the percept law `μ(e_t ∣ s, æ_{<t} a_t)`, and
the utility of a percept. The action likelihood `μ(a_t ∣ s, æ_{<t})` of the paper's equation (2) is
**not** a parameter: the tree draws `a_t ∼ C(æ_{<t})`, independently of `s` (findings F13).
Source: EL&H §3.1 equation (2), §3.2 (lifetime `m`, `u`)
Kind: D
Fidelity: variant: `s`-independent action likelihood (Definition 6's independent draw) -/
structure ElhEnv (A : Type) (ns ne : ℕ) where
  /-- The prior `μ(s)` on the hidden state. -/
  ρ : FinDistr ℚ (Fin ns)
  /-- The percept law `μ(e ∣ s, æ_{<t} a_t)`. -/
  μ : Fin ns → Hist A ne → A → FinDistr ℚ (Fin ne)
  /-- The utility of a percept. -/
  u : Fin ne → ℚ

/-- The utility of a trajectory, `∑_t u(e_t)`. Source: EL&H §3.2. Kind: D -/
def histUtil (u : Fin ne → ℚ) (h : Hist A ne) : ℚ := (h.map fun x => u x.2).sum

/-- The subtree after state `s` and history `h` with `n` rounds to go: a decision node at the point
`h`, then a chance node drawing the percept, then the subtree at `h ++ [(a, e)]`.
Source: EL&H §3.1–3.2 (the finite-horizon interaction); mandate T8
Kind: D
Fidelity: variant: finite-tree rendering; hidden state as a chance root (below) -/
def elhSub (E : ElhEnv A ns ne) (s : Fin ns) :
    ℕ → Hist A ne → Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ
  | 0, h => .leaf (s, h) (histUtil E.u h)
  | n + 1, h => .decision h fun a => .chance ne (E.μ s h a) fun e => elhSub E s n (h ++ [(a, e)])

/-- **The EL&H tree** with lifetime `m`: a chance root draws the hidden state, then `elhSub`.
Source: EL&H §3.1 (Figure 3: the hidden state is drawn first); mandate T8
Kind: D
Fidelity: variant: finite-tree rendering of EL&H's environment; hidden state as a chance root;
`s`-independent action likelihood -/
def elhTree (E : ElhEnv A ns ne) (m : ℕ) : Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ :=
  .chance ns E.ρ fun s => elhSub E s m []

/-- The leaves with trajectory prefix `p`. Source: EL&H §3.3 (the events `æ_{<t} a_t`). Kind: D -/
noncomputable def prefixEv (B : Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ) (p : Hist A ne) :
    Finset B.Leaves := by
  classical exact Finset.univ.filter fun ℓ => p <+: (world B ℓ).2

/-- **The prefix mass** `μ_{B,C}{æ_{1:m} has prefix p}`. Source: EL&H §3.3 (`μ(æ_{<t} a_t)`). Kind: D -/
noncomputable def massPrefix (C : Proc (Hist A ne) (fun _ => A) ℚ)
    (B : Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ) (p : Hist A ne) : ℚ :=
  mass C B (prefixEv B p)

/-- The prefix mass as an indicator sum. Source: none: infrastructure. Kind: L -/
theorem massPrefix_eq_sum (C : Proc (Hist A ne) (fun _ => A) ℚ)
    (B : Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ) (p : Hist A ne) :
    massPrefix C B p = ∑ ℓ, if p <+: (world B ℓ).2 then leafLaw C B ℓ else 0 := by
  unfold massPrefix prefixEv mass
  rw [Finset.sum_filter]

variable (E : ElhEnv A ns ne) (s : Fin ns) (C : Proc (Hist A ne) (fun _ => A) ℚ)

/-- The world of a leaf of `elhSub E s n h` has state `s` and a trajectory extending `h`.
Source: none: infrastructure. Kind: L -/
theorem elhSub_world :
    (n : ℕ) → ∀ (h : Hist A ne) (ℓ : (elhSub E s n h).Leaves),
      (world (elhSub E s n h) ℓ).1 = s ∧ h <+: (world (elhSub E s n h) ℓ).2 ∧
        ((world (elhSub E s n h) ℓ).2).length = h.length + n
  | 0, h, _ => ⟨rfl, List.prefix_refl h, by simp [elhSub, world]⟩
  | n + 1, h, ⟨a, e, ℓ⟩ => by
      obtain ⟨h1, h2, h3⟩ := elhSub_world n (h ++ [(a, e)]) ℓ
      refine ⟨h1, (List.prefix_append h [(a, e)]).trans h2, ?_⟩
      show ((world (elhSub E s n (h ++ [(a, e)])) ℓ).2).length = h.length + (n + 1)
      rw [h3]; simp; ring

/-- **The recursion of the prefix mass on a subtree**: at `h` with `n + 1` rounds to go,
`massPrefix (elhSub s (n+1) h) p = ∑_a C(h)(a) ∑_e μ(e ∣ s, h, a) · massPrefix (elhSub s n (h ++ [(a,e)])) p`.
Source: EL&H equation (2) (the factorisation of `μ(s, æ_{<t})`); mandate T8
Kind: P -/
theorem massPrefix_elhSub_succ (n : ℕ) (h : Hist A ne) (p : Hist A ne) :
    massPrefix C (elhSub E s (n + 1) h) p =
      ∑ a, (C h).w a * ∑ e, (E.μ s h a).w e * massPrefix C (elhSub E s n (h ++ [(a, e)])) p := by
  unfold massPrefix prefixEv mass
  simp only [Finset.sum_filter]
  show (∑ ℓ : (Tree.decision h fun a => Tree.chance ne (E.μ s h a) fun e =>
      elhSub E s n (h ++ [(a, e)])).Leaves,
      if p <+: (world (Tree.decision h fun a => Tree.chance ne (E.μ s h a) fun e =>
        elhSub E s n (h ++ [(a, e)])) ℓ).2 then
        leafLaw C (Tree.decision h fun a => Tree.chance ne (E.μ s h a) fun e =>
          elhSub E s n (h ++ [(a, e)])) ℓ else 0) = _
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_leaves_chance, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [leafLaw_decision, leafLaw_chance, world_decision, world_chance]
  split_ifs <;> ring

/-- At the leaf (`n = 0`) the prefix mass is the indicator `[p <+: h]`. Source: none: infrastructure.
Kind: L -/
theorem massPrefix_elhSub_zero (h p : Hist A ne) :
    massPrefix C (elhSub E s 0 h) p = if p <+: h then 1 else 0 := by
  unfold massPrefix prefixEv mass
  rw [Finset.sum_filter]
  show (∑ ℓ : (Tree.leaf (s, h) (histUtil E.u h) : Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ).Leaves,
    if p <+: (world (Tree.leaf (s, h) (histUtil E.u h) :
      Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ) ℓ).2 then
      leafLaw C (Tree.leaf (s, h) (histUtil E.u h) :
        Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ) ℓ else 0) = _
  rw [Tree.sum_leaves_leaf]
  simp [world, leafLaw]

/-- If `p` is a prefix of the current history, the whole subtree has prefix `p`: mass `1`.
Source: none: infrastructure. Kind: L -/
theorem massPrefix_elhSub_of_prefix :
    (n : ℕ) → ∀ (h p : Hist A ne), p <+: h → massPrefix C (elhSub E s n h) p = 1
  | 0, h, p, hp => by rw [massPrefix_elhSub_zero, if_pos hp]
  | n + 1, h, p, hp => by
      rw [massPrefix_elhSub_succ]
      have : ∀ a e, massPrefix C (elhSub E s n (h ++ [(a, e)])) p = 1 := fun a e =>
        massPrefix_elhSub_of_prefix n _ p (hp.trans (List.prefix_append h [(a, e)]))
      simp only [this, mul_one, (E.μ s h _).sum_one, (C h).sum_one]

/-- If `p` and the current history are incomparable, no leaf has prefix `p`: mass `0`.
Source: none: infrastructure. Kind: L -/
theorem massPrefix_elhSub_of_incomparable :
    (n : ℕ) → ∀ (h p : Hist A ne), ¬ p <+: h → ¬ h <+: p → massPrefix C (elhSub E s n h) p = 0
  | 0, h, p, hp, _ => by rw [massPrefix_elhSub_zero, if_neg hp]
  | n + 1, h, p, hp, hh => by
      rw [massPrefix_elhSub_succ]
      have : ∀ a e, massPrefix C (elhSub E s n (h ++ [(a, e)])) p = 0 := by
        intro a e
        apply massPrefix_elhSub_of_incomparable n
        · intro hpe
          by_cases hlen : p.length ≤ h.length
          · exact hp (List.prefix_of_prefix_length_le hpe (List.prefix_append h [(a, e)]) hlen)
          · have hlen' : (h ++ [(a, e)]).length ≤ p.length := by
              simp; omega
            have := hpe.eq_of_length_le hlen'
            exact hh (this ▸ List.prefix_append h [(a, e)])
        · intro hhe
          exact hh ((List.prefix_append h [(a, e)]).trans hhe)
      simp only [this, mul_zero, Finset.sum_const_zero]

/-- **The congruence**: the prefix mass of `p` depends on the procedure only at the proper prefixes
of `p` (the histories at which a draw lies on every `p`-run before `p` is complete).
Source: EL&H Proposition 7's proof idea ("we do not get any extra evidence from the future
interventions"); mandate T8
Kind: P
Fidelity: exact -/
theorem massPrefix_congr {C C' : Proc (Hist A ne) (fun _ => A) ℚ} {p : Hist A ne}
    (hCC : ∀ h', h' <+: p → h' ≠ p → C h' = C' h') :
    (n : ℕ) → ∀ h : Hist A ne, massPrefix C (elhSub E s n h) p = massPrefix C' (elhSub E s n h) p
  | 0, h => by rw [massPrefix_elhSub_zero, massPrefix_elhSub_zero]
  | n + 1, h => by
      by_cases hph : p <+: h
      · rw [massPrefix_elhSub_of_prefix E s C _ h p hph,
          massPrefix_elhSub_of_prefix E s C' _ h p hph]
      · by_cases hhp : h <+: p
        · have hne : h ≠ p := fun e => hph (e ▸ List.prefix_refl p)
          rw [massPrefix_elhSub_succ, massPrefix_elhSub_succ, hCC h hhp hne]
          refine Finset.sum_congr rfl fun a _ => ?_
          congr 1
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [massPrefix_congr hCC n (h ++ [(a, e)])]
        · rw [massPrefix_elhSub_of_incomparable E s C _ h p hph hhp,
            massPrefix_elhSub_of_incomparable E s C' _ h p hph hhp]

/-- The prefix mass on the whole tree is the prior average of the subtree masses.
Source: EL&H equation (2) (`μ(s, æ_{<t}) = μ(s) ∏ …`); mandate T8
Kind: P -/
theorem massPrefix_elhTree (m : ℕ) (p : Hist A ne) :
    massPrefix C (elhTree E m) p = ∑ s, E.ρ.w s * massPrefix C (elhSub E s m []) p := by
  simp only [massPrefix_eq_sum]
  unfold elhTree
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [leafLaw_chance, world_chance]
  split_ifs <;> ring

/-- The congruence on the whole tree. Source: mandate T8. Kind: C -/
theorem massPrefix_elhTree_congr {C C' : Proc (Hist A ne) (fun _ => A) ℚ} {p : Hist A ne}
    (hCC : ∀ h', h' <+: p → h' ≠ p → C h' = C' h') (m : ℕ) :
    massPrefix C (elhTree E m) p = massPrefix C' (elhTree E m) p := by
  rw [massPrefix_elhTree, massPrefix_elhTree]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [massPrefix_congr E s hCC m []]

/-! ## The three beliefs and Proposition 7 -/

variable (m : ℕ)

/-- **SAEDT's next-percept belief** `μ(e_t ∣ æ_{<t} a_t)`: the prefix `æ_{<t} a_t e_t` over the
prefix `æ_{<t} a_t` (junk `0` at a null denominator). Under Definition 6 it is the draw event's
conditional at the history node (`dp-local-opt`'s `condDraw_eq_forced`: forcing there).
Source: EL&H Definition 3 (SAEDT); mandate T8
Kind: D
Fidelity: variant: finite-tree rendering -/
noncomputable def saedtBelief (h : Hist A ne) (a : A) (e : Fin ne) : ℚ :=
  massPrefix C (elhTree E m) (h ++ [(a, e)]) / ∑ e', massPrefix C (elhTree E m) (h ++ [(a, e')])

/-- The causal intervention `do(π_{t:m})`: the deviation `C[d' ↦ π(d')]` at every history of length
`≥ t` (every future point), `C` elsewhere — `dp-core-tree`'s deviation, not a new primitive.
Source: EL&H equation (5) (`do(a_t := π(æ_{<t}), …, a_m := π(æ_{<m}))`); mandate T8
Kind: D -/
def doProc (π : Hist A ne → A) (t : ℕ) : Proc (Hist A ne) (fun _ => A) ℚ :=
  fun h' => if t ≤ h'.length then FinDistr.pure (π h') else C h'

/-- **SCDT's next-percept belief with the whole future policy intervened**,
`μ(e_t ∣ æ_{<t}, do(π_{t:m}))`: the prefix `æ_{<t} π(æ_{<t}) e_t` over the prefix `æ_{<t}` under
`doProc C π t`.
Source: EL&H Definition 6 and equation (5); mandate T8
Kind: D
Fidelity: variant: finite-tree rendering -/
noncomputable def scdtBelief (π : Hist A ne → A) (h : Hist A ne) (e : Fin ne) : ℚ :=
  massPrefix (doProc C π h.length) (elhTree E m) (h ++ [(π h, e)]) /
    massPrefix (doProc C π h.length) (elhTree E m) h

/-- **SCDT's belief with only `a_t = π(æ_{<t})` intervened**: the single-point deviation
`C[æ_{<t} ↦ π(æ_{<t})]`, i.e. forcing at the history node.
Source: EL&H Definition 6 (`μ(e_t ∣ æ_{<t}, do(a_t))`); mandate T8
Kind: D -/
noncomputable def scdt1Belief (π : Hist A ne → A) (h : Hist A ne) (e : Fin ne) : ℚ :=
  massPrefix (C.deviatePure h (π h)) (elhTree E m) (h ++ [(π h, e)]) /
    massPrefix (C.deviatePure h (π h)) (elhTree E m) h

/-- **Proposition 7 (Policy-Causal = Action-Causal)**: `μ(e_t ∣ æ_{<t}, do(π_{t:m})) = μ(e_t ∣ æ_{<t},
do(π(æ_{<t})))` — the whole-future deviation and the one-point deviation agree on every proper prefix
of `æ_{<t} π(æ_{<t}) e_t` and of `æ_{<t}`, so both prefix masses coincide: the percept's chance node
sits between the current decision and every later one, and the future interventions carry no
evidence.
Source: EL&H Proposition 7 (line 511); mandate T8
Kind: P
Fidelity: variant: finite-tree rendering with `do` as `dp-core-tree`'s deviation
Hyps: (a) none -/
theorem scdtBelief_eq_scdt1Belief (π : Hist A ne → A) (h : Hist A ne) (e : Fin ne) :
    scdtBelief E C m π h e = scdt1Belief E C m π h e := by
  unfold scdtBelief scdt1Belief
  have hnum : ∀ h', h' <+: h ++ [(π h, e)] → h' ≠ h ++ [(π h, e)] →
      doProc C π h.length h' = C.deviatePure h (π h) h' := by
    intro h' hp hne
    have hlen : h'.length ≤ h.length := by
      have := hp.length_le
      simp at this
      by_contra hc
      exact hne (hp.eq_of_length_le (by simp; omega))
    by_cases hh : h' = h
    · subst hh
      simp [doProc, Proc.deviatePure, Proc.deviate_same]
    · have hlt : h'.length < h.length := by
        rcases lt_or_eq_of_le hlen with hlt | heq
        · exact hlt
        · exact absurd (List.prefix_of_prefix_length_le hp (List.prefix_append h _) hlen
            |>.eq_of_length heq) hh
      simp [doProc, not_le.mpr hlt, Proc.deviatePure, Proc.deviate_ne C _ hh]
  have hden : ∀ h', h' <+: h → h' ≠ h → doProc C π h.length h' = C.deviatePure h (π h) h' := by
    intro h' hp hne
    have hlt : h'.length < h.length := by
      rcases lt_or_eq_of_le hp.length_le with hlt | heq
      · exact hlt
      · exact absurd (hp.eq_of_length heq) hne
    simp [doProc, not_le.mpr hlt, Proc.deviatePure, Proc.deviate_ne C _ hne]
  rw [massPrefix_elhTree_congr E hnum m, massPrefix_elhTree_congr E hden m]

/-! ## SPEDT and the one-step coincidence -/

/-- The trajectory `t` follows the policy `π` at every position `≥ k`: `a_i = π(æ_{<i})` for `i ≥ k`.
Source: EL&H equation (4) (`Π_{t:m} := {æ_{1:∞} ∣ ∀ t ≤ i ≤ m, π(æ_{<i}) = a_i}`); mandate T8
Kind: D -/
def Follows (π : Hist A ne → A) (k : ℕ) (t : Hist A ne) : Prop :=
  ∀ i (hi : i < t.length), k ≤ i → (t.get ⟨i, hi⟩).1 = π (t.take i)

/-- The leaves whose trajectory follows `π` from position `k` on. Source: EL&H equation (4). Kind: D -/
noncomputable def followsEv (π : Hist A ne → A) (k : ℕ)
    (B : Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ) : Finset B.Leaves := by
  classical exact Finset.univ.filter fun ℓ => Follows π k (world B ℓ).2

/-- **SPEDT's next-percept belief** `μ(e_t ∣ æ_{<t} a_t, π_{t+1:m})`: the prefix `æ_{<t} a_t e_t` over
the prefix `æ_{<t} a_t`, both intersected with the future-policy event from position `t + 1`
(positions are `0`-based: the history `h` has length `t − 1`, so the next action sits at position
`h.length` and the future policy constrains positions `≥ h.length + 1`).
Source: EL&H Definition 4 (SPEDT), equation (4); mandate T8
Kind: D
Fidelity: variant: finite-tree rendering -/
noncomputable def spedtBelief (π : Hist A ne → A) (h : Hist A ne) (a : A) (e : Fin ne) : ℚ :=
  mass C (elhTree E m) (prefixEv _ (h ++ [(a, e)]) ∩ followsEv π (h.length + 1) _) /
    mass C (elhTree E m)
      ((Finset.univ.biUnion fun e' => prefixEv _ (h ++ [(a, e')])) ∩ followsEv π (h.length + 1) _)

/-- Every trajectory of the lifetime-`m` tree has length `m`. Source: none: infrastructure. Kind: L -/
theorem elhTree_world_length (ℓ : (elhTree E m).Leaves) : ((world (elhTree E m) ℓ).2).length = m := by
  rcases ℓ with ⟨s, ℓ⟩
  have := (elhSub_world E s m [] ℓ).2.2
  simpa [elhTree, world_chance] using this

/-- **The one-step coincidence**: at the last round (`h.length + 1 ≥ m`), the future-policy event is
every trajectory, so SPEDT's and SAEDT's beliefs coincide.
Source: EL&H line 419 ("For one-step decisions (`m = t + 1`), SAEDT and SPEDT coincide"; with the
paper's `1`-based `t` and `h.length = t − 1` this is `h.length + 1 ≥ m`); mandate T8
Kind: P
Fidelity: exact (the paper's sentence read as "no later draw"; findings F13) -/
theorem spedtBelief_eq_saedtBelief_last (π : Hist A ne → A) (h : Hist A ne) (a : A) (e : Fin ne)
    (hlast : m ≤ h.length + 1) :
    spedtBelief E C m π h a e = saedtBelief E C m h a e := by
  classical
  have hall : followsEv π (h.length + 1) (elhTree E m) = Finset.univ := by
    unfold followsEv
    have hF : ∀ ℓ : (elhTree E m).Leaves, Follows π (h.length + 1) (world (elhTree E m) ℓ).2 := by
      intro ℓ i hi hk
      rw [elhTree_world_length] at hi
      omega
    exact Finset.filter_true_of_mem fun ℓ _ => hF ℓ
  unfold spedtBelief saedtBelief massPrefix
  rw [hall, Finset.inter_univ, Finset.inter_univ]
  congr 1
  unfold mass
  rw [Finset.sum_biUnion]
  intro e₁ _ e₂ _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro ℓ h₁ h₂
  unfold prefixEv at h₁ h₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
  have := List.prefix_of_prefix_length_le h₁ h₂ (by simp)
  have := this.eq_of_length (by simp)
  simp at this
  exact hne this

/-! ## Proposition 10: expansion over the hidden state -/

/-- The leaves with hidden state `s`. Source: EL&H Proposition 10 (the sum over `s ∈ S`). Kind: D -/
noncomputable def stateEv (B : Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ) (s : Fin ns) :
    Finset B.Leaves := by
  classical exact Finset.univ.filter fun ℓ => (world B ℓ).1 = s

/-- Every event partitions over the hidden state: `mass X = ∑_s mass (X ∩ {state = s})`.
Source: EL&H Proposition 10 (equations (6)–(8): "`∑_{s ∈ S}`"); mandate T8
Kind: P -/
theorem mass_eq_sum_state (B : Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ)
    (X : Finset B.Leaves) : mass C B X = ∑ s, mass C B (X ∩ stateEv B s) := by
  classical
  unfold mass stateEv
  simp only [Finset.inter_filter, Finset.inter_univ, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp

/-- **The conditional chain rule over the hidden state** (Proposition 10's equations (6)–(8) in
one form): for any events `X` (the conditioning event) and `Y` (the percept event) with `mass X > 0`,
`μ(Y ∣ X) = ∑_s μ(s ∣ X) · μ(Y ∣ s, X)`, where a state of null mass under `X` contributes `0` on both
sides (Lean's `x / 0 = 0` agrees with the paper's convention of omitting null terms).
Source: EL&H Proposition 10 (equations (6)–(8)); mandate T8
Kind: P
Fidelity: exact (the three instances (6), (7), (8) are the three choices of `X`: the next-action
prefix, the future-policy event, the intervened prefix)
Hyps: (a) `0 < mass X` -/
theorem condChain_state (B : Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ) (X Y : Finset B.Leaves)
    (hX : 0 < mass C B X) :
    mass C B (Y ∩ X) / mass C B X =
      ∑ s, (mass C B (X ∩ stateEv B s) / mass C B X) *
        (mass C B (Y ∩ X ∩ stateEv B s) / mass C B (X ∩ stateEv B s)) := by
  rw [mass_eq_sum_state C B (Y ∩ X), Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases (mass_nonneg C B (X ∩ stateEv B s)).lt_or_eq with hs | hs
  · field_simp
  · have hYs : mass C B (Y ∩ X ∩ stateEv B s) = 0 := by
      apply le_antisymm _ (mass_nonneg C B _)
      rw [hs]
      exact mass_mono C B (Finset.inter_subset_inter Finset.inter_subset_right (Finset.Subset.refl _))
    rw [hYs, ← hs]
    simp

end elh

end Cleanroom.Decision.DpReferentsCdt
