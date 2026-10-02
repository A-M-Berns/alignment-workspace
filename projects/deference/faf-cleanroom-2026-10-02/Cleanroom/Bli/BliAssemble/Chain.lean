import Cleanroom.Bli.BliAssemble.Defs

/-!
# `bli-assemble` · Chain: the chain bridge (target 2)

The three facts that make `chainExpr` denote the Tier-A price:

* `chainProbH_singleton_eq_lastMarg` — (a): the forward chain probability of a one-entry chain
  `[(m, q)]` from day `n` over the horizon to `m` is `bli-superbelief`'s `lastMarg` at the decoded
  table. Through `chainProbH_eq_trajMass`: both are `trajLaw` sums over `trajGrid`, the chain
  event of a single entry is "the last table codes to `q`", which under `StateCoding.inj` is
  "the last table is `decode m q`".
* `chainProbH_restart` — (b), the restart identity at the chain's earliest day: for a consistent
  chain whose earliest entry `(m, q)` has a candidate code, the forward probability over
  `(m − n) + K` days factors as the one-entry probability of `(m, q)` times the probability of
  the whole chain restarted at day `m` from the **known** table `decode m q`. Induction on
  `m − n − 1` through the defining recursion (`chainProbH_succ`), the day-`n+1` condition being
  vacuous until the earliest day, where `inj` and consistency pin the day-`m` table.
* `denoteRat_chainExpr` — (c): for every rational history `V` and every parse `tierA` accepts,
  `chainExpr`'s exact rational denotation at `V` is `tierAPrice` from the day-`n` actual table of
  `V`. Composition of (a), (b) and `tentExpr_denoteRat`.

The bridge is proved for **every** Tier-A parse — chains of any length, with or without a small
part — not only for single state atoms (mandate trap). `Map.lean` audits it on a two-atom chain
with a small part.

Sources: [[bli-program]] §2.5, §3.4; mandate target 2.
-/

namespace Cleanroom.Bli.BliAssemble

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliTransfer Cleanroom.Bli.BliSuperbelief

open Classical

noncomputable section

variable {𝓜 : Mesh} (c : StateCoding 𝓜) (sk : Skeleton smallIndex 𝓜.d)

/-! ## Coding lemmas -/

/-- A candidate code is the code of its decoding.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma code_decode {m q : ℕ} (hq : q ∈ c.states m) : c.code m (c.decode m q) = q := by
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hq
  rw [c.decode_code hQ]

/-- On the grid, "codes to `q`" is "is the decoding of `q`".
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma code_eq_iff_eq_decode {m q : ℕ} (hq : q ∈ c.states m) {Q : Table smallIndex m}
    (hQ : Q ∈ grid smallIndex 𝓜.d m) : c.code m Q = q ↔ Q = c.decode m q := by
  constructor
  · intro h; rw [← h, c.decode_code hQ]
  · intro h; rw [h, code_decode c hq]

/-! ## (a) One entry: the chain probability is the last-day marginal -/

/-- **Bridge (a).** The forward chain probability of the one-entry chain `[(m, q)]` from the
day-`n` table `t` over `h + 1` days, where `m = n + h + 1` and `q` is a candidate code, is the
last-day marginal `lastMarg sk n (h+1) t (decode m q)` — `bli-superbelief`'s
`𝐏_n(𝐐_m = decode m q)`. Both sides are `trajLaw` sums over `trajGrid` (`chainProbH_eq_trajMass`);
the chain event of a single entry says the day-`m` table codes to `q` (`Traj.day_last`), which
under `StateCoding.inj` is "the last table is `decode m q`" (`code_eq_iff_eq_decode`).
Source: mandate target 2(a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem chainProbH_singleton_eq_lastMarg (h n m : ℕ) (hm : m = n + h + 1) {q : ℕ}
    (hq : q ∈ c.states m) (t : Table smallIndex n) :
    chainProbH sk c [(m, q)] n t (h + 1) = lastMarg sk n (h + 1) t (c.decode (n + h + 1) q) := by
  subst hm
  rw [chainProbH_eq_trajMass]
  unfold trajMass lastMarg
  rw [sum_trajGrid_succ, sum_trajGrid_succ]
  refine Finset.sum_congr rfl fun τ' _ => Finset.sum_congr rfl fun Q hQ => ?_
  have hev : ChainEvent c n [(n + h + 1, q)] (show Traj smallIndex n (h + 1) from (τ', Q)) ↔
      Q = c.decode (n + h + 1) q := by
    unfold ChainEvent
    constructor
    · intro hE
      have := hE (n + h + 1, q) (List.mem_singleton_self _) (by omega) (by omega)
      rw [Traj.day_last] at this
      exact (code_eq_iff_eq_decode c hq hQ).mp this
    · intro hQd x hx h1 h2
      rw [List.mem_singleton] at hx
      subst hx
      rw [Traj.day_last]
      exact (code_eq_iff_eq_decode c hq hQ).mpr hQd
  simp only [Traj.last_succ]
  by_cases hE : ChainEvent c n [(n + h + 1, q)] (show Traj smallIndex n (h + 1) from (τ', Q))
  · rw [if_pos hE, if_pos (hev.mp hE), mul_one]
  · rw [if_neg hE, if_neg (fun h' => hE (hev.mpr h')), mul_zero]

/-! ## (b) The restart identity at the chain's earliest day -/

/-- **Bridge (b), the restart identity.** For a consistent chain `l` whose earliest entry is
`(m, q)` with `q` a candidate code (`m = n + 1 + h`), the forward probability from the day-`n`
table `t` over `h + 1 + K` days is the one-entry probability of `(m, q)` over `h + 1` days times
the probability of the **whole chain restarted at day `m` from the known table `decode m q`**
over `K` days. Induction on `h`: until day `m` the recursion's day-`(n+1)` condition is vacuous
(every entry is at or after `m`), and on day `m` the condition "codes to `q` on every day-`m`
entry" holds exactly at `decode m q` (consistency and `inj`), collapsing the sum.
Source: bli-soto-a-035 (chain rule); mandate target 2(b)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem chainProbH_restart {l : List (ℕ × ℕ)} (hcons : Consistent l) {m q : ℕ}
    (hmem : (m, q) ∈ l) (hmin : ∀ x ∈ l, m ≤ x.1) (hq : q ∈ c.states m) (K : ℕ) :
    ∀ (h n : ℕ), m = n + 1 + h → ∀ t : Table smallIndex n,
      chainProbH sk c l n t (h + 1 + K) =
        chainProbH sk c [(m, q)] n t (h + 1) * chainProbH sk c l m (c.decode m q) K := by
  intro h
  induction h with
  | zero =>
      intro n hm t
      obtain rfl : m = n + 1 := by omega
      set A := c.decode (n + 1) q with hA
      have hAg : A ∈ grid smallIndex 𝓜.d (n + 1) := c.decode_mem_grid hq
      have hcode : c.code (n + 1) A = q := code_decode c hq
      have hsing : chainProbH sk c [(n + 1, q)] n t (0 + 1) = (sk.κ n).law t A := by
        have := chainProbH_singleton_code c sk hAg t 0
        rwa [hcode] at this
      rw [hsing, show 0 + 1 + K = K + 1 by omega, chainProbH_succ]
      have key : ∀ B ∈ grid smallIndex 𝓜.d (n + 1),
          (sk.κ n).law t B *
            (if ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) B = x.2
              then chainProbH sk c l (n + 1) B K else 0)
          = if B = A then (sk.κ n).law t A * chainProbH sk c l (n + 1) A K else 0 := by
        intro B hB
        by_cases hc : ∀ x ∈ l, x.1 = n + 1 → c.code (n + 1) B = x.2
        · have hBq : c.code (n + 1) B = q := hc (n + 1, q) hmem rfl
          have hBA : B = A := (code_eq_iff_eq_decode c hq hB).mp hBq
          rw [if_pos hc, if_pos hBA, hBA]
        · have hBA : B ≠ A := by
            intro hBA
            apply hc
            intro x hx h1
            rw [hBA, hcode]
            exact (hcons x hx (n + 1, q) hmem h1).symm
          rw [if_neg hc, if_neg hBA, mul_zero]
      rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (grid smallIndex 𝓜.d (n + 1)) A, if_pos hAg]
  | succ h ih =>
      intro n hm t
      have hvac : ∀ (l' : List (ℕ × ℕ)), (∀ x ∈ l', m ≤ x.1) →
          ∀ B : Table smallIndex (n + 1),
            (∀ x ∈ l', x.1 = n + 1 → c.code (n + 1) B = x.2) := by
        intro l' hl' B x hx h1
        have := hl' x hx
        omega
      have hmin' : ∀ x ∈ [(m, q)], m ≤ x.1 := by
        intro x hx; rw [List.mem_singleton] at hx; subst hx; exact le_rfl
      rw [show h + 1 + 1 + K = (h + 1 + K) + 1 by omega, chainProbH_succ c sk l,
        chainProbH_succ c sk [(m, q)], Finset.sum_mul]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [if_pos (hvac l hmin B), if_pos (hvac [(m, q)] hmin' B),
        ih (n + 1) (by omega) B]
      ring

/-! ## (c) The chain expression denotes the Tier-A price -/

/-- Denotation of a product.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma denoteRat_mul (a b : EF) (V : ℕ → Sentence → ℚ) :
    (EF.mul a b).denoteRat V = a.denoteRat V * b.denoteRat V := rfl

/-- Denotation of a constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma denoteRat_const (q : ℚ) (V : ℕ → Sentence → ℚ) : (EF.const q).denoteRat V = q := rfl

/-- **Bridge (c).** For every rational history `V` and every parse `(l, s)` that `tierA` returns
at day `n`, the exact rational denotation of `chainExpr 𝓜 c n (l, s)` at `V` is the Tier-A price
`tierAPrice (tentSkeleton smallIndex 𝓜) c n (actualTable smallIndex V n) (l, s)`. Consistent
chain: `tentExpr_denoteRat` gives the earliest entry's marginal, (a) identifies it with the
one-entry chain probability, (b) restarts the rest from the decoded table; the small factor is
the same constant on both sides. Inconsistent chain: both sides are `0`. Holds for **every**
Tier-A parse (chains of any length, any small part), not only for single state atoms.
Source: [[bli-program]] §3.4; mandate target 2(c)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem denoteRat_chainExpr (n : ℕ) (V : ℕ → Sentence → ℚ) {ψ : Sentence}
    {l : List (ℕ × ℕ)} {s : Option Sentence} (hψ : tierA c n ψ = some (l, s)) :
    (chainExpr 𝓜 c n (l, s)).denoteRat V =
      tierAPrice (tentSkeleton smallIndex 𝓜) c n (actualTable smallIndex V n) (l, s) := by
  obtain ⟨hp, hne, -⟩ := tierA_eq_some c hψ
  have hent : ∀ x ∈ l, n < x.1 ∧ x.2 ∈ c.states x.1 := parse_entries c hp
  have hmem : minEntry l ∈ l := minEntry_mem hne
  have hmin : ∀ x ∈ l, (minEntry l).1 ≤ x.1 := fun x hx => minEntry_le x hx
  obtain ⟨hn, hq⟩ := hent _ hmem
  have hle : (minEntry l).1 ≤ (latestEntry l).1 := le_latestEntry _ hmem
  by_cases hc : Consistent l
  · rw [chainExpr_of_consistent 𝓜 c n s hc hn, tierAPrice_of_consistent c _ _ hc,
      denoteRat_mul, denoteRat_const, tentExpr_denoteRat]
    unfold chainMass
    rcases hme : minEntry l with ⟨m, q⟩
    rw [hme] at hn hq hmem hmin hle
    dsimp only at hn hq hmin hle ⊢
    rw [show (latestEntry l).1 - n = (m - n - 1) + 1 + ((latestEntry l).1 - m) by omega,
      chainProbH_restart c (tentSkeleton smallIndex 𝓜) hc hmem hmin hq _ (m - n - 1) n (by omega),
      chainProbH_singleton_eq_lastMarg c (tentSkeleton smallIndex 𝓜) (m - n - 1) n m (by omega) hq]
    ring
  · rw [chainExpr_of_not_consistent 𝓜 c n s hc, tierAPrice_of_not_consistent c _ _ hc,
      denoteRat_const]

end

end Cleanroom.Bli.BliAssemble
