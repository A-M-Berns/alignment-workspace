import Cleanroom.Corrigibility.LegitNegStatic.Proposals

/-!
# The toys of record and the witness constructions

Package `legit-neg-static`, target 6. Sources: `clusters/B/fixtures/common.py:18-31`,
`clusters/C/fixtures/c01_toy_thresholds.py:23-33`, `clusters/D/fixtures/d1_t2_floor.py:15-21`,
`clusters/A/fixtures/run.py:116-123, 264-275`, `clusters/B/fixtures/fx_conditioning.py:7-24`,
`fx_timing.py:20-31`, `fx_readouts.py:9-14`, `clusters/C/fixtures/c02_sources.py:18-45`,
`c04_lexical.py:16-24`; pinned by [[corr-legit-neg-2-inventory]] items 2-005 and 2-006.

Each construction is a total function from a few rationals (plus the range proofs the prior
needs) to a `Problem`. Only well-formedness is proved here; the B/C headlines belong to
`legit-neg-pricing`. Encodings: `Fin 2` states are `0 = g`, `1 = b`; `Fin 2` actions are
`0 = a₀ / safe / keep`, `1 = a₁ / risky / void`; the four-state selection model uses `Fin 4`
with `0 = (W, L)`, `1 = (W, N)`, `2 = (S, L)`, `3 = (S, N)`.
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset

/-! ### The chat's toy (B, C, D1) -/

/-- **B's toy** `toy(v, w, ug0, ug1, π_b)` (`common.py:18-31`): states `g, b` with `π(b) = π_b`;
`a₀` legitimate in both, `a₁` void in `b`; `u(g, a₀) = ug0`, `u(g, a₁) = ug1`, `u(b, a₀) = v`,
`u(b, a₁) = w` (the human value of the void terminal: `0` floor, `> 0` mild, `< 0` below the
floor).
Source: [[corr-legit-neg-2-inventory]] item 2-005
Kind: D
Fidelity: exact -/
def toyB (v w ug0 ug1 πb : ℚ) (h0 : 0 ≤ πb) (h1 : πb ≤ 1) : Problem (Fin 2) (Fin 2) where
  prior := ![1 - πb, πb]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_two]
  leg := fun s a => !(decide (s = 1) && decide (a = 1))
  u := fun s a => ![![ug0, ug1], ![v, w]] s a

/-- **C's toy** `toy(v, p, x, c, off)` as a `Problem`: B's toy with `u_{g0} = 1`, `u_{g1} = 1 − p`,
`π_b = 1/2`, and the void grade `x` carried as `u(b, a₁)` (C keeps it in `W`, see `toyC_W`).
Source: [[corr-legit-neg-2-inventory]] item 2-005
Kind: D
Fidelity: exact -/
def toyC (v p x : ℚ) : Problem (Fin 2) (Fin 2) :=
  toyB v x 1 (1 - p) (1/2) (by norm_num) (by norm_num)

/-- C's constant void grade `W ≡ x` (`W = {("b","a1"): {"a0": x, "a1": x}}`).
Source: [[corr-legit-neg-2-inventory]] item 2-005
Kind: D
Fidelity: exact -/
def toyC_W (x : ℚ) : MenuVec (Fin 2) (Fin 2) := fun _ _ _ => x

/-- C's constant cross-branch assessment `K ≡ c` at every legitimate terminal.
Source: [[corr-legit-neg-2-inventory]] item 2-005
Kind: D
Fidelity: exact -/
def toyC_K (c : ℚ) : MenuVec (Fin 2) (Fin 2) := fun _ _ _ => c

/-- C's primitive menu vector with its settable off-diagonal entries (`off`): diagonal
`V_{g,a₀}(a₀) = 1`, `V_{b,a₀}(a₀) = v`, `V_{g,a₁}(a₁) = 1 − p`; off-diagonal `V_{g,a₀}(a₁) = g01`
(default `1`), `V_{b,a₀}(a₁) = b01` (default `v`), `V_{g,a₁}(a₀) = g10` (default `1`).
Source: [[corr-legit-neg-2-inventory]] item 2-005
Kind: D
Fidelity: exact -/
def toyC_V (v p g01 b01 g10 : ℚ) : MenuVec (Fin 2) (Fin 2) :=
  fun s a c => ![![![1, g01], ![g10, 1 - p]], ![![v, b01], ![0, 0]]] s a c

/-- **D1's lotteries** `lotteries(G, v, β, p, post_g)` as a `Problem`: a cell with
`P(g | I) = post_g`; `a₀ ↦ {(post_g, 1, G), (post_b, 1, v)}`, `a₁ ↦ {(post_g, 1, G + β − p), (post_b, 0, 0)}`
— B's toy with `u_{g0} = G`, `u_{g1} = G + β − p`, `w = 0`, `π_b = 1 − post_g`.
Source: [[corr-legit-neg-2-inventory]] item 2-005
Kind: D
Fidelity: exact -/
def toyD (G v β p postg : ℚ) (h0 : 0 ≤ postg) (h1 : postg ≤ 1) : Problem (Fin 2) (Fin 2) :=
  toyB v 0 G (G + β - p) (1 - postg) (by linarith) (by linarith)

/-- D's lottery of `a` in `toyD` is the pushforward the reconciliation of item 2-001 states.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toyD_lotteryOf (G v β p postg : ℚ) (h0 : 0 ≤ postg) (h1 : postg ≤ 1) (a : Fin 2) :
    (toyD G v β p postg h0 h1).lotteryOf (S1 (toyD G v β p postg h0 h1).u) a =
      fun s => ((toyD G v β p postg h0 h1).prior s, (toyD G v β p postg h0 h1).leg s a,
        (toyD G v β p postg h0 h1).u s a) := rfl

/-! ### Cluster A's witness constructions -/

/-- **`incautionInstance q δ x harm`** (`run.py:116-123`): states `g` (legitimate) and `b`
(void), `π(b) = q`; `Q(g, ·) = (x, x + δ)`, `Q(b, ·) = (1, 1 − harm)`; actions `0 = safe`,
`1 = risky`. The standard is the problem's `u`. Sealed by `fun s => decide (s = 0)`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def incautionInstance (q δ x harm : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Problem (Fin 2) (Fin 2) where
  prior := ![1 - q, q]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_two]
  leg := fun s _ => decide (s = 0)
  u := fun s a => ![![x, x + δ], ![1, 1 - harm]] s a

/-- The legitimacy event of the two-state instances: `L = {g}`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def legG : Fin 2 → Bool := fun s => decide (s = 0)

/-- `incautionInstance_SealedBy`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma incautionInstance_SealedBy (q δ x harm : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (incautionInstance q δ x harm h0 h1).SealedBy legG := fun _ _ => rfl

/-- The adversary strength of a `Fin 4` selection-model state: `0 = W`, `1 = S`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def smK : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The legitimacy event of the selection model: states `0 = (W, L)` and `2 = (S, L)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def smL : Fin 4 → Bool := ![true, false, true, false]

/-- **`selectionModelWith aW aS Q`** (`run.py:264-275`, the prior and legitimacy structure):
latent adversary strength `k ∈ {W, S}` with prior `1/2` each, `P(L | k) = a_k`; starting states
`(k, L)`, `(k, N)` with `π(k, L) = a_k / 2`, `π(k, N) = (1 − a_k) / 2`; the standard `Q` is a
parameter (A3 and A4b use different ones). Sealed by `smL`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def selectionModelWith (aW aS : ℚ) (hW0 : 0 ≤ aW) (hW1 : aW ≤ 1) (hS0 : 0 ≤ aS) (hS1 : aS ≤ 1)
    (Q : Fin 4 → Fin 2 → ℚ) : Problem (Fin 4) (Fin 2) where
  prior := ![aW / 2, (1 - aW) / 2, aS / 2, (1 - aS) / 2]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_four]; ring
  leg := fun s _ => smL s
  u := Q

/-- `selectionModelWith_SealedBy`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma selectionModelWith_SealedBy (aW aS : ℚ) (hW0 : 0 ≤ aW) (hW1 : aW ≤ 1) (hS0 : 0 ≤ aS)
    (hS1 : aS ≤ 1) (Q : Fin 4 → Fin 2 → ℚ) :
    (selectionModelWith aW aS hW0 hW1 hS0 hS1 Q).SealedBy smL := fun _ _ => rfl

/-- A3's standard on the selection model (`run.py:295-298`): on `L` states `safe = x`,
`risky = x + δ`; on `N` states `safe = 1`, `risky = 1 − h(k)` with `h = (hW, hS)`.
Source: [[corr-legit-neg-2-inventory]] item 2-009
Kind: D
Fidelity: exact -/
def smQ (x δ hW hS : ℚ) : Fin 4 → Fin 2 → ℚ := fun s a =>
  if smL s then x + (if a = 1 then δ else 0) else 1 - (if a = 1 then ![hW, hS] (smK s) else 0)

/-- **`selectionModel aW aS x hW hS δ`**: the selection model with A3's standard.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def selectionModel (aW aS x hW hS δ : ℚ) (hW0 : 0 ≤ aW) (hW1 : aW ≤ 1) (hS0 : 0 ≤ aS)
    (hS1 : aS ≤ 1) : Problem (Fin 4) (Fin 2) :=
  selectionModelWith aW aS hW0 hW1 hS0 hS1 (smQ x δ hW hS)

/-- A4b's standard on the selection model (`run.py:428-433`): `Q(s, idle) = λ · [k = W]`
(`L'` holds under `idle` iff the adversary is weak), `Q(s, protect) = λ − ε`; actions
`0 = idle`, `1 = protect`.
Source: [[corr-legit-neg-inventory]] item 011 (A4b)
Kind: D
Fidelity: exact -/
def smQprot (lam ε : ℚ) : Fin 4 → Fin 2 → ℚ := fun s a =>
  if a = 1 then lam - ε else lam * (if smK s = 0 then 1 else 0)

/-! ### Cluster B/C witness constructions (well-formedness only; headlines are `legit-neg-pricing`'s) -/

/-- A proper non-empty subset of the states: the index type of `voidingFamily`'s voiding
options, so that "for every `B`" is a real quantifier downstream.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
abbrev ProperSub (S : Type) [Fintype S] [DecidableEq S] :=
  {B : Finset S // B.Nonempty ∧ B ≠ univ}

/-- **`voidingFamily prior x p w`** (`fx_conditioning.py:7-24`): menu `keep` (`none`) plus
`void B` (`some B`) for every proper non-empty `B ⊆ S`; `void B` voids legitimacy on `B`
with `u = w` there and `u = x s − p` off `B`; `keep` is legitimate everywhere with `u = x s`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def voidingFamily {S : Type} [Fintype S] [DecidableEq S] (prior : S → ℚ)
    (hn : ∀ s, 0 ≤ prior s) (hs : ∑ s, prior s = 1) (x : S → ℚ) (p w : ℚ) :
    Problem S (Option (ProperSub S)) where
  prior := prior
  prior_nonneg := hn
  prior_sum := hs
  leg := fun s a => match a with
    | none => true
    | some B => !(decide (s ∈ B.1))
  u := fun s a => match a with
    | none => x s
    | some B => if s ∈ B.1 then w else x s - p

/-- **`gambleProblem v X' ε w`** (`fx_timing.py:20-31`): T2 in state `b`; `keep` (`0`) is
legitimate with score `v`; `gamble` (`1`) keeps legitimacy only on the coin `h` (state `0`,
probability `ε`), scoring `X'` there, else void with human value `w`. (The fixture drops a
zero-probability coin state; here both states are kept, one possibly of mass `0`.)
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def gambleProblem (v X' ε w : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : Problem (Fin 2) (Fin 2) where
  prior := ![ε, 1 - ε]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_two]
  leg := fun s a => decide (a = 0) || decide (s = 0)
  u := fun s a => if a = 0 then v else if s = 0 then X' else w

/-- **`withAllvoid P wval`** (`fx_readouts.py:9-14`): `P` with one extra action (`none`) that is
void in every state with `u = wval`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def withAllvoid {S A : Type} [Fintype S] [Fintype A] (P : Problem S A) (wval : ℚ) :
    Problem S (Option A) where
  prior := P.prior
  prior_nonneg := P.prior_nonneg
  prior_sum := P.prior_sum
  leg := fun s a => match a with
    | none => false
    | some a => P.leg s a
  u := fun s a => match a with
    | none => wval
    | some a => P.u s a

/-- **`capture r vb`** (`c02_sources.py:18-26`) as a `Problem` (`r` lives in `captureW`): states
`g, b` equiprobable, actions `0 = a₀`, `1 = cap`; `cap` voids in `b`; `u` is C's `H`:
`(1/2, 1/2; vb, 0)`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def capture (vb : ℚ) : Problem (Fin 2) (Fin 2) where
  prior := ![1/2, 1/2]
  prior_nonneg := by intro s; fin_cases s <;> simp
  prior_sum := by simp [Fin.sum_univ_two]; norm_num
  leg := fun s a => !(decide (s = 1) && decide (a = 1))
  u := fun s a => ![![1/2, 1/2], ![vb, 0]] s a

/-- `capture`'s primitive menu vector: `1/2` at the `g` terminals, `vb` at `(b, a₀)`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def captureV (vb : ℚ) : MenuVec (Fin 2) (Fin 2) := fun s _ _ => if s = 1 then vb else 1/2

/-- `capture`'s void grade (G3, the captured report): `W ≡ r`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def captureW (r : ℚ) : MenuVec (Fin 2) (Fin 2) := fun _ _ _ => r

/-- `capture`'s cross-branch assessment: the legitimate humans at `(g, cap)` see the harm in
`b`, `K ≡ 0`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def captureK : MenuVec (Fin 2) (Fin 2) := fun _ _ _ => 0

/-- Whether a `voiProblem` state's hypothesis is `A` (`hit = 1`): states `0 = (g, A)`,
`1 = (g, B)`, `2 = (b, A)`, `3 = (b, B)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def voiHit : Fin 4 → ℚ := ![1, 0, 1, 0]

/-- **`voiProblem q r g`** (`c02_sources.py:29-45`): states `(s, θ)` with prior `π(s) · cred(θ)`,
`π(b) = r`, `cred(A) = q`; `a₀` legitimate everywhere with value `1/2`; `a₁` legitimate on `g`
with value `(g + 1)/2` and void on `b` with graded value `(g + hit)/2`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def voiProblem (q r g : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Problem (Fin 4) (Fin 2) where
  prior := ![(1 - r) * q, (1 - r) * (1 - q), r * q, r * (1 - q)]
  prior_nonneg := by
    intro s; fin_cases s <;> simp <;> exact mul_nonneg (by linarith) (by linarith)
  prior_sum := by simp [Fin.sum_univ_four]; ring
  leg := fun s a => !(decide (2 ≤ s.val) && decide (a = 1))
  u := fun s a => if a = 0 then 1/2 else if s.val < 2 then (g + 1) / 2 else (g + voiHit s) / 2

/-- `voiProblem`'s cross-branch assessment at the legitimate `(g, θ, a₁)` terminals:
`(g + hit)/2` (accurate humans: what `a₁` does if `¬L`).
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def voiK (g : ℚ) : MenuVec (Fin 4) (Fin 2) := fun s _ _ => (g + voiHit s) / 2

/-- `voiProblem`'s void grade at `(b, θ, a₁)`: `(g + hit)/2`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def voiW (g : ℚ) : MenuVec (Fin 4) (Fin 2) := fun s _ _ => (g + voiHit s) / 2

/-- **`epsProblem ε w`** (`c04_lexical.py:16-24`): states `main` (`0`), `eps` (`1`) with
`π(eps) = ε`; actions `0 = safe`, `1 = good`; `good` voids on `eps`; `u` is C's gap-satisfying
standard `(1/2, 1; 1/2, (2/5) w)`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def epsProblem (ε w : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : Problem (Fin 2) (Fin 2) where
  prior := ![1 - ε, ε]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_two]
  leg := fun s a => !(decide (s = 1) && decide (a = 1))
  u := fun s a => ![![1/2, 1], ![1/2, 2/5 * w]] s a

/-- `epsProblem`'s primitive menu vector: `good` scored `1` at its legitimate terminal, `safe`
scored `0` everywhere.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def epsV : MenuVec (Fin 2) (Fin 2) := fun _ a _ => if a = 1 then 1 else 0

/-- `epsProblem`'s void grade `W ≡ w`.
Source: [[corr-legit-neg-2-inventory]] item 2-006
Kind: D
Fidelity: exact -/
def epsW (w : ℚ) : MenuVec (Fin 2) (Fin 2) := fun _ _ _ => w

end Cleanroom.Corrigibility.LegitNegStatic
