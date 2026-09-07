# The decision-theory bill of the Normative Inductor theorem

Labels: **LEAN** (`GatedChoice.lean`, `PracticalCertificate.lean`, `NormativeInductionInterface.lean`),
**FIX** (exact fixture, named test), **PAPER**, **EXT** (external contract), **OPEN**.
Types are quoted from the Lean on `main` at the canonicalization commit.

## 1. What the theorem consumes — LEAN

`Evaluation O Service` declares, for the accounted state `O`:

```
services : Finset Service
μ : Occ → ℝ                        evaluation measure on exposed occurrences
T : Occ → Service → ℝ              transport plan, row-bounded by μ, nonnegative
Response : Service → Type
Pi : (s : Service) → History → Response s      the ONE response realized at s
loss : Req → (s : Service) → Response s → ℝ    anchored loss, a function of the anchor
defect : Service → History → ℝ                 the public operative defect d_s
lam ρ : Service → ℝ                             intensity and uptake work
M ε : Occ → Service → ℝ                          the certificate constants
Γ D : ℝ
```

`edgeLoss market e s := loss (anchor e) s (Pi s market)` and

```
PracticalCert market e s :  edgeLoss market e s ≤ M e s * defect s market + ε e s .    (R)
```

`PracticalUptake market` packages `(R)` on every supported edge with `0 ≤ defect`,
`0 ≤ lam`, `0 < Σ lam`, the uptake work `lam s * defect s ^ 2 ≤ ρ s`, `0 ≤ Γ`, and the
amplification `Σ_e T e s * M e s ≤ Γ * lam s / Σ lam`.  `progress_bound` gives

```
progress ≤ Γ √(Σρ / Σlam) + Σ T ε + D · residual .
```

The theorem hands decision theory exactly one obligation: produce `Pi` and constants
`M, ε` with `(R)` at the realized market on every supported edge, **and constants `M`
small enough that the amplification hypothesis holds with a `Γ` that does not swallow
the modulus** (§5).  `Pi` is the decision adapter.

## 2. The factorization the repository already has — LEAN

`adequate_set_route` (`PracticalCertificate.lean`):

```
  hadequate : ∀ q ∈ adequate, lam q ≤ εad                    (D2a) adequate ⇒ small loss
  hbound    : ∀ q ∈ menu, lam q ≤ D                           (D2b) loss range
  hcouple   : Σ_{q ∈ menu \ adequate} p q ≤ κ * d + θ         (D1)  the coupling
  ⊢ anchoredLoss menu p lam ≤ (D * κ) * d + (εad + D * θ)
```

(D2) is semantics.  (D1) is the decision-theoretic arrow: the adapter's mass on
inadequate responses is affine in the public defect.  Nothing new is needed to *state*
the bill; the dispatch's `d^dec` is `Σ_{q ∉ A} p q`.

## 3. The abstract form of (D1) — LEAN

`adapter_coupling`: for any map `D` from score vectors to response vectors,

```
massOff (D u) A ≤ θ            (sound at the region point u)
l1 (D b) (D u) ≤ κ · d         (ℓ¹-Lipschitz between b and u, d the sup-distance)
⊢ massOff (D b) A ≤ κ · d + θ .
```

`adapter_practicalCert` composes it with `adequate_set_route`: a sound, Lipschitz adapter
whose output is a distribution pays `(R)` with `M = D κ`, `ε = εad + D θ`.  Algebra, and
the mature statement of the bill:

> **sound on the region + Lipschitz in the scores ⇒ PracticalCert.**

This is the object decision theory owes.  It is not the soft gate; the soft gate is one
realization (§4), and its theorems are proved directly rather than through its
`ℓ¹`-Lipschitz constant, which is not derived (OPEN, minor).

## 4. The soft-gate realization — LEAN, with its regime stated

Scores `b`, region point `u`, threshold `τ`, ramp width `δ`, task preference `pref`:

```
Region u A τ       ∀ q ∉ A, u q ≤ τ
Margin u A τ δ     ∃ q ∈ A, τ + 2δ ≤ u q                (one witness; W = pmin)
MarginMass ... W   A₁ ⊆ A, all marked at τ + 2δ, Σ_{A₁} pref ≥ W
Within b u d       ∀ q, |b q − u q| ≤ d
```

`softGate b q = ramp((b q − τ)/δ) · pref q / total`.  **On the regime `total > 0`:**

```
softGate_massOff_le_sharp   d ≤ δ:  massOff ≤ (Σ_{q ∉ A} pref q) / W · (d / δ)
softGate_massOff_le         d ≤ δ:  massOff ≤ |Q| · pmax / (pmin · δ) · d      (corollary)
softGate_coupling           d ≥ 0:  massOff ≤ κ d + 0
softGate_practicalCert              anchoredLoss ≤ (D κ) d + εad
```

The sharp constant is *inadequate preference mass over certified adequate mass, per unit
relative defect*; `|Q|` and `pmin` disappear.  `Margin` is `MarginMass` with one witness
(`marginMass_of_margin`), and the coarse bound is the sharp one with `W = pmin` and the
inadequate mass bounded by `|Q| pmax` (`coarse_le_sharp_bound`).

**Inquiry is a wrapper, not part of these theorems.**  `gateWithInquiry` on `Option Q`
is the soft gate when `total ≥ W` and the point mass on `none` otherwise; under
`MarginMass` at mass `W` and `d ≤ δ` the wrapper never fires
(`gateWithInquiry_regime`), so on that regime the coupling theorems are theorems about
it.  Nothing is proved about the inquiry branch beyond its definition; what it is
charged is the application's inquiry semantics (§6).

**Scores, not prices.**  All hypotheses are on real vectors; adequacy prices are one
instance.  The same theorems cover a signed adequacy margin `m(q)` with `τ = 0`, or a
constraint-distance vector under `max_r d_r(q)` after negation.

## 5. The rate hidden in `M = Dκ` — PAPER, algebra on the LEAN hypotheses

`softGate_practicalCert` supplies `M e s = D κ_s` at each service `s`.  The amplification
hypothesis then reads

```
D κ_s · Σ_e T e s  ≤  Γ · lam s / Σ lam ,
```

so the smallest admissible `Γ` is `D · sup_s [κ_s · T_s · Σlam / lam s]` with
`T_s = Σ_e T e s` the transported mass at `s`.  Progress is then bounded by

```
D · sup_s [κ_s T_s Σlam / lam s] · √(Σρ / Σlam) + Σ T εad + D · residual .
```

Consequences, each exact:

- `d_s → 0` is not enough.  With `κ_s = (Σ_{∉A} pref)/(W_s δ_s)`, Progress vanishes only
  if `κ_s d_s` vanishes in the service-weighted sense the modulus expresses, i.e. the
  certified margin `δ_s` and the adequate mass `W_s` must not shrink faster than the
  defect.  A menu growing without bound (`Σ_{∉A} pref → ∞`) or a margin vanishing
  (`δ_s → 0`) defeats Progress at zero defect.  The amplification hypothesis is exactly
  where this is charged; it was already the theorem-level place, and the gate makes the
  charge legible.
- **Optimal ramp.**  `κ_s ∝ 1/δ_s` and `Margin` needs `τ + 2δ_s ≤ u(q₀)`, so the widest
  admissible ramp is half the certified margin `m_s = u(q₀) − τ`, giving
  `κ_s = 2 (Σ_{∉A} pref)/(W_s m_s)`.  A wider ramp than the margin allows breaks
  `Margin`; a narrower one raises `κ`.  The schedule is `δ_s = m_s / 2`, and the rate
  condition is `d_s / m_s → 0`: **market error must vanish relative to the certified
  margin.**
- Task selectivity: within the ramp band adequate responses are down-weighted; a wider
  ramp is less selective among weakly marked adequate responses.  Task competence is not
  part of `(R)`, so this trade-off is the application's.

## 6. The bill, stated

Decision theory owes a **sound Lipschitz adapter** (§3), realized by a soft gate (§4),
with `κ` bounded relative to the market's defect (§5).  Semantics owes `Region` (the
region refutes inadequacy at its points), `MarginMass` (it marks adequate responses with
margin and mass — `PRIORITIES.md` item 85), and `(D2)`.  The application owes: the
inquiry semantics (`⊥` charged at `D` through the residual, or `Adequate(⊥)` compiled so
that inquiry is an ordinary response, `NORMATIVE_CHOICE_THEOREM.md` §4), the evaluation
protocol, the menu, `pref`, and the ramp schedule.  Task competence inside the read-adequate
set is outside `(R)` and is the application's (`CANDIDATE_DECISION_THEORIES.md` §2.8).

## 7. Answers to the dispatch's four questions

1. **What `d^dec` measures.**  The adapter's mass on inadequate responses.
2. **Minimal theorem sufficient for `(R)`.**  `adapter_coupling` + `adequate_set_route`.
   Not trivial in the sense that matters: the hard gate is sound at every region point
   and fails (D1) at every positive defect (`hardGate_discontinuous`), so continuity is
   the whole decision-theoretic content.
3. **Is `adequate_set_route` the hint?**  Yes; `hcouple` is the bill and the route's
   absence of any value vector is the point.
4. **Which parts are what.**  Semantics: `Region`, `MarginMass`, `(D2)`.  Decision
   theory: soundness + continuity of the adapter, realized by a ramp.  Implementation:
   `δ`, `pref`, menu, floor `W`.  Application: inquiry semantics, task competence,
   evaluation protocol.
