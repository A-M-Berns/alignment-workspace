# The decision-theory bill of the Normative Inductor theorem

Extracted from `lean/Workspace/Normativity/Contrib/NormativeInductionInterface.lean`,
`NormativeInductor.lean`, `NormativeInductorComposition.lean` and
`PracticalCertificate.lean` on `main` at the canonicalization commit.  Types are quoted
from the Lean; nothing is remembered notation.

## 1. What the theorem consumes

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

`PracticalUptake market` packages: `0 ≤ defect`, `(R)` on every edge with `T e s > 0`,
`0 ≤ lam`, `0 < Σ lam`, the uptake work `lam s * defect s ^ 2 ≤ ρ s`, `0 ≤ Γ`, and the
amplification `Σ_e T e s * M e s ≤ Γ * lam s / Σ lam`.  `progress_bound` then gives

```
progress ≤ Γ √(Σρ / Σlam) + Σ T ε + D · residual .
```

So the theorem hands decision theory exactly one obligation: **produce `Pi` and the
constants `M, ε` such that `(R)` holds at the realized market on every supported edge.**
`Pi` is the decision adapter — a map from the market history to one response per
service.  Nothing in the interface says how `Pi` reads the market, what `Response s` is,
or how `loss` relates to `defect`; `(R)` is the whole contract.

## 2. The factorization the repository already has

`PracticalCertificate.lean` gives three routes to `(R)`; the one that separates the
arrows is the adequate-set route:

```
adequate_set_route  (menu adequate : Finset Q) {p lam : Q → ℝ}
  hsub : adequate ⊆ menu
  hp, hprob : p is a distribution on menu
  hadequate : ∀ q ∈ adequate, lam q ≤ εad                    (D2a) adequate ⇒ small loss
  hbound    : ∀ q ∈ menu, lam q ≤ D                           (D2b) loss range
  hcouple   : Σ_{q ∈ menu \ adequate} p q ≤ κ * d + θ         (D1)  the coupling
  ⊢ anchoredLoss menu p lam ≤ (D * κ) * d + (εad + D * θ)
```

with `anchoredLoss menu p lam = Σ p q * lam q` the expected anchored loss of a response
*distribution*.  Reading `p = Pi s market` as a distribution over a finite menu:

- **(D2)** is semantics: which responses are adequate for the anchor and what an
  inadequate one costs.  It is the practical-semantics contract as the architecture
  round already records it.
- **(D1)** is the decision-theoretic arrow the dispatch asks for.  `d^dec` in the
  dispatch's notation is the **mass the adapter places outside the adequate set**, and
  (D1) says it is affine in the public normative defect.

The candidate factorization `d^dec ≤ C d^norm + η`, `Λ ≤ L d^dec + ε` is therefore
already the repository's, with `d^dec := Σ_{q ∉ A} p q`, `C = κ`, `η = θ`, `L = D`,
`ε = εad`.  Nothing needs to be added to the Lean interface to state the bill; what is
missing is a theorem *producing* (D1).

## 3. What (D1) asks of an adapter

`d = dist_∞(b_s, K_s)` is the sup-distance of the displayed prices to the compiled
region (`NormativeInductor.lean`, chosen for padding invariance).  So (D1) is a
statement about a map from *price vectors* to *response distributions*:

> the mass the adapter places on inadequate responses is at most `κ` per unit of
> sup-distance of the prices from the region, plus `θ`.

Split it once more, because two different things are being asked:

- **(D1a) region soundness** — at every region point `u ∈ K_s`, the adapter's mass off
  the true adequate set is at most `θ`.
- **(D1b) Lipschitz continuity** — the adapter's mass off the adequate set moves at most
  `κ` per unit sup-distance in the prices.

(D1a) is not purely decision theory: it says that when the market conforms to the norm
the adapter chooses adequately, which needs the region to *encode* adequacy and the
adapter to *read* it.  Split again:

- the region encodes adequacy: inadequate responses are priced at most `τ` at region
  points, and some adequate response is priced above `τ` with a margin
  (`GatedChoice.Region`, `GatedChoice.Margin`) — the compiler's soundness plus the
  market's accuracy on settling adequacy sentences, both external;
- the adapter reads it: a gate on the adequacy price.

(D1b) is pure decision theory, and it is where a naive adapter fails.

## 4. The bill, stated

**Decision theory owes the Normative Inductor a gate**: a map `Dec : Prices → Δ(Q ∪ {⊥})`
such that, given a region encoding of adequacy with margin,

1. **(soundness)** at region points the gate's mass off the read-adequate set is at
   most `θ`;
2. **(continuity)** the mass off the read-adequate set is `κ`-Lipschitz in the
   sup-norm of the prices;
3. **(inquiry)** when no response is confidently adequate the gate returns `⊥`, which
   is charged at `D` by the Progress statistic and is not a violation;
4. **(competence)** among the read-adequate responses the gate's task regret against a
   declared comparison class is small — a requirement of the application, not of
   `(R)`, which `progress_bound` never consults.

Semantics owes: the region encodes adequacy soundly at the realized market
(`Region`), and adequate responses have anchored loss at most `εad` while every response
has loss at most `D` (`(D2)`).  Implementation owes: the finite menu, the task preference,
and the ramp width `δ`.

`softGate_practicalCert` (`GatedChoice.lean`) discharges 1–3 for the soft gate and
composes with `adequate_set_route`: `(R)` with `M = D · |Q| · pmax / (pmin · δ)` and
`ε = εad`.  Item 4 is outside `(R)` and is what a BRIA-style learner supplies inside the
gate (`CANDIDATE_DECISION_THEORIES.md` §5).

## 5. Answers to the dispatch's four questions

1. **What does `d^dec` measure?**  The adapter's mass on inadequate responses.  Not a
   value gap: `regret_dominance_vacuous_on_forbidden_optimum` already records that a
   value-optimal forbidden response forces the value route's constant to absorb the whole
   loss range.
2. **Minimal decision-theoretic theorem sufficient for `(R)`.**  A Lipschitz, sound
   gate (`softGate_coupling`).  It is not trivial: the hard gate has no Lipschitz
   constant (`hardGate_discontinuous`), so continuity forces a randomized or ramped
   adapter near the adequacy threshold.
3. **Is `adequate_set_route` hinting at the answer?**  Yes: its `hcouple` is the bill,
   and the route's absence of any value vector is the point — the adapter needs an
   adequate *set*, not a utility.
4. **Which parts are what.**  Semantics: `Region`, `(D2)`.  Decision theory: the gate,
   its continuity, its inquiry mode, and task competence within it.  Implementation:
   `δ`, `pref`, the menu, the ramp.
