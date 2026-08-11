# Finite model skeleton — v2

**Frozen 2026-08-11 for round `prompts/2026-08-11-corrigibility-phase-ii/`.**
Binding input to the finite settlement track and the certificate track. Both work
over *these* objects; a track that needs different ones reports the deficiency and
proposes a patch rather than forking the ontology.

Its purpose is composability, not generality. It is the thinnest set of carriers on
which both a settlement classification and a local certificate can be stated, and
it deliberately leaves holes where the round has not decided.

This is a shared specification object for the current finite round. It is not
proposed as the canonical model of the deference project.

All names below are **provisional** (`AGENTS.md` standard 6); they are listed in §9.

---

## 1. Carriers

| object | type | constraint |
|---|---|---|
| `T` | finite linearly ordered set of times | nonempty |
| `Ω` | finite set of states | nonempty |
| `𝓕` | family `(𝓕_t)_{t ∈ T}` of partitions of `Ω` | nondecreasing in refinement: `t ≤ t'` ⇒ `𝓕_{t'}` refines `𝓕_t` |
| `N` | finite set of decision indices | nonempty; each `n ∈ N` carries a time `t(n) ∈ T` |
| `Π_n` | finite set of interventions, per `n` | nonempty; carries a fixed linear order |
| `⊥` | the null effect | `Π_n^⊥ = Π_n ⊔ {⊥}` |
| `B` | bound | positive rational |
| `X_{n,π}` | `Ω → ℚ`, per `n` and `π ∈ Π_n^⊥` | `\|X_{n,π}(ω)\| ≤ B` |
| `F` | `N → T` | `F(n) > t(n)` |

`𝓕_t` is the information available at time `t`: a function is *`t`-measurable* when
it is constant on every cell of `𝓕_t`. Refinement is the only structure the round
needs; no probability is attached to `𝓕`.

`X_{n,π}` is the intervention-indexed quantity. **It is not assumed measurable at
any time**, and is not identified with an observed reward. Which quantities become
observable, and when, is the settlement slot's job (§5) — that is the question the
round is asking, so building an answer into the carrier would beg it.

**`X_{n,⊥}` is a declared per-instantiation modelling commitment.** Scoring the null
effect at `0`, at a status quo, or at a worst case are three different theories of
what refusal costs; the skeleton fixes none of them and requires each instantiation
to declare one. It is indexed over `Π_n^⊥` rather than `Π_n` so that `V_n` (§6) is a
total function on conducts under every execution layer of §4a — without it, any
conduct that can be refused has no valuation at all, and every V-register statement
over a protecting `κ_n` is ill-typed rather than false.

## 2. The principal

| object | type | constraint |
|---|---|---|
| `v⁺_n` | `Ω × Π_n → ℚ` | `\|v⁺_n(ω,π)\| ≤ B`; `F(n)`-measurable in `ω` |
| `J_n` | `Ω → Π_n` | least maximizer of `v⁺_n(ω,·)` in `Π_n`'s fixed order |

`J_n` is `F(n)`-measurable because `v⁺_n` is. The tie-break is fixed and computable,
so `J_n` is a function and not a relation: a theorem may not exploit tie-break
freedom.

`v⁺_n` settles **what the designated principal judged**, at `F(n)`. It carries no
claim of independent normative correctness; §5 keeps that distinction.

**`v⁺_n` is indexed by `Π_n`, not `Π_n^⊥`: the principal grades interventions and
does not grade refusal.** This asymmetry with §1 is deliberate and is the source of
the register discipline in §4b. Supplying a grade for `⊥` would make the null effect
an object of the principal's judgment, which is a substantive theory of refusal and
not a carrier choice.

### 2a. Competence vocabulary

A **competence hypothesis** is a predicate of `(v⁺_n, X_n)` alone. A hypothesis that
also mentions `P_n` (§6) is a **joint competence–credence hypothesis** and is
declared as one.

The distinction is load-bearing and v1 could not express it: it is exactly the line
between a hypothesis equivalent to the delegation inequality and one strictly
stronger than it. Nothing is retyped by this clause; it fixes vocabulary.

## 3. The prediction channel

| object | type | constraint |
|---|---|---|
| `v̂⁺_n` | `Ω × Π_n → ℚ` | `\|v̂⁺_n(ω,π)\| ≤ B`; **`t(n)`-measurable** in `ω` |
| `Ĵ_n` | `Ω → Π_n` | least maximizer of `v̂⁺_n(ω,·)`, same order |

`v̂⁺_n` is `A`'s model of the principal, available at decision time. **No axiom
relates `v̂⁺` to `v⁺`.** They may agree everywhere, differ everywhere, or — the case
the channel track wants — agree except on one cell.

The measurability difference is the skeleton's whole account of the asymmetry:
`v̂⁺_n` is available at `t(n)` and `v⁺_n` is not. A model in which `v⁺_n` happens to
be `t(n)`-measurable is permitted, and is the perfectly-predictable-principal case
the program is forbidden to rule out.

## 4. Conduct: proposal, realization, quantity

A **conduct** for decision `n` is a **proposal** `α : Ω → Π_n` with a declared
information time `r ∈ T`. Its **realization** is `ω ↦ E_n(α(ω), ρ_n(ω))` and its
**quantity** is `ω ↦ X_{n, realization(ω)}(ω)`, with `E_n` and `ρ_n` from §4a.

The three are separate because the round's central distinctions live in the gaps
between them. A comparator is *identified* by its proposal and *evaluated* through
its quantity, and under a protecting execution layer the two come apart: what an
agent proposes is not what occurs.

A conduct is **well-timed** when its proposal is `r`-measurable. Well-timedness is
a property, not a standing assumption: `DELEGATE` is deliberately not well-timed at
`t(n)`.

### The conducts the skeleton must represent

| provisional name | proposal | information time |
|---|---|---|
| `DELEGATE` | `ι_n ∘ ρ_n` | `F(n)` |
| `FIXED[π]` | `ω ↦ π` | `t(n)` |
| `SIM` | `Ĵ_n` | `t(n)` |
| `FU[g]` | *not fixed by this version* | `g(n)` |

`FU[g]` is a **hole**. The fully-updated comparator needs `A`'s own later
evaluation, which requires an object this skeleton does not carry: a time-indexed
family of `A`-valuations. A track needing it reports the deficiency; the round does
not invent it, because collapsing `FU[g]` into `SIM` by definitional stretching is
forbidden, and careless invention is how that collapse would happen.

`DELEGATE` and `SIM` are the pair the substitution question is about. When
`v̂⁺_n = v⁺_n` pointwise their realizations and quantities coincide under the free
instantiation; their proposals still differ, and whether that difference does any
work is the open question, not an assumption.

### 4a. The execution layer

| object | type | constraint |
|---|---|---|
| `R_n` | finite set of reports | nonempty |
| `ρ_n` | `Ω → R_n` | `F(n)`-measurable |
| `ι_n` | `R_n → Π_n` | the intervention a report designates |
| `E_n` | `Π_n × R_n → Π_n^⊥` | `E_n(ι_n(r), r) = ι_n(r)` |

Derived: `κ_n(r) = E_n(Π_n × {r})`, the authorized menu at report `r`. The honesty
condition `E_n(ι_n(r), r) = ι_n(r)` says the report's own designation is always
executable; whether anything *else* is, is what `κ_n` declares.

Whether a given instantiation protects anything is the properness of `κ_n`, declared
per instantiation and per state. **The clause adds no probability on reports, no
admissibility restriction on conducts, no causal calculus, no token and no
cryptography.**

**Conservativity.** With `R_n = Π_n`, `ι_n = id`, `ρ_n = J_n` and `E_n(π, r) = π`,
the realization is the proposal, `κ_n ≡ Π_n`, and `⊥` is unreachable. Every v1
statement is a v2 statement about this **free instantiation**. The opposite pole,
`κ_n(r) = {ι_n(r), ⊥}`, is **strict protection**.

### 4b. Register discipline

Two registers score conducts, and v2 does not define them on the same domain.

- The **V-register** (`V_n`, §6) scores **realizations**, and is total because §1
  indexes `X` over `Π_n^⊥`.
- The **grade register** (`G_n`, and the derived defect and advantage functionals)
  scores **proposals**, and is *not* defined on realizations, because §2 gives
  `v⁺_n` no value at `⊥`.

**A grade-register statement over v2 is a statement about proposals, and must say
so.** Read over realizations it is ill-typed, not false. Extending the grade
register to `⊥` is an open modelling choice (§8.7), not a defect to be patched
silently: it is the question of what the principal's judgment says about refusal,
and no track has proposed an answer.

## 5. The settlement slot

**No settlement semantics is built in.** A *settlement instantiation* supplies a set
`Q` of settleable items, a map `when : Q → T`, and for each `q ∈ Q` a valuation
`val_q : Ω → ℚ` required `when(q)`-measurable.

The round instantiates it three ways. What each yields is the settlement track's
deliverable, not a fact recorded here.

1. **Grade/report settlement.** `Q = {(n,π)}`, `when(n,π) = F(n)`,
   `val_{(n,π)} = v⁺_n(·,π)`. Settles what the principal judged.
2. **World/outcome settlement.** `Q ⊆ {(n,π)}`, `when(n,π) = F(n)`,
   `val_{(n,π)} = X_{n,π}` — available only for those `(n,π)` whose `X` is in fact
   `F(n)`-measurable. The skeleton does not assume any are; an instantiation
   declares which, and that declaration is a modelling commitment to be reported.
3. **Underwriting/enforcement.** A transfer schedule `τ : {(n,π)} → ℚ` fixed
   exogenously, not derived from any `Ω`-measurable truth. It settles nothing
   epistemic; it is the arrangement giving an authority relation practical force
   where independent settlement does not reach.

Instantiation 3 exists so that "we have enforcement rather than epistemic trust" is
a *statable* outcome. That outcome would be a result, not a failure.

## 6. Valuation

`A`'s time-`n` credence is a probability measure `P_n` on `Ω` with rational masses
summing exactly to `1`. The default valuation of a conduct with proposal `α` is

```
V_n(α)  =  Σ_{ω ∈ Ω}  P_n(ω) · X_{n, E_n(α(ω), ρ_n(ω))}(ω)
```

in exact rational arithmetic. `ε` denotes a nonnegative rational tolerance. Under the
free instantiation this is v1's `V_n` verbatim.

`P_n` is a single measure rather than a conditional system: conditioning is
expressed by choosing the measure, which suffices for one decision index and avoids
committing to an update rule the round has not decided.

**A track needing a different valuation states it as an added assumption.** The
target inequality `V_n(DELEGATE) ≥ V_n(π) − ε` is stated in this `V`; a track
proving it in another has proved a different theorem.

## 7. Exactness

Every numeric carrier is a `fractions.Fraction` or a Lean rational. No floats appear
in any theorem-bearing computation, and a test recomputing a constant compares it
exactly (`AGENTS.md` standard 2).

## 8. What this version deliberately does not fix

Each is a hole, not an oversight. Filling one is a maintainer decision or a track's
reported deficiency.

1. **`FU[g]`** — needs a time-indexed family of `A`-valuations (§4).
2. **Admissibility** — no restriction on which conducts or traders are legal. The
   red-team track works *over* this skeleton to propose candidates; none is
   installed here.
3. **Trader legality and the market** — absent entirely, exactly as in the inherited
   corpus. This skeleton does not close the market/trader gap and must not be read
   as doing so.
4. **Which `X_{n,π}` settle** — a per-instantiation declaration (§5.2).
5. **The relation between `v⁺` and `X`** — none. Whether the principal's grade
   tracks the intervention-indexed quantity is a hypothesis a theorem may assume and
   must then display.
6. **Cross-decision structure** — stated per decision index. Any result aggregating
   over `N` states its own aggregation. A per-`n` credence family with a declared
   admissible weight class was considered and **deliberately not adopted**: the
   competence track proved that no such aggregate constrains any named decision, so
   the patch buys nothing the finite kernel needs.
7. **The grade of the null effect** — `v⁺_n` is not defined on `⊥` (§2, §4b). Until
   it is, no grade-register statement quantifies over realizations.
8. **`X_{n,⊥}`'s value** — §1 requires each instantiation to declare it and fixes no
   default. All of protection's valuation content sits here.

## 9. Provisional names

`DELEGATE`, `FIXED`, `SIM`, `FU`, `conduct`, `proposal`, `realization`, `quantity`,
`well-timed`, `settlement instantiation`, `execution layer`, `authorized menu`,
`free instantiation`, `strict protection`, `null effect`, `competence hypothesis`,
`joint competence–credence hypothesis`, `V-register`, `grade register`, `v̂⁺`, `P_n`,
`V_n`. All are this round's working vocabulary; none is proposed for permanence.

## 10. Version

`v2`, frozen 2026-08-11, superseding `v1` (frozen 2026-08-11, wave-1 tracks
dispatched against repository commit `ec7d6cc`). A revision is a new version number,
recorded here, with every track that consumed the previous version either rerun or
explicitly reconciled.

### What changed, and why

1. **§1 — `X` is indexed over `Π_n^⊥`, with `\|X_{n,⊥}\| ≤ B`.** Required: without it
   `V_n` is not total on conducts under any protecting `κ_n`, so the V-register is
   ill-typed over the execution layer rather than merely unproved.
2. **§4a — the execution layer.** Required: v1 has no capability structure, so
   fail-closed in its strong form — the agent *cannot execute* an unauthorized
   alternative — is not expressible in it at all.
3. **§4 — conduct is a proposal with a realization.** Forced by §4a; v1's selection
   is the realization under the free instantiation, so v1's distinctions survive.
4. **§4b — register discipline.** Required for coherence: §1 extends to `⊥` and §2
   does not, so grade-register and V-register statements have different domains, and
   a statement that does not say which register it is in is ambiguous over v2.
5. **§2a — competence vocabulary.** Additive; fixes the credence-free line that the
   competence track showed to be the boundary between a circular hypothesis and a
   usable one.
6. **§8.6 — cross-decision aggregation declined**, on the competence track's own
   evidence rather than for economy.

### Rerun or reconcile

| track | binding | disposition |
|---|---|---|
| A, E, F | not v1-bound | unaffected |
| D (item 17, channel) | v1 | **reconciled** — Propositions 1–8 are statements about the free instantiation and survive verbatim under §4a's conservativity |
| B (item 15, settlement) | v1 | **reconciled** — the classification and the `2B` bond are statements about the free instantiation |
| C (item 16, certificate) | v1 | **rerun, and the rerun is on record.** Under strict protection: L1, L2 and L7 are invariant; L3 survives as a statement about the grade-register defect but its bound is *not* a bound on the protected valuation gap; L5's comparator is not realizable; and the settlement-loaded branch of the preemption bound is **false**, with 1443 refuting instances. Theorem C′ is unaffected as a grade-register statement about proposals (§4b) |
| G (item 20, admissibility red team) | v1 | **rerun recommended, not performed.** A restriction on the conduct set is now nameable as a capability assignment, so the red team should re-ask whether its candidate families are `κ`-statements in disguise |

The Lean promotions in `lean/Workspace/Deference/Contrib/` are **unaffected**. They
were deliberately restricted to the grade register and to settlement-free statements,
so nothing refuted above was ever promoted; `CertificateBounds.gradeRegister_strict`
is a statement about proposals and is exactly the reading §4b declares.
