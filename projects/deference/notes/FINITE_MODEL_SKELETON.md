# Finite model skeleton — v1

**Frozen 2026-08-11 for round `prompts/2026-08-11-deference-corrigibility/`.**
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
| `B` | bound | positive rational |
| `X_{n,π}` | `Ω → ℚ`, per `n` and `π ∈ Π_n` | `|X_{n,π}(ω)| ≤ B` |
| `F` | `N → T` | `F(n) > t(n)` |

`𝓕_t` is the information available at time `t`: a function is *`t`-measurable* when
it is constant on every cell of `𝓕_t`. Refinement is the only structure the round
needs; no probability is attached to `𝓕`.

`X_{n,π}` is the intervention-indexed quantity. **It is not assumed measurable at
any time**, and is not identified with an observed reward. Which quantities become
observable, and when, is the settlement slot's job (§5) — that is the question the
round is asking, so building an answer into the carrier would beg it.

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

## 4. Conduct: rule, selection, quantity

A **conduct** for decision `n` is a triple:

- **rule** — how the intervention is chosen, with a declared information time `r ∈ T`;
- **selection** — a function `c : Ω → Π_n`;
- **quantity** — `ω ↦ X_{n, c(ω)}(ω)`.

The three are separate because the round's central distinctions live in the gaps
between them. Two conducts with different rules may have equal selections on part
of `Ω` and differ elsewhere; a comparator is *identified* by its rule and
*evaluated* through its quantity.

A conduct is **well-timed** when its selection is `r`-measurable. Well-timedness is
a property, not a standing assumption: `DELEGATE` is deliberately not well-timed at
`t(n)`.

### The conducts the skeleton must represent

| provisional name | rule | selection | information time |
|---|---|---|---|
| `DELEGATE` | take whatever the actual principal reports | `J_n` | `F(n)` |
| `FIXED[π]` | take `π` | `ω ↦ π` | `t(n)` |
| `SIM` | take the argmax of `A`'s model of the principal | `Ĵ_n` | `t(n)` |
| `FU[g]` | *not fixed by this version* | — | `g(n)` |

`FU[g]` is a **hole**. The fully-updated comparator needs `A`'s own later
evaluation, which requires an object this skeleton does not carry: a time-indexed
family of `A`-valuations. A track needing it reports the deficiency; the round does
not invent it, because collapsing `FU[g]` into `SIM` by definitional stretching is
forbidden, and careless invention is how that collapse would happen.

`DELEGATE` and `SIM` are the pair the substitution question is about. When
`v̂⁺_n = v⁺_n` pointwise their selections and quantities coincide; their rules still
differ, and whether that difference does any work is the open question, not an
assumption.

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
summing exactly to `1`. The default valuation of a conduct `c` is

```
V_n(c)  =  Σ_{ω ∈ Ω}  P_n(ω) · X_{n, c(ω)}(ω)
```

in exact rational arithmetic. `ε` denotes a nonnegative rational tolerance.

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
   over `N` states its own aggregation.

## 9. Provisional names

`DELEGATE`, `FIXED`, `SIM`, `FU`, `conduct`, `rule`, `selection`, `quantity`,
`well-timed`, `settlement instantiation`, `v̂⁺`, `P_n`, `V_n`. All are this round's
working vocabulary; none is proposed for permanence.

## 10. Version

`v1`, frozen 2026-08-11 at commit `3ad66b0`. A revision is a new version number,
recorded here, with every track that consumed the previous version either rerun or
explicitly reconciled.
