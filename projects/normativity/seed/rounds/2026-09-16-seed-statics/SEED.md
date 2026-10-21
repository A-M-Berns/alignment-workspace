# The seed as a typed object

Lean: `lean/Workspace/Normativity/Contrib/SeedStatics.lean` §§1–2, §9, §11.  Executable:
`src/seed.py`.  Every name here is provisional.

## 1. Fragment, settlement, specialization

A fragment of dimension `d` is `Fin d` with rational prices in `[0,1]^d`.  A **settlement**
`F : Settlement d` is `val : Fin d → Option Bool`; a price vector is **pinned** by `F` when
it agrees with `F` on every settled coordinate.  `F.le F'` is inclusion with compatible
valuations.

A row is the compiler's `Row d` (`a · x ≤ b`).  **Specialization** substitutes the
settled coordinates:

    specialize F r = ⟨ (i ↦ if settled i then 0 else a i),  b − Σ_{settled i} a i · truth (F i) ⟩

`specialize_sat_iff`: on the pinned slice the specialized row and the original row say
the same thing.  The pin rows `x i ≤ v`, `−x i ≤ −v` of every settled coordinate cut the
pinned slice out of the cube (`pinRows_sat_iff`).

## 2. The three layers

| layer | Lean | what it holds | how it leaves |
|---|---|---|---|
| substantive `S_sub` | `SubItem` = `Form` + `port` | a leverage form `premise X c` (`P(X) ≥ c`), `applicability X XA c` (`P(X∧A) ≥ c·P(X)`), `strength XA XAY c` (`P(X∧A∧Y) ≥ c·P(X∧A)`), each with strength `c` | a defeater landing on its port (`DocketState.defeated`) |
| structural `S_str` | `StrItem` = `Row` + `StrKind` + `id` | a raw row of strength one, declared `dominance`, `impartiality` or `coherence` | a surface-change occurrence naming its id (`DocketState.withdrawn`) |
| constitutive `S_con` | `Constitutive` = `standing : Finset A` + `protectedClass : Finset (Fin d)` | the declared standing set and protected class | not by the reasoner (declared data; see `ALIGNMENT_READING.md`) |

A warrant `ρ : α ⇝ β` with applicability `A_ρ` is the triple of forms on `X = α`,
`X∧A`, `X∧A∧Y`; the fixtures compile it that way and canonicalize settled conjuncts
away (`FIXTURES.md` §1).

The two withdrawal channels are separate by construction: `liveStr_indep_defeat` (a docket
defeat never reaches a structural item) and `liveSub_indep_withdraw` (a surface change
never reaches a substantive item) are both `rfl`.  "Revisable by counterexample" is the
second channel; nothing in this round says *which* counterexamples license a surface
change.

## 3. Humility

Three predicates, kept apart because the round found they behave differently:

- **Item-level humility** `Seed.HumbleItems`: every substantive strength lies in `(0,1)`.
  Decidable.  This is the prompt's humility, and it does **not** prevent the substantive
  layer from pinning a coordinate (`CONFINEMENT.md` §3, `c3_refuted`).
- **Level neutrality** `Seed.LevelNeutral`: the structural layer alone — no substantive
  item, no warrant, quiet docket, empty settlement — bounds no coordinate away from
  `[0,1]`.  Stated as a Prop over valid bounds; decided in the fixtures by two LPs per
  coordinate; a bound certificate with positive lower value is a witness against it.
- **Strict humility** (`CONFINEMENT.md` §4): a substantive item is *strict* when its
  endorsement is the open halfspace `μ(g) > 0`.  This is the hypothesis under which
  seed-independence on the point-forced fragment holds (`seed_independence_strict`).

`Seed.Humble := HumbleItems ∧ LevelNeutral`.  Witness: `emptySeed_humble`;
`sandwichSeed_humble` is item-humble and pins.

### The non-dogmatism criterion for structural items

A structural item is **substantive in disguise** when it narrows a level.  The checkable
criterion is level neutrality, and it catches the pressure test's disguise: impartiality
`P(φ) − P(¬φ) = 0` together with coherence `P(φ) + P(¬φ) = 1` forces `P(φ) = 1/2`, and
`disguise_caught` exhibits the lower bound `1/2` (Lean) — `src/fixtures.py::disguise`
computes both intervals as the point `1/2`.

What it cannot catch, recorded rather than hidden:

1. **Relational disguises.**  `P(x) − P(y) = 0` on two unrelated sentences narrows no
   level, so level neutrality passes it.  The only further check is *symmetry
   generation* (`symmetry_generated`): every impartiality row must be `P(s) = P(σ s)` for
   the declared symmetry `σ`.  Under the identity symmetry the row is caught; under a
   declared swap `x ↔ y` it passes.  The content has moved into the declaration of `σ`,
   which is the constitutive layer's, not checkable inside the statics.
2. **Symmetry plus completeness narrows a level.**  On the moral fixture, impartiality on
   the mirror pair `r(a,b) = r(b,a)` together with completeness `r(a,b) + r(b,a) ≥ 1`
   forces both to `[1/2, 1]`; level neutrality flags it, symmetry generation passes it.
   So the combined criterion is: *every level narrowing by the structural layer is
   attributable to a declared symmetry*, checked by running level neutrality on the
   structural layer with the symmetry-generated rows removed
   (`level_neutral_violations_without_impartiality = {}` on the fixture).

The criterion therefore catches every disguise that is not licensed by a declared
symmetry, and cannot adjudicate the symmetry declaration itself.

## 4. The transport rule

A refinement is a map `ρ : Fin d → Fin d'` from old coordinates to new.  **Transport**
reindexes a row along it:

    transport ρ r = ⟨ (j ↦ Σ_{i : ρ i = j} a i),  b ⟩

`transport_sat_iff`: `(transport ρ r).Sat x' ↔ r.Sat (x' ∘ ρ)` — the transported row
holds at new prices exactly when the old row holds at the pulled-back prices.

The **conservative transport** `τ` sends each old sentence `p` to the coordinate of its
disjunction `p₁ ∨ … ∨ p_k` in the new fragment, which the new fragment's coherence rows
tie to the refinements (`p = p₁ + p₂` for exclusive halves).  A **narrowing** transport
sends `p` to one refinement.  Both satisfy `transport_sat_iff`; they differ in `ρ`, and
the fixture `refinement` shows the split: with `P(p) = P(q)` structural and `q` pinned at
`1/2`, conservative transport leaves `p₁ ∈ [0, 1/2]` while narrowing pins `p₁ = 1/2` and
widens `p` to `[1/2, 1]`.  Two reasoners with one seed and different transports have
different forced regions; with both on `τ` they coincide (`both_tau_equal`).

Nothing here says when a refinement occurs or who declares `ρ`; the rule is what
endorsements become once it has.
