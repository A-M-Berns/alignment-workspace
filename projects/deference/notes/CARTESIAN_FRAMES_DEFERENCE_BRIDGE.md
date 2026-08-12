# Cartesian frames and the deference representation boundary

**Status:** `ci-only`; verification register for
`prompts/2026-08-12-cartesian-frames/`. Names introduced here are provisional.

**Verdict: mixed.** Cartesian frames distinguish execution architectures that the current
deference view identifies, and they represent both ways of losing future corrective agency.
They **fail** on delegation versus accurate simulation: a process that predicts the
principal is identified with delegation, which is the case the obstruction was about. They
supply no jurisdiction object, no valuation and no deference inequality, and they leave
computational futurity where Stage V left it. Within its positive half the result is
representational only — no corrigibility statement follows.

**The round's own adversarial review refuted its first headline** and the document now
states the corrected version; §4b and §5 carry the refutation and what survives it.

## 1. The question, stated exactly

Stage IV's diagnosis is type-level: two authorisation regimes inducing the same
realisation map are the same object in a signature whose only outputs are realisation maps
priced by one measure. Stage V made that conditional statement exact —
`StaticViewFactorization.value_eq_of_price_realization_eq` — over a worked architecture
type whose hidden payload is a `jurisdiction : Bool` field.

The field is the weakness. It shows the factorization boundary exists; it says nothing
about what real structure lives behind it, and a payload that no formula reads is what the
Stage-IV round was criticised for in the first place.

The question this round asks: **is there a mathematical structure, already formalized,
that (i) is erased by the projection the deference valuation takes, (ii) is not a label,
and (iii) is the structure the deference line was reaching for when it said
"jurisdiction"?** Cartesian frames answer yes to (i), qualified yes to (ii), and no to
(iii). §4b states the qualification, which is the round's own adversarial finding.

## 2. Source and Lean surface

The authoritative formalization of the Cartesian Frames paper (Garrabrant, Herrmann and
Lopez-Wild, arXiv:2109.10996) is `CartesianFrames/` in Formalized-Agent-Foundations,
verified at commit `e13dc5bd0117486b1947fbb5643045e14743e98d`, which is now the head of
both `main` and `cartesian-frames-formalization` there. It was an unmerged branch when
this round was dispatched and reached `main` during it. Neither commit is the one
`lean/lakefile.toml` pins, and the pin is a trust-chain value.

Two Lean surfaces therefore exist. Every load-bearing result below holds on both; the
in-repo surface additionally carries `later_commitment_view_blind` and the two-stage
statement, and the cross-check additionally carries `foreclose_subagent` and
`transfer_subagent`, the two `◁` facts §4d cites.

| surface | path | Cartesian-frame definitions | what it proves |
|---|---|---|---|
| in-repo | `lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean` | mirrored, self-contained, no category-theory dependency | 46 declarations, axiom-clean, in the `lean` gate |
| cross-check | `prompts/2026-08-12-cartesian-frames/artifacts/CFCrossCheck.lean` | the authoritative ones: real `≃ᵇ`, `◁`, `◁₊`, `◁ₓ`, `commit`, `externalQuot`, `image` | 35 declarations, axiom-clean, compiled against Formalized-Agent-Foundations |

The mirror's header carries the name-by-name correspondence and the two places its
rendering differs. It proves one direction of Claim 39 (`HomotopyEquiv.of_biextEquiv`),
which is what turns a `¬ HomotopyEquiv` into a `¬ BiextEquiv`; it does not mirror Claim 38,
so its positive results are stated as homotopy equivalences. Its `Iso` constrains only the
agent components, making its `BiextEquiv` weaker than the authoritative `≃ᵇ` and every
`¬ BiextEquiv` it proves correspondingly stronger.

**The cross-check removes both qualifications.** With the real Claim 39 available in both
directions, every positive result below is a genuine biextensional equivalence, every
negation is of the authoritative relation, and every subagency is the real one.

## 3. The construction

One world type for both indices, carrying no controller coordinate:

```lean
structure World where
  executed    : Bool   -- the action actually executed
  disturbance : Bool   -- an exogenous coordinate
```

Five frames over `World`, each the *principal's* frame — agent carrier is the principal's
disposition or corrective choice, environment carrier is everything not the principal's to
choose.

| frame | agent | environment | outcome |
|---|---|---|---|
| `delegated` | `Bool` | `Bool` | `fun h s => ⟨h, s⟩` |
| `simulated h₀` | `Bool` | `Bool` | `fun _ s => ⟨h₀, s⟩` |
| `preserve` | `Bool` | `Bool` | `fun c s => ⟨c, s⟩` |
| `foreclose d₀` | `Bool` | `Bool` | `fun _ s => ⟨d₀, s⟩` |
| `transfer` | `Bool` | `Bool × Bool` | `fun _ p => ⟨p.1, p.2⟩` |

`delegated` and `simulated h₀` share agent carrier, environment carrier and world type.
They differ only in `outcome`, and only in whether it varies with the agent coordinate.

The separating property:

```lean
def AgentInert (C : Frame W) : Prop :=
  ∀ (a₀ a₁ : C.Agent) (e : C.Env), C.outcome a₀ e = C.outcome a₁ e
```

## 4. Results

### 4a. Equal realized play, distinct control structure

`pin C a` restricts the agent coordinate to the choice actually taken.
`pin_biextEquiv_commit` proves `pin C a ≃ᵇ Commit^{a}(C)`, so it is Definition 28's
operation and not a new one.

- **`pin_delegated_eq_pin_simulated`** — `pin delegated h₀ = pin (simulated h₀) h₀`, by
  `rfl`. The perfect simulator agrees with the principal at every environment state, not
  merely on one trajectory.
- **`delegated_not_biextEquiv_simulated`** — `¬ (delegated ≃ᵇ simulated h₀)`, from
  `delegated_not_agentInert`, `simulated_agentInert` and the invariance below.
- **`commitment_view_blind`** — for every world map `p : World → V` and every functional
  `valuation : Frame V → Value`,
  `valuation (mapWorlds p (pin delegated h₀)) = valuation (mapWorlds p (pin (simulated h₀) h₀))`,
  by `rfl`.

**H1 as the dispatch states it is refuted, and the surviving statement is different.**
H1 asks for a coarse *world map* `p°` under which the two frames become equivalent. There
is none that keeps any information about the executed action:
`mapWorlds_delegated_not_biextEquiv_simulated` proves
`¬ (p° delegated ≃ᵇ p° (simulated h₀))` for every `p` separating the executed action at
even one environment state. The projection that does collapse them is
`mapWorlds p ∘ pin` — a world map after a `Commit`, not a world map alone. That §4a's
statement is the one the deference view takes is §7.7's architectural reading, not H1.

**`commitment_view_blind` is the inhabitation witness, not an analogue of the Stage-V
theorem.** The Stage-V theorem has a factorization hypothesis and derives equal value.
This has no hypothesis: the two arguments are literally the same term, so it holds for an
arbitrary `valuation`, invariant or not. It is what makes the Stage-V theorem non-vacuous
at a pair whose hidden difference is structural. The content of §4a is
`delegated_not_biextEquiv_simulated`; the `rfl` is the premise the deference setting
supplies.

### 4b. The hidden-label control, and the argument that fails

`AgentInert` is a biextensional-equivalence invariant
(`AgentInert.iff_of_biextEquiv`, and `AgentInert.of_biextEquiv` on the authoritative
surface): it is a function of `outcome` alone and survives the collapse that deletes
duplicate rows and columns.

**Invariance does not certify that a separation is structural, and the round's first
version of this section claimed it did.** `image` is a `≃ᵇ`-invariant, so any property
reading a world coordinate through `image` is one too. `labelledHuman` and
`labelledAgent` are the adversary: two frames over a world type carrying a `controller`
coordinate, differing only in the value they write there, both agent-active — so
`AgentInert` does no work — and separated at the authoritative `≃ᵇ` by their images alone
(`labelledHuman_not_biextEquiv_labelledAgent`). Item 28's `jurisdiction : Bool`, moved
from the architecture record into the world type, passes every test the first version
used.

**What survives is robustness under world maps, and it is an asymmetry rather than a
criterion.** The label separation is destroyed by the world map that forgets the label and
keeps the executed action: `mapWorlds_forgetLabel` makes the two frames the same object,
by `rfl`. No world map does that to §4a's pair —
`mapWorlds_delegated_not_biextEquiv_simulated` again. A label can be forgotten by a map of
worlds; a dependence structure cannot, because `agentInert_mapWorlds` carries it through
every such map.

So the honest form of the claim is narrower than "not a label":

> `AgentInert` is computed from `outcome`, so unlike an unread architecture field it
> constrains something; and the separation it supports is not destroyed by any world map
> that retains the executed action, which the label separation is.

That is a **structural argument, not a proof**. It does not show that no label can pass
it, and §7.1 records the residue: Cartesian frames do not derive which coordinate belongs
to the agent, so the modeller's choice still does work.

### 4c. Delegation versus accurate simulation: the negative result

`simRead f` executes `f` of the principal's disposition. `simRead id = delegated` and
`simRead (fun _ => h₀) = simulated h₀`, both by `rfl`, so §4a's two arms are the two ends
of one family.

**A process that accurately predicts the principal is not separated from delegation.**
Prediction means the output is a function of the principal's disposition, so it is
`simRead f` for some `f`; and for any `f` whose action on the disposition is invertible
the frame is equivalent to `delegated`. The sharp case is
`simRead_not_biextEquiv_delegated`: a process executing the **opposite** of the
principal's disposition is biextensionally equivalent to delegation. The invariant reads
whether execution *varies with* the principal's coordinate, which is strictly weaker than
tracking it, and provenance — who computed the value — is invisible entirely.

The dispatch's §V asks to separate "H produced the recommendation that controls execution"
from "A accurately predicted what H would have recommended and supplied the same value".
Cartesian frames do not. What §4a separates is the neighbouring case: a process supplying
a **fixed** value that happens to coincide with the principal's actual disposition.

Whether the control reading — a faithful predictor is a channel through which the
principal controls execution, and therefore is delegation — is the one the deference line
wants is an interpretive question it has not settled. Either way the answer to the
dispatch's question as posed is no.

### 4d. Preservation, foreclosure and transfer at a later index

Both present actions execute `d₀`; they differ only in the future frame they induce.

- **`foreclose_biextEquiv_commit`** — `foreclose d₀ ≃ᵇ Commit^{d₀}(preserve)`.
- **`commit_preserve_addSubagent`** — `Commit^{d₀}(preserve) ◁₊ preserve`, the paper's
  Claim 30.
- **`foreclose_not_biextEquiv_preserve`** — the additive subagency is **proper**:
  `¬ (preserve ≃ᵇ foreclose d₀)`. Negative control N5.
- **`transfer_biextEquiv_externalQuot`** —
  `transfer ≃ᵇ External^{/⊤}(preserve)` at the one-cell partition.
- **`externalQuot_preserve_multSubagent`** —
  `External^{/⊤}(preserve) ◁ₓ preserve`, the paper's Claim 34/45.
- **`later_commitment_view_blind`** — the preserve/foreclose pair reproduces §4a's
  blindness at the later index.

H3 and H4 both confirmed. **What the two subagency facts do and do not carry:**
`Commit^B(C) ◁₊ C` holds for every `C` and every `B`, and `External^{/s}(C) ◁ₓ C` for
every `C` and every `s` — they are the library's Claims 30 and 34/45 at arbitrary
arguments and say nothing specific about these arms. The content is on the other side: the
`≃ᵇ` statements identify which operation each arm *is*, and `¬ (preserve ≃ᵇ foreclose d₀)`
makes the additive subagency **proper**, which no schema supplies. Both arms are subagents
of `preserve` (`foreclose_subagent`, `transfer_subagent`), so Theorem 24 applies — but
each is already `◁₊` or `◁ₓ`, so the factorization it produces is the trivial one and the
invocation carries nothing.

**The two indices in one object.** `PresentAction` has the three constructors,
`presentStage` is the present frame over the same `World`, and `futureFrame` is the map
from a present action to the corrective frame it leaves. Then:

- **`presentStage_agentInert`** — at the present index the three actions are
  indistinguishable, and not merely in their executed action: the present frame is inert.
- **`futureFrame_separates`** — the three induced future frames are pairwise
  non-equivalent.

Cartesian frames have no time index. `presentStage` and `futureFrame` are two frames and a
function between an action type and frames; that the second is "later" than the first is
stipulated by the model, not derived. §7.3 and the computational-futurity row of §6 are
where that limit is accounted for.

### 4e. The invariant separating restriction from externalization

Both arms leave the principal's agent coordinate inert. They differ in `image`:

| | agent coordinate | reachable worlds |
|---|---|---|
| `Commit^{d₀}` (additive) | inert | shrink — `foreclose_image_ne_preserve` |
| `External^{/⊤}` (multiplicative) | inert | preserved — `transfer_image` |

Hence `foreclose_not_biextEquiv_transfer`: the two operations are not interchangeable
models of losing corrective agency. Under commitment the reachable set shrinks; under
externalization it does not.

**Who exercises the transferred coordinate is not in the model.**
`transfer_biextEquiv_exogenous` proves `transfer` equivalent to a frame with a one-point
agent carrier in which the executed coordinate is simply part of the environment. A frame
has no notion of *whose* environment state a coordinate is, so "another process now
decides" and "the coordinate is exogenous" are the same object here. §7.2's concession
that control is not authorisation applies to the environment side too.

Two further limits. The shrinkage in the table is a fact about the set committed to, not
about `Commit` — committing to everything preserves the image. And only the one-cell
partition is exhibited: partial externalization, where the principal keeps part of the
coordinate, is not constructed.

## 5. Negative controls

| control | outcome | evidence |
|---|---|---|
| N1 hidden-label cheat | **the invariance argument fails**; a weaker world-map argument survives | `labelledHuman_not_biextEquiv_labelledAgent` is the adversary that passes the first test; `mapWorlds_forgetLabel` and `mapWorlds_delegated_not_biextEquiv_simulated` are the asymmetry that survives. §4b |
| N2 duplicate-behaviour collapse | survives | separation is at `≃ᵇ`, which is collapse-invariant by construction |
| N3 perfect simulator | **fails for a predictor**; survives for a fixed coinciding value | `simRead_not_biextEquiv_delegated` — even an *inverting* process is equivalent to delegation. `pin_delegated_eq_pin_simulated` covers only the constant arm. §4c |
| N4 trivial future frame | survives | `preserve_not_agentInert` — the preserved arm's choices move the world after collapse |
| N5 foreclosure by notation | survives for `Commit`; **fails for the reading of `External`** | `foreclose_not_biextEquiv_preserve` — `Commit` changes the frame, not only its type. But `transfer_biextEquiv_exogenous` shows `External^{/⊤}` does not distinguish a second agent from an exogenous coordinate. §4e |

## 6. Which obstructions this addresses

| deference obstruction | addressed? | how | remaining debt |
|---|---|---|---|
| same realisation, different jurisdiction | partial | architectures agreeing on the realized play separated by a property of `outcome` whose separation no world map deletes | Cartesian frames represent **control**, not **authorisation** (§7.2); needs agent-side counterfactual variation the current signature lacks (§7.3); invariance alone does not exclude labels (§4b) |
| delegation vs accurate simulation | **no** | a predictor is identified with delegation, and so is an inverter | only a fixed coinciding value is separated (§4c); whether the control reading is the wanted criterion is unsettled |
| future agent absent from model | partial | the future principal's corrective frame is a first-class object with three constructed arms | Cartesian frames have no time index and no transition; "later" is stipulated, and the interface is still one index deep |
| foreclosure absent from signature | yes, at representation | `Commit` and `External^{/}` with proper additive subagency and an `image` separator | no valuation, no inequality; the English reading is architectural (§7.4); the holder of a transferred coordinate is not represented (§4e) |
| capability/admissibility conflation | no | — | the agent carrier conflates what the principal *can* do with what it *may* do |
| computational futurity | no | — | Cartesian frames are resource-free; every frame here is presently computable. Q4 untouched |
| competence / calibration | no | — | no epistemic content in the formalism |
| near-indifference leakage | no | — | item 25 untouched |

**Nothing in Stage III–V is refuted or weakened.** The Stage-V factorization theorem
stands exactly as stated; what changes is the diagnosis of what its projection erases.

## 7. What this does not establish

### 7.1 Cartesian frames do not derive who the agent is

Which degree of freedom sits on the agent side of the principal's frame is written down by
the modeller. Cartesian frames take "whose frame is this" as given. The improvement over
the item-28 worked case is real but bounded: `jurisdiction : Bool` is a payload no formula
reads, while the agent/environment split determines an entire counterfactual structure
that survives every world map. **A label with mathematical consequences is not the same as
a derived object**, and §4b shows that invariance alone does not even establish the first
half.

### 7.2 Control is not authorisation

`AgentInert` measures counterfactual power. A frame in which an unauthorised process holds
the agent coordinate is indistinguishable from one in which a rightful principal does.
Jurisdiction — normative authority — is not supplied. What is supplied is the thing
jurisdiction is *about*. This is why the verdict is not simply CF-positive.

### 7.3 The separation requires counterfactual variation the current signature lacks

Every separation here lives in the column where the principal's disposition differs from
the one actually held. The deference model's realisation map `Ω → A` is already the
post-commitment object: the agent's counterfactual coordinate has been quotiented away
before the valuation sees anything. Cartesian frames do not repair the Stage-V negative;
they say precisely what must be added to the type for the distinction to exist at all.

### 7.4 `Commit` and `External` are not thereby definitions of foreclosure

What is proved is that the foreclosed frame *is* the commitment of the preserved one and
the transferred frame *is* its externalization, and that the two are not interchangeable.
That these operations deserve the English word "foreclosure" is an architectural reading.
The subagency half of each identification is a universal schema (§4d), and the
externalization arm is reachable without `External` at all — the whole `≃ᵇ`-invariant
content of the contrast is `image`.

### 7.8 There is no transition, and the interface is still one index deep

`presentStage` and `futureFrame` are a frame and a function; nothing makes the second
later than the first, and no operation reassigns anything at a later index. Q3 names two
holes — an operation that reassigns the authorization relation later, and the interface's
depth — and this round closes neither. It supplies a candidate object for *what is lost*,
not for *how a present act loses it*.

### 7.5 No normative premise is supplied or assumed

Nothing here says preserved corrective agency is preferable. `AgentInert` and `image` are
descriptive invariants. Adding a valuation that rewards preserved agency would be a value
premise, and this round adds none.

### 7.6 `AgentInert` is binary

It is the degenerate case, sufficient for these witnesses and not proposed as a measure. A
graded invariant of corrective agency is not developed.

### 7.7 `pin` as a model of the deference view is an interpretation

`pin C a ≃ᵇ Commit^{a}(C)` is proved. That the current signature's `(P, r)` is exactly
`mapWorlds p ∘ pin` is not; it is the architectural reading that makes §4a relevant to
item 28.

## 8. Evidence classes

| result | class |
|---|---|
| every declaration in `CartesianFrameBridge.lean` | Lean-established, axiom-clean, unregistered |
| every declaration in `artifacts/CFCrossCheck.lean` | Lean-established against the authoritative library, unregistered, outside the `lean` gate |
| Claims 30, 34/45, 39, Theorem 24 as used | source-theorem fact |
| H1 as the dispatch states it, over a world map alone | **negative result** — `mapWorlds_delegated_not_biextEquiv_simulated` |
| delegation separated from accurate simulation | **negative result** — `simRead_not_biextEquiv_delegated` |
| `≃ᵇ`-invariance certifies a separation as non-label | **negative result** — `labelledHuman_not_biextEquiv_labelledAgent` |
| the world-map asymmetry as what survives that | structural argument, not a proof |
| the frames as models of the architectures they are named for | architectural interpretation |
| `mapWorlds p ∘ pin` as the current deference view | architectural interpretation |
| the LI observables as functionals of the committed view | architectural interpretation |
| Cartesian frames cannot express authorisation | structural argument, not a proof |
| partial externalization behaves as the one-cell case does | open |
| a graded invariant of corrective agency | open |

## 9. Next target, and what it would close

**Dispatchable, and it is a re-instantiation rather than a new theorem.** Restate the
Stage-V factorization over a signature carrying a frame and the choice actually taken —
`(price, C : Frame W, a₀ : C.Agent)` — in place of `(price, realization, jurisdiction)`.
The statement is `value_eq_of_price_realization_eq` instantiated at
`realization := fun A => mapWorlds p (pin A.C A.a₀)`, with `commitment_view_blind` as the
inhabitation witness; both are already proved, so there is no new mathematical content.
What changes is the witness: the hidden payload becomes a named structure that constrains
something instead of a field no formula reads. Worth doing for that reason and not for a
theorem.

**Not yet dispatchable.** A graded `≃ᵇ`-invariant of corrective agency, and whether
`Commit` and `External^{/}` move it monotonically. Q3-level: the shape is unknown.

**Finite factored sets are not indicated.** The missing structure §7.3 names is an
agent-side counterfactual coordinate in the deference signature, and Cartesian frames
already supply it. Escalating to a second formalism before the signature change of the
dispatchable target is tried would be reaching past an available answer.
