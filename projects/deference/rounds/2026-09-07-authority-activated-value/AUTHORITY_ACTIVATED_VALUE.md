# Authority-activated value

**Status:** `ci-only`; verification register for
`prompts/2026-09-07-authority-activated-value/`.  Lean:
`lean/Workspace/Deference/Contrib/ActivatedValue.lean` (the algebra) and
`lean/Workspace/Normativity/Contrib/AuthorityActivation.lean` (the activation
semantics).  Fixtures: `src/`, `tests/`.  Names are provisional.

Evidence labels: **LEAN** kernel-checked here; **FIX** exact finite fixture in
`tests/`; **PAPER** inherited from the pinned Logical Induction dependency or the
inherited deference algebra; **EXT** external semantic or protocol assumption;
**OPEN** unresolved.

## 1. Types

Notation: `𝔼ⁿ` is the novice's day-`n` expectation (the present principal-side
market), `𝔸ⁿ` the advisor's, `h_m` the authenticated history prefix at time `m`,
`O_m` the accounted obligation state at `h_m`.  The prompt writes `H_n` for both the
expectation and the history; the two are separated here.

| object | type | fixed at issuance | may evolve later |
|---|---|---|---|
| `o_n` | `Occ` — the occurrence identity | yes | never |
| `r_n = anchor o_n` | `EvalReq = (ρ_P, α_n, Q_n, s_n, τ)` | yes | never (it is the anchor) |
| `ρ_P` | principal role / authority identity | yes | the *holder* of the role may change by authorized succession; the role does not |
| `α_n` | the matter evaluated | its identity, yes | its representation, by an authorized `LocalLaw` (re-representation) |
| `Q_n` | finite candidate set, by identity | yes | candidate *semantics* may be transported by an authorized law; candidate *identity* never; a change of set is a fresh occurrence (§6) |
| `s_n` | designated evaluation slot | yes | rescheduling is an authorized `LocalLaw` whose child carries `s' ≠ s_n`; visible in the account |
| `τ` | output type: `V : Q_n → [0,1] ∩ ℚ`, plus a process receipt `ρ` | yes | never |
| `e_n` | the answer event at the slot; payload `(V_n, ρ_n)` read from `h_m` | — | — |
| `P⁺` | the actual future principal, after interacting with `A` | — | epistemic state, deliberation, representatives, tools, assistance: all free, provided each change is itself authorized |

Nothing on the right-hand column is a new primitive: each is a `LocalLaw` in
`OccurrenceIntegrity.Program.combine`, authorized under a warrant in force at a strict
prefix, and the account records it.  The invariants on the left are exactly what the
`anchor` map fixes.

**The evaluation requirement** is the anchor of an ordinary occurrence.  An
`EvalReq` adds no constructor to the protocol; it is one value of `Req`.  What makes
it an evaluation requirement is the protocol's `AnswerOK` for that value (§3).

## 2. The activation event

For the account `T = O_m.account o_n` of the occurrence at `h_m`:

```
C_n(h_m) := activated T ∧ LegitimateFor(o_n, Γ_n; O_n, O_m)
activated T := (T.fates = {answered})
```

`activated` is `OccurrenceIntegrity.Program.activated` (**LEAN**): the fate multiset is
exactly one authenticated answer leaf.  Consequences, all **LEAN**:

- an answer leaf activates; a closure leaf does not; a live leaf does not
  (`answer_activated`, `close_not_activated`, `live_not_activated`);
- any account containing a live or closed leaf is not activated
  (`not_activated_of_live_mem`, `not_activated_of_closed_mem`); so
  `answered → activated`, `closed → no activation`, `live → no activation` is the
  three-fate calculus read directly, with no new clause;
- a unary law (carry, re-representation, rescheduling) is transparent
  (`combine_zero_fates`);
- two answer leaves (a split law answered twice) do not activate: "exactly one";
- **the first answer binds**: an account with no live port is unchanged by every
  further step (`fates_subst_of_terminal`), so activation, once true, persists along
  every step (`activated_subst`) and no second receipt can enter.

`LegitimateFor(o_n, Γ_n; O_n, O_m)` is `AuthorityActivation.LegitimateForSegment Γ_n`
(**LEAN**, §5 of `INTERFACE_WITH_LEGITIMACY.md`): the Integrity evolution from `O_n`
to `O_m`, open at every state for the concerns `Γ_n` the application declares relevant
to the evaluation.

**The value vector.**  The answer leaf's receipt carries `event : ℕ`, the history
position of the answer.  `V_n := payload(h_m, event)` is read off the authenticated
history at that event.  The account does not store the payload and does not need to:
it stores which event is the answer, and the history is append-only.  That the
payload at that event is what `P⁺` committed to is the semantic-authentication input
the generic theory already names (**EXT**).

## 3. Adequacy of an evaluation answer

The protocol predicate `AnswerOK h r w` for `r = EvalReq(…)` is declared as

```
AnswerOK h r w  :=  SessionOK(h, s)  ∧  ProcessCert(h, r, w, ρ.proc)  ∧  Bind(ρ.key, V)
```

with `ρ = (ρ.proc, ρ.key)` the process receipt at the answer event.

- `SessionOK`: the answer event is at the designated slot (or at the slot an
  authorized rescheduling law moved it to — the law is in the account).
- `ProcessCert`: the process receipts hold.  Reads `ρ.proc` and the history; does
  **not** read `V`.  Its content is §4.
- `Bind`: `ρ.key` is a commitment by the holder of `ρ_P` to exactly `V`.

**Epistemic neutrality (LEAN, `Neutral.certifiable_iff`).**  With `ProcessCert` blind
to the payload and `Bind` total (the principal can commit to any vector),

```
(∃ ρ, Cert ρ V)  ↔  ∃ π, ProcessCert π
```

so certifiability of the occurrence is a property of the process alone, and
`Neutral.certifiable_congr`: two payloads are certifiable or not together.  The
certificate cannot be literally value-independent (the signature is over `V`); what is
value-independent is *whether a certificate exists*.  This is the strongest
factorization statement that is true, and fixture **B** is what fails without it: a
certificate that inspects `V` turns activation into a selection on the payload and
flips the argmax (`COUNTERMODELS.md` §B).

The totality of `Bind` is a requirement on the commitment scheme (**EXT**).  A scheme
under which some vectors cannot be committed is a value-dependent certificate by
another name.

## 4. The process certificate

`ProcessCert` is the place for the authorship contract.  It is typed here and not
solved.  Its clauses are receipts of protocol events, each verifiable against `h_m`:

| clause | receipt | what it rules out |
|---|---|---|
| designated session | the answer event sits in the session the anchor names | cherry-picking (fixture **C**) |
| no-preview | the commitment `ρ.key` is timestamped before the reveal of `𝔸`'s selection and quotes for `o_n` | the self-referential menu (fixture **I**) |
| no direct write | no event in the session is a write to the principal's preference state by `A` | substitution of authorship |
| no coercive channel | the session's channel class is in the declared admissible set | coercion |
| assistance allowed | authenticated evidence, proofs, ordinary argument from `A` are admissible session events | nothing — this is what makes `P⁺` AI-informed rather than isolated |

**What `ProcessCert = 1` means.**  That these receipts are present and authentic.
**That the resulting `V` is P-authored** — that a principal who read `A`'s evidence
and changed their mind radically is still the author of their conclusion — is
**EXT**: it is the same kind of assumption as "`Admitted` means admitted", and the
generic theory leaves it external on purpose.  The prompt's phrase "genuinely
P-authored" is not derived here and is not claimed.

The no-preview clause is narrow.  It seals the exact self-referential object (the
selection and quotes for this occurrence) from the session before the commitment; it
does not isolate `P⁺` from `A` in general.  Its mathematical role is §3 of
`LI_DEFERENCE_COMPOSITION.md`: it is the admissible-domain condition of the
inherited Value theorem, realized as a receipt.

## 5. The activated securities

```
U_{n,a} := C_n · V_n(a),     a ∈ Q_n
```

In the pinned dependency a `[0,1]`-valued security is a `LUV`, a family of threshold
sentences `X.gt r = ⌜X > r⌝` (`Framework/Expectations.lean:58`), with expectation
`expectApprox V k X = (1/k) Σ_{i<k} V(X.gt (i/k))` (`def:e`).  So the activated
security is the LUV

```
U_{n,a}.gt r := C_n ∧ (V_n(a) > r)      (r ≥ 0);   U_{n,a}.gt r := ⊤  (r < 0)
```

and the threshold securities `S_{n,a,r} = 1[C_n ∧ V_n(a) > r]` the prompt names are
exactly its threshold sentences.  No arbitrary-real-valued security is needed.
`expectApprox` reconstructs `𝔼[C_n V_n(a)]` within `1/k` (**FIX**,
`TestReconstruction`; it is the LUV definition's own grid error, **PAPER**).

Both `C_n` and `V_n(a) > r` are sentences about `h_m`: they settle when the history
reaches `m` and the deductive process reports the verifier's output (§7).  The menu
`{U_{n,a}}_a` is efficiently computable as syntax when `o_n`, the verifier and the
slot are (they are fixed data).

**Common activation.**  One `C_n` for the whole menu.  With `mass = 𝔼[C_n]`:

```
𝔼[U_{n,a}] − 𝔼[U_{n,b}] = 𝔼[C_n · (V_n(a) − V_n(b))]                   (pairwise, LEAN)
𝔼[U_{n,a}] ≤ 𝔼[U_{n,b}]  ↔  𝔼[V_n(a) | C_n] ≤ 𝔼[V_n(b) | C_n]   when mass > 0  (argmax_iff, LEAN)
```

so the activated argmax is the conditional argmax: deference is to the future
principal's evaluation on the certified branch and to nothing else.  The void branch
is comparison-neutral because every candidate cancels to the same payoff there.  With
per-candidate activation this identity fails (`PerAction.argmax_breaks`, **LEAN**;
fixture **D**): the selection then mixes valuation with certifiability, a channel `A`
can act on.

## 6. The availability transfer theorem

Let `V_n(a) ∈ [0,1]`, `η_n ≥ 𝔼ⁿ[1 − C_n]`, and let `Ŝ_n` be the followed strategy —
a world-dependent probability vector over `Q_n`, covering the hard selector `â_n(w)`
and the soft mixture.  If activated regret is at most `ε_n`,

```
∀a.  𝔼ⁿ[U_{n,a}] − 𝔼ⁿ[Ŝ_n^U] ≤ ε_n
```

then unactivated regret against the actual future principal's evaluation is

```
∀a.  𝔼ⁿ[V_n(a)] − 𝔼ⁿ[Ŝ_n^V] ≤ ε_n + η_n .
```

**LEAN** `availability_transfer` (fixed selection), `availability_transfer_strategy`
(followed strategy), `availability_transfer_range` (payoffs in `[L, L + D]`: `ε + D·η`).

**The constant is `1`, not `2`.**  `V − U = (1 − C) V`, so a competitor's excess over
its activated value is at most `1 · 𝔼[1 − C]` and the selection's excess is at least
`0`; only one side spends the void mass.  `Sharp.transfer_sharp` (**LEAN**) attains
`ε + η` with `ε = 0`: activated and void worlds, the candidates tie on the activated
branch, and differ by `1` on the void one.  So `ε + η` is exact and `ε + 2η` is not
needed.  For a general range `D` the sharp constant is `D`.

**Asymptotic form.**  `availability_transfer_asymptotic` (**LEAN**) is the same
inequality over real sequences in the dependency's `≲ₙ`, with the two pointwise
facts `0 ≤ V − U ≤ 1 − C` entering as the named hypotheses that linearity of
expectation and provability induction supply in the LI reading (**PAPER**, the same
two inputs `value_asymptotic` uses).

**Selective failure.**  `A` may steer `C_n = 0` exactly on the branches where `P⁺`
would disagree.  The theorem does not assume independence of `C_n` and anything; the
bound is algebra in one common event.  Fixture **G** realizes the attack and attains
the bound exactly: the damage is `η_n · D`, no more.  So the question "is high
availability sufficient?" has the answer: **yes, and the damage of selective failure
is exactly the void mass under the novice's own expectation.**  What this requires is
that `η_n = 𝔼ⁿ[1 − C_n]` be small *whatever `A` selects* — availability is a property
of the ecosystem's answering behaviour, not of `A`'s policy, and a novice calibrated on
`C_n` prices selective failure at its frequency (§7).  No conditional-independence
machinery is introduced.

**Vacuity.**  `C_n ≡ 0` gives activated regret `0` for every selection (`vacuous`,
**LEAN**) and `η_n = 1`; the transfer bound reads `ε + 1` and says nothing.  A
certified-deference claim without an availability certificate is empty (fixture
**F**).

## 7. Operational `C_n`

`C_n` is proof-carrying.  The bundle `B_n = (V_n, ρ_n, segment, openness data)` is the
certificate itself: the transition chain from `O_n` to `O_m` (an `Evolution`, whose
target accounts are *computed* by propagation, not chosen), the per-state openness
data for `Γ_n` from the application's semantics, and the receipt data.  The verifier

```
VerifyEval_n(h_m, B_n) := decide (activated (propagate segment (O_n.account) o_n))
                          ∧ decide (AllStates (OpenAtFor Γ_n sem) segment)
```

is a decidable computation on finite data (`Decidable (OpenAtFor …)`, **LEAN**;
`activated` is a `Bool`).  Soundness is by construction: `VerifyEval_n = 1` *is* the
existence of the answer receipt, of the segment, and of the openness certificate,
because the bundle is the Lean term.  What is external is that the protocol predicates
in the receipts mean what they say (**EXT**, the generic theory's standing input).

**Availability, in the LI sense.**  `C_n` is an atom about `h_m`; it enters the
deductive process by feedback when `h_m` is reached.  Two regimes:

- *All certified.*  If every `C_n` settles true and the sequence of sentences is
  efficiently codeable, `lic_provind_true` (`Properties/AffineCoherence.lean:888`,
  **PAPER**: `hthm : ∀ n, ∃ k, φ n ∈ DP.D k`) gives `𝔼ⁿ[C_n] → 1` pointwise, whatever
  the delay of each settlement.  Then `η_n → 0` and unactivated regret `≲ ε_n`.
- *Mostly certified.*  If a positive fraction fails, only averaged statements are
  available from the dependency (`lic_wub_ofComputation_unconditional`, **PAPER**,
  weighted signed bias), and the transfer theorem should be read with `η_n` the
  novice's actual price, which is what the algebra uses.  A pointwise rate is
  **OPEN** and is not needed for the statement.

**That the ecosystem answers** — that `P⁺` sits the designated session and commits,
that the lineage stays open on `Γ_n` — is not a theorem of anything here.  It is the
residual bridge, filed as `PRIORITIES.md` item 87.

## 8. The end-to-end statement

```
Value_{H→A} on {U_{n,a}}          (PAPER: tower on U + novice expprovind; scope: no-preview)
   ⇒  ∀a. 𝔼ⁿ[U_{n,a}] − 𝔼ⁿ[Ŝ_n^U] ≲ₙ 0                                  [ε_n → 0]
+  𝔼ⁿ[1 − C_n] ≤ η_n              (availability; PAPER via provind when all certified)
   ⇒  ∀a. 𝔼ⁿ[V_n(a)] − 𝔼ⁿ[Ŝ_n^V] ≲ₙ η_n                                  [LEAN transfer]
+  η_n → 0
   ⇒  the novice expects following A to do as well, by the actual AI-informed
      principal's certified evaluation, as any fixed candidate.
```

No reference evaluator appears.  No property of a human who did not interact with `A`
is used.  The future evaluation is not required to resemble the present one.  The
certificate never inspects `V`.  `closed` never activates.  No endpoint certifies its
own authority: every receipt's authority is a fresh event at a strict prefix under a
warrant in force there (`OccurrenceIntegrity.Authority`).

## 9. What is not established

- That any process satisfies `ProcessCert`, or that satisfying it makes `V` P-authored
  (**EXT**).
- That the tower `Mart_{H→A}` holds on the activated menu; it is the deference
  hypothesis of the inherited theorem, not discharged here (**PAPER**, conditional).
- That `η_n → 0` for any realized ecosystem (**EXT**; item 87).
- Anything about a menu whose candidate set changes between `n` and `m` (§1: a fresh
  occurrence), about multi-parent aggregation laws (not expressible in the calculus,
  as `OccurrenceIntegrity.lean` records), or about a principal role whose succession is
  contested.
- A pointwise availability rate in the mostly-certified regime (**OPEN**).
