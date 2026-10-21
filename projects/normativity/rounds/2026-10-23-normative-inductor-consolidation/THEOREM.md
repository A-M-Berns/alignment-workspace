# The warrant Normative Inductor — statement and assumption ledger

Every named object is a declaration under `lean/Workspace/Normativity/Contrib/`; the theorem is
`WarrantInductor.warrant_inductor`, its two runs `WarrantInductorWitness.inductor` and
`WarrantInductorRebuttal.inductor`.

## The statement

**Setting.** A fragment of `d` sentences, coordinate `j` priced as `ι j` (`ι` injective). A
deductive process `DP`. For each date `n` a **normative state** `N n`: grounds `G_n` (typed
warrant occurrences — premise `P(X) ≥ c`, applicability `P(X∧A) ≥ c·P(X)` citing a premise,
strength `P(X∧A∧Y) ≥ c·P(X∧A)` citing an applicability — each with an identity, a citation and
a defeat set), a docket, a settlement, structural rows, and the events the record authorizes.
Its **survivors** `S_n` are the least fixed point of the grounded step: not undercut by the
docket, kept by the settlement (not retired, vacuous or rebutted), citing a survivor. Its
**bundle** `B_n` is the survivors' rows specialized by the settlement, the live structural rows
and the settlement's pins, each cited by its producer; `K_n`, the region, is the set of price
vectors in the cube satisfying every row. The compiler returns `r_n` — a witness, a Farkas
conflict certificate, or nothing — and the date's **outcome** is *idle* (`B_n = ∅`), *enforced*
(the witness checks into `K_n`; every row held) or *withheld* (rows present, no checked
witness; `r_n` carried). The **enforcer** holds, on each held row, a position proportional to
the row's violation at the displayed price, at intensity `κ_n = (ε_n + A_n)/tol_n²`, and the
**market** `P` is the deductive process's source firm priced together with it.

**Theorem** (`warrant_inductor`). Let an accounted obligation state `O` and a relation
`Expresses : Req → Form → Prop` be given, and assume:

- **H1 (entitlement, well-formedness).** For every `n`, an `Entitlement O G_n Expresses`: a map
  from occurrences to exposed obligation occurrences of `O` such that each origin is admitted by
  the protocol at `O`'s history, its account carries a live leaf, and the occurrence's form
  expresses the origin's anchor. Identities in `G_n` are unique and citations resolve.
- **H2 (computability).** `DP` is computable; the enforcer's trade map is effective.
- **H3 (affordability).** A constant `B` with `−B ≤` the enforcer's net worth at every world
  plausible at date `n`, for every `n`.
- **H4 (the services).** An adapter protocol — service dates, an evaluation measure `μ` and a
  transport plan `T`, per service a finite menu `Q` scored by affine functionals of the displayed
  prices, a declared adequate set `A_s` with margin witnesses `A₁ ⊆ A_s`, a positive preference,
  threshold `τ`, ramp `δ`, witness mass `W` — such that every service date is *enforced*, each
  inadequate response has an upper certificate on `B_s` with `offset + value ≤ τ` (`Excludes`),
  and each margin witness a lower certificate with `τ + δ ≤ offset − value − mass·tol_s`
  (`Margins`).
- **H5 (adequacy).** Anchored losses `lam r s q` with `lam ≤ εad_s` on `A_s` and `lam ≤ D`.
- **H6 (constants).** `lamS ≥ 0` with positive sum; `lamS_s·(massCap_s·tol_s)² ≤ ρ_s`;
  `Σ_e T(e,s)·D·κ_s ≤ Γ·lamS_s/Σ lamS`, where `κ_s = (Σ_{q∉A_s} pref q)/(W δ)` and
  `massCap_s` is the inadequate responses' certificate mass.

Then:

1. **Logical Induction.** `P` is a logical inductor over `DP`.
2. **Conformance and provenance.** At every enforced date, every row of `B_n` has excess at most
   `tol_n` at the displayed price. Every held substantive row is the row of an *entitled*
   survivor whose citation names exactly one survivor; every other held row is a structural row
   or a pin.
3. **The adapter.** At every service, the gate's mass on inadequate responses is at most
   `κ_s · defect_s`, and `defect_s ≤ massCap_s · tol_s`, where `defect_s` is the displayed
   inadequate excess `Σ_{q∉A_s} (score_q − τ)⁺`.
4. **Progress.** `progress ≤ Γ √(Σ ρ_s / Σ lamS_s) + Σ T ε + D · residual`, with the uptake
   package derived from 2 and 3.

**What is substantive.** Nothing above is a conjunction of hypotheses restated. Conclusion 1
uses the market maker's and the source firm's contracts and the compiled bounded evaluator:
`ComputableMarket` is derived from H2. Conclusion 2's inequality is the force layer's
`Σ κ g² ≤ ε + A` discharged at the realized market — the slack by the maker's contract, the
volume by the aggregate's syntactic bound — with the calibrated intensity turning it into
`g ≤ tol`. Conclusion 3 is certificate transport (a certificate's multiplier mass is the
Lipschitz constant carrying rowwise conformance to a functional) composed with the soft gate's
coupling through a synthetic region point. Conclusion 4 derives `PracticalUptake`. Conclusion
2's provenance half is soundness of the compile — nothing reaches the market that H1 and the
survivor rule did not admit — and is not an inequality.

**What it is not.** Pointwise in `n`: the state process is supplied, and nothing relates `N n`
to `N (n+1)`. Conformance is per row, not distance to `K_n`. The conformance claim is
conditional on enforcement: a withheld date carries none, trades nothing, and keeps its
obligations. Entitlement is typed: `Admitted` and `Expresses` are the protocol's and the
application's.

## The assumption ledger

| | established by market mathematics (no input) | assumed about the normative state | assumed about adequacy | specific to the runs |
|---|---|---|---|---|
| **state** | the survivor rule's fixed point, its monotonicity (`activeIds_fixed`, `survivors_anti`); the bundle read as region, licence, elimination input and rows | the state process `N` itself, with its docket and settlement; well-formedness of the grounds | — | five sentences; strengths `4/5, 3/4, 2/3, 3/4`; `X` true at 3, `Y` refuted at 8; A: port 2 defeated at 5, B: quiet docket |
| **entitlement** | enforced substantive rows are entitled survivors' (`warrant_inductor` 2′) | the `Entitlement`: origin exposed; `Protocol.Admitted` at the history; a live leaf in the account; `Expresses` | — | the trivial protocol (`Admitted ≡ True`), `Expresses ≡ True`; `state₀` with both accounts live; `answered_not_entitled` on `state₁` |
| **compile** | conservation (`outcome_obligations`), transparency (`outcome_idle_iff`, `withheld_of_not_check`, `conflict_withheld`, `conflict_region_empty`, `unknown_withheld`), a withheld date trades nothing | the compiler's results `r_n` | — | `r_n = compiled (wit n)`; every date enforced |
| **market** | `IsLogicalInductor` from H2, H3 (`isLogicalInductor`); conformance at enforced dates (`excess_le_tol`); transport (`bracket_at_market`) | `DP` and its computability; the liability bound — discharged by `liability`/`liability_reopened` from slack plausible worlds, which is a hypothesis about the settlement against `DP` | — | `DP` a step function (`process`); three or four bundle phases (`computation`); odds `4`, worlds `allTrue` and `wAY`, bankroll `−72` |
| **adapter** | displayed exclusion and margin from certificates (`scoreR_le`, `scoreR_ge`); `massOff ≤ κ·defect` (`massOff_le`); `PracticalCert`, `PracticalUptake`, Progress | — | `A_s`, `A₁`, `pref`, `τ`, `δ`, `W`; the certificates `Excludes`, `Margins` (checkable on `B_s`); `lam`, `εad`, `D`; `μ`, `T`, `lamS`, `ρ`, `Γ` | `P₁` (act/refrain on the conclusion), `P₂` (act/refrain on `Z`); `τ = 1/3`, `δ = 1/12`; `tol = 1/400`; the certificates `upS`, `loS`, `certZ`; `progress ≤ 37/100` |
| **revision** | Scenario B: operative before, withdrawn by rebuttal, contraposition blocked, region flip, no certificate after, gate reversal at the market, residual accounting | that the settlement is sound for the deductive process (through the slack worlds) | whether refraining is adequate after the refutation — not answered | the same `P₁` at dates 4 and 9; the restricted protocol's residual `1/2` |

The first column is kernel-checked with no semantic input. The second is where the
normative content enters and is not derived here: which warrants exist, how they are revised,
and whether their origins were legitimately incurred. The third is where the practical
meaning enters: the mathematics turns conformance into a bound on the mass placed on responses
*declared* inadequate, and says nothing about the declaration. The fourth is what the two runs
instantiate and is not claimed beyond them.
