# Composition: the conclusion of each theorem is the hypothesis of the next

**Status:** `ci-only`; second pass.  Lean: `lean/Workspace/Deference/Contrib/ReasonSupply.lean`
§4 (`li_gated_le`, `expect_constLUV`, `li_noncapture`).

## 1. The chain

```
Supply theorem            ⟹  in every consistent world on the audited branch,
(SUPPLY_THEOREM.md §3)        D^A_n ≤ α_n                        [a Γ-valid sentence]

Sensitivity theorem       ⟹  |V(N_form T) − V(N_form N)| ≤ A_tot · (D^A_n / A_tot)
(CONTENT_RESIDUAL.md)         [the compiled pair's `lip`, with d := D^A/A_tot, L := A_tot]

Canonicalization theorem  ⟹  κ_n = 0 in every consistent world
(extensional_form_free)       [the compiled pair's `Gρ` is valued 0]

Audit/sealing              ⟹  φ_T,n → φ_N,n in every consistent world
(a hypothesis of the        [the compiled pair's `GM` is valued 0]
 realization, not a theorem
 here)

LI steering theorem       ⟹  𝔼ₙ(U_T) − 𝔼ₙ(U_N) ≲ₙ A_tot·𝔼ₙ(G_δ) + 𝔼ₙ(G_ρ) + 𝔼ₙ(G_M)
(li_steering_le)

li_gated_le (three times) ⟹  𝔼ₙ(G_δ) ≲ α,   𝔼ₙ(G_ρ) ≲ 0,   𝔼ₙ(G_M) ≲ 0

li_noncapture             ⟹  𝔼ₙ(U_T) − 𝔼ₙ(U_N) ≲ₙ A_tot · α
```

Every arrow is a Lean term or a per-world fact of the type the next theorem's
hypothesis names.  There is no prose bridge.

## 2. The one new lemma, and why it is needed

The landed theorem bounds the *difference of expectations* by *expectations of the
residual LUVs*.  To conclude anything numerical one needs the inductor's expectation of
a residual LUV to respect a bound that holds in every consistent world.  For a single
fixed LUV that is Expectation Provability Induction (`lic_expectation_provind_le`,
`thm:expprovind`); for a *family* `U_n` it needs the sequence form, whose only landed
certificate is the compiled pair's.  `li_gated_le` gets the sequence form for free by
feeding the landed theorem a **degenerate pair**

```
Uraw := U_n,  Ucorr := constLUV α,  Gδ = Gρ = GM := constLUV 0,  φraw := φ_n,  φcorr := ⊤,  λ := 0
```

whose validity package is exactly "`U_n ≤ α` where `φ_n` holds", and whose conclusion is
`𝔼ₙ(U_n) − 𝔼ₙ(constLUV α) ≲ₙ 0·𝔼ₙ(0) + 𝔼ₙ(0) + 𝔼ₙ(0)`.  The constants are then removed by
`expect_constLUV`: the inductor's expectation of a constant LUV converges to the
constant (`lic_expectation_provind_eq` on the single LUV `constLUV α`, whose emission code
is the landed sequence code reindexed).  No new generability certificate is built; the
degenerate pair reuses `MediatedPair.syntaxOf` verbatim.

## 3. The theorem

`li_noncapture`.  Hypotheses, in the order the realization supplies them:

| hypothesis | who discharges it |
|---|---|
| `hvalid`: the compiled steering package in every consistent world | `steering_validAt` from the audit, the program's verdicts and the sensitivity certificate |
| `hsupply`: `X_d,n` is valued `d` with `d ≤ a/b` wherever both audits hold | the supply theorem, `α_n := Miss*_n / A_tot` on the discovered docket, uniformly `≤ a/b` |
| `hext`: `X_κ,n` is valued `0` | the program is extensional (`extensional_form_free`) |
| `hsealed`: `φ_T,n → φ_N,n` | the audit is monotone in content: against `N_form` or `N_full`/`N_disc` it is (`NONCAPTURE_COMPILATION.md` §2) |
| `hworld`, emission codes of `φ_T, φ_N, X_T, X_N, X_d, X_κ`, `0 ≤ L` | the landed realization inputs |

Conclusion: `𝔼ₙ(U_T,n) − 𝔼ₙ(U_N,n) ≲ₙ L · (a/b)`.  With `a/b = 0` (the suffix-cut
condition holds on the discovered docket at every occurrence) the right-hand side is `0`:

> the bounded agent asymptotically assigns no advantage to steering the principal's
> deliberative inputs over the independently serviced, authenticated, canonical trace.

**Vanishing bounds.**  The theorem is stated for a constant `a/b`.  If `α_n → 0` then for
every rational `ε > 0` the hypotheses hold with `a/b = ε` from some `N` on, and
`li_bypass_le_compiled` needs validity at every `n`; shifting the families by `N`
(`hvalid` for `n ≥ N` becomes `hvalid` for all `n` of the shifted family, whose emission
codes are the old ones composed with `n ↦ n + N`, `RpnSentenceCodes.comp`) gives
`≲ₙ L·ε` for every `ε`, hence `≲ₙ 0`.  This shift is routine and not mechanized.

## 4. Which comparator

`hsupply` is a *per-world* bound on the content LUV.  Against the **discovered
comparator** `N_disc` (every discovered true declared reason, canonical form) the
content term is the service loss plus the authentication loss, both computations on
the log: the bound `Miss*_n ≤ α_n` is a `Γ`-valid sentence and the theorem is sound with
no oracle.  Against the **fully-informed** `N_full` the content term adds the discovery
loss, which is a world fact no log determines; the theorem still holds as an inequality
with the world-valued LUV, but no realizable process certifies `hsupply` for it.  So:

- **realizable service regret** = the theorem against `N_disc`, certified by the supplier;
- **ideal completeness regret** = the same against `N_full`, with the discovery term
  carried as an uncertified world quantity.

The realizable statement is the one to make.  The supplier comparator `N_service` (what
the certified policy actually produces) is not a separate comparator: with the supplier
in the loop the actual trace *is* `N_service`, and the theorem's content is exactly
`N_service` versus `N_disc`, i.e. the service loss.

## 5. With the effect side

The landed effect-side theorem (`li_bypass_le_compiled`, PR #100) and `li_noncapture`
have the same shape and consume the same certificate:

```
Adv_bypass    ≲ₙ  L·𝔼ₙ(Δ)      + 𝔼ₙ(R)     + D·𝔼ₙ(M)         (mediation, decision regret, activation mismatch)
Adv_steering  ≲ₙ  A_tot·α      + 0         + 0               (missed adverse mass, form, audit mismatch)
```

Both are relative to: effect completeness (the corrigibility theorem's hypothesis), a
declared reason representation (the comparator's domain), the sealed comparison
architecture (item 89) for the effect side's `M`, the sealed audit for the reason side's,
and the declared-transform contract wherever a counterfactual is named.  The combined
statement is in `REPORT.md` §"The strongest honest combined statement".
