Registration status is excluded. “False” below marks a contradiction, rather than merely an unsupported claim.

1. **CURRENT, §1.2 — (a), false conflation.**  
   > “Trickery: how far her estimate is from what her observations support (`AppraisalAccount.miscalibration`, `valuationError`).”

   `miscalibration` conditions on the estimate’s value; `valuationError` conditions on her observations and includes unused information. See [Appraisal header, lines 39–47](/private/tmp/f14_review/AppraisalAccount_header.lean:39).  
   **Correction:** “Minimal miscalibration measures error conditional on her estimate; `valuationError` measures error conditional on her observations and includes unused information.”

2. **CURRENT, §1.4 — false as a blanket claim.**  
   > “None of these is defined in Lean: in the theorems they are data or hypotheses.”

   Lean defines `Gate.Legit` and the quantitative predicate `SoundModel.Sound`; it does not establish that they capture the philosophical concepts. See [AccountJoin header, gate](/private/tmp/f14_review/AccountJoin_header.lean:10) and [SoundModel](/private/tmp/f14_review/AccountJoin_header.lean:54).  
   **Correction:** “Lean defines a gate predicate and a quantitative soundness predicate, but does not establish that they capture these philosophical distinctions.”

3. **CURRENT, §1.5 — (a), false.**  
   > “Her evaluation comes apart from her true utility in three ways, each shown by an instance in which the adviser does no wrong on the reading given: she misreads what she has (I2, an honest slip; I4, selection; `account/DERIVATION.md`); the adviser knows something relevant that its record does not carry (I3, where the wrong is non-disclosure); her valuing is not what it would have been (`Witness.d2a_needed`).”

   I3 expressly involves wrongdoing: non-disclosure. The welcome-change reading of `d2a_needed` is an interpretation. See [AA.2, instances](/private/tmp/f14_review/REPORT_passes_10_to_13.md:982) and [AA.5.22](/private/tmp/f14_review/REPORT_passes_10_to_13.md:1080).  
   **Correction:** “The examples separate evaluation from true utility through honest error or selection, non-disclosure in I3, and changed valuing in `d2a_needed`, interpreted as a welcome unasked change.”

4. **CURRENT, §1.7 — (a); material “Solid” omission.**  
   > “From it, her evaluation is unbiased for a fixed function of the world (`ScoringTheorem.eval_unbiased_of_process`), under her prior.”

   This requires her evaluation to **be her credence’s expectation of that function**. Applying it to D1 additionally requires the prior/world-law identification and, conditional on the adviser’s information, disclosure. These are not supplied by correct credence alone. See [AA.8](/private/tmp/f14_review/REPORT_passes_10_to_13.md:1146), [AA.2](/private/tmp/f14_review/REPORT_passes_10_to_13.md:966), and [Scoring header](/private/tmp/f14_review/ScoringTheorem_header.lean:38).  
   **Correction:** “If her evaluation is her credence’s expectation of a fixed function, correct credence makes it unbiased under her prior and the actual process; deriving D1 requires additional assumptions about that prior and disclosure.”

5. **CURRENT, §1.8, and wiki, “What is proved” — (a).**  
   CURRENT:
   > “The post's Theorems 1 and 3 hold for any legitimacy predicate and bounded evaluation, so they hold for a gate built from the account's components (`Gate.theorem1_join`, `Gate.theorem3_join`); Theorem 2 is not instantiated.”

   Wiki:
   > “The post's Theorems 1 and 3 at a gate built from the account's components, the gate's conditions being inputs (Lean `AccountJoin.Gate.theorem1_join`, `theorem3_join`).”

   Boundedness and supplied gate predicates are not the whole hypothesis package: the prescribed score ranges matter; Theorem 3 retains maximisation, feedback unbiasedness, and alternative availability/range assumptions. See [Z.2, claim 1](/private/tmp/f14_review/REPORT_passes_10_to_13.md:773).  
   **Correction:** “The gate instantiates Theorems 1 and 3 with the prescribed score ranges; Theorem 3’s maximisation, feedback and alternative hypotheses remain assumptions.”

6. **CURRENT, §3 opening — false.**  
   > “None has a result.”

   Several questions have partial results: D1 is partly derivable; D2(b) follows on an added reading; both responsibility tests have counterexamples. See [AA.2](/private/tmp/f14_review/REPORT_passes_10_to_13.md:964) and [AA.4](/private/tmp/f14_review/REPORT_passes_10_to_13.md:1024).  
   **Correction:** “None is resolved; several have partial derivations or counterexamples.”

7. **CURRENT, §3.2 — (a).**  
   > “What supplies her trustworthiness. Not the adviser's conduct.”

   The record establishes non-implication, expressly **not** that conduct cannot help calibration. See [AA.8](/private/tmp/f14_review/REPORT_passes_10_to_13.md:1151).  
   **Correction:** “The adviser’s good conduct alone does not supply her trustworthiness; conduct can contribute under additional assumptions.”

8. **CURRENT, §3.4 — false.**  
   > “The measures and the derivations take the true law, and her prior as that law.”

   The finite identities use supplied weights. The derivation lemmas average under her prior without assuming that it is the world’s law conditional on the adviser’s information. See [Appraisal header, hypotheses](/private/tmp/f14_review/AppraisalAccount_header.lean:65) and [Scoring header, final limitation](/private/tmp/f14_review/ScoringTheorem_header.lean:54).  
   **Correction:** “The measures use supplied weights and the derivations use her prior; identifying these with the relevant true law is an additional modelling premise.”

9. **CURRENT, closing paragraph — (a), unsupported queue-status claim.**  
   > “One question on this line is still queued for him there: whether a practice's rules cover a deception she did not herself ask for.”

   The supplied record still queues careless inducing, exploiting an uncorrectable mistake, and voiding versus earning nothing, alongside earlier questions. It supplies no later resolutions. See [AA.9, outstanding actions](/private/tmp/f14_review/REPORT_passes_10_to_13.md:1188).  
   **Correction:** “The supplied record leaves several maintainer questions outstanding; any subsequent reduction to one question needs a later source.”

10. **Wiki, legitimate judgment — (a), false generalisation.**  
    > “A legitimate judgment can be mistaken: an adviser that reports a false belief it sincerely holds has left her wrong and her permission stands.”

    Sincerity alone does not establish clean conduct: I1 sincerely reports its belief yet counts as manipulation under the proposed *lean* reading. See [AA.2, I1](/private/tmp/f14_review/REPORT_passes_10_to_13.md:994).  
    **Correction:** “A legitimate judgment can be mistaken: I2 illustrates an honest error judged non-wrongful; sincerity alone does not establish legitimacy.”

11. **Wiki, value interference — (a), (c), false.**  
    > “Value interference is changing what she wants without her asking.”

    This turns requesting into a blanket permission constraint. The record treats a welcome unasked change as no wrong under the philosophical reading, distinguishes the stricter alternative, and removes the question whether every welcome change must await a request. See [AA.2, D2(a)](/private/tmp/f14_review/REPORT_passes_10_to_13.md:968) and [AA.7](/private/tmp/f14_review/REPORT_passes_10_to_13.md:1134).  
    **Correction:** “Which changes count as value interference remains unsettled; the maintainer’s working position permits welcome unasked changes.”

12. **Wiki, “What is assumed” — (a).**  
    > “The scoring theorem takes as hypotheses that her audited judgment is not fooled upward and her valuing not made easier to please, that a conduct audit has few false flags and some power, that an honest course exists, and that the adviser maximises.”

    This omits D4 and the reverse comparisons D1(b)/D2(b) at the honest alternative. D6 permits a tolerance and compares actual expected scores. See [AA.1](/private/tmp/f14_review/REPORT_passes_10_to_13.md:940), [AA.2](/private/tmp/f14_review/REPORT_passes_10_to_13.md:966), and [Scoring header](/private/tmp/f14_review/ScoringTheorem_header.lean:18).  
    **Correction:** “The bounds assume the relevant D1/D2 comparisons at the chosen and honest courses, the relevant audit conditions, independent sampling, an available honest course, and approximate maximisation of actual expected score.”

13. **Wiki, final limitations sentence — false.**  
    > “The bounds are of expected scores, for one decision, on detected violations, with a finite penalty.”

    The principal conclusions bound expected **true utility**, the probability of **actual wrongdoing**, and expected **detected authority violations**. Only the last quantity is restricted to detected violations. See [AA.1](/private/tmp/f14_review/REPORT_passes_10_to_13.md:944) and [Scoring header](/private/tmp/f14_review/ScoringTheorem_header.lean:23).  
    **Correction:** “For one decision, the theorem bounds expected true utility, actual wrongdoing probability, and expected detected authority violations; the finite penalty supplies no strict priority.”

14. **CURRENT, “Solid” §1.8 — material omitted limitation.**  
    The sound-signal and guarantee results concern expectations in **true utility**, not the realised point or the gate’s score `V`. Moreover, `SoundModel` obtains its legitimate-history bound by defining soundness through the relevant error bound. See [Z.7](/private/tmp/f14_review/REPORT_passes_10_to_13.md:886) and [Z.2, claim 2](/private/tmp/f14_review/REPORT_passes_10_to_13.md:774). The caveat in §1.6 is scoped to the separate scoring theorem.  
    **Add:** “These sound-signal and guarantee bounds are expectations in true utility, not realised-history or `V` guarantees; `SoundModel` assumes the needed error bound through its definition of soundness.”

15. **CURRENT, “Solid” §1.8 — material omitted limitation.**  
    The join does not model the inducing test, counterfactual later self, acting on her behalf, or line 3 at every moment. In particular, the proved `ValueChange.line3` is not connected to `Gate.line3`. See [Z.7](/private/tmp/f14_review/REPORT_passes_10_to_13.md:884) and [AccountJoin header](/private/tmp/f14_review/AccountJoin_header.lean:78).  
    **Add:** “The join leaves those behavioural and temporal components unmodelled, and no declaration connects the proved `ValueChange.line3` to the gate’s field.”

16. **CURRENT, “Solid” §1.8 — material omitted limitation.**  
    The join proves neither that worsening options lowers `V` nor that overriding a choice between equally rated options counts as a violation; it also does not connect its legitimacy predicate to `Legitimacy.Segment`. See [Z.3](/private/tmp/f14_review/REPORT_passes_10_to_13.md:793) and [AccountJoin’s exclusions](/private/tmp/f14_review/AccountJoin_header.lean:86).  
    **Add:** “The join supplies no options-loss guarantee, no violation encoding for overriding equally rated choices, and no connection to segment legitimacy.”

**No separate (b) finding in either document:** both explicitly mark the account and wrongdoing definitions as unfinished. **No (c) finding in CURRENT:** it identifies the distinctions as vocabulary and the maintainer’s answers as revisable working positions. The wiki’s corresponding “no wrong of the first kind” wording correctly accommodates I3’s non-disclosure; CURRENT’s “no wrong” does not.
