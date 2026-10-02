import Cleanroom.Deference.DefLatticeArrows.GapBets

/-!
# T11 — Value ⟹ Tower via gap-bet probe menus

Package `def-lattice-arrows`, file 6. [[value-implies-tower]] (PDF slide 11,
lean-deference-070) over `def-lattice`'s objects: on the two-option menu
`{G, K}` with `G` the rescaled gap-bet of `Z` and `K = constLUV ((1 − ε)/2)` the constant
probe (the page's `const(−ε)`, rescaled), the expert's pins put `G` strictly on top
eventually, so the follower `S` is valued as `G` eventually; the **menu-local** Value instance
`E^H_n(S_n) ≳ₙ E^H_n(K_n)` then gives `E^H_n(G_n) ≳ₙ (1 − ε)/2`. Mirrored on `G'`, diagonalized
over `ε`, and unfolded (`tower_of_gap_halves`), this is the Tower instance at `(Z, Y)`.

* `probe_instance` — the per-`ε` instance;
* `tower_of_value_probes` — the headline (per-instance Value on the probe menus for every
  `0 < ε ≤ 1`, both ways, plus the pins);
* `towerValued_of_value_of_probes` — the predicate-level corollary from unconditional `Value`
  with the existence clause `ProbeMenusAvailable` (the wiki's "channel" cost), named for
  where it lands;
* `selfEndorse_probe` — T2's self-endorsement hypothesis on a probe menu, from the pins *and*
  the expert's pin on the follower (finding: it is not automatic from the option pins alone).

The probe menu is def-lattice's `twoOptionMenu G K` (`O 0 = G`, `O 1 = K`); it is not
redefined. "No rate": the argument fixes `ε` per menu and yields no rate, because the pins
supply none (the page's §Why ε must be fixed per menu; not attempted).
-/

namespace Cleanroom.Deference.DefLatticeArrows

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

variable {P : History} {DP : DeductiveProcess}

/-- The constant probe option `K_ε := constLUV ((1 − ε)/2)`, the rescaled `const(−ε)`.
Source: [[value-implies-tower]] §The probe menu
Kind: D
Fidelity: variant: rescaled -/
def probeConst (ε : ℚ) : ℕ → LUV := fun _ => constLUV ((1 - ε) / 2)

/-- `(1 − ε)/2 ∈ [0,1]` for `0 < ε ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem probeConst_mem {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ (1 - ε) / 2 ∧ (1 - ε) / 2 ≤ 1 := ⟨by linarith, by linarith⟩

/-- **The probe data** at margin `ε`: an e.c. follower `S` of the expert's least-index argmax on
the probe menu `{G, K_ε}` (`Follows`, a value clause). The gap quote `G` is given separately
(its code certificate is what the menu needs); the expert's pins are separate hypotheses.
Source: [[value-implies-tower]] §Hypotheses (V); mandate design decision 2
Kind: D
Fidelity: exact (reflection form) -/
structure ProbeData (DP : DeductiveProcess) (E : Expert DP) (ε : ℚ) (G S : ℕ → LUV)
    (hG : LUV.MachineThresholdCodeSeq G) where
  /-- the margin is in `(0, 1]` -/
  hε : 0 < ε ∧ ε ≤ 1
  /-- the follower is efficiently describable -/
  codes_S : LUV.MachineThresholdCodeSeq S
  /-- `S` follows the expert's argmax on `{G, K_ε}` -/
  follows : Follows DP E (twoOptionMenu G (probeConst ε) hG (constLUV_codes (probeConst_mem hε.1 hε.2).1)) S

namespace ProbeData

variable {E : Expert DP} {ε : ℚ} {G S : ℕ → LUV} {hG : LUV.MachineThresholdCodeSeq G}

/-- The probe menu of the data.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def menu (d : ProbeData DP E ε G S hG) : Menu 1 :=
  twoOptionMenu G (probeConst ε) hG (constLUV_codes (probeConst_mem d.hε.1 d.hε.2).1)

/-- The probe menu is world-valued when `G` is.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem menu_valued (d : ProbeData DP E ε G S hG) (hGv : Valued DP G) : d.menu.Valued DP := by
  intro j
  by_cases h : j = 0
  · subst h; simpa [menu] using hGv
  · have h1 : j = 1 := by
      revert h; generalize j = a; intro h
      fin_cases a
      · exact absurd rfl h
      · rfl
    subst h1
    intro n v _
    exact ⟨_, constLUV_valuesAt (probeConst_mem d.hε.1 d.hε.2) v⟩

end ProbeData

/-- **The expert quotes the gap-bet strictly above the probe, eventually**: from the pins
`E*(G_n) ≈ₙ ½` and `E*(K_n) ≈ₙ (1 − ε)/2`, with margin `ε/2 > 0`.
Source: [[value-implies-tower]] §Proof Step 2 ("strictly top-quoted for all `n ≥ N`")
Kind: L
Fidelity: exact (asymptotic pins)
Hyps: the pins (b)/(c) -/
theorem probe_eventually_top {E : Expert DP} {ε : ℚ} (hε : 0 < ε) {G : ℕ → LUV}
    (pinG : ExpertPin E G (1 / 2))
    (pinK : ExpertPin E (probeConst ε) (((1 - ε) / 2 : ℚ) : ℝ)) :
    ∀ᶠ n in atTop, E.estimate (probeConst ε) n < E.estimate G n := by
  have hε' : (0 : ℝ) < ε / 8 := by positivity
  filter_upwards [asympEq_eventually_abs_le pinG hε', asympEq_eventually_abs_le pinK hε']
    with n h1 h2
  rw [abs_le] at h1 h2
  push_cast at h2
  linarith [h1.1, h2.2]

/-- **The follower is valued as the gap-bet, eventually**: once `G` is strictly top-quoted the
least-index argmax is `0` (`Menu.argmax_two`), and `Follows` transfers `G_n`'s world value to
`S_n`; T0 (eventual, exact) gives `E^H_n(S_n) ≈ₙ E^H_n(G_n)`.
Source: [[value-implies-tower]] §Proof Step 2–3 (`Γ ⊢ Ŝ_n = G_n` for `n ≥ N`, carried by
`expprovind` with the early days patched)
Kind: C
Fidelity: exact
Hyps: (a) the data; the pins (b)/(c); `hworld` -/
theorem expect_follower_asympEq_gap [IsLogicalInductor P DP] {E : Expert DP} {ε : ℚ}
    {G S : ℕ → LUV} {hG : LUV.MachineThresholdCodeSeq G} (d : ProbeData DP E ε G S hG)
    (hGv : Valued DP G) (pinG : ExpertPin E G (1 / 2))
    (pinK : ExpertPin E (probeConst ε) (((1 - ε) / 2 : ℚ) : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (S n).expect P n) ≈ₙ (fun n => (G n).expect P n) := by
  have htop := probe_eventually_top d.hε.1 pinG pinK
  have hS : ∀ n, E.estimate (probeConst ε) n < E.estimate G n → ∀ (v : PCWorld),
      v.ConsistentWithTheory DP → ∀ x, v.ValuesAt (G n) x → v.ValuesAt (S n) x := by
    intro n hn v hv x hx
    have hargmax := (twoOptionMenu G (probeConst ε) hG
      (constLUV_codes (probeConst_mem d.hε.1 d.hε.2).1)).argmax_two E n
    simp only [Menu.quote, twoOptionMenu_O_zero, twoOptionMenu_O_one] at hargmax
    rw [if_pos hn.le] at hargmax
    have := d.follows n v hv x
    rw [hargmax, twoOptionMenu_O_zero] at this
    exact this hx
  have h := expect_listComb_eq_of_eventually (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, S), (-1, G)])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact d.codes_S
      · exact hG)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · intro n v hv
        -- world-valuedness of `S` on early days is not given by `Follows` alone; use
        -- eventual valuedness through the argmax on all days: `S n` is valued as the
        -- selected option, which is valued in every world (both options are)
        obtain ⟨x, hx⟩ : ∃ x, v.ValuesAt (d.menu.O (d.menu.argmax E n) n) x :=
          d.menu_valued hGv _ n v hv
        exact ⟨x, d.follows n v hv x hx⟩
      · exact hGv))
    (0 : ℝ) (fun ε' hε' => by
      filter_upwards [htop] with n hn v hv ν hν
      have hSv := listComb_valuesAt_mem hν (p := (1, S)) (by simp)
      have hGv' := listComb_valuesAt_mem hν (p := (-1, G)) (by simp)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hSv.eq (hS n hn v hv _ hGv')]
      simpa using hε'.le) hworld
  have h' : (fun n => (S n).expect P n - (G n).expect P n) ≈ₙ (fun _ => (0 : ℝ)) := by
    refine (tendsto_congr (fun n => ?_)).mp h
    simp [listComb_expect, sub_eq_add_neg]
  exact asympEq_sub_zero_iff.mp h'

/-- The novice's expectation of the constant probe tends to its value (T0, all days).
Source: [[value-implies-tower]] §Proof Step 3 ("this LUV is provably `−ε`", rescaled)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem expect_probeConst_asympEq [IsLogicalInductor P DP] {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (probeConst ε n).expect P n) ≈ₙ (fun _ => (((1 - ε) / 2 : ℚ) : ℝ)) := by
  have hm := probeConst_mem hε hε1
  have h := expect_listComb_eq_of_slack (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, probeConst ε)])
    (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact constLUV_codes hm.1)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact constLUV_valued hm DP))
    (((1 - ε) / 2 : ℚ) : ℝ) (slack := fun _ => 0) tendsto_const_nhds
    (fun n v hv ν hν => by
      have := listComb_valuesAt_mem hν (p := (1, probeConst ε)) (List.mem_singleton_self _)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [this.eq (constLUV_valuesAt hm v)]
      simp) hworld
  refine (tendsto_congr (fun n => ?_)).mp h
  simp [listComb_expect]

/-- **Value on one probe menu ⟹ the lower gap half, per `ε` (T11, the instance)**: with the
probe data, the pins, and the **menu-local** Value instance `E^H_n(S_n) ≳ₙ E^H_n(K_n)`,
`E^H_n(G_n) ≳ₙ (1 − ε)/2`. Chain: `E^H_n(G_n) ≈ₙ E^H_n(S_n) ≳ₙ E^H_n(K_n) ≈ₙ (1 − ε)/2`.
Source: [[value-implies-tower]] §Proof Steps 1–3; PDF slide 11 (root-deference-017);
lean-deference-070; vq-wiki-019
Kind: C
Fidelity: variant: rescaled to `[0,1]`; hypothesis is the menu-local Value instance, not
unconditional `Value` (def-lattice F17)
Hyps: (a) the data and the Value instance `hval`; (b)/(c) the pins (`pinK` is (a) for an
inductor expert, `expertPin_constLUV`; `pinG` is the expert's `loe` + introspection on the
gap, (b) self / (c) general); `hworld` -/
theorem probe_instance [IsLogicalInductor P DP] {E : Expert DP} {ε : ℚ} {G S : ℕ → LUV}
    {hG : LUV.MachineThresholdCodeSeq G} (d : ProbeData DP E ε G S hG) (hGv : Valued DP G)
    (pinG : ExpertPin E G (1 / 2)) (pinK : ExpertPin E (probeConst ε) (((1 - ε) / 2 : ℚ) : ℝ))
    (hval : (fun n => (S n).expect P n) ≳ₙ (fun n => (probeConst ε n).expect P n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (G n).expect P n) ≳ₙ (fun _ => (((1 - ε) / 2 : ℚ) : ℝ)) := by
  have hSG := expect_follower_asympEq_gap (P := P) d hGv pinG pinK hworld
  have hK := expect_probeConst_asympEq (P := P) d.hε.1 d.hε.2 hworld
  exact (hK.symm.trans_asympLE hval).trans_asympEq hSG

/-- A gap quote's `G` is world-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem GapQuote.gap_valued {E : Expert DP} {Z Y G : ℕ → LUV} {a : ℚ}
    (q : GapQuote DP E Z Y a G) : Valued DP G := by
  intro n v hv
  obtain ⟨z, hz⟩ := q.source_valued n v hv
  obtain ⟨g, hg, -⟩ := q.gap_reflected n v hv z hz
  exact ⟨g, hg⟩

/-- **Value ⟹ Tower via probe menus (T11, the headline)**: given the gap quote `G` and its
mirror `G'` for `(Z, Y)`, the expert's pins on them, the pins on the constant probes, and —
for every `0 < ε ≤ 1` — probe data on `G` and on `G'` with their menu-local Value instances:
`E^H_n(Z_n) ≈ₙ E^H_n(Y_n)`. Composition: `probe_instance` both ways at every `ε`, the
diagonal over `ε` (`asympGE_of_forall_rat_sub_le` at `η = ½`), then `tower_of_gap_halves`.
Source: [[value-implies-tower]] §Proof (Steps 1–5); PDF slide 11; lean-deference-070;
vq-wiki-019
Kind: C
Fidelity: variant: rescaled; per-menu Value instances (F17)
Hyps: (a) the packages and Value instances (data); (b)/(c) the pins; `hworld` -/
theorem tower_of_value_probes [IsLogicalInductor P DP] {E : Expert DP} {Z Y G G' : ℕ → LUV}
    (hZ : LUV.MachineThresholdCodeSeq Z) (hY : LUV.MachineThresholdCodeSeq Y)
    (qP : GapQuote DP E Z Y 1 G) (qM : GapQuote DP E Z Y (-1) G')
    (pinP : ExpertPin E G (1 / 2)) (pinM : ExpertPin E G' (1 / 2))
    (pinK : ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ExpertPin E (probeConst ε) (((1 - ε) / 2 : ℚ) : ℝ))
    (hprobeP : ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∃ S : ℕ → LUV, ∃ _d : ProbeData DP E ε G S qP.codes,
      (fun n => (S n).expect P n) ≳ₙ (fun n => (probeConst ε n).expect P n))
    (hprobeM : ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∃ S : ℕ → LUV, ∃ _d : ProbeData DP E ε G' S qM.codes,
      (fun n => (S n).expect P n) ≳ₙ (fun n => (probeConst ε n).expect P n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (Z n).expect P n) ≈ₙ (fun n => (Y n).expect P n) := by
  have half : ∀ (G₀ : ℕ → LUV) (hG₀ : LUV.MachineThresholdCodeSeq G₀), Valued DP G₀ →
      ExpertPin E G₀ (1 / 2) →
      (∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∃ S : ℕ → LUV, ∃ _d : ProbeData DP E ε G₀ S hG₀,
        (fun n => (S n).expect P n) ≳ₙ (fun n => (probeConst ε n).expect P n)) →
      (fun n => (G₀ n).expect P n) ≳ₙ (fun _ => (1 / 2 : ℝ)) := by
    intro G₀ hG₀ hGv pin hpr
    refine asympGE_of_forall_rat_sub_le (η := 1 / 2) (by norm_num) (fun ε hε hε2 => ?_)
    obtain ⟨S, d, hval⟩ := hpr (2 * ε) (by positivity) (by linarith)
    have := probe_instance (P := P) d hGv pin (pinK (2 * ε) (by positivity) (by linarith)) hval
      hworld
    intro ε' hε'
    filter_upwards [this ε' hε'] with n hn
    push_cast at hn
    linarith
  exact tower_of_gap_halves hZ hY qP qM
    (half G qP.codes qP.gap_valued pinP hprobeP) (half G' qM.codes qM.gap_valued pinM hprobeM)
    hworld

/-- **Probe menus available** — the wiki's "channel" cost as an existence clause: for every
e.c. valued `Z` with e.c. quote `Y`, both gap quotes exist, and for every margin both probe
followers exist. `(c)` for a general expert; on `Expert.self` the packages are
`li-quote-lane`'s.
Source: [[value-implies-tower]] §What the theorem costs ("Menu class")
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def ProbeMenusAvailable (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ Z Y : ℕ → LUV, LUV.MachineThresholdCodeSeq Z → LUV.MachineThresholdCodeSeq Y →
    Valued DP Z → Reflects DP E Z Y → ∃ G G' : ℕ → LUV,
      ∃ qP : GapQuote DP E Z Y 1 G, ∃ qM : GapQuote DP E Z Y (-1) G',
        ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
          (∃ S : ℕ → LUV, Nonempty (ProbeData DP E ε G S qP.codes)) ∧
          (∃ S : ℕ → LUV, Nonempty (ProbeData DP E ε G' S qM.codes))

/-- **Value ⟹ Tower on valued sources** (predicate level, T11): from unconditional `Value`,
the probe menus, the gap pins and the constant pins. Lands in `TowerValued`, and is named for
where it lands (the mandate's `tower_of_value_of_probes`; audit r1 fidelity 5).
Source: [[value-implies-tower]] §Statement; vq-wiki-019
Kind: L
Fidelity: weaker: on valued sources; rescaled
Hyps: (c) `ProbeMenusAvailable` (existence); `ExpertPinsGaps` ((b) self / (c) general);
`pinK` ((a) for an inductor expert, `expertPin_constLUV`); `Value` is the deference
hypothesis (the corpus holds it false unconditionally for inductor-experts — the per-menu
form `tower_of_value_probes` is the theorem); `hworld` -/
theorem towerValued_of_value_of_probes [IsLogicalInductor P DP] {E : Expert DP}
    (hV : Value P DP E) (hp : ProbeMenusAvailable DP E) (hpins : ExpertPinsGaps DP E)
    (pinK : ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ExpertPin E (probeConst ε) (((1 - ε) / 2 : ℚ) : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    TowerValued P DP E := by
  intro Z Y hZ hY hval hR
  obtain ⟨G, G', qP, qM, hpr⟩ := hp Z Y hZ hY hval hR
  refine tower_of_value_probes hZ hY qP qM (hpins Z Y 1 (Or.inl rfl) G qP)
    (hpins Z Y (-1) (Or.inr rfl) G' qM) pinK
    (fun ε hε hε1 => ?_) (fun ε hε hε1 => ?_) hworld
  · obtain ⟨S, ⟨d⟩⟩ := (hpr ε hε hε1).1
    refine ⟨S, d, ?_⟩
    have := hV 1 d.menu (d.menu_valued qP.gap_valued) S d.codes_S d.follows 1
    simpa [ProbeData.menu] using this
  · obtain ⟨S, ⟨d⟩⟩ := (hpr ε hε hε1).2
    refine ⟨S, d, ?_⟩
    have := hV 1 d.menu (d.menu_valued qM.gap_valued) S d.codes_S d.follows 1
    simpa [ProbeData.menu] using this

/-- **Value ⟹ Tower on valued sources for an inductor expert**: the constant pins discharged
by `expertPin_constLUV` (grade (a)).
Source: [[value-implies-tower]]; def-lattice F3
Kind: L
Fidelity: weaker: on valued sources; rescaled
Hyps: (c) `ProbeMenusAvailable`; `ExpertPinsGaps` ((b) self / (c) general); `Value`;
`[IsLogicalInductor E.A DP]`; `hworld` -/
theorem towerValued_of_value_of_probes_inductor [IsLogicalInductor P DP] {E : Expert DP}
    [IsLogicalInductor E.A DP] (hV : Value P DP E) (hp : ProbeMenusAvailable DP E)
    (hpins : ExpertPinsGaps DP E) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    TowerValued P DP E :=
  towerValued_of_value_of_probes hV hp hpins
    (fun _ hε hε1 => expertPin_constLUV E (probeConst_mem hε hε1) hworld) hworld

/-- **Self-endorsement on a probe menu** (T2's hypothesis `hSE`, the H3-laden step): on
`{G, K_ε}` with the pins on `G` and `K_ε` **and** the expert's pin on the follower
(`E*(S_n) ≈ₙ E*(G_n)`), the expert's estimate of the follower tracks the maximal quote:
`E*(S_n) ≈ₙ M_n`. The follower pin is not implied by the option pins: `S_n` is valued as `G_n`
only in the worlds, and the expert's day-`f n` estimate of `S_n` is a separate asymptotic fact
(for the self-expert a day-`f n` provability-induction pull-back, `(b)`; `(c)` in general) —
the mandate's "holds automatically" needs it (see the findings).
Source: [[value-implies-tower]] §The scope condition is vacuous here; mandate T2/T11
(`selfEndorse_probe`)
Kind: L
Fidelity: weaker: needs the follower pin (disclosed)
Hyps: (b)/(c) the three pins -/
theorem selfEndorse_probe {E : Expert DP} {ε : ℚ} (hε : 0 < ε) {G S : ℕ → LUV}
    {hG : LUV.MachineThresholdCodeSeq G} (d : ProbeData DP E ε G S hG)
    (pinG : ExpertPin E G (1 / 2)) (pinK : ExpertPin E (probeConst ε) (((1 - ε) / 2 : ℚ) : ℝ))
    (pinS : (fun n => E.estimate S n) ≈ₙ (fun n => E.estimate G n)) :
    (fun n => E.estimate S n) ≈ₙ (fun n => d.menu.maxQuote E n) := by
  have htop := probe_eventually_top hε pinG pinK
  unfold AsympEq at pinS ⊢
  refine pinS.congr' ?_
  filter_upwards [htop] with n hn
  rw [Menu.maxQuote_two]
  simp only [Menu.quote, ProbeData.menu, twoOptionMenu_O_zero, twoOptionMenu_O_one]
  rw [max_eq_left hn.le]

end

end Cleanroom.Deference.DefLatticeArrows
