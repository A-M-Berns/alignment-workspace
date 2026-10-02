import Cleanroom.Bli.BliSuperbelief.Face
import Cleanroom.Bli.BliSuperbelief.Expr
import Cleanroom.Bli.BliSuperbelief.Bits
import Cleanroom.Bli.BliSuperbelief.Escape
import Cleanroom.Bli.BliSuperbelief.Modulus
import Cleanroom.Bli.BliSuperbelief.Boundary
import Cleanroom.Bli.BliSuperbelief.Dogmatism
import Cleanroom.Bli.BliSuperbelief.CoherentGrid
import Cleanroom.Bli.BliSuperbelief.Paper
import Cleanroom.Bli.BliSuperbelief.Witnesses

/-!
# `bli-superbelief`: existence and non-degeneracy of superbeliefs on finite grids

Root module of the package `bli-superbelief` (area `bli`, namespace
`Cleanroom.Bli.BliSuperbelief`), over `bli-finite`'s objects (`SmallIndex`, `Table`, `grid`,
`Superbelief`, `faceGen`, `tentLaw`, `Kernel`, `RatHistory`) and FAF's `EF`; the FAF-side facts
live in `Paper.lean` (the only file importing `bli-found`, `Construction.LIA` and `paperDP`).

* **Face** (E1) — `exists_fullSupport_faceGen` (a rational balance solution supported exactly on
  the generated face, on an arbitrary finite carrier; scope `faceGen_nonempty_iff_mem_hull`),
  `faceGen_eq_hullFace` (the back-away
  characterization through `convexHull ℚ` of the restricted carrier), `faceGen_eq_iff_backaway`,
  `faceProd_eq_grid_iff`, and the face-constancy corollaries `faceConst`/`faceConst_prod`.
* **Expr** (E2) — `tentExpr`/`tentExpr₁`, the FAF `EF` terms for the tent chain's marginals
  (`add`/`mul`/`max`/`const`/`price` only, clamp inside), `tentExpr_denoteRat`/`tentExpr₁_denoteRat`
  (exact rational denotation for every rational history), `tentExpr_priceLeavesIn` (leaves are
  day-`m` prices of day-`m` small sentences), `tentExpr_cost_le`/`tentExpr_size_le` (node and
  token counts linear in `|S (m+h+1)|`), via the coordinatewise factorization
  `lastMarg_tent_eq_prod_coordMarg` and the three-constant mixture `chainFrom_tentW`.
* **Bits** (E2(d), the bit-metered half) — `chainDen` and `chainFrom_den`/`coordMarg_den` (every
  constant of `tentExpr` is a probability with denominator dividing `chainDen 𝓜 m h`, which is
  `≤ (D+1)^(2h+1)` under a mesh bound: `chainDen_le_pow`), `tentExpr_constsBounded`,
  `encode_rat_lt`, and the FAF digit-meter bound `tentExpr_digitize_length_le` (with the explicit
  exponent `tentExpr_digitize_length_le_log` and the mandate's polynomial form
  `tentExpr_digitize_length_le_poly`) — the digit stream of `serialize`.
* **Escape** (E2(d), the stream FAF's class reads; repair round 2) — FAF's decoder contracts
  sentence blocks (`unRpn`) before deserialization, so a machine must emit an `unRpn`-preimage:
  FAF's `escExpand`. `escExpand_serialize_spec`/`escExpand_serializeTrades_spec` (the expansion
  of a closed same-day term, or of a strategy stream of such terms, contracts back exactly and
  costs two digits per price leaf and per trade frame), `priceLeaves_tentExpr` (`4·|S m|` leaves),
  `unRpn_escExpand_tentExpr`, `escExpand_tentExpr_digitize_length` (`+ 8·|S m|` digits),
  `tentExpr_escExpand_digitize_length_le`/`_poly` and the one-trade stream
  `escExpand_serializeTrades_single_digitize_length_le`; `encode_sentence_ne_zero` (no sentence
  has code `0`, so the escape is available at every slot).
* **Modulus** (E2(a)) — `tentLaw_l1_le`: the tent kernel's `ℓ¹`-modulus is `4·|S m|·‖t − t'‖∞`
  (the program's `2|S|` is false: `tentLaw_l1_two_witness`, `4/3 > 1` at `d = 2`), via the
  4-Lipschitz weights `tent_weights_lipschitz`, `tent1_l1_le`, and the general product bound
  `prod_l1_le`.
* **Boundary** (E5) — the refuted printed grid `posGrid` (`posGrid_no_balance_below`), full
  support on the whole grid against a `0/1` price (`fullSupport_grid_contra_zeroOne`), and the
  surviving `FS` (`nonDegenerate_face_satisfiable`, `nonDegenerate_yes_fullSupport_no`).
* **Dogmatism** (E6, finite) — `actual_mem_faceProd_iff`, `null_of_not_mem_faceProd`,
  `dogmatism` (positive mass on the realized state iff the face condition, under `FS`),
  `roundVal_pos_iff`, `null_of_zero_moved`.
* **CoherentGrid** (E7, finite) — `base_coherent_of_coherentGrid` (mix the world measures; the
  charged points need only be coherent on `S m`), `base_coherent_of_balance_on_coherentGrid`,
  `faceGen_coherentGrid_eq_empty_of_not_coherent`, `not_coherent_of_zero_of_neg_ne_one` and its
  pair form `not_coherent_of_offSupport_pair`.
* **Paper** (E6(c)/(d), E7(c) at `liaStates`) — `smallIndex`, `liaQuote_eq_zero_of_not_mem_support`,
  `liaStates_support_subset_firm`, `supportEntry_not_mem_faceProd`, `supportEntry_null`,
  `lia_not_coherent_of_offSupport_neg_ne_one`/`lia_not_coherent_of_offSupport_pair`,
  `lia_coherentGrid_infeasible_of_neg_ne_one`/`lia_coherentGrid_infeasible`, and the OPEN
  `exists_supportEntry_day_paperDP`.
* **Witnesses** — the N+/N− instances: `face_witness` (E1 on the coherent grid, two charged
  points), `ext1_backaway`/`extQ₀_no_backaway`, `tentExpr₁_witness`/`mix3E_witness`/
  `tentExpr_two_witness` (E2), `posGrid_witness`/`boundary_witness` (E5), `dogmatism_witness`/
  `dogmatism_positive_witness` (E6, both directions), `extT_coherent`/
  `ext11_charged_not_coherent`/`offSupport_pair_witness` (E7).
-/
