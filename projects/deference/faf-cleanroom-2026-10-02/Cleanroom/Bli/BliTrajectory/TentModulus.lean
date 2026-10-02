import Cleanroom.Bli.BliTrajectory.Update
import Cleanroom.Bli.BliSuperbelief.Modulus

/-!
# `bli-trajectory` · TentModulus: `KernelLip` is inhabited by the tent (repair round 2)

Adopted from audit r2's adversarial probe `audit-r2-probes/KernelLipTent.lean` (N2). The ledger
row for `Update.bli_update_tierA_modulus` said `KernelLip sk L` had no witness here and that the
tent's constant was `bli-superbelief`'s. `bli-superbelief`'s `Modulus.tentLaw_l1_le` has landed
(its module imports only `bli-finite` and Mathlib, so the import is acyclic): the tent law is
`4·|S m|`-Lipschitz in `ℓ¹` — and it *refutes* the program's `2|S|` (`tentLaw_l1_two_witness`).
So `KernelLip (tentSkeleton smallIndex 𝓜) (fun m => 4·|smallSet m|)` holds (`kernelLip_tent`),
and the modulus row instantiates at the package's own N+ skeleton with `hQ` alone
(`bli_update_tierA_modulus_tent`).

**Not imported by the root module.** This is the package's only cross-package import beyond
its two declared dependencies (`bli-found`, `bli-finite`); whether dependents should carry a
dependency on `bli-superbelief`'s `Modulus` is the orchestrator's call at consolidation. The
module is gated (`scripts/wp-audit`) alongside the thirteen root modules.
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite

open Classical

noncomputable section

/-- **The tent skeleton has ℓ¹-modulus `4·|S m|`** (`bli-superbelief`'s `tentLaw_l1_le`; the
program's `2|S|` is false there).
Source: [[bli-program]] §3.4/§3.5 (iii) (constant corrected to `4|S|` by `bli-superbelief` E2(a));
audit r2 adversarial N2 (probe `KernelLipTent.lean`)
Kind: C
Fidelity: exact (constant `4|S m|`, not the program's `2|S|`)
Hyps: (a) none -/
theorem kernelLip_tent (𝓜 : Mesh) :
    KernelLip (tentSkeleton smallIndex 𝓜) (fun m => 4 * ((smallSet m).card : ℚ)) := by
  intro m t t' ε _ _ hε
  exact Cleanroom.Bli.BliSuperbelief.tentLaw_l1_le (𝒮 := smallIndex) (𝓜 := 𝓜) t t' hε

/-- **The modulus row at the tent instance**, with `hQ` alone: for Tier-A `ψ` (small part
mentioning no day-`(n+1)` atom), `|𝐏_{n+1}(ψ) 𝐏_n(σ) − 𝐏_n(ψ ⋏ σ)| ≤ 𝐏_n(σ) · 4|S_{n+1}| / (2 d_{n+1})`.
Source: [[bli-program]] §3.5 (iii); mandate M6 (modulus form); audit r2 adversarial N2
Kind: C
Fidelity: exact (the tent instance of `bli_update_tierA_modulus`)
Hyps: (a) `hQ`; (a) syntactic (`hψ`, `hs`) -/
theorem bli_update_tierA_modulus_tent {𝓜 : Mesh} (c : StateCoding 𝓜) (Q : RatHistory)
    (hQ : ∀ n φ, 0 ≤ Q n φ ∧ Q n φ ≤ 1) (n : ℕ) {ψ : Sentence} {l : List (ℕ × ℕ)}
    {s : Option Sentence} (hψ : tierA c (n + 1) ψ = some (l, s))
    (hs : ∀ φ, s = some φ → NoFutureState c n φ) :
    |bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c (n + 1) ψ *
        bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n
          (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) -
      bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n
        (ψ ⋏ stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1)))|
      ≤ bliHistory Q 𝓜 (tentSkeleton smallIndex 𝓜) c n
          (stateAtom (n + 1) ((bliStateSystem Q 𝓜 c).actual (n + 1))) *
          (((4 * ((smallSet (n + 1)).card : ℚ) : ℚ) : ℝ) / (2 * (𝓜.d (n + 1) : ℝ))) :=
  bli_update_tierA_modulus c (tentSkeleton smallIndex 𝓜) Q hQ (kernelLip_tent 𝓜) n hψ hs

end

end Cleanroom.Bli.BliTrajectory
