/-! Load-bearing mechanism for the finite revision trilemma. -/

namespace NormativeLearner.Migration

/-- If a proposed new ontology identifies two comparison states that a live old
observable separates, that observable cannot be represented exactly by a
new-ontology-only function.  A residual legacy carrier, suspension, or explicit
loss is therefore unavoidable. -/
theorem noExactNewOnlyTransport
    {Arena Ontology Value : Type}
    (π : Arena → Ontology) (liveValue : Arena → Value)
    (left right : Arena)
    (hcollapse : π left = π right)
    (hseparate : liveValue left ≠ liveValue right) :
    ¬ ∃ transported : Ontology → Value, ∀ state : Arena,
      liveValue state = transported (π state) := by
  rintro ⟨transported, htransport⟩
  apply hseparate
  calc
    liveValue left = transported (π left) := htransport left
    _ = transported (π right) := congrArg transported hcollapse
    _ = liveValue right := (htransport right).symm

end NormativeLearner.Migration
