/-
# Static-view factorization

This answers the conditional core of `PRIORITIES.md` item 28.  If an
architecture's value factors only through a price object and a realization object, then
architectures with equal projections receive equal values.  No probability, finiteness,
or Logical Induction premise is needed.

The conclusion is evaluative indistinguishability, not identity of architectures.  A
jurisdiction-sensitive functional exists in the worked case and necessarily fails the
factorization premise.  Thus the theorem does not say jurisdiction is valueless; it says
that jurisdiction must reach the valuation through an input not erased at the
factorization boundary.

All names are provisional (`AGENTS.md` standard 6).
-/

namespace Workspace.Deference.Contrib.StaticViewFactorization

universe uA uP uR uV

/-- A value functional sees an architecture only through its price and realization
projections. -/
def FactorsThroughStaticView {Architecture : Type uA} {Price : Type uP}
    {Realization : Type uR} {Value : Type uV}
    (price : Architecture → Price) (realization : Architecture → Realization)
    (value : Architecture → Value) : Prop :=
  ∃ score : Price → Realization → Value,
    ∀ architecture, value architecture = score (price architecture) (realization architecture)

/-- Any value functional factoring through `(price, realization)` is constant on each
fiber of that pair of projections. -/
theorem value_eq_of_price_realization_eq
    {Architecture : Type uA} {Price : Type uP} {Realization : Type uR} {Value : Type uV}
    {price : Architecture → Price} {realization : Architecture → Realization}
    {value : Architecture → Value} {left right : Architecture}
    (hfactor : FactorsThroughStaticView price realization value)
    (hprice : price left = price right)
    (hrealization : realization left = realization right) :
    value left = value right := by
  obtain ⟨score, hscore⟩ := hfactor
  rw [hscore left, hscore right, hprice, hrealization]

/-- When the whole architecture type is literally the static pair, agreement of both
coordinates gives literal identity.  This stronger conclusion does not apply to an
architecture carrying hidden authorization or transition state. -/
theorem staticView_eq {Price : Type uP} {Realization : Type uR}
    {left right : Price × Realization} (hprice : left.1 = right.1)
    (hrealization : left.2 = right.2) : left = right :=
  Prod.ext hprice hrealization

namespace WorkedCase

/-- A smallest architecture with jurisdiction present in the type but absent from the
static view. -/
structure Architecture where
  price : Bool
  realization : Bool
  jurisdiction : Bool
  deriving DecidableEq

def humanAuthorized : Architecture := ⟨false, true, true⟩
def agentAuthorized : Architecture := ⟨false, true, false⟩

def staticValue (architecture : Architecture) : Bool :=
  architecture.price && architecture.realization

def jurisdictionValue (architecture : Architecture) : Bool := architecture.jurisdiction

theorem jurisdiction_differs :
    humanAuthorized.jurisdiction ≠ agentAuthorized.jurisdiction := by decide

theorem price_agrees : humanAuthorized.price = agentAuthorized.price := rfl

theorem realization_agrees :
    humanAuthorized.realization = agentAuthorized.realization := rfl

theorem staticValue_factors :
    FactorsThroughStaticView Architecture.price Architecture.realization staticValue := by
  exact ⟨fun price realization => price && realization, fun _ => rfl⟩

/-- The main theorem is inhabited at two architectures with different jurisdiction and
identical static views. -/
theorem staticValue_agrees : staticValue humanAuthorized = staticValue agentAuthorized :=
  value_eq_of_price_realization_eq staticValue_factors price_agrees realization_agrees

theorem jurisdictionValue_differs :
    jurisdictionValue humanAuthorized ≠ jurisdictionValue agentAuthorized := by decide

/-- A functional that actually reads jurisdiction is a concrete counterexample to the
overstrong claim that no valuation can distinguish it.  What fails is precisely static
factorization. -/
theorem jurisdictionValue_not_static :
    ¬ FactorsThroughStaticView Architecture.price Architecture.realization
      jurisdictionValue := by
  intro hfactor
  exact jurisdictionValue_differs
    (value_eq_of_price_realization_eq hfactor price_agrees realization_agrees)

end WorkedCase

#print axioms value_eq_of_price_realization_eq
#print axioms staticView_eq
#print axioms WorkedCase.jurisdiction_differs
#print axioms WorkedCase.price_agrees
#print axioms WorkedCase.realization_agrees
#print axioms WorkedCase.staticValue_factors
#print axioms WorkedCase.staticValue_agrees
#print axioms WorkedCase.jurisdictionValue_differs
#print axioms WorkedCase.jurisdictionValue_not_static

end Workspace.Deference.Contrib.StaticViewFactorization
