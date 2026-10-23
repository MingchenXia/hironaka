import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Local overrings of valuation rings in their own fraction fields

The local-map condition forces an actual injective overring to equal the
valuation ring. Normal Noetherian local domains of dimension at most one are
valuation rings, including the zero-dimensional field case.
-/

noncomputable section

namespace DeJongAlterations.Algebra.DiscreteValuationOverring

/-- An injective local overring of a valuation ring in its actual fraction
field is the original ring. The comparison is the given coefficient map. -/
theorem bijective_of_local_overring
    {R S K : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsLocalRing S] [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R →+* S) (g : S →+* K) [IsLocalHom f]
    (hg : Function.Injective g) (h : g.comp f = algebraMap R K) :
    Function.Bijective f := by
  have H := bijective_rangeRestrict_comp_of_valuationRing f g h
  refine ⟨Function.Injective.of_comp (f := g) ?_, ?_⟩
  · rw [← RingHom.coe_comp, h]
    exact IsFractionRing.injective R K
  · intro s
    obtain ⟨r, hr⟩ := H.2 (g.rangeRestrict s)
    exact ⟨r, hg (congrArg Subtype.val hr)⟩

/-- A normal Noetherian local domain of dimension at most one is a valuation
ring. This formulation includes fields and needs no choice of uniformizer. -/
theorem valuationRing_of_normal_dimLE_one
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Ring.KrullDimLE 1 R] :
    ValuationRing R := by
  let : Ring.DimensionLEOne R := ⟨fun _ hP => hP.isMaximal_of_ne_bot ‹_›⟩
  let : IsDedekindRing R := .mk
  let : IsDedekindDomain R := .mk
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 2 1).mp
    (inferInstance : IsDedekindDomain R)

end DeJongAlterations.Algebra.DiscreteValuationOverring
