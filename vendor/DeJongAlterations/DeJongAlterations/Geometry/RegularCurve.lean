import DeJongAlterations.Regular
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Normal curves are regular

Normality is expressed on the actual scheme local rings. The dimension-one
regularity result imposes no assumptions on residue fields or characteristic.
-/

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations

/-- A scheme is normal when all its local rings are integrally closed domains. -/
def IsNormalScheme (X : Scheme) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-- A normal Noetherian local domain of dimension at most one is regular. -/
theorem isRegularLocalRing_of_isIntegrallyClosed_of_krullDimLE_one
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Ring.KrullDimLE 1 R] : IsRegularLocalRing R := by
  let : Ring.DimensionLEOne R := ⟨fun _ hP ↦ hP.isMaximal_of_ne_bot ‹_›⟩
  let : IsDedekindRing R := .mk
  let : IsDedekindDomain R := .mk
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing R

/-- A scheme dimension bound also bounds every actual local ring. -/
theorem krullDimLE_stalk_of_topologicalKrullDim_le (X : Scheme) {n : ℕ}
    (hdim : topologicalKrullDim X ≤ n) (x : X) :
    Ring.KrullDimLE n (X.presheaf.stalk x) := by
  have horder : Order.krullDim X ≤ n := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  have hcoheight : Order.coheight x ≤ (n : ℕ∞) := by
    exact_mod_cast (Order.coheight_le_krullDim x).trans horder
  exact krullDimLE_of_coheight_le hcoheight

/-- Every normal locally Noetherian scheme of dimension at most one is regular. -/
theorem isRegularScheme_of_isNormalScheme_of_topologicalKrullDim_le_one
    (X : Scheme) [IsLocallyNoetherian X] (hnormal : IsNormalScheme X)
    (hdim : topologicalKrullDim X ≤ 1) : IsRegularScheme X := by
  intro x
  let := (hnormal x).1
  let := (hnormal x).2
  let := krullDimLE_stalk_of_topologicalKrullDim_le X hdim x
  exact isRegularLocalRing_of_isIntegrallyClosed_of_krullDimLE_one (X.presheaf.stalk x)

/-- The spectrum of an integrally closed domain is normal, with its actual local rings. -/
theorem isNormalScheme_spec (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsNormalScheme (Spec (CommRingCat.of R)) := by
  intro x
  let p : PrimeSpectrum R := x
  let : p.asIdeal.IsPrime := p.isPrime
  let : Algebra R ((Spec (.of R)).presheaf.stalk x) := StructureSheaf.stalkAlgebra R p
  let : IsLocalization.AtPrime ((Spec (.of R)).presheaf.stalk x) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R p
  refine ⟨inferInstance, ?_⟩
  apply isIntegrallyClosed_of_isLocalization _ p.asIdeal.primeCompl
  intro a ha
  exact mem_nonZeroDivisors_iff_ne_zero.mpr fun hzero ↦ ha (hzero ▸ p.asIdeal.zero_mem)

/-- Noetherian normal affine curves are regular over arbitrary ground fields. -/
theorem isRegularScheme_spec_of_isIntegrallyClosed_of_krullDimLE_one (R : Type*)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Ring.KrullDimLE 1 R] : IsRegularScheme (Spec (CommRingCat.of R)) := by
  apply isRegularScheme_of_isNormalScheme_of_topologicalKrullDim_le_one _
    (isNormalScheme_spec R)
  change topologicalKrullDim (PrimeSpectrum R) ≤ 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact Ring.krullDimLE_iff.mp inferInstance

end DeJongAlterations
