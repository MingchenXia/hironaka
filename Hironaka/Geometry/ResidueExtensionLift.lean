import Hironaka.Algebra.ResidueExtensionLiftPoint
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Native finite free lifts and their actual etale base neighbourhood

The base open is the complement of the actual finite image of the derivative
zero locus. It controls the entire inverse image, not a selected source piece.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ResidueExtensionLift

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Hironaka.Algebra.ResidueExtensionLift

variable {R : Type u} [CommRing R] (P : Ideal R) [P.IsMaximal]
  (L : Type u) [Field L] [Algebra P.ResidueField L]
  [FiniteDimensional P.ResidueField L] [Algebra.IsSeparable P.ResidueField L]

/-- The actual native spectrum of the internally constructed monic root algebra. -/
def liftScheme : Scheme.{u} := Spec (.of (LiftRing P L))

/-- Its actual native finite-free coefficient morphism. -/
def structureMap : liftScheme P L ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (LiftRing P L)))

instance structureMap_isFinite : IsFinite (structureMap P L) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance structureMap_flat : Flat (structureMap P L) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- The entire actual scheme-theoretic fibre is the spectrum of the specified extension. -/
def fibreIso : (structureMap P L).fiber (⟨P, inferInstance⟩ : PrimeSpectrum R) ≅ Spec (.of L) :=
  (Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R (LiftRing P L) ⟨P, inferInstance⟩)) ≪≫
    Scheme.Spec.mapIso (fibreEquiv P L).toRingEquiv.toCommRingCatIso.symm.op

/-- The source derivative open is defined by the literal derivative of the lifted polynomial. -/
def derivativeOpen : (liftScheme P L).Opens := PrimeSpectrum.basicOpen (derivativeElement P L)

/-- The actual derivative open is etale over the original base. -/
theorem derivativeOpen_etale : Etale ((derivativeOpen P L).ι ≫ structureMap P L) := by
  let S := LiftRing P L
  let d := derivativeElement P L
  let : Algebra.Etale R (Localization.Away d) := derivativeLocalization_etale P L
  let : Etale (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away d)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  rw [show (derivativeOpen P L).ι = (basicOpenIsoSpecAway (R := .of S) d).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away d))) from
        (basicOpenIsoSpecAway_hom_SpecMap (R := .of S) d).symm, Category.assoc]
  have h : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away d))) ≫ structureMap P L =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away d))) := by
    rw [structureMap, ← Spec.map_comp]
    rfl
  rw [h]
  infer_instance

/-- The actual base neighbourhood removes the finite image of the entire derivative-zero locus. -/
def etaleBaseOpen : (Spec (.of R)).Opens :=
  ⟨(structureMap P L '' ((derivativeOpen P L : Set (liftScheme P L))ᶜ))ᶜ,
    ((structureMap P L).isClosedMap _ (derivativeOpen P L).isOpen.isClosed_compl).isOpen_compl⟩

/-- The original actual closed point belongs to the constructed base neighbourhood. -/
theorem mem_etaleBaseOpen : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ etaleBaseOpen P L := by
  rintro ⟨q, hq, hqP⟩
  have hqeq : q = liftPoint P L := unique_point_over P L q hqP
  subst q
  exact hq (derivative_not_mem_liftPrime P L)

/-- The entire inverse image of that base neighbourhood lies in the actual derivative open. -/
theorem preimage_etaleBaseOpen_le : structureMap P L ⁻¹ᵁ etaleBaseOpen P L ≤ derivativeOpen P L := by
  intro q hq
  by_contra hqd
  exact hq ⟨q, hqd, rfl⟩

/-- The actual full restricted finite-free map is etale above the actual neighbourhood. -/
theorem structureMap_restrict_etale : Etale (structureMap P L ∣_ etaleBaseOpen P L) := by
  let h := preimage_etaleBaseOpen_le P L
  let : Etale ((derivativeOpen P L).ι ≫ structureMap P L) := derivativeOpen_etale P L
  have hc : Etale ((structureMap P L ⁻¹ᵁ etaleBaseOpen P L).ι ≫ structureMap P L) := by
    have : Etale ((liftScheme P L).homOfLE h ≫
        (derivativeOpen P L).ι ≫ structureMap P L) := inferInstance
    simpa only [Scheme.homOfLE_ι_assoc] using this
  have : Etale ((structureMap P L ∣_ etaleBaseOpen P L) ≫ (etaleBaseOpen P L).ι) := by
    rw [morphismRestrict_ι]
    exact hc
  exact Etale.of_comp (structureMap P L ∣_ etaleBaseOpen P L) (etaleBaseOpen P L).ι

end Hironaka.Geometry.ResidueExtensionLift
