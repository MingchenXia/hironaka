import DeJongAlterations.Geometry.NodeFamilyFlat
import DeJongAlterations.Algebra.NodeFamilyLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! Actual smooth open loci of the node coefficient morphism over an arbitrary ring. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.NodeFamilySmooth

open Algebra.NodeBlowupChart NodeFamilyFlat

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- The actual principal coordinate open of the original node spectrum. -/
def coordinateOpen (t : A) (i : Fin 2) : (Spec (CommRingCat.of (Node A t))).Opens :=
  PrimeSpectrum.basicOpen (coordinate t i)

/-- The literal coefficient morphism from the actual coordinate localization. -/
def coordinateMorphism (t : A) (i : Fin 2) :
    Spec (CommRingCat.of (Localization.Away (coordinate t i))) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (coordinate t i))))

/-- Smoothness of the actual localized node coefficient morphism. -/
theorem coordinateMorphism_smooth (t : A) (i : Fin 2) : Smooth (coordinateMorphism t i) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr
    (Algebra.NodeFamilyLocalization.coordinateOpen_smooth_of_index t i)

/-- The actual localization morphism has its exact coefficient structure triangle. -/
theorem coordinate_structure (t : A) (i : Fin 2) :
    Spec.map (CommRingCat.ofHom (algebraMap (Node A t) (Localization.Away (coordinate t i)))) ≫
      nodeMorphism t = coordinateMorphism t i := by
  dsimp only [nodeMorphism, coordinateMorphism]
  rw [← Spec.map_comp]
  congr 1

/-- The literal original node morphism is smooth on each actual coordinate open. -/
theorem nodeMorphism_smooth_on_coordinate (t : A) (i : Fin 2) :
    Smooth ((coordinateOpen t i).ι ≫ nodeMorphism t) := by
  let e := basicOpenIsoSpecAway (R := CommRingCat.of (Node A t)) (coordinate t i)
  let : Smooth (coordinateMorphism t i) := coordinateMorphism_smooth t i
  have h : e.hom ≫ coordinateMorphism t i = (coordinateOpen t i).ι ≫ nodeMorphism t := by
    rw [← coordinate_structure, ← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
    rfl
  rw [← h]
  infer_instance

local instance node_locallyOfFinitePresentation (t : A) : LocallyOfFinitePresentation (nodeMorphism t) :=
  nodeMorphism_locallyOfFinitePresentation t

/-- Each actual principal coordinate open lies in the native smooth locus. -/
theorem coordinateOpen_le_smoothLocus (t : A) (i : Fin 2) :
    coordinateOpen t i ≤ (nodeMorphism t).smoothLocus := by
  let : Smooth ((coordinateOpen t i).ι ≫ nodeMorphism t) := nodeMorphism_smooth_on_coordinate t i
  have h := Scheme.Hom.preimage_smoothLocus_eq (coordinateOpen t i).ι (nodeMorphism t)
  rw [Scheme.Hom.smoothLocus_eq_top ((coordinateOpen t i).ι ≫ nodeMorphism t)] at h
  intro x hx
  have hy : (⟨x, hx⟩ : coordinateOpen t i) ∈
      (coordinateOpen t i).ι ⁻¹ᵁ (nodeMorphism t).smoothLocus := by rw [h]; trivial
  exact hy

/-- The actual complement of the simultaneous coordinate-zero locus is smooth over the base. -/
theorem coordinateUnion_le_smoothLocus (t : A) :
    coordinateOpen t 0 ⊔ coordinateOpen t 1 ≤ (nodeMorphism t).smoothLocus :=
  sup_le (coordinateOpen_le_smoothLocus t 0) (coordinateOpen_le_smoothLocus t 1)

/-- A unit smoothing parameter makes the actual whole node family smooth. -/
theorem nodeMorphism_smooth_of_isUnit (t : A) (ht : IsUnit t) : Smooth (nodeMorphism t) := by
  have hp : coordinate t 0 * coordinate t 1 = algebraMap A (Node A t) t :=
    Algebra.NodeDomain.nodeCoordinateProduct t
  have huv : IsUnit (coordinate t 0 * coordinate t 1) := by
    rw [hp]
    exact ht.map (algebraMap A (Node A t))
  have hu : IsUnit (coordinate t 0) := isUnit_of_mul_isUnit_left huv
  have htop : coordinateOpen t 0 = ⊤ := by
    ext p
    change coordinate t 0 ∉ p.asIdeal ↔ True
    exact iff_true_intro (Ideal.notMem_of_isUnit p.asIdeal hu)
  apply (Scheme.Hom.smoothLocus_eq_top_iff).mp
  apply top_unique
  rw [← htop]
  exact coordinateOpen_le_smoothLocus t 0

end DeJongAlterations.Geometry.NodeFamilySmooth
