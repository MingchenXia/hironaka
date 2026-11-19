import Hironaka.Geometry.ProjectiveSecantProjectionComponentOpen
import Hironaka.Geometry.ProjectiveSecantProjectionGeneralImageOpen

/-!
# Actual whole-source native birational projection from a finite original smooth-point family

The original finite smooth-point family must meet every original component.
Producing this family from dense geometric reducedness remains a separate step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveRationalPointCoordinates ProjectiveProjectionPoint

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  {ι : Type v} [Finite ι] (s : ι → (Spec (CommRingCat.of k) ⟶ X))
  (hs : ∀ a, (s a ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hx : ∀ a, s a (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)
  (hdim : topologicalKrullDim X < n)
  (hcover : ∀ C ∈ irreducibleComponents X, ∃ a, s a (⊥ : PrimeSpectrum k) ∈ C)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hc : pointImage k n p ∈ smoothPointFamilyCenterOpen k n i s hs hx hdim)

/-- The actual original rational centre constructs the same actual point-centred projection of the whole source. -/
def projectionFromSmoothPointFamilyOpen : X ⟶ projectiveSpace k n :=
  projectionFromPoint k n p hp i (smoothPointFamilyCenterOpen_avoids_image k n i s hs hx hdim hcover _ hc)

/-- Finiteness is internally produced for this unchanged original projection. -/
theorem projectionFromSmoothPointFamilyOpen_isFinite :
    IsFinite (projectionFromSmoothPointFamilyOpen k n i s hs hx hdim hcover p hp hc) :=
  projectionFromPoint_isFinite _ _ _ _ _ _

/-- The actual original projection retains the entire original coefficient triangle. -/
@[reassoc]
theorem projectionFromSmoothPointFamilyOpen_structure :
    projectionFromSmoothPointFamilyOpen k n i s hs hx hdim hcover p hp hc ≫ projectiveSpaceStructure k n =
      i ≫ projectiveSpaceStructure k (n + 1) := projectionFromPoint_structure _ _ _ _ _ _

/-- Actual original componentwise smooth points produce native birationality onto the entire actual native image, without reducing either scheme. -/
theorem projectionFromSmoothPointFamilyOpen_birational :
    let f := projectionFromSmoothPointFamilyOpen k n i s hs hx hdim hcover p hp hc
    Scheme.BirationalOver f.toImage (𝟙 f.image) := by
  let f := projectionFromSmoothPointFamilyOpen k n i s hs hx hdim hcover p hp hc
  let : IsFinite f := projectionFromSmoothPointFamilyOpen_isFinite k n i s hs hx hdim hcover p hp hc
  apply toImage_birationalOver_of_component_point_data f
  intro C hC
  obtain ⟨a, ha⟩ := hcover C hC
  refine ⟨s a (⊥ : PrimeSpectrum k), ha, ?_⟩
  have hca := (mem_smoothPointFamilyCenterOpen_iff k n i s hs hx hdim _).mp hc a
  exact projectionFromGeneralTangentSecantOpen_point_data k n i (s a) (hs a) (hx a) hdim p hp hca

end Hironaka.Geometry.ProjectiveSecant
