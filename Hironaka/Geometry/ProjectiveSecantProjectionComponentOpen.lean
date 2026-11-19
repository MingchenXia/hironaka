import Hironaka.Geometry.ProjectiveSecantGeneralTangentOpen
import Hironaka.Geometry.ProjectiveSecantProjectionComponentBirational

/-!
# Actual finite smooth-point families produce an original nonempty centre open
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

/-- The finite original smooth-point family internally determines all tangent and whole-source secant conditions. -/
def smoothPointFamilyCenterOpen : (projectiveSpace k (n + 1)).Opens :=
  ⨅ a, generalTangentSecantCenterOpen k n i (s a) (hs a) (hx a) hdim

/-- Native finite intersection membership is exactly membership in every original geometric factor. -/
theorem mem_smoothPointFamilyCenterOpen_iff (c : projectiveSpace k (n + 1)) :
    c ∈ smoothPointFamilyCenterOpen k n i s hs hx hdim ↔
      ∀ a, c ∈ generalTangentSecantCenterOpen k n i (s a) (hs a) (hx a) hdim := by
  change c ∈ (((⨅ a, generalTangentSecantCenterOpen k n i (s a) (hs a) (hx a) hdim) :
    (projectiveSpace k (n + 1)).Opens) : Set (projectiveSpace k (n + 1))) ↔ _
  rw [Opens.coe_iInf, Set.mem_iInter]
  rfl

/-- The same actual ambient generic point lies in all internally computed original family conditions. -/
theorem smoothPointFamilyCenterOpen_mem_generic :
    ambientGenericPoint k n ∈ smoothPointFamilyCenterOpen k n i s hs hx hdim := by
  apply (mem_smoothPointFamilyCenterOpen_iff k n i s hs hx hdim _).mpr
  intro a
  exact ⟨originalTangentOpen_mem_generic k n i (s a) (hs a) hdim.le (hx a),
    generalFixedPointCenterOpen_mem_generic k n i (s a ≫ i) (hs a) hdim⟩

/-- This is an actual nonempty open in the unchanged original centre parameter scheme. -/
theorem smoothPointFamilyCenterOpen_nonempty :
    (smoothPointFamilyCenterOpen k n i s hs hx hdim : Set (projectiveSpace k (n + 1))).Nonempty :=
  ⟨ambientGenericPoint k n, smoothPointFamilyCenterOpen_mem_generic k n i s hs hx hdim⟩

variable (hcover : ∀ C ∈ irreducibleComponents X, ∃ a, s a (⊥ : PrimeSpectrum k) ∈ C)

include hcover in
/-- Meeting every original component derives whole-image avoidance, including the empty-source case. -/
theorem smoothPointFamilyCenterOpen_avoids_image (c : projectiveSpace k (n + 1))
    (hc : c ∈ smoothPointFamilyCenterOpen k n i s hs hx hdim) : c ∉ Set.range i := by
  rintro ⟨x, rfl⟩
  obtain ⟨a, _⟩ := hcover (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
  exact generalFixedPointCenterOpen_avoids_image k n (s a ≫ i) (hs a) i hdim _
    (((mem_smoothPointFamilyCenterOpen_iff k n i s hs hx hdim _).mp hc a).2) ⟨x, rfl⟩

end Hironaka.Geometry.ProjectiveSecant
