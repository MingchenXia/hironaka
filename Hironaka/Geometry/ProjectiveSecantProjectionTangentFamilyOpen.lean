import Hironaka.Geometry.ProjectiveSecantProjectionComponentEtale
import Hironaka.Geometry.ProjectiveSecantProjectionEtaleOpen

/-!
# An actual nonempty tangent-family centre open for the whole original pure-dimensional source
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveRationalPointCoordinates ProjectiveProjectionPoint

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual original dimension alone puts the original ambient generic point outside the entire original closed image. -/
theorem genericPoint_not_mem_original_image_of_dimension_le
    (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (hdim : topologicalKrullDim X ≤ n) :
    genericPoint (projectiveSpace k (n + 1)) ∉ Set.range i := by
  intro hgen
  have hclosed : IsClosed (Set.range i) := i.isClosedMap.isClosed_range
  have hsurj : Function.Surjective i := fun y =>
    (genericPoint_specializes y).mem_closed hclosed hgen
  have hhomeo : IsHomeomorph i := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨i.isClosedEmbedding.isEmbedding, hsurj⟩
  have hd := hhomeo.topologicalKrullDim_eq
  rw [projectiveSpace_dimension] at hd
  rw [hd] at hdim
  have hn : n + 1 ≤ n := by exact_mod_cast hdim
  omega

variable (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
  (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  {ι : Type v} [Finite ι] (s : ι → (Spec (CommRingCat.of k) ⟶ X))
  (hs : ∀ a, (s a ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hx : ∀ a, s a (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)
  (hdim : topologicalKrullDim X ≤ n)

/-- The actual original tangent conditions and entire original image complement determine the original centre open. -/
def tangentPointFamilyCenterOpen : (projectiveSpace k (n + 1)).Opens :=
  (⨅ a, originalTangentOpen k n i (s a) (hs a) hdim (hx a)) ⊓
    ⟨(Set.range i)ᶜ, i.isClosedMap.isClosed_range.isOpen_compl⟩

/-- A genuine actual original ambient generic point witnesses nonemptiness of all computed original conditions. -/
theorem tangentPointFamilyCenterOpen_nonempty :
    (tangentPointFamilyCenterOpen k n i s hs hx hdim : Set (projectiveSpace k (n + 1))).Nonempty := by
  refine ⟨genericPoint (projectiveSpace k (n + 1)), ?_, genericPoint_not_mem_original_image_of_dimension_le k n i hdim⟩
  change genericPoint (projectiveSpace k (n + 1)) ∈
    (((⨅ a, originalTangentOpen k n i (s a) (hs a) hdim (hx a)) :
      (projectiveSpace k (n + 1)).Opens) : Set (projectiveSpace k (n + 1)))
  rw [Opens.coe_iInf, Set.mem_iInter]
  intro a
  exact (genericPoint_spec (projectiveSpace k (n + 1))).mem_open_set_iff
    (originalTangentOpen k n i (s a) (hs a) hdim (hx a)).isOpen |>.mpr
      (by simpa using originalTangentOpen_nonempty k n i (s a) (hs a) hdim (hx a))

omit [Finite ι] in
/-- Actual original pure dimensions and actual original smooth points meeting every component internally give native GE of the SAME original finite projection for every actual rational centre in the computed original open. -/
theorem projectionFromTangentPointFamilyOpen_isGenericallyEtale
    (hpure : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = n)
    (hcover : ∀ C ∈ irreducibleComponents X, ∃ a, s a (⊥ : PrimeSpectrum k) ∈ C)
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ tangentPointFamilyCenterOpen k n i s hs hx hdim) :
    IsGenericallyEtale (projectionFromPoint k n p hp i hc.2) := by
  let f := projectionFromPoint k n p hp i hc.2
  let : IsFinite f := projectionFromPoint_isFinite k n p hp i hc.2
  let : IsLocallyNoetherian (projectiveSpace k n) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceStructure k n)
  let : IsVariety (projectiveSpaceStructure k n) := .mk
  apply genericallyEtale_of_component_dimension_and_stalks (projectiveSpaceStructure k n) f
  · intro C hC
    rw [projectiveSpace_dimension, hpure C hC]
  · intro C hC
    obtain ⟨a, ha⟩ := hcover C hC
    refine ⟨s a (⊥ : PrimeSpectrum k), ha, ?_⟩
    have hca : pointImage k n p ∈ originalTangentOpen k n i (s a) (hs a) hdim (hx a) :=
      (iInf_le (fun b => originalTangentOpen k n i (s b) (hs b) hdim (hx b)) a) hc.1
    exact projectionFromPoint_stalkMap_formallyUnramified k n i p hp (s a) (hs a) hdim (hx a) hc.2 hca

end Hironaka.Geometry.ProjectiveSecant
