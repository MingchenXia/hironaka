import Hironaka.Geometry.ProjectiveSecantProjectionEtale

/-!
# A genuine original nonempty open of generically etale projection centres
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveProjectionPoint ProjectiveRationalPointCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original geometric dimension forces the actual original ambient generic point outside the SAME original closed image. -/
theorem genericPoint_not_mem_original_image
    (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (hdim : topologicalKrullDim X = n) :
    genericPoint (projectiveSpace k (n + 1)) ∉ Set.range i := by
  intro hgen
  have hclosed : IsClosed (Set.range i) := i.isClosedMap.isClosed_range
  have hsurj : Function.Surjective i := fun y =>
    (genericPoint_specializes y).mem_closed hclosed hgen
  have hhomeo : IsHomeomorph i := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨i.isClosedEmbedding.isEmbedding, hsurj⟩
  have hd := hhomeo.topologicalKrullDim_eq
  rw [hdim, projectiveSpace_dimension] at hd
  have hn : n ≠ n + 1 := by omega
  apply hn
  exact_mod_cast hd

variable (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}} [IsIntegral X]
  (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hdim : topologicalKrullDim X = n)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)

/-- The actual original parameter open is internally computed from the original tangent form and SAME original closed source image. -/
def projectionEtaleCenterOpen : (projectiveSpace k (n + 1)).Opens :=
  originalTangentOpen k n i s hs hdim.le hx ⊓
    ⟨(Set.range i)ᶜ, i.isClosedMap.isClosed_range.isOpen_compl⟩

omit [IsIntegral X] in
/-- The SAME actual original ambient generic point internally witnesses nonemptiness of this SAME original geometric centre open. -/
theorem projectionEtaleCenterOpen_nonempty :
    (projectionEtaleCenterOpen k n i s hs hdim hx : Set (projectiveSpace k (n + 1))).Nonempty := by
  refine ⟨genericPoint (projectiveSpace k (n + 1)), ?_, genericPoint_not_mem_original_image k n i hdim⟩
  exact (genericPoint_spec (projectiveSpace k (n + 1))).mem_open_set_iff
    (originalTangentOpen k n i s hs hdim.le hx).isOpen |>.mpr
      (by simpa using originalTangentOpen_nonempty k n i s hs hdim.le hx)

/-- Every actual original rational centre in this internally produced actual nonempty open gives the SAME original finite dominant generically etale projection, with an internally produced actual dense target etale open. -/
theorem originalProjection_from_etaleCenterOpen
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ projectionEtaleCenterOpen k n i s hs hdim hx) :
    let f := projectionFromPoint k n p hp i hc.2
    IsFinite f ∧ IsDominant f ∧ IsGenericallyEtale f ∧
      ∃ V : (projectiveSpace k n).Opens, genericPoint (projectiveSpace k n) ∈ V ∧
        Dense (V : Set (projectiveSpace k n)) ∧ Etale (f ∣_ V) := by
  exact ⟨projectionFromPoint_isFinite k n p hp i hc.2,
    originalProjection_isDominant_of_dimension_eq k n i p hp hc.2 hdim,
    originalProjection_isGenericallyEtale k n i p hp s hs hdim hx hc.2 hc.1,
    exists_originalProjection_dense_target_etale_open k n i p hp s hs hdim hx hc.2 hc.1⟩

end Hironaka.Geometry.ProjectiveSecant
