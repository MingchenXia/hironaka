import Hironaka.Geometry.ProjectiveSecantScalarGeometricOpen
import Hironaka.Geometry.ProjectiveSecantIntegralDimension
import Hironaka.Geometry.ProjectiveSecantProjectiveOpenDescent
import Hironaka.Geometry.ProjectiveSecantGeometricBirationalOpen
import Hironaka.Geometry.ProjectiveSecantProjectionTangentFamilyOpen
import Hironaka.Geometry.ProjectiveSecantProjectionScalarComparison

/-!
# The paper's actual original hypotheses internally produce an original birational parameter open

Birationality here is on the same actual canonical separable-closure source.
Descent of that property to all finite separable fields remains separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveRationalPointCoordinates ProjectiveProjectionPoint BlowupProjectiveEmbedding

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Arbitrary original field and actual original geometric hypotheses internally produce an actual nonempty ORIGINAL parameter open, outside the entire original image, with native BR of every same actual original normalized projection over the same separable closure. -/
theorem exists_original_birational_parameter_open_over_separableClosure
    (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (U : X.Opens) (hU : Dense (U : Set X))
    [GeometricallyReduced (U.ι ≫ (i ≫ projectiveSpaceStructure k (n + 1)))]
    (hdim : topologicalKrullDim X < n) :
    let K := SeparableClosure k
    let iK := scalarClosedInclusion k K (algebraMap k K) n i
    ∃ O : (projectiveSpace k (n + 1)).Opens, (O : Set (projectiveSpace k (n + 1))).Nonempty ∧
      (O : Set (projectiveSpace k (n + 1))) ⊆ (Set.range i)ᶜ ∧
      ∀ (p : Spec (.of K) ⟶ projectiveSpace K (n + 1))
        (hp : p ≫ projectiveSpaceStructure K (n + 1) = 𝟙 _),
        projectiveCoefficientMap (algebraMap k K) (n + 1) (pointImage K n p) ∈ O →
        ∃ hout : pointImage K n p ∉ Set.range iK,
          IsFinite (projectionFromPoint K n p hp iK hout) ∧
          projectionFromPoint K n p hp iK hout ≫ projectiveSpaceStructure K n =
            iK ≫ projectiveSpaceStructure K (n + 1) ∧
          Scheme.BirationalOver (projectionFromPoint K n p hp iK hout).toImage
            (𝟙 (projectionFromPoint K n p hp iK hout).image) := by
  let K := SeparableClosure k
  let φ := algebraMap k K
  let pX := i ≫ projectiveSpaceStructure k (n + 1)
  let iK := scalarClosedInclusion k K φ n i
  let UK := originalScalarOpen k K φ pX U
  have hUK : Dense (UK : Set (pullback pX (Spec.map (CommRingCat.ofHom φ)) : Scheme.{u})) :=
    originalScalarOpen_dense k K φ pX U hU
  let : GeometricallyReduced (UK.ι ≫ (iK ≫ projectiveSpaceStructure K (n + 1))) := by
    rw [scalarClosedInclusion_structure]
    exact originalScalarOpen_geometricallyReduced k K φ pX U
  have hdimK : topologicalKrullDim (pullback pX (Spec.map (CommRingCat.ofHom φ)) : Scheme.{u}) < n :=
    (topologicalKrullDim_algebraicScalar_le k K pX).trans_lt hdim
  obtain ⟨OK, hOK, hgood⟩ :=
    exists_original_birational_center_open_of_isSepClosed K n iK UK hUK hdimK
  obtain ⟨V, hV, hpre⟩ :=
    exists_original_projective_open_under_algebraicScalar k K (n + 1) OK hOK
  let C : (projectiveSpace k (n + 1)).Opens :=
    ⟨(Set.range i)ᶜ, i.isClosedMap.isClosed_range.isOpen_compl⟩
  let O := V ⊓ C
  have hηV : genericPoint (projectiveSpace k (n + 1)) ∈ V :=
    (genericPoint_spec _).mem_open_set_iff V.isOpen |>.mpr (by simpa using hV)
  have hηC : genericPoint (projectiveSpace k (n + 1)) ∈ C :=
    genericPoint_not_mem_original_image_of_dimension_le k n i hdim.le
  refine ⟨O, ⟨_, hηV, hηC⟩, inf_le_right, ?_⟩
  intro p hp hc
  exact hgood p hp (hpre hc.1)

end Hironaka.Geometry.ProjectiveSecant
