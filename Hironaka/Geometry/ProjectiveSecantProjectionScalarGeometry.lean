import Hironaka.Geometry.ProjectiveSecantProjectionScalarComparison
import Hironaka.Geometry.ProjectiveSecantProjectionTargetIso
import Hironaka.Geometry.ProjectiveSecantProjectionScalarBirational

/-!
# Genuine native GE and birationality of the SAME independently normalized scalar projection
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveProjectionPoint ProjectiveRationalPointCoordinates ProjectiveLinearCoordinates
open BlowupProjectiveEmbedding

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME independently normalized actual scalar projection is the SAME canonical original projection's scalar extension followed by its internally constructed actual target automorphism. -/
theorem independentlyNormalizedScalarProjection_eq_scalar_comp_target
    (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
    {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _) (hout : pointImage k n p ∉ Set.range i) :
    independentlyNormalizedScalarProjection k L φ n i p hp hout =
      originalProjectionScalar k L φ n (projectionFromPoint k n p hp i hout)
        (i ≫ projectiveSpaceStructure k (n + 1)) (projectionFromPoint_structure k n p hp i hout) ≫
      (scalarPointTargetAutomorphism k L φ n p hp).hom := by
  let E := scalarPointTargetAutomorphism k L φ n p hp
  have h := congrArg (fun m => m ≫ E.hom)
    (independentlyNormalizedScalarProjection_comparison k L φ n i p hp hout)
  change (independentlyNormalizedScalarProjection k L φ n i p hp hout ≫ E.inv) ≫ E.hom = _ at h
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- Native generic etaleness of the SAME original projection transports to its SAME independently normalized actual scalar projection, via the internally proved ENTIRE original map comparison. -/
theorem independentlyNormalizedScalarProjection_isGenericallyEtale
    (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
    {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _) (hout : pointImage k n p ∉ Set.range i)
    (hf : IsGenericallyEtale (projectionFromPoint k n p hp i hout)) :
    IsGenericallyEtale (independentlyNormalizedScalarProjection k L φ n i p hp hout) := by
  rw [independentlyNormalizedScalarProjection_eq_scalar_comp_target]
  exact (originalProjectionScalar_isGenericallyEtale k L φ n _ hf _ _).comp
    (isGenericallyEtale_of_etale (scalarPointTargetAutomorphism k L φ n p hp).hom)

/-- Actual original codimension-one general-position geometry internally gives finite plus native GE of the SAME independently normalized actual new scalar projection, with no finite/GE or scalar-integrality certificate supplied. -/
theorem originalProjection_from_etaleCenterOpen_independent_scalar
    (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
    {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hdim : topologicalKrullDim X = n)
    (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ projectionEtaleCenterOpen k n i s hs hdim hx) :
    IsFinite (independentlyNormalizedScalarProjection k L φ n i p hp hc.2) ∧
      IsGenericallyEtale (independentlyNormalizedScalarProjection k L φ n i p hp hc.2) :=
  ⟨independentlyNormalizedScalarProjection_isFinite k L φ n i p hp hc.2,
    independentlyNormalizedScalarProjection_isGenericallyEtale k L φ n i p hp hc.2
      (originalProjection_isGenericallyEtale k n i p hp s hs hdim hx hc.2 hc.1)⟩

/-- Actual original lower-dimensional general-position geometry internally gives finite plus native BR onto the SAME actual native image of the SAME independently normalized actual scalar projection, without scalar integrality, image or birationality certificates. -/
theorem originalProjection_from_tangentSecantOpen_independent_scalar
    (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
    {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hsmall : topologicalKrullDim X < n)
    (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ tangentSecantCenterOpen k n i s hs hx hsmall) :
    let hout := fixedPointCenterOpen_avoids_image k n (s ≫ i) hs i hsmall _ hc.2
    let g := independentlyNormalizedScalarProjection k L φ n i p hp hout
    IsFinite g ∧ Scheme.BirationalOver g.toImage (𝟙 g.image) := by
  let hout := fixedPointCenterOpen_avoids_image k n (s ≫ i) hs i hsmall _ hc.2
  let g := independentlyNormalizedScalarProjection k L φ n i p hp hout
  let f := originalProjectionScalar k L φ n (projectionFromPoint k n p hp i hout)
    (i ≫ projectiveSpaceStructure k (n + 1)) (projectionFromPoint_structure k n p hp i hout)
  have hb : Scheme.BirationalOver f.toImage (𝟙 f.image) :=
    (originalProjection_from_tangentSecantOpen_scalar k L φ n i s hs hsmall hx p hp hc).2.1
  exact ⟨independentlyNormalizedScalarProjection_isFinite k L φ n i p hp hout,
    toImage_birationalOver_of_targetIso f g (scalarPointTargetAutomorphism k L φ n p hp)
      (independentlyNormalizedScalarProjection_eq_scalar_comp_target k L φ n i p hp hout) hb⟩

end Hironaka.Geometry.ProjectiveSecant
