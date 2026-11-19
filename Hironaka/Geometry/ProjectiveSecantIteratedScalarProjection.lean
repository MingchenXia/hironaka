import Hironaka.Geometry.ProjectiveSecantIteratedScalarSource
import Hironaka.Geometry.ProjectiveSecantProjectionSourceNaturality

/-!
# The actual direct original and iterated scalar point projections are isomorphic arrows
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

open BlowupProjectiveEmbedding ProjectiveSpaceBaseChange
open ProjectiveProjectionPoint ProjectiveRationalPointCoordinates ProjectiveLinearCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L K : Type u) [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] (χ : L →ₐ[k] K)
  (n : ℕ) {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]


variable (p : Spec (.of L) ⟶ projectiveSpace L (n + 1))
  (hp : p ≫ projectiveSpaceStructure L (n + 1) = 𝟙 _)
  (hout : pointImage L n p ∉ Set.range (scalarClosedInclusion k L (algebraMap k L) n i))


include hout

omit [IsClosedImmersion i] in
/-- The same actual lifted centre avoids the direct original source, internally through the whole iterated source isomorphism. -/
theorem iteratedOriginalScalar_centre_outside : pointImage K n (scalarPoint L K χ.toRingHom n p hp) ∉ Set.range (scalarClosedInclusion k K (algebraMap k K) n i) := by
  let e := iteratedOriginalScalarSourceIso k L K χ n i
  have H : e.hom ≫ (scalarClosedInclusion k K (algebraMap k K) n i) = (scalarClosedInclusion L K χ.toRingHom n (scalarClosedInclusion k L (algebraMap k L) n i)) := iteratedOriginalScalarSourceIso_embedding k L K χ n i
  have hout' := scalarClosedInclusion_centre_outside L K χ.toRingHom n (scalarClosedInclusion k L (algebraMap k L) n i) p hp hout
  rintro ⟨x, hx⟩
  apply hout'
  refine ⟨e.inv x, ?_⟩
  calc
    (scalarClosedInclusion L K χ.toRingHom n (scalarClosedInclusion k L (algebraMap k L) n i)) (e.inv x) = (e.inv ≫ (scalarClosedInclusion L K χ.toRingHom n (scalarClosedInclusion k L (algebraMap k L) n i))) x := rfl
    _ = (scalarClosedInclusion k K (algebraMap k K) n i) x := by rw [← H, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = pointImage K n (scalarPoint L K χ.toRingHom n p hp) := hx

/-- The whole actual projection comparison retains the SAME direct original source, actual centre, original scalar projection and internally produced target normalization. -/
theorem iteratedOriginalScalarProjection_comparison :
    (iteratedOriginalScalarSourceIso k L K χ n i).hom ≫
      projectionFromPoint K n (scalarPoint L K χ.toRingHom n p hp) (scalarPoint_structure L K χ.toRingHom n p hp) (scalarClosedInclusion k K (algebraMap k K) n i) (iteratedOriginalScalar_centre_outside k L K χ n i p hp hout) ≫
      (scalarPointTargetAutomorphism L K χ.toRingHom n p hp).inv =
    originalProjectionScalar L K χ.toRingHom n (projectionFromPoint L n p hp (scalarClosedInclusion k L (algebraMap k L) n i) hout)
      ((scalarClosedInclusion k L (algebraMap k L) n i) ≫ projectiveSpaceStructure L (n + 1)) (projectionFromPoint_structure L n p hp (scalarClosedInclusion k L (algebraMap k L) n i) hout) := by
  have N := projectionFromPoint_source_triangle K n (scalarPoint L K χ.toRingHom n p hp) (scalarPoint_structure L K χ.toRingHom n p hp) (scalarClosedInclusion k K (algebraMap k K) n i) (scalarClosedInclusion L K χ.toRingHom n (scalarClosedInclusion k L (algebraMap k L) n i))
    (iteratedOriginalScalarSourceIso k L K χ n i).hom
    (iteratedOriginalScalarSourceIso_embedding k L K χ n i)
    (iteratedOriginalScalar_centre_outside k L K χ n i p hp hout)
  have C := independentlyNormalizedScalarProjection_comparison L K χ.toRingHom n (scalarClosedInclusion k L (algebraMap k L) n i) p hp hout
  change projectionFromPoint K n (scalarPoint L K χ.toRingHom n p hp) (scalarPoint_structure L K χ.toRingHom n p hp) (scalarClosedInclusion L K χ.toRingHom n (scalarClosedInclusion k L (algebraMap k L) n i)) _ ≫ _ = _ at C
  rw [N] at C
  simpa only [Category.assoc] using C

/-- The entire actual source and target triangles internally construct the SAME original actual projection arrow isomorphism. -/
def iteratedOriginalScalarProjectionArrowIso :
    Arrow.mk (originalProjectionScalar L K χ.toRingHom n (projectionFromPoint L n p hp (scalarClosedInclusion k L (algebraMap k L) n i) hout)
      ((scalarClosedInclusion k L (algebraMap k L) n i) ≫ projectiveSpaceStructure L (n + 1)) (projectionFromPoint_structure L n p hp (scalarClosedInclusion k L (algebraMap k L) n i) hout)) ≅
    Arrow.mk (projectionFromPoint K n (scalarPoint L K χ.toRingHom n p hp) (scalarPoint_structure L K χ.toRingHom n p hp) (scalarClosedInclusion k K (algebraMap k K) n i) (iteratedOriginalScalar_centre_outside k L K χ n i p hp hout)) := by
  let e := iteratedOriginalScalarSourceIso k L K χ n i
  let E := scalarPointTargetAutomorphism L K χ.toRingHom n p hp
  refine Arrow.isoMk e E ?_
  have C := congrArg (fun m => m ≫ E.hom)
    (iteratedOriginalScalarProjection_comparison k L K χ n i p hp hout)
  simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, e, E, Category.assoc, Iso.inv_hom_id, Category.comp_id] using C

end Hironaka.Geometry.ProjectiveSecant
