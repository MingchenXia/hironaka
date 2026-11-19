import Hironaka.Geometry.ProjectiveSecantIteratedScalarProjection
import Hironaka.Geometry.ProjectiveSecantOriginalParameterCenter
import Hironaka.Geometry.GenericPropertyArrowIso
import Hironaka.Geometry.ProjectiveScalarPropertyDescent

/-!
# Generic properties descend to the SAME actual original separable point projection
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

open BlowupProjectiveEmbedding ProjectiveProjectionPoint ProjectiveRationalPointCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsSeparable k L]
  (n : ℕ) {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (p : Spec (.of L) ⟶ projectiveSpace L (n + 1))
  (hp : p ≫ projectiveSpaceStructure L (n + 1) = 𝟙 _)
  (hout : pointImage L n p ∉ Set.range (scalarClosedInclusion k L (algebraMap k L) n i))

/-- Native generic etaleness on the SAME original separable closure source descends to the SAME actual original separable point projection. -/
theorem projectionFromPoint_genericallyEtale_of_separableClosure
    (hGE : IsGenericallyEtale
      (projectionFromPoint (SeparableClosure k) n (separableClosureCenter k L n p hp)
        (separableClosureCenter_structure k L n p hp)
        (scalarClosedInclusion k (SeparableClosure k) (algebraMap k (SeparableClosure k)) n i)
        (iteratedOriginalScalar_centre_outside k L (SeparableClosure k)
          (originalSeparableClosureEmbedding k L) n i p hp hout))) :
    IsGenericallyEtale (projectionFromPoint L n p hp
      (scalarClosedInclusion k L (algebraMap k L) n i) hout) := by
  let χ := originalSeparableClosureEmbedding k L
  let iL := scalarClosedInclusion k L (algebraMap k L) n i
  let f := projectionFromPoint L n p hp iL hout
  let pX := iL ≫ projectiveSpaceStructure L (n + 1)
  let e := iteratedOriginalScalarProjectionArrowIso k L (SeparableClosure k) χ n i p hp hout
  have hscalar := GenericPropertyArrowIso.genericallyEtale_of_arrowIso _ _ e.symm hGE
  exact ProjectiveScalarPropertyDescent.genericallyEtale_descent L (SeparableClosure k)
    χ.toRingHom n f pX (projectionFromPoint_structure L n p hp iL hout)
    (originalSeparableClosureEmbedding_isIntegral k L) hscalar

/-- Native BR onto the ENTIRE original native image descends from the SAME actual direct original closure projection, retaining all original components and nilpotents. -/
theorem projectionFromPoint_toImage_birationalOver_of_separableClosure
    (hBR : Scheme.BirationalOver
      (projectionFromPoint (SeparableClosure k) n (separableClosureCenter k L n p hp)
        (separableClosureCenter_structure k L n p hp)
        (scalarClosedInclusion k (SeparableClosure k) (algebraMap k (SeparableClosure k)) n i)
        (iteratedOriginalScalar_centre_outside k L (SeparableClosure k)
          (originalSeparableClosureEmbedding k L) n i p hp hout)).toImage (𝟙 _)) :
    Scheme.BirationalOver (projectionFromPoint L n p hp
      (scalarClosedInclusion k L (algebraMap k L) n i) hout).toImage (𝟙 _) := by
  let χ := originalSeparableClosureEmbedding k L
  let iL := scalarClosedInclusion k L (algebraMap k L) n i
  let f := projectionFromPoint L n p hp iL hout
  let pX := iL ≫ projectiveSpaceStructure L (n + 1)
  let e := iteratedOriginalScalarProjectionArrowIso k L (SeparableClosure k) χ n i p hp hout
  have hscalar := GenericPropertyArrowIso.toImage_birationalOver_of_arrowIso _ _ e.symm hBR
  exact ProjectiveScalarPropertyDescent.toImage_birationalOver_descent L (SeparableClosure k)
    χ.toRingHom n f pX (projectionFromPoint_structure L n p hp iL hout)
    (originalSeparableClosureEmbedding_isIntegral k L) hscalar

end Hironaka.Geometry.ProjectiveSecant
