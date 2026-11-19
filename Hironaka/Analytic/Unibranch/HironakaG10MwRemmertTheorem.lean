import Hironaka.Analytic.Unibranch.HironakaG10MwRemmertFinal
import Hironaka.Analytic.Unibranch.HironakaG10RkImageDim

/-!
# Remmert's proper mapping theorem for reduced complex spaces (hF1 item 5; lanes G10MW, G10R2, G10R3)

**`nativeProperImage : NativeProperImage`**: for a morphism `f : Y ⟶ X` of reduced complex spaces and an
analytic `P ⊆ Y` on which `f` is proper, `f(P)` is analytic in `X`.  `isAnalyticSubset_image_of_isProperMap` is
the case of a proper morphism.

Assembled from `HironakaG10MwRemmertFinal.nativeProperImage_of_imageDim` and lane G10R3's image-dimension bound
`HironakaG10RkImageDim.add_le_of_regularAtDim_image`.  No named input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10MwRemmertTheorem

open SourceReducedComplexSpace Hironaka.Analytic.Unibranch.HironakaG10MwRemmertRegular

/-- **Remmert's proper mapping theorem for reduced complex spaces.** -/
theorem nativeProperImage : NativeProperImage :=
  HironakaG10MwRemmertFinal.nativeProperImage_of_imageDim
    fun _Y _ _k _M _ _ _ _C _hC φ _T hT _a _b ha hfib _w _j hw =>
      HironakaG10RkImageDim.add_le_of_regularAtDim_image φ hT ha hfib hw

/-- **Images of analytic sets under proper morphisms are analytic.** -/
theorem isAnalyticSubset_image_of_isProperMap {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) {P : Set Y.obj.left} (hP : Y.IsAnalyticSubset P) :
    X.IsAnalyticSubset (f.hom.left.base '' P) :=
  nativeProperImage X Y f P hP fun _K hK =>
    (hf.isCompact_preimage hK).inter_left hP.isClosed

end Hironaka.Analytic.Unibranch.HironakaG10MwRemmertTheorem
