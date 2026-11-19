import Hironaka.Analytic.Unibranch.HironakaG10MwRemmertAssembly
import Hironaka.Analytic.Unibranch.HironakaG10RkNativeRank
import Hironaka.Analytic.Unibranch.HironakaG10RkFibreDim

/-!
# Native Remmert: discharging the rank inputs (lane G10MW)

`rankInputs_of_imageDim` — the named input `RankInputs` of `HironakaG10MwRemmertAssembly` from lane G10R3's
items 5.3 (`HironakaG10RkNativeRank.isAnalyticSubset_rankDegeneracy`, `exists_maxRank_of_irreducible`) and 5.4
(`HironakaG10RkFibreDim.nativeLocDimGE_fibre`), given item 5.5 in its announced shape (`ImageDimStatement`);
`nativeProperImage_of_imageDim : ImageDimStatement → NativeProperImage`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10MwRemmertFinal

open Hironaka Hironaka AnalyticDimensionBasics
  SourceReducedComplexSpace HironakaG10EpNativeDim Hironaka.Analytic.Unibranch.HironakaG10MwRemmertRegular
  Hironaka.Analytic.Unibranch.HironakaG10MwRemmertAssembly

/-- **Item 5.5** in the shape announced by lane G10R3 (`HironakaG10RkImageDim`): the image of an analytic set of
dimension `≤ a` all of whose fibres have local dimension `≥ b` has regular points of dimension `≤ a - b`. -/
def ImageDimStatement : Prop :=
  ∀ (Y : SourceReducedComplexSpace) [SecondCountableTopology Y.obj.left] (k : ℕ) (M : Type)
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    (C : Set M) (hC : IsComplexAnalyticSubset (n := k) C) (φ : Y ⟶ ofClosedAnalytic C hC)
    (T : Set Y.obj.left), Y.IsAnalyticSubset T → ∀ a b, NativeDimLE Y T a →
      (∀ y ∈ T, HironakaG10RkFibreDim.NativeLocDimGE Y (T ∩ pointMap φ ⁻¹' {pointMap φ y}) y b) →
      ∀ w j, RegularAtDim (n := k) (pointMap φ '' T) w j → j + b ≤ a

/-- **`RankInputs` from items 5.3, 5.4 and 5.5.** -/
theorem rankInputs_of_imageDim (h55 : ImageDimStatement) : RankInputs := by
  intro Y _ d k M _ _ _ C hC φ hY
  refine ⟨HironakaG10RkNativeRank.isAnalyticSubset_rankDegeneracy φ hY, fun hirr => ?_,
    fun r hr T hT hsat a ha => h55 Y k M C hC φ T hT a (d - r) ha (fun y hy => ?_)⟩
  · obtain ⟨r, h1, h2, -⟩ := HironakaG10RkNativeRank.exists_maxRank_of_irreducible φ hY hirr
    exact ⟨r, h1, h2⟩
  · have hset : T ∩ pointMap φ ⁻¹' {pointMap φ y} = pointMap φ ⁻¹' {pointMap φ y} := by
      refine inter_eq_right.mpr fun z hz => hsat ⟨y, hy, ?_⟩
      exact (mem_singleton_iff.mp hz).symm
    rw [hset]
    exact HironakaG10RkFibreDim.nativeLocDimGE_fibre φ hY hr y

/-- **Native Remmert from item 5.5.** -/
theorem nativeProperImage_of_imageDim (h55 : ImageDimStatement) : NativeProperImage :=
  nativeProperImage_of_rankInputs (rankInputs_of_imageDim h55)

end Hironaka.Analytic.Unibranch.HironakaG10MwRemmertFinal
