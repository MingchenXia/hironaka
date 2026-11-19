import Hironaka.Geometry.CurveFibrationBaseChangeBoundaryComparison
import Hironaka.Geometry.CurveFibrationBaseChangePaperModel
import Hironaka.Geometry.FiniteGenericallyEtaleOpen
import Hironaka.Geometry.CartierBoundarySectionComponents

/-!
# Actual generic etaleness of the whole reduced inverse boundary

The original finite boundary gives a genuine target etale open. The
actual reduced comparison is an isomorphism there. Actual Cartier
component dimensions derive density in the whole new boundary.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.IdealSheafData
open Hironaka.Geometry.CartierBoundaryComponentDimension
open Hironaka.Geometry.CartierBoundaryDominance

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {B X S Y T : Scheme.{u}}

/-- Restricted native Cartesian squares genuinely pull an original target etale open back. -/
theorem pullback_snd_etale_on_preimage (b : B ⟶ S) (g : Y ⟶ S) (V : S.Opens)
    [Etale (b ∣_ V)] : Etale ((pullback.snd b g) ∣_ (g ⁻¹ᵁ V)) := by
  let A := b ⁻¹ᵁ V
  let U := g ⁻¹ᵁ V
  let m := pullback.fst b g
  let n := pullback.snd b g
  let W := n ⁻¹ᵁ U
  have hW : m ⁻¹ᵁ A = W := by
    dsimp [m, n, A, U, W]
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback b g)
    (US := V) (UT := U) (UX := A) (UY := W) le_rfl le_rfl (by rw [hW, inf_idem])
  let : Etale (b.resLE V A le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have he : Etale (n.resLE U W le_rfl) := MorphismProperty.of_isPullback H inferInstance
  simpa only [W, Scheme.Hom.resLE_eq_morphismRestrict] using he

/-- Actual component dominance gives density in the WHOLE actual reduced support. -/
theorem dense_reducedBoundary_preimage_of_componentDominant [IsIntegral Y]
    (q : T ⟶ Y) (E : T.IdealSheafData)
    [∀ C : DivisorComponent E, IsDominant (componentInclusion E C ≫ q)]
    (U : Y.Opens) (hη : genericPoint Y ∈ U) :
    Dense ((reducedBoundaryInclusion E ≫ q) ⁻¹' (U : Set Y)) := by
  apply dense_iff_inter_open.mpr
  intro W hW hWne
  obtain ⟨z, hzW⟩ := hWne
  obtain ⟨C, c, hc⟩ := CartierBoundarySection.components_cover E z.val z.property
  let k := componentBoundaryInclusion E C
  have hkc : k c = z := by
    apply (reducedBoundaryInclusion E).isEmbedding.injective
    change (k ≫ reducedBoundaryInclusion E) c = z.val
    simpa only [k, componentBoundaryInclusion_structure] using hc
  let η := genericPoint (componentScheme E C)
  have hsp : k η ⤳ z := by
    rw [← hkc]
    exact (genericPoint_specializes c).map k.continuous
  have hηW : k η ∈ W := hsp.mem_open hW hzW
  have hηU : (reducedBoundaryInclusion E ≫ q) (k η) ∈ U := by
    change (k ≫ reducedBoundaryInclusion E ≫ q) η ∈ U
    rw [← Category.assoc, componentBoundaryInclusion_structure,
      genericPoint_map_of_isDominant (componentInclusion E C ≫ q)]
    exact hη
  exact ⟨k η, hηW, hηU⟩

/-- The SAME whole reduced inverse boundary is actually etale above the original target etale open. -/
theorem reducedBoundary_etale_on_preimage [IsIntegral Y]
    (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData) (V : S.Opens)
    [Etale ((reducedBoundaryInclusion D ≫ f) ∣_ V)] [Nonempty (g ⁻¹ᵁ V)] :
    Etale ((reducedBoundaryInclusion (D.comap (reductionι f g ≫ pullback.fst f g)) ≫
      (reductionι f g ≫ pullback.snd f g)) ∣_ (g ⁻¹ᵁ V)) := by
  let U := g ⁻¹ᵁ V
  let E := D.comap (reductionι f g ≫ pullback.fst f g)
  let s := pullback.snd (reducedBoundaryInclusion D ≫ f) g
  let r := reducedBoundaryComparison f g D
  let b := reducedBoundaryInclusion E ≫ (reductionι f g ≫ pullback.snd f g)
  let W := s ⁻¹ᵁ U
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : Etale (s ∣_ U) := pullback_snd_etale_on_preimage _ g V
  let : IsReduced W.toScheme := isReduced_of_smooth_integral_base (s ∣_ U)
  let : Surjective (r ∣_ W) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict r W).flip inferInstance
  let : IsIso (r ∣_ W) := isIso_of_isClosedImmersion_of_surjective _
  let : Etale (W.ι ≫ s) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have H : Etale ((r ∣_ W) ≫ (W.ι ≫ s)) := inferInstance
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc, reducedBoundaryComparison_snd] at H
  have hO : r ⁻¹ᵁ W = b ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, reducedBoundaryComparison_snd]
  have hb : Etale ((b ⁻¹ᵁ U).ι ≫ b) := by
    change Etale ((r ⁻¹ᵁ W).ι ≫ b) at H
    exact (congrArg (fun O : (reducedBoundary E).Opens => Etale (O.ι ≫ b)) hO).mp H
  let : Etale (((b ∣_ U) ≫ U.ι)) := by rw [morphismRestrict_ι]; exact hb
  exact Etale.of_comp (b ∣_ U) U.ι

end Hironaka.Geometry.CurveFibrationBaseChange
