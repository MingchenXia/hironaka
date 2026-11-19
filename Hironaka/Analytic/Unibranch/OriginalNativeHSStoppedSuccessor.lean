import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterRun
import Hironaka.Analytic.Unibranch.OriginalNativeHSAbsentOuterSuccessor

/-! A genuine left STOP and incoming whole-current-fibre native identification
make the actual right NEXT absent. No future endpoint/absence packet or
Run recursion is input. Blueprint FIRST: original-native-hs-stopped-successor.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSStoppedSuccessor
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11CompatibleAnalyticCover
  OriginalNativeHSShadowOuterState OriginalIntrinsicHSSuperlevels

variable {X W : SourceReducedComplexSpace} {K₁ K₂ : Set X.obj.left}
  (S : State X K₁) (T : State X K₂)
  (a : W ⟶ S.source) (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left)
  (b : W ⟶ T.source) (hb : LocallyRingedSpace.IsOpenImmersion b.hom.left)
  (hsq : a ≫ S.history.projection ≫ S.inclusion = b ≫ T.history.projection ≫ T.inclusion)
  (C : Set X.obj.left) (hC : C ⊆ K₁)
  (hCover : T.history.projection.hom.left.base ⁻¹' (T.inclusion.hom.left.base ⁻¹' C) ⊆
    range b.hom.left.base)
  (hStop : singularShadow S = ∅)

include ha hb hsq hC hCover hStop in
/-- Genuine whole-current-fibre regularity comes from the actual left stop. -/
theorem right_fibre_singular_empty : intrinsicSingularLocus T.source.obj ∩
    T.history.projection.hom.left.base ⁻¹' (T.inclusion.hom.left.base ⁻¹' C) = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro t ⟨htS,htC⟩
  obtain ⟨w,hw⟩ := hCover htC
  have hbS : b.hom.left.base w ∈ intrinsicSingularLocus T.source.obj := hw.symm ▸ htS
  have hwS : w ∈ intrinsicSingularLocus W.obj :=
    (Set.ext_iff.mp (preimage_intrinsicSingularLocus_of_isOpenImmersion b hb) w).mp hbS
  have haS : a.hom.left.base w ∈ intrinsicSingularLocus S.source.obj :=
    (Set.ext_iff.mp (preimage_intrinsicSingularLocus_of_isOpenImmersion a ha) w).mpr hwS
  have ep := congrArg (fun f : W ⟶ X => f.hom.left.base w) hsq
  have hbC : T.inclusion.hom.left.base (T.history.projection.hom.left.base (b.hom.left.base w)) ∈ C := by
    rw [hw]
    exact htC
  have haC : S.inclusion.hom.left.base (S.history.projection.hom.left.base (a.hom.left.base w)) ∈ C :=
    ep.symm ▸ hbC
  have bad : a.hom.left.base w ∈ singularShadow S := ⟨haS,hC haC⟩
  rw [hStop] at bad
  exact bad

variable (hK₂ : IsCompact K₂) (hn : (singularShadow T).Nonempty)
  (L : Set (OriginalNativeHSShadowOuterRun.next T hK₂ hn).base.obj.left) (hL : IsCompact L)
  (hLC : (OriginalNativeHSShadowOuterRun.next T hK₂ hn).inclusion.hom.left.base '' L ⊆ C)

local notation "B₀" => OriginalNativeHSOuterSuccessor.base T.history (baseShadow T) (baseShadow_compact T hK₂) hn
local notation "A" => OriginalNativeHSOuterSuccessor.oldSource T.history (baseShadow T) (baseShadow_compact T hK₂) hn
local notation "N₀" => OriginalNativeHSOuterSuccessor.neighbourhood T.history (baseShadow T) (baseShadow_compact T hK₂) hn
local notation "Q" => OriginalNativeHSAbsentOuterSuccessor.oldPrefix T.history (baseShadow T) (baseShadow_compact T hK₂) hn
local notation "H" => OriginalNativeHSOuterInitialBound.profile T.history (baseShadow T) (baseShadow_compact T hK₂) hn

include ha hb hsq hC hCover hStop hLC in
/-- The ENTIRE actual old-prefix fibre is regular, without a supplied lower-domain/absence packet. -/
theorem old_fibre_singular_empty :
    OriginalNativeHSAbsentOuterSuccessor.oldFibre T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L ∩ intrinsicSingularLocus (A).obj = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro y ⟨hyL,hyS⟩
  have hOrig : T.inclusion.hom.left.base (T.history.projection.hom.left.base
      ((OriginalNativeHSOuterSuccessor.oldInclusion T.history (baseShadow T)
        (baseShadow_compact T hK₂) hn).hom.left.base y)) ∈ C := by
    have hv : (OriginalNativeHSShadowOuterRun.next T hK₂ hn).inclusion.hom.left.base
        ((Q).projection.hom.left.base y) ∈ C :=
      hLC ⟨(Q).projection.hom.left.base y,hyL,rfl⟩
    have ep := congrArg (fun f : (A) ⟶ T.base => f.hom.left.base y)
      (OriginalNativePhysicalHistoryRestriction.projection_square T.history (N₀).openSet (N₀).compactClosure)
    exact (congrArg T.inclusion.hom.left.base ep) ▸ hv
  have hOldOpen : LocallyRingedSpace.IsOpenImmersion
      (OriginalNativeHSOuterSuccessor.oldInclusion T.history (baseShadow T)
        (baseShadow_compact T hK₂) hn).hom.left :=
    OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _
  have hOldS : (OriginalNativeHSOuterSuccessor.oldInclusion T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn).hom.left.base y ∈ intrinsicSingularLocus T.source.obj :=
    (Set.ext_iff.mp (preimage_intrinsicSingularLocus_of_isOpenImmersion
      (OriginalNativeHSOuterSuccessor.oldInclusion T.history (baseShadow T)
        (baseShadow_compact T hK₂) hn) hOldOpen) y).mpr hyS
  have bad : (OriginalNativeHSOuterSuccessor.oldInclusion T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn).hom.left.base y ∈ intrinsicSingularLocus T.source.obj ∩
        T.history.projection.hom.left.base ⁻¹' (T.inclusion.hom.left.base ⁻¹' C) := ⟨hOldS,hOrig⟩
  rw [right_fibre_singular_empty (S := S) (T := T) (a := a) (ha := ha) (b := b) (hb := hb)
    (hsq := hsq) (C := C) (hC := hC) (hCover := hCover) (hStop := hStop)] at bad
  exact bad

include ha hb hsq hC hCover hStop hLC in
/-- This is the honest internally derived D41 absence input for the ACTUAL next head. -/
theorem old_threshold_empty :
    OriginalNativeHSAbsentOuterSuccessor.oldFibre T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L ∩ originalSingularHSThreshold (A) (H) = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro y ⟨hyL,hyH⟩
  have bad : y ∈ OriginalNativeHSAbsentOuterSuccessor.oldFibre T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L ∩ intrinsicSingularLocus (A).obj := ⟨hyL,hyH.1⟩
  rw [old_fibre_singular_empty (S := S) (T := T) (a := a) (ha := ha) (b := b) (hb := hb)
    (hsq := hsq) (C := C) (hC := hC) (hCover := hCover) (hStop := hStop)
    (hK₂ := hK₂) (hn := hn) (L := L) (hLC := hLC)] at bad
  exact bad

local notation "he" => old_threshold_empty (S := S) (T := T) (a := a) (ha := ha) (b := b) (hb := hb)
  (hsq := hsq) (C := C) (hC := hC) (hCover := hCover) (hStop := hStop)
  (hK₂ := hK₂) (hn := hn) (L := L) (hLC := hLC)

include ha hb hsq hC hCover hStop hLC in
/-- An actual stop-to-next coupling, retaining ALL L and both original chronological histories. -/
theorem exists_successor_coupling :
    let N := OriginalNativeHSAbsentOuterSuccessor.neighbourhood T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L hL (he)
    let old := OriginalNativeHSAbsentOuterSuccessor.oldHistory T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L hL (he)
    let next := OriginalNativeHSAbsentOuterSuccessor.nextHistory T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L hL (he)
    ∃ E : OriginalNativeHSAbsentOuterSuccessor.nextSource T.history (baseShadow T)
        (baseShadow_compact T hK₂) hn L hL (he) ≅
      OriginalNativeHSAbsentOuterSuccessor.oldSource T.history (baseShadow T)
        (baseShadow_compact T hK₂) hn L hL (he),
      L ⊆ range N.inclusion.hom.left.base ∧
      E.hom ≫ old.projection = next.projection ∧
      E.hom ≫ old.projection ≫ N.inclusion ≫ (N₀).inclusion ≫ T.inclusion =
        next.projection ≫ N.inclusion ≫ (N₀).inclusion ≫ T.inclusion ∧
      old.length = T.history.length ∧
      next.length = (OriginalNativeHSShadowOuterRun.next T hK₂ hn).history.length ∧
      E.hom.hom.left ≫ (OriginalNativeHSAbsentOuterSuccessor.oldSource T.history (baseShadow T)
        (baseShadow_compact T hK₂) hn L hL (he)).obj.hom =
        (OriginalNativeHSAbsentOuterSuccessor.nextSource T.history (baseShadow T)
          (baseShadow_compact T hK₂) hn L hL (he)).obj.hom := by
  dsimp only
  refine ⟨OriginalNativeHSAbsentOuterSuccessor.comparison T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L hL (he),
    OriginalNativeHSAbsentOuterSuccessor.compact_retained T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L hL (he),
    OriginalNativeHSAbsentOuterSuccessor.comparison_projection T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L hL (he),?_,
    OriginalNativeHSAbsentOuterSuccessor.old_length T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L hL (he),
    OriginalNativeHSAbsentOuterSuccessor.next_length T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L hL (he),
    OriginalNativeHSAbsentOuterSuccessor.comparison_scalar T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L hL (he)⟩
  have h := congrArg (fun f => f ≫ T.inclusion)
    (OriginalNativeHSAbsentOuterSuccessor.comparison_original_base_square T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn L hL (he))
  simpa only [Category.assoc] using h

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSStoppedSuccessor
