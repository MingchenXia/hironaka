import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterEndpointRange
import Hironaka.Analytic.Unibranch.OriginalNativeHSEqualProfilePhaseComparison

/-! Actual coupled phase endpoints inside the SAME computed outer successors.
Blueprint FIRST: original-native-hs-outer-phase-coupling.tex.
Only ordinary PRESENT histories/compact shadows/native overlaps are inputs.
No next-source range, phase comparison or global cover packet is supplied. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSOuterPhaseCoupling
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSOuterHistory
  Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus

private theorem lift_with_range {A B D : SourceReducedComplexSpace}
    (e : B ⟶ D) (a : A ⟶ D)
    (he : LocallyRingedSpace.IsOpenImmersion e.hom.left)
    (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left)
    (S : Set D.obj.left) (hRa : range a.hom.left.base = S)
    (hS : S ⊆ range e.hom.left.base) :
    ∃ k : A ⟶ B, LocallyRingedSpace.IsOpenImmersion k.hom.left ∧ k ≫ e = a ∧
      range k.hom.left.base = e.hom.left.base ⁻¹' S := by
  obtain ⟨k,hk,hsq⟩ := OriginalNativeSmoothOpenLocality.exists_native_open_lift e a he ha (hRa.symm ▸ hS)
  refine ⟨k,hk,hsq,?_⟩
  ext b
  constructor
  · rintro ⟨x,rfl⟩
    have hx := congrArg (fun f : A ⟶ D => f.hom.left.base x) hsq
    exact hRa ▸ (show e.hom.left.base (k.hom.left.base x) ∈ range a.hom.left.base from ⟨x,hx.symm⟩)
  · intro hb
    obtain ⟨x,hx⟩ := (show e.hom.left.base b ∈ range a.hom.left.base from hRa.symm ▸ hb)
    refine ⟨x,he.base_open.injective ?_⟩
    exact (congrArg (fun f : A ⟶ D => f.hom.left.base x) hsq).trans hx

private theorem singularNonempty {B Y : SourceReducedComplexSpace}
    (h : PhysicalHistory B Y) (K : Set B.obj.left)
    (hne : (intrinsicSingularLocus Y.obj ∩ OriginalNativeHSOuterSuccessor.shadow h K).Nonempty) :
    (OriginalNativeHSOuterSuccessor.shadow h K ∩ intrinsicSingularLocus Y.obj).Nonempty := by
  simpa only [inter_comm] using hne

variable {BT BS YT YS Z : SourceReducedComplexSpace}
  (hT : PhysicalHistory BT YT) (hS : PhysicalHistory BS YS)
  (KT : Set BT.obj.left) (KS : Set BS.obj.left) (hKT : IsCompact KT) (hKS : IsCompact KS)
  (hneT : (intrinsicSingularLocus YT.obj ∩ OriginalNativeHSOuterSuccessor.shadow hT KT).Nonempty)
  (hneS : (intrinsicSingularLocus YS.obj ∩ OriginalNativeHSOuterSuccessor.shadow hS KS).Nonempty)
  (aT : Z ⟶ YT) (aS : Z ⟶ YS)
  (haT : LocallyRingedSpace.IsOpenImmersion aT.hom.left)
  (haS : LocallyRingedSpace.IsOpenImmersion aS.hom.left)
  (C : Set Z.obj.left) (hC : IsCompact C)
  (hImageT : aT.hom.left.base '' C ⊆ OriginalNativeHSOuterSuccessor.shadow hT KT)
  (hImageS : aS.hom.left.base '' C ⊆ OriginalNativeHSOuterSuccessor.shadow hS KS)

/-- The ACTUAL computed old-source inverse-open traces, with no overlap packet. -/
def overlapOpen : Opens Z.obj.left :=
  ⟨aT.hom.left.base ⁻¹' range (OriginalNativeHSOuterSuccessor.oldInclusion hT KT hKT hneT).hom.left.base ∩
    aS.hom.left.base ⁻¹' range (OriginalNativeHSOuterSuccessor.oldInclusion hS KS hKS hneS).hom.left.base,
    ((OriginalNativeHSOuterEndpointRange.oldInclusion_isOpenImmersion hT KT hKT hneT).base_open.isOpen_range.preimage
      aT.hom.left.base.hom.continuous).inter
      ((OriginalNativeHSOuterEndpointRange.oldInclusion_isOpenImmersion hS KS hKS hneS).base_open.isOpen_range.preimage
        aS.hom.left.base.hom.continuous)⟩

include hImageT hImageS in
theorem compact_subset_overlap : C ⊆ overlapOpen hT hS KT KS hKT hKS hneT hneS aT aS := by
  intro z hz
  exact ⟨OriginalNativeHSOuterSuccessor.oldShadow_retained hT KT hKT hneT (hImageT ⟨z,hz,rfl⟩),
    OriginalNativeHSOuterSuccessor.oldShadow_retained hS KS hKS hneS (hImageS ⟨z,hz,rfl⟩)⟩

local notation "KT₀" => OriginalNativeHSOuterSuccessor.shadow hT KT
local notation "KS₀" => OriginalNativeHSOuterSuccessor.shadow hS KS
local notation "hKT₀" => OriginalNativeHSOuterSuccessor.shadow_isCompact hT KT hKT
local notation "hKS₀" => OriginalNativeHSOuterSuccessor.shadow_isCompact hS KS hKS
local notation "hST" => singularNonempty hT KT hneT
local notation "hSS" => singularNonempty hS KS hneS
local notation "Ω" => overlapOpen hT hS KT KS hKT hKS hneT hneS aT aS
local notation "hΩ" => compact_subset_overlap hT hS KT KS hKT hKS hneT hneS aT aS C hImageT hImageS
local notation "N" => OriginalNativeHSEqualProfilePhaseComparison.neighbourhood YT YS
  (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ)
local notation "L" => OriginalNativeHSEqualProfilePhaseComparison.leftEndpoint YT YS
  (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ)
local notation "R" => OriginalNativeHSEqualProfilePhaseComparison.rightEndpoint YT YS
  (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ)
local notation "lh" => OriginalNativeHSEqualProfilePhaseComparison.leftHistory YT YS
  (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ)
local notation "rh" => OriginalNativeHSEqualProfilePhaseComparison.rightHistory YT YS
  (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ)
local notation "bT" => OriginalNativeHSEqualProfilePhaseComparison.leftInclusion YT YS
  (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ)
local notation "bS" => OriginalNativeHSEqualProfilePhaseComparison.rightInclusion YT YS
  (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ)
local notation "eT" => OriginalNativeHSOuterEndpointRange.endpointInclusion hT KT hKT hneT
local notation "eS" => OriginalNativeHSOuterEndpointRange.endpointInclusion hS KS hKS hneS
local notation "fT" => PhysicalHistory.projection (OriginalNativeHSShadowPhaseFactory.history YT (KT₀) (hKT₀) (hST)) ≫
  OriginalNativeHSShadowPhaseFactory.baseInclusion YT (KT₀) (hKT₀) (hST)
local notation "fS" => PhysicalHistory.projection (OriginalNativeHSShadowPhaseFactory.history YS (KS₀) (hKS₀) (hSS)) ≫
  OriginalNativeHSShadowPhaseFactory.baseInclusion YS (KS₀) (hKS₀) (hSS)

private theorem left_lift : ∃ k : (L) ⟶ OriginalNativeHSOuterSuccessor.source hT KT hKT hneT,
    LocallyRingedSpace.IsOpenImmersion k.hom.left ∧ k ≫ (eT) = (bT) ∧
      range k.hom.left.base = (eT).hom.left.base ⁻¹' ((fT).hom.left.base ⁻¹'
        (aT.hom.left.base '' ((N).openSet : Set Z.obj.left))) := by
  apply lift_with_range (eT) (bT)
    (OriginalNativeHSOuterEndpointRange.endpointInclusion_isOpenImmersion hT KT hKT hneT)
    (OriginalNativeHSEqualProfilePhaseComparison.leftInclusion_isOpenImmersion YT YS
      (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ)) _
    (OriginalNativeHSEqualProfilePhaseComparison.leftInclusion_range YT YS
      (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ))
  intro t ht
  rw [OriginalNativeHSOuterEndpointRange.endpoint_range]
  obtain ⟨z,hz,hzt⟩ := ht
  have hzΩ : z ∈ (Ω) := ((N).closure_subset (subset_closure hz)).2
  change (fT).hom.left.base t ∈
    range (OriginalNativeHSOuterSuccessor.oldInclusion hT KT hKT hneT).hom.left.base
  exact hzt ▸ hzΩ.1

private theorem right_lift : ∃ k : (R) ⟶ OriginalNativeHSOuterSuccessor.source hS KS hKS hneS,
    LocallyRingedSpace.IsOpenImmersion k.hom.left ∧ k ≫ (eS) = (bS) ∧
      range k.hom.left.base = (eS).hom.left.base ⁻¹' ((fS).hom.left.base ⁻¹'
        (aS.hom.left.base '' ((N).openSet : Set Z.obj.left))) := by
  apply lift_with_range (eS) (bS)
    (OriginalNativeHSOuterEndpointRange.endpointInclusion_isOpenImmersion hS KS hKS hneS)
    (OriginalNativeHSEqualProfilePhaseComparison.rightInclusion_isOpenImmersion YT YS
      (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ)) _
    (OriginalNativeHSEqualProfilePhaseComparison.rightInclusion_range YT YS
      (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ))
  intro t ht
  rw [OriginalNativeHSOuterEndpointRange.endpoint_range]
  obtain ⟨z,hz,hzt⟩ := ht
  have hzΩ : z ∈ (Ω) := ((N).closure_subset (subset_closure hz)).2
  change (fS).hom.left.base t ∈
    range (OriginalNativeHSOuterSuccessor.oldInclusion hS KS hKS hneS).hom.left.base
  exact hzt ▸ hzΩ.2

/-- The ACTUAL left endpoint lift into the SAME computed next source. -/
def leftMap : (L) ⟶ OriginalNativeHSOuterSuccessor.source hT KT hKT hneT :=
  (left_lift hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).choose
def rightMap : (R) ⟶ OriginalNativeHSOuterSuccessor.source hS KS hKS hneS :=
  (right_lift hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).choose

theorem leftMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion
    (leftMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom.left :=
  (left_lift hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).choose_spec.1
theorem rightMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion
    (rightMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom.left :=
  (right_lift hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).choose_spec.1
theorem leftMap_square :
    leftMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS ≫ (eT) = (bT) :=
  (left_lift hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).choose_spec.2.1
theorem rightMap_square :
    rightMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS ≫ (eS) = (bS) :=
  (right_lift hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).choose_spec.2.1

theorem leftMap_range :
    range (leftMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom.left.base =
      (OriginalNativeHSOuterSuccessor.sourceMap hT KT hKT hneT).hom.left.base ⁻¹'
        (aT.hom.left.base '' ((N).openSet : Set Z.obj.left)) := by
  have hr : range (leftMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom.left.base =
      (eT).hom.left.base ⁻¹' ((fT).hom.left.base ⁻¹'
        (aT.hom.left.base '' ((N).openSet : Set Z.obj.left))) :=
    (left_lift hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).choose_spec.2.2
  have hs : (eT) ≫ (fT) = OriginalNativeHSOuterSuccessor.sourceMap hT KT hKT hneT :=
    OriginalNativeHSOuterEndpointRange.endpoint_square hT KT hKT hneT
  apply Set.ext
  intro y
  have hm : y ∈ range (leftMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom.left.base ↔
      (fT).hom.left.base ((eT).hom.left.base y) ∈ aT.hom.left.base '' ((N).openSet : Set Z.obj.left) :=
    Set.ext_iff.mp hr y
  have hy := congrArg (fun f : OriginalNativeHSOuterSuccessor.source hT KT hKT hneT ⟶ YT =>
    f.hom.left.base y) hs
  exact hm.trans (iff_of_eq (congrArg (fun z : YT.obj.left =>
    z ∈ aT.hom.left.base '' ((N).openSet : Set Z.obj.left)) hy))

theorem rightMap_range :
    range (rightMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom.left.base =
      (OriginalNativeHSOuterSuccessor.sourceMap hS KS hKS hneS).hom.left.base ⁻¹'
        (aS.hom.left.base '' ((N).openSet : Set Z.obj.left)) := by
  have hr : range (rightMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom.left.base =
      (eS).hom.left.base ⁻¹' ((fS).hom.left.base ⁻¹'
        (aS.hom.left.base '' ((N).openSet : Set Z.obj.left))) :=
    (right_lift hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).choose_spec.2.2
  have hs : (eS) ≫ (fS) = OriginalNativeHSOuterSuccessor.sourceMap hS KS hKS hneS :=
    OriginalNativeHSOuterEndpointRange.endpoint_square hS KS hKS hneS
  apply Set.ext
  intro y
  have hm : y ∈ range (rightMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom.left.base ↔
      (fS).hom.left.base ((eS).hom.left.base y) ∈ aS.hom.left.base '' ((N).openSet : Set Z.obj.left) :=
    Set.ext_iff.mp hr y
  have hy := congrArg (fun f : OriginalNativeHSOuterSuccessor.source hS KS hKS hneS ⟶ YS =>
    f.hom.left.base y) hs
  exact hm.trans (iff_of_eq (congrArg (fun z : YS.obj.left =>
    z ∈ aS.hom.left.base '' ((N).openSet : Set Z.obj.left)) hy))

theorem left_old_square :
    leftMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS ≫
      OriginalNativeHSOuterSuccessor.sourceMap hT KT hKT hneT =
        (lh).projection ≫ (N).inclusion ≫ aT := by
  calc
    _ = leftMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS ≫ (eT) ≫ (fT) :=
      congrArg (fun f => leftMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS ≫ f)
        (OriginalNativeHSOuterEndpointRange.endpoint_square hT KT hKT hneT).symm
    _ = (bT) ≫ (fT) := by
      rw [← Category.assoc, leftMap_square]
    _ = _ := (OriginalNativeHSEqualProfilePhaseComparison.left_old_square YT YS
      (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ)).symm
theorem right_old_square :
    rightMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS ≫
      OriginalNativeHSOuterSuccessor.sourceMap hS KS hKS hneS =
        (rh).projection ≫ (N).inclusion ≫ aS := by
  calc
    _ = rightMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS ≫ (eS) ≫ (fS) :=
      congrArg (fun f => rightMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS ≫ f)
        (OriginalNativeHSOuterEndpointRange.endpoint_square hS KS hKS hneS).symm
    _ = (bS) ≫ (fS) := by
      rw [← Category.assoc, rightMap_square]
    _ = _ := (OriginalNativeHSEqualProfilePhaseComparison.right_old_square YT YS
      (KT₀) (KS₀) (hKT₀) (hKS₀) (hST) (hSS) aT aS haT haS C hC hImageT hImageS (Ω) (hΩ)).symm

theorem left_scalar :
    (leftMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom.left ≫
      (OriginalNativeHSOuterSuccessor.source hT KT hKT hneT).obj.hom = (L).obj.hom :=
  Over.w (leftMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom
theorem right_scalar :
    (rightMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom.left ≫
      (OriginalNativeHSOuterSuccessor.source hS KS hKS hneS).obj.hom = (R).obj.hom :=
  Over.w (rightMap hT hS KT KS hKT hKS hneT hneS aT aS haT haS C hC hImageT hImageS).hom

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSOuterPhaseCoupling
