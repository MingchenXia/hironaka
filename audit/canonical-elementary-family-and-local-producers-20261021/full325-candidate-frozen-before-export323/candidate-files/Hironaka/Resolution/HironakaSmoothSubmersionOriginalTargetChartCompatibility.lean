/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalLocalGlobalArrow
/-! Genuine target-chart compatibility on actual original source intersections.
Complete mathematics preceded code. Real source-base restrictions preserve the
full global-target universal property before genuine finite source tower
projection uniqueness identifies the actual arrows. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalTargetChartCompatibility
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms CanonicalCentres
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaSmoothSubmersionOriginalLocalChartArrow HironakaSmoothSubmersionOriginalLocalGlobalArrow
  HironakaSmoothSubmersionOriginalTerminalFunctor HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange
open ResolutionInvariantSpec (IsInvDomain)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold
variable {m n : ℕ}

/-- Actual literal inclusion between the two true source-base opens. -/
def actualSourceOpenInclusion {Y : CMfd.{u} m} {U V : Opens Y} (hUV : U ≤ V) : U → V :=
  fun y => ⟨y.val,hUV y.property⟩

theorem actualSourceOpenInclusion_contMDiff {Y : CMfd.{u} m} {U V : Opens Y} (hUV : U ≤ V) :
    ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ (actualSourceOpenInclusion hUV) :=
  BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val (fun y => hUV y.property)

/-- Actual final-space open inclusion supplied by the real original projection. -/
def actualTerminalOpenInclusion {Y E : CMfd.{u} m} (S : BlowupTower Y E)
    {U V : Opens Y} (hUV : U ≤ V) : openPreimage S U → openPreimage S V :=
  fun y => ⟨y.val,hUV y.property⟩

theorem actualTerminalOpenInclusion_contMDiff {Y E : CMfd.{u} m} (S : BlowupTower Y E)
    {U V : Opens Y} (hUV : U ≤ V) :
    ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ (actualTerminalOpenInclusion S hUV) :=
  BlowupRestrictOpen.contMDiff_opens_mk (V := openPreimage S V)
    (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞
      (Subtype.val : openPreimage S U → E)) (fun y => hUV y.property)

theorem holomorphicSquarePullback_source_open_restriction
    {Y E : CMfd.{u} m} {X D : CMfd.{u} n} (S : BlowupTower Y E)
    {U V : Opens Y} (hUV : U ≤ V) (f : V → X) (g : openPreimage S V → D) (t : D → X)
    (hU : HolomorphicSquarePullback f g (restrict V S).proj t) :
    HolomorphicSquarePullback (f ∘ actualSourceOpenInclusion hUV)
      (g ∘ actualTerminalOpenInclusion S hUV) (restrict U S).proj t := by
  intro k W a b ha hb hcone
  obtain ⟨w,hw,huniq⟩ := hU k W (actualSourceOpenInclusion hUV ∘ a) b
    ((actualSourceOpenInclusion_contMDiff hUV).comp ha) hb hcone
  have hwmember : ∀ z, (w z).val ∈ openPreimage S U := by
    intro z
    have hp : S.proj (w z).val=(a z).val :=
      (proj_restrict V S (w z)).symm.trans (congrArg Subtype.val (hw.2.1 z))
    change S.proj (w z).val ∈ U
    rw [hp]
    exact (a z).property
  let wU : W → openPreimage S U := fun z => ⟨(w z).val,hwmember z⟩
  have hwU : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel m) ∞ wU :=
    BlowupRestrictOpen.contMDiff_opens_mk (contMDiff_subtype_val.comp hw.1) hwmember
  refine ⟨wU,⟨hwU,?_,?_⟩,?_⟩
  · intro z
    apply Subtype.ext
    exact (proj_restrict U S (wU z)).trans
      ((proj_restrict V S (w z)).symm.trans (congrArg Subtype.val (hw.2.1 z)))
  · intro z
    change g (actualTerminalOpenInclusion S hUV (wU z))=b z
    have hi : actualTerminalOpenInclusion S hUV (wU z)=w z := Subtype.ext rfl
    rw [hi]
    exact hw.2.2 z
  · intro v hv
    have hbase : ∀ z, (restrict V S).proj (actualTerminalOpenInclusion S hUV (v z))=
        actualSourceOpenInclusion hUV (a z) := by
      intro z
      apply Subtype.ext
      exact (proj_restrict V S _).trans
        ((proj_restrict U S (v z)).symm.trans (congrArg Subtype.val (hv.2.1 z)))
    have he := huniq (actualTerminalOpenInclusion S hUV ∘ v)
      ⟨(actualTerminalOpenInclusion_contMDiff S hUV).comp hv.1,hbase,hv.2.2⟩
    funext z
    apply Subtype.ext
    exact congrArg (fun x : openPreimage S V => x.val) (congrFun he z)

section ActualOriginal
variable {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
  (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
  (M : MarkedIdeal n X) (hM : IsInvDomain n M)

/-- Entire maps into the same original global target agree on their literal
source intersection; BOTH full square laws were internally produced. -/
theorem originalLocalTerminalSmoothGlobalArrow_target_compatibility (i : Y) (j k : X) :
    let A := actualLocalTerminalAtlas (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM)
    let B := actualLocalTerminalAtlas M hM
    let U := actualSmoothChartNestedOpen hf (A.openSet i) (B.openSet j)
    let V := actualSmoothChartNestedOpen hf (A.openSet i) (B.openSet k)
    (originalLocalTerminalSmoothGlobalArrow hf M hM i j) ∘
        actualTerminalOpenInclusion (A.tower i) (inf_le_left : U ⊓ V ≤ U)=
      (originalLocalTerminalSmoothGlobalArrow hf M hM i k) ∘
        actualTerminalOpenInclusion (A.tower i) (inf_le_right : U ⊓ V ≤ V) := by
  dsimp only
  let A := actualLocalTerminalAtlas (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM)
  let B := actualLocalTerminalAtlas M hM
  let U := actualSmoothChartNestedOpen hf (A.openSet i) (B.openSet j)
  let V := actualSmoothChartNestedOpen hf (A.openSet i) (B.openSet k)
  let Q := U ⊓ V
  let G := originalLocalTerminalSmoothGlobalArrow hf M hM i j
  let H := originalLocalTerminalSmoothGlobalArrow hf M hM i k
  have hG := originalLocalTerminalSmoothGlobalArrow_properties hf M hM i j
  have hH := originalLocalTerminalSmoothGlobalArrow_properties hf M hM i k
  have hGU := holomorphicSquarePullback_source_open_restriction (A.tower i)
    (inf_le_left : Q ≤ U) (originalSmoothChartOriginalBaseMap hf M hM i j) G
    (originalTerminalGluedProjection M hM) hG.2.2
  have hHU := holomorphicSquarePullback_source_open_restriction (A.tower i)
    (inf_le_right : Q ≤ V) (originalSmoothChartOriginalBaseMap hf M hM i k) H
    (originalTerminalGluedProjection M hM) hH.2.2
  have hgp : ∀ z : openPreimage (A.tower i) Q,
      originalTerminalGluedProjection M hM (G (actualTerminalOpenInclusion (A.tower i) inf_le_left z))=
        (originalSmoothChartOriginalBaseMap hf M hM i j ∘ actualSourceOpenInclusion inf_le_left)
          ((restrict Q (A.tower i)).proj z) := by
    intro z
    have hp := congrArg (fun q : A.openSet i => q.val) (proj_restrict Q (A.tower i) z)
    exact (hG.2.1 (actualTerminalOpenInclusion (A.tower i) inf_le_left z)).trans (congrArg f hp.symm)
  have hhp : ∀ z : openPreimage (A.tower i) Q,
      originalTerminalGluedProjection M hM (H (actualTerminalOpenInclusion (A.tower i) inf_le_right z))=
        (originalSmoothChartOriginalBaseMap hf M hM i j ∘ actualSourceOpenInclusion inf_le_left)
          ((restrict Q (A.tower i)).proj z) := by
    intro z
    have hp := congrArg (fun q : A.openSet i => q.val) (proj_restrict Q (A.tower i) z)
    exact (hH.2.1 (actualTerminalOpenInclusion (A.tower i) inf_le_right z)).trans (congrArg f hp.symm)
  exact final_holomorphic_pullback_map_eq (restrict Q (A.tower i)) (originalTerminalGluedProjection M hM)
    _ _ (hG.1.comp (actualTerminalOpenInclusion_contMDiff (A.tower i) inf_le_left))
    (hH.1.comp (actualTerminalOpenInclusion_contMDiff (A.tower i) inf_le_right)) hgp hhp hGU hHU

end ActualOriginal
end
end Hironaka.HironakaSmoothSubmersionOriginalTargetChartCompatibility
