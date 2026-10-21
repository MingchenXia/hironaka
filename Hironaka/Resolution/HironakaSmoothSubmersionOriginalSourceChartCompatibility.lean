/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalSourceChartMap
/-! Actual original source overlap compatibility of the entire chart arrows.
Complete mathematics preceded code. Genuine original common-open base/final
biholomorphisms transport the already constructed full Cartesian squares;
actual finite source tower geometry then proves the gluing equality. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalSourceChartCompatibility
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms CanonicalCentres
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalOverlapComparison HironakaSmoothSubmersionOriginalSourceChartMap
  HironakaSmoothSubmersionOriginalTerminalFunctor HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange MaxLocusLocal
open ResolutionInvariantSpec (IsInvDomain)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold
variable {m n : ℕ}

private theorem holomorphicSquarePullback_whole_source_open_restriction
    {Y E : CMfd.{u} m} {X D : CMfd.{u} n} (S : BlowupTower Y E) (U : Opens Y)
    (f : Y → X) (g : E → D) (t : D → X) (hU : HolomorphicSquarePullback f g S.proj t) :
    HolomorphicSquarePullback (f ∘ (Subtype.val : U → Y))
      (g ∘ (Subtype.val : openPreimage S U → E)) (restrict U S).proj t := by
  intro k W a b ha hb hcone
  obtain ⟨w,hw,huniq⟩ := hU k W (Subtype.val ∘ a) b
    (contMDiff_subtype_val.comp ha) hb hcone
  have hmember : ∀ z, w z ∈ openPreimage S U := by
    intro z
    change S.proj (w z) ∈ U
    rw [hw.2.1 z]
    exact (a z).property
  let wU : W → openPreimage S U := fun z => ⟨w z,hmember z⟩
  refine ⟨wU,⟨BlowupRestrictOpen.contMDiff_opens_mk hw.1 hmember,?_,hw.2.2⟩,?_⟩
  · intro z
    apply Subtype.ext
    exact (proj_restrict U S (wU z)).trans (hw.2.1 z)
  · intro v hv
    have he : (Subtype.val : openPreimage S U → E) ∘ v=w := huniq (Subtype.val ∘ v)
      ⟨contMDiff_subtype_val.comp hv.1,fun z =>
        (proj_restrict U S (v z)).symm.trans (congrArg Subtype.val (hv.2.1 z)),hv.2.2⟩
    funext z
    apply Subtype.ext
    exact congrFun he z

/-- True entire base/final commuting biholomorphisms preserve the universal
property itself; no new lift or square certificate is supplied. -/
theorem holomorphicSquarePullback_source_biholomorphism
    {A B E F : CMfd.{u} m} {X D : CMfd.{u} n}
    {fa : A → X} {fb : B → X} {g : F → D} {pa : E → A} {pb : F → B} {t : D → X}
    (Φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ B)
    (η : E ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ F)
    (hproj : ∀ y, pb (η y)=Φ (pa y)) (hbase : ∀ x, fb (Φ x)=fa x)
    (hU : HolomorphicSquarePullback fb g pb t) : HolomorphicSquarePullback fa (g ∘ η) pa t := by
  intro k W a b ha hb hcone
  obtain ⟨w,hw,huniq⟩ := hU k W (Φ ∘ a) b (Φ.contMDiff.comp ha) hb
    (fun z => (hbase (a z)).trans (hcone z))
  refine ⟨η.symm ∘ w,⟨η.symm.contMDiff.comp hw.1,?_,?_⟩,?_⟩
  · intro z
    apply Φ.injective
    have hp := hproj (η.symm (w z))
    rw [η.apply_symm_apply] at hp
    exact hp.symm.trans (hw.2.1 z)
  · intro z
    change g (η (η.symm (w z)))=b z
    rw [η.apply_symm_apply]
    exact hw.2.2 z
  · intro v hv
    have he : η ∘ v=w := huniq (η ∘ v)
      ⟨η.contMDiff.comp hv.1,fun z => (hproj (v z)).trans (congrArg Φ (hv.2.1 z)),hv.2.2⟩
    funext z
    apply η.injective
    change η (v z)=η (η.symm (w z))
    rw [η.apply_symm_apply]
    exact congrFun he z

section Original
variable {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
  (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
  (M : MarkedIdeal n X) (hM : IsInvDomain n M)

theorem originalSourceChartSmoothMap_overlap (i j : Y)
    (y : originalTerminalOverlapOpen (markedPullback (m := m) f M)
      (original_ambient_domain_pullback hf M hM) i j) :
    originalSourceChartSmoothMap hf M hM i y.val=
      originalSourceChartSmoothMap hf M hM j
        (originalTerminalTransition (markedPullback (m := m) f M)
          (original_ambient_domain_pullback hf M hM) i j y).val := by
  let N := markedPullback (m := m) f M
  let hN := original_ambient_domain_pullback hf M hM
  let C := actualLocalTerminalAtlas N hN
  let U := C.openSet i
  let V := C.openSet j
  let Q := U ⊓ V
  let Ui := nestedOpens U Q
  let Uj := nestedOpens V Q
  let Si := restrict Ui (C.tower i)
  let Sj := restrict Uj (C.tower j)
  let Φ := overlapBaseEquiv (n := m) (X := Y) (U := U) (V := V) (W := Q) inf_le_left inf_le_right
  let η := commonOpenTerminalComparison N hN (W := Q) inf_le_left inf_le_right
    (C.tower i) (C.tower j) (C.canonical i) (C.canonical j) (C.terminal i) (C.terminal j)
  let fi := originalSourceChartBaseMap hf M hM i ∘ (Subtype.val : Ui → U)
  let fj := originalSourceChartBaseMap hf M hM j ∘ (Subtype.val : Uj → V)
  let gi := originalSourceChartSmoothMap hf M hM i ∘ (Subtype.val : openPreimage (C.tower i) Ui → C.finalSpace i)
  let gj := originalSourceChartSmoothMap hf M hM j ∘ (Subtype.val : openPreimage (C.tower j) Uj → C.finalSpace j)
  have hUi := holomorphicSquarePullback_whole_source_open_restriction (C.tower i) Ui
    (originalSourceChartBaseMap hf M hM i) (originalSourceChartSmoothMap hf M hM i)
    (originalTerminalGluedProjection M hM) (originalSourceChartSmoothMap_cartesian hf M hM i)
  have hUj := holomorphicSquarePullback_whole_source_open_restriction (C.tower j) Uj
    (originalSourceChartBaseMap hf M hM j) (originalSourceChartSmoothMap hf M hM j)
    (originalTerminalGluedProjection M hM) (originalSourceChartSmoothMap_cartesian hf M hM j)
  have hη : ∀ z, Sj.proj (η z)=Φ (Si.proj z) := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    have hi := congrArg (fun q : U => q.val) (proj_restrict Ui (C.tower i) z)
    have hj := congrArg (fun q : V => q.val) (proj_restrict Uj (C.tower j) (η z))
    exact hj.trans ((commonOpenTerminalComparison_proj N hN inf_le_left inf_le_right
      (C.tower i) (C.tower j) (C.canonical i) (C.canonical j) (C.terminal i) (C.terminal j) z).trans hi.symm)
  have hbase : ∀ z, fj (Φ z)=fi z := fun _ => rfl
  have hpi : ∀ z, originalTerminalGluedProjection M hM (gi z)=fi (Si.proj z) := by
    intro z
    have hp := congrArg (fun q : U => q.val) (proj_restrict Ui (C.tower i) z)
    exact (originalSourceChartSmoothMap_proj hf M hM i z.val).trans (congrArg f hp.symm)
  have hpj : ∀ z, originalTerminalGluedProjection M hM (gj z)=fj (Sj.proj z) := by
    intro z
    have hp := congrArg (fun q : V => q.val) (proj_restrict Uj (C.tower j) z)
    exact (originalSourceChartSmoothMap_proj hf M hM j z.val).trans (congrArg f hp.symm)
  have hUj' := holomorphicSquarePullback_source_biholomorphism Φ η hη hbase hUj
  have he : gi=gj ∘ η := final_holomorphic_pullback_map_eq Si (originalTerminalGluedProjection M hM)
    gi (gj ∘ η) ((originalSourceChartSmoothMap_contMDiff hf M hM i).comp contMDiff_subtype_val)
    (((originalSourceChartSmoothMap_contMDiff hf M hM j).comp contMDiff_subtype_val).comp η.contMDiff)
    hpi (fun z => (hpj (η z)).trans ((congrArg fj (hη z)).trans (hbase (Si.proj z)))) hUi hUj'
  let q : openPreimage (C.tower i) Ui := ⟨y.val,⟨((C.tower i).proj y.val).property,y.property⟩⟩
  have hp := congrFun he q
  have hpoint := originalTerminalTransition_pair_point N hN i j y
  exact hp.trans (congrArg (originalSourceChartSmoothMap hf M hM j) hpoint.symm)

end Original
end
end Hironaka.HironakaSmoothSubmersionOriginalSourceChartCompatibility
