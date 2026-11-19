import Hironaka.Resolution.HironakaActualNativeLowerEmbedding
import Hironaka.Resolution.HironakaActualNativeSectionZeroWholeTails
import Hironaka.Resolution.HironakaDisjointRecursiveNativeHistory

/-! Actual lower-tail native frames for the SAME joint contact glueing and
actual prescribed ambient/native histories. No canonicality certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeLowerTailFrames
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail BlowupTowerSplitIso
  ResolutionInvariantSpec InvDomainTowerAlong NormalCrossings NormalCrossingsInvariance
  SubmanifoldChartedSpace SubmanifoldCodRestrict MarkedIdealBiholomorphism
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionNormalCrossings
  HironakaActualNativeInvariantDomain HironakaDisjointNativeOpenLift HironakaDisjointNativeReferenceWindow
  HironakaActualNativeSectionZeroWholeTails HironakaActualNativeSectionContactChoices
  HironakaActualNativeLowerEmbedding HironakaDisjointRecursiveNativeHistory
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  HomogenizedIdealAlong HomogenizedIdealAlongTower HomogenizedGlueingAlong HomogenizedGlueingAlongTower
  HomogenizedGlueingLiftAlong HomogenizedGlueingTower MemberInterTowerAlong
  StepOneValue StepOneValueMasked StepOneLowerDomain StepOneTangentChange
  RelativePrincipalizationSpan GermIdealPullbackCalculus

private theorem actual_changed_tail_frame_core {n k : ℕ} {X : CMfd.{0} n}
    {hk : k≤n} {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    {E : List (Set X)} {Y : CMfd.{0} n} {T : BlowupTower X Y}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (U U' : Opens (nativeManifold hk W hW))
    (Φ : CMfd.of (n:=k) U ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ CMfd.of (n:=k) U')
    (χ : CMfd.of (n:=k) (openPreimage Q U) ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
      CMfd.of (n:=k) (openPreimage Q U'))
    (hχ : IsTowerIso Φ (restrict U Q) (restrict U' Q) χ)
    (O : Opens U) (B : Opens X)
    (hTrace : (Subtype.val : W→X) ⁻¹' (B : Set X)=
      (Subtype.val : U'→nativeManifold hk W hW) '' (Φ '' (O : Set U)))
    (Ψ : CMfd.of (n:=k) O ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
      nativeManifold hk (openSection W B) (openSection_regular hW B))
    (hΨ : ∀w,(Ψ w).val.val=(Φ w.val).val.val) :
    ∃(hSc : IsClosed (openSection V (openPreimage T B)))
      (hS : ∀y∈openSection V (openPreimage T B),RegularAtDim (n:=n) (openSection V (openPreimage T B)) y k)
      (P : BlowupTower (nativeManifold hk (openSection W B) (openSection_regular hW B))
        (nativeManifold hk (openSection V (openPreimage T B)) hS))
      (ν : CMfd.of (n:=k) (openPreimage (restrict U Q) O) ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
        nativeManifold hk (openSection V (openPreimage T B)) hS),
      Lift hk (openSection W B) (hWc.preimage continuous_subtype_val) (openSection_regular hW B)
        (E.map ((Subtype.val : B→X) ⁻¹' ·)) (restrict B T) (openSection V (openPreimage T B)) hSc hS P ∧
      IsTowerIso Ψ (restrict O (restrict U Q)) P ν ∧
      ∀w,(endpointEquiv h B (ν w)).val.val=(χ w.val).val.val := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let NWB:=nativeWindow hk W hW B
  have hBU' : NWB≤U':=by
    intro y hy
    have hS : y∈(Subtype.val : U'→nativeManifold hk W hW) '' (Φ '' (O : Set U)):=by
      rw [←hTrace]
      exact hy
    obtain ⟨z,_hz,hzy⟩:=hS
    exact hzy ▸ z.property
  let C:=MaxLocusLocal.nestedOpens U' NWB
  have hMatch : ∀y : U,y∈O ↔ Φ y∈C:=by
    intro y
    change y∈O ↔ (Φ y).val∈(Subtype.val : W→X) ⁻¹' (B : Set X)
    rw [hTrace]
    constructor
    · intro hy;exact ⟨Φ y,⟨y,hy,rfl⟩,rfl⟩
    · rintro ⟨z,⟨w,hw,hwz⟩,hzPhi⟩
      have hz : z=Φ y:=Subtype.ext hzPhi
      have hwy : w=y:=Φ.injective (hwz.trans hz)
      exact hwy ▸ hw
  let F:=diffeoOpens Φ O C hMatch
  have hEndMatch:=isTowerIso_mem_openPreimage_iff hχ hMatch
  let χO:=diffeoOpens χ (openPreimage (restrict U Q) O) (openPreimage (restrict U' Q) C) hEndMatch
  have hRestricted : IsTowerIso F (restrict O (restrict U Q)) (restrict C (restrict U' Q)) χO:=
    isTowerIso_restrictOpens hMatch hχ hEndMatch
  let τ:=MaxLocusLocal.nestedDiffeo (n:=k) (openPreimage Q U')
    (openPreimage (restrict U' Q) C) (openPreimage Q NWB)
    (MaxLocusLocal.mem_openPreimage_restrict_nestedOpens U' NWB Q) (MaxLocusLocal.openPreimage_mono Q hBU')
  have hFlat : IsTowerIso (MaxLocusLocal.nestedOpensDiffeo (n:=k) hBU')
      (restrict C (restrict U' Q)) (restrict NWB Q) τ:=
    MaxLocusLocal.isTowerIso_restrict_nestedOpens hBU' Q
  obtain ⟨hSc,hS,P,hActual,hNativeFrame⟩:=exists_open_lift h B
  let δ:=χO.trans τ
  let ν:=δ.trans (endpointEquiv h B).symm
  have hAll:=((hRestricted.trans hFlat).trans hNativeFrame.symm)
  have hFrame : IsTowerIso Ψ (restrict O (restrict U Q)) P ν:=by
    apply BlowupTowerSplitIso.IsTowerIso.congr_base hAll
    intro w
    apply Subtype.ext
    apply Subtype.ext
    exact hΨ w
  refine ⟨hSc,hS,P,ν,hActual,hFrame,?_⟩
  intro w
  change (endpointEquiv h B ((endpointEquiv h B).symm (δ w))).val.val=(χ w.val).val.val
  rw [(endpointEquiv h B).apply_symm_apply]
  rfl

/-- Actual stagewise frame of the SAME contact-changed tail by the actual
native Lift of the literal ambient restriction. The endpoint keeps the exact
original contact map on ambient points; no native CAN/domain certificate. -/
theorem exists_actual_changed_tail_frame {n k : ℕ} {X : CMfd.{0} n}
    {hk : k≤n} {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    {E : List (Set X)} {Y : CMfd.{0} n} {T : BlowupTower X Y}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW E T V hVc hV Q)
    (U U' : Opens (nativeManifold hk W hW))
    (Φ : CMfd.of (n:=k) U ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ CMfd.of (n:=k) U')
    (χ : CMfd.of (n:=k) (openPreimage Q U) ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
      CMfd.of (n:=k) (openPreimage Q U'))
    (hχ : IsTowerIso Φ (restrict U Q) (restrict U' Q) χ)
    (O : Opens U) (B : Opens X)
    (hTrace : (Subtype.val : W→X) ⁻¹' (B : Set X)=
      (Subtype.val : U'→nativeManifold hk W hW) '' (Φ '' (O : Set U)))
    (Ψ : CMfd.of (n:=k) O ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
      nativeManifold hk (openSection W B) (openSection_regular hW B))
    (hΨ : ∀w,(Ψ w).val.val=(Φ w.val).val.val) :
    ∃(hSc : IsClosed (openSection V (openPreimage T B)))
      (hS : ∀y∈openSection V (openPreimage T B),RegularAtDim (n:=n) (openSection V (openPreimage T B)) y k)
      (P : BlowupTower (nativeManifold hk (openSection W B) (openSection_regular hW B))
        (nativeManifold hk (openSection V (openPreimage T B)) hS))
      (ν : CMfd.of (n:=k) (openPreimage (restrict U Q) O) ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
        nativeManifold hk (openSection V (openPreimage T B)) hS),
      Lift hk (openSection W B) (hWc.preimage continuous_subtype_val) (openSection_regular hW B)
        (E.map ((Subtype.val : B→X) ⁻¹' ·)) (restrict B T) (openSection V (openPreimage T B)) hSc hS P ∧
      IsTowerIso Ψ (restrict O (restrict U Q)) P ν ∧
      ∀w,(ν w).val.val=(χ w.val).val.val := by
  obtain ⟨hSc,hS,P,ν,hActual,hFrame,hPoint⟩:=actual_changed_tail_frame_core h U U' Φ χ hχ O B hTrace Ψ hΨ
  refine ⟨hSc,hS,P,ν,hActual,hFrame,?_⟩
  intro w
  have hp:=hPoint w
  rw [endpointEquiv_val_native h B (ν w)] at hp
  exact hp

end
end Hironaka.HironakaActualNativeLowerTailFrames
