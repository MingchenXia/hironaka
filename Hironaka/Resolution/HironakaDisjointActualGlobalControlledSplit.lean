/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaDisjointActualControlledSplit

/-! Whole actual mark-one split at EVERY current cosupport point. Actual
strict-contact regularity itself chooses the ambient flattening; no source
joint chart or over-centre condition remains. ONE prescribed-base comparison
is constructed before quantifying over current points. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaDisjointActualGlobalControlledSplit
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupExceptionalDivisor BlowupControlledTransform BlowupStrictIdeal
  BlowupStrictSubmanifold InvertibleIdealQuotient IdealWeightPowers
  GermIdealPullbackCalculus HironakaActualClosedContactBlowupRestriction
  HironakaActualClosedContactControlledRestriction HironakaDisjointActualControlledSplit
  HironakaDisjointMatchedControlledTrace HironakaRelativeNormalIdeal
  HironakaSmoothSubmersionGermIdealColon
variable {d t : ℕ} {A Y Z : Type}
    [TopologicalSpace A] [ChartedSpace (ComplexModel (d+t)) A] [IsComplexManifold (d+t) A]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- No chart/centre-coordinate/trace certificate is input. Actual native
regularity chooses each Θ; ONE actual E works on the entire current cosupport. -/
theorem exists_actual_global_controlled_split {N : Set A} (hNc : IsClosed N)
    (hN : ∀ x ∈ N,RegularAtDim (n:=d+t) N x d) (D : Set N)
    (π : Y → A) (hπ : IsBlowupAlong (d+t) ((Subtype.val : N → A) '' D) π)
    (J : GermIdeal (d+t) A) (hJ : J.IsCoherent)
    (hnormal : (vanishingIdeal (n:=d+t) N).Le J)
    (hadm : J.Le (idealPow (vanishingIdeal (n:=d+t) ((Subtype.val : N → A) '' D)) 1)) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_add_right d t) hN
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (ρ : Z → N) (hρ : IsBlowupAlong d D ρ),
    letI := strictChartedSpace (Nat.le_add_right d t) hNc hN hπ
    letI := strict_isComplexManifold (Nat.le_add_right d t) hNc hN hπ
    ∃ (E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
      geoStrictTransform π ((Subtype.val : N → A) '' D) N),
      restrictedProjection hNc D hπ ∘ E=ρ ∧
    ∀ (y : Y), y ∈ GermIdealOrder.cosupport (d+t) univ (controlledTransform hπ J 1) 1 →
    ∃ (hyS : y ∈ geoStrictTransform π ((Subtype.val : N → A) '' D) N)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
      (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y)=0)
      (Ψ : LocalHolomorphicEquivAt (chartAt (ComplexModel d) (E.symm ⟨y,hyS⟩) (E.symm ⟨y,hyS⟩)))
      (hΨ0 : Ψ.toFun (chartAt (ComplexModel d) (E.symm ⟨y,hyS⟩) (E.symm ⟨y,hyS⟩))=0),
      Θ.source ⊆ (chartAt (ComplexModel (d+t)) y).target ∧
      (∀ v, v ∈ (chartAt (ComplexModel (d+t)) y).source →
        chartAt (ComplexModel (d+t)) y v ∈ Θ.source →
        (v ∈ geoStrictTransform π ((Subtype.val : N → A) '' D) N ↔
          Θ.toFun (chartAt (ComplexModel (d+t)) y v) ∈ complexCoordinatePlane (d+t) d)) ∧
      Ideal.map (planeTrace d t).toRingHom (adaptedIdeal (controlledTransform hπ J 1) y Θ hΘ0)=
        adaptedIdeal (controlledTransform hρ (GermIdeal.pullback (m:=d) (Subtype.val : N → A) J) 1)
          (E.symm ⟨y,hyS⟩) Ψ hΨ0 ∧
      adaptedIdeal (controlledTransform hπ J 1) y Θ hΘ0=
        Ideal.comap (planeTrace d t).toRingHom
          (adaptedIdeal (controlledTransform hρ (GermIdeal.pullback (m:=d) (Subtype.val : N → A) J) 1)
            (E.symm ⟨y,hyS⟩) Ψ hΨ0) := by
  let hk:=Nat.le_add_right d t
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  intro ρ hρ
  let := strictChartedSpace hk hNc hN hπ
  let := strict_isComplexManifold hk hNc hN hπ
  let S:=geoStrictTransform π ((Subtype.val : N → A) '' D) N
  have hCN : ((Subtype.val : N → A) '' D) ⊆ N:=by rintro _ ⟨p,_hp,rfl⟩;exact p.property
  have hNcsm : IsClosedSubmanifold (d+t) N:=⟨hNc,fun x hx=>⟨d,hN x hx⟩⟩
  have hS : ∀ v ∈ S,RegularAtDim (n:=d+t) S v d:=fun v hv=>regularAtDim_geoStrictTransform hπ hNc hN hCN hv
  obtain ⟨E,hcomm⟩:=exists_strictContact_diffeomorph hk hNc hN hπ hρ
  have hJctrl:=isCoherent_controlledTransform hπ hJ hadm
  let I:=GermIdeal.pullback (m:=d) (Subtype.val : N → A) J
  have hI : I.IsCoherent:=isCoherent_pullback (SubmanifoldChartedSpace.contMDiff_val hk hN) hJ
  have hIadm : I.Le (idealPow (vanishingIdeal (n:=d) D) 1):=
    restricted_original_admissibility hk hN hπ J 1 hadm
  have hσ:=restrictedProjection_isBlowupAlong hk hNc hN D hπ hρ.1 hρ.2.1
  have hrest:=restricted_controlledTransform hk hNc hN hπ J hJ 1 hadm hρ.1 hρ.2.1
  have htrans:=controlled_pullback_over hσ hρ E hcomm I hI hIadm
  have hvalS : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ (Subtype.val : S → Y):=
    SubmanifoldChartedSpace.contMDiff_val hk hS
  have hwhole : GermIdeal.pullback (m:=d) (fun z : Z => (E z).val) (controlledTransform hπ J 1)=controlledTransform hρ I 1 := by
    calc
      _=GermIdeal.pullback (m:=d) E (GermIdeal.pullback (m:=d) (Subtype.val : S → Y) (controlledTransform hπ J 1)) :=
        HironakaSmoothSubmersionOrderedChoiceImageTrace.coherent_pullback_comp hvalS E.contMDiff (controlledTransform hπ J 1) hJctrl
      _=controlledTransform hρ I 1 := by rw [hrest,htrans]
  have hInc : (vanishingIdeal (n:=d+t) S).Le (controlledTransform hπ J 1) := by
    have hm : (controlledTransform hπ (vanishingIdeal (n:=d+t) N) 1).Le (controlledTransform hπ J 1) := by
      intro v F hF
      exact ⟨hF.1,fun g hg => pullback_le_pullback hnormal v (fun w => g w*F w) (hF.2 g hg)⟩
    rw [controlledTransform_vanishingIdeal hπ hNcsm hCN] at hm
    exact hm
  refine ⟨E,hcomm,fun y hcut => ?_⟩
  have hyS:=current_cosupport_mem_strict_contact hπ hNcsm hCN J hnormal y hcut
  obtain ⟨Θ,hsrc,hΘ0,hflat⟩:=(hS y hyS).2.2
  have htarget : ∀ v, v ∈ (chartAt (ComplexModel (d+t)) y).source →
      chartAt (ComplexModel (d+t)) y v ∈ Θ.source →
      (v ∈ S ↔ Θ.toFun (chartAt (ComplexModel (d+t)) y v) ∈ complexCoordinatePlane (d+t) d):=
    fun v hv hvΘ=>hflat hv hvΘ
  let p : S:=⟨y,hyS⟩
  obtain ⟨Ψ,hΨ0,_hcoord,htrace⟩:=exists_matched_coherent_trace hS p Θ hsrc hΘ0 htarget E
  have htraceJ:=htrace (controlledTransform hπ J 1) hJctrl
  rw [hwhole] at htraceJ
  have hker:=HironakaDisjointFlattenedNormalKernel.ker_planeTrace_le_adaptedIdeal S y Θ hsrc hΘ0 htarget
    (controlledTransform hπ J 1) hInc
  have hfull : adaptedIdeal (controlledTransform hπ J 1) y Θ hΘ0=
      Ideal.comap (planeTrace d t).toRingHom (adaptedIdeal (controlledTransform hρ I 1) (E.symm p) Ψ hΨ0) := by
    have hm:=Ideal.comap_map_of_surjective (planeTrace d t).toRingHom (planeTrace_surjective d t)
      (adaptedIdeal (controlledTransform hπ J 1) y Θ hΘ0)
    change Ideal.comap (planeTrace d t).toRingHom
      (Ideal.map (planeTrace d t).toRingHom (adaptedIdeal (controlledTransform hπ J 1) y Θ hΘ0))=
        adaptedIdeal (controlledTransform hπ J 1) y Θ hΘ0 ⊔ RingHom.ker (planeTrace d t).toRingHom at hm
    rw [sup_of_le_left hker] at hm
    exact hm.symm.trans (congrArg (Ideal.comap (planeTrace d t).toRingHom) htraceJ)
  exact ⟨hyS,Θ,hΘ0,Ψ,hΨ0,hsrc,htarget,htraceJ,hfull⟩
end
end Hironaka.HironakaDisjointActualGlobalControlledSplit
