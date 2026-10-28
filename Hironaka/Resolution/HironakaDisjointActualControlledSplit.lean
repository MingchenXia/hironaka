/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaDisjointMatchedControlledTrace
import Hironaka.Resolution.HironakaDisjointFlattenedNormalKernel
import Hironaka.Resolution.HironakaActualStrictContactBlowupCoordinates
import Hironaka.Analytic.VanishingIdealZeroLocus

/-! Actual prescribed ambient/base blowups and the WHOLE mark-one controlled
split; old ideals remain nonradical. Source-facing BP precedes Lean. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaDisjointActualControlledSplit
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupExceptionalDivisor BlowupControlledTransform BlowupStrictIdeal
  BlowupStrictSubmanifold InvertibleIdealQuotient IdealWeightPowers
  RelativePrincipalizationSpan GermIdealPullbackCalculus GermIdealTotalTransform
  HironakaSmoothSubmersionCoefficientIdeals VanishingIdealZeroLocus
  HironakaActualClosedContactBlowupRestriction HironakaActualClosedContactControlledRestriction
  HironakaDisjointMatchedControlledTrace HironakaActualStrictContactBlowupCoordinates
  HironakaRelativeNormalIdeal HironakaSmoothSubmersionGermIdealColon
  HironakaActualSingularChartTransport HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance BlowupFlatCoordinates

theorem controlled_pullback_over {d : ℕ} {N P Z : Type}
    [TopologicalSpace N] [ChartedSpace (ComplexModel d) N] [IsComplexManifold d N]
    [TopologicalSpace P] [ChartedSpace (ComplexModel d) P] [IsComplexManifold d P]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]
    {D : Set N} {σ : P → N} {ρ : Z → N}
    (hσ : IsBlowupAlong d D σ) (hρ : IsBlowupAlong d D ρ)
    (E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P)
    (hcomm : σ ∘ E=ρ) (I : GermIdeal d N) (hI : I.IsCoherent)
    (hadm : I.Le (idealPow (vanishingIdeal (n:=d) D) 1)) :
    GermIdeal.pullback (m:=d) E (controlledTransform hσ I 1)=controlledTransform hρ I 1 := by
  have hQ:=isCoherent_controlledTransform hσ hI hadm
  have hD:=isCoherent_ideal (exceptionalDivisor hσ)
  have hD1:=isCoherent_idealPow hD 1
  have hDI : GermIdeal.pullback (m:=d) E (exceptionalDivisor hσ).ideal=(exceptionalDivisor hρ).ideal := by
    rw [exceptionalDivisor_ideal,exceptionalDivisor_ideal,
      ←pullback_comp hσ.contMDiff E.contMDiff (isCoherent_vanishingIdeal_centre hσ),hcomm]
  have hDP : GermIdeal.pullback (m:=d) E (idealPow (exceptionalDivisor hσ).ideal 1)=
      idealPow (exceptionalDivisor hρ).ideal 1 := by
    rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow E.contMDiff hD 1,hDI]
  apply eq_controlledTransform_of_eq_mul hρ (isCoherent_pullback E.contMDiff hQ)
  calc
    GermIdeal.pullback (m:=d) ρ I=GermIdeal.pullback (m:=d) E (GermIdeal.pullback (m:=d) σ I) := by
      rw [←pullback_comp hσ.contMDiff E.contMDiff hI,hcomm]
    _=GermIdeal.pullback (m:=d) E ((idealPow (exceptionalDivisor hσ).ideal 1).mul (controlledTransform hσ I 1)) := by
      rw [pullback_eq_mul_controlledTransform hσ hI hadm]
    _=(GermIdeal.pullback (m:=d) E (idealPow (exceptionalDivisor hσ).ideal 1)).mul
        (GermIdeal.pullback (m:=d) E (controlledTransform hσ I 1)) := HironakaSmoothSubmersionCoefficientIdeals.pullback_mul E.contMDiff hD1 hQ
    _=(idealPow (exceptionalDivisor hρ).ideal 1).mul
        (GermIdeal.pullback (m:=d) E (controlledTransform hσ I 1)) := by rw [hDP]

theorem current_cosupport_mem_strict_contact {n : ℕ} {A Y : Type}
    [TopologicalSpace A] [ChartedSpace (ComplexModel n) A] [IsComplexManifold n A]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {C N : Set A} {π : Y → A} (hπ : IsBlowupAlong n C π)
    (hN : IsClosedSubmanifold n N) (hCN : C ⊆ N)
    (J : GermIdeal n A) (hnormal : (vanishingIdeal (n:=n) N).Le J)
    (y : Y) (hcut : y  ∈  GermIdealOrder.cosupport n univ (controlledTransform hπ J 1) 1) :
    y  ∈  geoStrictTransform π C N := by
  have hmono : (controlledTransform hπ (vanishingIdeal (n:=n) N) 1).Le (controlledTransform hπ J 1) := by
    intro z F hF
    exact ⟨hF.1,fun g hg => pullback_le_pullback hnormal z (fun w => g w*F w) (hF.2 g hg)⟩
  rw [controlledTransform_vanishingIdeal hπ hN hCN] at hmono
  apply zeroLocus_vanishingIdeal_subset (n:=n) (show IsClosed (geoStrictTransform π C N) from isClosed_closure)
  intro F hF
  have hm:=hmono y F hF
  exact (GermIdealOrder.vanishesToOrderOn_one_iff (mem_univ y) hm.1).mp (hcut.2 F hm)

section Actual
variable {d t : ℕ} {A Y Z : Type}
    [TopologicalSpace A] [ChartedSpace (ComplexModel (d+t)) A] [IsComplexManifold (d+t) A]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- Internally produced actual comparison and matched trace for prescribed
ambient and base blowups. The lower source ideal is its literal WHOLE pullback. -/
theorem exists_actual_controlled_split {N : Set A} (hNc : IsClosed N)
    (hN : ∀ x ∈ N,RegularAtDim (n:=d+t) N x d) (D : Set N)
    (π : Y → A) (hπ : IsBlowupAlong (d+t) ((Subtype.val : N → A) '' D) π)
    (J : GermIdeal (d+t) A) (hJ : J.IsCoherent)
    (hnormal : (vanishingIdeal (n:=d+t) N).Le J)
    (hadm : J.Le (idealPow (vanishingIdeal (n:=d+t) ((Subtype.val : N → A) '' D)) 1))
    (y : Y) (hcut : y ∈ GermIdealOrder.cosupport (d+t) univ (controlledTransform hπ J 1) 1)
    (k : ℕ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) (π y) (π y)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π y))=0)
    (hflatC : ∀ {x : A},x ∈ (chartAt (ComplexModel (d+t)) (π y)).source →
      chartAt (ComplexModel (d+t)) (π y) x ∈ Φ.source →
      (x ∈ (Subtype.val : N → A) '' D ↔ Φ.toFun (chartAt (ComplexModel (d+t)) (π y) x) ∈ complexCoordinatePlane (d+t) k))
    (hflatN : ∀ {x : A},x ∈ (chartAt (ComplexModel (d+t)) (π y)).source →
      chartAt (ComplexModel (d+t)) (π y) x ∈ Φ.source →
      (x ∈ N ↔ Φ.toFun (chartAt (ComplexModel (d+t)) (π y) x) ∈ complexCoordinatePlane (d+t) d)) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_add_right d t) hN
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (ρ : Z → N) (hρ : IsBlowupAlong d D ρ),
    ∃ (hyS : y ∈ geoStrictTransform π ((Subtype.val : N → A) '' D) N),
    letI := strictChartedSpace (Nat.le_add_right d t) hNc hN hπ
    letI := strict_isComplexManifold (Nat.le_add_right d t) hNc hN hπ
    ∃ (E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
      geoStrictTransform π ((Subtype.val : N → A) '' D) N),
      restrictedProjection hNc D hπ ∘ E=ρ ∧
    ∃ (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
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
  have hCN : ((Subtype.val : N → A) '' D) ⊆ N:=by rintro _ ⟨p,_hp,rfl⟩;exact p.property
  have hNcsm : IsClosedSubmanifold (d+t) N:=⟨hNc,fun x hx=>⟨d,hN x hx⟩⟩
  have hyS:=current_cosupport_mem_strict_contact hπ hNcsm hCN J hnormal y hcut
  refine ⟨hyS,?_⟩
  let := strictChartedSpace hk hNc hN hπ
  let := strict_isComplexManifold hk hNc hN hπ
  let S:=geoStrictTransform π ((Subtype.val : N → A) '' D) N
  have hS : ∀ v ∈ S,RegularAtDim (n:=d+t) S v d:=fun v hv=>regularAtDim_geoStrictTransform hπ hNc hN hCN hv
  obtain ⟨E,hcomm⟩:=exists_strictContact_diffeomorph hk hNc hN hπ hρ
  refine ⟨E,hcomm,?_⟩
  obtain ⟨_e,_b,Θ,hsrc,hΘ0,_he,_hed,_hbt,_hbn,_hbe,hchart⟩:=
    exists_actual_strict_contact_blowup_coordinates hπ y k d Φ hΦsrc hΦ0 hflatC hflatN hyS
  have htarget : ∀ v, v ∈ (chartAt (ComplexModel (d+t)) y).source →
      chartAt (ComplexModel (d+t)) y v ∈ Θ.source →
      (v ∈ S ↔ Θ.toFun (chartAt (ComplexModel (d+t)) y v) ∈ complexCoordinatePlane (d+t) d):=
    fun v hv hvΘ=>(hchart v hv hvΘ).2.2
  let p : S:=⟨y,hyS⟩
  obtain ⟨Ψ,hΨ0,_hcoord,htrace⟩:=exists_matched_coherent_trace hS p Θ hsrc hΘ0 htarget E
  have hJctrl:=isCoherent_controlledTransform hπ hJ hadm
  have htraceJ:=htrace (controlledTransform hπ J 1) hJctrl
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
  rw [hwhole] at htraceJ
  have hInc : (vanishingIdeal (n:=d+t) S).Le (controlledTransform hπ J 1) := by
    have hm : (controlledTransform hπ (vanishingIdeal (n:=d+t) N) 1).Le (controlledTransform hπ J 1) := by
      intro v F hF
      exact ⟨hF.1,fun g hg => pullback_le_pullback hnormal v (fun w => g w*F w) (hF.2 g hg)⟩
    rw [controlledTransform_vanishingIdeal hπ hNcsm hCN] at hm
    exact hm
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
  exact ⟨Θ,hΘ0,Ψ,hΨ0,hsrc,htarget,htraceJ,hfull⟩
end Actual
end
end Hironaka.HironakaDisjointActualControlledSplit
