/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaDisjointConstructedAmbientLift
import Hironaka.Resolution.HironakaDisjointActualGlobalControlledSplit
import Hironaka.MarkedIdeal.HadamardBridge

/-! Construct an ACTUAL ambient admissible mark-one controlled blowup using
only the original intrinsic step, whole traced boundary, and lower original
ideal admissibility. The entire old ideal remains nonradical. No ambient pi,
upper admissibility or target controlled trace is assumed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaDisjointConstructedControlledLift
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  NormalCrossings BlowupStrictSubmanifold SubmanifoldChartedSpace
  HironakaActualClosedContactBlowupRestriction InvertibleIdealQuotient
  RelativePrincipalizationSpan GermIdealOrder GermIdealTotalTransform
  HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaActualSingularChartTransport BlowupControlledTransform BlowupStrictIdeal
  BlowupExceptionalDivisor IdealWeightPowers GermIdealPullbackCalculus
  HironakaSmoothSubmersionGermIdealColon

/-- Lower mark-one SOURCE admissibility forces actual full ambient cosupport
at every literal image-centre point. No normal containment or upper pi needed. -/
theorem image_subset_cosupport_of_native_admissibility {n d : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {N : Set X} (hk : d≤n) (hS : ∀ x∈N,RegularAtDim (n := n) N x d)
    (J : GermIdeal n X) (hJ : J.IsCoherent) :
    letI := chartedSpace hk hS
    letI := isComplexManifold_chartedSpace hk hS
    ∀ (D : Set N), (GermIdeal.pullback (m := d) (Subtype.val : N → X) J).Le
      (idealPow (vanishingIdeal (n := d) D) 1) →
      ((Subtype.val : N → X) '' D) ⊆ cosupport n univ J 1 := by
  let := chartedSpace hk hS
  let := isComplexManifold_chartedSpace hk hS
  intro D hadm
  rw [cosupport_one (fun x F hF => GermIdeal.IsCoherent.holomorphicAt_mem hJ hF)]
  rintro _ ⟨p,hp,rfl⟩
  refine ⟨mem_univ _,?_⟩
  intro F hF
  have hFhol : HolomorphicAt n F p.val := GermIdeal.IsCoherent.holomorphicAt_mem hJ hF
  have hcomp : HolomorphicAt d (F∘(Subtype.val : N → X)) p :=
    hFhol.comp_contMDiff (Eventually.of_forall fun _ => (contMDiff_val hk hS).contMDiffAt)
  have hpull : (GermIdeal.pullback (m := d) (Subtype.val : N → X) J).mem p
      (F∘(Subtype.val : N → X)) := by
    apply GermIdeal.mem_pullback_iff.mpr
    exact isInSpanAt_self ⟨F,hF,rfl⟩ hcomp
  have hpow := hadm p (F∘(Subtype.val : N → X)) hpull
  obtain ⟨_hhol,r,s,a,hs,_ha,heq⟩ := mem_idealPow_succ_iff.mp hpow
  change (F∘(Subtype.val : N → X)) p=0
  rw [heq.self_of_nhds]
  apply Finset.sum_eq_zero
  intro i _hi
  obtain ⟨b,c,_hb,hc,hsi⟩ := hs i
  have hc0 : c p=0 := hc.2.self_of_nhds hp
  rw [hsi]
  simp only [Pi.mul_apply,hc0,mul_zero]

/-- Construct the genuine whole one-step controlled ambient lift from the
prescribed lower step and lower admissibility, retaining ALL old/born geometry. -/
theorem exists_constructed_controlled_lift {d t : ℕ} {X Z : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]
    {N : Set X} (hNc : IsClosed N)
    (hS : ∀ x∈N, RegularAtDim (n := d+t) N x d) (ht : 0<t)
    {B : List (Set X)} (hB : IsSNCDivisor (d+t) B) (hT : IsTransverse (d+t) N B)
    (J : GermIdeal (d+t) X) (hJ : J.IsCoherent)
    (hnormal : (vanishingIdeal (n := d+t) N).Le J) :
    letI := chartedSpace (Nat.le_add_right d t) hS
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
    ∀ (D : Set N) (ρ : Z → N) (hρ : IsBlowupAlong d D ρ),
      HasNormalCrossings d D (B.map fun H => (Subtype.val : N → X) ⁻¹' H) →
      (GermIdeal.pullback (m := d) (Subtype.val : N → X) J).Le
        (idealPow (vanishingIdeal (n := d) D) 1) →
      ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (d+t)) Y)
        (_ : IsComplexManifold (d+t) Y) (π : Y → X)
        (hπ : IsBlowupAlong (d+t) ((Subtype.val : N → X) '' D) π),
        J.Le (idealPow (vanishingIdeal (n := d+t) ((Subtype.val : N → X) '' D)) 1) ∧
        HasNormalCrossings (d+t) ((Subtype.val : N → X) '' D) B ∧
        IsSNCDivisor (d+t) (B.map (geoStrictTransform π ((Subtype.val : N → X) '' D)) ++
          [π ⁻¹' ((Subtype.val : N → X) '' D)]) ∧
        IsTransverse (d+t) (geoStrictTransform π ((Subtype.val : N → X) '' D) N)
          (B.map (geoStrictTransform π ((Subtype.val : N → X) '' D)) ++
            [π ⁻¹' ((Subtype.val : N → X) '' D)]) ∧
        (letI := strictChartedSpace (Nat.le_add_right d t) hNc hS hπ
         letI := strict_isComplexManifold (Nat.le_add_right d t) hNc hS hπ
         ∃ (E : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯
             geoStrictTransform π ((Subtype.val : N → X) '' D) N),
           restrictedProjection hNc D hπ ∘ E=ρ ∧
    ∀ (y : Y), y ∈ GermIdealOrder.cosupport (d+t) univ (controlledTransform hπ J 1) 1 →
    ∃ (hyS : y ∈ geoStrictTransform π ((Subtype.val : N → X) '' D) N)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
      (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y)=0)
      (Ψ : LocalHolomorphicEquivAt (chartAt (ComplexModel d) (E.symm ⟨y,hyS⟩) (E.symm ⟨y,hyS⟩)))
      (hΨ0 : Ψ.toFun (chartAt (ComplexModel d) (E.symm ⟨y,hyS⟩) (E.symm ⟨y,hyS⟩))=0),
      Θ.source ⊆ (chartAt (ComplexModel (d+t)) y).target ∧
      (∀ v, v ∈ (chartAt (ComplexModel (d+t)) y).source →
        chartAt (ComplexModel (d+t)) y v ∈ Θ.source →
        (v ∈ geoStrictTransform π ((Subtype.val : N → X) '' D) N ↔
          Θ.toFun (chartAt (ComplexModel (d+t)) y v) ∈ complexCoordinatePlane (d+t) d)) ∧
      Ideal.map (planeTrace d t).toRingHom (adaptedIdeal (controlledTransform hπ J 1) y Θ hΘ0)=
        adaptedIdeal (controlledTransform hρ (GermIdeal.pullback (m:=d) (Subtype.val : N → X) J) 1)
          (E.symm ⟨y,hyS⟩) Ψ hΨ0 ∧
      adaptedIdeal (controlledTransform hπ J 1) y Θ hΘ0=
        Ideal.comap (planeTrace d t).toRingHom
          (adaptedIdeal (controlledTransform hρ (GermIdeal.pullback (m:=d) (Subtype.val : N → X) J) 1)
            (E.symm ⟨y,hyS⟩) Ψ hΨ0)) := by
  let := chartedSpace (Nat.le_add_right d t) hS
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
  intro D ρ hρ hDNC hlower
  have hsub := image_subset_cosupport_of_native_admissibility
    (Nat.le_add_right d t) hS J hJ D hlower
  obtain ⟨Y,τ,cs,hY,π,hπ,hNC,hSNC,hT',_hgeometry⟩ :=
    HironakaDisjointConstructedAmbientLift.exists_constructed_ambient_lift hNc hS ht hB hT D ρ hρ hDNC
  have hadm := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hJ hπ.1 hsub
  refine ⟨Y,τ,cs,hY,π,hπ,hadm,hNC,hSNC,hT',?_⟩
  exact HironakaDisjointActualGlobalControlledSplit.exists_actual_global_controlled_split
    hNc hS D π hπ J hJ hnormal hadm ρ hρ

end
end Hironaka.HironakaDisjointConstructedControlledLift
