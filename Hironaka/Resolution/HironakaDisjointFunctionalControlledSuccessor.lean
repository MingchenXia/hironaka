/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaDisjointConstructedControlledLift
import Hironaka.Resolution.HironakaDisjointStrictBoundaryTrace

/-! Actual constructed one-step functional controlled successor. The SAME
factory pi and ONE native comparison carry whole functional ideal equality,
persistent entire normal containment, coherence, and the entire old/born
boundary. No incoming successor record, ideal or boundary dictionary. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaDisjointFunctionalControlledSuccessor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  NormalCrossings BlowupStrictSubmanifold SubmanifoldChartedSpace
  HironakaActualClosedContactBlowupRestriction HironakaActualClosedContactControlledRestriction
  InvertibleIdealQuotient BlowupControlledTransform BlowupStrictIdeal
  BlowupExceptionalDivisor IdealWeightPowers GermIdealPullbackCalculus
  HironakaSmoothSubmersionGermIdealColon HironakaDisjointActualControlledSplit

/-- One actual internally constructed ambient successor carries ENTIRE
functional ideal equality and the SAME complete chronological boundary. -/
theorem exists_functional_controlled_successor {d t : ℕ} {X Z : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]
    {N : Set X} (hNc : IsClosed N)
    (hS : ∀ x∈N,RegularAtDim (n := d+t) N x d) (ht : 0<t)
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
        let S := geoStrictTransform π ((Subtype.val : N → X) '' D) N
        let K := controlledTransform hπ J 1
        let B' := B.map (geoStrictTransform π ((Subtype.val : N → X) '' D)) ++
          [π ⁻¹' ((Subtype.val : N → X) '' D)]
        J.Le (idealPow (vanishingIdeal (n := d+t) ((Subtype.val : N → X) '' D)) 1) ∧
        IsClosed S ∧ (∀ y∈S,RegularAtDim (n := d+t) S y d) ∧
        K.IsCoherent ∧ (vanishingIdeal (n := d+t) S).Le K ∧
        IsSNCDivisor (d+t) B' ∧ IsTransverse (d+t) S B' ∧
        (letI := strictChartedSpace (Nat.le_add_right d t) hNc hS hπ
         letI := strict_isComplexManifold (Nat.le_add_right d t) hNc hS hπ
         ∃ F : Z ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ S,
           restrictedProjection hNc D hπ ∘ F=ρ ∧
           GermIdeal.pullback (m := d) (fun z : Z => (F z).val) K=
             controlledTransform hρ (GermIdeal.pullback (m := d) (Subtype.val : N → X) J) 1 ∧
           (∀ i : Fin B.length,
             F ⁻¹' ((Subtype.val : S → Y) ⁻¹'
               geoStrictTransform π ((Subtype.val : N → X) '' D) (B.get i))=
               geoStrictTransform ρ D ((Subtype.val : N → X) ⁻¹' B.get i)) ∧
           F ⁻¹' ((Subtype.val : S → Y) ⁻¹' (π ⁻¹' ((Subtype.val : N → X) '' D)))=ρ ⁻¹' D ∧
           B'.map (fun H => (fun z : Z => (F z).val) ⁻¹' H)=
             (B.map fun H => (Subtype.val : N → X) ⁻¹' H).map (geoStrictTransform ρ D) ++[ρ ⁻¹' D]) := by
  let hk := Nat.le_add_right d t
  let := chartedSpace hk hS
  let := isComplexManifold_chartedSpace hk hS
  intro D ρ hρ hDNC hlower
  obtain ⟨Y,τ,cs,hY,π,hπ,hadm,_hNC,hSNC,hT',hcomp⟩ :=
    HironakaDisjointConstructedControlledLift.exists_constructed_controlled_lift
      hNc hS ht hB hT J hJ hnormal D ρ hρ hDNC hlower
  let S := geoStrictTransform π ((Subtype.val : N → X) '' D) N
  have hCN : ((Subtype.val : N → X) '' D)⊆N := by
    rintro _ ⟨p,_hp,rfl⟩; exact p.property
  have hS' : ∀ y∈S,RegularAtDim (n := d+t) S y d :=
    fun y hy => regularAtDim_geoStrictTransform hπ hNc hS hCN hy
  have hK : (controlledTransform hπ J 1).IsCoherent := isCoherent_controlledTransform hπ hJ hadm
  have hNreg : IsClosedSubmanifold (d+t) N := ⟨hNc,fun x hx => ⟨d,hS x hx⟩⟩
  have hInc : (vanishingIdeal (n := d+t) S).Le (controlledTransform hπ J 1) := by
    have hm : (controlledTransform hπ (vanishingIdeal (n := d+t) N) 1).Le
        (controlledTransform hπ J 1) := by
      intro y f hf
      exact ⟨hf.1,fun g hg => pullback_le_pullback hnormal y
        (fun w => g w*f w) (hf.2 g hg)⟩
    rw [controlledTransform_vanishingIdeal hπ hNreg hCN] at hm
    exact hm
  let := strictChartedSpace hk hNc hS hπ
  let := strict_isComplexManifold hk hNc hS hπ
  obtain ⟨F,hcomm,_hpointwise⟩ := hcomp
  let I := GermIdeal.pullback (m := d) (Subtype.val : N → X) J
  have hI : I.IsCoherent := isCoherent_pullback (contMDiff_val hk hS) hJ
  have hσ := restrictedProjection_isBlowupAlong hk hNc hS D hπ hρ.1 hρ.2.1
  have hrest := restricted_controlledTransform hk hNc hS hπ J hJ 1 hadm hρ.1 hρ.2.1
  have htrans := controlled_pullback_over hσ hρ F hcomm I hI hlower
  have hval : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ (Subtype.val : S → Y) :=
    contMDiff_val hk hS'
  have hwhole : GermIdeal.pullback (m := d) (fun z : Z => (F z).val) (controlledTransform hπ J 1)=
      controlledTransform hρ I 1 := by
    calc
      _=GermIdeal.pullback (m := d) F
          (GermIdeal.pullback (m := d) (Subtype.val : S → Y) (controlledTransform hπ J 1)) :=
        HironakaSmoothSubmersionOrderedChoiceImageTrace.coherent_pullback_comp hval F.contMDiff
          (controlledTransform hπ J 1) hK
      _=controlledTransform hρ I 1 := by rw [hrest,htrans]
  have hn : 0<d+t := by omega
  refine ⟨Y,τ,cs,hY,π,hπ,hadm,isClosed_closure,hS',hK,hInc,hSNC,hT',F,hcomm,hwhole,?_,?_,?_⟩
  · exact HironakaDisjointStrictBoundaryTrace.every_original_strict_trace hNc hS hπ hn hB hT ρ F hcomm hDNC
  · exact HironakaDisjointStrictBoundaryTrace.born_exceptional_trace hNc hS hπ ρ F hcomm
  · exact HironakaDisjointStrictBoundaryTrace.whole_old_born_boundary_trace hNc hS hπ hn hB hT ρ F hcomm hDNC

end
end Hironaka.HironakaDisjointFunctionalControlledSuccessor
