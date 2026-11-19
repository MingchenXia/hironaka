import Hironaka.Resolution.HironakaActualTransportedOriginalTangent
import Hironaka.Invariant.ContactLowerValue

/-! Genuine target-only TN23 transport constructs an alternate kept contact
reference, its lower domain and canonical actual tail. These are outputs;
no alternate canonicality or numerical comparison is supplied. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualAlternateContactReference
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  RelativePrincipalizationSpan TangentDirectionAlong HomogenizedIdealAlong
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupTowerIsomorphism
  ResolutionInvariantExt StepOneValue StepOneLowerDomain
  StepOneValueMasked StepOneTangentChange ContactStageKept RestrictEmptyTower MaxLocusLocal
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y Z : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

theorem exists_alternate_contact_reference
    (R : ResolutionInvariant.{u,v} n k Λ) (B : MarkedIdeal n X)
    (hB : B.IsWellFormed) (hd : 1≤B.d)
    (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked B) (T₀.append T₁))
    (z : Z) (hz : z∈(geoTransformAlong (barMarked B) (T₀.append T₁)).cosupp)
    (hData : LowerDataL R B (lowerMarkedM B) 0 T₀ T₁ z)
    (O : Set X) (g : X → ℂ) (hg : IsTangentDirectionAlong B.N B.ideal B.d O g)
    (Wg : Opens Y) (hzWg : T₁.proj z∈Wg)
    (hWg : (Wg : Set Y)⊆T₀.proj ⁻¹' O)
    (hWgE : ∀H∈origMembers B T₀,Disjoint (Wg : Set Y) H) :
    ∃Vg : Opens Y,∃hzg : T₁.proj z∈Vg,Vg≤Wg ∧
      IsInvDomain k (contactMarkedKept B g T₀ Vg) ∧
      IsCanonical (contactMarkedKept B g T₀ Vg)
        (R.inv (contactMarkedKept B g T₀ Vg)) (restrict Vg T₁) ∧
      (⟨z,hzg⟩ : openPreimage T₁ Vg)∈
        (geoTransformAlong (contactMarkedKept B g T₀ Vg) (restrict Vg T₁)).cosupp ∧
      lowerValueL R B (lowerMarkedM B) 0 T₀ T₁ z=
        ((R.inv (contactMarkedKept B g T₀ Vg) (restrict Vg T₁) ⟨z,hzg⟩ : Λ) : WithTop Λ) ∧
      ∃Vu : Opens Y,∃hzu : T₁.proj z∈Vu,
      ∃ψ : CMfd.of (n := n) Vg ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) Vu,
      ∃ξ : CMfd.of (n := n) (openPreimage T₁ Vg) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T₁ Vu),
      Vu≤maskB B T₀ (T₁.proj z) ∧ IsTowerIso ψ (restrict Vg T₁) (restrict Vu T₁) ξ ∧
      ξ ⟨z,hzg⟩=⟨z,hzu⟩ ∧
      MarkedIdeal.pullback ψ (contactMarkedKept B
        (tangentChoice B (T₀.proj (T₁.proj z))).2 T₀ Vu)=contactMarkedKept B g T₀ Vg := by
  have hDataSave:=hData
  obtain ⟨hzW,hdomW,hcanW,_hcosW⟩:=hData
  let W:=maskB B T₀ (T₁.proj z)
  let f:=(tangentChoice B (T₀.proj (T₁.proj z))).2
  have hxf : T₀.proj (T₁.proj z)∈(tangentChoice B (T₀.proj (T₁.proj z))).1 :=
    (interior_subset hzW).1
  have hf:=StepOneCompare.tangentChoice_spec_of_mem B hxf
  have hx : T₀.proj (T₁.proj z)∈B.cosupp := by
    have hBar:=isWellFormed_barMarked B hB
    have h:=proj_mem_cosupp_of_mem_cosupp hBar.isClosedSubmanifold_N hBar.isCoherent _ hT hz
    rw [cosupp_barMarked B hB hd,BlowupTower.proj_append] at h
    exact h
  obtain ⟨V,hxV,hV⟩:=exists_tail_iso_opens (M := X) hB.isCoherent hB.isClosedSubmanifold_N
    hd hx hf hxf hg (hWg hzWg)
  have hT' : IsGeoTestTower (MaximalOrderStepOneB.stepOneMarked B.N B.ideal B.d) (T₀.append T₁):=
    StepOneRegime.isGeoTestTower_stepOneMarked_of_coeffHom B _ hT
  have hz' : z∈(geoTransformAlong (MaximalOrderStepOneB.stepOneMarked B.N B.ideal B.d) (T₀.append T₁)).cosupp := by
    rw [StepOneRegime.cosupp_geoTransformAlong_stepOneMarked]
    exact hz
  obtain ⟨Vu,Vg,hzu,hzg,ψ,ξ,hVuW,hVgWg,hIso,hFix,hrec⟩:=
    hV T₀ T₁ hT' W Wg z hzW hzWg hxV hz'
  have hmask (H) (hH : H∈(geoTransformAlong (barMarked B) T₀).E.take B.E.length)
      (y : Y) (hy : y∈Vu) : y∉H :=
    (interior_subset (hVuW hy)).2.1 H hH
  have hother (H) (hH : H∈(geoTransformAlong (barMarked B) T₀).E.take B.E.length)
      (y : Y) (hy : y∈Vg) : y∉H :=
    Set.disjoint_left.mp (hWgE H hH) (hVgWg hy)
  have hKept : MarkedIdeal.pullback ψ (contactMarkedKept B f T₀ Vu)=contactMarkedKept B g T₀ Vg := by
    change MarkedIdeal.pullback ψ (MarkedIdeal.pullback (Subtype.val : Vu → Y) _)=
      MarkedIdeal.pullback (Subtype.val : Vg → Y) _
    rw [pullback_val_restrictedCoeffHom_eq B T₀ f Vu hmask,
      pullback_val_restrictedCoeffHom_eq B T₀ g Vg hother,pullback_replicate_empty,hrec]
  have hT₀:=((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1
  have hcoh:=isCoherent_restrictedCoeff B hB.isCoherent hB.isClosedSubmanifold_N f T₀ hT₀
  obtain ⟨hdomVu,hcanVu,_⟩:=restrict_nestedOpens R hcoh hVuW hdomW T₁ hcanW
  have hdomg : IsInvDomain k (contactMarkedKept B g T₀ Vg) := by
    rw [←hKept]
    exact InvDomainTowerAlong.isInvDomain_pullback ψ hdomVu
  have hcang : IsCanonical (contactMarkedKept B g T₀ Vg)
      (R.inv (contactMarkedKept B g T₀ Vg)) (restrict Vg T₁) := by
    rw [←hKept]
    exact ResolutionInvariantExt.isCanonical_of_isTowerIso R hdomVu ψ hIso hcanVu
  have hcosg : (⟨z,hzg⟩ : openPreimage T₁ Vg)∈
      (geoTransformAlong (contactMarkedKept B g T₀ Vg) (restrict Vg T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le B hB.isClosedSubmanifold_N
      hB.isCoherent hd ⟨O,hg.isOpen⟩ hg T₀ T₁ hT Vg (fun y hy=>hWg (hVgWg hy))).2]
    exact hz
  refine ⟨Vg,hzg,hVgWg,hdomg,hcang,hcosg,?_,Vu,hzu,ψ,ξ,hVuW,hIso,hFix,hKept⟩
  exact ContactLowerValue.lowerValueL_zero_eq R B hB hd T₀ T₁ hT hg Vg
    (fun y hy=>hWg (hVgWg hy))
    (fun H hH=>Set.disjoint_left.mpr fun y hy=>hother H hH y hy)
    hdomg hcang hzg hz hDataSave

end
end Hironaka.HironakaActualAlternateContactReference
