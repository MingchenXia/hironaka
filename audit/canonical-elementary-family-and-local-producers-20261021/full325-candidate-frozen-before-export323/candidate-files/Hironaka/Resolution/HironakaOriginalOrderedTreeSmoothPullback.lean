/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalLocalPureHeadHosts
import Hironaka.Resolution.HironakaActualTowerPullbackAppend

/-!
# Genuine intrinsic smooth histories for the same actual ordered tree

Actual analytic carriers and density off a genuine closed centre support
supply all whole strict identities internally. The support is kept separate
from the recursive allowed-support index of the actual tree.
Blueprint: `hironaka-original-ordered-tree-smooth-pullback-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalOrderedTreeSmoothPullback
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  CanonicalCentres HironakaAdmissibleSequence HironakaAdmissibleCalculus RestrictEmptyTower
  HironakaOriginalCanonicalPartListResolution HironakaOriginalCanonicalOrderedResolution
  HironakaOriginalCanonicalSumSeparation HironakaOriginalLocalPureHeadHosts
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionNormalCrossings
  HironakaSmoothSubmersionCoefficientIdeals
  HironakaOriginalStoppedPrefixSmoothComparison
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y : CMfd.{u} m}

/-- Genuine canonical sum stages and literal boundary composition give the actual admissible map. -/
theorem separation_chain_admissible
    {E : List (Set X)} {A : Set X} {L : List (Set X × ℕ)}
    {T : BlowupTower X D} {Ef : List (Set D)}
    (h : CanonicalSeparationChain E A L T Ef) :
    ∀ F : Set X,CentresOver F T → IsAdmissibleBlowupSequence n X E F D T.proj Ef := by
  induction h with
  | nil => intro F _;exact .refl
  | cons T S hA hB hM hc hr hs ih =>
    intro F hover
    obtain ⟨hoverT,hoverS⟩ := (centresOver_append_iff F T S).mp hover
    have ht := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hM T hc
    have haT := isAdmissibleBlowupSequence_proj _ F T ht hoverT
    have haS := ih _ hoverS
    simpa only [BlowupTower.proj_append,sumMarkedIdeal] using IsAdmissibleBlowupSequence.comp haT haS

/-- Every real ordered tree carries actual admissibility with its entire chronological boundary. -/
theorem ordered_tree_admissible
    {E : List (Set X)} {G : Set X} {L : List (Set X × ℕ)}
    {T : BlowupTower X D} {Ef : List (Set D)}
    (h : CanonicalOrderedResolution E G L T Ef) :
    ∀ F : Set X,CentresOver F T → IsAdmissibleBlowupSequence n X E F D T.proj Ef := by
  induction h with
  | nil => intro F _;exact .refl
  | cons T₀ T₁ T hsep hhead htail ih =>
    intro F hover
    obtain ⟨hover₀,hoverRest⟩ := (centresOver_append_iff F T₀ (T₁.append T)).mp hover
    obtain ⟨hover₁,hoverT⟩ := (centresOver_append_iff (T₀.proj ⁻¹' F) T₁ T).mp hoverRest
    have ha₀ := separation_chain_admissible hsep F hover₀
    have ht := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hhead.domain T₁ hhead.canonical
    have ha₁ := isAdmissibleBlowupSequence_proj _ (T₀.proj ⁻¹' F) T₁ ht hover₁
    have haT := ih _ hoverT
    simpa only [BlowupTower.proj_append] using IsAdmissibleBlowupSequence.comp ha₀ (IsAdmissibleBlowupSequence.comp ha₁ haT)

private theorem centresOver_pullback {A C : CMfd.{u} n} {B E : CMfd.{u} m} {b : B → A}
    {Q : BlowupTower B E} {T : BlowupTower A C} {g : E → C}
    (h : IsActualTowerPullback b Q T g) (F : Set A) (hover : CentresOver F T) :
    CentresOver (b ⁻¹' F) Q := by
  induction h with
  | refl => trivial
  | @step D' D Z' Z Q T g h hg C π hπ ρ hρ ih =>
    refine ⟨ih hover.1,?_⟩
    intro z hz
    change b (Q.proj z)∈F
    rw [← h.proj_comm z]
    exact hover.2 hz

/-- Natural whole original carriers and genuine actual centre support internally
supply the intrinsic source chain on the SAME actual Cartesian pullback. -/
theorem separation_chain_smooth_pullback
    {E₀ : List (Set X)} {A : Set X} {L : List (Set X × ℕ)}
    {T : BlowupTower X D} {Ef : List (Set D)}
    (hchain : CanonicalSeparationChain E₀ A L T Ef)
    (F : Set X) (hF : IsClosed F) (hA : IsComplexAnalyticSubset (n := n) A)
    (hL : ∀ p∈L,IsComplexAnalyticSubset (n := n) p.1)
    (hdA : A ⊆ closure (A \ F)) (hdL : ∀ p∈L,p.1 ⊆ closure (p.1 \ F))
    (hover : CentresOver F T) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
      IsActualTowerPullback b Q T g ∧
      CanonicalSeparationChain (E₀.map (b ⁻¹' ·)) (b ⁻¹' A)
        (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) Q (Ef.map (g ⁻¹' ·)) ∧
      CentresOver (b ⁻¹' F) Q ∧
      IsAdmissibleBlowupSequence m Y (E₀.map (b ⁻¹' ·)) (b ⁻¹' F) C Q.proj (Ef.map (g ⁻¹' ·)) ∧
      ∀ P : Set X,P ⊆ closure (P \ F) →
        strictTransform m Q.proj (b ⁻¹' P)=g ⁻¹' strictTransform n T.proj P := by
  induction hchain generalizing m Y with
  | @nil X E₀ A =>
    have h := IsActualTowerPullback.refl hb
    refine ⟨Y,.refl,b,h,.nil,True.intro,.refl,?_⟩
    intro P hd
    let O : Opens X := ⟨Fᶜ,hF.isOpen_compl⟩
    exact IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb h O True.intro P hd
  | @cons X E₀ A B e L D Z T S hAa hBa hM hc hr Ef hs ih =>
    obtain ⟨hoverT,hoverS⟩ := (centresOver_append_iff F T S).mp hover
    obtain ⟨C₀,Q₀,g₀,hactual₀⟩ := exists_actual_tower hb T
    let M := sumMarkedIdeal A B E₀
    let N := sumMarkedIdeal (b ⁻¹' A) (b ⁻¹' B) (E₀.map (b ⁻¹' ·))
    have heq : markedPullback (m := m) b M=N := pullback_sumMarkedIdeal_eq hAa hBa E₀ hb
    have hN : IsInvDomain m N := by
      rw [← heq]
      exact original_ambient_domain_pullback hb M hM
    have hcQ : IsCanonical N ((canonicalInvariant m).inv N) Q₀ := by
      rw [← heq]
      exact IsActualTowerPullback.original_ambient_canonical hactual₀ M hM hc
    obtain ⟨htQ,hrec⟩ := IsActualTowerPullback.relative_marked_dictionary hactual₀ M hM.isWellFormed hr.1
    have hcos := IsActualTowerPullback.relative_cosupport_dictionary hactual₀ M hM.isWellFormed hr.1
    have hrQ : IsGeoResolution N Q₀ := by
      rw [← heq]
      exact ⟨htQ,by rw [hcos,hr.2,preimage_empty]⟩
    have hEQ : (geoTransformAlong N Q₀).E=(geoTransformAlong M T).E.map (g₀ ⁻¹' ·) := by
      rw [← heq]
      exact congrArg MarkedIdeal.E hrec
    have hLt : ∀ p∈L,IsComplexAnalyticSubset (n := n) p.1 :=
      fun p hp => hL p (List.mem_cons_of_mem _ hp)
    have hdLt : ∀ p∈L,p.1 ⊆ closure (p.1 \ F) :=
      fun p hp => hdL p (List.mem_cons_of_mem _ hp)
    have hA₁ := isComplexAnalyticSubset_strictTransform T.isBlowupSequence hA
    have hL₁ : ∀ p∈strictParts T L,IsComplexAnalyticSubset (n := n) p.1 := by
      intro p hp
      obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp
      exact isComplexAnalyticSubset_strictTransform T.isBlowupSequence (hLt p₀ hp₀)
    have hdA₁ := strictTransform_subset_closure_diff T.contMDiff_proj hA.isClosed hdA
    have hdL₁ : ∀ p∈strictParts T L,p.1 ⊆ closure (p.1 \ T.proj ⁻¹' F) := by
      intro p hp
      obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp
      exact strictTransform_subset_closure_diff T.contMDiff_proj (hLt p₀ hp₀).isClosed (hdLt p₀ hp₀)
    obtain ⟨C,Q,g,hactual,hchainQ,hoverQ,hadmQ,_hstrictQ⟩ :=
      ih (T.proj ⁻¹' F) (hF.preimage T.contMDiff_proj.continuous) hA₁ hL₁ hdA₁ hdL₁ hoverS hactual₀.isSubmersion
    let O : Opens X := ⟨Fᶜ,hF.isOpen_compl⟩
    have haT : CentresAvoid O T := centresAvoid_of_centresOver O disjoint_compl_left T hoverT
    have hstrict₀ (P : Set X) (hd : P ⊆ closure (P \ F)) :
        strictTransform m Q₀.proj (b ⁻¹' P)=g₀ ⁻¹' strictTransform n T.proj P :=
      IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hactual₀ O haT P hd
    have hhead := hstrict₀ A hdA
    have hparts : (strictParts T L).map (fun p => (g₀ ⁻¹' p.1,p.2+(m-n)))=
        strictParts Q₀ (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) := by
      simp only [strictParts,List.map_map]
      apply List.map_congr_left
      intro p hp
      exact Prod.ext (hstrict₀ p.1 (hdLt p hp)).symm rfl
    have hchainQ' : CanonicalSeparationChain (geoTransformAlong N Q₀).E
        (strictTransform m Q₀.proj (b ⁻¹' A))
        (strictParts Q₀ (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n))))) Q (Ef.map (g ⁻¹' ·)) := by
      rw [hEQ,hhead,← hparts]
      exact hchainQ
    have hwhole : IsActualTowerPullback b (Q₀.append Q) (T.append S) g := hactual₀.append hactual
    have hsrc : CanonicalSeparationChain (E₀.map (b ⁻¹' ·)) (b ⁻¹' A)
        (((B,e)::L).map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) (Q₀.append Q) (Ef.map (g ⁻¹' ·)) :=
      .cons Q₀ Q (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hAa)
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hb.contMDiff hBa) hN hcQ hrQ hchainQ'
    have hOver := centresOver_pullback hwhole F hover
    refine ⟨C,Q₀.append Q,g,hwhole,hsrc,hOver,separation_chain_admissible hsrc _ hOver,?_⟩
    intro P hd
    have hav : CentresAvoid O (T.append S) := centresAvoid_of_centresOver O disjoint_compl_left _ hover
    exact IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hwhole O hav P hd

private theorem partsUnion_shifted_preimage {A : Type u} {B : Type u} (f : B → A)
    (L : List (Set A × ℕ)) (r : ℕ) :
    partsUnion (L.map (fun p => (f ⁻¹' p.1,p.2+r)))=f ⁻¹' partsUnion L := by
  ext z
  simp [partsUnion]

/-- The whole actual ordered tree pulls back intrinsically using genuine
analytic/density/support data, without source compactness or a history certificate. -/
theorem ordered_tree_smooth_pullback
    {E₀ : List (Set X)} {G : Set X} {L : List (Set X × ℕ)}
    {T : BlowupTower X D} {Ef : List (Set D)}
    (htree : CanonicalOrderedResolution E₀ G L T Ef)
    (F : Set X) (hF : IsClosed F)
    (hL : ∀ p∈L,IsComplexAnalyticSubset (n := n) p.1)
    (hdL : ∀ p∈L,p.1 ⊆ closure (p.1 \ F))
    (hover : CentresOver F T) {b : Y → X}
    (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b) :
    ∃ (C : CMfd.{u} m) (Q : BlowupTower Y C) (g : C → D),
      IsActualTowerPullback b Q T g ∧
      CanonicalOrderedResolution (E₀.map (b ⁻¹' ·)) (b ⁻¹' G)
        (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))) Q (Ef.map (g ⁻¹' ·)) ∧
      CentresOver (b ⁻¹' F) Q ∧
      IsAdmissibleBlowupSequence m Y (E₀.map (b ⁻¹' ·)) (b ⁻¹' F) C Q.proj (Ef.map (g ⁻¹' ·)) ∧
      ∀ P : Set X,P ⊆ closure (P \ F) →
        strictTransform m Q.proj (b ⁻¹' P)=g ⁻¹' strictTransform n T.proj P := by
  induction htree generalizing m Y with
  | @nil X E₀ G =>
    have h := IsActualTowerPullback.refl hb
    refine ⟨Y,.refl,b,h,.nil,True.intro,.refl,?_⟩
    intro P hd
    let O : Opens X := ⟨Fᶜ,hF.isOpen_compl⟩
    exact IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb h O True.intro P hd
  | @cons X D₀ D₁ D E₀ G A d L E₁ E₂ T₀ T₁ T hsep hhead htail ih =>
    obtain ⟨hover₀,hoverRest⟩ := (centresOver_append_iff F T₀ (T₁.append T)).mp hover
    obtain ⟨hover₁,hoverT⟩ := (centresOver_append_iff (T₀.proj ⁻¹' F) T₁ T).mp hoverRest
    have hAa := hL (A,d) (List.mem_cons_self ..)
    have hdA := hdL (A,d) (List.mem_cons_self ..)
    have hLt : ∀ p∈L,IsComplexAnalyticSubset (n := n) p.1 :=
      fun p hp => hL p (List.mem_cons_of_mem _ hp)
    have hdLt : ∀ p∈L,p.1 ⊆ closure (p.1 \ F) :=
      fun p hp => hdL p (List.mem_cons_of_mem _ hp)
    obtain ⟨C₀,Q₀,g₀,hactual₀,hsepQ,_hoverQ₀,_hadmQ₀,hstrict₀⟩ :=
      separation_chain_smooth_pullback hsep F hF hAa hLt hdA hdLt hover₀ hb
    obtain ⟨C₁,Q₁,g₁,hactual₁⟩ := exists_actual_tower hactual₀.isSubmersion T₁
    obtain ⟨hheadQ,hEQ⟩ := pureHeadStage_pullback hhead hactual₀.isSubmersion hactual₁
    have hAeq := hstrict₀ A hdA
    rw [← hAeq] at hheadQ hEQ
    let F₁ := T₁.proj ⁻¹' (T₀.proj ⁻¹' F)
    let L₁ := strictParts T₁ (strictParts T₀ L)
    have hF₁ : IsClosed F₁ := (hF.preimage T₀.contMDiff_proj.continuous).preimage T₁.contMDiff_proj.continuous
    have hL₁ : ∀ p∈L₁,IsComplexAnalyticSubset (n := n) p.1 := by
      intro p hp
      obtain ⟨p₁,hp₁,rfl⟩ := List.mem_map.mp hp
      obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp₁
      exact isComplexAnalyticSubset_strictTransform T₁.isBlowupSequence
        (isComplexAnalyticSubset_strictTransform T₀.isBlowupSequence (hLt p₀ hp₀))
    have hdL₁ : ∀ p∈L₁,p.1 ⊆ closure (p.1 \ F₁) := by
      intro p hp
      obtain ⟨p₁,hp₁,rfl⟩ := List.mem_map.mp hp
      obtain ⟨p₀,hp₀,rfl⟩ := List.mem_map.mp hp₁
      exact strictTransform_subset_closure_diff T₁.contMDiff_proj
        (isClosed_closure : IsClosed (strictTransform n T₀.proj p₀.1))
        (strictTransform_subset_closure_diff T₀.contMDiff_proj (hLt p₀ hp₀).isClosed (hdLt p₀ hp₀))
    obtain ⟨C,Q,g,hactual,hTreeQ,_hoverQ,_hadmQ,_hstrictQ⟩ :=
      ih F₁ hF₁ hL₁ hdL₁ hoverT hactual₁.isSubmersion
    have hprefix := hactual₀.append hactual₁
    have hoverPrefix : CentresOver F (T₀.append T₁) :=
      (centresOver_append_iff F T₀ T₁).mpr ⟨hover₀,hover₁⟩
    let O : Opens X := ⟨Fᶜ,hF.isOpen_compl⟩
    have havPrefix := centresAvoid_of_centresOver O disjoint_compl_left (T₀.append T₁) hoverPrefix
    have hStrictPrefix (P : Set X) (hd : P ⊆ closure (P \ F)) :
        strictTransform m (Q₀.append Q₁).proj (b ⁻¹' P)=g₁ ⁻¹' strictTransform n (T₀.append T₁).proj P :=
      IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hprefix O havPrefix P hd
    have hList : L₁.map (fun p => (g₁ ⁻¹' p.1,p.2+(m-n)))=
        strictParts Q₁ (strictParts Q₀ (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n))))) := by
      simp only [L₁,strictParts,List.map_map]
      apply List.map_congr_left
      intro p hp
      apply Prod.ext
      · change g₁ ⁻¹' strictTransform n T₁.proj (strictTransform n T₀.proj p.1)=
          strictTransform m Q₁.proj (strictTransform m Q₀.proj (b ⁻¹' p.1))
        simpa only [BlowupTower.proj_append,
          StrictTransformComposition.strictTransform_comp T₀.contMDiff_proj T₁.contMDiff_proj,
          StrictTransformComposition.strictTransform_comp Q₀.contMDiff_proj Q₁.contMDiff_proj] using
          (hStrictPrefix p.1 (hdLt p hp)).symm
      · rfl
    have hG : g₁ ⁻¹' (T₁.proj ⁻¹' (T₀.proj ⁻¹' G))=
        Q₁.proj ⁻¹' (Q₀.proj ⁻¹' (b ⁻¹' G)) := by
      ext z
      change T₀.proj (T₁.proj (g₁ z))∈G ↔ b (Q₀.proj (Q₁.proj z))∈G
      have hp := hprefix.proj_comm z
      simp only [BlowupTower.proj_append,Function.comp_apply] at hp
      rw [hp]
    have hBad : g₁ ⁻¹' (T₁.proj ⁻¹' (T₀.proj ⁻¹' G) ∩ partsUnion L₁)=
        Q₁.proj ⁻¹' (Q₀.proj ⁻¹' (b ⁻¹' G)) ∩
          partsUnion (strictParts Q₁ (strictParts Q₀ (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))))) := by
      rw [preimage_inter,hG,← hList,partsUnion_shifted_preimage]
    have hTreeQ' : CanonicalOrderedResolution
        (geoTransformAlong (partMarkedIdeal (E₁.map (g₀ ⁻¹' ·)) (strictTransform m Q₀.proj (b ⁻¹' A))) Q₁).E
        (Q₁.proj ⁻¹' (Q₀.proj ⁻¹' (b ⁻¹' G)) ∩
          partsUnion (strictParts Q₁ (strictParts Q₀ (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))))))
        (strictParts Q₁ (strictParts Q₀ (L.map (fun p => (b ⁻¹' p.1,p.2+(m-n)))))) Q (E₂.map (g ⁻¹' ·)) := by
      rw [hEQ,← hBad,← hList]
      exact hTreeQ
    have hwhole : IsActualTowerPullback b (Q₀.append (Q₁.append Q)) (T₀.append (T₁.append T)) g :=
      hactual₀.append (hactual₁.append hactual)
    have hsrc : CanonicalOrderedResolution (E₀.map (b ⁻¹' ·)) (b ⁻¹' G)
        (((A,d)::L).map (fun p => (b ⁻¹' p.1,p.2+(m-n))))
        (Q₀.append (Q₁.append Q)) (E₂.map (g ⁻¹' ·)) :=
      .cons Q₀ Q₁ Q hsepQ hheadQ hTreeQ'
    have hOver := centresOver_pullback hwhole F hover
    refine ⟨C,Q₀.append (Q₁.append Q),g,hwhole,hsrc,hOver,ordered_tree_admissible hsrc _ hOver,?_⟩
    intro P hd
    have hav := centresAvoid_of_centresOver O disjoint_compl_left (T₀.append (T₁.append T)) hover
    exact IsActualTowerPullback.strictTransform_preimage_of_centresAvoid hb hwhole O hav P hd

end
end Hironaka.HironakaOriginalOrderedTreeSmoothPullback
