import Hironaka.Resolution.HironakaG1LaterContactRecursiveDomain
import Hironaka.Resolution.HironakaG1LaterContactFieldExistence
import Hironaka.Resolution.HironakaG1SeparateCarrierMemberCut

/-! The actual positive member cut of a later order companion. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1BornSelectedCompanionPhase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec GeneralValue GeneralCompare NonmonomialOrderTail StepOneValue StepOneLowerDomain BoundaryCount InvDomainMemberRestriction
  CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedGlueingLiftAlong TangentDirectionAlong
  DerivativeIdealAlong ContactEquivalenceAlong RelativePrincipalizationSpan
  HironakaG8LocalHistory HironakaG8HomStable HironakaG8ContactMax
  HironakaG1LaterSelectedNormalTangent HironakaG1LaterContactFieldExistence
  HironakaG1RecursiveMemberValueTransport HironakaG1LaterPositiveMaskContact
  HironakaG1SeparateCarrierMemberCut HironakaG1ClassReferenceContact
  HironakaG1ChosenCommonContactClassData ContactIndependenceAlong

private theorem tangent_bar_of_normalized_fields {n k : ℕ} {X : CMfd.{0} n}
    (J : MarkedIdeal n X) (hJ : IsInvDomain k J) (V : Opens X) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d V u)
    (hFields : ∀ x ∈ V, ∃ (e : ComplexChart n X) (ξ : Fin n → X → ℂ),
      IsTangentField J.N e ξ x ∧ fieldDeriv e ξ u =ᶠ[𝓝 x] fun _ => 1) :
    IsTangentDirectionAlong (barMarked J).N (barMarked J).ideal (barMarked J).d V u := by
  let A := homMarkedAlong J
  have hA : A.IsWellFormed := ⟨hJ.isWellFormed.isClosedSubmanifold_N,
    isCoherent_homMarkedAlong hJ.isWellFormed.isCoherent hJ.isWellFormed.isClosedSubmanifold_N,
    hJ.isWellFormed.isSNCDivisor, hJ.isWellFormed.isTransverse⟩
  have hAu : IsTangentDirectionAlong A.N A.ideal A.d V u := by
    refine ⟨V.isOpen, fun x hx => ?_, hu.multiplicity_one⟩
    exact iterDerivIdealAlong_mono (N := J.N)
      (le_homogenizedIdealAlong (fun _ _ hf =>
        GermIdeal.IsCoherent.holomorphicAt_mem hJ.isWellFormed.isCoherent hf) hJ.one_le_d)
      (J.d - 1) x u (hu.mem x hx)
  have hEmpty : (memberRestrict A ∅).N = J.N := by
    rw [memberRestrict_N]
    change J.N ∩ memberInter A.E ∅ = J.N
    simp [memberInter]
  have hB := selected_tangent_of_current_contact A hA hJ.one_le_d ∅ V u hAu
    (fun x hx => by rw [hEmpty]; exact hFields x hx)
  change IsTangentDirectionAlong (memberRestrict A ∅).N (barMarked J).ideal (barMarked J).d V u at hB
  rw [hEmpty] at hB
  exact hB

set_option maxHeartbeats 1500000 in
/-- On a genuine positive companion mask, select all incident inherited
slots, including the slots born before the companion was formed. The
prescribed normal zero trace identifies the carrier of the actual supported
member cut. The coefficient contact restriction has its whole local weak
class and its literal ordered boundary. -/
theorem exists_born_selected_companion_contact {n k l s : ℕ} (hn : 0 < n)
    {X : CMfd.{0} n} (J R : MarkedIdeal n X)
    (hJ : IsInvDomain k J) (hR : IsInvDomain l R) (hClass : LocWPEquiv J R)
    (hRJ : R.N ⊆ J.N) (p : X) (hpR : p ∈ R.N)
    (hl : level J (.refl : BlowupTower X X) p = s + 1)
    (hNS : ¬ IsSpecial J (.refl : BlowupTower X X) p)
    (V : Opens X) (hpV : p ∈ V) (u : X → ℂ)
    (hu : IsTangentDirectionAlong J.N J.ideal J.d V u)
    (hTrace : J.N ∩ {x | u x = 0} ∩ V = R.N ∩ V) :
    let H : BlowupTower X X := .refl
    let B := barMarked J
    ∃ W : Opens X, p ∈ W ∧ W ≤ V ∧ W ≤ maskA J H p ∧
      let K := positiveMemberOn J H p W
      let S := positiveMemberOn R H p W
      let C := withN (coeffMarkedAlong K) (K.N ∩ {z : W | u z.val = 0})
      IsInvDomain (k - 1) K ∧
      IsTangentDirectionAlong K.N K.ideal K.d univ (u ∘ (Subtype.val : W → X)) ∧
      C.N = S.N ∧ C.E = K.E ∧ C.E = S.E ∧
      C.E = (B.E.filter (fun F => decide ¬ (F ∈ origMembers J H ∧ p ∈ F))).map
        ((Subtype.val : W → X) ⁻¹' ·) ∧
      LocWPEquiv (X := CMfd.of (n := n) W) C S := by
  intro H B
  let D := barMarked R
  let I := membersThrough B.E (origMembers J H) p
  let K₀ := memberRestrict B I
  have hpU : u p = 0 := ((Set.ext_iff.mp hTrace p).mpr ⟨hpR, hpV⟩).1.2
  obtain ⟨e, ξ, hξ, hDetect⟩ := hu.multiplicity_one p hpV hpU
  have hVan : (vanishingIdeal (n := n) R.N).mem p u := by
    refine ⟨GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong
      (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hJ.isWellFormed.isCoherent hf)
      (J.d - 1) p u (hu.mem p hpV), ?_⟩
    filter_upwards [V.isOpen.mem_nhds hpV] with z hz hzR
    exact ((Set.ext_iff.mp hTrace z).mpr ⟨hzR, hz⟩).1.2
  have hEqE : J.E = R.E := hClass.wEquiv.1
  have hTR : NormalCrossings.IsTransverse n R.N B.E := by
    change NormalCrossings.IsTransverse n R.N J.E
    rw [hEqE]
    exact hR.isWellFormed.isTransverse
  have hFields₀ := exists_normalized_tangent_field_of_transverse_boundary hn
    B.E ∅ hJ.isWellFormed.isSNCDivisor hJ.isWellFormed.isTransverse hTR
    (by simp) hpR hRJ hVan hξ hDetect
  have hEmpty : J.N ∩ memberInter B.E ∅ = J.N := by simp [memberInter]
  rw [hEmpty] at hFields₀
  have hFields := exists_normalized_tangent_field_of_transverse_boundary hn
    B.E I hJ.isWellFormed.isSNCDivisor hJ.isWellFormed.isTransverse hTR
    (fun i hi => (mem_membersThrough.mp hi).2) hpR hRJ hVan hξ hDetect
  have hpM : p ∈ maskA J H p := mem_maskA J hJ.isWellFormed hJ.one_le_d hn H trivial
    (by rw [hl]; omega) hNS
  have hVnear : ∀ᶠ z in 𝓝 p, z ∈ V := V.isOpen.mem_nhds hpV
  have hMnear : ∀ᶠ z in 𝓝 p, z ∈ maskA J H p := (maskA J H p).isOpen.mem_nhds hpM
  obtain ⟨M, hM, hMo, hpM'⟩ := mem_nhds_iff.mp
    (hFields₀.and (hFields.and (hVnear.and hMnear)))
  let W : Opens X := ⟨M, hMo⟩
  have hWV : W ≤ V := fun _ hx => (hM hx).2.2.1
  have hWM : W ≤ maskA J H p := fun _ hx => (hM hx).2.2.2
  have huW : IsTangentDirectionAlong J.N J.ideal J.d W u :=
    ⟨W.isOpen, fun x hx => hu.mem x (hWV hx), fun x hx => hu.multiplicity_one x (hWV hx)⟩
  have hBu := tangent_bar_of_normalized_fields J hJ W u huW (fun _ hx => (hM hx).1)
  have hB : B.IsWellFormed := isWellFormed_barMarked J hJ.isWellFormed
  have hBD : IsInvDomain k B := HironakaCoherentTransformExtension.isInvDomain_barMarked J hJ
  have hK₀u := selected_tangent_of_current_contact B hB hBD.one_le_d I W u hBu
    (fun _ hx => (hM hx).2.1)
  have hK₀ := isWellFormed_memberRestrict hn hB I
  let A := CMfd.of (n := n) W
  let K := positiveMemberOn J H p W
  let S := positiveMemberOn R H p W
  let C := withN (coeffMarkedAlong K) (K.N ∩ {z : W | u z.val = 0})
  have hK : IsInvDomain (k - 1) K :=
    positive_member_domain_on_subwindow hn J hJ H trivial p hl W hWM
  have hKu : IsTangentDirectionAlong K.N K.ideal K.d univ (u ∘ (Subtype.val : W → X)) :=
    isTangentDirectionAlong_pullback_val W
      (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK₀.isCoherent hf) hK₀u
  have hKS : LocWPEquiv (X := A) K S :=
    member_stage_local_of_local hn J R hJ hR hClass H trivial W p
  have hCN : IsClosedSubmanifold (X := A) n C.N := by
    change IsClosedSubmanifold (X := A) n (K.N ∩ {z : W | u z.val = 0})
    simpa only [Set.inter_univ, Function.comp_apply] using
      isClosedSubmanifold_contact_along hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hKu
  have hContact : MaxContact K C.N := by
    change MaxContact K (K.N ∩ {z : W | u z.val = 0})
    simpa only [Set.inter_univ, Function.comp_apply] using maxContact_base K hK.isWellFormed.isCoherent hKu
  have hKC : LocWPEquiv (X := A) K C :=
    locWPEquiv_of_reference_maxContact K K
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d
      hK.isWellFormed.isClosedSubmanifold_N hK.isWellFormed.isCoherent hK.one_le_d
      rfl (LocEquiv.refl _ K) C.N hCN (fun _ hz => hz.1) hContact
  have hOrig : origMembers J H = origMembers R H :=
    HironakaG8MemberLoci.origMembers_eq_of_E_eq hEqE H
  have hOld : ∀ F ∈ origMembers J H, F ∈ B.E := fun _ h => List.mem_of_mem_take h
  have hOldR : ∀ F ∈ origMembers R H, F ∈ D.E := fun _ h => List.mem_of_mem_take h
  have hN : C.N = S.N := by
    change ((Subtype.val : W → X) ⁻¹' (J.N ∩ memberInter B.E I)) ∩ {z : W | u z.val = 0} =
      (Subtype.val : W → X) ⁻¹' (R.N ∩ memberInter D.E (membersThrough D.E (origMembers R H) p))
    unfold I
    rw [memberInter_membersThrough hOld p, memberInter_membersThrough hOldR p, hOrig]
    ext z
    have hzV : (z : X) ∈ V := hWV z.property
    have h := Set.ext_iff.mp hTrace z.val
    exact ⟨fun hz => ⟨(h.mp ⟨⟨hz.1.1, hz.2⟩, hzV⟩).1, hz.1.2⟩,
      fun hz => ⟨⟨hRJ hz.1, hz.2⟩, (h.mpr ⟨hz.1, hzV⟩).1.2⟩⟩
  have hSub : C.E = (B.E.filter (fun F => decide ¬ (F ∈ origMembers J H ∧ p ∈ F))).map
      ((Subtype.val : W → X) ⁻¹' ·) := by
    change (memberRestrict B I).E.map _ = _
    rw [InvDomainRebase.memberRestrict_membersThrough_E]
  exact ⟨W, hpM', hWV, hWM, hK, hKu, hN, rfl, hKS.wEquiv.1, hSub, hKC.symm.trans hKS⟩

set_option maxHeartbeats 800000 in
/-- Specialization to the actual order companion on its literal order mask.
Its domain is produced by the tested lower prefix and positive order.
The retained slots of that companion are the original slots of the next
positive Step One selection. -/
theorem exists_born_selected_contact_of_actual_compAt {n k l s o : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (L : MarkedIdeal n X) (hL : IsInvDomain k L)
    (T : BlowupTower X Y) (hT : IsGeoTestTower L T) (ho : 1 ≤ o) :
    let O := ordMask (geoTransformAlong L T) o
    let A := CMfd.of (n := n) O
    let J := compAt L o T
    let H : BlowupTower A A := .refl
    ∀ (R : MarkedIdeal n A), IsInvDomain l R → LocWPEquiv J R → R.N ⊆ J.N →
    ∀ (p : A), p ∈ R.N →
    level J H p = s + 1 → (¬ IsSpecial J H p) →
    ∀ (V : Opens A), p ∈ V → ∀ (u : A → ℂ),
    IsTangentDirectionAlong J.N J.ideal J.d V u →
    J.N ∩ {x | u x = 0} ∩ V = R.N ∩ V →
    ∃ W : Opens A, p ∈ W ∧ W ≤ V ∧ W ≤ maskA J H p ∧
      let K := positiveMemberOn J H p W
      let S := positiveMemberOn R H p W
      let C := withN (coeffMarkedAlong K) (K.N ∩ {z : W | u z.val = 0})
      IsInvDomain (k - 1) K ∧
      IsTangentDirectionAlong K.N K.ideal K.d univ (u ∘ (Subtype.val : W → A)) ∧
      C.N = S.N ∧ C.E = K.E ∧ C.E = S.E ∧
      C.E = ((barMarked J).E.filter (fun F => decide ¬ (F ∈ origMembers J H ∧ p ∈ F))).map
        ((Subtype.val : W → A) ⁻¹' ·) ∧
      LocWPEquiv (X := CMfd.of (n := n) W) C S := by
  intro O A J H R hR hClass hRJ p hp hl hNS V hpV u hu hTrace
  have hStage := InvDomainTowerAlong.isInvDomain_geoTransformAlong hL T hT
  have hJ : IsInvDomain k J := isInvDomain_compAt hn ho T hStage
  exact exists_born_selected_companion_contact hn J R hJ hR hClass hRJ p hp hl hNS V hpV u hu hTrace

end Hironaka.HironakaG1BornSelectedCompanionPhase
