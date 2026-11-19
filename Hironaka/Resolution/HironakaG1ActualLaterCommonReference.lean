import Hironaka.Resolution.HironakaG1LaterOrderMaskNonfactor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ActualLaterCommonReference
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain GeneralValue GeneralCompare
  NonmonomialOrderTail InvDomainMemberRestriction InvDomainTowerAlong BoundaryCount
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalContact HironakaActualSectionBoundaryGeometry
  HironakaG1PositiveNormalPhase HironakaG1LaterPositiveMaskContact HironakaG1LaterSelectedActualOrder
  HironakaG1RecursiveMemberValueTransport HironakaG1ActualLaterCompanionTangent
  HironakaG1LaterOrderMaskSupportedLocal HironakaG1LaterOrderMaskNonfactor
  HironakaG8LocalHistory HironakaG8LocalRestrictEquiv HironakaG8LocalContactStage
  ContactRepresentative MarkedIdealOperationsAlong.MarkedIdeal GermIdealPullbackCalculus
  RelativePrincipalizationSpan HironakaActualOpenZeroSectionDifferentials

private theorem domain_shrink {n k : ℕ} {X : CMfd.{0} n}
    {R : MarkedIdeal n X} (hR : R.ideal.IsCoherent) {V W : Opens X} (hWV : W ≤ V)
    (hV : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : V → X) R)) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → X) R) := by
  have h := isInvDomain_pullback_val (MaxLocusLocal.nestedOpens V W) hV
  have h' := isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n) hWV).symm h
  rwa [MaxLocusLocal.pullback_symm_nestedOpensDiffeo hR hWV] at h'

private theorem comparison_shrink {n : ℕ} {X : CMfd.{0} n}
    {L J : MarkedIdeal n X} (hL : L.ideal.IsCoherent) (hJ : J.ideal.IsCoherent)
    {V W : Opens X} (hWV : W ≤ V)
    (h : RestrictEquiv (MarkedIdeal.pullback (Subtype.val : V → X) L)
      (MarkedIdeal.pullback (Subtype.val : V → X) J)) :
    RestrictEquiv (MarkedIdeal.pullback (Subtype.val : W → X) L)
      (MarkedIdeal.pullback (Subtype.val : W → X) J) := by
  let A := CMfd.of (n := n) V
  let B := CMfd.of (n := n) (MaxLocusLocal.nestedOpens V W)
  have hv : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : A → X) := contMDiff_subtype_val
  have hw : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : B → A) := contMDiff_subtype_val
  have h' := restrictEquiv_pullback_val (MaxLocusLocal.nestedOpens V W) h
    (isCoherent_pullback hv hL) (isCoherent_pullback hv hJ)
  let e := (MaxLocusLocal.nestedOpensDiffeo (n := n) hWV).symm
  have he := restrictEquiv_pullback_map e.contMDiff h'
    (isCoherent_pullback hw (isCoherent_pullback hv hL))
    (isCoherent_pullback hw (isCoherent_pullback hv hJ))
    (P' := MarkedIdeal.pullback e (MarkedIdeal.pullback (Subtype.val : B → A)
      (MarkedIdeal.pullback (Subtype.val : A → X) L)))
    (Q' := MarkedIdeal.pullback e (MarkedIdeal.pullback (Subtype.val : B → A)
      (MarkedIdeal.pullback (Subtype.val : A → X) J))) rfl rfl
    (congrArg (List.map (e ⁻¹' ·)) h'.E_eq) rfl rfl rfl rfl
  rwa [MaxLocusLocal.pullback_symm_nestedOpensDiffeo hL hWV,
    MaxLocusLocal.pullback_symm_nestedOpensDiffeo hJ hWV] at he

set_option maxHeartbeats 1900000 in
/-- The actual positive lower companion and the literal supported
reference share an open neighborhood of the split anchor on the exact
order mask. On it the reference has its ordinary domain and the local
weak class of the companion with its ordered boundary. -/
theorem exists_actual_later_common_supported_reference {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let M := maskA Sec H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let B := CMfd.of (n := n + 1) C
    let J := compAt L L.d (.refl : BlowupTower A A)
    let R := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) (positiveMemberOn Sec H p O)
    let V₀ := MaxLocusLocal.nestedOpens C (MaxLocusLocal.nestedOpens O M)
    (¬ IsSpecial Sec H p) →
    ∃ (a : C) (W : Opens B), a.val.val = p ∧ a ∈ W ∧ W ≤ V₀ ∧
      let D := CMfd.of (n := n + 1) W
      let Jw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) J
      let Rw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) R
      IsInvDomain (k + 1) Jw ∧ IsInvDomain k Rw ∧ LocWPEquiv (X := D) Jw Rw ∧
      Jw.d = J.d ∧ Jw.E = J.E.map ((Subtype.val : W → B) ⁻¹' ·) := by
  intro X P Sec r H S p O M A L C B J R V₀ hNSS
  let F := invFamily (Nat.succ_pos n) (k + 1)
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  obtain ⟨hBarTest, hTest, hCos⟩ :=
    Seq.StepOneBridge.isGeoTestTower_of_isCanonical F P hP hMax (Nat.succ_pos n) T hCan
  obtain ⟨hReg, hpBar⟩ :=
    stepRegime_and_mem_cosupp_head P hP.isWellFormed T hBarTest (hCos.symm ▸ hy) hNS
  rw [hLevel] at hReg hpBar
  have hHeadTest := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
  obtain ⟨N, _, hpN, hNO, hN, _, _, hFactor, _⟩ :=
    exists_later_selected_actual_normal_order Q hQ H hHeadTest p hpBar hReg.1 hReg.2
  obtain ⟨hp, hq, _, _, _, _, hJ, _, _⟩ :=
    exists_actual_later_initial_order_companion_tangent Q hQ T hCan y hy hLevel hNS
  obtain ⟨_, _, _, _, _, _, hL, _, _⟩ :=
    original_normal_positive_phase_head Q hQ T hCan y hy hLevel hNS
  obtain ⟨hV₀, hRv, _⟩ :=
    later_supported_reference_on_exact_order_window Q hQ H hHeadTest p hReg.1 hNSS
  let a : C := ⟨⟨p, hp⟩, hq⟩
  let B₀ := geoTransformAlong (barMarked P) H
  let K := memberRestrict B₀ (membersThrough B₀.E (origMembers P H) p)
  have hB₀ : B₀.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked P hP.isWellFormed) H
      ((isGeoTestTower_iff_head_tail (barMarked P) T r).mp hBarTest).1
  have hK : K.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hB₀ _
  have hCmp := initial_companion_restrictEquiv_of_ambient_nonfactor
    (Nat.succ_pos n) K hK.isCoherent hNO hL hN hFactor
  let V₁ := MaxLocusLocal.nestedOpens C (MaxLocusLocal.nestedOpens O N)
  let W : Opens B := V₀ ⊓ V₁
  have haW : a ∈ W := ⟨hV₀ a rfl, hpN⟩
  let Lc := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) L
  have hLc : IsInvDomain (k + 1) Lc := isInvDomain_pullback_val C hL
  have hLR : LocWPEquiv (X := A) L (positiveMemberOn Sec H p O) :=
    (positive_lower_section_class Q hQ H hHeadTest p).1
  have hRaj := ((hLR.restrict C).restrict W)
  have hRcoh : R.ideal.IsCoherent := by
    let BS := geoTransformAlong (barMarked Sec) H
    have hSec : IsInvDomain (k + 1) Sec := section_projected_domain (k + 1) Q.N Q.E Q.ideal Q.d hQ
    have hST := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hHeadTest
    have hBST := ((HironakaG8HomStable.bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hST
    have hBS : BS.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (StepOneLowerDomain.isWellFormed_barMarked Sec hSec.isWellFormed) H hBST
    have hKS := isWellFormed_memberRestrict (Nat.succ_pos n) hBS
      (membersThrough BS.E (origMembers Sec H) p)
    exact (MarkedIdealRestrictOpen.IsWellFormed.pullback_val
      (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hKS O) C).isCoherent
  have hCmpW := comparison_shrink hLc.isWellFormed.isCoherent hJ.isWellFormed.isCoherent
    (show W ≤ V₁ from inf_le_right) hCmp
  have hLw := isInvDomain_pullback_val W hLc
  have hJw := isInvDomain_pullback_val W hJ
  have hRw := domain_shrink hRcoh (show W ≤ V₀ from inf_le_left) hRv
  exact ⟨a, W, rfl, haW, inf_le_left, hJw, hRw,
    (locWPEquiv_of_restrictEquiv hLw hJw hCmpW).symm.trans hRaj, rfl, rfl⟩

end
end Hironaka.HironakaG1ActualLaterCommonReference
