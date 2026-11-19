import Hironaka.Invariant.StepOneCanonicalTail
import Hironaka.Invariant.MemberRestrictAdmissible
import Hironaka.Resolution.HironakaStageCenters

/-! Actual positive old-count cuts derive the SAME fixed lower tests on
noncanonical parent histories. The whole lower stratum, genuinely smaller
carrier and exact common born suffix are outputs. This is a native core
presentation transform layer, not a complete recursive CORE value law. -/
set_option autoImplicit false
open Set Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualPositiveCoreCountPresentation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedIdealAlong
  StepOneValue StepOneValueMasked StepOneLowerDomain StepOneMaskTower
  StepOneCompare StepOneCanonicalTail MemberRestrictAdmissible MemberInterTowerAlong
  HironakaStageCenters
open ResolutionInvariantSpec (IsInvDomain)

variable {n k : ℕ} {X Y₀ : CMfd.{u} n}

/-- Geometric every-prefix old-count cuts DERIVE lower member testness;
selected-member containment and lower tests are not caller hypotheses. -/
theorem actual_positive_count_lower_tests
    (hn : 0<n) (J : MarkedIdeal n X) (hJ : J.IsWellFormed)
    (T₀ : BlowupTower X Y₀) (s : ℕ) (a : Y₀)
    (hLevel : level J T₀ a=s+1) (hMask : a∈lowerMask J (s+1) T₀ a) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower Y₀ Y),
      IsGeoTestTower (barMarked J) (T₀.append T) →
      StageCentres (fun S C=>∀c∈C,s+1≤level J (T₀.append S) c) T →
        IsGeoTestTower (lowerMarked J (s+1) T₀ a) (restrict (lowerMask J (s+1) T₀ a) T)
  | _, .refl, _, _ => trivial
  | _, .step S C π hπ, hT, hCuts => by
      have hTests : IsGeoTestTower (barMarked J) (.step (T₀.append S) C π hπ):=hT
      have ih:=actual_positive_count_lower_tests hn J hJ T₀ s a hLevel hMask S hTests.1 hCuts.1
      have hCurrent:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
        (isWellFormed_barMarked J hJ) (T₀.append S) hTests.1
      have hParent : (MarkedIdeal.pullback
          (Subtype.val : openPreimage S (lowerMask J (s+1) T₀ a)→_)
          (geoTransformAlong (barMarked J) (T₀.append S))).IsAdmissibleCentre
            ((Subtype.val : openPreimage S (lowerMask J (s+1) T₀ a)→_) ⁻¹' C) :=
        IsAdmissibleCentre.pullback_val
          (fun _ _ hg=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
            hCurrent.isCoherent hg) hTests.2 _
      refine ⟨ih,?_⟩
      apply (isAdmissibleCentre_lowerMarked_succ_iff J hJ hn T₀ S hTests.1 hMask ih _).mpr
      refine ⟨hParent,?_⟩
      intro c hc
      have hClosed : ∀H∈J.E,IsClosed H:=fun H hH=>hJ.isSNCDivisor.1 H hH
      have hUpper:=level_le_of_mem_maskA J hClosed T₀ S (y₀:=a) c.2
      have hLower : level J T₀ a≤level J (T₀.append S) c:=by
        rw [hLevel]
        exact hCuts.2 c hc
      exact (level_eq_iff_of_mem_maskA J hClosed T₀ S c.2).mp (hUpper.antisymm hLower)

private theorem same_born_suffix {A : CMfd.{u} n} (L M : MarkedIdeal n A) :
    ∀ {B : CMfd.{u} n} (T : BlowupTower A B),
      (geoTransformAlong L T).E.drop L.E.length=(geoTransformAlong M T).E.drop M.E.length
  | _, .refl => by simp
  | _, .step T C π hπ => by
      rw [drop_E_geoTransformAlong_step,drop_E_geoTransformAlong_step,same_born_suffix L M T]

/-- Original maximal-order geometry selects a native smaller lower model
BEFORE all future parent histories; geometric count-cut centres produce
its tests, ENTIRE transformed stratum and exact SAME chronological births. -/
theorem actual_positive_count_whole_presentation
    (hn : 0<n) (J : MarkedIdeal n X) (hJ : IsInvDomain (k+1) J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d)
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked J) T₀)
    (s : ℕ) (a : Y₀) (ha : a∈(geoTransformAlong (barMarked J) T₀).cosupp)
    (hLevel : level J T₀ a=s+1) (hNotSpecial : ¬IsSpecial J T₀ a) :
    let W:=lowerMask J (s+1) T₀ a
    let L:=lowerMarked J (s+1) T₀ a
    a∈W ∧ IsInvDomain k L ∧
      ∀ {Y : CMfd.{u} n} (T : BlowupTower Y₀ Y),
        IsGeoTestTower (barMarked J) (T₀.append T) →
        StageCentres (fun S C=>∀c∈C,s+1≤level J (T₀.append S) c) T →
          IsGeoTestTower L (restrict W T) ∧
          IsInvDomain k (geoTransformAlong L (restrict W T)) ∧
          (geoTransformAlong L (restrict W T)).cosupp=
            (Subtype.val : openPreimage T W→Y) ⁻¹'
              {z | z∈(geoTransformAlong (barMarked J) (T₀.append T)).cosupp ∧
                level J (T₀.append T) z=s+1} ∧
          (geoTransformAlong L (restrict W T)).E.drop L.E.length=
            ((geoTransformAlong (barMarked J) (T₀.append T)).E.map
              (fun H=>(Subtype.val : openPreimage T W→Y) ⁻¹' H)).drop
                (geoTransformAlong (barMarked J) T₀).E.length := by
  dsimp only
  have hReg : stepRegime J (s+1) T₀ a:=⟨hLevel,hNotSpecial⟩
  obtain ⟨hMask,hDomain⟩:=mem_lowerMask_and_isInvDomain_M J hJ.isWellFormed hJ.one_le_d
    hn hMax hJ.dimLE T₀ hT₀ ha hReg
  have hL : IsInvDomain k (lowerMarked J (s+1) T₀ a):=by
    simpa only [lowerMarkedM_succ,Nat.add_sub_cancel] using hDomain
  refine ⟨hMask,hL,?_⟩
  intro Y T hT hCuts
  let W:=lowerMask J (s+1) T₀ a
  let L:=lowerMarked J (s+1) T₀ a
  have hTL : IsGeoTestTower L (restrict W T):=
    actual_positive_count_lower_tests hn J hJ.isWellFormed T₀ s a hLevel hMask T hT hCuts
  refine ⟨hTL,InvDomainTowerAlong.isInvDomain_geoTransformAlong hL (restrict W T) hTL,?_,?_⟩
  · ext p
    exact mem_cosupp_lowerMarkedM_iff J hJ.isWellFormed hJ.one_le_d hn hMax
      T₀ T hT ha hLevel hMask hTL p
  · let M:=geoTransformAlong (barMarked J) T₀
    let A:=MarkedIdeal.pullback (Subtype.val : W→Y₀) M
    have hTail:=((isGeoTestTower_append_iff (barMarked J) T₀ T).mp hT).2
    have hM:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (isWellFormed_barMarked J hJ.isWellFormed) T₀ hT₀
    have hTransform : geoTransformAlong A (restrict W T)=
        MarkedIdeal.pullback (Subtype.val : openPreimage T W→Y)
          (geoTransformAlong (barMarked J) (T₀.append T)) := by
      rw [geoTransformAlong_restrict W hM.isClosedSubmanifold_N hM.isCoherent T hTail]
      rw [geoTransformAlong_append]
    have hBorn:=same_born_suffix L A (restrict W T)
    rw [hTransform] at hBorn
    simpa only [A,M,MarkedIdeal.pullback,List.length_map] using hBorn

end
end Hironaka.HironakaActualPositiveCoreCountPresentation
