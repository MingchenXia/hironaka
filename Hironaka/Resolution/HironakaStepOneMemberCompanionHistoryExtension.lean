/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneMemberLowerOrderPredicates

/-!
# Actual member companion histories and entire controlled extensions

True member prefix cosupports and all natural order histories yield an actual
analytic zero-dimensional curve exception fixing every OrdRegime run. Original
literal masked lower runs equal the whole candidate runs. Genuine parent test
geometry supplies the same true carrier and boundary for actual companionOf
and barMarked; actual coherent colon and strict accumulation supply their whole
nonzero controlled transforms without candidate centre containment or testness.
The entire generated ideals, carrier, boundary and mark restrict exactly to the
original literal masked prefix ideals and actual compAt order mask. Original
constructed General3 canonical inputs internally supply all history and domain
inputs. Deeper General2 value descent, level-zero contact and whole General3/G3
remain open.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneMemberCompanionHistoryExtension
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  HironakaStepOneMemberLowerOrderPredicates HironakaCoherentTransformExtension
  InvDomainMemberRestriction NonmonomialOrderLocal MonomialPartAlong
  AnalyticDimensionBasics GlobalComponents HironakaCurveAnalyticPredicates
  NormalCrossings GermIdealOrder HomogenizedIdealAlong StepOneValue StepOneLowerDomain
  StepOneRegime NonmonomialOrderRegime CompanionRebase InvDomainCompanion
  MarkedIdealRestrictOpen CodimOneSupportAlong CoefficientIdealRestriction
  CompanionReductionAlong MarkedIdealBiholomorphism HironakaDimensionTwoStepOneAnalyticSuperlevels ContactStageKept
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

def memberPrefixCosupportPredicate (m : MarkedIdeal n X) (S : Finset (Fin m.E.length))
    (T : BlowupTower X Y) (i : ℕ) : Set Y :=
  (tail T i).proj ⁻¹' (geoTransformAlong (memberRemainderMarked m S) (head T i)).cosupp

theorem isComplexAnalyticSubset_memberPrefixCosupportPredicate (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (i : ℕ) :
    IsComplexAnalyticSubset (n := n) (memberPrefixCosupportPredicate m S T i) := by
  have ht := (isGeoTestTower_iff_head_tail m T i).mp hT
  have hd := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS (head T i) ht.1
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (tail T i).contMDiff_proj
    (isComplexAnalyticSubset_cosupport_along hd.isWellFormed.isCoherent hd.isWellFormed.isClosedSubmanifold_N hd.one_le_d)

theorem regimeRun_memberRemainder_restrict (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (U : Opens X) (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (q : ℕ) (z : openPreimage T U) :
    regimeRun (OrdRegime (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S)) q) (restrict U T) z =
      regimeRun (OrdRegime (memberRemainderMarked m S) q) T z := by
  apply regimeRun_restrict_of U (OrdRegime (memberRemainderMarked m S) q) _
    (fun T => IsGeoTestTower m T)
    (fun T C π hπ hT => ((isGeoTestTower_step_iff m T C π hπ).mp hT).1) _ T hT z
  intro V R hR p
  have hd := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS R hR
  change p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S)) (restrict U R)).cosupp ∧
    nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) (memberRemainderMarked m S)) (restrict U R)) p = q ↔ _
  rw [geoTransformAlong_restrict_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS U R hR,
    cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hd.isWellFormed.isCoherent hg),
    nmOrd_pullback_val hn hd.isWellFormed hd.isNonzeroAlongAt (openPreimage R U) p]
  rfl

theorem exists_analytic_dimzero_member_all_order_run_history (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdim : DimLE (n := n) Z 1)
    (hsub : Z ⊆ (geoTransformAlong (memberRemainderMarked m S) T).N) :
    ∃ E : Set Y, IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ Z ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ x ∈ B \ E, ∀ y ∈ B \ E,
        (∀ q, regimeRun (OrdRegime (memberRemainderMarked m S) q) T x =
          regimeRun (OrdRegime (memberRemainderMarked m S) q) T y) ∧
        regimeRun (OrdRegime (memberRemainderMarked m S)
          (nmOrd (geoTransformAlong (memberRemainderMarked m S) T) x)) T x =
        regimeRun (OrdRegime (memberRemainderMarked m S)
          (nmOrd (geoTransformAlong (memberRemainderMarked m S) T) y)) T y := by
  obtain ⟨Eo, hEo, hdEo, hEoZ, ho⟩ := exists_analytic_dimzero_member_order_history_exception hn m h S hS T hT hZ hdim hsub
  let P : Fin (T.length+1) → Set Y := fun i => memberPrefixCosupportPredicate m S T i
  have hP : ∀ i, IsComplexAnalyticSubset (n := n) (P i) :=
    fun i => isComplexAnalyticSubset_memberPrefixCosupportPredicate hn m h S hS T hT i
  obtain ⟨Ec, hEc, hdEc, hEcZ, hc⟩ := exists_analytic_dimzero_predicate_exception hZ hdim P hP
  obtain ⟨hE, hdE⟩ := analytic_dimzero_union hEo hdEo hEc hdEc
  refine ⟨Eo ∪ Ec, hE, hdE, union_subset hEoZ hEcZ, ?_⟩
  intro B hB x hx y hy
  have hxo : x ∈ B \ Eo := ⟨hx.1, fun hh => hx.2 (Or.inl hh)⟩
  have hyo : y ∈ B \ Eo := ⟨hy.1, fun hh => hy.2 (Or.inl hh)⟩
  have hxc : x ∈ B \ Ec := ⟨hx.1, fun hh => hx.2 (Or.inr hh)⟩
  have hyc : y ∈ B \ Ec := ⟨hy.1, fun hh => hy.2 (Or.inr hh)⟩
  have hruns : ∀ q, regimeRun (OrdRegime (memberRemainderMarked m S) q) T x =
      regimeRun (OrdRegime (memberRemainderMarked m S) q) T y := by
    intro q
    apply regimeRun_eq_of_head_predicates
    intro r hr
    let i : Fin (T.length+1) := ⟨r, by omega⟩
    have hcs : x ∈ P i ↔ y ∈ P i :=
      (hc B hB x hxc i).trans (hc B hB y hyc i).symm
    have heq := (ho B hB x hxo y hyo i).1
    change (_ ∧ _ = q) ↔ (_ ∧ _ = q)
    change (_ ↔ _) at hcs
    rw [heq]
    exact and_congr hcs Iff.rfl
  have hfinal := (ho B hB x hxo y hyo ⟨0, by omega⟩).1
  have hfinal' : nmOrd (geoTransformAlong (memberRemainderMarked m S) T) x =
      nmOrd (geoTransformAlong (memberRemainderMarked m S) T) y := by
    cases T <;> exact hfinal
  refine ⟨hruns, ?_⟩
  rw [hfinal']
  exact hruns _

private theorem domain_same_member_geometry {k : ℕ}
    (m K J : MarkedIdeal n X) (hJ : IsInvDomain k J) (hN : J.N = K.N) (hE : J.E = K.E)
    (hmodel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V), IsGeoTestTower m R → IsInvDomain k (geoTransformAlong K R)) :
    ∀ {V : CMfd.{u} n} (R : BlowupTower X V), IsGeoTestTower m R → IsInvDomain k (geoTransformAlong J R)
  | _, .refl, _ => hJ
  | _, .step R C π hπ, hR => by
    obtain ⟨hprev, _⟩ := (isGeoTestTower_step_iff m R C π hπ).mp hR
    have hdprev := domain_same_member_geometry m K J hJ hN hE hmodel R hprev
    have hdmodel := hmodel (.step R C π hπ) hR
    have hNafter := geoTransformAlong_N_eq_of_N_eq hN (.step R C π hπ)
    have hEafter := geoTransformAlong_E_eq_of_E_eq hE (.step R C π hπ)
    have hSM : IsClosedSubmanifold n ((geoTransformAlong J R).geoTransform C π).N := by
      change IsClosedSubmanifold n (geoTransformAlong J (.step R C π hπ)).N
      rw [hNafter]
      exact hdmodel.isWellFormed.isClosedSubmanifold_N
    refine ⟨⟨hSM, isCoherent_geoTransform_ideal_of_smooth_strict _ hdprev.isWellFormed.isCoherent hπ hSM, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hEafter]
      exact hdmodel.isWellFormed.isSNCDivisor
    · rw [hNafter, hEafter]
      exact hdmodel.isWellFormed.isTransverse
    · rw [hNafter]
      exact hdmodel.dimLE
    · rw [d_geoTransformAlong]
      exact hJ.one_le_d
    · exact isNonzeroAlongAt_geoTransform_of_smooth_strict _ hdprev.isWellFormed.isClosedSubmanifold_N
        hdprev.isWellFormed.isCoherent hπ hSM hdprev.isNonzeroAlongAt

private theorem restrict_same_member_geometry {k : ℕ}
    (m K J : MarkedIdeal n X) (hJ : IsInvDomain k J) (hN : J.N = K.N) (hE : J.E = K.E)
    (hmodel : ∀ {V : CMfd.{u} n} (R : BlowupTower X V), IsGeoTestTower m R → IsInvDomain k (geoTransformAlong K R))
    (U : Opens X) :
    ∀ {V : CMfd.{u} n} (R : BlowupTower X V), IsGeoTestTower m R →
      geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) J) (restrict U R) =
        MarkedIdeal.pullback (Subtype.val : openPreimage R U → V) (geoTransformAlong J R)
  | _, .refl, _ => rfl
  | _, .step R C π hπ, hR => by
    obtain ⟨hprev, _⟩ := (isGeoTestTower_step_iff m R C π hπ).mp hR
    have hdprev := domain_same_member_geometry m K J hJ hN hE hmodel R hprev
    have hdafter := domain_same_member_geometry m K J hJ hN hE hmodel (.step R C π hπ) hR
    have ih := restrict_same_member_geometry m K J hJ hN hE hmodel U R hprev
    change (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) J) (restrict U R)).geoTransform
      ((Subtype.val : openPreimage R U → _) ⁻¹' C) _ = _
    rw [ih]
    exact geoTransform_pullback_val hdprev.isWellFormed.isCoherent hπ hdafter.isWellFormed.isCoherent (openPreimage R U) _

def memberPrefixCompanion (m : MarkedIdeal n X) (S : Finset (Fin m.E.length))
    {V : CMfd.{u} n} (H : BlowupTower X V) (q : ℕ) : MarkedIdeal n V :=
  companionOf n (geoTransformAlong (memberRemainderMarked m S) H) q

def memberPrefixCoefficientCompanion (m : MarkedIdeal n X) (S : Finset (Fin m.E.length))
    {V : CMfd.{u} n} (H : BlowupTower X V) (q : ℕ) : MarkedIdeal n V :=
  barMarked (memberPrefixCompanion m S H q)

private theorem member_prefix_model_domain (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    {V : CMfd.{u} n} (H : BlowupTower X V) (hH : IsGeoTestTower m H)
    {W : CMfd.{u} n} (R : BlowupTower V W) (hR : IsGeoTestTower (geoTransformAlong m H) R) :
    IsInvDomain 2 (geoTransformAlong (geoTransformAlong (memberRemainderMarked m S) H) R) := by
  have hfull := (isGeoTestTower_append_iff m H R).mpr ⟨hH, hR⟩
  have hd := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS (H.append R) hfull
  rwa [geoTransformAlong_append] at hd

theorem member_prefix_companion_entire_domains (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    {V : CMfd.{u} n} (H : BlowupTower X V) (hH : IsGeoTestTower m H)
    (R : BlowupTower V Y) (hR : IsGeoTestTower (geoTransformAlong m H) R)
    (q : ℕ) (hq : 1 ≤ q) :
    IsInvDomain 2 (geoTransformAlong (memberPrefixCompanion m S H q) R) ∧
      IsInvDomain 2 (geoTransformAlong (memberPrefixCoefficientCompanion m S H q) R) := by
  let I := geoTransformAlong (memberRemainderMarked m S) H
  let C := memberPrefixCompanion m S H q
  let B := memberPrefixCoefficientCompanion m S H q
  have hdI := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS H hH
  have hdC : IsInvDomain 2 C := isInvDomain_companionAlong hn hdI hq
  have hdB : IsInvDomain 2 B := isInvDomain_barMarked C hdC
  have hCN : C.N = I.N := by simp only [C, I, memberPrefixCompanion, companionOf, companionAlong_N]
  have hCE : C.E = I.E := by simp only [C, I, memberPrefixCompanion, companionOf, companionAlong_E]
  have hBN : B.N = I.N := by simp only [B, memberPrefixCoefficientCompanion, barMarked_N]; exact hCN
  have hBE : B.E = I.E := by simp only [B, memberPrefixCoefficientCompanion, barMarked_E]; exact hCE
  have hmodel : ∀ {W : CMfd.{u} n} (T : BlowupTower V W),
      IsGeoTestTower (geoTransformAlong m H) T → IsInvDomain 2 (geoTransformAlong I T) :=
    fun T ht => member_prefix_model_domain hn m h S hS H hH T ht
  exact ⟨domain_same_member_geometry _ I C hdC hCN hCE hmodel R hR,
    domain_same_member_geometry _ I B hdB hBN hBE hmodel R hR⟩

theorem member_prefix_companion_entire_open_identity (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    {V : CMfd.{u} n} (H : BlowupTower X V) (hH : IsGeoTestTower m H)
    (R : BlowupTower V Y) (hR : IsGeoTestTower (geoTransformAlong m H) R)
    (U : Opens V) (q : ℕ) (hq : 1 ≤ q) :
    geoTransformAlong
        (companionOf n (MarkedIdeal.pullback (Subtype.val : U → V)
          (geoTransformAlong (memberRemainderMarked m S) H)) q) (restrict U R) =
      MarkedIdeal.pullback (Subtype.val : openPreimage R U → Y)
        (geoTransformAlong (memberPrefixCompanion m S H q) R) ∧
    geoTransformAlong
        (barMarked (X := CMfd.of (n := n) U)
          (companionOf n (MarkedIdeal.pullback (Subtype.val : U → V)
            (geoTransformAlong (memberRemainderMarked m S) H)) q)) (restrict U R) =
      MarkedIdeal.pullback (Subtype.val : openPreimage R U → Y)
        (geoTransformAlong (memberPrefixCoefficientCompanion m S H q) R) := by
  let I := geoTransformAlong (memberRemainderMarked m S) H
  let C := memberPrefixCompanion m S H q
  let B := memberPrefixCoefficientCompanion m S H q
  have hdI := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS H hH
  have hdC : IsInvDomain 2 C := isInvDomain_companionAlong hn hdI hq
  have hdB : IsInvDomain 2 B := isInvDomain_barMarked C hdC
  have hCN : C.N = I.N := by simp only [C, I, memberPrefixCompanion, companionOf, companionAlong_N]
  have hCE : C.E = I.E := by simp only [C, I, memberPrefixCompanion, companionOf, companionAlong_E]
  have hBN : B.N = I.N := by simp only [B, memberPrefixCoefficientCompanion, barMarked_N]; exact hCN
  have hBE : B.E = I.E := by simp only [B, memberPrefixCoefficientCompanion, barMarked_E]; exact hCE
  have hmodel : ∀ {W : CMfd.{u} n} (T : BlowupTower V W),
      IsGeoTestTower (geoTransformAlong m H) T → IsInvDomain 2 (geoTransformAlong I T) :=
    fun T ht => member_prefix_model_domain hn m h S hS H hH T ht
  have hCinit := (pullback_val_companionOf hn hdI.isWellFormed hdI.isNonzeroAlongAt U q).symm
  constructor
  · rw [hCinit]
    exact restrict_same_member_geometry _ I C hdC hCN hCE hmodel U R hR
  · have hbar : barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → V) C) =
        MarkedIdeal.pullback (Subtype.val : U → V) (barMarked C) :=
      barMarked_pullback_val U hdC.isWellFormed.isCoherent hdC.isWellFormed.isClosedSubmanifold_N hdC.one_le_d
    rw [hCinit]
    change geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → V) C))
      (restrict U R) = MarkedIdeal.pullback (Subtype.val : openPreimage R U → Y) (geoTransformAlong B R)
    rw [hbar]
    exact restrict_same_member_geometry _ I B hdB hBN hBE hmodel U R hR

private theorem member_lower_parent_domain_and_nonempty (m : MarkedIdeal n X) (h : IsInvDomain 3 m)
    {V : CMfd.{u} n} (H : BlowupTower X V) (hH : IsGeoTestTower (barMarked m) H)
    (y₀ : V) {s : ℕ} (hl : level m H y₀ = s+1) :
    IsInvDomain 3 (geoTransformAlong (barMarked m) H) ∧
      (membersThrough (geoTransformAlong (barMarked m) H).E (origMembers m H) y₀).Nonempty := by
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong (isInvDomain_barMarked m h) H hH
  have hE₀ : ∀ B ∈ origMembers m H, B ∈ (geoTransformAlong (barMarked m) H).E :=
    fun B hB => List.mem_of_mem_take hB
  exact ⟨hd, membersThrough_nonempty hE₀ (by change 1 ≤ level m H y₀; rw [hl]; omega)⟩

theorem regimeRun_memberLowerExtension_eq_literal (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) {V : CMfd.{u} n}
    (H : BlowupTower X V) (hH : IsGeoTestTower (barMarked m) H)
    (y₀ : V) {s : ℕ} (hl : level m H y₀ = s+1)
    (T : BlowupTower V Y) (hT : IsGeoTestTower (geoTransformAlong (barMarked m) H) T)
    (q : ℕ) (z : openPreimage T (maskA m H y₀)) :
    regimeRun (OrdRegime (X := CMfd.of (n := n) (maskA m H y₀)) (lowerMarked m (s+1) H y₀) q)
      (restrict (maskA m H y₀) T) z =
      regimeRun (OrdRegime (memberLowerExtension m H y₀) q) T z := by
  obtain ⟨hd, hS⟩ := member_lower_parent_domain_and_nonempty m h H hH y₀ hl
  rw [← pullback_memberLowerExtension_eq_lowerMarked_succ hn m h.isWellFormed H hH y₀ hl]
  exact regimeRun_memberRemainder_restrict hn _ hd _ hS (maskA m H y₀) T hT q z

theorem regimeRun_memberLowerExtension_eq_literal_own_order (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) {V : CMfd.{u} n}
    (H : BlowupTower X V) (hH : IsGeoTestTower (barMarked m) H)
    (y₀ : V) {s : ℕ} (hl : level m H y₀ = s+1)
    (T : BlowupTower V Y) (hT : IsGeoTestTower (geoTransformAlong (barMarked m) H) T)
    (z : openPreimage T (maskA m H y₀)) :
    regimeRun (OrdRegime (X := CMfd.of (n := n) (maskA m H y₀)) (lowerMarked m (s+1) H y₀)
      (ofLex ((CanonicalCentres.invFamily hn 2).inv (lowerMarked m (s+1) H y₀)
        (restrict (maskA m H y₀) T) z)).1) (restrict (maskA m H y₀) T) z =
      regimeRun (OrdRegime (memberLowerExtension m H y₀)
        (nmOrd (geoTransformAlong (memberLowerExtension m H y₀) T) z)) T z := by
  rw [member_lower_first_entry_eq_entire_nmOrd hn m h H hH y₀ hl T hT z]
  exact regimeRun_memberLowerExtension_eq_literal hn m h H hH y₀ hl T hT _ z

theorem member_prefix_compAt_entire_identity (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    {V : CMfd.{u} n} (H : BlowupTower X V) (hH : IsGeoTestTower m H)
    (R : BlowupTower V Y) (hR : IsGeoTestTower (geoTransformAlong m H) R)
    (q : ℕ) (hq : 1 ≤ q) :
    let U := NonmonomialOrderTail.ordMask (geoTransformAlong (memberRemainderMarked m S) H) q
    geoTransformAlong (GeneralValue.compAt (memberRemainderMarked m S) q H) (restrict U R) =
      MarkedIdeal.pullback (Subtype.val : openPreimage R U → Y)
        (geoTransformAlong (memberPrefixCompanion m S H q) R) ∧
    geoTransformAlong (barMarked (GeneralValue.compAt (memberRemainderMarked m S) q H)) (restrict U R) =
      MarkedIdeal.pullback (Subtype.val : openPreimage R U → Y)
        (geoTransformAlong (memberPrefixCoefficientCompanion m S H q) R) :=
  member_prefix_companion_entire_open_identity hn m h S hS H hH R hR _ q hq

theorem member_lower_prefix_companion_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) {V : CMfd.{u} n}
    (H : BlowupTower X V) (hH : IsGeoTestTower (barMarked m) H)
    (y₀ : V) {s : ℕ} (hl : level m H y₀ = s+1)
    (T : BlowupTower V Y) (hT : IsGeoTestTower (geoTransformAlong (barMarked m) H) T)
    (i q : ℕ) (hq : 1 ≤ q) :
    let J₀ := geoTransformAlong (barMarked m) H
    let S := membersThrough J₀.E (origMembers m H) y₀
    let C := memberPrefixCompanion J₀ S (head T i) q
    let B := memberPrefixCoefficientCompanion J₀ S (head T i) q
    let U := openPreimage (head T i) (maskA m H y₀)
    let L := geoTransformAlong (lowerMarked m (s+1) H y₀) (restrict (maskA m H y₀) (head T i))
    IsInvDomain 2 (geoTransformAlong C (tail T i)) ∧
      IsInvDomain 2 (geoTransformAlong B (tail T i)) ∧
      geoTransformAlong (companionOf n L q) (restrict U (tail T i)) =
        MarkedIdeal.pullback (Subtype.val : openPreimage (tail T i) U → Y)
          (geoTransformAlong C (tail T i)) ∧
      geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (companionOf n L q)) (restrict U (tail T i)) =
        MarkedIdeal.pullback (Subtype.val : openPreimage (tail T i) U → Y)
          (geoTransformAlong B (tail T i)) := by
  dsimp only
  let J₀ := geoTransformAlong (barMarked m) H
  let S := membersThrough J₀.E (origMembers m H) y₀
  obtain ⟨hd, hS⟩ := member_lower_parent_domain_and_nonempty m h H hH y₀ hl
  have ht := (isGeoTestTower_iff_head_tail J₀ T i).mp hT
  obtain ⟨hC, hB⟩ := member_prefix_companion_entire_domains hn J₀ hd S hS (head T i) ht.1 (tail T i) ht.2 q hq
  have hid := member_prefix_companion_entire_open_identity hn J₀ hd S hS (head T i) ht.1 (tail T i) ht.2
    (openPreimage (head T i) (maskA m H y₀)) q hq
  have heq := (memberLowerExtension_tail_domain_and_mask_identity hn m h H hH y₀ hl (head T i) ht.1).2
  refine ⟨hC, hB, ?_⟩
  rw [heq]
  exact hid

open HironakaGeneralThreeNonspecialAnalyticLoci
open Hironaka.ResolutionInvariantSpec (IsCanonical)

theorem exists_actual_general_three_member_companion_history (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((CanonicalCentres.invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hnsp : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (hpos : 1 ≤ level (companionAt m T x) (companionTailAt m T x) p) :
    let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
    let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
      (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let I := memberLowerExtension K H p₀
    ∃ s : ℕ, level K R p = s+1 ∧ p₀ ∈ maskA K H p₀ ∧
      ∃ A E : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) A ∧
        DimLE (n := n) A 1 ∧ A ⊆ (geoTransformAlong I Q).N ∧ p ∈ A ∧
        IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ A ∧
        (∀ B ∈ globalComponents (n := n) A, ∀ z ∈ B \ E, ∀ w ∈ B \ E,
          (∀ q, regimeRun (OrdRegime I q) Q z = regimeRun (OrdRegime I q) Q w) ∧
          regimeRun (OrdRegime I (nmOrd (geoTransformAlong I Q) z)) Q z =
            regimeRun (OrdRegime I (nmOrd (geoTransformAlong I Q) w)) Q w) ∧
        ∀ q, ∀ z : openPreimage Q (maskA K H p₀),
          regimeRun (OrdRegime (X := CMfd.of (n := n) (maskA K H p₀)) (lowerMarked K (s+1) H p₀) q)
            (restrict (maskA K H p₀) Q) z = regimeRun (OrdRegime I q) Q z := by
  dsimp only
  let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
  let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
    (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  let J₀ := geoTransformAlong (barMarked K) H
  let S := membersThrough J₀.E (origMembers K H) p₀
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (CanonicalCentres.invFamily hn 2) K hK hmax hn R hcanK
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail (barMarked K) R r).mp hb.1
  obtain ⟨s, hs, hmask, _, A, hA, hdA, hsubA, hpA⟩ := exists_actual_companion_member_history_curve hn m h T hcan x hx hq p hp hnsp hpos
  have hpbar : p ∈ (geoTransformAlong (barMarked K) R).cosupp := by rw [hb.2.2]; exact hp
  have hreg := (StepOneValueMasked.stepRegime_and_mem_cosupp_head K hK.isWellFormed R hb.1 hpbar hnsp).1
  have hl : level K H p₀ = s+1 := hreg.1.trans hs
  obtain ⟨hdJ₀, hS⟩ := member_lower_parent_domain_and_nonempty K hK H hhead p₀ hl
  obtain ⟨E, hE, hdE, hEA, hruns⟩ := exists_analytic_dimzero_member_all_order_run_history hn J₀ hdJ₀ S hS Q htail hA hdA hsubA
  refine ⟨s, hs, hmask, A, E, hA, hdA, hsubA, hpA, hE, hdE, hEA, hruns, ?_⟩
  intro q z
  exact regimeRun_memberLowerExtension_eq_literal hn K hK H hhead p₀ hl Q htail q z

theorem exists_actual_general_three_member_companion_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((CanonicalCentres.invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hnsp : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (hpos : 1 ≤ level (companionAt m T x) (companionTailAt m T x) p) :
    let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
    let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
      (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let J₀ := geoTransformAlong (barMarked K) H
    let S := membersThrough J₀.E (origMembers K H) p₀
    ∃ s : ℕ, level K R p = s+1 ∧ p₀ ∈ maskA K H p₀ ∧
      ∀ i q : ℕ, 1 ≤ q →
        let C := memberPrefixCompanion J₀ S (head Q i) q
        let B := memberPrefixCoefficientCompanion J₀ S (head Q i) q
        let U := openPreimage (head Q i) (maskA K H p₀)
        let L := geoTransformAlong (lowerMarked K (s+1) H p₀) (restrict (maskA K H p₀) (head Q i))
        IsInvDomain 2 (geoTransformAlong C (tail Q i)) ∧
          IsInvDomain 2 (geoTransformAlong B (tail Q i)) ∧
          geoTransformAlong (companionOf n L q) (restrict U (tail Q i)) =
            MarkedIdeal.pullback (Subtype.val : openPreimage (tail Q i) U → CMfd.of (n := n) (patchAt m T x))
              (geoTransformAlong C (tail Q i)) ∧
          geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (companionOf n L q)) (restrict U (tail Q i)) =
            MarkedIdeal.pullback (Subtype.val : openPreimage (tail Q i) U → CMfd.of (n := n) (patchAt m T x))
              (geoTransformAlong B (tail Q i)) := by
  dsimp only
  let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
  let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
    (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (CanonicalCentres.invFamily hn 2) K hK hmax hn R hcanK
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail (barMarked K) R r).mp hb.1
  obtain ⟨s, hs, hmask, _, _, _⟩ := exists_actual_companion_member_tail_extension hn m h T hcan x hx hq p hp hnsp hpos
  have hpbar : p ∈ (geoTransformAlong (barMarked K) R).cosupp := by rw [hb.2.2]; exact hp
  have hreg := (StepOneValueMasked.stepRegime_and_mem_cosupp_head K hK.isWellFormed R hb.1 hpbar hnsp).1
  have hl : level K H p₀ = s+1 := hreg.1.trans hs
  exact ⟨s, hs, hmask, fun i q hq => member_lower_prefix_companion_dictionary hn K hK H hhead p₀ hl Q htail i q hq⟩

end
end Hironaka.HironakaStepOneMemberCompanionHistoryExtension
