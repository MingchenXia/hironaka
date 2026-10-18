/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCoherentHistoryYearIdeal
import Hironaka.Resolution.HironakaSharpOriginalMemberProductDomain
/-! Actual indexed SNC intersection-product ideals, genuine chronological
whole year equations, and SAME literal original positive tagged-count ideals.
BOTH finite germ directions and real SAME-boundary auxiliary marked inputs.
Complete source-first blueprint precedes Lean. All original indexed positions
are retained; G3's distinct bad-point trace-germ count is not substituted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCoherentCompanionCountIdeal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  GermIdealOrder NonmonomialOrderLocal RestrictedIdealExtension IdealWeightPowers
  NormalCrossings SimultaneousNormalCrossings BoundaryCount
  HironakaOriginalCoherentHistoryYearIdeal HironakaOriginalCompanionHistoryYearAnalytic
  HironakaOriginalCompanionChronologicalBoundaryAnalytic
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaStepOneMemberLowerExtension CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y : CMfd.{u} n}

private theorem zeroLocus_sumIdeal {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    (sumIdeal I J).zeroLocus = I.zeroLocus ∩ J.zeroLocus := by
  ext x
  constructor
  · intro hx
    exact ⟨fun g hg => hx g (le_sumIdeal_left hI x g hg),fun g hg => hx g (le_sumIdeal_right hJ x g hg)⟩
  · rintro ⟨hxI,hxJ⟩ g hg
    obtain ⟨_,N,s,a,hs,_,he⟩ := hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _hi
    rcases hs i with hi | hi
    · rw [hxI _ hi,mul_zero]
    · rw [hxJ _ hi,mul_zero]

private theorem mem_idealListProduct_zeroLocus (L : List (GermIdeal n X))
    (hL : ∀ I ∈ L,I.IsCoherent) (x : X) :
    x ∈ (idealListProduct L).zeroLocus ↔ ∃ I ∈ L,x ∈ I.zeroLocus := by
  induction L with
  | nil =>
    constructor
    · intro hx
      exact False.elim (one_ne_zero (hx (fun _ => 1) (holomorphicAt_const 1)))
    · rintro ⟨I,hI,_⟩
      simp at hI
  | cons I L ih =>
    rw [idealListProduct,HironakaEffectiveDivisorSum.zeroLocus_mul_eq_union
      (hL I (List.mem_cons_self)) (isCoherent_idealListProduct L (fun J hJ => hL J (List.mem_cons_of_mem I hJ)))]
    constructor
    · rintro (hx | hx)
      · exact ⟨I,List.mem_cons_self,hx⟩
      · obtain ⟨J,hJ,hxJ⟩ := (ih (fun J hJ => hL J (List.mem_cons_of_mem I hJ))).mp hx
        exact ⟨J,List.mem_cons_of_mem I hJ,hxJ⟩
    · rintro ⟨J,hJ,hxJ⟩
      rcases List.mem_cons.mp hJ with rfl | hJ
      · exact Or.inl hxJ
      · exact Or.inr ((ih (fun J hJ => hL J (List.mem_cons_of_mem I hJ))).mpr ⟨J,hJ,hxJ⟩)

private def indexedBoundaryFactors (E : List (Set X)) (s : ℕ) : List (GermIdeal n X) :=
  ((Finset.univ : Finset (Fin E.length)).powersetCard s).toList.map
    (fun S => vanishingIdeal (n := n) (memberInter E S))

/-- All real fixed-cardinality indexed SNC intersections, with the literal actual unit product. -/
def indexedBoundaryCountIdeal (E : List (Set X)) (s : ℕ) : GermIdeal n X :=
  idealListProduct (indexedBoundaryFactors E s)

private theorem indexedBoundaryFactors_coherent (hn : 0 < n) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (s : ℕ) : ∀ I ∈ indexedBoundaryFactors E s,I.IsCoherent := by
  intro I hI
  obtain ⟨S,_hS,rfl⟩ := List.mem_map.mp hI
  exact VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_memberInter hn hE S)

theorem isCoherent_indexedBoundaryCountIdeal (hn : 0 < n) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (s : ℕ) : (indexedBoundaryCountIdeal E s).IsCoherent :=
  isCoherent_idealListProduct _ (indexedBoundaryFactors_coherent hn hE s)

theorem zeroLocus_indexedBoundaryCountIdeal (hn : 0 < n) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (s : ℕ) :
    (indexedBoundaryCountIdeal E s).zeroLocus = {x | s ≤ boundaryCount E x} := by
  ext x
  rw [indexedBoundaryCountIdeal,mem_idealListProduct_zeroLocus _ (indexedBoundaryFactors_coherent hn hE s) x]
  constructor
  · rintro ⟨I,hI,hxI⟩
    obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hI
    have hScard : S.card=s := (Finset.mem_powersetCard.mp (Finset.mem_toList.mp hS)).2
    rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (isClosed_memberInter hE.1 S)] at hxI
    have hsub : S ⊆ Finset.univ.filter (fun i : Fin E.length => x ∈ E.get i) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,hxI i hi⟩
    exact hScard.symm.trans_le (Finset.card_le_card hsub)
  · intro hx
    obtain ⟨S,hS,hScard⟩ := Finset.exists_subset_card_eq hx
    refine ⟨vanishingIdeal (n := n) (memberInter E S),?_,?_⟩
    · exact List.mem_map.mpr ⟨S,Finset.mem_toList.mpr
        (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hScard⟩),rfl⟩
    · rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (isClosed_memberInter hE.1 S)]
      intro i hi
      exact (Finset.mem_filter.mp (hS hi)).2

private def chronologicalCountFactors (m : MarkedIdeal n X) (T : BlowupTower X Y) (q s : ℕ) :
    List (GermIdeal n Y) :=
  (Finset.range (T.length+1)).toList.map (fun r =>
    sumIdeal (companionHistoryYearIdeal m T q r) (indexedBoundaryCountIdeal (chronologicalMembers m T r) s))

/-- SAME actual chronological prefixes and genuine original year ideals, before any desired-locus certificate. -/
def chronologicalCompanionCountIdeal (m : MarkedIdeal n X) (T : BlowupTower X Y) (q s : ℕ) : GermIdeal n Y :=
  idealListProduct (chronologicalCountFactors m T q s)

private theorem chronologicalCountFactors_coherent (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (q s : ℕ) :
    ∀ I ∈ chronologicalCountFactors m T q s,I.IsCoherent := by
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  intro I hI
  obtain ⟨r,_hr,rfl⟩ := List.mem_map.mp hI
  exact isCoherent_sumIdeal (original_companionHistoryYearIdeal_coherent_dictionary hn m h T hc q r).1
    (isCoherent_indexedBoundaryCountIdeal hn
      (NormalCrossingsComparison.isSNCDivisor_of_sublist hd.isWellFormed.isSNCDivisor (List.take_sublist _ _)) s)

theorem isCoherent_chronologicalCompanionCountIdeal (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (q s : ℕ) :
    (chronologicalCompanionCountIdeal m T q s).IsCoherent :=
  isCoherent_idealListProduct _ (chronologicalCountFactors_coherent hn m h T hc q s)

theorem zeroLocus_chronologicalCompanionCountIdeal (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (q s : ℕ) :
    (chronologicalCompanionCountIdeal m T q s).zeroLocus =
      {y | y ∈ (geoTransformAlong m T).cosupp ∧ q ≤ nmOrd (geoTransformAlong m T) y ∧
        s ≤ companionChronologicalCount m T q y} := by
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  rw [companionChronologicalCount_superlevel_eq_biUnion]
  ext y
  rw [chronologicalCompanionCountIdeal,mem_idealListProduct_zeroLocus _ (chronologicalCountFactors_coherent hn m h T hc q s) y]
  constructor
  · rintro ⟨I,hI,hy⟩
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hI
    have hY := original_companionHistoryYearIdeal_coherent_dictionary hn m h T hc q r
    have hE : IsSNCDivisor n (chronologicalMembers m T r) :=
      NormalCrossingsComparison.isSNCDivisor_of_sublist hd.isWellFormed.isSNCDivisor (List.take_sublist _ _)
    rw [zeroLocus_sumIdeal hY.1 (isCoherent_indexedBoundaryCountIdeal hn hE s),hY.2,
      zeroLocus_indexedBoundaryCountIdeal hn hE s] at hy
    exact mem_iUnion₂.mpr ⟨r,Finset.mem_toList.mp hr,hy⟩
  · intro hy
    obtain ⟨r,hr,hy⟩ := mem_iUnion₂.mp hy
    have hY := original_companionHistoryYearIdeal_coherent_dictionary hn m h T hc q r
    have hE : IsSNCDivisor n (chronologicalMembers m T r) :=
      NormalCrossingsComparison.isSNCDivisor_of_sublist hd.isWellFormed.isSNCDivisor (List.take_sublist _ _)
    refine ⟨sumIdeal (companionHistoryYearIdeal m T q r) (indexedBoundaryCountIdeal (chronologicalMembers m T r) s),
      List.mem_map.mpr ⟨r,Finset.mem_toList.mpr hr,rfl⟩,?_⟩
    rw [zeroLocus_sumIdeal hY.1 (isCoherent_indexedBoundaryCountIdeal hn hE s),hY.2,
      zeroLocus_indexedBoundaryCountIdeal hn hE s]
    exact hy

/-- The literal higher current order branch and SAME real chronological count, with the true ideal product. -/
def positiveCanonicalCompanionCountIdeal (m : MarkedIdeal n X) (T : BlowupTower X Y) (q s : ℕ) : GermIdeal n Y :=
  (companionYearBaselineIdeal (geoTransformAlong m T) (q+1)).mul (chronologicalCompanionCountIdeal m T q s)

/-- ONLY original inputs give coherence and the exact ENTIRE full original positive tagged-count threshold. -/
theorem original_positiveCanonicalCompanionCountIdeal_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (q s : ℕ) (hq : 1 ≤ q) :
    (positiveCanonicalCompanionCountIdeal m T q s).IsCoherent ∧
      (positiveCanonicalCompanionCountIdeal m T q s).zeroLocus =
        {y | y ∈ (geoTransformAlong m T).cosupp ∧
          positiveCanonicalCompanionCountThreshold k q s ≤ (invFamily hn (k+1)).inv m T y} := by
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hB := isCoherent_companionYearBaselineIdeal hn hd (q+1)
  have hC := isCoherent_chronologicalCompanionCountIdeal hn m h T hc q s
  refine ⟨isCoherent_mul hB hC,?_⟩
  rw [positiveCanonicalCompanionCountIdeal,HironakaEffectiveDivisorSum.zeroLocus_mul_eq_union hB hC,
    zeroLocus_companionYearBaselineIdeal hn hd (q+1),zeroLocus_chronologicalCompanionCountIdeal hn m h T hc q s,
    canonical_positive_companion_count_superlevel_eq_union hn m h T hc q s hq]
  have hBase : {y | y ∈ (geoTransformAlong m T).cosupp ∧ q+1 ≤ nmOrd (geoTransformAlong m T) y} =
      (geoTransformAlong m T).cosupp ∩ ordGe (geoTransformAlong m T) (q+1) := by
    ext y
    exact and_congr_right fun hy => (mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt
      ((geoTransformAlong m T).cosupp_subset_N hy) (q+1)).symm
  rw [hBase]

/-- BOTH actual nearby germ span directions, and SAME literal original full threshold equations. -/
theorem exists_original_positiveCanonicalCompanionCountIdeal_generators (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (q s : ℕ) (hq : 1 ≤ q) (x : Y) :
    ∃ U : Set Y,IsOpen U ∧ x ∈ U ∧ ∃ (N : ℕ) (a : Fin N → Y → ℂ),
      (∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (a i) U) ∧
      (∀ y ∈ U,∀ g,(positiveCanonicalCompanionCountIdeal m T q s).mem y g ↔ IsInSpanAt (n := n) (· ∈ range a) y g) ∧
      ∀ y ∈ U,(y ∈ (geoTransformAlong m T).cosupp ∧
        positiveCanonicalCompanionCountThreshold k q s ≤ (invFamily hn (k+1)).inv m T y) ↔ ∀ i,a i y=0 := by
  obtain ⟨hI,hZ⟩ := original_positiveCanonicalCompanionCountIdeal_dictionary hn m h T hc q s hq
  obtain ⟨U,hU,hxU,N,a,ha,hgen⟩ := hI x
  refine ⟨U,hU,hxU,N,a,ha,hgen,?_⟩
  intro y hy
  change y ∈ {z | z ∈ (geoTransformAlong m T).cosupp ∧
    positiveCanonicalCompanionCountThreshold k q s ≤ (invFamily hn (k+1)).inv m T z} ↔ _
  rw [← hZ]
  constructor
  · intro hz i
    have hol : HolomorphicAt n (a i) y := eventually_of_mem (hU.mem_nhds hy)
      (fun z hz => (ha i z hz).mdifferentiableAt (hU.mem_nhds hz))
    apply hz (a i)
    apply (hgen y hy (a i)).mpr
    exact isInSpanAt_of_eq_mul ⟨i,rfl⟩ hol (holomorphicAt_const 1)
      (Eventually.of_forall fun z => (one_mul (a i z)).symm)
  · intro hz g hg
    obtain ⟨_,M,t,b,ht,_,he⟩ := (hgen y hy g).mp hg
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _hi
    obtain ⟨j,hj⟩ := ht i
    rw [← hj,hz j,mul_zero]

private theorem interior_cosupp_eq_empty {m : MarkedIdeal n Y} (h : IsInvDomain k m) :
    interior m.cosupp = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨g,hg,hfreq⟩ := h.isNonzeroAlongAt x (m.cosupp_subset_N (interior_subset hx))
  have hmem := HomogenizedGlueing.eventually_mem h.isWellFormed.isCoherent hg
  obtain ⟨z,⟨hzN,hzg⟩,hzgmem,hzO⟩ := (hfreq.and_eventually (hmem.and (isOpen_interior.mem_nhds hx))).exists
  have hzcs := interior_subset hzO
  have hhol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h.isWellFormed.isCoherent hzgmem
  exact hzg ((vanishesToOrderOn_one_iff hzN hhol).mp ((hzcs.2 g hzgmem).mono h.one_le_d))

/-- Whole ambient carrier, SAME actual current boundary and literal genuine threshold ideal. -/
def positiveCanonicalCompanionCountMarked (m : MarkedIdeal n X) (T : BlowupTower X Y) (q s : ℕ) : MarkedIdeal n Y :=
  ⟨univ,(geoTransformAlong m T).E,positiveCanonicalCompanionCountIdeal m T q s,1⟩

/-- ONLY original inputs internally supply genuine full ambient SAME-boundary marked-domain geometry. -/
theorem original_positiveCanonicalCompanionCountMarked_isInvDomain (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (q s : ℕ) (hq : 1 ≤ q) :
    IsInvDomain n (positiveCanonicalCompanionCountMarked m T q s) := by
  have hT := (invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  obtain ⟨hI,hZ⟩ := original_positiveCanonicalCompanionCountIdeal_dictionary hn m h T hc q s hq
  have hi : interior (positiveCanonicalCompanionCountIdeal m T q s).zeroLocus = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hm := interior_mono (show (positiveCanonicalCompanionCountIdeal m T q s).zeroLocus ⊆ (geoTransformAlong m T).cosupp from
      fun z hz => (hZ ▸ hz).1) hy
    rw [interior_cosupp_eq_empty hd] at hm
    exact hm
  have hN : IsClosedSubmanifold n (univ : Set Y) :=
    ⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
  refine ⟨⟨hN,hI,hd.isWellFormed.isSNCDivisor,isTransverse_univ_of_isSNCDivisor hd.isWellFormed.isSNCDivisor⟩,
    (fun x _ => ⟨n,le_rfl,AnalyticIrreducibleComponents.regularAtDim_univ x⟩),le_rfl,?_⟩
  intro x hx
  apply isNonzeroAlongAt_of_thin_cosupport (d := 1) hI
  · intro O hO hOA
    change O ∩ univ ⊆ cosupport n univ (positiveCanonicalCompanionCountIdeal m T q s) 1 at hOA
    change O ∩ univ = ∅
    rw [inter_univ] at hOA ⊢
    rw [cosupport_one (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg),univ_inter] at hOA
    have hsub : O ⊆ interior (positiveCanonicalCompanionCountIdeal m T q s).zeroLocus := by
      rw [← hO.interior_eq]
      exact interior_mono hOA
    rw [hi] at hsub
    exact eq_empty_iff_forall_notMem.mpr (fun y hy => hsub hy)
  · exact hx

end
end Hironaka.HironakaOriginalCoherentCompanionCountIdeal
