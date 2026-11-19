/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCoherentHistoryYearSmoothNaturality
import Hironaka.Resolution.HironakaOriginalCoherentCompanionCountOpenNaturality

/-! WHOLE actual indexed/chronological positive count presentations and all
marked fields under genuine smooth pullback of ANY ORIGINAL test history. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCoherentCompanionCountSmoothNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaOriginalCoherentHistoryYearIdeal HironakaOriginalCoherentCompanionCountIdeal
  HironakaOriginalCoherentHistoryYearSmoothNaturality HironakaOriginalCoherentCompanionCountOpenNaturality
  HironakaOriginalCompanionChronologicalBoundaryAnalytic
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeRestriction
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower NormalCrossings SimultaneousNormalCrossings
  BoundaryCount RestrictedIdealExtension RelativePrincipalizationSpan IdealWeightPowers
open ResolutionInvariantSpec (IsInvDomain)
variable {n m k : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m}

private theorem pullback_unitIdeal_mixed (f : Y → X) :
    GermIdeal.pullback (m := m) f (unitIdeal n X)=unitIdeal m Y := by
  apply GermIdeal.ext
  funext y g
  apply propext
  constructor
  · exact fun hg => hg.1
  · intro hg
    exact isInSpanAt_of_eq_mul (S := fun s => ∃ a,(unitIdeal n X).mem (f y) a ∧ s=a ∘ f)
      (s := fun _ => (1 : ℂ)) (a := g)
      ⟨fun _ => (1 : ℂ),holomorphicAt_const 1,rfl⟩ hg hg (Eventually.of_forall fun _ => by simp)

/-- Genuine finite coherent products include the true unit in arbitrary model dimensions. -/
theorem pullback_idealListProduct {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (L : List (GermIdeal n X)) (hL : ∀ I ∈ L,I.IsCoherent) :
    GermIdeal.pullback (m := m) f (idealListProduct L)=
      idealListProduct (L.map (GermIdeal.pullback (m := m) f)) := by
  induction L with
  | nil => exact pullback_unitIdeal_mixed f
  | cons I L ih =>
    have hI := hL I (by simp)
    have hRest : ∀ J ∈ L,J.IsCoherent := fun J hJ => hL J (List.mem_cons_of_mem I hJ)
    change GermIdeal.pullback (m := m) f (I.mul (idealListProduct L))=_
    rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hf hI (isCoherent_idealListProduct L hRest),ih hRest]
    rfl

/-- The genuine finite original position equivalence retains every numeric list index. -/
def originalSmoothBoundaryIndexEquiv (E : List (Set X)) (f : Y → X) :
    Fin E.length ≃ Fin (E.map (f ⁻¹' ·)).length :=
  finCongr (List.length_map (f := (f ⁻¹' ·))).symm

private theorem actual_smooth_index_get (E : List (Set X)) (f : Y → X) (i : Fin E.length) :
    (E.map (f ⁻¹' ·)).get (originalSmoothBoundaryIndexEquiv E f i) =
      f ⁻¹' E.get i := by
  simp [originalSmoothBoundaryIndexEquiv,List.get_eq_getElem]

/-- Both actual intersection membership directions precede any count or zero-set dictionary. -/
theorem memberInter_original_smooth_pullback (E : List (Set X)) (f : Y → X) (S : Finset (Fin E.length)) :
    memberInter (E.map (f ⁻¹' ·))
      ((originalSmoothBoundaryIndexEquiv E f).finsetCongr S) =
        f ⁻¹' memberInter E S := by
  ext x
  constructor
  · intro hx i hi
    have hm := hx (originalSmoothBoundaryIndexEquiv E f i)
      (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    rwa [actual_smooth_index_get] at hm
  · intro hx i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    change x ∈ (E.map (f ⁻¹' ·)).get (originalSmoothBoundaryIndexEquiv E f j)
    rw [actual_smooth_index_get]
    exact hx j hj

private theorem actual_fixed_card_index_family_perm {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (s : ℕ) :
    (((Finset.univ : Finset A).powersetCard s).toList.map e.finsetCongr).Perm
      ((Finset.univ : Finset B).powersetCard s).toList := by
  apply List.perm_of_nodup_nodup_toFinset_eq
    ((Finset.nodup_toList _).map e.finsetCongr.injective) (Finset.nodup_toList _)
  ext S
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_toList,Finset.mem_powersetCard,
    Finset.subset_univ,true_and]
  constructor
  · rintro ⟨T,hT,rfl⟩
    simpa only [Equiv.finsetCongr_apply,Finset.card_map] using hT
  · intro hS
    exact ⟨e.symm.finsetCongr S,by simpa only [Equiv.finsetCongr_apply,Finset.card_map] using hS,
      e.finsetCongr.apply_symm_apply S⟩


/-- Actual smooth Hadamard and the real fixed-cardinality position bijection
prove the WHOLE count ideal equality before any zero-locus argument. -/
theorem pullback_indexedBoundaryCountIdeal {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0 < n) {E : List (Set X)} (hE : IsSNCDivisor n E) (s : ℕ) :
    GermIdeal.pullback (m := m) f (indexedBoundaryCountIdeal E s)=
      indexedBoundaryCountIdeal (E.map (f ⁻¹' ·)) s := by
  let L := ((Finset.univ : Finset (Fin E.length)).powersetCard s).toList
  let e := originalSmoothBoundaryIndexEquiv E f
  let F := fun S : Finset (Fin E.length) => vanishingIdeal (n := n) (memberInter E S)
  let G := fun S : Finset (Fin (E.map (f ⁻¹' ·)).length) =>
    vanishingIdeal (n := m) (memberInter (E.map (f ⁻¹' ·)) S)
  have hcoh : ∀ I ∈ L.map F,I.IsCoherent := by
    intro I hI
    obtain ⟨S,_hS,rfl⟩ := List.mem_map.mp hI
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_memberInter hn hE S)
  change GermIdeal.pullback (m := m) f (idealListProduct (L.map F))=
    idealListProduct (((Finset.univ : Finset (Fin (E.map (f ⁻¹' ·)).length)).powersetCard s).toList.map G)
  rw [pullback_idealListProduct hf.contMDiff _ hcoh,List.map_map]
  have heq : L.map (fun S => GermIdeal.pullback (m := m) f (F S))=(L.map e.finsetCongr).map G := by
    rw [List.map_map]
    apply List.map_congr_left
    intro S _hS
    dsimp only [F,G,e]
    change GermIdeal.pullback (m := m) f (vanishingIdeal (n := n) (memberInter E S))=
      vanishingIdeal (n := m) (memberInter (E.map (f ⁻¹' ·)) ((originalSmoothBoundaryIndexEquiv E f).finsetCongr S))
    rw [memberInter_original_smooth_pullback,pullback_vanishingIdeal_submersion hf (isClosedSubmanifold_memberInter hn hE S)]
  change idealListProduct (L.map (fun S => GermIdeal.pullback (m := m) f (F S)))=_
  rw [heq]
  apply idealListProduct_eq_of_perm (X := Y) ((actual_fixed_card_index_family_perm e s).map G)
  intro I hI
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hI
  obtain ⟨R,_hR,rfl⟩ := List.mem_map.mp hS
  dsimp only [G,e]
  rw [memberInter_original_smooth_pullback,←pullback_vanishingIdeal_submersion hf (isClosedSubmanifold_memberInter hn hE R)]
  exact GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff
    (VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_memberInter hn hE R))

private theorem actual_chronological_factors_coherent (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X D) (ht : IsGeoTestTower m T)
    (q s : ℕ) : ∀ r : ℕ,
      (sumIdeal (companionHistoryYearIdeal m T q r)
        (indexedBoundaryCountIdeal (chronologicalMembers m T r) s)).IsCoherent := by
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  intro r
  exact isCoherent_sumIdeal (isCoherent_companionHistoryYearIdeal hn h T ht q r)
    (isCoherent_indexedBoundaryCountIdeal hn
      (NormalCrossingsComparison.isSNCDivisor_of_sublist hd.isWellFormed.isSNCDivisor (List.take_sublist _ _)) s)

private theorem actual_chronological_ideal_coherent (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X D) (ht : IsGeoTestTower m T)
    (q s : ℕ) : (chronologicalCompanionCountIdeal m T q s).IsCoherent := by
  change (idealListProduct ((Finset.range (T.length+1)).toList.map (fun r =>
    sumIdeal (companionHistoryYearIdeal m T q r)
      (indexedBoundaryCountIdeal (chronologicalMembers m T r) s)))).IsCoherent
  apply isCoherent_idealListProduct
  intro I hI
  obtain ⟨r,_hr,rfl⟩ := List.mem_map.mp hI
  exact actual_chronological_factors_coherent hn m h T ht q s r



/-- Real WHOLE current E and true history/original lengths identify the SAME chronological prefix. -/
theorem chronologicalMembers_actual_smooth_pullback {f : Y → X} {g : D' → D}
    {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (a : ℕ) :
    chronologicalMembers (markedPullback (m := m) f M) Q a=(chronologicalMembers M T a).map (g ⁻¹' ·) := by
  unfold chronologicalMembers
  rw [(HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hT).2]
  simp only [markedPullback,List.length_map,h.length_eq,List.map_take]

/-- WHOLE chronological ideal equality over ANY actual original test prefix. -/
theorem actual_pullback_chronologicalCompanionCountIdeal {f : Y → X} {g : D' → D}
    {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (hn : 0 < n) (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (q s : ℕ) :
    GermIdeal.pullback (m := m) g (chronologicalCompanionCountIdeal M T q s)=
      chronologicalCompanionCountIdeal (markedPullback (m := m) f M) Q q s := by
  let F := fun a => sumIdeal (companionHistoryYearIdeal M T q a)
    (indexedBoundaryCountIdeal (chronologicalMembers M T a) s)
  have hF : ∀ I ∈ (Finset.range (T.length+1)).toList.map F,I.IsCoherent := by
    intro I hI
    obtain ⟨a,_ha,rfl⟩ := List.mem_map.mp hI
    exact actual_chronological_factors_coherent hn M hM T hT q s a
  change GermIdeal.pullback (m := m) g (idealListProduct ((Finset.range (T.length+1)).toList.map F))=
    idealListProduct ((Finset.range (Q.length+1)).toList.map (fun a =>
      sumIdeal (companionHistoryYearIdeal (markedPullback (m := m) f M) Q q a)
        (indexedBoundaryCountIdeal (chronologicalMembers (markedPullback (m := m) f M) Q a) s)))
  rw [h.length_eq,pullback_idealListProduct h.isSubmersion.contMDiff _ hF,List.map_map]
  apply congrArg idealListProduct
  apply List.map_congr_left
  intro a _ha
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hYear := isCoherent_companionHistoryYearIdeal hn hM T hT q a
  have hE : IsSNCDivisor n (chronologicalMembers M T a) :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist hd.isWellFormed.isSNCDivisor (List.take_sublist _ _)
  have hCount := isCoherent_indexedBoundaryCountIdeal hn hE s
  change GermIdeal.pullback (m := m) g
    (sumIdeal (companionHistoryYearIdeal M T q a) (indexedBoundaryCountIdeal (chronologicalMembers M T a) s))=_
  rw [pullback_sumIdeal_dimensions (I := companionHistoryYearIdeal M T q a)
    (J := indexedBoundaryCountIdeal (chronologicalMembers M T a) s) h.isSubmersion.contMDiff hYear hCount,
    actual_pullback_companionHistoryYearIdeal hn h M hM hT q a,
    pullback_indexedBoundaryCountIdeal h.isSubmersion hn hE s,
    ←chronologicalMembers_actual_smooth_pullback h M hM hT a]

/-- The named positive count equation uses its true higher baseline/product;
this WHOLE smooth comparison does not require original canonicality. -/
theorem actual_pullback_positiveCanonicalCompanionCountIdeal {f : Y → X} {g : D' → D}
    {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (hn : 0 < n) (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (q s : ℕ) :
    GermIdeal.pullback (m := m) g (positiveCanonicalCompanionCountIdeal M T q s)=
      positiveCanonicalCompanionCountIdeal (markedPullback (m := m) f M) Q q s := by
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  rw [positiveCanonicalCompanionCountIdeal,HironakaSmoothSubmersionCoefficientIdeals.pullback_mul h.isSubmersion.contMDiff
    (isCoherent_companionYearBaselineIdeal hn hd (q+1)) (actual_chronological_ideal_coherent hn M hM T hT q s),
    pullback_companionYearBaselineIdeal h.isSubmersion hn _ hd (q+1),
    actual_pullback_chronologicalCompanionCountIdeal hn h M hM hT q s,
    ←(HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hT).2]
  rfl

/-- ALL FOUR literal positive-count marked fields retain the SAME original boundary and actual history. -/
theorem actual_pullback_positiveCanonicalCompanionCountMarked {f : Y → X} {g : D' → D}
    {Q : BlowupTower Y D'} {T : BlowupTower X D}
    (hn : 0 < n) (h : IsActualTowerPullback f Q T g) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (hT : IsGeoTestTower M T) (q s : ℕ) :
    markedPullback (m := m) g (positiveCanonicalCompanionCountMarked M T q s)=
      positiveCanonicalCompanionCountMarked (markedPullback (m := m) f M) Q q s := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact preimage_univ
  · have hrec := (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
      h M hM.isWellFormed hT).2
    exact (congrArg (fun J => J.E) hrec).symm
  · exact actual_pullback_positiveCanonicalCompanionCountIdeal hn h M hM hT q s
  · rfl


/-- ONLY original smooth map/domain/ANY TEST history construct ONE real source
prefix and EVERY coherent whole count-presentation/marked comparison. -/
theorem exists_original_test_history_coherent_count_smooth_pullback {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hn : 0 < n) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T : BlowupTower X D) (hT : IsGeoTestTower M T) :
    ∃ (D' : CMfd.{u} m) (Q : BlowupTower Y D') (g : D' → D),
      IsActualTowerPullback f Q T g ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧ Q.length=T.length ∧
      IsInvDomain (k+(m-n)) (markedPullback (m := m) f M) ∧
      IsGeoTestTower (markedPullback (m := m) f M) Q ∧
      geoTransformAlong (markedPullback (m := m) f M) Q=markedPullback (m := m) g (geoTransformAlong M T) ∧
      ∀ q s : ℕ,
        (chronologicalCompanionCountIdeal (markedPullback (m := m) f M) Q q s).IsCoherent ∧
        (positiveCanonicalCompanionCountIdeal (markedPullback (m := m) f M) Q q s).IsCoherent ∧
        GermIdeal.pullback (m := m) g (chronologicalCompanionCountIdeal M T q s)=
          chronologicalCompanionCountIdeal (markedPullback (m := m) f M) Q q s ∧
        GermIdeal.pullback (m := m) g (positiveCanonicalCompanionCountIdeal M T q s)=
          positiveCanonicalCompanionCountIdeal (markedPullback (m := m) f M) Q q s ∧
        markedPullback (m := m) g (positiveCanonicalCompanionCountMarked M T q s)=
          positiveCanonicalCompanionCountMarked (markedPullback (m := m) f M) Q q s := by
  obtain ⟨D',Q,g,h⟩ := exists_actual_tower hf T
  obtain ⟨hqt,hrecord⟩ := HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary
    h M hM.isWellFormed hT
  refine ⟨D',Q,g,h,h.isSubmersion,h.length_eq,isInvDomain_markedPullback_submersion hf M hM,hqt,hrecord,?_⟩
  intro q s
  have hChron := actual_pullback_chronologicalCompanionCountIdeal hn h M hM hT q s
  have hPos := actual_pullback_positiveCanonicalCompanionCountIdeal hn h M hM hT q s
  have hc := actual_chronological_ideal_coherent hn M hM T hT q s
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hpcoh : (positiveCanonicalCompanionCountIdeal M T q s).IsCoherent :=
    isCoherent_mul (isCoherent_companionYearBaselineIdeal hn hd (q+1)) hc
  have hsourceChron := GermIdealPullbackCalculus.isCoherent_pullback h.isSubmersion.contMDiff hc
  have hsourcePos := GermIdealPullbackCalculus.isCoherent_pullback h.isSubmersion.contMDiff hpcoh
  rw [hChron] at hsourceChron
  rw [hPos] at hsourcePos
  exact ⟨hsourceChron,hsourcePos,hChron,hPos,actual_pullback_positiveCanonicalCompanionCountMarked hn h M hM hT q s⟩

end
end Hironaka.HironakaOriginalCoherentCompanionCountSmoothNaturality
