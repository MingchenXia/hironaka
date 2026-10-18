/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.BlowupTowerRestrictLengthExact
import Hironaka.Resolution.HironakaOriginalCoherentHistoryYearOpenNaturality
/-! Entire actual indexed, chronological and positive companion-count ideal
pullbacks on genuine original open histories. Every actual indexed and empty
position is retained. Complete source-first blueprint precedes this code.
Full arbitrary recursive threshold analytics and global scheduler remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCoherentCompanionCountOpenNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaOriginalCoherentHistoryYearIdeal HironakaOriginalCoherentCompanionCountIdeal
  HironakaOriginalCoherentHistoryYearOpenNaturality HironakaOriginalCompanionChronologicalBoundaryAnalytic
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  NormalCrossings SimultaneousNormalCrossings BoundaryCount MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen CanonicalCentres RestrictedIdealExtension
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n k : ℕ} {X Y : CMfd.{u} n}

/-- Actual finite coherent factor induction retains the original unit product. -/
theorem pullback_val_idealListProduct (U : Opens X) (L : List (GermIdeal n X))
    (hL : ∀ I ∈ L,I.IsCoherent) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (idealListProduct L) =
      idealListProduct (L.map (GermIdeal.pullback (m := n) (Subtype.val : U → X))) := by
  induction L with
  | nil => exact BlowupExceptionalDivisor.pullback_unitIdeal
  | cons I L ih =>
    have hI := hL I (by simp)
    have hRest : ∀ J ∈ L,J.IsCoherent := fun J hJ => hL J (List.mem_cons_of_mem I hJ)
    change GermIdeal.pullback (m := n) (Subtype.val : U → X) (I.mul (idealListProduct L)) = _
    rw [GermIdealTotalTransform.pullback_mul contMDiff_subtype_val hI
      (isCoherent_idealListProduct L hRest),ih hRest]
    rfl

/-- GENUINE enumeration permutations preserve the SAME whole coherent ideal product. -/
theorem idealListProduct_eq_of_perm {L K : List (GermIdeal n X)} (hP : L.Perm K)
    (hL : ∀ I ∈ L,I.IsCoherent) : idealListProduct L = idealListProduct K := by
  induction hP with
  | nil => rfl
  | cons I _h ih =>
    exact congrArg (I.mul) (ih fun J hJ => hL J (List.mem_cons_of_mem I hJ))
  | swap I J L =>
    have hI := hL I (by simp)
    have hJ := hL J (by simp)
    have hRest := isCoherent_idealListProduct L (fun A hA => hL A (by simp [hA]))
    change J.mul (I.mul (idealListProduct L)) = I.mul (J.mul (idealListProduct L))
    rw [← GermIdealTotalTransform.mul_assoc hJ hI hRest,
      RestrictLeCalculus.mul_comm' J I,GermIdealTotalTransform.mul_assoc hI hJ hRest]
  | trans hP _hQ ihP ihQ =>
    exact (ihP hL).trans (ihQ fun I hI => hL I (hP.mem_iff.mpr hI))

/-- The genuine finite original position equivalence retains every numeric list index. -/
def originalOpenBoundaryIndexEquiv (E : List (Set X)) (U : Opens X) :
    Fin E.length ≃ Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length :=
  finCongr (List.length_map (f := ((Subtype.val : U → X) ⁻¹' ·))).symm

private theorem actual_open_index_get (E : List (Set X)) (U : Opens X) (i : Fin E.length) :
    (E.map ((Subtype.val : U → X) ⁻¹' ·)).get (originalOpenBoundaryIndexEquiv E U i) =
      (Subtype.val : U → X) ⁻¹' E.get i := by
  simp [originalOpenBoundaryIndexEquiv,List.get_eq_getElem]

/-- Both actual intersection membership directions precede any count or zero-set dictionary. -/
theorem memberInter_original_open_pullback (E : List (Set X)) (U : Opens X) (S : Finset (Fin E.length)) :
    memberInter (E.map ((Subtype.val : U → X) ⁻¹' ·))
      ((originalOpenBoundaryIndexEquiv E U).finsetCongr S) =
        (Subtype.val : U → X) ⁻¹' memberInter E S := by
  ext x
  constructor
  · intro hx i hi
    have hm := hx (originalOpenBoundaryIndexEquiv E U i)
      (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    rwa [actual_open_index_get] at hm
  · intro hx i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    change x ∈ (E.map ((Subtype.val : U → X) ⁻¹' ·)).get (originalOpenBoundaryIndexEquiv E U j)
    rw [actual_open_index_get]
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

/-- ONLY original SNC constructs actual whole fixed-cardinality intersection-product pullback. -/
theorem pullback_val_indexedBoundaryCountIdeal (hn : 0 < n) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (U : Opens X) (s : ℕ) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (indexedBoundaryCountIdeal E s) =
      indexedBoundaryCountIdeal (X := CMfd.of (n := n) U)
        (E.map ((Subtype.val : U → X) ⁻¹' ·)) s := by
  let L := ((Finset.univ : Finset (Fin E.length)).powersetCard s).toList
  let e := originalOpenBoundaryIndexEquiv E U
  let f := fun S : Finset (Fin E.length) => vanishingIdeal (n := n) (memberInter E S)
  let g := fun S : Finset (Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length) =>
    vanishingIdeal (n := n) (memberInter (E.map ((Subtype.val : U → X) ⁻¹' ·)) S)
  have hcoh : ∀ I ∈ L.map f,I.IsCoherent := by
    intro I hI
    obtain ⟨S,_hS,rfl⟩ := List.mem_map.mp hI
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_memberInter hn hE S)
  change GermIdeal.pullback (m := n) (Subtype.val : U → X) (idealListProduct (L.map f)) =
    idealListProduct (((Finset.univ : Finset (Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length)).powersetCard s).toList.map g)
  rw [pullback_val_idealListProduct U _ hcoh,List.map_map]
  have heq : L.map (fun S => GermIdeal.pullback (m := n) (Subtype.val : U → X) (f S)) =
      (L.map e.finsetCongr).map g := by
    rw [List.map_map]
    apply List.map_congr_left
    intro S _hS
    dsimp only [f,g,e]
    change GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (vanishingIdeal (n := n) (memberInter E S)) =
        vanishingIdeal (n := n) (memberInter (E.map ((Subtype.val : U → X) ⁻¹' ·))
          ((originalOpenBoundaryIndexEquiv E U).finsetCongr S))
    rw [memberInter_original_open_pullback,SmoothCentreHomogeneity.pullback_val_vanishingIdeal]
  change idealListProduct (L.map (fun S => GermIdeal.pullback (m := n) (Subtype.val : U → X) (f S))) = _
  rw [heq]
  apply idealListProduct_eq_of_perm (X := CMfd.of (n := n) U) ((actual_fixed_card_index_family_perm e s).map g)
  intro I hI
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hI
  obtain ⟨R,_hR,rfl⟩ := List.mem_map.mp hS
  dsimp only [g,e]
  rw [memberInter_original_open_pullback,← SmoothCentreHomogeneity.pullback_val_vanishingIdeal]
  exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
    (VanishingIdealCoherent.isCoherent_vanishingIdeal (isClosedSubmanifold_memberInter hn hE R))


private theorem hol_of_coherent {I : GermIdeal n X} (h : I.IsCoherent) :
    ∀ x g,I.mem x g → HolomorphicAt n g x :=
  fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h hg

/-- Actual whole current boundary and original/history lengths retain the SAME chronological prefix. -/
theorem chronologicalMembers_original_open_pullback (m : MarkedIdeal n X) (h : IsInvDomain k m)
    (T : BlowupTower X Y) (ht : IsGeoTestTower m T) (U : Opens X) (r : ℕ) :
    chronologicalMembers (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) r =
      (chronologicalMembers m T r).map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·) := by
  unfold chronologicalMembers
  rw [geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T ht]
  simp only [MarkedIdeal.pullback,List.length_map,length_restrict,List.map_take]

private theorem actual_chronological_factors_coherent (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y) (ht : IsGeoTestTower m T)
    (q s : ℕ) : ∀ r : ℕ,
      (sumIdeal (companionHistoryYearIdeal m T q r)
        (indexedBoundaryCountIdeal (chronologicalMembers m T r) s)).IsCoherent := by
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  intro r
  exact isCoherent_sumIdeal (isCoherent_companionHistoryYearIdeal hn h T ht q r)
    (isCoherent_indexedBoundaryCountIdeal hn
      (NormalCrossingsComparison.isSNCDivisor_of_sublist hd.isWellFormed.isSNCDivisor (List.take_sublist _ _)) s)

private theorem actual_chronological_ideal_coherent (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y) (ht : IsGeoTestTower m T)
    (q s : ℕ) : (chronologicalCompanionCountIdeal m T q s).IsCoherent := by
  change (idealListProduct ((Finset.range (T.length+1)).toList.map (fun r =>
    sumIdeal (companionHistoryYearIdeal m T q r)
      (indexedBoundaryCountIdeal (chronologicalMembers m T r) s)))).IsCoherent
  apply isCoherent_idealListProduct
  intro I hI
  obtain ⟨r,_hr,rfl⟩ := List.mem_map.mp hI
  exact actual_chronological_factors_coherent hn m h T ht q s r

/-- True original source-test data give whole ideal equality over EVERY actual original open history. -/
theorem pullback_val_chronologicalCompanionCountIdeal (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y) (ht : IsGeoTestTower m T)
    (U : Opens X) (q s : ℕ) :
    GermIdeal.pullback (m := n) (Subtype.val : openPreimage T U → Y) (chronologicalCompanionCountIdeal m T q s) =
      chronologicalCompanionCountIdeal (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) q s := by
  let F := fun r => sumIdeal (companionHistoryYearIdeal m T q r)
    (indexedBoundaryCountIdeal (chronologicalMembers m T r) s)
  have hF : ∀ I ∈ (Finset.range (T.length+1)).toList.map F,I.IsCoherent := by
    intro I hI
    obtain ⟨r,_hr,rfl⟩ := List.mem_map.mp hI
    exact actual_chronological_factors_coherent hn m h T ht q s r
  change GermIdeal.pullback (m := n) (Subtype.val : openPreimage T U → Y)
    (idealListProduct ((Finset.range (T.length+1)).toList.map F)) =
    idealListProduct ((Finset.range ((restrict U T).length+1)).toList.map (fun r =>
      sumIdeal (companionHistoryYearIdeal (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) q r)
        (indexedBoundaryCountIdeal (chronologicalMembers (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) r) s)))
  rw [length_restrict,pullback_val_idealListProduct (openPreimage T U) _ hF,List.map_map]
  apply congrArg idealListProduct
  apply List.map_congr_left
  intro r _hr
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  have hYear := isCoherent_companionHistoryYearIdeal hn h T ht q r
  have hE : IsSNCDivisor n (chronologicalMembers m T r) :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist hd.isWellFormed.isSNCDivisor (List.take_sublist _ _)
  have hCount := isCoherent_indexedBoundaryCountIdeal hn hE s
  change GermIdeal.pullback (m := n) (Subtype.val : openPreimage T U → Y)
      (sumIdeal (companionHistoryYearIdeal m T q r) (indexedBoundaryCountIdeal (chronologicalMembers m T r) s)) = _
  rw [MarkedIdealOperationsTransform.pullback_sumIdeal
    (𝔞 := companionHistoryYearIdeal m T q r) (𝔟 := indexedBoundaryCountIdeal (chronologicalMembers m T r) s)
    contMDiff_subtype_val (hol_of_coherent hYear) (hol_of_coherent hCount),
    pullback_val_companionHistoryYearIdeal hn h T ht U q r,
    pullback_val_indexedBoundaryCountIdeal hn hE (openPreimage T U) s,
    ← chronologicalMembers_original_open_pullback m h T ht U r]

/-- The actual higher original baseline and SAME whole chronological ideal retain their true product. -/
theorem pullback_val_positiveCanonicalCompanionCountIdeal (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y) (ht : IsGeoTestTower m T)
    (U : Opens X) (q s : ℕ) :
    GermIdeal.pullback (m := n) (Subtype.val : openPreimage T U → Y) (positiveCanonicalCompanionCountIdeal m T q s) =
      positiveCanonicalCompanionCountIdeal (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) q s := by
  have hd := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T ht
  rw [positiveCanonicalCompanionCountIdeal,GermIdealTotalTransform.pullback_mul contMDiff_subtype_val
    (isCoherent_companionYearBaselineIdeal hn hd (q+1)) (actual_chronological_ideal_coherent hn m h T ht q s),
    pullback_val_companionYearBaselineIdeal hn hd (openPreimage T U) (q+1),
    pullback_val_chronologicalCompanionCountIdeal hn m h T ht U q s,
    ← geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T ht]
  rfl

/-- All four real fields give the SAME entire original-boundary auxiliary marked record. -/
theorem pullback_val_positiveCanonicalCompanionCountMarked (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (T : BlowupTower X Y) (ht : IsGeoTestTower m T)
    (U : Opens X) (q s : ℕ) :
    MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (positiveCanonicalCompanionCountMarked m T q s) =
      positiveCanonicalCompanionCountMarked (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) q s := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact preimage_univ
  · have hrec := geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T ht
    exact (congrArg (fun J => J.E) hrec).symm
  · exact pullback_val_positiveCanonicalCompanionCountIdeal hn m h T ht U q s
  · rfl

/-- ONLY literal original canonical inputs internally supply the genuine entire open-history comparison. -/
theorem original_positiveCanonicalCompanionCountMarked_open_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain (k+1) m) (T : BlowupTower X Y)
    (hc : IsCanonical m ((invFamily hn (k+1)).inv m) T) (U : Opens X) (q s : ℕ) :
    MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (positiveCanonicalCompanionCountMarked m T q s) =
      positiveCanonicalCompanionCountMarked (MarkedIdeal.pullback (Subtype.val : U → X) m) (restrict U T) q s :=
  pullback_val_positiveCanonicalCompanionCountMarked hn m h T
    ((invFamily hn (k+1)).isInvValue.isGeoTestTower_of_isCanonical h T hc) U q s

end
end Hironaka.HironakaOriginalCoherentCompanionCountOpenNaturality
