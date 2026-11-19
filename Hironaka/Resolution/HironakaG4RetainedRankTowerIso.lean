import Hironaka.Resolution.HironakaG4RetainedRankOpenComparison
import Hironaka.Resolution.HironakaG34JointMaskEquivariance
import Hironaka.Resolution.HironakaSharpActualDistinctCountOpenNaturality
import Hironaka.Invariant.ContactEmptyPrefix
import Hironaka.Resolution.HironakaOriginalBoundaryCanonicalPrincipalization
import Hironaka.Resolution.HironakaG4RetainedDefectCompactRank

/-! The actual retained profile and inactive factors under tower
isomorphisms over an arbitrary native base biholomorphism. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4RetainedRankTowerIso
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism HomogenizedGlueingTower
  MarkedIdealRestrictOpen BlowupTowerIsoTail RestrictEmptyTower
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  HironakaSharpActualFiniteChronologicalHistory HironakaActualRetainedBornResidualSeed
  HironakaActualRetainedBornResidualHistory HironakaActualRetainedBoundaryMaskBlock
  HironakaG4RetainedFactorOpenComparison HironakaG4RetainedRankOpenComparison
  HironakaG4PreparedCentreCoordinates HironakaG34JointMaskEquivariance
  HironakaSharpOriginalProductTraceOrder NonmonomialOrderLocal RelativePrincipalizationSpan
  HironakaG4RetainedDefectCompactRank HironakaActualRetainedBoundaryJointStep
  HironakaActualGlobalDefectProfileBlock
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualDistinctCountOpenNaturality
  HironakaSharpActualEmptyChronologicalDefect HironakaSharpActualFiniteMemberProduct

variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

private def diffeoTop (Y : CMfd.{u} n) :
    Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (⊤ : Opens Y) where
  toFun y := ⟨y,trivial⟩
  invFun y := y.val
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk (V := (⊤ : Opens Y)) contMDiff_id
    (fun _ => trivial)
  contMDiff_invFun := contMDiff_subtype_val


/-- A stage biholomorphism is an open holomorphic embedding onto the whole target. -/
theorem isOpenHoloEmbedding_diffeomorph
    (e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y) :
    HironakaBaseChange.IsOpenHoloEmbedding n e :=
  ⟨⊤,e.trans (diffeoTop Y),fun _ => rfl⟩

private theorem monomialPartAlong_append_empty_slots (N : Set Y')
    (I : GermIdeal n Y') (E : List (Set Y')) (r : ℕ) :
    MonomialPartAlong.monomialPartAlong n N I (E ++ List.replicate r ∅) =
      MonomialPartAlong.monomialPartAlong n N I E := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.replicate_succ',←List.append_assoc,MonomialPartEtale.monomialPartAlong_append_empty,ih]

private theorem nonmonomialPartAlong_append_empty_slots (N : Set Y')
    (I : GermIdeal n Y') (E : List (Set Y')) (r : ℕ) :
    MonomialPartAlong.nonmonomialPartAlong n N I (E ++ List.replicate r ∅) =
      MonomialPartAlong.nonmonomialPartAlong n N I E := by
  unfold MonomialPartAlong.nonmonomialPartAlong
  rw [monomialPartAlong_append_empty_slots]

set_option maxHeartbeats 500000 in
/-- The ordered actual residual and factor comparisons depend only on the
final geometric tuple. Extra genuinely empty born slots do not change them. -/
theorem actual_retained_row_factor_under_endpoint_diffeo (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    {N' : Set X'} {old' born' : List (Set X')}
    (hN' : IsClosedSubmanifold n N') (hE' : IsSNCDivisor n (old' ++ born'))
    (hTr' : IsTransverse n N' born') (hdense' : N' ⊆ closure (N' \ ⋃ H ∈ old' ++ born',H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (R : BlowupTower X' Y') (hR : IsGeoTestTower (geometricTemplate N' born') R)
    (hFullR : IsGeoTestTower (geometricTemplate (univ : Set X') (old' ++ born')) R)
    (e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (ι : Fin old.length ≃ Fin old'.length) (m : ℕ)
    (hAN : (geoTransformAlong (geometricTemplate N' born') R).N =
      e ⁻¹' (geoTransformAlong (geometricTemplate N born) S).N)
    (hAB : (geoTransformAlong (geometricTemplate N' born') R).E =
      (geoTransformAlong (geometricTemplate N born) S).E.map (e ⁻¹' ·) ++ List.replicate m ∅)
    (hOld : ∀ i,strictAlong R (old'.get (ι i)) = e ⁻¹' strictAlong S (old.get i)) (z : Y') :
    ∀ i : Fin old.length,retainedProfileAlong N' old' born' R z (ι i) =
        retainedProfileAlong N old born S (e z) i ∧
      ((retainedFactorMarked N' old' born' R (ι i)).ideal.mem z 1 ↔
        (retainedFactorMarked N old born S i).ideal.mem (e z) 1) ∧
      GermIdeal.pullback (m := n) e
        (chronologicalMarked (retainedResidualMarked N old born i) S).ideal =
        (chronologicalMarked (retainedResidualMarked N' old' born' (ι i)) R).ideal := by
  intro i
  let A := geoTransformAlong (geometricTemplate N born) S
  let AR := geoTransformAlong (geometricTemplate N' born') R
  let O := old.map (strictAlong S)
  let O' := old'.map (strictAlong R)
  let j : Fin O.length := Fin.cast (List.length_map _).symm i
  let j' : Fin O'.length := Fin.cast (List.length_map _).symm (ι i)
  have hGet : O.get j = strictAlong S (old.get i) := by simp [O,j]
  have hGet' : O'.get j' = strictAlong R (old'.get (ι i)) := by simp [O',j']
  have hOldEq : O'.get j' = e ⁻¹' O.get j := by rw [hGet,hGet',hOld]
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense S hS hFull
  have hRec' := actual_retained_born_recorded_residual_dictionary hn hN' hE' hTr' hdense' R hR hFullR
  let J := oldResidualPart A.N O A.E j
  let J' := oldResidualPart AR.N O' AR.E j'
  let D := oldMonomialPart A.N O A.E j
  let D' := oldMonomialPart AR.N O' AR.E j'
  have hSeed := retainedResidualMarked_geometry hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1 j
  have hEh := isOpenHoloEmbedding_diffeomorph e
  have hJ : GermIdeal.pullback (m := n) e J = J' := by
    unfold J J' oldResidualPart oldTraceIdeal
    rw [hAN,hOldEq,hAB,nonmonomialPartAlong_append_empty_slots]
    exact pullback_residual hEh hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1 j
  have hHD := MonomialPart.isClosedSubmanifold_get hn
    (isSNCDivisor_of_sublist hRec.2.1 (List.sublist_append_left O A.E)) j
  have hD : GermIdeal.pullback (m := n) e D = D' := by
    have hF := pullback_factorOf (Y := Y') hEh A.E hRec.1
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hHD)
    unfold D D' oldMonomialPart oldTraceIdeal
    rw [hAN,hOldEq,hAB,monomialPartAlong_append_empty_slots]
    exact congrArg (fun M : MarkedIdeal n Y' => M.ideal) hF
  have hRowS : (chronologicalMarked (retainedResidualMarked N old born i) S).ideal = J :=
    congrArg (fun M : MarkedIdeal n Y => M.ideal)
      (retained_seed_eq_chronological_current hn hN hE hTr hdense S hS hFull i).symm
  have hRowR : (chronologicalMarked (retainedResidualMarked N' old' born' (ι i)) R).ideal = J' :=
    congrArg (fun M : MarkedIdeal n Y' => M.ideal)
      (retained_seed_eq_chronological_current hn hN' hE' hTr' hdense' R hR hFullR (ι i)).symm
  have hDC : D.IsCoherent :=
    (actual_old_parts_geometry hn hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1 j).2.2.2.2.1
  refine ⟨?_,?_,?_⟩
  · unfold retainedProfileAlong
    rw [hRowS,hRowR]
    have hOrder := nmOrd_pullback_diffeo hn e
      (ordinaryTraceMarked_isWellFormed hRec.1 hSeed.1.isCoherent) hSeed.2.1 z
    change ordinaryTraceOrder (e ⁻¹' A.N) (GermIdeal.pullback (m := n) e J) z =
      ordinaryTraceOrder A.N J (e z) at hOrder
    rwa [←hAN,hJ] at hOrder
  · unfold retainedFactorMarked
    have hUnit := unit_mem_iff_of_coherent_pullback e.contMDiff hDC hD z
    unfold D D' oldMonomialPart oldTraceIdeal at hUnit
    rw [hGet,hGet'] at hUnit
    exact hUnit
  · rw [hRowS,hRowR]
    exact hJ

set_option maxHeartbeats 500000 in
/-- An actual stagewise tower isomorphism over a change of native base
pulls back the entire row profile and the true unit status at every old
label. The result concerns actual transformed records. -/
theorem actual_retained_row_and_factor_under_tower_iso (hn : 0 < n)
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (R : BlowupTower X' Y') (e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (he : IsTowerIso φ R S e) (z : Y') :
    let NR := φ ⁻¹' N
    let OR := old.map (φ ⁻¹' ·)
    let BR := born.map (φ ⁻¹' ·)
    let ι : Fin old.length ≃ Fin OR.length := finCongr (List.length_map _).symm
    ∀ i : Fin old.length,retainedProfileAlong NR OR BR R z (ι i) =
        retainedProfileAlong N old born S (e z) i ∧
      ((retainedFactorMarked NR OR BR R (ι i)).ideal.mem z 1 ↔
        (retainedFactorMarked N old born S i).ideal.mem (e z) 1) := by
  intro NR OR BR ι i
  let A := geoTransformAlong (geometricTemplate N born) S
  let AR := geoTransformAlong (geometricTemplate NR BR) R
  have hNR := (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff φ).mpr hN
  have hER : IsSNCDivisor n (OR ++ BR) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates φ) φ.continuous hE
  have hTR : IsTransverse n NR BR := isTransverse_preimage (pullsBackCoordinates φ) hTr
  have hDenseR : NR ⊆ closure (NR \ ⋃ H ∈ OR ++ BR,H) := by
    intro y hy
    have h := preimage_mono (f := φ) hdense hy
    change y ∈ φ.toHomeomorph ⁻¹' closure (N \ ⋃ H ∈ old ++ born,H) at h
    rw [φ.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage φ.toHomeomorph.continuous] at h
    change y ∈ closure ((φ : X' → X) ⁻¹' (N \ ⋃ H ∈ old ++ born,H)) at h
    rw [Set.preimage_sdiff,HironakaEmbeddedBoundary.preimage_biUnion_list,List.map_append] at h
    exact h
  have hTmpl : MarkedIdeal.pullback φ (geometricTemplate N born) = geometricTemplate NR BR :=
    HironakaG34NonPureLowDim.template_pullback φ N born
  have hR := (IsTowerIso.isGeoTestTower_iff φ hN IdealWeightPowers.isCoherent_unitIdeal he).mpr hS
  rw [hTmpl] at hR
  have hFullR := (IsTowerIso.isGeoTestTower_iff φ isClosedSubmanifold_univ
    IdealWeightPowers.isCoherent_unitIdeal he).mpr hFull
  rw [HironakaG34NonPureLowDim.template_pullback φ,Set.preimage_univ,List.map_append] at hFullR
  have hFields : AR = MarkedIdeal.pullback e A := by
    change geoTransformAlong (geometricTemplate NR BR) R = MarkedIdeal.pullback e A
    rw [←hTmpl]
    exact IsTowerIso.geoTransformAlong_eq φ hN IdealWeightPowers.isCoherent_unitIdeal he hS
  have hAN : AR.N = e ⁻¹' A.N := congrArg MarkedIdeal.N hFields
  have hAB : AR.E = A.E.map (e ⁻¹' ·) := congrArg MarkedIdeal.E hFields
  have hOld (j : Fin old.length) : strictAlong R (OR.get (ι j)) = e ⁻¹' strictAlong S (old.get j) := by
    have hGet : OR.get (ι j) = φ ⁻¹' old.get j := by simp [OR,ι]
    rw [hGet,he.strictAlong_eq]
  have h := actual_retained_row_factor_under_endpoint_diffeo hn hN hE hTr hdense
    hNR hER hTR hDenseR S hS hFull R hR hFullR e ι 0 hAN (by simpa using hAB) hOld z i
  exact ⟨h.1,h.2.1⟩

/-- The exact transformed rank comparison for an arbitrary native base
biholomorphism, including the full inactive set at corresponding points. -/
theorem actual_retained_rank_under_tower_iso (hn : 0 < n)
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N : Set X} {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (R : BlowupTower X' Y') (e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (he : IsTowerIso φ R S e) (z : Y') :
    let NR := φ ⁻¹' N
    let OR := old.map (φ ⁻¹' ·)
    let BR := born.map (φ ⁻¹' ·)
    let ι : Fin old.length ≃ Fin OR.length := finCongr (List.length_map _).symm
    let rS := retainedProfileAlong N old born S (e z)
    let rR := retainedProfileAlong NR OR BR R z
    (∀ i,rR (ι i)=rS i) ∧
      retainedInactiveRows NR OR BR rR R z =
        (retainedInactiveRows N old born rS S (e z)).map ι.toEmbedding ∧
      retainedDefectRankAlong NR OR BR R z = retainedDefectRankAlong N old born S (e z) := by
  intro NR OR BR ι rS rR
  have hComp := actual_retained_row_and_factor_under_tower_iso hn φ hN hE hTr hdense S hS hFull R e he z
  have hOrd (i : Fin old.length) : rR (ι i)=rS i := (hComp i).1
  exact ⟨hOrd,inactive_mask_and_rank_eq_of_ordered_comparison S R (e z) z ι hOrd (fun i => (hComp i).2)⟩

/-- Exact rank transport from a chart biholomorphic to an open of the
source to the literal whole tower on that source. -/
theorem actual_retained_rank_open_tower_iso_over_equiv (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (U : Opens X)
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (R : BlowupTower X' Y')
    (e : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage S U)
    (he : IsTowerIso φ R (restrict U S) e) (z : Y') :
    let f := (Subtype.val : U → X) ∘ φ
    retainedDefectRankAlong (f ⁻¹' N) (old.map (f ⁻¹' ·)) (born.map (f ⁻¹' ·)) R z =
      retainedDefectRankAlong N old born S (e z).val := by
  intro f
  let XU := CMfd.of (n := n) U
  let NU := (Subtype.val : U → X) ⁻¹' N
  let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  have hNU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hEU : IsSNCDivisor n (OU ++ BU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hTU : IsTransverse n NU BU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hDenseU : NU ⊆ closure (NU \ ⋃ H ∈ OU ++ BU,H) := by
    simpa only [List.map_append] using HironakaG34NonPureLowDim.open_full_density hdense U
  have hSU := isGeoTestTower_restrict U hN IdealWeightPowers.isCoherent_unitIdeal S hS
  rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := XU) (Subtype.val : U → X)] at hSU
  have hFullU := isGeoTestTower_restrict U isClosedSubmanifold_univ IdealWeightPowers.isCoherent_unitIdeal S hFull
  rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := XU) (Subtype.val : U → X),Set.preimage_univ,
    List.map_append] at hFullU
  have hA := (actual_retained_rank_under_tower_iso hn φ hNU hEU hTU hDenseU
    (restrict U S) hSU hFullU R e he z).2.2
  have hM (L : List (Set X)) :
      (L.map ((Subtype.val : U → X) ⁻¹' ·)).map (φ ⁻¹' ·) = L.map (f ⁻¹' ·) := by
    rw [List.map_map]
    rfl
  rw [show OU.map (φ ⁻¹' ·) = old.map (f ⁻¹' ·) from hM old,
    show BU.map (φ ⁻¹' ·) = born.map (f ⁻¹' ·) from hM born] at hA
  have hOpen := (actual_retained_rank_open_tower_iso hn hN hE hTr hdense U S hS hFull
    (restrict U S) hSU hFullU (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (openPreimage S U) ∞)
    (IsTowerIso.refl_self (restrict U S)) (e z)).2.2
  exact hA.trans hOpen


/-- An actual all-empty history preserves both rank coordinates on the
same physical base point, including every ordered old label. -/
theorem actual_retained_stamp_empty_tower (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    (hEmpty : ResolutionInvariantExt.IsEmptyTower S) (z : Y) :
    let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) (S.proj z)
    (∀ i,retainedProfileAlong N old born S z i = r i) ∧
      retainedInactiveRows N old born (retainedProfileAlong N old born S z) S z =
        inactiveCanonicalRows N old born r (S.proj z) ∧
      retainedDefectRankAlong N old born S z = retainedDefectRank N old born (S.proj z) ∧
      actualDistinctProperCount
        (fun i => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal) z =
        actualDistinctProperCount (oldResidualPart N old born) (S.proj z) := by
  intro r
  obtain ⟨e,hProj⟩ := HironakaOriginalEmptyHeadPrefix.exists_empty_tower_projection S hEmpty
  have he : (e : Y → X) = S.proj := funext hProj
  have hN' : (geoTransformAlong (geometricTemplate N born) S).N = e ⁻¹' N := by
    rw [N_geoTransformAlong]
    change strictAlong S N = e ⁻¹' N
    rw [ContactEmptyPrefix.strictAlong_of_isEmptyTower hN.1 S hEmpty,he]
  have hE' : (geoTransformAlong (geometricTemplate N born) S).E =
      born.map (e ⁻¹' ·) ++ List.replicate S.length ∅ := by
    rw [he]
    exact HironakaOriginalBoundaryCanonicalPrincipalization.boundary_of_all_empty_tower
      (geometricTemplate N born) (fun H hH => hE.1 H (List.mem_append_right old hH)) S hEmpty
  have hOld (i : Fin old.length) : strictAlong S (old.get i) = e ⁻¹' old.get i := by
    rw [ContactEmptyPrefix.strictAlong_of_isEmptyTower (hE.1 _ (List.mem_append_left _ (List.get_mem _ i)))
      S hEmpty,he]
  have hCmp := actual_retained_row_factor_under_endpoint_diffeo hn hN hE hTr hdense hN hE hTr hdense
    (.refl : BlowupTower X X) trivial trivial S hS hFull e (Equiv.refl _) S.length hN' hE' hOld z
  obtain ⟨hMask,hRank⟩ := inactive_mask_and_rank_eq_of_ordered_comparison
    (.refl : BlowupTower X X) S (e z) z (Equiv.refl _) (fun i => (hCmp i).1) (fun i => (hCmp i).2.1)
  change retainedDefectRankAlong N old born S z = retainedDefectRank N old born (e z) at hRank
  have hMask' : retainedInactiveRows N old born (retainedProfileAlong N old born S z) S z =
      inactiveCanonicalRows N old born (fun i => ordinaryTraceOrder N (oldResidualPart N old born i) (e z)) (e z) := by
    change _ = (inactiveCanonicalRows N old born
      (fun i => ordinaryTraceOrder N (oldResidualPart N old born i) (e z)) (e z)).map
        (Equiv.refl (Fin old.length)).toEmbedding at hMask
    simpa using hMask
  refine ⟨?_,?_,hProj z ▸ hRank,?_⟩
  · intro i
    have hI := (hCmp i).1
    change retainedProfileAlong N old born S z i =
      ordinaryTraceOrder N (oldResidualPart N old born i) (e z) at hI
    change retainedProfileAlong N old born S z i =
      ordinaryTraceOrder N (oldResidualPart N old born i) (S.proj z)
    rw [←hProj]
    exact hI
  · rwa [hProj] at hMask'
  · have hPull : (fun i => GermIdeal.pullback (m := n) e (oldResidualPart N old born i)) =
        (fun i => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal) :=
      funext fun i => (hCmp i).2.2
    have hGeo i := retainedResidualMarked_geometry hn hN hE hTr hdense i
    have h := actual_distinct_proper_count_biholo e (oldResidualPart N old born)
      (fun i => (hGeo i).1.isCoherent) z
    rw [hPull,hProj] at h
    exact h

set_option maxHeartbeats 500000 in
/-- The actual rank at a point outside the original closed centre
footprint is exactly the initial rank at its projection. -/
theorem actual_retained_stamp_unchanged_off_closed_footprint (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    {C : Set X} (hC : IsClosed C) (hOver : CentresOver C S)
    (z : Y) (hz : S.proj z ∉ C) :
    let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) (S.proj z)
    (∀ i,retainedProfileAlong N old born S z i = r i) ∧
      retainedInactiveRows N old born (retainedProfileAlong N old born S z) S z =
        inactiveCanonicalRows N old born r (S.proj z) ∧
      retainedDefectRankAlong N old born S z = retainedDefectRank N old born (S.proj z) ∧
      actualDistinctProperCount
        (fun i => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal) z =
        actualDistinctProperCount (oldResidualPart N old born) (S.proj z) := by
  intro r
  let U : Opens X := ⟨Cᶜ,hC.isOpen_compl⟩
  let XU := CMfd.of (n := n) U
  let R := restrict U S
  let p : openPreimage S U := ⟨z,hz⟩
  let ν := (Subtype.val : U → X)
  let NU := ν ⁻¹' N
  let OU := old.map (ν ⁻¹' ·)
  let BU := born.map (ν ⁻¹' ·)
  let e := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (openPreimage S U) ∞
  have hEmpty := isEmptyTower_restrict_of_centresOver U (Set.disjoint_left.mpr
    (fun _ ha hb => ha hb)) S hOver
  have hNU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hEU : IsSNCDivisor n (OU ++ BU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hTU : IsTransverse n NU BU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hDenseU : NU ⊆ closure (NU \ ⋃ H ∈ OU ++ BU,H) := by
    simpa only [List.map_append] using HironakaG34NonPureLowDim.open_full_density hdense U
  have hR := isGeoTestTower_restrict U hN IdealWeightPowers.isCoherent_unitIdeal S hS
  rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := XU) ν] at hR
  have hFullR := isGeoTestTower_restrict U isClosedSubmanifold_univ IdealWeightPowers.isCoherent_unitIdeal S hFull
  rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := XU) ν,Set.preimage_univ,
    List.map_append] at hFullR
  have hOpen := actual_retained_rank_open_tower_iso hn hN hE hTr hdense U S hS hFull
    R hR hFullR e (IsTowerIso.refl_self R) p
  have hEq := actual_retained_stamp_empty_tower (X := XU)
    hn hNU hEU hTU hDenseU R hR hFullR hEmpty p
  let I : BlowupTower X X := .refl
  let IR := restrict U I
  let eI := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (openPreimage I U) ∞
  have hInitial := actual_retained_rank_open_tower_iso hn hN hE hTr hdense U I trivial trivial
    IR trivial trivial eI (IsTowerIso.refl_self IR) (R.proj p)
  let ι : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
  have hProj : (R.proj p).val = S.proj z := proj_restrict U S p
  have hRank : retainedDefectRankAlong NU OU BU R p = retainedDefectRankAlong N old born S z :=
    hOpen.2.2
  have hInitialRank : retainedDefectRank NU OU BU (R.proj p) = retainedDefectRank N old born (R.proj p).val :=
    hInitial.2.2
  refine ⟨?_,?_,hRank.symm.trans (hEq.2.2.1.trans (hInitialRank.trans
    (congrArg (retainedDefectRank N old born) hProj))),?_⟩
  · intro i
    have hSRow : retainedProfileAlong NU OU BU R p (ι i) = retainedProfileAlong N old born S z i :=
      hOpen.1 i
    have hInitialRow : ordinaryTraceOrder NU (oldResidualPart (X := XU) NU OU BU (ι i)) (R.proj p) =
        ordinaryTraceOrder N (oldResidualPart N old born i) (R.proj p).val := hInitial.1 i
    exact hSRow.symm.trans ((hEq.1 (ι i)).trans (hInitialRow.trans
      (congrArg (ordinaryTraceOrder N (oldResidualPart N old born i)) hProj)))
  · apply Finset.map_injective ι.toEmbedding
    let rU := fun i => ordinaryTraceOrder NU (oldResidualPart (X := XU) NU OU BU i) (R.proj p)
    let rOld := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) (R.proj p).val
    have hM := hOpen.2.1
    have hInitialMask : inactiveCanonicalRows (X := XU) NU OU BU rU (R.proj p) =
        (inactiveCanonicalRows N old born rOld (R.proj p).val).map ι.toEmbedding := hInitial.2.1
    change (retainedInactiveRows N old born (retainedProfileAlong N old born S z) S z).map ι.toEmbedding =
      (inactiveCanonicalRows N old born r (S.proj z)).map ι.toEmbedding
    have hInit : inactiveCanonicalRows N old born rOld (R.proj p).val =
        inactiveCanonicalRows N old born r (S.proj z) := by
      unfold rOld r
      rw [hProj]
    rw [←hInit]
    exact hM.symm.trans (hEq.2.1.trans hInitialMask)

  · have hCast {Z : CMfd.{u} n} {a b : ℕ} (hab : a=b) (F : Fin b → GermIdeal n Z) (y : Z) :
        actualDistinctProperCount (fun i : Fin a => F (finCongr hab i)) y =
          actualDistinctProperCount F y := by
      subst b
      rfl
    let FR := fun i : Fin OU.length => (chronologicalMarked (retainedResidualMarked NU OU BU i) R).ideal
    let FI := oldResidualPart (X := XU) NU OU BU
    have hRI := (actual_retained_orders_and_count_open_tower_iso hn hN hE hTr hdense
      U S hS hFull R hR hFullR e (IsTowerIso.refl_self R) p).2.1
    have hIO := (actual_retained_orders_and_count_open_tower_iso hn hN hE hTr hdense
      U I trivial trivial IR trivial trivial eI (IsTowerIso.refl_self IR) (R.proj p)).2.1
    change actualDistinctProperCount (fun i => FR (ι i)) p =
      actualDistinctProperCount (fun i => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal) z at hRI
    change actualDistinctProperCount (fun i => FI (ι i)) (R.proj p) =
      actualDistinctProperCount (oldResidualPart N old born) (R.proj p).val at hIO
    have hCastR : actualDistinctProperCount (fun i => FR (ι i)) p = actualDistinctProperCount FR p :=
      hCast (List.length_map (as := old) _).symm FR p
    have hCastI : actualDistinctProperCount (fun i => FI (ι i)) (R.proj p) =
        actualDistinctProperCount FI (R.proj p) := hCast (List.length_map (as := old) _).symm FI (R.proj p)
    rw [hCastR] at hRI
    rw [hCastI,hProj] at hIO
    exact hRI.symm.trans (hEq.2.2.2.trans hIO)


private theorem actual_retained_family_order_sum (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (z : Y) (hz : z ∈ (geoTransformAlong (geometricTemplate N born) S).N) :
    let A := geoTransformAlong (geometricTemplate N born) S
    let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
    ordinaryTraceOrder A.N (relativeIdealListProduct A.N (List.ofFn F)) z =
      ∑ i,retainedProfileAlong N old born S z i := by
  intro A F
  have hProduct : (retainedProductMarked N old born 0 S).ideal =
      relativeIdealListProduct A.N (List.ofFn F) := by
    unfold retainedProductMarked
    dsimp only
    congr 1
    conv_lhs => rw [←List.ofFn_get old,List.map_ofFn]
    rfl
  rw [←hProduct]
  exact (retained_product_geometry hn hN hE hTr hdense 0 S hS).2.2.2 z hz

/-- The true distinct defect is unchanged off the actual closed footprint.
This includes both the transformed carrier and its full quotient count. -/
theorem actual_retained_defect_unchanged_off_closed_footprint (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : BlowupTower X Y) (hS : IsGeoTestTower (geometricTemplate N born) S)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) S)
    {C : Set X} (hC : IsClosed C) (hOver : CentresOver C S)
    (z : Y) (hz : S.proj z ∉ C) :
    z ∈ retainedDistinctDefect N old born S ↔
      S.proj z ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) := by
  let U : Opens X := ⟨Cᶜ,hC.isOpen_compl⟩
  let R := restrict U S
  let p : openPreimage S U := ⟨z,hz⟩
  let ν := (Subtype.val : U → X)
  have hNU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hEmpty := isEmptyTower_restrict_of_centresOver U (Set.disjoint_left.mpr
    (fun _ ha hb => ha hb)) S hOver
  have hCarrier : z ∈ (geoTransformAlong (geometricTemplate N born) S).N ↔ S.proj z ∈ N := by
    rw [N_geoTransformAlong]
    change p.val ∈ strictAlong S N ↔ S.proj p.val ∈ N
    rw [←show (R.proj p).val = S.proj p.val from proj_restrict U S p]
    have hSet := (strictAlong_restrict U S N).symm.trans
      (ContactEmptyPrefix.strictAlong_of_isEmptyTower hNU.1 R hEmpty)
    change p ∈ (Subtype.val : openPreimage S U → Y) ⁻¹' strictAlong S N ↔ p ∈ R.proj ⁻¹' (ν ⁻¹' N)
    rw [hSet]
  have hStamp := actual_retained_stamp_unchanged_off_closed_footprint hn hN hE hTr hdense S hS hFull hC hOver z hz
  let A := geoTransformAlong (geometricTemplate N born) S
  let F := fun i : Fin old.length => (chronologicalMarked (retainedResidualMarked N old born i) S).ideal
  change (z ∈ A.N ∧ actualDistinctProperCount F z <
    ordinaryTraceOrder A.N (relativeIdealListProduct A.N (List.ofFn F)) z) ↔
      S.proj z ∈ N ∧ actualDistinctProperCount (oldResidualPart N old born) (S.proj z) <
        ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn (oldResidualPart N old born))) (S.proj z)
  have hOrder (hzN : z ∈ A.N) :
      ordinaryTraceOrder A.N (relativeIdealListProduct A.N (List.ofFn F)) z =
        ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn (oldResidualPart N old born))) (S.proj z) := by
    have hNew := actual_retained_family_order_sum hn hN hE hTr hdense S hS z hzN
    have hOld := actual_retained_family_order_sum hn hN hE hTr hdense
      (.refl : BlowupTower X X) trivial (S.proj z) (hCarrier.mp hzN)
    exact hNew.trans ((Finset.sum_congr rfl (fun i _ => hStamp.1 i)).trans hOld.symm)
  refine ⟨fun h => ⟨hCarrier.mp h.1,?_⟩,fun h => ⟨hCarrier.mpr h.1,?_⟩⟩
  · have hLt := h.2
    rwa [hStamp.2.2.2,hOrder h.1] at hLt
  · rw [hStamp.2.2.2,hOrder (hCarrier.mpr h.1)]
    exact h.2

end
end Hironaka.HironakaG4RetainedRankTowerIso
