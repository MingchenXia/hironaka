import Hironaka.Resolution.HironakaActualProcessedMaskControlledSum
import Hironaka.Resolution.HironakaG4SharpBadFootprint
import Hironaka.Resolution.HironakaOriginalCompactCosupportGlobalScheduler
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Resolution.HironakaG4CompactPositiveFullMarked
import Hironaka.Resolution.HironakaG4UniformRowsMaskBound

/-! One actual finite coherent-SUM block on the same original processed rows.
Source-first proof: `hironaka-g4-processed-mask-finite-block-20261101.tex`.
Full sharp joint G4 termination and all-mask/lower-count scheduling remain open. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualProcessedMaskFiniteBlock
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  NormalCrossings NormalCrossingsComparison MonomialPartAlong DivisorExponentAlong
  GermIdealOrder MonomialCaseAlong MonomialCase BoundaryCount
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4PreparedCentreCoordinates
  HironakaG4MonomialFamilyInvariant HironakaActualProcessedMaskControlledSum
  HironakaG4CompactWholeMonomialMaskPhase HomogenizedGlueingTower RestrictEmptyTower
  HironakaG4CompactPositivePhase HironakaG4CompactPositiveFullMarked HironakaG4DivisorExponentIdealMonotone
  RestrictLeCalculus

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Actual canonical old factor at the unchanged ORIGINAL index. -/
def oldFactor (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (i : Fin E.length) : GermIdeal n Y :=
  let A := geoTransformAlong (geometricTemplate W []) T
  monomialPartAlong n A.N
    (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E

/-- All columns of the actual current born list, with the same original rows. -/
def factorMatrix (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (x : Y) :
    Fin E.length → Fin (geoTransformAlong (geometricTemplate W []) T).E.length → ℕ :=
  fun i j => divExpAlong n (geoTransformAlong (geometricTemplate W []) T).N
    (oldFactor W E T i) ((geoTransformAlong (geometricTemplate W []) T).E.get j) x

/-- True support of the same original chronological residual row. -/
def residualSupport (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (i : Fin E.length) : Set Y :=
  (geoTransformAlong (geometricTemplate W []) T).N ∩
    (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus

private def maskSum {ι : Type*} (D : ι → GermIdeal n Y) (P : Finset ι) : GermIdeal n Y :=
  ⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩

private theorem cosupport_maskSum_one {ι : Type*} (D : ι → GermIdeal n Y)
    (hc : ∀ i,(D i).IsCoherent) (P : Finset ι) (N : Set Y) (x : Y) :
    x ∈ cosupport n N (maskSum D P) 1 ↔
      x ∈ N ∧ ∀ i ∈ P,x ∈ cosupport n N (D i) 1 := by
  have hRow (i : ι) : x ∈ cosupport n N (D i) 1 ↔
      x ∈ N ∧ ∀ g,(D i).mem x g → g x=0 := by
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hc i) hg)]
    rfl
  rw [cosupport_one (𝔞 := maskSum D P) (fun _ _ hg => hg.1)]
  constructor
  · rintro ⟨hxN,hx⟩
    refine ⟨hxN,fun i hi => (hRow i).mpr ⟨hxN,fun g hg => hx g ?_⟩⟩
    exact isInSpanAt_self (S := fun f => ∃ j ∈ P,(D j).mem x f) ⟨i,hi,hg⟩
      (GermIdeal.IsCoherent.holomorphicAt_mem (hc i) hg)
  · rintro ⟨hxN,hx⟩
    refine ⟨hxN,?_⟩
    intro g hg
    obtain ⟨_hg,k,s,a,hs,_ha,hEq⟩ := hg
    rw [hEq.self_of_nhds]
    apply Finset.sum_eq_zero
    intro j _hj
    obtain ⟨i,hi,hsi⟩ := hs j
    rw [((hRow i).mp (hx i hi)).2 _ hsi,mul_zero]

private theorem oldFactor_geometry (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) :
    ∀ i : Fin E.length,(oldFactor W E T i).IsCoherent ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
        IsNonzeroAlongAt (geoTransformAlong (geometricTemplate W []) T).N (oldFactor W E T i) y) ∧
      IsMonomialAlong n (geoTransformAlong (geometricTemplate W []) T).N
        (oldFactor W E T i) (geoTransformAlong (geometricTemplate W []) T).E := by
  have h := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hBorn := isSNCDivisor_of_sublist h.2.1 (List.sublist_append_right _ _)
  intro i
  have hp := NonmonomialTransformAlong.parts_hypotheses hn
    (⟨_,_,restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
      (vanishingIdeal (n := n) (strictAlong T (E.get i))),1⟩ : MarkedIdeal n Y)
    ⟨h.1,(h.2.2.2.2 i).1,hBorn,h.2.2.1⟩ (h.2.2.2.2 i).2.1
  exact ⟨hp.2.1,hp.2.2.1,hp.2.2.2.1⟩
private theorem exponent_zero_of_not_mem {N H : Set X} {I : GermIdeal n X}
    (hc : IsClosed (N ∩ H)) {x : X} (hx : x ∉ H) :
    divExpAlong n N I H x=0 := by
  have hnot : ¬∃ e,¬IsDivNearAlong n N I H (e+1) x := by
    rintro ⟨e,he⟩
    exact he (isDivNearAlong_of_notMem hc (fun h => hx h.2) (e+1))
  unfold divExpAlong
  rw [dif_neg hnot]

private theorem row_cosupport_iff (hn : 0<n) {N : Set X}
    {B : List (Set X)} {D : GermIdeal n X} (hN : IsClosedSubmanifold n N)
    (hB : IsSNCDivisor n B) (hTr : IsTransverse n N B) (hc : D.IsCoherent)
    (hne : ∀ y ∈ N,IsNonzeroAlongAt N D y) (hm : IsMonomialAlong n N D B)
    {x : X} (hx : x ∈ N) :
    x ∈ cosupport n N D 1 ↔ 0<∑ j : Fin B.length,divExpAlong n N D (B.get j) x := by
  classical
  rw [mem_cosupport_iff_of_isMonomialAlong hn hN hB hTr hc hne hm 1 hx]
  have hsum : (∑ i ∈ memberIdx B x,expDataAlong n N D B x i)=
      ∑ j : Fin B.length,divExpAlong n N D (B.get j) x := by
    rw [memberIdx,Finset.sum_map]
    simp only [Fin.valEmbedding_apply,expDataAlong,Fin.eta]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [dif_pos j.isLt]
    change (if x ∈ B.get j then divExpAlong n N D (B.get j) x else 0)=
      divExpAlong n N D (B.get j) x
    by_cases hxj : x ∈ B.get j
    · simp only [if_pos hxj]
    · simp only [if_neg hxj]
      exact (exponent_zero_of_not_mem (hN.1.inter (hB.1 _ (List.get_mem B j))) hxj).symm
  rw [hsum]
  omega


private theorem canonical_proper_subset_bad (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born))
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length) :
    {x | x ∈ N ∧ ¬(oldMonomialPart N old born i).mem x 1} ⊆
      originalSharpBadLocus (n := n) N (old ++ born) := by
  let k : Fin (old ++ born).length := ⟨i.val,by simp only [List.length_append]; omega⟩
  let L : List (Fin (old ++ born).length) := List.ofFn fun j : Fin born.length =>
    ⟨old.length+j.val,by simp only [List.length_append]; omega⟩
  have hOld : (old ++ born).get k=old.get i := by
    simp only [k,List.get_eq_getElem,List.getElem_append_left i.isLt]
  have hBorn : L.map (old ++ born).get=born := by
    calc
      L.map (old ++ born).get=List.ofFn (fun j : Fin born.length => born.get j) := by
        dsimp only [L]
        rw [List.map_ofFn]
        congr 1
        funext j
        simp only [Function.comp_apply,List.get_eq_getElem]
        rw [List.getElem_append_right (Nat.le_add_right old.length j.val)]
        simp only [Nat.add_sub_cancel_left]
      _=born := List.ofFn_get born
  have hL : ∀ j ∈ L,k ≠ j := by
    intro j hj
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hj
    intro h
    have hval := congrArg Fin.val h
    change i.val=old.length+a.val at hval
    omega
  have hBad := HironakaG4ActiveMonomialSharpBad.active_old_monomial_subset_originalSharpBadLocus
    hn hN hE hdense k L hL
  simpa only [hOld,hBorn,oldMonomialPart,oldTraceIdeal] using hBad


/-- The actual processed mask cosupport is exactly the joint row activity. -/
theorem mem_processed_mask_cosupport_iff (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (P : Finset (Fin E.length)) (x : Y) :
    x ∈ (processedMaskMarked W E T P).cosupp ↔
      x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧
        P ⊆ properRows (factorMatrix W E T x) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  have h := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hBorn := isSNCDivisor_of_sublist h.2.1 (List.sublist_append_right _ _)
  have hp := oldFactor_geometry hn hW hE hdense T hT hFull
  change x ∈ cosupport n A.N (maskSum (oldFactor W E T) P) 1 ↔ _
  rw [cosupport_maskSum_one (oldFactor W E T) (fun i => (hp i).1) P A.N x]
  constructor
  · rintro ⟨hx,hall⟩
    refine ⟨hx,fun i hi => ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (row_cosupport_iff hn h.1 hBorn h.2.2.1 (hp i).1 (hp i).2.1 (hp i).2.2 hx).mp (hall i hi)⟩
  · rintro ⟨hx,hall⟩
    refine ⟨hx,fun i hi => ?_⟩
    exact (row_cosupport_iff hn h.1 hBorn h.2.2.1 (hp i).1 (hp i).2.1 (hp i).2.2 hx).mpr
      (Finset.mem_filter.mp (hall hi)).2

/-- The actual selected mask cosupport is closed on every geometric test prefix. -/
theorem isClosed_actual_processed_mask_cosupport (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (P : Finset (Fin E.length)) : IsClosed (processedMaskMarked W E T P).cosupp := by
  let A := geoTransformAlong (geometricTemplate W []) T
  have h := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hParts := oldFactor_geometry hn hW hE hdense T hT hFull
  have hCosEq : (processedMaskMarked W E T P).cosupp=
      A.N ∩ ⋂ i ∈ P,cosupport n A.N (oldFactor W E T i) 1 := by
    ext x
    change x ∈ cosupport n A.N (maskSum (oldFactor W E T) P) 1 ↔ _
    rw [cosupport_maskSum_one (oldFactor W E T) (fun i => (hParts i).1) P A.N x]
    simp only [Set.mem_inter_iff,Set.mem_iInter]
  rw [hCosEq]
  exact h.1.1.inter (isClosed_iInter fun i => isClosed_iInter fun _hi =>
    GiraudAlong.isClosed_cosupport_along (hParts i).1 h.1 1)

/-- The actual high-count locus is closed, as a finite union of actual
processed mask cosupports of the indicated cardinality. -/
theorem isClosed_actual_processed_high_count (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) (q : ℕ) :
    IsClosed {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧
      q ≤ tauD (factorMatrix W E T x)} := by
  classical
  let F := (Finset.univ : Finset (Fin E.length)).powersetCard q
  have hEq : {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧
      q ≤ tauD (factorMatrix W E T x)} =
      ⋃ P ∈ F,(processedMaskMarked W E T P).cosupp := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨hxN,hxQ⟩
      have hCard : q ≤ (properRows (factorMatrix W E T x)).card := hxQ
      obtain ⟨P,hSub,hP⟩ := Finset.exists_subset_card_eq hCard
      refine ⟨P,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hP⟩,?_⟩
      exact (mem_processed_mask_cosupport_iff hn hW hE hdense T hT hFull P x).mpr ⟨hxN,hSub⟩
    · rintro ⟨P,hPF,hxP⟩
      have hP := (Finset.mem_powersetCard.mp hPF).2
      obtain ⟨hxN,hSub⟩ := (mem_processed_mask_cosupport_iff hn hW hE hdense T hT hFull P x).mp hxP
      exact ⟨hxN,by simpa only [tauD,hP] using Finset.card_le_card hSub⟩
  rw [hEq]
  exact isClosed_biUnion_finset fun P _ => isClosed_actual_processed_mask_cosupport hn hW hE hdense T hT hFull P

/-- Compact high-count support at a lower threshold controls every higher
threshold at the same actual prefix. -/
theorem isCompact_actual_high_count_of_lower (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (p q : ℕ) (hpq : p ≤ q)
    (hK : IsCompact {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧
      p ≤ tauD (factorMatrix W E T x)}) :
    IsCompact {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧
      q ≤ tauD (factorMatrix W E T x)} := by
  exact hK.of_isClosed_subset (isClosed_actual_processed_high_count hn hW hE hdense T hT hFull q)
    (fun _ hx => ⟨hx.1,hpq.trans hx.2⟩)

/-- Proper-row monotonicity transports compact high-count support along the
same actual continuation by proper inverse image. -/
theorem isCompact_actual_high_count_of_forward (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (R : BlowupTower Y Z)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hU : IsGeoTestTower (geometricTemplate W []) (T.append R))
    (hFullU : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R))
    (hRows : ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
      properRows (factorMatrix W E (T.append R) z) ⊆ properRows (factorMatrix W E T (R.proj z)))
    (q : ℕ) (hK : IsCompact {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧
      q ≤ tauD (factorMatrix W E T x)}) :
    IsCompact {z | z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N ∧
      q ≤ tauD (factorMatrix W E (T.append R) z)} := by
  apply ((HironakaLocalPrincipalization.isProperMap_proj R).isCompact_preimage hK).of_isClosed_subset
    (isClosed_actual_processed_high_count hn hW hE hdense (T.append R) hU hFullU q)
  intro z ⟨hzN,hzQ⟩
  have hN := (HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull).1.1
  have hNid : (geoTransformAlong (geometricTemplate W []) (T.append R)).N =
      strictAlong R (geoTransformAlong (geometricTemplate W []) T).N := by
    rw [geoTransformAlong_append]
    exact N_geoTransformAlong _ _
  have hzN' := hNid ▸ hzN
  refine ⟨MemberInterTowerAlong.strictAlong_subset_preimage R hN hzN',?_⟩
  exact hzQ.trans (Finset.card_le_card (hRows z hzN))

/-- Every actual q-mask lies in the current high-count locus. -/
theorem actual_processed_mask_subset_high_count (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (q : ℕ)
    (P : Finset (Fin E.length)) (hCard : P.card=q) :
    (processedMaskMarked W E T P).cosupp ⊆
      {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧ q ≤ tauD (factorMatrix W E T x)} := by
  intro x hx
  have ⟨hxN,hRows⟩ := (mem_processed_mask_cosupport_iff hn hW hE hdense T hT hFull P x).mp hx
  refine ⟨hxN,?_⟩
  have hCardLe := Finset.card_le_card hRows
  simpa only [hCard,tauD] using hCardLe


/-- Compactness of a current high-count locus bounds every literal mask
of that size, even if the full sharp-bad locus is noncompact. -/
theorem isCompact_actual_processed_mask_of_compact_high_count (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (q : ℕ) (hHigh : IsCompact {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧
      q ≤ tauD (factorMatrix W E T x)})
    (P : Finset (Fin E.length)) (hCard : P.card=q) :
    IsCompact (processedMaskMarked W E T P).cosupp := by
  exact hHigh.of_isClosed_subset
    (isClosed_actual_processed_mask_cosupport hn hW hE hdense T hT hFull P)
    (actual_processed_mask_subset_high_count hn hW hE hdense T hT hFull q P hCard)

/-- The later literal mask support lies over the initial one along any
actual test continuation whose original proper rows are monotone. -/
theorem actual_processed_mask_subset_preimage_of_forward (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (R : BlowupTower Y Z)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hU : IsGeoTestTower (geometricTemplate W []) (T.append R))
    (hFullU : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R))
    (hRows : ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
      properRows (factorMatrix W E (T.append R) z) ⊆ properRows (factorMatrix W E T (R.proj z)))
    (P : Finset (Fin E.length)) :
    (processedMaskMarked W E (T.append R) P).cosupp ⊆
      R.proj ⁻¹' (processedMaskMarked W E T P).cosupp := by
  intro z hz
  have ⟨hzN,hzRows⟩ := (mem_processed_mask_cosupport_iff hn hW hE hdense (T.append R) hU hFullU P z).mp hz
  apply (mem_processed_mask_cosupport_iff hn hW hE hdense T hT hFull P (R.proj z)).mpr
  have hNmap := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hNid : (geoTransformAlong (geometricTemplate W []) (T.append R)).N =
      strictAlong R (geoTransformAlong (geometricTemplate W []) T).N := by
    rw [geoTransformAlong_append]
    exact N_geoTransformAlong _ _
  have hzN' := hNid ▸ hzN
  refine ⟨?_,hzRows.trans (hRows z hzN)⟩
  exact MemberInterTowerAlong.strictAlong_subset_preimage R hNmap.1.1 hzN'


/-- Proper-row monotonicity transports compactness of the very same mask
support along an actual tower, without compactness of the full bad locus. -/
theorem isCompact_actual_processed_mask_of_forward (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (R : BlowupTower Y Z)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hU : IsGeoTestTower (geometricTemplate W []) (T.append R))
    (hFullU : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R))
    (hRows : ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
      properRows (factorMatrix W E (T.append R) z) ⊆ properRows (factorMatrix W E T (R.proj z)))
    (P : Finset (Fin E.length)) (hCompact : IsCompact (processedMaskMarked W E T P).cosupp) :
    IsCompact (processedMaskMarked W E (T.append R) P).cosupp := by
  exact ((HironakaLocalPrincipalization.isProperMap_proj R).isCompact_preimage hCompact).of_isClosed_subset
    (isClosed_actual_processed_mask_cosupport hn hW hE hdense (T.append R) hU hFullU P)
    (actual_processed_mask_subset_preimage_of_forward hn hW hE hdense T R hT hFull hU hFullU hRows P)

/-- Compactness of the literal present SUM support is derived from the actual
original sharp footprint; no whole-carrier compactness is assumed. -/
theorem isCompact_actual_processed_mask_cosupport (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (P : Finset (Fin E.length)) (hP : P.Nonempty) :
    IsCompact (processedMaskMarked W E T P).cosupp := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  have h := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hParts := oldFactor_geometry hn hW hE hdense T hT hFull
  obtain ⟨hBad,_hOver⟩ := HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
    hW.1 hE.1 T hSharp
  have hBoundary := HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T
  have hN : A.N=strictAlong T W := N_geoTransformAlong _ _
  have hBadSub : originalSharpBadLocus (n := n) A.N (old ++ A.E) ⊆
      T.proj ⁻¹' originalSharpBadLocus (n := n) W E := by
    rw [hN,←hBoundary]
    exact hBad
  have hCompactBad : IsCompact (originalSharpBadLocus (n := n) A.N (old ++ A.E)) :=
    ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
      (isClosed_originalSharpBadLocus h.1.1 h.2.1.1) hBadSub
  have hCosEq : (processedMaskMarked W E T P).cosupp=
      A.N ∩ ⋂ i ∈ P,cosupport n A.N (oldFactor W E T i) 1 := by
    ext x
    change x ∈ cosupport n A.N (maskSum (oldFactor W E T) P) 1 ↔ _
    rw [cosupport_maskSum_one (oldFactor W E T) (fun i => (hParts i).1) P A.N x]
    simp only [Set.mem_inter_iff,Set.mem_iInter]
  have hClosed := isClosed_actual_processed_mask_cosupport hn hW hE hdense T hT hFull P
  refine hCompactBad.of_isClosed_subset hClosed ?_
  intro x hx
  have hxRows := (mem_processed_mask_cosupport_iff hn hW hE hdense T hT hFull P x).mp hx
  obtain ⟨i,hi⟩ := hP
  have hxDi : x ∈ cosupport n A.N (oldFactor W E T i) 1 := by
    have hc := hCosEq ▸ hx
    exact mem_iInter.mp (mem_iInter.mp hc.2 i) hi
  have hNot : ¬(oldFactor W E T i).mem x 1 := by
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hParts i).1 hg)] at hxDi
    exact fun hu => one_ne_zero (hxDi.2 1 hu)
  let oi : Fin old.length := ⟨i.val,by simp [old]⟩
  have hGet : old.get oi=strictAlong T (E.get i) := by simp [old,oi]
  apply canonical_proper_subset_bad hn h.1 h.2.1 h.2.2.2.1 oi
  refine ⟨hxRows.1,?_⟩
  change ¬(monomialPartAlong n A.N
    (restrictOn n A.N (vanishingIdeal (n := n) (old.get oi))) A.E).mem x 1
  rw [hGet]
  exact hNot


/-- The native state certified at every head of a processed mask block. -/
def processedAt (W : Set X) (E : List (Set X)) (P : Finset (Fin E.length))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) : Prop :=
  let A := geoTransformAlong (geometricTemplate W []) T
  IsGeoTestTower (geometricTemplate W []) T ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
    CurrentSharpCentres W E T ∧
    (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1) ∧
    (∀ i : Fin E.length,HasNormalCrossings n (residualSupport W E T i)
      ((E.map (strictAlong T)).eraseIdx i.val ++ A.E)) ∧
    (∀ i : Fin E.length,residualSupport W E T i ⊆ closure (residualSupport W E T i \
      ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H)) ∧
    (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x) ∧
    ∀ x ∈ A.N,tauD (factorMatrix W E T x) ≤ P.card

/-- Read the complete processed state, chronological residual pullbacks,
and row activity along any actual test tower of the current mask. -/
theorem actual_processed_mask_test_history (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (P : Finset (Fin E.length)) (hP : 2 ≤ P.card)
    (hStart : processedAt W E P T) :
    ∀ {Z : CMfd.{u} n} (R : BlowupTower Y Z),
      IsGeoTestTower (processedMaskMarked W E T P) R →
      processedAt W E P (T.append R) ∧
        geoTransformAlong (processedMaskMarked W E T P) R=
          processedMaskMarked W E (T.append R) P ∧
        (∀ i : Fin E.length,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal=
            vanishingIdeal (n := n) (R.proj ⁻¹' residualSupport W E T i) ∧
          residualSupport W E (T.append R) i=R.proj ⁻¹' residualSupport W E T i) ∧
        ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
          properRows (factorMatrix W E (T.append R) z) ⊆
            properRows (factorMatrix W E T (R.proj z)) := by
  intro Z R
  induction R with
  | refl =>
    intro _hR
    refine ⟨hStart,rfl,?_,fun z _hz => Finset.Subset.refl _⟩
    intro i
    rcases hStart with ⟨hT,hFull,_hSharp,hOrd,hNC,hDenseS,_hPrepared,_hBound⟩
    have hProtect := HironakaG4ProtectedResidualEndpoint.actual_original_selected_endpoint_protection
      hn hW hE hdense i T hT hFull (fun x hx => hOrd x hx i) (hNC i) (hDenseS i)
    exact ⟨hProtect.2.1,rfl⟩
  | @step Z' Z R C π hπ ih =>
    intro hR
    obtain ⟨hCurrent,hEq,hRows,hActivity⟩ := ih hR.1
    rcases hCurrent with ⟨hUTest,hUFull,hUSharp,hUOrd,hUNC,hUDense,hUPrepared,hUBound⟩
    let U := T.append R
    let A := geoTransformAlong (geometricTemplate W []) U
    let U' := BlowupTower.step U C π hπ
    let A' := geoTransformAlong (geometricTemplate W []) U'
    have hAdm : (processedMaskMarked W E U P).IsAdmissibleCentre C := by
      rw [←hEq]
      exact hR.2
    have hRecordStep := (actual_processed_mask_controlled_record hn hW hE hdense
      U hUTest hUFull hUOrd hUNC hUDense P hP hUBound).2 C π hπ hAdm |>.1
    obtain ⟨_hDomain,hStep⟩ :=
      HironakaG4ProcessedSupportHighCountStep.actual_processed_original_high_count_step
        (Z := Z) hn hW hE hdense U hUTest hUFull hUOrd hUNC hUDense hUPrepared P hP hUBound
    obtain ⟨_hCNC,hSharp,hDisjoint,hTest',hFull',hRowsStep,hOrd',hActive',hPrepared'⟩ :=
      hStep C π hπ hAdm
    have hGeometry := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
      hn hW hE hdense U hUTest hUFull
    have hSupportStep (i : Fin E.length) :
        residualSupport W E U' i=π ⁻¹' residualSupport W E U i := by
      have hSub : π ⁻¹' residualSupport W E U i ⊆ A'.N := by
        intro z hz
        change z ∈ geoStrictTransform π C A.N
        exact subset_closure ⟨hz.1,fun hzC => Set.disjoint_left.mp (hDisjoint i) hzC hz⟩
      change A'.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U').ideal.zeroLocus=_
      rw [(hRowsStep i).2.1,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hRowsStep i).1.1]
      exact Set.inter_eq_right.mpr hSub
    have hNC' (i : Fin E.length) : HasNormalCrossings n (residualSupport W E U' i)
        ((E.map (strictAlong U')).eraseIdx i.val ++ A'.E) := by
      rw [hSupportStep i]
      exact (hRowsStep i).2.2.2.1
    have hDense' (i : Fin E.length) : residualSupport W E U' i ⊆
        closure (residualSupport W E U' i \
          ⋃ H ∈ (E.map (strictAlong U')).eraseIdx i.val ++ A'.E,H) := by
      rw [hSupportStep i]
      exact (hRowsStep i).2.2.2.2
    have hSharp' : CurrentSharpCentres W E U' := by
      refine ⟨hUSharp,?_⟩
      have hN : A.N=strictAlong U W := N_geoTransformAlong _ _
      rw [←hN,HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E U]
      exact hSharp
    have hState' : processedAt W E P U' :=
      ⟨hTest',hFull',hSharp',hOrd',hNC',hDense',hPrepared',
        fun z hz => (hActive' z hz).2⟩
    refine ⟨hState',?_,?_,?_⟩
    · change (geoTransformAlong (processedMaskMarked W E T P) R).geoTransform C π=
        processedMaskMarked W E U' P
      rw [hEq]
      exact hRecordStep
    · intro i
      have hIdeal := (hRowsStep i).2.1
      have hSupport := hSupportStep i
      change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U').ideal=
        vanishingIdeal (n := n) (π ⁻¹' residualSupport W E U i) at hIdeal
      rw [(hRows i).2] at hIdeal hSupport
      exact ⟨hIdeal,hSupport⟩
    · intro z hz
      have hMap : π z ∈ A.N :=
        geoStrictTransform_subset_preimage hπ.contMDiff.continuous hGeometry.1.1 hz
      exact ((hActive' z hz).1).trans (hActivity (π z) hMap)



/-- A processed mask is resolved on one actual sharp test history when its
positive nonmonomial support is compact and all source row exponents are bounded. -/
theorem exists_actual_processed_mask_block_of_compact_positive
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hNC : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (hPrepared : let A := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x)
    (P : Finset (Fin E.length)) (hP : 2 ≤ P.card)
    (hPositive : IsCompact (positiveSupport (processedMaskMarked W E T P)))
    (hRowsBound : ∃ B,∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,∀ j : Fin (geoTransformAlong (geometricTemplate W []) T).E.length,
        divExpAlong n (geoTransformAlong (geometricTemplate W []) T).N
          (oldFactor W E T i) ((geoTransformAlong (geometricTemplate W []) T).E.get j) x ≤ B)
    (hBound : let A := geoTransformAlong (geometricTemplate W []) T
      let D := fun i : Fin E.length => monomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
      ∀ x ∈ A.N,tauD (fun i j => divExpAlong n A.N (D i) (A.E.get j) x) ≤ P.card) :
    let M := processedMaskMarked W E T P
    ∃ (V : CMfd.{u} n) (P₀ : BlowupTower Y V) (Z : CMfd.{u} n) (S : BlowupTower V Z),
      ResolutionInvariantSpec.IsCanonical M ((CanonicalCentres.invFamily hn (n+1)).inv M) P₀ ∧
      IsGeoTestTower M P₀ ∧ CentresOver (positiveSupport M) P₀ ∧
      IsMonomialAlong n (geoTransformAlong M P₀).N (geoTransformAlong M P₀).ideal (geoTransformAlong M P₀).E ∧
      ResolutionDriver.IsCanonicalSegment (geoTransformAlong M P₀)
        (fun {Q} R => MonomialStepAlong.towerInvAlong (geoTransformAlong M P₀) (Y := Q) R) S ∧
      let R := P₀.append S
      IsGeoResolution M R ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let U := T.append Q
        let A := geoTransformAlong (geometricTemplate W []) U
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        RestrictEmptyTower.CentresOver
          (originalSharpBadLocus (n := n) W E) U ∧
        geoTransformAlong M Q=processedMaskMarked W E U P ∧
        (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal x ≤ 1) ∧
        (∀ i : Fin E.length,HasNormalCrossings n (residualSupport W E U i)
          ((E.map (strictAlong U)).eraseIdx i.val ++ A.E)) ∧
        (∀ i : Fin E.length,residualSupport W E U i ⊆ closure (residualSupport W E U i \
          ⋃ H ∈ (E.map (strictAlong U)).eraseIdx i.val ++ A.E,H)) ∧
        (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong U)) A.E x) ∧
        (∀ x ∈ A.N,tauD (factorMatrix W E U x) ≤ P.card) ∧
        (∀ i : Fin E.length,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal=
            vanishingIdeal (n := n) (Q.proj ⁻¹' residualSupport W E T i) ∧
          residualSupport W E U i=Q.proj ⁻¹' residualSupport W E T i) ∧
        ∀ z ∈ A.N,properRows (factorMatrix W E U z) ⊆
          properRows (factorMatrix W E T (Q.proj z))) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        ¬P ⊆ properRows (factorMatrix W E (T.append R) z) := by
  let M := processedMaskMarked W E T P
  have hStart : processedAt W E P T :=
    ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,hPrepared,hBound⟩
  have hDom := (actual_processed_mask_controlled_record (Z := Y) hn hW hE hdense
    T hT hFull hOrd hNC hDenseS P hP hBound).1
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i,hi⟩ := hPne
  obtain ⟨B,hB⟩ := hRowsBound
  have hGeom := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  have hParts := oldFactor_geometry hn hW hE hdense T hT hFull
  have hLe : (oldFactor W E T i).Le M.ideal := by
    intro x g hg
    change IsInSpanAt (n := n) (fun f => ∃ j ∈ P,(oldFactor W E T j).mem x f) x g
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨i,hi,hg⟩
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem (hParts i).1 hg)
  have hExp : ∀ x ∈ M.cosupp,∀ j : Fin M.E.length,x ∈ M.E.get j →
      divExpAlong n M.N M.ideal (M.E.get j) x ≤ B := by
    intro x hx j hj
    have hxN := M.cosupp_subset_N hx
    exact (divExpAlong_le_of_ideal_le hGeom.1 hDom.isWellFormed.isCoherent (hParts i).1
      hLe hxN hj ((hParts i).2.1 x hxN)).trans (hB x hxN i j)
  obtain ⟨V,P₀,Z,S,hCan,hTestP,hOverP,hMono,hSegment,hRes,_hOver,_hHol,_hProper,_hIso⟩ :=
    exists_mark_one_phased_resolution_of_compact_positive_support hn n M hDom rfl hPositive B hExp
  let R := P₀.append S
  have hEnd := actual_processed_mask_test_history hn hW hE hdense T P hP hStart R hRes.1
  refine ⟨V,P₀,Z,S,hCan,hTestP,hOverP,hMono,hSegment,hRes,?_,?_⟩
  · intro k
    let Q := BlowupTowerSplit.head R k
    have hQ : IsGeoTestTower M Q :=
      ((BlowupTowerSplit.isGeoTestTower_iff_head_tail M R k).mp hRes.1).1
    obtain ⟨hState,hEq,hRows,hActivity⟩ :=
      actual_processed_mask_test_history hn hW hE hdense T P hP hStart Q hQ
    rcases hState with ⟨hTestU,hFullU,hSharpU,hOrdU,hNCU,hDenseU,hPreparedU,hBoundU⟩
    have hOver := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
      hW.1 hE.1 (T.append Q) hSharpU).2
    exact ⟨hTestU,hFullU,hSharpU,hOver,hEq,hOrdU,hNCU,hDenseU,hPreparedU,hBoundU,hRows,hActivity⟩
  · intro z hz hMask
    have hEmpty : (processedMaskMarked W E (T.append R) P).cosupp=∅ := by
      rw [←hEnd.2.1]
      exact hRes.2
    have hCos := (mem_processed_mask_cosupport_iff hn hW hE hdense (T.append R)
      hEnd.1.1 hEnd.1.2.1 P z).mpr ⟨hz,hMask⟩
    exact Set.notMem_empty z (hEmpty ▸ hCos)

/-- ONE internally selected native finite coherent-SUM resolution erases its
original mask, preserving every actual prefix and processed original row. -/
theorem exists_actual_processed_mask_finite_block_of_compact_mask
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hNC : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (hPrepared : let A := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x)
    (P : Finset (Fin E.length)) (hP : 2 ≤ P.card)
    (hCompact : IsCompact (processedMaskMarked W E T P).cosupp)
    (hBound : let A := geoTransformAlong (geometricTemplate W []) T
      let D := fun i : Fin E.length => monomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
      ∀ x ∈ A.N,tauD (fun i j => divExpAlong n A.N (D i) (A.E.get j) x) ≤ P.card) :
    let M := processedMaskMarked W E T P
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      ResolutionInvariantSpec.IsCanonical M ((CanonicalCentres.invFamily hn (n+1)).inv M) R ∧
      IsGeoResolution M R ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let U := T.append Q
        let A := geoTransformAlong (geometricTemplate W []) U
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        RestrictEmptyTower.CentresOver
          (originalSharpBadLocus (n := n) W E) U ∧
        geoTransformAlong M Q=processedMaskMarked W E U P ∧
        (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal x ≤ 1) ∧
        (∀ i : Fin E.length,HasNormalCrossings n (residualSupport W E U i)
          ((E.map (strictAlong U)).eraseIdx i.val ++ A.E)) ∧
        (∀ i : Fin E.length,residualSupport W E U i ⊆ closure (residualSupport W E U i \
          ⋃ H ∈ (E.map (strictAlong U)).eraseIdx i.val ++ A.E,H)) ∧
        (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong U)) A.E x) ∧
        (∀ x ∈ A.N,tauD (factorMatrix W E U x) ≤ P.card) ∧
        (∀ i : Fin E.length,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal=
            vanishingIdeal (n := n) (Q.proj ⁻¹' residualSupport W E T i) ∧
          residualSupport W E U i=Q.proj ⁻¹' residualSupport W E T i) ∧
        ∀ z ∈ A.N,properRows (factorMatrix W E U z) ⊆
          properRows (factorMatrix W E T (Q.proj z))) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        ¬P ⊆ properRows (factorMatrix W E (T.append R) z) := by
  let M := processedMaskMarked W E T P
  have hStart : processedAt W E P T :=
    ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,hPrepared,hBound⟩
  have hDom := (actual_processed_mask_controlled_record (Z := Y) hn hW hE hdense
    T hT hFull hOrd hNC hDenseS P hP hBound).1
  obtain ⟨Z,R,hCanonical,hResolution⟩ :=
    HironakaOriginalCompactCosupportGlobalScheduler.exists_original_compact_cosupport_terminal_tower
      hn (n+1) M hDom hCompact
  have hEnd := actual_processed_mask_test_history hn hW hE hdense T P hP hStart R hResolution.1
  refine ⟨Z,R,hCanonical,hResolution,?_,?_⟩
  · intro k
    let Q := BlowupTowerSplit.head R k
    have hQ : IsGeoTestTower M Q :=
      ((BlowupTowerSplit.isGeoTestTower_iff_head_tail M R k).mp hResolution.1).1
    obtain ⟨hState,hEq,hRows,hActivity⟩ :=
      actual_processed_mask_test_history hn hW hE hdense T P hP hStart Q hQ
    rcases hState with ⟨hTestU,hFullU,hSharpU,hOrdU,hNCU,hDenseU,hPreparedU,hBoundU⟩
    have hOver := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
      hW.1 hE.1 (T.append Q) hSharpU).2
    exact ⟨hTestU,hFullU,hSharpU,hOver,hEq,hOrdU,hNCU,hDenseU,hPreparedU,hBoundU,hRows,hActivity⟩
  · intro z hz hMask
    have hEmpty : (processedMaskMarked W E (T.append R) P).cosupp=∅ := by
      rw [←hEnd.2.1]
      exact hResolution.2
    have hCos := (mem_processed_mask_cosupport_iff hn hW hE hdense (T.append R)
      hEnd.1.1 hEnd.1.2.1 P z).mpr ⟨hz,hMask⟩
    exact Set.notMem_empty z (hEmpty ▸ hCos)


/-- ONE internally selected native finite coherent-SUM resolution erases its
original mask, preserving every actual prefix and processed original row. -/
theorem exists_actual_processed_mask_finite_block
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hNC : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (hPrepared : let A := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x)
    (P : Finset (Fin E.length)) (hP : 2 ≤ P.card)
    (hBound : let A := geoTransformAlong (geometricTemplate W []) T
      let D := fun i : Fin E.length => monomialPartAlong n A.N
        (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) A.E
      ∀ x ∈ A.N,tauD (fun i j => divExpAlong n A.N (D i) (A.E.get j) x) ≤ P.card) :
    let M := processedMaskMarked W E T P
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      ResolutionInvariantSpec.IsCanonical M ((CanonicalCentres.invFamily hn (n+1)).inv M) R ∧
      IsGeoResolution M R ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let U := T.append Q
        let A := geoTransformAlong (geometricTemplate W []) U
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        RestrictEmptyTower.CentresOver
          (originalSharpBadLocus (n := n) W E) U ∧
        geoTransformAlong M Q=processedMaskMarked W E U P ∧
        (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal x ≤ 1) ∧
        (∀ i : Fin E.length,HasNormalCrossings n (residualSupport W E U i)
          ((E.map (strictAlong U)).eraseIdx i.val ++ A.E)) ∧
        (∀ i : Fin E.length,residualSupport W E U i ⊆ closure (residualSupport W E U i \
          ⋃ H ∈ (E.map (strictAlong U)).eraseIdx i.val ++ A.E,H)) ∧
        (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong U)) A.E x) ∧
        (∀ x ∈ A.N,tauD (factorMatrix W E U x) ≤ P.card) ∧
        (∀ i : Fin E.length,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal=
            vanishingIdeal (n := n) (Q.proj ⁻¹' residualSupport W E T i) ∧
          residualSupport W E U i=Q.proj ⁻¹' residualSupport W E T i) ∧
        (∀ S : Finset (Fin E.length),S.Nonempty →
          IsCompact (processedMaskMarked W E U S).cosupp) ∧
        ∀ z ∈ A.N,properRows (factorMatrix W E U z) ⊆
          properRows (factorMatrix W E T (Q.proj z))) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        ¬P ⊆ properRows (factorMatrix W E (T.append R) z) := by
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  have hCompact := isCompact_actual_processed_mask_cosupport hn hW hE hdense
    hK T hT hFull hSharp P hPne
  obtain ⟨Z,R,hCan,hRes,hPrefixes,hEnd⟩ :=
    exists_actual_processed_mask_finite_block_of_compact_mask
      hn hW hE hdense T hT hFull hSharp hOrd hNC hDenseS hPrepared P hP hCompact hBound
  refine ⟨Z,R,hCan,hRes,?_,hEnd⟩
  intro k
  have h := hPrefixes k
  rcases h with ⟨hTest,hFull',hSharp',hOver,hEq,hOrd',hNC',hDense',hPrep',hBound',hRows,hActivity⟩
  refine ⟨hTest,hFull',hSharp',hOver,hEq,hOrd',hNC',hDense',hPrep',hBound',hRows,?_,hActivity⟩
  intro S hS
  exact isCompact_actual_processed_mask_cosupport hn hW hE hdense hK
    (T.append (BlowupTowerSplit.head R k)) hTest hFull' hSharp' S hS

end
end Hironaka.HironakaActualProcessedMaskFiniteBlock
