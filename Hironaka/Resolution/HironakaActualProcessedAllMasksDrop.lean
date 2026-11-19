import Hironaka.Resolution.HironakaActualProcessedMaskFiniteBlock
import Hironaka.Resolution.HironakaSharpOriginalDynamicGoodPrefixes
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Resolution.HironakaOriginalCrossingLowerHistory

/-! Internally constructed all-original-mask count descent on one actual
processed original history. Source-first proof:
`hironaka-actual-processed-all-masks-drop-20261101.tex`.
Original residual/prepared-state production and full sharp joint G4 termination
are not assumed to follow from this processed-phase result. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualProcessedAllMasksDrop
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaActualProcessedMaskFiniteBlock HironakaActualProcessedMaskControlledSum HironakaG4CompactWholeMonomialMaskPhase
  HomogenizedGlueingTower RestrictedIdealExtension

variable {n : ℕ} {X Y Z V : CMfd.{u} n}

def At (W : Set X) (E : List (Set X)) (q : ℕ)
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
    ∀ x ∈ A.N,tauD (factorMatrix W E T x) ≤ q

def Forward (W : Set X) (E : List (Set X)) (q : ℕ)
    (T : BlowupTower X Y) (R : BlowupTower Y Z) : Prop :=
  At W E q (T.append R) ∧
    (∀ i : Fin E.length,
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal=
        vanishingIdeal (n := n) (R.proj ⁻¹' residualSupport W E T i) ∧
      residualSupport W E (T.append R) i=R.proj ⁻¹' residualSupport W E T i) ∧
    ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
      properRows (factorMatrix W E (T.append R) z) ⊆
        properRows (factorMatrix W E T (R.proj z))

def Erased (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (U : BlowupTower X Y) (P : Finset (Fin E.length)) : Prop :=
  ∀ x ∈ (geoTransformAlong (geometricTemplate W []) U).N,
    ¬P ⊆ properRows (factorMatrix W E U x)

theorem forward_refl (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (q : ℕ) (T : BlowupTower X Y) (h : At W E q T) :
    Forward W E q T (BlowupTower.refl : BlowupTower Y Y) := by
  refine ⟨h,?_,fun x _hx => Finset.Subset.refl _⟩
  intro i
  rcases h with ⟨hT,hFull,_hSharp,hOrd,hNC,hDense,_hPrep,_hBound⟩
  have hp := HironakaG4ProtectedResidualEndpoint.actual_original_selected_endpoint_protection
    hn hW hE hdense i T hT hFull (fun x hx => hOrd x hx i) (hNC i) (hDense i)
  exact ⟨hp.2.1,rfl⟩

private theorem carrier_append_maps (W : Set X) (T : BlowupTower X Y)
    (R : BlowupTower Y Z)
    (hClosed : IsClosed (geoTransformAlong (geometricTemplate W []) T).N) :
    (geoTransformAlong (geometricTemplate W []) (T.append R)).N ⊆
      R.proj ⁻¹' (geoTransformAlong (geometricTemplate W []) T).N := by
  rw [geoTransformAlong_append,N_geoTransformAlong]
  exact MemberInterTowerAlong.strictAlong_subset_preimage R hClosed

private theorem forward_append (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (q : ℕ)
    (T : BlowupTower X Y) (R : BlowupTower Y Z) (S : BlowupTower Z V)
    (hR : Forward W E q T R) (hS : Forward W E q (T.append R) S) :
    Forward W E q T (R.append S) := by
  rcases hR with ⟨hAtR,hRowsR,hActR⟩
  rcases hS with ⟨hAtS,hRowsS,hActS⟩
  have hGeom := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense (T.append R) hAtR.1 hAtR.2.1
  have hState : At W E q (T.append (R.append S)) := by
    rw [←BlowupTower.append_assoc]
    exact hAtS
  refine ⟨hState,?_,?_⟩
  · intro i
    rw [←BlowupTower.append_assoc]
    have hI := (hRowsS i).1
    have hSupport := (hRowsS i).2
    rw [(hRowsR i).2] at hI hSupport
    rw [BlowupTower.proj_append]
    exact ⟨hI,hSupport⟩
  · intro x hx
    rw [←BlowupTower.append_assoc] at hx ⊢
    rw [BlowupTower.proj_append]
    exact (hActS x hx).trans
      (hActR (S.proj x) (carrier_append_maps W (T.append R) S hGeom.1.1 hx))

theorem forward_end {W : Set X} {E : List (Set X)} {q : ℕ}
    (T : BlowupTower X Y) (R : BlowupTower Y Z)
    (h : ∀ k : ℕ,Forward W E q T (BlowupTowerSplit.head R k)) : Forward W E q T R := by
  have he := h 0
  change Forward W E q T (BlowupTowerSplit.split R 0).2.1 at he
  rw [StepOneEmptyPrefix.split_zero R] at he
  exact he

theorem global_count_lt_of_all_masks {r b q : ℕ} (A : Fin r → Fin b → ℕ)
    (hBound : tauD A ≤ q)
    (hErased : ∀ P ∈ (Finset.univ : Finset (Fin r)).powersetCard q,¬P ⊆ properRows A) :
    tauD A < q := by
  apply lt_of_le_of_ne hBound
  intro hEq
  have hMem : properRows A ∈ (Finset.univ : Finset (Fin r)).powersetCard q :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hEq⟩
  exact hErased _ hMem (Finset.Subset.refl _)


def Folded (W : Set X) (E : List (Set X)) (q : ℕ)
    (T : BlowupTower X Y) (F : Finset (Finset (Fin E.length)))
    (R : BlowupTower Y Z) : Prop :=
  (∀ k : ℕ,Forward W E q T (BlowupTowerSplit.head R k)) ∧
    ∀ P ∈ F,Erased W E (T.append R) P

theorem folded_insert (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (q : ℕ)
    (T : BlowupTower X Y) (R : BlowupTower Y Z) (S : BlowupTower Z V)
    {F : Finset (Finset (Fin E.length))} {P : Finset (Fin E.length)}
    (hR : Folded W E q T F R)
    (hS : ∀ k : ℕ,Forward W E q (T.append R) (BlowupTowerSplit.head S k))
    (hErased : Erased W E ((T.append R).append S) P) :
    Folded W E q T (insert P F) (R.append S) := by
  have hREnd := forward_end T R hR.1
  have hSEnd := forward_end (T.append R) S hS
  refine ⟨?_,?_⟩
  · intro k
    by_cases hk : k ≤ S.length
    · have hs := StepOneEmptyPrefix.split_append_of_le R S k hk
      change Forward W E q T (BlowupTowerSplit.split (R.append S) k).2.1
      rw [hs]
      exact forward_append hn hW hE hdense q T R (BlowupTowerSplit.head S k) hREnd (hS k)
    · have hs := HironakaOriginalCrossingLowerHistory.split_append_above_tail
        R S k (by omega)
      change Forward W E q T (BlowupTowerSplit.split (R.append S) k).2.1
      rw [hs]
      exact hR.1 (k-S.length)
  · intro P0 hP0
    rcases Finset.mem_insert.mp hP0 with hEq | hOld
    · rw [hEq,←BlowupTower.append_assoc]
      exact hErased
    · have hGeom := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
        hn hW hE hdense (T.append R) hREnd.1.1 hREnd.1.2.1
      intro x hx hMask
      rw [←BlowupTower.append_assoc] at hx hMask
      exact hR.2 P0 hOld (S.proj x)
        (carrier_append_maps W (T.append R) S hGeom.1.1 hx)
        (hMask.trans (hSEnd.2.2 x hx))

theorem centresOver_mono_local {A : CMfd.{u} n} {F G : Set A} (h : F ⊆ G) :
    ∀ {B : CMfd.{u} n} (R : BlowupTower A B),
      RestrictEmptyTower.CentresOver F R → RestrictEmptyTower.CentresOver G R
  | _, .refl, _ => trivial
  | _, .step R _ _ _, hR => ⟨centresOver_mono_local h R hR.1,fun _ hx => h (hR.2 hx)⟩

/-- Every original mask of one high count is internally cleared, yielding
a true global strict count drop on the same actual original history. -/
theorem exists_actual_processed_all_masks_drop_with_high_footprint
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

    (q : ℕ) (hq : 2 ≤ q)
    (hMasks : ∀ P : Finset (Fin E.length),P.card=q →
      IsCompact (processedMaskMarked W E T P).cosupp)
    (hBound : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      tauD (factorMatrix W E T x) ≤ q) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      RestrictEmptyTower.CentresOver
        {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧ q ≤ tauD (factorMatrix W E T x)} R ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let U := T.append Q
        let A := geoTransformAlong (geometricTemplate W []) U
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
        (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal x ≤ 1) ∧
        (∀ i : Fin E.length,HasNormalCrossings n (residualSupport W E U i)
          ((E.map (strictAlong U)).eraseIdx i.val ++ A.E)) ∧
        (∀ i : Fin E.length,residualSupport W E U i ⊆ closure (residualSupport W E U i \
          ⋃ H ∈ (E.map (strictAlong U)).eraseIdx i.val ++ A.E,H)) ∧
        (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong U)) A.E x) ∧
        (∀ x ∈ A.N,tauD (factorMatrix W E U x) ≤ q) ∧
        (∀ i : Fin E.length,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal=
            vanishingIdeal (n := n) (Q.proj ⁻¹' residualSupport W E T i) ∧
          residualSupport W E U i=Q.proj ⁻¹' residualSupport W E T i) ∧
        ∀ z ∈ A.N,properRows (factorMatrix W E U z) ⊆
          properRows (factorMatrix W E T (Q.proj z))) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        tauD (factorMatrix W E (T.append R) z) < q := by
  classical
  let K := {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧ q ≤ tauD (factorMatrix W E T x)}
  have hStart : At W E q T := ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,hPrepared,hBound⟩
  have fold (F : Finset (Finset (Fin E.length))) :
      (∀ P ∈ F,P.card=q) →
        ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),Folded W E q T F R ∧ RestrictEmptyTower.CentresOver K R := by
    induction F using Finset.induction_on with
    | empty =>
      intro _hCards
      refine ⟨Y,.refl,⟨?_,?_⟩,trivial⟩
      · intro k
        cases k <;> exact forward_refl hn hW hE hdense q T hStart
      · intro P hP
        exact (Finset.notMem_empty P hP).elim
    | @insert P F _hPF ih =>
      intro hCards
      obtain ⟨Z,R,hR⟩ := ih (fun P0 hP0 => hCards P0 (Finset.mem_insert_of_mem hP0))
      have hCard : P.card=q := hCards P (Finset.mem_insert_self P F)
      have hP : 2 ≤ P.card := by omega
      have hREnd := forward_end T R hR.1.1
      rcases hREnd.1 with ⟨hTestR,hFullR,hSharpR,hOrdR,hNCR,hDenseR,hPrepR,hBoundR⟩
      have hBoundP : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
          tauD (factorMatrix W E (T.append R) x) ≤ P.card := by
        rw [hCard]
        exact hBoundR
      have hCompactP := isCompact_actual_processed_mask_of_forward hn hW hE hdense
        T R hT hFull hTestR hFullR hREnd.2.2 P (hMasks P hCard)
      obtain ⟨V,S,_hCanonical,hResolution,hS,hErase⟩ :=
        exists_actual_processed_mask_finite_block_of_compact_mask hn hW hE hdense
          (T.append R) hTestR hFullR hSharpR hOrdR hNCR hDenseR hPrepR P hP hCompactP hBoundP
      have hForwardS : ∀ k : ℕ,Forward W E q (T.append R) (BlowupTowerSplit.head S k) := by
        intro k
        rcases hS k with ⟨hTestS,hFullS,hSharpS,_hOverS,_hSumS,hOrdS,hNCS,hDenseS,hPrepS,hBoundS,hRowsS,hActivityS⟩
        refine ⟨?_,hRowsS,hActivityS⟩
        refine ⟨hTestS,hFullS,hSharpS,hOrdS,hNCS,hDenseS,hPrepS,?_⟩
        simpa only [hCard] using hBoundS
      have hDom := (actual_processed_mask_controlled_record (Z := V) hn hW hE hdense
        (T.append R) hTestR hFullR hOrdR hNCR hDenseR P hP hBoundP).1
      have hSover := HironakaAdmissibleSequence.centresOver_cosupp _
        hDom.isWellFormed.isClosedSubmanifold_N hDom.isWellFormed.isCoherent S hResolution.1
      have hSub : (processedMaskMarked W E (T.append R) P).cosupp ⊆ R.proj ⁻¹' K := by
        intro z hz
        have hPre := actual_processed_mask_subset_preimage_of_forward hn hW hE hdense
          T R hT hFull hTestR hFullR hREnd.2.2 P hz
        exact actual_processed_mask_subset_high_count hn hW hE hdense T hT hFull q P hCard hPre
      have hSoverK : RestrictEmptyTower.CentresOver (R.proj ⁻¹' K) S :=
        centresOver_mono_local hSub S hSover
      refine ⟨V,R.append S,folded_insert hn hW hE hdense q T R S hR.1 hForwardS hErase,?_⟩
      exact (RestrictEmptyTower.centresOver_append_iff K R S).mpr ⟨hR.2,hSoverK⟩
  let All := (Finset.univ : Finset (Fin E.length)).powersetCard q
  obtain ⟨Z,R,hR⟩ := fold All (fun P hP => (Finset.mem_powersetCard.mp hP).2)
  have hEnd := forward_end T R hR.1.1
  refine ⟨Z,R,hR.2,?_,?_⟩
  · intro k
    rcases hR.1.1 k with ⟨hState,hRows,hActivity⟩
    rcases hState with ⟨hTestQ,hFullQ,hSharpQ,hOrdQ,hNCQ,hDenseQ,hPrepQ,hBoundQ⟩
    have hOver := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
      hW.1 hE.1 (T.append (BlowupTowerSplit.head R k)) hSharpQ).2
    exact ⟨hTestQ,hFullQ,hSharpQ,hOver,hOrdQ,hNCQ,hDenseQ,hPrepQ,hBoundQ,hRows,hActivity⟩
  · rcases hEnd.1 with ⟨_hTest,_hFull,_hSharp,_hOrd,_hNC,_hDense,_hPrep,hEndBound⟩
    intro z hz
    exact global_count_lt_of_all_masks (factorMatrix W E (T.append R) z) (hEndBound z hz)
      (fun P hP => hR.1.2 P hP z hz)





/-- Every original mask of one high count is internally cleared, yielding
a true global strict count drop on the same actual original history. -/
theorem exists_actual_processed_all_masks_drop_of_compact_masks
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

    (q : ℕ) (hq : 2 ≤ q)
    (hMasks : ∀ P : Finset (Fin E.length),P.card=q →
      IsCompact (processedMaskMarked W E T P).cosupp)
    (hBound : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      tauD (factorMatrix W E T x) ≤ q) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let U := T.append Q
        let A := geoTransformAlong (geometricTemplate W []) U
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
        (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal x ≤ 1) ∧
        (∀ i : Fin E.length,HasNormalCrossings n (residualSupport W E U i)
          ((E.map (strictAlong U)).eraseIdx i.val ++ A.E)) ∧
        (∀ i : Fin E.length,residualSupport W E U i ⊆ closure (residualSupport W E U i \
          ⋃ H ∈ (E.map (strictAlong U)).eraseIdx i.val ++ A.E,H)) ∧
        (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong U)) A.E x) ∧
        (∀ x ∈ A.N,tauD (factorMatrix W E U x) ≤ q) ∧
        (∀ i : Fin E.length,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal=
            vanishingIdeal (n := n) (Q.proj ⁻¹' residualSupport W E T i) ∧
          residualSupport W E U i=Q.proj ⁻¹' residualSupport W E T i) ∧
        ∀ z ∈ A.N,properRows (factorMatrix W E U z) ⊆
          properRows (factorMatrix W E T (Q.proj z))) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        tauD (factorMatrix W E (T.append R) z) < q := by
  obtain ⟨Z,R,_hOver,hPrefixes,hEnd⟩ :=
    exists_actual_processed_all_masks_drop_with_high_footprint hn hW hE hdense
      T hT hFull hSharp hOrd hNC hDenseS hPrepared q hq hMasks hBound
  exact ⟨Z,R,hPrefixes,hEnd⟩

/-- The same fixed-q drop follows from compactness of the actual current
high-count locus; the lower-count bad locus may remain noncompact. -/
theorem exists_actual_processed_all_masks_drop_of_compact_high_count
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

    (q : ℕ) (hq : 2 ≤ q)
    (hHigh : IsCompact {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧
      q ≤ tauD (factorMatrix W E T x)})
    (hBound : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      tauD (factorMatrix W E T x) ≤ q) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let U := T.append Q
        let A := geoTransformAlong (geometricTemplate W []) U
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
        (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal x ≤ 1) ∧
        (∀ i : Fin E.length,HasNormalCrossings n (residualSupport W E U i)
          ((E.map (strictAlong U)).eraseIdx i.val ++ A.E)) ∧
        (∀ i : Fin E.length,residualSupport W E U i ⊆ closure (residualSupport W E U i \
          ⋃ H ∈ (E.map (strictAlong U)).eraseIdx i.val ++ A.E,H)) ∧
        (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong U)) A.E x) ∧
        (∀ x ∈ A.N,tauD (factorMatrix W E U x) ≤ q) ∧
        (∀ i : Fin E.length,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal=
            vanishingIdeal (n := n) (Q.proj ⁻¹' residualSupport W E T i) ∧
          residualSupport W E U i=Q.proj ⁻¹' residualSupport W E T i) ∧
        ∀ z ∈ A.N,properRows (factorMatrix W E U z) ⊆
          properRows (factorMatrix W E T (Q.proj z))) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        tauD (factorMatrix W E (T.append R) z) < q := by
  have hMasks : ∀ P : Finset (Fin E.length),P.card=q →
      IsCompact (processedMaskMarked W E T P).cosupp := by
    intro P hCard
    exact isCompact_actual_processed_mask_of_compact_high_count hn hW hE hdense
      T hT hFull q hHigh P hCard
  exact exists_actual_processed_all_masks_drop_of_compact_masks hn hW hE hdense
    T hT hFull hSharp hOrd hNC hDenseS hPrepared q hq hMasks hBound

/-- The same high-count drop has its entire tail over the compact initial
high-count locus, hence is an isomorphism on its complement. -/
theorem exists_actual_processed_high_count_drop_compact_footprint
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

    (q : ℕ) (hq : 2 ≤ q)
    (hHigh : IsCompact {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧
      q ≤ tauD (factorMatrix W E T x)})
    (hBound : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      tauD (factorMatrix W E T x) ≤ q) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      RestrictEmptyTower.CentresOver
        {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧ q ≤ tauD (factorMatrix W E T x)} R ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ R.proj ∧ IsProperMap R.proj ∧
      IsIsomorphismOver n R.proj
        {x | x ∈ (geoTransformAlong (geometricTemplate W []) T).N ∧ q ≤ tauD (factorMatrix W E T x)}ᶜ ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let U := T.append Q
        let A := geoTransformAlong (geometricTemplate W []) U
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
        (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal x ≤ 1) ∧
        (∀ i : Fin E.length,HasNormalCrossings n (residualSupport W E U i)
          ((E.map (strictAlong U)).eraseIdx i.val ++ A.E)) ∧
        (∀ i : Fin E.length,residualSupport W E U i ⊆ closure (residualSupport W E U i \
          ⋃ H ∈ (E.map (strictAlong U)).eraseIdx i.val ++ A.E,H)) ∧
        (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong U)) A.E x) ∧
        (∀ x ∈ A.N,tauD (factorMatrix W E U x) ≤ q) ∧
        (∀ i : Fin E.length,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal=
            vanishingIdeal (n := n) (Q.proj ⁻¹' residualSupport W E T i) ∧
          residualSupport W E U i=Q.proj ⁻¹' residualSupport W E T i) ∧
        ∀ z ∈ A.N,properRows (factorMatrix W E U z) ⊆
          properRows (factorMatrix W E T (Q.proj z))) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        tauD (factorMatrix W E (T.append R) z) < q := by
  have hMasks : ∀ P : Finset (Fin E.length),P.card=q →
      IsCompact (processedMaskMarked W E T P).cosupp := by
    intro P hCard
    exact isCompact_actual_processed_mask_of_compact_high_count hn hW hE hdense
      T hT hFull q hHigh P hCard
  obtain ⟨Z,R,hOver,hPrefixes,hEnd⟩ :=
    exists_actual_processed_all_masks_drop_with_high_footprint hn hW hE hdense
      T hT hFull hSharp hOrd hNC hDenseS hPrepared q hq hMasks hBound
  exact ⟨Z,R,hOver,R.contMDiff_proj,HironakaLocalPrincipalization.isProperMap_proj R,
    HironakaSharpOriginalDynamicGoodPrefixes.isIsomorphismOver_proj_of_centresOver _ R hOver,hPrefixes,hEnd⟩

/-- Every original mask of one high count is internally cleared, yielding
a true global strict count drop on the same actual original history. -/
theorem exists_actual_processed_all_masks_drop
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

    (q : ℕ) (hq : 2 ≤ q)
    (hBound : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      tauD (factorMatrix W E T x) ≤ q) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let U := T.append Q
        let A := geoTransformAlong (geometricTemplate W []) U
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
        (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal x ≤ 1) ∧
        (∀ i : Fin E.length,HasNormalCrossings n (residualSupport W E U i)
          ((E.map (strictAlong U)).eraseIdx i.val ++ A.E)) ∧
        (∀ i : Fin E.length,residualSupport W E U i ⊆ closure (residualSupport W E U i \
          ⋃ H ∈ (E.map (strictAlong U)).eraseIdx i.val ++ A.E,H)) ∧
        (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong U)) A.E x) ∧
        (∀ x ∈ A.N,tauD (factorMatrix W E U x) ≤ q) ∧
        (∀ i : Fin E.length,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal=
            vanishingIdeal (n := n) (Q.proj ⁻¹' residualSupport W E T i) ∧
          residualSupport W E U i=Q.proj ⁻¹' residualSupport W E T i) ∧
        ∀ z ∈ A.N,properRows (factorMatrix W E U z) ⊆
          properRows (factorMatrix W E T (Q.proj z))) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        tauD (factorMatrix W E (T.append R) z) < q := by
  have hMasks : ∀ P : Finset (Fin E.length),P.card=q →
      IsCompact (processedMaskMarked W E T P).cosupp := by
    intro P hCard
    have hP : P.Nonempty := Finset.card_pos.mp (by omega)
    exact isCompact_actual_processed_mask_cosupport hn hW hE hdense hK T hT hFull hSharp P hP
  exact exists_actual_processed_all_masks_drop_of_compact_masks hn hW hE hdense T hT hFull hSharp
    hOrd hNC hDenseS hPrepared q hq hMasks hBound

private theorem at_mono {W : Set X} {E : List (Set X)} {a b : ℕ}
    {T : BlowupTower X Y} (h : At W E a T) (hab : a ≤ b) : At W E b T := by
  rcases h with ⟨hT,hFull,hSharp,hOrd,hNC,hDense,hPrep,hBound⟩
  exact ⟨hT,hFull,hSharp,hOrd,hNC,hDense,hPrep,fun x hx => (hBound x hx).trans hab⟩

private theorem forward_mono {W : Set X} {E : List (Set X)} {a b : ℕ}
    {T : BlowupTower X Y} {R : BlowupTower Y Z}
    (h : Forward W E a T R) (hab : a ≤ b) : Forward W E b T R :=
  ⟨at_mono h.1 hab,h.2⟩

private theorem prefix_forward_append (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (q : ℕ)
    (T : BlowupTower X Y) (R : BlowupTower Y Z) (S : BlowupTower Z V)
    (hR : ∀ k : ℕ,Forward W E q T (BlowupTowerSplit.head R k))
    (hS : ∀ k : ℕ,Forward W E q (T.append R) (BlowupTowerSplit.head S k)) :
    ∀ k : ℕ,Forward W E q T (BlowupTowerSplit.head (R.append S) k) := by
  intro k
  by_cases hk : k ≤ S.length
  · have hs := StepOneEmptyPrefix.split_append_of_le R S k hk
    change Forward W E q T (BlowupTowerSplit.split (R.append S) k).2.1
    rw [hs]
    exact forward_append hn hW hE hdense q T R (BlowupTowerSplit.head S k)
      (forward_end T R hR) (hS k)
  · have hs := HironakaOriginalCrossingLowerHistory.split_append_above_tail R S k (by omega)
    change Forward W E q T (BlowupTowerSplit.split (R.append S) k).2.1
    rw [hs]
    exact hR (k-S.length)

private theorem descend_processed_count (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) (q : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),At W E q T →
      ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
        (∀ k : ℕ,Forward W E q T (BlowupTowerSplit.head R k)) ∧ At W E 1 (T.append R) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro Y T hAt
    by_cases hLow : q ≤ 1
    · refine ⟨Y,.refl,?_,at_mono hAt hLow⟩
      intro k
      cases k <;> exact forward_refl hn hW hE hdense q T hAt
    · have hq : 2 ≤ q := by omega
      rcases hAt with ⟨hT,hFull,hSharp,hOrd,hNC,hDense,hPrep,hBound⟩
      obtain ⟨Z,R,hR,hDrop⟩ := exists_actual_processed_all_masks_drop hn hW hE hdense
        T hT hFull hSharp hK hOrd hNC hDense hPrep q hq hBound
      have hForwardR : ∀ k : ℕ,Forward W E q T (BlowupTowerSplit.head R k) := by
        intro k
        rcases hR k with ⟨hTestQ,hFullQ,hSharpQ,_hOverQ,hOrdQ,hNCQ,hDenseQ,hPrepQ,hBoundQ,hRowsQ,hActivityQ⟩
        exact ⟨⟨hTestQ,hFullQ,hSharpQ,hOrdQ,hNCQ,hDenseQ,hPrepQ,hBoundQ⟩,hRowsQ,hActivityQ⟩
      have hEnd := (forward_end T R hForwardR).1
      rcases hEnd with ⟨hTestR,hFullR,hSharpR,hOrdR,hNCR,hDenseR,hPrepR,_hBoundR⟩
      have hLower : At W E (q-1) (T.append R) := by
        refine ⟨hTestR,hFullR,hSharpR,hOrdR,hNCR,hDenseR,hPrepR,?_⟩
        intro x hx
        have hd := hDrop x hx
        omega
      obtain ⟨V,S,hS,hEndS⟩ := ih (q-1) (by omega) (T.append R) hLower
      refine ⟨V,R.append S,?_,?_⟩
      · exact prefix_forward_append hn hW hE hdense q T R S hForwardR
          (fun k => forward_mono (hS k) (Nat.sub_le q 1))
      · rw [←BlowupTower.append_assoc]
        exact hEndS

/-- The genuine internally constructed high-count blocks descend the actual
old-factor count to at most one, starting from the automatic original row bound. -/
theorem exists_actual_processed_count_at_most_one
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
 :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head R k
        let U := T.append Q
        let A := geoTransformAlong (geometricTemplate W []) U
        IsGeoTestTower (geometricTemplate W []) U ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
        CurrentSharpCentres W E U ∧
        RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
        (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal x ≤ 1) ∧
        (∀ i : Fin E.length,HasNormalCrossings n (residualSupport W E U i)
          ((E.map (strictAlong U)).eraseIdx i.val ++ A.E)) ∧
        (∀ i : Fin E.length,residualSupport W E U i ⊆ closure (residualSupport W E U i \
          ⋃ H ∈ (E.map (strictAlong U)).eraseIdx i.val ++ A.E,H)) ∧
        (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong U)) A.E x) ∧
        (∀ i : Fin E.length,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) U).ideal=
            vanishingIdeal (n := n) (Q.proj ⁻¹' residualSupport W E T i) ∧
          residualSupport W E U i=Q.proj ⁻¹' residualSupport W E T i) ∧
        ∀ z ∈ A.N,properRows (factorMatrix W E U z) ⊆
          properRows (factorMatrix W E T (Q.proj z))) ∧
      ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        tauD (factorMatrix W E (T.append R) z) ≤ 1 := by
  have hBound : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      tauD (factorMatrix W E T x) ≤ E.length := by
    intro x _hx
    simpa only [tauD,Fintype.card_fin] using Finset.card_le_univ (properRows (factorMatrix W E T x))
  have hAt : At W E E.length T := ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,hPrepared,hBound⟩
  obtain ⟨Z,R,hR,hEnd⟩ := descend_processed_count hn hW hE hdense hK E.length T hAt
  refine ⟨Z,R,?_,?_⟩
  · intro k
    rcases hR k with ⟨hState,hRows,hActivity⟩
    rcases hState with ⟨hTestQ,hFullQ,hSharpQ,hOrdQ,hNCQ,hDenseQ,hPrepQ,_hBoundQ⟩
    have hOver := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
      hW.1 hE.1 (T.append (BlowupTowerSplit.head R k)) hSharpQ).2
    exact ⟨hTestQ,hFullQ,hSharpQ,hOver,hOrdQ,hNCQ,hDenseQ,hPrepQ,hRows,hActivity⟩
  · exact hEnd.2.2.2.2.2.2.2

end
end Hironaka.HironakaActualProcessedAllMasksDrop
