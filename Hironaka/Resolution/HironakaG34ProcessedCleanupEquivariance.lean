import Hironaka.Resolution.HironakaActualProcessedAllMasksDrop
import Hironaka.Resolution.HironakaActualProcessedSharpCleanup
import Hironaka.Resolution.HironakaActualOriginalProcessedSharpCleanupAllDimensions
import Hironaka.Resolution.HironakaG34ZeroMaskFoldEquivariance

/-!
# K3 (the processed-row cleanup) with an equivariance conclusion (twelfth brick of EQ_d)

Lane G34 (run 0080, round 10).  Blueprint: `hironaka-g34-resume-processed-cleanup-equivariance.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §1 (rows "K3 masks", "K3 zero mask"), §2(c)(iii).

The held K3 chain (`HironakaActualProcessedAllMasksDrop`, `HironakaActualProcessedSharpCleanup`,
`HironakaActualOriginalProcessedSharpCleanup`, `HironakaActualOriginalProcessedSharpCleanupAllDimensions`) is existential
and its towers are built by PRIVATE helpers.  This module re-derives it verbatim (the helpers below are copies of the held
ones; the held files are not edited) and threads ONE more conclusion through every level: an equivariant prefix stays
equivariant (`HironakaG34MaskFoldEquivariance.IsEquivariant W E`).  The primitive blocks are the equivariant processed mask
block (`HironakaG34ProcessedMaskEquivariance.exists_actual_processed_mask_finite_block_equivariant`) and the equivariant
zero-mask fold (`HironakaG34ZeroMaskFoldEquivariance.exists_prepared_zero_mask_fixed_q_drop_equivariant`, on the current
data, appended by `IsEquivariant.append_of_current`).

## Main results

* `exists_actual_processed_all_masks_drop_equivariant`, `exists_actual_processed_count_at_most_one_equivariant`;
* `exists_actual_count_one_sharp_cleanup_equivariant`, **`exists_actual_processed_sharp_cleanup_equivariant`**;
* `exists_actual_original_processed_sharp_cleanup_equivariant`,
  **`exists_actual_original_processed_sharp_cleanup_all_dimensions_equivariant`** (K3 in every ambient dimension).

New file; no existing statement changed; no named input.  Sorry-free.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34ProcessedCleanupEquivariance
noncomputable section

section AllMasks
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaActualProcessedMaskFiniteBlock HironakaG4CompactWholeMonomialMaskPhase
  HomogenizedGlueingTower RestrictedIdealExtension
  HironakaG34MaskFoldEquivariance

variable {n : ℕ} {X Y Z V : CMfd.{u} n}

private def At (W : Set X) (E : List (Set X)) (q : ℕ)
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

private def Forward (W : Set X) (E : List (Set X)) (q : ℕ)
    (T : BlowupTower X Y) (R : BlowupTower Y Z) : Prop :=
  At W E q (T.append R) ∧
    (∀ i : Fin E.length,
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal=
        vanishingIdeal (n := n) (R.proj ⁻¹' residualSupport W E T i) ∧
      residualSupport W E (T.append R) i=R.proj ⁻¹' residualSupport W E T i) ∧
    ∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
      properRows (factorMatrix W E (T.append R) z) ⊆
        properRows (factorMatrix W E T (R.proj z))

private def Erased (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (U : BlowupTower X Y) (P : Finset (Fin E.length)) : Prop :=
  ∀ x ∈ (geoTransformAlong (geometricTemplate W []) U).N,
    ¬P ⊆ properRows (factorMatrix W E U x)

private theorem forward_refl (hn : 0 < n) {W : Set X} {E : List (Set X)}
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

private theorem forward_end {W : Set X} {E : List (Set X)} {q : ℕ}
    (T : BlowupTower X Y) (R : BlowupTower Y Z)
    (h : ∀ k : ℕ,Forward W E q T (BlowupTowerSplit.head R k)) : Forward W E q T R := by
  have he := h 0
  change Forward W E q T (BlowupTowerSplit.split R 0).2.1 at he
  rw [StepOneEmptyPrefix.split_zero R] at he
  exact he

private theorem global_count_lt_of_all_masks {r b q : ℕ} (A : Fin r → Fin b → ℕ)
    (hBound : tauD A ≤ q)
    (hErased : ∀ P ∈ (Finset.univ : Finset (Fin r)).powersetCard q,¬P ⊆ properRows A) :
    tauD A < q := by
  apply lt_of_le_of_ne hBound
  intro hEq
  have hMem : properRows A ∈ (Finset.univ : Finset (Fin r)).powersetCard q :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hEq⟩
  exact hErased _ hMem (Finset.Subset.refl _)


private def Folded (W : Set X) (E : List (Set X)) (q : ℕ)
    (T : BlowupTower X Y) (F : Finset (Finset (Fin E.length)))
    (R : BlowupTower Y Z) : Prop :=
  (∀ k : ℕ,Forward W E q T (BlowupTowerSplit.head R k)) ∧
    ∀ P ∈ F,Erased W E (T.append R) P

private theorem folded_insert (hn : 0 < n) {W : Set X} {E : List (Set X)}
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

/-- **Every original mask of one high count is internally cleared, equivariantly**: the conclusions of
`HironakaActualProcessedAllMasksDrop.exists_actual_processed_all_masks_drop`, plus: an equivariant prefix stays
equivariant. -/
theorem exists_actual_processed_all_masks_drop_equivariant
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
      (∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        tauD (factorMatrix W E (T.append R) z) < q) ∧
      (IsEquivariant W E T → IsEquivariant W E (T.append R)) := by
  classical
  have hStart : At W E q T := ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,hPrepared,hBound⟩
  have fold (F : Finset (Finset (Fin E.length))) :
      (∀ P ∈ F,P.card=q) →
        ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),Folded W E q T F R ∧
          (IsEquivariant W E T → IsEquivariant W E (T.append R)) := by
    induction F using Finset.induction_on with
    | empty =>
      intro _hCards
      refine ⟨Y,.refl,⟨?_,?_⟩,fun h => h⟩
      · intro k
        cases k <;> exact forward_refl hn hW hE hdense q T hStart
      · intro P hP
        exact (Finset.notMem_empty P hP).elim
    | @insert P F _hPF ih =>
      intro hCards
      obtain ⟨Z,R,hR,hEqR⟩ := ih (fun P0 hP0 => hCards P0 (Finset.mem_insert_of_mem hP0))
      have hCard : P.card=q := hCards P (Finset.mem_insert_self P F)
      have hP : 2 ≤ P.card := by omega
      have hREnd := forward_end T R hR.1
      rcases hREnd.1 with ⟨hTestR,hFullR,hSharpR,hOrdR,hNCR,hDenseR,hPrepR,hBoundR⟩
      have hBoundP : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
          tauD (factorMatrix W E (T.append R) x) ≤ P.card := by
        rw [hCard]
        exact hBoundR
      obtain ⟨V,S,_hCanonical,_hResolution,hS,hErase,hEqS⟩ :=
        HironakaG34ProcessedMaskEquivariance.exists_actual_processed_mask_finite_block_equivariant hn hW hE hdense
          (T.append R) hTestR hFullR hSharpR hK hOrdR hNCR hDenseR hPrepR P hP hBoundP
      have hForwardS : ∀ k : ℕ,Forward W E q (T.append R) (BlowupTowerSplit.head S k) := by
        intro k
        rcases hS k with ⟨hTestS,hFullS,hSharpS,_hOverS,_hSumS,hOrdS,hNCS,hDenseS,hPrepS,hBoundS,hRowsS,_hCompactS,hActivityS⟩
        refine ⟨?_,hRowsS,hActivityS⟩
        refine ⟨hTestS,hFullS,hSharpS,hOrdS,hNCS,hDenseS,hPrepS,?_⟩
        simpa only [hCard] using hBoundS
      exact ⟨V,R.append S,folded_insert hn hW hE hdense q T R S hR hForwardS hErase,
        isEquivariant_clause_trans hEqR hEqS⟩
  let All := (Finset.univ : Finset (Fin E.length)).powersetCard q
  obtain ⟨Z,R,hR,hEqR⟩ := fold All (fun P hP => (Finset.mem_powersetCard.mp hP).2)
  have hEnd := forward_end T R hR.1
  refine ⟨Z,R,?_,?_,hEqR⟩
  · intro k
    rcases hR.1 k with ⟨hState,hRows,hActivity⟩
    rcases hState with ⟨hTestQ,hFullQ,hSharpQ,hOrdQ,hNCQ,hDenseQ,hPrepQ,hBoundQ⟩
    have hOver := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
      hW.1 hE.1 (T.append (BlowupTowerSplit.head R k)) hSharpQ).2
    exact ⟨hTestQ,hFullQ,hSharpQ,hOver,hOrdQ,hNCQ,hDenseQ,hPrepQ,hBoundQ,hRows,hActivity⟩
  · rcases hEnd.1 with ⟨_hTest,_hFull,_hSharp,_hOrd,_hNC,_hDense,_hPrep,hEndBound⟩
    intro z hz
    exact global_count_lt_of_all_masks (factorMatrix W E (T.append R) z) (hEndBound z hz)
      (fun P hP => hR.2 P hP z hz)


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
        (∀ k : ℕ,Forward W E q T (BlowupTowerSplit.head R k)) ∧ At W E 1 (T.append R) ∧
          (IsEquivariant W E T → IsEquivariant W E (T.append R)) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro Y T hAt
    by_cases hLow : q ≤ 1
    · refine ⟨Y,.refl,?_,at_mono hAt hLow,fun h => h⟩
      intro k
      cases k <;> exact forward_refl hn hW hE hdense q T hAt
    · have hq : 2 ≤ q := by omega
      rcases hAt with ⟨hT,hFull,hSharp,hOrd,hNC,hDense,hPrep,hBound⟩
      obtain ⟨Z,R,hR,hDrop,hEqR⟩ := exists_actual_processed_all_masks_drop_equivariant hn hW hE hdense
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
      obtain ⟨V,S,hS,hEndS,hEqS⟩ := ih (q-1) (by omega) (T.append R) hLower
      refine ⟨V,R.append S,?_,?_,isEquivariant_clause_trans hEqR hEqS⟩
      · exact prefix_forward_append hn hW hE hdense q T R S hForwardR
          (fun k => forward_mono (hS k) (Nat.sub_le q 1))
      · rw [←BlowupTower.append_assoc]
        exact hEndS

/-- **The high-count blocks descend the count to at most one, equivariantly**: the conclusions of
`HironakaActualProcessedAllMasksDrop.exists_actual_processed_count_at_most_one`, plus: an equivariant prefix stays
equivariant. -/
theorem exists_actual_processed_count_at_most_one_equivariant
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
      (∀ z ∈ (geoTransformAlong (geometricTemplate W []) (T.append R)).N,
        tauD (factorMatrix W E (T.append R) z) ≤ 1) ∧
      (IsEquivariant W E T → IsEquivariant W E (T.append R)) := by
  have hBound : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      tauD (factorMatrix W E T x) ≤ E.length := by
    intro x _hx
    simpa only [tauD,Fintype.card_fin] using Finset.card_le_univ (properRows (factorMatrix W E T x))
  have hAt : At W E E.length T := ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,hPrepared,hBound⟩
  obtain ⟨Z,R,hR,hEnd,hEqR⟩ := descend_processed_count hn hW hE hdense hK E.length T hAt
  refine ⟨Z,R,?_,?_,hEqR⟩
  · intro k
    rcases hR k with ⟨hState,hRows,hActivity⟩
    rcases hState with ⟨hTestQ,hFullQ,hSharpQ,hOrdQ,hNCQ,hDenseQ,hPrepQ,_hBoundQ⟩
    have hOver := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
      hW.1 hE.1 (T.append (BlowupTowerSplit.head R k)) hSharpQ).2
    exact ⟨hTestQ,hFullQ,hSharpQ,hOver,hOrdQ,hNCQ,hDenseQ,hPrepQ,hRows,hActivity⟩
  · exact hEnd.2.2.2.2.2.2.2

end AllMasks

section Sharp
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison RelativePrincipalizationSpan
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4PreparedCentreCoordinates
  HironakaG4MonomialFamilyInvariant HironakaActualProcessedMaskFiniteBlock
  HironakaG4CompactWholeMonomialMaskPhase HomogenizedGlueingTower RestrictedIdealExtension
  MonomialPartAlong DivisorExponentAlong GermIdealOrder
  HironakaG34MaskFoldEquivariance

variable {n : ℕ} {X Y Z V : CMfd.{u} n}


private theorem nuOne_eq_zero_of_tauD_eq_one {r b : ℕ} (A : Fin r → Fin b → ℕ)
    (h : tauD A=1) : nuOne A=0 := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp h
  have hne : (properRows A).Nonempty := by rw [hi];exact Finset.singleton_nonempty i
  apply (nuOne_eq_zero_iff_exists_gcd_row A hne).mpr
  refine ⟨i,by rw [hi];exact Finset.mem_singleton_self i,?_⟩
  intro j
  simp only [gcdColumn,dif_pos hne,hi,Finset.inf'_singleton]

private theorem tauD_row_equiv {r s b : ℕ} (e : Fin r ≃ Fin s)
    (A : Fin s → Fin b → ℕ) : tauD (fun i => A (e i))=tauD A := by
  have hRows : (properRows (fun i => A (e i))).map e.toEmbedding=properRows A := by
    ext i
    simp only [Finset.mem_map,properRows,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact hj
    · intro hi
      exact ⟨e.symm i,by simpa only [rowOrder,e.apply_symm_apply] using hi,e.apply_symm_apply i⟩
  unfold tauD
  rw [←hRows,Finset.card_map]

private def tupleMatrix (N : Set X) (O B : List (Set X))
    {Y : CMfd.{u} n} (R : BlowupTower X Y) (x : Y) :
    Fin O.length → Fin (geoTransformAlong (geometricTemplate N B) R).E.length → ℕ :=
  fun i j => divExpAlong n (strictAlong R N)
    (monomialPartAlong n (strictAlong R N)
      (restrictOn n (strictAlong R N) (vanishingIdeal (n := n) (strictAlong R (O.get i))))
      (geoTransformAlong (geometricTemplate N B) R).E)
    ((geoTransformAlong (geometricTemplate N B) R).E.get j) x

private def tuplePrepared (N : Set X) (O B : List (Set X))
    {Y : CMfd.{u} n} (R : BlowupTower X Y) : Prop :=
  let NR := strictAlong R N
  let OR := O.map (strictAlong R)
  let BR := (geoTransformAlong (geometricTemplate N B) R).E
  IsClosedSubmanifold n NR ∧ IsSNCDivisor n (OR ++ BR) ∧ IsTransverse n NR BR ∧
    NR ⊆ closure (NR \ ⋃ H ∈ OR ++ BR,H) ∧
    (∀ x ∈ NR,∀ i,ordinaryTraceOrder NR (oldResidualPart NR OR BR i) x ≤ 1) ∧
    (∀ x ∈ NR,IsPreparedResidualSNCAt NR OR BR x)

private theorem native_count_one_cleanup (hn : 0 < n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O ++ B))
    (hTr : IsTransverse n N B) (hdense : N ⊆ closure (N \ ⋃ H ∈ O ++ B,H))
    (hK : IsCompact (originalSharpBadLocus (n := n) N (O ++ B)))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1)
    (hPrep : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x)
    (hCount : ∀ x ∈ N,tauD (tupleMatrix N O B (.refl : BlowupTower X X) x) ≤ 1) :
    ∃ (Y : CMfd.{u} n) (R : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N B) R ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (O ++ B)) R ∧
      CurrentSharpCentres N (O ++ B) R ∧
      (∀ x ∈ strictAlong R N,tauD (tupleMatrix N O B R x)=0) ∧
      IsClosedSubmanifold n (strictAlong R N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E ∧
      HasNormalCrossings n (strictAlong R N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E ∧
      IsEquivariant N (O ++ B) R := by
  have hNu : ∀ x ∈ N,tauD (tupleMatrix N O B (.refl : BlowupTower X X) x)=1 →
      nuOne (tupleMatrix N O B (.refl : BlowupTower X X) x)=0 :=
    fun x _hx he => nuOne_eq_zero_of_tauD_eq_one _ he
  obtain ⟨Y,R,hCarrier,hFull,hSharp,_hOver,hEqR,_hResidualTests,hPrefixes,hDrop⟩ :=
    HironakaG34ZeroMaskFoldEquivariance.exists_prepared_zero_mask_fixed_q_drop_equivariant
      hn hN hE hTr hdense hOrd hPrep 1 (by omega) hK hCount hNu
  have hEnd : tuplePrepared N O B (BlowupTowerSplit.split R 0).2.1 := by
    have h := hPrefixes 0
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩
  rw [StepOneEmptyPrefix.split_zero R] at hEnd
  rcases hEnd with ⟨hNR,hER,hTrR,hDenseR,hOrdR,hPrepR⟩
  let NR := strictAlong R N
  let OR := O.map (strictAlong R)
  let BR := (geoTransformAlong (geometricTemplate N B) R).E
  let A : Y → Fin OR.length → Fin BR.length → ℕ := fun x i j =>
    divExpAlong n NR (oldMonomialPart NR OR BR i) (BR.get j) x
  let e : Fin O.length ≃ Fin OR.length := finCongr (by simp [OR])
  have hGet (i : Fin O.length) : OR.get (e i)=strictAlong R (O.get i) := by simp [OR,e]
  have hMatrix (x : Y) : (fun i => A x (e i))=tupleMatrix N O B R x := by
    funext i j
    simp only [A,oldMonomialPart,oldTraceIdeal,hGet,tupleMatrix,NR,BR]
  have hZero (x : Y) (hx : x ∈ NR) : tauD (A x)=0 := by
    rw [←tauD_row_equiv e (A x),hMatrix]
    have hh : tauD (tupleMatrix N O B R x)<1 := hDrop x hx
    omega
  have hBorn : IsSNCDivisor n BR := isSNCDivisor_of_sublist hER (List.sublist_append_right OR BR)
  have hUnit (x : Y) (hx : x ∈ NR) (i : Fin OR.length) :
      (oldMonomialPart NR OR BR i).mem x 1 := by
    have hNoProper : properRows (A x)=∅ := Finset.card_eq_zero.mp (hZero x hx)
    have hRowZero : rowOrder (A x) i=0 := by
      by_contra hne
      have hi : i ∈ properRows (A x) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
      rw [hNoProper] at hi
      exact Finset.notMem_empty i hi
    have hColumns (j : Fin BR.length) : A x i j=0 := by
      have hj : A x i j ≤ rowOrder (A x) i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hp := actual_old_parts_geometry hn hNR hER hTrR hDenseR i
    exact HironakaG4CanonicalZeroRowUnit.one_mem_of_zero_canonical_row hn hNR hBorn hTrR
      hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hx hColumns
  have hNC := (prepared_selected_born_centre_geometry hn hNR hER hTrR hDenseR
    hOrdR hPrepR (∅ : Finset (Fin BR.length))
    (fun x hx i hNot => (hNot (hUnit x hx.1 i)).elim)).2
  have hEmpty : NR ∩ BoundaryCount.memberInter BR ∅=NR := by
    ext x
    simp [BoundaryCount.memberInter]
  rw [hEmpty] at hNC
  have hBoundary : (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) R).E=OR ++ BR := by
    have h := full_ordered N O.get B R
    have ho : List.ofFn O.get=O := List.ofFn_get O
    have ht : (List.ofFn fun i => strictAlong R (O.get i))=O.map (strictAlong R) := by
      simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map O (strictAlong R)
    rw [ho,ht] at h
    exact h
  refine ⟨Y,R,hCarrier,hFull,hSharp,?_,hNR,?_,?_,hEqR⟩
  · intro x hx
    have hh : tauD (tupleMatrix N O B R x)<1 := hDrop x hx
    omega
  · rw [hBoundary]
    exact hER
  · rw [hBoundary]
    exact hNC

private theorem original_tuple_count (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (R : BlowupTower Y Z) (x : Z) :
    tauD (factorMatrix W E (T.append R) x)=
      tauD (tupleMatrix (strictAlong T W) (E.map (strictAlong T))
        (geoTransformAlong (geometricTemplate W []) T).E R x) := by
  let O := E.map (strictAlong T)
  let e : Fin E.length ≃ Fin O.length := finCongr (by simp [O])
  have hGet (i : Fin E.length) : O.get (e i)=strictAlong T (E.get i) := by simp [O,e]
  let A := geoTransformAlong (geometricTemplate W []) T
  have hTemplate : A=geometricTemplate (strictAlong T W) A.E := template_current W [] T
  unfold factorMatrix oldFactor
  rw [geoTransformAlong_append]
  change tauD (fun i j => divExpAlong n
    (geoTransformAlong A R).N
    (monomialPartAlong n (geoTransformAlong A R).N
      (restrictOn n (geoTransformAlong A R).N
        (vanishingIdeal (n := n) (strictAlong (T.append R) (E.get i))))
      (geoTransformAlong A R).E) ((geoTransformAlong A R).E.get j) x)=_
  rw [hTemplate]
  rw [←tauD_row_equiv e]
  congr 1
  funext i j
  simp only [O] at hGet
  simp only [tupleMatrix,N_geoTransformAlong,MemberInterLocusAlong.strictAlong_append]
  rw [hGet]
  rfl

private theorem current_full_template (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) :
    geoTransformAlong (geometricTemplate (univ : Set X) E) T=
      geometricTemplate (univ : Set Y) (E.map (strictAlong T) ++
        (geoTransformAlong (geometricTemplate W []) T).E) := by
  rw [template_current,strict_univ,
    HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T]


/-- **The count-one branch, equivariantly**: the conclusions of
`HironakaActualProcessedSharpCleanup.exists_actual_count_one_sharp_cleanup` (after the equivariance clause, which comes
first). -/
theorem exists_actual_count_one_sharp_cleanup_equivariant (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hPrepared : let A := geoTransformAlong (geometricTemplate W []) T
      ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x)
    (hCount : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      tauD (factorMatrix W E T x) ≤ 1) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      (IsEquivariant W E T → IsEquivariant W E (T.append R)) ∧
      let U := T.append R
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      (∀ x ∈ A.N,tauD (factorMatrix W E U x)=0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧
      IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let N := strictAlong T W
  let O := E.map (strictAlong T)
  let B := A.E
  have hN : A.N=N := N_geoTransformAlong _ _
  have hD := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  change IsClosedSubmanifold n A.N ∧ IsSNCDivisor n (O ++ B) ∧ IsTransverse n A.N B ∧
    A.N ⊆ closure (A.N \ ⋃ H ∈ O ++ B,H) ∧ _ at hD
  rw [hN] at hD
  let e : Fin E.length ≃ Fin O.length := finCongr (by simp [O])
  have hGet (i : Fin E.length) : O.get (e i)=strictAlong T (E.get i) := by simp [O,e]
  have hRow (i : Fin E.length) : oldResidualPart N O B (e i)=
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal := by
    unfold oldResidualPart oldTraceIdeal
    rw [hGet]
    exact (hD.2.2.2.2 i).2.2.1
  have hOrdN : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1 := by
    intro x hx i
    have h := hOrd x (hN.symm ▸ hx) (e.symm i)
    change ordinaryTraceOrder A.N _ x ≤ 1 at h
    rw [hN,←hRow (e.symm i),e.apply_symm_apply] at h
    exact h
  have hPrepN : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x := by
    change ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N O B x at hPrepared
    rw [hN] at hPrepared
    exact hPrepared
  have hCountN : ∀ x ∈ N,tauD (tupleMatrix N O B (.refl : BlowupTower Y Y) x) ≤ 1 := by
    intro x hx
    rw [←original_tuple_count W E T (.refl : BlowupTower Y Y) x]
    exact hCount x (hN.symm ▸ hx)
  obtain ⟨hBad,_hOverT⟩ := HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
    hW.1 hE.1 T hSharp
  have hBoundary := HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T
  have hBadSub : originalSharpBadLocus (n := n) N (O ++ B) ⊆
      T.proj ⁻¹' originalSharpBadLocus (n := n) W E := by
    rw [←hBoundary]
    exact hBad
  have hCompact : IsCompact (originalSharpBadLocus (n := n) N (O ++ B)) :=
    ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
      (isClosed_originalSharpBadLocus hD.1.1 hD.2.1.1) hBadSub
  obtain ⟨Z,R,hNative,hNativeFull,hNativeSharp,hZero,hSmooth,hSNC,hNC,hEqNative⟩ :=
    native_count_one_cleanup hn hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hCompact hOrdN hPrepN hCountN
  have hTemplate : A=geometricTemplate N B := template_current W [] T
  have hFullTemplate : geoTransformAlong (geometricTemplate (univ : Set X) E) T=
      geometricTemplate (univ : Set Y) (O ++ B) := current_full_template W E T
  have hTestU : IsGeoTestTower (geometricTemplate W []) (T.append R) := by
    apply (isGeoTestTower_append_iff _ T R).mpr
    refine ⟨hT,?_⟩
    change IsGeoTestTower A R
    rw [hTemplate]
    exact hNative
  have hFullU : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R) := by
    apply (isGeoTestTower_append_iff _ T R).mpr
    exact ⟨hFull,hFullTemplate.symm ▸ hNativeFull⟩
  have hSharpU : CurrentSharpCentres W E (T.append R) := by
    apply currentSharp_append W E T R hSharp
    rw [hBoundary]
    exact hNativeSharp
  have hOverU := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
    hW.1 hE.1 (T.append R) hSharpU).2
  have hCarrier : (geoTransformAlong (geometricTemplate W []) (T.append R)).N=strictAlong R N := by
    rw [geoTransformAlong_append]
    change (geoTransformAlong A R).N=_
    rw [hTemplate,N_geoTransformAlong]
    rfl
  have hFullBoundary : (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append R)).E=
      (geoTransformAlong (geometricTemplate (univ : Set Y) (O ++ B)) R).E := by
    rw [geoTransformAlong_append,hFullTemplate]
  have hSeq := HironakaAdmissibleSequence.isAdmissibleBlowupSequence_proj
    (geometricTemplate (univ : Set X) E) (originalSharpBadLocus (n := n) W E)
    (T.append R) hFullU hOverU
  have hEqClause : IsEquivariant W E T → IsEquivariant W E (T.append R) := by
    intro hEqT
    have hFull' : IsGeoTestTower (geometricTemplate (univ : Set X) (E ++ [])) T := by
      rw [List.append_nil]
      exact hFull
    have hEqT' : IsEquivariant W (E ++ []) T := by
      rw [List.append_nil]
      exact hEqT
    have hEqR : IsEquivariant (geoTransformAlong (geometricTemplate W []) T).N
        (E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E) R := by
      change IsEquivariant A.N (O ++ B) R
      rw [hN]
      exact hEqNative
    have h := IsEquivariant.append_of_current hW T hT hFull' hEqT' R hEqR
    rw [List.append_nil] at h
    exact h
  refine ⟨Z,R,hEqClause,hTestU,hFullU,hSharpU,hOverU,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    rw [original_tuple_count W E T R x]
    exact hZero x (hCarrier ▸ hx)
  · exact hCarrier.symm ▸ hSmooth
  · exact hFullBoundary.symm ▸ hSNC
  · rw [hCarrier,hFullBoundary]
    exact hNC
  · exact HironakaAdmissibleCalculus.isProperMap_of_isBlowupSequence hSeq.isBlowupSequence
  · exact HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hSeq


private def originalReady (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) : Prop :=
  let A := geoTransformAlong (geometricTemplate W []) T
  IsGeoTestTower (geometricTemplate W []) T ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
    CurrentSharpCentres W E T ∧
    (∀ x ∈ A.N,∀ i : Fin E.length,ordinaryTraceOrder A.N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1) ∧
    (∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x)

private def cleanupEndpoint (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (U : BlowupTower X Y) : Prop :=
  let A := geoTransformAlong (geometricTemplate W []) U
  let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
  IsGeoTestTower (geometricTemplate W []) U ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
    CurrentSharpCentres W E U ∧
    RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
    (∀ x ∈ A.N,tauD (factorMatrix W E U x)=0) ∧
    IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
    IsProperMap U.proj ∧
    IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ

/-- **Full sharp cleanup of the original processed phase, equivariantly**: the conclusions of
`HironakaActualProcessedSharpCleanup.exists_actual_processed_sharp_cleanup` (after the equivariance clause, which comes
first). -/
theorem exists_actual_processed_sharp_cleanup_equivariant (hn : 0 < n) {W : Set X} {E : List (Set X)}
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
      ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x) :
    ∃ (Z : CMfd.{u} n) (R : BlowupTower Y Z),
      (IsEquivariant W E T → IsEquivariant W E (T.append R)) ∧
      let U := T.append R
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      RestrictEmptyTower.CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      (∀ x ∈ A.N,tauD (factorMatrix W E U x)=0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧
      IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  obtain ⟨Z,R,hHeads,hCount,hEqR⟩ := exists_actual_processed_count_at_most_one_equivariant
    hn hW hE hdense T hT hFull hSharp hK hOrd hNC hDenseS hPrepared
  have hReady : originalReady W E (T.append (BlowupTowerSplit.split R 0).2.1) := by
    have h := hHeads 0
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.2.2.1⟩
  rw [StepOneEmptyPrefix.split_zero R] at hReady
  rcases hReady with ⟨hTR,hFullR,hSharpR,hOrdR,hPrepR⟩
  obtain ⟨V,S,hEqS,hS⟩ := exists_actual_count_one_sharp_cleanup_equivariant hn hW hE hdense
    (T.append R) hTR hFullR hSharpR hK hOrdR hPrepR hCount
  refine ⟨V,R.append S,isEquivariant_clause_trans hEqR hEqS,?_⟩
  change cleanupEndpoint W E (T.append (R.append S))
  rw [←BlowupTower.append_assoc]
  exact hS

end Sharp

section Original
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower NormalCrossings
  HironakaG4PreparedCentreCoordinates HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualChronologicalStrictStep HironakaActualProcessedMaskFiniteBlock
  HironakaActualOriginalProcessedJointPreparedness
  HironakaG4RecordedTowerResidualCompatibility HironakaSharpActualCurveWholeBoundaryTransversality
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong GermIdealOrder
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossingsComparison
  HironakaG4MonomialFamilyInvariant HironakaG4CompactWholeMonomialMaskPhase
  HironakaG34MaskFoldEquivariance

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **Genuine K3 processed cleanup, equivariantly**: the conclusions of
`HironakaActualOriginalProcessedSharpCleanup.exists_actual_original_processed_sharp_cleanup` (after the equivariance
clause, which comes first). -/
theorem exists_actual_original_processed_sharp_cleanup_equivariant (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W\⋃H∈E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hK : IsCompact (originalSharpBadLocus (n:=n) W E))
    (hOrd : ∀x∈(geoTransformAlong (geometricTemplate W []) T).N,
      ∀i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x≤1)
    (hNC : ∀i : Fin E.length,
      let A:=geoTransformAlong (geometricTemplate W []) T
      let S:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val++A.E))
    (hDenseS : ∀i : Fin E.length,
      let A:=geoTransformAlong (geometricTemplate W []) T
      let S:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S⊆closure (S\⋃H∈(E.map (strictAlong T)).eraseIdx i.val++A.E,H)) :
    ∃(Z : CMfd.{u} n)(R : BlowupTower Y Z),
      (IsEquivariant W E T → IsEquivariant W E (T.append R)) ∧
      let U:=T.append R
      let A:=geoTransformAlong (geometricTemplate W []) U
      let F:=(geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      RestrictEmptyTower.CentresOver (originalSharpBadLocus (n:=n) W E) U ∧
      (∀x∈A.N,tauD (factorMatrix W E U x)=0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n:=n) W E)ᶜ ∧
      ∀k : ℕ,
        let P:=BlowupTowerSplit.head U k
        let B:=geoTransformAlong (geometricTemplate W []) P
        let G:=(geoTransformAlong (geometricTemplate (univ : Set X) E) P).E
        G=E.map (strictAlong P)++B.E ∧ B.E.length=P.length ∧ G.length=E.length+P.length ∧
          ∀i : Fin E.length,
            let I:=restrictOn n B.N (vanishingIdeal (n:=n) (strictAlong P (E.get i)))
            let D:=monomialPartAlong n B.N I B.E
            let J:=chronologicalMarked (originalRelativeMemberMarked W (E.get i)) P
            J.N=B.N ∧ J.E=B.E ∧ J.d=0 ∧ J.IsWellFormed ∧
              I.IsCoherent ∧ D.IsCoherent ∧
              nonmonomialPartAlong n B.N I B.E=J.ideal ∧
              I=restrictOn n B.N (D.mul J.ideal) := by
  have hPrepared:=actual_original_processed_joint_preparedness hn hW hE hdense
    T hT hFull hOrd hNC hDenseS
  obtain ⟨Z,R,hEqR,hU,hUF,hUS,hOver,hZero,hSmooth,hSNC,hFinalNC,hProper,hIso⟩:=
    exists_actual_processed_sharp_cleanup_equivariant
      hn hW hE hdense T hT hFull hSharp hK hOrd hNC hDenseS hPrepared
  refine ⟨Z,R,hEqR,hU,hUF,hUS,hOver,hZero,hSmooth,hSNC,hFinalNC,hProper,hIso,?_⟩
  intro k
  have hHead:=((BlowupTowerSplit.isGeoTestTower_iff_head_tail
    (geometricTemplate W []) (T.append R) k).mp hU).1
  have hHeadFull:=((BlowupTowerSplit.isGeoTestTower_iff_head_tail
    (geometricTemplate (univ : Set X) E) (T.append R) k).mp hUF).1
  exact HironakaActualOriginalProcessedSharpCleanup.actual_original_tower_parts_and_clocks hn hW hE hdense
    (BlowupTowerSplit.head (T.append R) k) hHead hHeadFull


end Original

section AllDimensions
open Classical
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualEmptyChronologicalDefect
  HironakaActualProcessedMaskFiniteBlock HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpActualCurveWholeBoundaryTransversality HironakaG4SharpBadFootprint
  HironakaSharpOriginalProductTraceOrder
  HironakaG4MonomialFamilyInvariant HironakaSNCSupportedMonomialIdeal
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  IdealWeightPowers InvertibleIdealQuotient DivisorExponentAlong GermIdealOrder MonomialPartAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower HironakaAdmissibleSequence
  HironakaAdmissibleCalculus
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
open HironakaG34MaskFoldEquivariance

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **K3 in ALL ambient dimensions, equivariantly**: the conclusions of
`HironakaActualOriginalProcessedSharpCleanupAllDimensions.exists_actual_original_processed_sharp_cleanup_all_dimensions`
(after the equivariance clause, which comes first): an equivariant prefix stays equivariant. -/
theorem exists_actual_original_processed_sharp_cleanup_all_dimensions_equivariant {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W\⋃H∈E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hK : IsCompact (originalSharpBadLocus (n:=n) W E))
    (hOrd : ∀x∈(geoTransformAlong (geometricTemplate W []) T).N,
      ∀i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x≤1)
    (hNC : ∀i : Fin E.length,
      let A:=geoTransformAlong (geometricTemplate W []) T
      let S:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val++A.E))
    (hDenseS : ∀i : Fin E.length,
      let A:=geoTransformAlong (geometricTemplate W []) T
      let S:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S⊆closure (S\⋃H∈(E.map (strictAlong T)).eraseIdx i.val++A.E,H)) :
    ∃(Z : CMfd.{u} n)(R : BlowupTower Y Z),
      (IsEquivariant W E T → IsEquivariant W E (T.append R)) ∧
      let U:=T.append R
      let A:=geoTransformAlong (geometricTemplate W []) U
      let F:=(geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n:=n) W E) U ∧
      (∀x∈A.N,tauD (factorMatrix W E U x)=0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n:=n) W E)ᶜ ∧
      ∀k : ℕ,
        let P:=BlowupTowerSplit.head U k
        let B:=geoTransformAlong (geometricTemplate W []) P
        let G:=(geoTransformAlong (geometricTemplate (univ : Set X) E) P).E
        G=E.map (strictAlong P)++B.E ∧ B.E.length=P.length ∧ G.length=E.length+P.length ∧
          ∀i : Fin E.length,
            let I:=restrictOn n B.N (vanishingIdeal (n:=n) (strictAlong P (E.get i)))
            let D:=monomialPartAlong n B.N I B.E
            let J:=chronologicalMarked (originalRelativeMemberMarked W (E.get i)) P
            J.N=B.N ∧ J.E=B.E ∧ J.d=0 ∧ J.IsWellFormed ∧
              I.IsCoherent ∧ D.IsCoherent ∧
              nonmonomialPartAlong n B.N I B.E=J.ideal ∧
              I=restrictOn n B.N (D.mul J.ideal) := by
  by_cases hn : 0<n
  · exact exists_actual_original_processed_sharp_cleanup_equivariant
      hn hW hE hdense T hT hFull hSharp hK hOrd hNC hDenseS
  · have hn0 : n=0:=Nat.eq_zero_of_not_pos hn
    subst n
    refine ⟨Y,.refl,fun h => h,?_⟩
    exact HironakaActualOriginalProcessedSharpCleanupAllDimensions.zero_current_sharp_endpoint hW hE T hSharp


end AllDimensions

end
end Hironaka.HironakaG34ProcessedCleanupEquivariance
