import Hironaka.Resolution.HironakaG4ProcessedMaskNearCompact

/-! A processed mask step on an actual restricted prefix. Previously
erased masks remain erased on the same physical continuation. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4RelativeProcessedMasks

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFiniteChronologicalHistory HironakaG4MonomialFamilyInvariant
  HironakaG4ProcessedMaskNearCompact HironakaG4ProcessedMaskRestriction
  CanonicalCentres HironakaActualProcessedAllMasksDrop HironakaActualProcessedMaskControlledSum HironakaActualProcessedMaskFiniteBlock
  HironakaG4RecordedTowerResidualCompatibility MarkedIdealBiholomorphism HomogenizedGlueingTower

open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The prescribed finite set contains every possible unerased mask of the
current cardinality. -/
def MasksRemaining (W : Set X) (E : List (Set X)) (q : ℕ) (T : BlowupTower X Y)
    (F : Finset (Finset (Fin E.length))) : Prop :=
  ∀ P : Finset (Fin E.length),P.card = q → P ∉ F → Erased W E T P

set_option maxHeartbeats 500000 in
/-- A chosen mask is erased near the entire compact enclosure, and masks
already erased stay erased. The same physical restricted prefix is
retained and every original label follows its literal position. -/
theorem exists_relative_processed_canonical_mask_erase (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (q : ℕ) (hq : 2 ≤ q)
    (F : Finset (Finset (Fin E.length))) (P : Finset (Fin E.length)) (hP : P.card = q)
    (hAt : At W E q T) (hOld : MasksRemaining W E q T F)
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X,K ⊆ O ∧ ∃ (Z : CMfd.{u} n) (S : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let v := (Subtype.val : O → X)
      let WO := v ⁻¹' W
      let EO := E.map (v ⁻¹' ·)
      let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
      let R := restrict O T
      let M := processedMaskMarked WO EO R (P.map e.toEmbedding)
      IsInvDomain (n+1) M ∧ IsCanonical M ((invFamily hn (n+1)).inv M) S ∧ IsGeoResolution M S ∧
      (∀ k : ℕ,Forward WO EO q R (BlowupTowerSplit.head S k)) ∧
      MasksRemaining WO EO q (R.append S) ((F.erase P).map e.finsetCongr.toEmbedding) := by
  have hAtP : At W E P.card T := hP.symm ▸ hAt
  obtain ⟨O,hKO,Z,S,hDom,hCan,hMask,hForward,hErase⟩ :=
    exists_processed_mask_canonical_block_near_compact hn hW hE hdense T P (hP.symm ▸ hq) hAtP K hK
  let v := (Subtype.val : O → X)
  let u := (Subtype.val : openPreimage T O → Y)
  let WO := v ⁻¹' W
  let EO := E.map (v ⁻¹' ·)
  let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
  let R := restrict O T
  have hFor (k : ℕ) : Forward WO EO q R (BlowupTowerSplit.head S k) := hP ▸ hForward k
  have hF := forward_end R S hFor
  let A := geoTransformAlong (geometricTemplate W []) T
  let A₀ := geoTransformAlong (geometricTemplate WO []) R
  let A₁ := geoTransformAlong (geometricTemplate WO []) (R.append S)
  have hA : A₀ = MarkedIdeal.pullback u A := original_carrier_template_restrict hW T hAt.1 O
  have hAN : A₀.N = u ⁻¹' A.N := congrArg MarkedIdeal.N hA
  have hGeom := actual_recorded_tower_residual_dictionary hn hW hE hdense T hAt.1 hAt.2.1
  have hClosed : IsClosed A₀.N := hAN.symm ▸ hGeom.1.1.preimage continuous_subtype_val
  have hMove : A₁.N ⊆ S.proj ⁻¹' A₀.N := by
    unfold A₁ A₀
    rw [geoTransformAlong_append,N_geoTransformAlong]
    exact MemberInterTowerAlong.strictAlong_subset_preimage S hClosed
  have hMatrix := (processed_mask_matrix_restrict hn hW hE hdense T hAt.1 hAt.2.1 O).2
  refine ⟨O,hKO,Z,S,hDom,hCan,hMask,hFor,?_⟩
  intro P₀ hCard hNot
  exact e.finsetCongr.surjective P₀ |>.elim fun Q hQ => by
    subst P₀
    by_cases hEq : Q = P
    · subst Q
      exact hErase
    have hNotOld : Q ∉ F := by
      intro hMem
      exact hNot (Finset.mem_map.mpr ⟨Q,Finset.mem_erase.mpr ⟨hEq,hMem⟩,rfl⟩)
    have hCardQ : Q.card = q := (Finset.card_map _).symm.trans hCard
    intro z hz hMask
    have hzS : S.proj z ∈ A₀.N := hMove hz
    have hu : (S.proj z).val ∈ A.N := by
      rw [hAN] at hzS
      exact hzS
    have hIn : Q ⊆ properRows (factorMatrix W E T (S.proj z).val) := by
      intro i hi
      rw [←(hMatrix (S.proj z)).1]
      refine Finset.mem_map.mpr ⟨e i,?_ ,e.symm_apply_apply i⟩
      exact (hF.2.2 z hz) (hMask (Finset.mem_map.mpr ⟨i,hi,rfl⟩))
    exact hOld Q hCardQ hNotOld _ hu hIn

set_option maxHeartbeats 500000 in
/-- A chosen mask is erased near the entire compact enclosure, and masks
already erased stay erased. The same physical restricted prefix is
retained and every original label follows its literal position. -/
theorem exists_relative_processed_mask_erase (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (q : ℕ) (hq : 2 ≤ q)
    (F : Finset (Finset (Fin E.length))) (P : Finset (Fin E.length)) (hP : P.card = q)
    (hAt : At W E q T) (hOld : MasksRemaining W E q T F)
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X,K ⊆ O ∧ ∃ (Z : CMfd.{u} n) (S : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let v := (Subtype.val : O → X)
      let WO := v ⁻¹' W
      let EO := E.map (v ⁻¹' ·)
      let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
      let R := restrict O T
      (∀ k : ℕ,Forward WO EO q R (BlowupTowerSplit.head S k)) ∧
      MasksRemaining WO EO q (R.append S) ((F.erase P).map e.finsetCongr.toEmbedding) := by

  obtain ⟨O,hKO,Z,S,_hDom,_hCan,_hMask,hForward,hRemaining⟩ :=
    exists_relative_processed_canonical_mask_erase hn hW hE hdense T q hq F P hP hAt hOld K hK
  exact ⟨O,hKO,Z,S,hForward,hRemaining⟩

end
end Hironaka.HironakaG4RelativeProcessedMasks
