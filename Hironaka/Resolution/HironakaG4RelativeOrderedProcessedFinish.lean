import Hironaka.Resolution.HironakaG4OrderedProcessedHeadAppend
import Hironaka.Resolution.HironakaG4OrderedProcessedFlatten
import Hironaka.Resolution.HironakaG4RelativeProcessedMasks
import Hironaka.Resolution.HironakaG4ProcessedCountOneNearCompact

/-! Fixed descending mask phases for the compact-relative sharp finish. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4RelativeOrderedProcessedFinish

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsInvariance
  HironakaSharpActualFiniteChronologicalHistory HironakaG34NonPureLowDim
  HironakaG4OrderedProcessedMaskHistory HironakaG4SharpTerminalAtlas
  HironakaG4OrderedProcessedHeadAppend HironakaG4OrderedProcessedFlatten
  HironakaG4RelativeProcessedMasks HironakaG4ProcessedCountOneNearCompact
  HironakaActualProcessedAllMasksDrop HironakaActualProcessedMaskFiniteBlock
  HironakaG4MonomialFamilyInvariant MaxLocusLocal HomogenizedGlueingTower

variable {n : ℕ} {X Y : CMfd.{u} n} {ι : Type v}

/-- An actual finishing tower on one literal base window, carrying the
given chronological list of phases. -/
def OrderedProcessedFinishNear (hn : 0 < n) (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (mask : ι → Finset (Fin E.length)) (L : List ι) (K : Set X) : Prop :=
  ∃ O : Opens X,K ⊆ O ∧ ∃ (Z : CMfd.{u} n) (S : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
    let v := (Subtype.val : O → X)
    let WO := v ⁻¹' W
    let EO := E.map (v ⁻¹' ·)
    let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
    let T₀ := restrict O T
    OrderedProcessedMaskHistory hn WO EO T₀ (fun a => (mask a).map e.toEmbedding) S L.reverse ∧
    IsSharpTerminalTower WO EO (T₀.append S)

/-- The chosen lists are followed in descending positive count. -/
def descendingMaskLabels (F : ℕ → List ι) : ℕ → List ι
  | 0 | 1 => F 1
  | q + 2 => F (q+2) ++ descendingMaskLabels F (q+1)

private theorem near_of_count_one (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hAt : At W E 1 T)
    [DecidableEq ι] (L : List ι) (mask : ι → Finset (Fin E.length))
    (hLabels : (L.map mask).toFinset = (Finset.univ : Finset (Fin E.length)).powersetCard 1)
    (K : Set X) (hK : IsCompact K) :
    OrderedProcessedFinishNear hn W E T mask L K := by
  obtain ⟨O,hKO,Z,Q,hTape,hT,hFull,hSharp,_hOver,_hZero,_hSmooth,_hSNC,hNC,_hProper,_hIso⟩ :=
    exists_labelled_processed_count_one_cleanup_near_compact hn hW hE hdense T hAt L mask hLabels K hK
  refine ⟨O,hKO,Z,Q,hTape,hT,hFull,hSharp,?_⟩
  let U := (restrict O T).append Q
  let W₀ := (Subtype.val : O → X) ⁻¹' W
  have hN : (geoTransformAlong (geometricTemplate W₀ []) U).N = strictAlong U W₀ :=
    N_geoTransformAlong _ _
  change HasNormalCrossings n (strictAlong U W₀) _
  rw [←hN]
  exact hNC

set_option maxHeartbeats 1400000 in
private theorem finish_mask_level (hn : 0 < n) (q : ℕ) (hq : 2 ≤ q)
    (F : ℕ → List ι) (lower : List ι)
    (finishLower : ∀ {X Y : CMfd.{u} n} {W : Set X} {E : List (Set X)},
      IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
      ∀ (T : BlowupTower X Y), At W E (q-1) T →
      ∀ (mask : ι → Finset (Fin E.length)),
        (∀ j,((F j).map mask).toFinset = (Finset.univ : Finset (Fin E.length)).powersetCard j) →
        ∀ (K : Set X), IsCompact K → OrderedProcessedFinishNear hn W E T mask lower K) :
    ∀ (L : List ι) {X Y : CMfd.{u} n} {W : Set X} {E : List (Set X)},
      IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
      ∀ (T : BlowupTower X Y), At W E q T →
      ∀ (mask : ι → Finset (Fin E.length)),
        (∀ j,((F j).map mask).toFinset = (Finset.univ : Finset (Fin E.length)).powersetCard j) →
        (∀ a ∈ L,(mask a).card = q) → MasksRemaining W E q T (L.map mask).toFinset →
        ∀ (K : Set X), IsCompact K → OrderedProcessedFinishNear hn W E T mask (L ++ lower) K := by
  intro L
  induction L with
  | nil =>
    intro X Y W E hW hE hdense T hAt mask hCover _hSizes hRemain K hK
    obtain ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,hPrep,hCount⟩ := hAt
    have hAtLower : At W E (q-1) T := by
      refine ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,hPrep,?_⟩
      intro x hx
      have hStrict := global_count_lt_of_all_masks (factorMatrix W E T x) (hCount x hx)
        (fun P hP => hRemain P (Finset.mem_powersetCard.mp hP).2 (by simp) x hx)
      omega
    exact finishLower hW hE hdense T hAtLower mask hCover K hK
  | cons label L ih =>
    intro X Y W E hW hE hdense T hAt mask hCover hSizes hRemain K hK
    let P := mask label
    let Rem := ((label :: L).map mask).toFinset
    have hP : P.card = q := hSizes label (List.mem_cons_self)
    obtain ⟨O,hKO,Z,S,hDom,hCan,hRes,hForward,hRemain₀⟩ :=
      exists_relative_processed_canonical_mask_erase hn hW hE hdense T q hq Rem P hP hAt hRemain K hK
    let v := (Subtype.val : O → X)
    let WO := v ⁻¹' W
    let EO := E.map (v ⁻¹' ·)
    let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
    let L₀ := restrict O T
    let R := L₀.append S
    let maskO := fun a => (mask a).map e.toEmbedding
    have hWO : IsClosedSubmanifold n WO := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O
    have hEO : IsSNCDivisor n EO := isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) O) continuous_subtype_val hE
    have hDenseO : WO ⊆ closure (WO \ ⋃ H ∈ EO,H) := open_full_density hdense O
    have hCompactO : IsCompact (v ⁻¹' K) :=
      (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
        (fun x hx => ⟨⟨x,hKO hx⟩,rfl⟩)).mpr hK
    have hState : At WO EO q R := (forward_end L₀ S hForward).1
    have hCoverO (j : ℕ) : ((F j).map maskO).toFinset =
        (Finset.univ : Finset (Fin EO.length)).powersetCard j := by
      unfold maskO
      rw [show (fun a => (mask a).map e.toEmbedding) =
        (fun P => P.map e.toEmbedding) ∘ mask from rfl,←List.map_map]
      exact mask_cover_reindex ((F j).map mask) e (hCover j)
    have hSizesO (a : ι) (ha : a ∈ L) : (maskO a).card = q := by
      rw [Finset.card_map]
      exact hSizes a (List.mem_cons_of_mem _ ha)
    have hRemainO : MasksRemaining WO EO q R (L.map maskO).toFinset := by
      intro U hU hNot
      apply hRemain₀ U hU
      rintro hMem
      obtain ⟨U₀,hU₀,rfl⟩ := Finset.mem_map.mp hMem
      obtain ⟨a,ha,hEq⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_of_mem_erase hU₀))
      have haL : a ∈ L := by
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ((Finset.mem_erase.mp hU₀).1 hEq.symm).elim
        · exact ha
      apply hNot
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,haL,congrArg (fun M => M.map e.toEmbedding) hEq⟩)
    obtain ⟨J,hKJ,hChart⟩ :=
      ih hWO hEO hDenseO R hState maskO hCoverO hSizesO hRemainO (v ⁻¹' K) hCompactO
    let V : Opens X := ⟨v '' (J : Set O),O.isOpen.isOpenMap_subtype_val _ J.isOpen⟩
    have hVO : V ≤ O := by
      rintro _ ⟨x,_hx,rfl⟩
      exact x.property
    have hJV : J = nestedOpens O V := by
      ext x
      constructor
      · intro hx
        exact ⟨x,hx,rfl⟩
      · rintro ⟨y,hy,he⟩
        exact (Subtype.ext he : y = x) ▸ hy
    rw [hJV] at hChart
    obtain ⟨B,Q,hTape,hEnd⟩ := hChart
    obtain ⟨C,Q₀,hTape₀,hEnd₀⟩ :=
      ordered_processed_head_append hn hWO hEO hDenseO L₀ S hState.1 hState.2.1
        maskO label ⟨hDom,hCan,hRes⟩ (nestedOpens O V) Q (L ++ lower).reverse hTape hEnd
    let EJ := EO.map ((Subtype.val : nestedOpens O V → O) ⁻¹' ·)
    let eJ : Fin EO.length ≃ Fin EJ.length := finCongr (List.length_map _).symm
    let eAll : Fin E.length ≃ Fin EJ.length := finCongr (by simp [EJ,EO])
    have hMask (a : ι) : (maskO a).map eJ.toEmbedding = (mask a).map eAll.toEmbedding := by
      unfold maskO
      rw [Finset.map_map]
      congr 1
    change OrderedProcessedMaskHistory (X := CMfd.of (n := n) (nestedOpens O V)) hn
      ((Subtype.val : nestedOpens O V → O) ⁻¹' WO) EJ (restrict (nestedOpens O V) L₀)
      (fun a => (maskO a).map eJ.toEmbedding) Q₀ ((L ++ lower).reverse ++ [label]) at hTape₀
    simp only [hMask] at hTape₀
    obtain ⟨D,Q₁,hTape₁,hEnd₁⟩ :=
      ordered_processed_flatten hn hW hE hdense T mask ((L ++ lower).reverse ++ [label]) hVO Q₀ hTape₀ hEnd₀
    refine ⟨V,?_,D,Q₁,?_,hEnd₁⟩
    · intro x hx
      exact ⟨⟨x,hKO hx⟩,hKJ hx,rfl⟩
    · simpa using hTape₁

/-- The same fixed descending list of actual mask phases finishes around
any compact enclosure. The full original prefix is literally restricted. -/
theorem exists_ordered_processed_finish_near (hn : 0 < n) [DecidableEq ι]
    (F : ℕ → List ι) (q : ℕ) :
    ∀ {X Y : CMfd.{u} n} {W : Set X} {E : List (Set X)},
      IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
      ∀ (T : BlowupTower X Y), At W E q T →
      ∀ (mask : ι → Finset (Fin E.length)),
      (∀ j,((F j).map mask).toFinset = (Finset.univ : Finset (Fin E.length)).powersetCard j) →
      ∀ (K : Set X), IsCompact K → OrderedProcessedFinishNear hn W E T mask (descendingMaskLabels F q) K := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro X Y W E hW hE hdense T hAt mask hCover K hK
    by_cases hq : q ≤ 1
    · obtain ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,hPrep,hCount⟩ := hAt
      have hAt₁ : At W E 1 T :=
        ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,hPrep,fun x hx => (hCount x hx).trans hq⟩
      have hEnd := near_of_count_one hn hW hE hdense T hAt₁ (F 1) mask (hCover 1) K hK
      interval_cases q <;> exact hEnd
    · have hq₂ : 2 ≤ q := by omega
      have hSizes (a : ι) (ha : a ∈ F q) : (mask a).card = q := by
        have hm : mask a ∈ ((F q).map mask).toFinset := List.mem_toFinset.mpr
          (List.mem_map.mpr ⟨a,ha,rfl⟩)
        rw [hCover q] at hm
        exact (Finset.mem_powersetCard.mp hm).2
      have hRemain : MasksRemaining W E q T ((F q).map mask).toFinset := by
        intro P hP hNot
        exact (hNot (by rw [hCover q]; exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hP⟩)).elim
      have hEnd := finish_mask_level hn q hq₂ F (descendingMaskLabels F (q-1))
        (ih (q-1) (by omega)) (F q) hW hE hdense T hAt mask hCover hSizes hRemain K hK
      match q with
      | q + 2 => exact hEnd

end
end Hironaka.HironakaG4RelativeOrderedProcessedFinish
