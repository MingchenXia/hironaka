import Hironaka.Resolution.HironakaG4CartierCentreContactDrop
import Hironaka.Resolution.HironakaSharpActualPrincipalOrderOneTrace
import Hironaka.Resolution.HironakaSharpActualTraceIncidence
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Resolution.HironakaAdmissibleCalculus

set_option autoImplicit false

/-! A bounded genuine ambient Cartier cleanup retaining every born position.
Blueprint: `hironaka-g4-one-born-cartier-cleanup.tex`.
No general simultaneous monomial-family driver or sharp termination is claimed. -/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OneBornCartierCleanup

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold NormalCrossings
  NormalCrossingsComparison SimultaneousNormalCrossings MemberInterAlong MemberInterTowerAlong
  HironakaG4CartierCentreContactDrop HironakaSharpOriginalAllBoundaryCentre
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualFirstAmbientStrictExponent
  HironakaSharpActualPrincipalOrderOneTrace HironakaSharpActualTraceIncidence
  HironakaSharpActualFiniteChronologicalHistory HomogenizedGlueingTower
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong GermIdealOrder
  MarkedIdealOperationsAlong MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaAdmissibleSequence HironakaAdmissibleCalculus RestrictEmptyTower
  HironakaSharpOriginalDistinctDefectAnalytic HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalRestrictedDistinctDefectCentre HironakaSharpOriginalMultiBoundaryBadLocus
  AnalyticDimensionBasics

variable {n d : ℕ} {X Y : CMfd.{u} n}

/-- Every centre is the ENTIRE actual current trace of the same original
hypersurface on the same original carrier. No future history is an input. -/
def cartierCleanupSteps (N H : Set X) : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step P C _ _ => cartierCleanupSteps N H P ∧ C = strictAlong P N ∩ strictAlong P H

private theorem ordinaryTraceOrder_restrictOn_eq {N : Set X}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hI : I.IsCoherent) (x : X) :
    ordinaryTraceOrder N (restrictOn n N I) x = ordinaryTraceOrder N I x := by
  apply NonmonomialOrderLocal.nmOrd_congr
  intro q
  rw [ordGe_ordinaryTraceMarked_eq_cosupport N (restrictOn n N I)
      (isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hN)),
    ordGe_ordinaryTraceMarked_eq_cosupport N I hI]
  exact ⟨fun h => cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hI) q h,
    fun h => cosupport_subset_of_restrictLe restrictLe_restrictOn q h⟩

private theorem regularAtDim_transverse_member (hn : 0 < n)
    {N F : Set X} (hN : IsClosedSubmanifold n N) (hF : IsSNCDivisor n [F])
    (hT : IsTransverse n N [F])
    (hrN : ∀ x ∈ N, RegularAtDim (n := n) N x (d+1))
    {x : X} (hx : x ∈ N ∩ F) : RegularAtDim (n := n) (N ∩ F) x d := by
  let A := restrictOn n N (vanishingIdeal (n := n) F)
  obtain ⟨hcA, hnzA, hprA, horder⟩ := actual_normalized_transverse_member_geometry hn hN hF hT
  obtain ⟨f, hf, hgen⟩ := hprA x hx.1
  obtain ⟨_U, _u, _hxU, _hu, _hux, _hgerm, _hideal, k, hNk, hCk⟩ :=
    actual_orderOne_relative_reduced_trace hN hcA hnzA hx.1 f hf hgen (horder x hx)
  have hk : k = d+1 := RegularPointDimension.eq_of_regularAtDim hNk (hrN x hx.1)
  have hFclosed := hF.1 F (by simp)
  have hcF : (vanishingIdeal (n := n) F).IsCoherent := by
    simpa using VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn hF (0 : Fin [F].length))
  have hzero : N ∩ A.zeroLocus = N ∩ F := by
    ext y
    apply and_congr_right
    intro hyN
    exact (zeroLocus_restrictOn_iff hcF hyN).trans (by
      rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hFclosed])
  rw [hzero, hk] at hCk
  simpa only [Nat.add_sub_cancel] using hCk

/-- The actual common trace is a shared trace of two distinct ambient positions,
so it lies in the original sharp bad locus, including when its contact is one. -/
theorem one_born_trace_subset_sharpBad (hn : 0 < n) {N H F : Set X}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n [H,F])
    (hT : IsTransverse n N [F])
    (hrN : ∀ x ∈ N, RegularAtDim (n := n) N x (d+1))
    (hdense : N ⊆ closure (N \ H)) (heq : N ∩ H = N ∩ F) :
    N ∩ H ⊆ originalSharpBadLocus (n := n) N [H,F] := by
  have hF : IsSNCDivisor n [F] := isSNCDivisor_of_sublist hE (by simp)
  have hdiff : N \ ⋃ K ∈ [H,F], K = N \ H := by
    ext x
    constructor
    · rintro ⟨hxN, hx⟩
      exact ⟨hxN, fun hxH => hx (mem_iUnion₂.mpr ⟨H, by simp, hxH⟩)⟩
    · rintro ⟨hxN, hxH⟩
      refine ⟨hxN, ?_⟩
      rintro hx
      obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hx
      rcases List.mem_cons.mp hK with rfl | hK
      · exact hxH hxK
      · have hKF : K = F := List.mem_singleton.mp hK
        have hxF : x ∈ N ∩ F := ⟨hxN, hKF ▸ hxK⟩
        exact hxH (heq.symm ▸ hxF).2
  have hDenseE : N ⊆ closure (N \ ⋃ K ∈ [H,F], K) := by
    rwa [hdiff]
  intro x hx
  apply originalDistinctDefectPhase_subset_sharpBad hn hN hE hDenseE
  rw [originalDistinctDefectPhase_eq_finite_geometric_loci hn hN hE hDenseE d hrN]
  right
  have hpair : N ∩ H ∩ F = N ∩ F := by
    rw [heq, inter_assoc, inter_self]
  have hloc : LocDimGE (n := n) (N ∩ H ∩ F) x d := by
    rw [hpair]
    exact AnalyticDimensionBasics.locDimGE_of_regularAtDim
      (regularAtDim_transverse_member hn hN hF hT hrN (heq ▸ hx))
  apply mem_iUnion.mpr
  refine ⟨(0 : Fin [H,F].length), mem_iUnion.mpr ⟨(1 : Fin [H,F].length), ?_⟩⟩
  simpa using hloc

private theorem hasNormalCrossings_cons_of_disjoint {N H : Set X} {E : List (Set X)}
    (hT : IsTransverse n N E) (hdisj : Disjoint N H) : HasNormalCrossings n N (H :: E) := by
  intro x hx
  obtain ⟨S₀, S, ⟨Φ, ht, h0, hfamily⟩, hcard⟩ := hT x hx
  let S' : Fin (H :: E).length → Finset (Fin n) := Fin.cases ∅ S
  refine ⟨S₀, S', ⟨Φ, ht, h0, ?_⟩, ?_⟩
  · rintro (_ | i) hi
    · exact hfamily none hi
    · cases i using Fin.cases with
      | zero => exact False.elim (Set.disjoint_left.mp hdisj hx hi)
      | succ j => exact hfamily (some j) hi
  · intro i hi
    cases i using Fin.cases with
    | zero => exact False.elim (Set.disjoint_left.mp hdisj hx hi)
    | succ j => exact (hcard j hi).1

private theorem strictAlong_isClosed {B : Set X} (hB : IsClosed B) :
    ∀ {Y : CMfd.{u} n} (P : BlowupTower X Y), IsClosed (strictAlong P B)
  | _, .refl => hB
  | _, .step _ _ _ _ => isClosed_closure

private theorem strictAlong_subset_preimage {B : Set X} (hB : IsClosed B) :
    ∀ {Y : CMfd.{u} n} (P : BlowupTower X Y), strictAlong P B ⊆ P.proj ⁻¹' B
  | _, .refl => subset_rfl
  | _, .step P C π hπ => by
    intro z hz
    have hy := geoStrictTransform_subset_preimage hπ.contMDiff.continuous
      (strictAlong_isClosed hB P) hz
    exact strictAlong_subset_preimage hB P hy

theorem one_le_trace_order_iff (hn : 0 < n) {N H : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hdense : N ⊆ closure (N \ H)) {x : X} (hx : x ∈ N) :
    1 ≤ ordinaryTraceOrder N (vanishingIdeal (n := n) H) x ↔ x ∈ H := by
  have hHsm : IsClosedSubmanifold n H :=
    MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hnzH : ∀ y ∈ N, DivisorExponentAlong.IsNonzeroAlongAt N
      (vanishingIdeal (n := n) H) y := fun y hy =>
    HironakaSharpSingleBoundaryTraceCentre.originalBoundaryIdeal_isNonzeroAlongAt_of_dense hH hdense hy
  rw [← ordinaryTraceOrder_cosupport_iff hN hcH hnzH hx 1]
  rw [cosupport_one (fun y g (hg : (vanishingIdeal (n := n) H).mem y g) => hg.1)]
  change (x ∈ N ∧ x ∈ (vanishingIdeal (n := n) H).zeroLocus) ↔ x ∈ H
  rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsm.1]
  exact and_iff_right hx

private theorem cleanup_centre_geometry (hn : 0 < n) {N H F : Set X}
    (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N, RegularAtDim (n := n) N x (d+1))
    (B : List (Set X)) (hE : IsSNCDivisor n (H :: (B ++ [F])))
    (hT : IsTransverse n N (B ++ [F]))
    (hB : ∀ G ∈ B, Disjoint N G) (heq : N ∩ H = N ∩ F) :
    IsClosedSubmanifold n (N ∩ F) ∧
      (∀ x ∈ N ∩ F, RegularAtDim (n := n) (N ∩ F) x d) ∧
      HasNormalCrossings n (N ∩ F) (H :: (B ++ [F])) ∧ interior (N ∩ F) = ∅ := by
  have hBorn : IsSNCDivisor n (B ++ [F]) :=
    isSNCDivisor_of_sublist hE (List.tail_sublist (H :: (B ++ [F])))
  have hF : IsSNCDivisor n [F] := isSNCDivisor_of_sublist hBorn (by simp)
  have hTF : IsTransverse n N [F] := isTransverse_of_forall_mem hT
    (fun G hG => List.mem_append_right B hG)
  have hcentre : N ∩ BoundaryCount.memberInter [F] {0} = N ∩ F := by
    ext x
    simp [BoundaryCount.memberInter]
  have hC : IsClosedSubmanifold n (N ∩ F) := by
    rw [← hcentre]
    exact isClosedSubmanifold_inter_memberInter hn hN.1 hF hTF {0}
  have hrC : ∀ x ∈ N ∩ F, RegularAtDim (n := n) (N ∩ F) x d :=
    fun _ hx => regularAtDim_transverse_member hn hN hF hTF hrN hx
  have hCH : N ∩ F ⊆ H := fun y hy => (heq.symm ▸ hy).2
  have hNC : HasNormalCrossings n (N ∩ F) (H :: (B ++ [F])) := by
    apply hasNormalCrossings_of_eventually_incident_containment hC hE
    intro x hx i hi
    rcases List.mem_cons.mp (List.get_mem (H :: (B ++ [F])) i) with hHi | hBi
    · exact Eventually.of_forall fun y hy => hHi.symm ▸ hCH hy
    · rcases List.mem_append.mp hBi with hBi | hFi
      · exact False.elim (Set.disjoint_left.mp (hB _ hBi) hx.1 hi)
      · have hFi' : (H :: (B ++ [F])).get i = F := List.mem_singleton.mp hFi
        exact Eventually.of_forall fun y hy => hFi'.symm ▸ hy.2
  have hint : interior (N ∩ F) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxC : x ∈ N ∩ F := interior_subset hx
    have he : (univ : Set X) ∩ interior (N ∩ F) = (N ∩ F) ∩ interior (N ∩ F) := by
      rw [univ_inter, inter_eq_right.mpr interior_subset]
    have hCn := RegularPointDimension.regularAtDim_of_inter_eq isOpen_interior hx he
      (AnalyticIrreducibleComponents.regularAtDim_univ (n := n) x)
    have hdim := RegularPointDimension.eq_of_regularAtDim hCn (hrC x hxC)
    have hdN := (hrN x hxC.1).1
    omega
  exact ⟨hC, hrC, hNC, hint⟩

theorem cleanup_step_geometry (hn : 0 < n) {N H F : Set X}
    (hN : IsClosedSubmanifold n N)
    (hrN : ∀ x ∈ N, RegularAtDim (n := n) N x (d+1))
    (B : List (Set X)) (hE : IsSNCDivisor n (H :: (B ++ [F])))
    (hT : IsTransverse n N (B ++ [F]))
    (hB : ∀ G ∈ B, Disjoint N G) (heq : N ∩ H = N ∩ F)
    (hdense : N ⊆ closure (N \ H)) (a : ℕ)
    (horder : ∀ x ∈ N ∩ H, ordinaryTraceOrder N (vanishingIdeal (n := n) H) x = a)
    {π : Y → X} (hπ : IsBlowupAlong n (N ∩ F) π) :
    let N' := geoStrictTransform π (N ∩ F) N
    let H' := geoStrictTransform π (N ∩ F) H
    let E' := (B ++ [F]).map (geoStrictTransform π (N ∩ F)) ++ [π ⁻¹' (N ∩ F)]
    IsClosedSubmanifold n N' ∧
      (∀ x ∈ N', RegularAtDim (n := n) N' x (d+1)) ∧
      IsSNCDivisor n (H' :: E') ∧ IsTransverse n N' E' ∧
      (∀ G ∈ (B ++ [F]).map (geoStrictTransform π (N ∩ F)), Disjoint N' G) ∧
      N' ⊆ closure (N' \ H') ∧
      (∀ z ∈ N' ∩ π ⁻¹' (N ∩ F),
        ordinaryTraceOrder N' (vanishingIdeal (n := n) H') z + 1 = a) ∧
      N' ∩ H' ⊆ π ⁻¹' (N ∩ F) := by
  dsimp only
  let C := N ∩ F
  let N' := geoStrictTransform π C N
  let H' := geoStrictTransform π C H
  let E' := (B ++ [F]).map (geoStrictTransform π C) ++ [π ⁻¹' C]
  obtain ⟨_hC, hrC, hNC, _hint⟩ := cleanup_centre_geometry hn hN hrN B hE hT hB heq
  have hBorn : IsSNCDivisor n (B ++ [F]) :=
    isSNCDivisor_of_sublist hE (List.tail_sublist (H :: (B ++ [F])))
  have hF : IsSNCDivisor n [F] := isSNCDivisor_of_sublist hBorn (by simp)
  have hH : IsSNCDivisor n [H] := isSNCDivisor_of_sublist hE (by simp)
  have hTF : IsTransverse n N [F] := isTransverse_of_forall_mem hT
    (fun G hG => List.mem_append_right B hG)
  have hNCBorn : HasNormalCrossings n C (B ++ [F]) :=
    hasNormalCrossings_of_forall_mem hNC (fun G hG => List.mem_cons_of_mem H hG)
  have hNCF : HasNormalCrossings n C [F] := hasNormalCrossings_of_forall_mem hNCBorn
    (fun G hG => List.mem_append_right B hG)
  have hCH : C ⊆ H := fun x hx =>
    (heq.symm ▸ (show x ∈ N ∩ F from hx)).2
  have hN' : IsClosedSubmanifold n N' :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN inter_subset_left
  have hrN' : ∀ x ∈ N', RegularAtDim (n := n) N' x (d+1) :=
    fun _ hx => regularAtDim_geoStrictTransform hπ hN.1 hrN inter_subset_left hx
  have hE' : IsSNCDivisor n (H' :: E') := by
    simpa only [List.map_cons, List.cons_append] using
      isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hE hNC
  have hT' : IsTransverse n N' E' :=
    isTransverse_geoTransformE_of_hasNormalCrossings hπ hN.1 inter_subset_left hBorn hT hNCBorn
  have hNF : N' ∩ geoStrictTransform π C F = ∅ := by
    have hinter := geoStrictTransform_inter_memberInter_eq hπ hN.1 inter_subset_left hF hTF hNCF {0}
    have hcentre : N ∩ BoundaryCount.memberInter [F] {0} = C := by
      ext x
      simp [C, BoundaryCount.memberInter]
    have hCC : geoStrictTransform π C C = ∅ := by
      change closure (π ⁻¹' (C \ C)) = ∅
      simp
    rw [hcentre, hCC] at hinter
    simpa using hinter.symm
  have hInactive : ∀ G ∈ (B ++ [F]).map (geoStrictTransform π C), Disjoint N' G := by
    intro G hG
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hG
    rcases List.mem_append.mp hK with hK | hK
    · apply Set.disjoint_left.mpr
      intro z hzN hzK
      have hxN := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hzN
      have hxK := geoStrictTransform_subset_preimage hπ.contMDiff.continuous
        (hBorn.1 K (List.mem_append_left [F] hK)) hzK
      exact Set.disjoint_left.mp (hB K hK) hxN hxK
    · have hKF : K = F := List.mem_singleton.mp hK
      rw [hKF]
      exact Set.disjoint_iff_inter_eq_empty.mpr hNF
  have hHclosed : IsClosed H := hE.1 H (by simp)
  have hDense' : N' ⊆ closure (N' \ H') := by
    change closure (π ⁻¹' (N \ C)) ⊆ closure (N' \ H')
    apply closure_mono
    intro z hz
    refine ⟨subset_closure hz, ?_⟩
    intro hzH
    have hxH := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hHclosed hzH
    apply hz.2
    change π z ∈ N ∩ F
    rw [← heq]
    exact ⟨hz.1, hxH⟩
  have hHnew : IsClosedSubmanifold n H' :=
    MonomialPart.isClosedSubmanifold_get hn hE' (0 : Fin (H' :: E').length)
  have hcHnew := VanishingIdealCoherent.isCoherent_vanishingIdeal hHnew
  have hOrder' : ∀ z ∈ N' ∩ π ⁻¹' C,
      ordinaryTraceOrder N' (vanishingIdeal (n := n) H') z + 1 = a := by
    intro z hz
    have hdrop := (actual_cartier_ambient_strict_trace_order_drop hn hN hrN hrC hH hdense
      hπ inter_subset_left hCH hz).1
    have hOldTrace : π z ∈ N ∩ H := by
      rw [heq]
      exact hz.2
    rw [ordinaryTraceOrder_restrictOn_eq hN' hcHnew z,
      horder (π z) hOldTrace] at hdrop
    exact hdrop
  have hTraceSub : N' ∩ H' ⊆ π ⁻¹' C := by
    intro z hz
    have hxN := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz.1
    have hxH := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hHclosed hz.2
    change π z ∈ N ∩ F
    rw [← heq]
    exact ⟨hxN, hxH⟩
  exact ⟨hN', hrN', hE', hT', hInactive, hDense', hOrder', hTraceSub⟩

private theorem full_boundary_dictionary (N H F : Set X) :
    ∀ {Y : CMfd.{u} n} (P : BlowupTower X Y),
      (geoTransformAlong (geometricTemplate N [H,F]) P).E =
        strictAlong P H :: (geoTransformAlong (geometricTemplate N [F]) P).E
  | _, .refl => rfl
  | _, .step P C π hπ => by
    change (geoTransformAlong (geometricTemplate N [H,F]) P).E.map (geoStrictTransform π C) ++
      [π ⁻¹' C] = geoStrictTransform π C (strictAlong P H) ::
        ((geoTransformAlong (geometricTemplate N [F]) P).E.map (geoStrictTransform π C) ++ [π ⁻¹' C])
    rw [full_boundary_dictionary N H F P]
    rfl

private theorem finish_from_prefix (hn : 0 < n) (N₀ H₀ F₀ : Set X)
    (hN₀ : IsClosed N₀) (hH₀ : IsClosed H₀) :
    ∀ (a : ℕ) {Y : CMfd.{u} n} (P : BlowupTower X Y) (B : List (Set Y)) (F : Set Y),
      (geoTransformAlong (geometricTemplate N₀ [F₀]) P).E = B ++ [F] →
      cartierCleanupSteps N₀ H₀ P → CentresOver (N₀ ∩ H₀) P →
      IsAdmissibleBlowupSequence n X [H₀,F₀] (N₀ ∩ H₀) Y P.proj
        (strictAlong P H₀ :: (geoTransformAlong (geometricTemplate N₀ [F₀]) P).E) →
      IsClosedSubmanifold n (strictAlong P N₀) →
      (∀ x ∈ strictAlong P N₀, RegularAtDim (n := n) (strictAlong P N₀) x (d+1)) →
      IsSNCDivisor n (strictAlong P H₀ :: (geoTransformAlong (geometricTemplate N₀ [F₀]) P).E) →
      IsTransverse n (strictAlong P N₀) (geoTransformAlong (geometricTemplate N₀ [F₀]) P).E →
      (∀ G ∈ B, Disjoint (strictAlong P N₀) G) →
      strictAlong P N₀ ∩ strictAlong P H₀ = strictAlong P N₀ ∩ F →
      strictAlong P N₀ ⊆ closure (strictAlong P N₀ \ strictAlong P H₀) →
      (∀ x ∈ strictAlong P N₀ ∩ strictAlong P H₀,
        ordinaryTraceOrder (strictAlong P N₀) (vanishingIdeal (n := n) (strictAlong P H₀)) x = a) →
      ∃ (Z : CMfd.{u} n) (T : BlowupTower X Z),
        T.length ≤ P.length + a ∧ cartierCleanupSteps N₀ H₀ T ∧ CentresOver (N₀ ∩ H₀) T ∧
        IsAdmissibleBlowupSequence n X [H₀,F₀] (N₀ ∩ H₀) Z T.proj
          (strictAlong T H₀ :: (geoTransformAlong (geometricTemplate N₀ [F₀]) T).E) ∧
        IsClosedSubmanifold n (strictAlong T N₀) ∧
        IsSNCDivisor n (strictAlong T H₀ :: (geoTransformAlong (geometricTemplate N₀ [F₀]) T).E) ∧
        IsTransverse n (strictAlong T N₀) (geoTransformAlong (geometricTemplate N₀ [F₀]) T).E ∧
        strictAlong T N₀ ∩ strictAlong T H₀ = ∅
  | 0, Y, P, B, F, _hBorn, hRecipe, hOver, hSeq, hN, _hrN, hE, hT, _hB, _heq, hDense, hOrder => by
    refine ⟨Y, P, by omega, hRecipe, hOver, hSeq, hN, hE, hT, ?_⟩
    have hH : IsSNCDivisor n [strictAlong P H₀] := isSNCDivisor_of_sublist hE (by simp)
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hp := (one_le_trace_order_iff hn hN hH hDense hx.1).mpr hx.2
    have hz := hOrder x hx
    omega
  | a+1, Y, P, B, F, hBorn, hRecipe, hOver, hSeq, hN, hrN, hE, hT, hB, heq, hDense, hOrder => by
    by_cases hEmpty : strictAlong P N₀ ∩ strictAlong P H₀ = ∅
    · exact ⟨Y, P, by omega, hRecipe, hOver, hSeq, hN, hE, hT, hEmpty⟩
    let N := strictAlong P N₀
    let H := strictAlong P H₀
    let C := N ∩ F
    have hEm : IsSNCDivisor n (H :: (B ++ [F])) := by simpa only [hBorn] using hE
    have hTm : IsTransverse n N (B ++ [F]) := by simpa only [hBorn] using hT
    obtain ⟨hC, _hrC, hNC, hint⟩ := cleanup_centre_geometry hn hN hrN B hEm hTm hB heq
    obtain ⟨Z, π, hπ⟩ := ResolutionDriver.exists_blowup C hC hint
    let P' : BlowupTower X Z := .step P C π hπ
    let B' := (B ++ [F]).map (geoStrictTransform π C)
    let Q : Set Z := π ⁻¹' C
    obtain ⟨hNnew, hrNnew, hEnew, hTnew, hInactive, hDensenew, hOrdnew, hSubnew⟩ :=
      cleanup_step_geometry hn hN hrN B hEm hTm hB heq hDense (a+1) hOrder hπ
    have hBorn' : (geoTransformAlong (geometricTemplate N₀ [F₀]) P').E = B' ++ [Q] := by
      change (geoTransformAlong (geometricTemplate N₀ [F₀]) P).E.map (geoStrictTransform π C) ++
        [π ⁻¹' C] = B' ++ [Q]
      rw [hBorn]
    have hE' : IsSNCDivisor n
        (strictAlong P' H₀ :: (geoTransformAlong (geometricTemplate N₀ [F₀]) P').E) := by
      rw [hBorn']
      exact hEnew
    have hT' : IsTransverse n (strictAlong P' N₀)
        (geoTransformAlong (geometricTemplate N₀ [F₀]) P').E := by
      rw [hBorn']
      exact hTnew
    have hCover : C ⊆ P.proj ⁻¹' (N₀ ∩ H₀) := by
      intro y hy
      have hyTrace : y ∈ strictAlong P N₀ ∩ strictAlong P H₀ := by
        rw [heq]
        exact hy
      exact ⟨strictAlong_subset_preimage hN₀ P hyTrace.1, strictAlong_subset_preimage hH₀ P hyTrace.2⟩
    have hRecipe' : cartierCleanupSteps N₀ H₀ P' := ⟨hRecipe, heq.symm⟩
    have hOver' : CentresOver (N₀ ∩ H₀) P' := ⟨hOver, hCover⟩
    have hNCnative : HasNormalCrossings n C
        (strictAlong P H₀ :: (geoTransformAlong (geometricTemplate N₀ [F₀]) P).E) := by
      rw [hBorn]
      exact hNC
    have hSeq' : IsAdmissibleBlowupSequence n X [H₀,F₀] (N₀ ∩ H₀) Z P'.proj
        (strictAlong P' H₀ :: (geoTransformAlong (geometricTemplate N₀ [F₀]) P').E) := by
      change IsAdmissibleBlowupSequence n X [H₀,F₀] (N₀ ∩ H₀) Z (P.proj ∘ π)
        ((strictAlong P H₀ :: (geoTransformAlong (geometricTemplate N₀ [F₀]) P).E).map
          (geoStrictTransform π C) ++ [π ⁻¹' C])
      exact IsAdmissibleBlowupSequence.step P.proj _ C π hSeq hπ hNCnative hCover
    have hHnew : IsSNCDivisor n [strictAlong P' H₀] := isSNCDivisor_of_sublist hE' (by simp)
    by_cases ha : a = 0
    · have hErase : strictAlong P' N₀ ∩ strictAlong P' H₀ = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hp := (one_le_trace_order_iff hn hNnew hHnew hDensenew hz.1).mpr hz.2
        have hdrop := hOrdnew z ⟨hz.1, hSubnew hz⟩
        change 1 ≤ ordinaryTraceOrder (strictAlong P' N₀)
          (vanishingIdeal (n := n) (strictAlong P' H₀)) z at hp
        change ordinaryTraceOrder (strictAlong P' N₀)
          (vanishingIdeal (n := n) (strictAlong P' H₀)) z + 1 = a+1 at hdrop
        omega
      exact ⟨Z, P', by change P.length+1 ≤ P.length+(a+1); omega,
        hRecipe', hOver', hSeq', hNnew, hE', hT', hErase⟩
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha
      have hTrace : strictAlong P' N₀ ∩ strictAlong P' H₀ = strictAlong P' N₀ ∩ Q := by
        ext z
        constructor
        · intro hz
          exact ⟨hz.1, hSubnew hz⟩
        · intro hz
          refine ⟨hz.1, ?_⟩
          have hp : 1 ≤ ordinaryTraceOrder (strictAlong P' N₀)
              (vanishingIdeal (n := n) (strictAlong P' H₀)) z := by
            have hdrop := hOrdnew z hz
            change ordinaryTraceOrder (strictAlong P' N₀)
              (vanishingIdeal (n := n) (strictAlong P' H₀)) z + 1 = a+1 at hdrop
            omega
          exact (one_le_trace_order_iff hn hNnew hHnew hDensenew hz.1).mp hp
      have hOrder' : ∀ z ∈ strictAlong P' N₀ ∩ strictAlong P' H₀,
          ordinaryTraceOrder (strictAlong P' N₀)
            (vanishingIdeal (n := n) (strictAlong P' H₀)) z = a := by
        intro z hz
        have hdrop := hOrdnew z ⟨hz.1, hSubnew hz⟩
        change ordinaryTraceOrder (strictAlong P' N₀)
          (vanishingIdeal (n := n) (strictAlong P' H₀)) z + 1 = a+1 at hdrop
        omega
      obtain ⟨W, T, hLen, hRec, hOv, hS, hNt, hEt, hTt, hErase⟩ :=
        finish_from_prefix hn N₀ H₀ F₀ hN₀ hH₀ a P' B' Q hBorn' hRecipe' hOver' hSeq'
          hNnew hrNnew hE' hT' hInactive hTrace hDensenew hOrder'
      exact ⟨W, T, by have hPlen : P'.length = P.length+1 := rfl; omega,
        hRec, hOv, hS, hNt, hEt, hTt, hErase⟩

/-- A real finite general-dimensional Cartier cleanup, using the same original
carrier/hypersurface and every original and born ambient boundary position. -/
theorem exists_one_born_cartier_cleanup (hn : 0 < n) {N H F : Set X}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n [H,F])
    (hT : IsTransverse n N [F])
    (hrN : ∀ x ∈ N, RegularAtDim (n := n) N x (d+1))
    (hdense : N ⊆ closure (N \ H)) (heq : N ∩ H = N ∩ F)
    (a : ℕ) (hOrder : ∀ x ∈ N ∩ H, ordinaryTraceOrder N (vanishingIdeal (n := n) H) x = a) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      T.length ≤ a ∧ cartierCleanupSteps N H T ∧ CentresOver (N ∩ H) T ∧
      IsAdmissibleBlowupSequence n X [H,F] (N ∩ H) Y T.proj
        (geoTransformAlong (geometricTemplate N [H,F]) T).E ∧
      IsProperMap T.proj ∧ IsIsomorphismOver n T.proj (N ∩ H)ᶜ ∧
      IsIsomorphismOver n T.proj (originalSharpBadLocus (n := n) N [H,F])ᶜ ∧
      IsClosedSubmanifold n (strictAlong T N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate N [H,F]) T).E ∧
      IsTransverse n (strictAlong T N) (geoTransformAlong (geometricTemplate N [F]) T).E ∧
      strictAlong T N ∩ strictAlong T H = ∅ ∧
      HasNormalCrossings n (strictAlong T N) (geoTransformAlong (geometricTemplate N [H,F]) T).E := by
  have hHclosed : IsClosed H := hE.1 H (by simp)
  obtain ⟨Y, T, hLen, hRecipe, hOver, hSeq, hNt, hEt, hTt, hErase⟩ :=
    finish_from_prefix hn N H F hN.1 hHclosed a (.refl : BlowupTower X X) [] F rfl
      trivial trivial IsAdmissibleBlowupSequence.refl hN hrN hE hT (by simp) heq hdense hOrder
  have hNC := hasNormalCrossings_cons_of_disjoint hTt (Set.disjoint_iff_inter_eq_empty.mpr hErase)
  rw [← full_boundary_dictionary N H F T] at hSeq hEt hNC
  exact ⟨Y, T, by simpa using hLen, hRecipe, hOver, hSeq,
    isProperMap_of_isBlowupSequence T.isBlowupSequence,
    HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hSeq,
    HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl
      (IsAdmissibleBlowupSequence.mono
        (one_born_trace_subset_sharpBad hn hN hE hT hrN hdense heq) hSeq),
    hNt, hEt, hTt, hErase, hNC⟩

end

end Hironaka.HironakaG4OneBornCartierCleanup
