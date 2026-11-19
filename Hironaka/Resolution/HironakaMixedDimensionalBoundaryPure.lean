import Hironaka.Resolution.HironakaOriginalNCMarkedStratumGoodOpen
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumCompactDriver
import Hironaka.Resolution.HironakaOriginalNCEmbeddedBoundary

/-!
# A pure embedded prefix with a retained list and prescribed carrier

The good open excludes the original prescribed carrier and every retained
boundary member. The actual arbitrary-boundary marked driver supplies the
resolving history internally. One first-meeting prefix gives smooth strict
transform, weak permitted image, and a single joint chart with every original
local carrier branch and every retained/born entry.

This is a partwise ingredient for mixed-dimensional assembly; the input part
is pure, and no original mixed-dimensional endpoint is claimed here.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaMixedDimensionalBoundaryPure
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings RestrictEmptyTower ResolutionDriver ResolutionInvariantDriver
  HironakaAdmissibleSequence HironakaEmbeddedBoundary
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaOriginalOldBranchOpenHistory
  HironakaOriginalNCOldStratumStrictEquality
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumCanonicalHistory
  HironakaOriginalNCMarkedStratumAdmissibleLevels HironakaOriginalNCMarkedStratumGoodOpen
  HironakaOriginalNCMarkedStratumCompactDriver HironakaOriginalNCMarkedStratumLocalDriver
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open HomogenizedGlueingTower (strictAlong)

variable {n : ℕ}

/-- The actual ENTIRE maximum, from the accepted full-open native field. -/
private theorem whole_maximum_admissible {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hCan : IsCanonical M (markedStratumHistoryValue M H) T) :
    (geoTransformAlong M T).IsAdmissibleCentre
      (maxLocus (markedStratumHistoryValue M H T) (geoTransformAlong M T).cosupp) := by
  by_cases hNe : (maxLocus (markedStratumHistoryValue M H T) (geoTransformAlong M T).cosupp).Nonempty
  · obtain ⟨x, hx⟩ := hNe
    have hLevel := markedStratum_history_value_levels_admissible M hM h T hCan
      ⊤ (markedStratumHistoryValue M H T x) (fun y hy _ => hx.2 y hy)
    rw [← maxLocus_eq_level hx] at hLevel
    have hTest := (markedStratum_canonical_history_joint_interpretation M hM h T hCan).1
    have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hTest
    exact isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hCurrent.isWellFormed.isCoherent hg) hLevel
  · rw [Set.not_nonempty_iff_eq_empty.mp hNe]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- ONE actual extra maximum blowup internally produces ALL augmented
branch-centre NC coordinates. Transfer THAT coordinate system along a
genuine germ equality; no future or triple-NC certificate is an input
to any public endpoint. This private ingredient has no separate BP node. -/
private theorem all_branch_normal_crossings_of_maximum {X Y : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E)
    (T : BlowupTower X Y) (hCan : IsCanonical M (markedStratumHistoryValue M H) T)
    (S : Set Y)
    (hSC : S ⊆ maxLocus (markedStratumHistoryValue M H T) (geoTransformAlong M T).cosupp)
    (hGerm : ∀ x ∈ S, ∀ᶠ y in 𝓝 x,
      y ∈ S ↔ y ∈ maxLocus (markedStratumHistoryValue M H T) (geoTransformAlong M T).cosupp) :
    ∀ (U : Opens X) (B : List (Set U)),
      IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E) →
      (Subtype.val : U → X) ⁻¹' H = (⋃ A ∈ B, A) →
      HasNormalCrossings n ((Subtype.val : openPreimage T U → Y) ⁻¹' S)
        (B.map (strictAlong (restrict U T)) ++
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).E) := by
  let C := maxLocus (markedStratumHistoryValue M H T) (geoTransformAlong M T).cosupp
  have hAdm := whole_maximum_admissible M hM h T hCan
  have hTest := (markedStratum_canonical_history_joint_interpretation M hM h T hCan).1
  obtain ⟨Z, π, hπ⟩ := exists_blowup C hAdm.1
    (interior_maxLocus_eq_empty hM T hTest (markedStratumHistoryValue M H T))
  have hCan' : IsCanonical M (markedStratumHistoryValue M H) (.step T C π hπ) := ⟨hCan, Or.inr rfl⟩
  have hHistory := (markedStratum_canonical_history_joint_interpretation M hM h (.step T C π hπ) hCan').2.1
  intro U B hB hUnion
  have hNC : HasNormalCrossings n ((Subtype.val : openPreimage T U → Y) ⁻¹' C)
      (geoTransformAlong
        ({ MarkedIdeal.pullback (Subtype.val : U → X) M with
          E := B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E } : MarkedIdeal n U)
        (restrict U T)).E := (hHistory U B hB hUnion).2.2.2
  rw [entire_original_old_retained_boundary (MarkedIdeal.pullback (Subtype.val : U → X) M) B (restrict U T)] at hNC
  apply CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
  intro x hx
  refine ⟨(Subtype.val : openPreimage T U → Y) ⁻¹' C, hSC hx, ?_, hNC⟩
  exact (continuous_subtype_val.tendsto x).eventually (hGerm x.val hx)

/-- The first actual whole maximum meeting the good open, cut BEFORE
that blowup. Original resolving input is supplied internally below. -/
private theorem exists_embedded_prefix {X : CMfd.{u} n} {W : Set X}
    {E₀ : List (Set X)}
    (hWa : IsComplexAnalyticSubset (n := n) W)
    (hM : IsInvDomain n (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H E₀)
    (O : Opens X) (hHO : Disjoint H (O : Set X))
    (hEO : ∀ A ∈ E₀, Disjoint A (O : Set X)) {d : ℕ}
    (hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W ∩ O))
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hCan₀ : IsCanonical (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
      (markedStratumHistoryValue (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) H) T₀)
    (hRes₀ : IsGeoResolution (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T₀) :
    let M : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      let E := (geoTransformAlong M T).E
      let S := strictTransform n T.proj W
      IsCanonical M (markedStratumHistoryValue M H) T ∧ IsGeoTestTower M T ∧
      IsOriginalBranchTestTower M H T ∧ CentresAvoid O T ∧
      IsClosedSubmanifold n S ∧ (∀ x ∈ S, RegularAtDim (n := n) S x d) ∧
      HasNormalCrossings n S E ∧ IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) E ∧
      ∀ (U : Opens X) (B : List (Set U)),
        IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E) →
        (Subtype.val : U → X) ⁻¹' H = (⋃ A ∈ B, A) →
        HasNormalCrossings n ((Subtype.val : openPreimage T U → Y) ⁻¹' S)
          (B.map (strictAlong (restrict U T)) ++
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).E) := by
  let M : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
  by_cases hAvoid : CentresAvoid O T₀
  · have hWO : ∀ x ∈ W, x ∉ O := by
      intro x hxW hxO
      obtain ⟨y, rfl⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective T₀.isBlowupSequence x
      have hy := (mem_cosupp_iff_of_centresAvoid hWa.isClosed hM O T₀ hRes₀.1 hAvoid hxO).mpr hxW
      rw [hRes₀.2] at hy
      exact hy
    have hW0 : W = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh := hdense hx
      rw [show W ∩ (O : Set X) = ∅ from eq_empty_iff_forall_notMem.mpr
        (fun y hy => hWO y hy.1 hy.2), closure_empty] at hh
      exact hh
    have hS0 : strictTransform n T₀.proj W = ∅ := by rw [hW0]; simp [strictTransform]
    have hHistory := (markedStratum_canonical_history_joint_interpretation M hM h T₀ hCan₀).2.1
    have hPair := (current_old_strata_eq_strict M h T₀ hRes₀.1 hHistory).1
    refine ⟨Y₀, T₀, hCan₀, hRes₀.1, hHistory, hAvoid, ?_, ?_, ?_, hPair, ?_⟩
    · rw [hS0]
      exact ⟨isClosed_empty, fun x hx => False.elim hx⟩
    · rw [hS0]
      exact fun x hx => False.elim hx
    · rw [hS0]
      exact fun x hx => False.elim hx
    · intro U B _hB _hUnion
      rw [hS0, preimage_empty]
      exact fun x hx => False.elim hx
  · obtain ⟨Y, T, _tail, _hAppend, hCan, hAvoidT, c, hc, hcO⟩ :=
      EmbeddedFromResolution.exists_first_centre M (markedStratumHistoryValue M H) O T₀ hCan₀ hAvoid
    obtain ⟨hTest, hHistory, _hBirths, _hFrame⟩ :=
      markedStratum_canonical_history_joint_interpretation M hM h T hCan
    let C := maxLocus (markedStratumHistoryValue M H T) (geoTransformAlong M T).cosupp
    have hPureO : ∀ x ∈ (Subtype.val : O → X) ⁻¹' W,
        RegularAtDim (n := n) ((Subtype.val : O → X) ⁻¹' W) x d := fun x hx =>
      AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hreg x hx x.2)
    have hZO : IsClosedSubmanifold n ((Subtype.val : O → X) ⁻¹' W) :=
      ⟨hWa.isClosed.preimage continuous_subtype_val, fun x hx => ⟨d, hPureO x hx⟩⟩
    have hCV (y : Y) (hy : T.proj y ∈ O) : y ∈ C ↔ T.proj y ∈ W := by
      have hCos := mem_cosupp_iff_of_centresAvoid hWa.isClosed hM O T hTest hAvoidT hy
      refine ⟨fun hyC => hCos.mp hyC.1, fun hyW => ?_⟩
      have hys := hCos.mpr hyW
      have heq := markedStratum_value_eq_over_good_open hM h O hHO
        hEO hZO hPureO T hCan
        ((isEmptyTower_restrict_iff O T).mpr hAvoidT)
        (p := ⟨c, hcO⟩) (p' := ⟨y, hy⟩) hc.1 hys
      refine ⟨hys, fun z hz => ?_⟩
      rw [heq]
      exact hc.2 z hz
    have hAdm := whole_maximum_admissible M hM h T hCan
    obtain ⟨hSC, hGerm, hReg⟩ := HironakaEmbeddedResolutionLocal.strictTransform_of_centresAvoid
      hWa O hreg hdense T hAvoidT hAdm.1 hCV
    have hNC := CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
      (R := strictTransform n T.proj W)
      (fun x hx => ⟨C, hSC hx, hGerm x hx, hAdm.2.2⟩)
    have hPair := (current_old_strata_eq_strict M h T hTest hHistory).1
    exact ⟨Y, T, hCan, hTest, hHistory, hAvoidT,
      ⟨isClosed_closure, fun x hx => ⟨d, hReg x hx⟩⟩, hReg, hNC, hPair,
      all_branch_normal_crossings_of_maximum M hM h T hCan (strictTransform n T.proj W) hSC hGerm⟩

/-- A compact pure part is resolved on one actual prefix retaining the original
list and prescribed carrier, with one universal old/retained/born joint chart. -/
theorem exists_retained_boundary_pure_embedded_of_isCompact {X : CMfd.{u} n}
    {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d))
    {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    {H : Set X} (hH : IsBoundaryAdaptedCarrier (n := n) H E₀)
    (hWH : W ⊆ closure (W \ (H ∪ ⋃ A ∈ E₀, A))) (hK : IsCompact W) :
    let M : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
    let F := W \ regularLocus (n := n) W d ∪ W ∩ (H ∪ ⋃ A ∈ E₀, A)
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      let E := (geoTransformAlong M T).E
      let S := strictTransform n T.proj W
      IsCanonical M (markedStratumHistoryValue M H) T ∧ IsGeoTestTower M T ∧
      IsOriginalBranchTestTower M H T ∧
      IsAdmissibleBlowupSequence n X E₀ F Y T.proj E ∧ IsSNCDivisor n E ∧
      exceptionalLocus n T.proj ⊆ (⋃ A ∈ E.drop E₀.length, A) ∧
      (⋃ A ∈ E.drop E₀.length, A) ⊆ T.proj ⁻¹' F ∧
      T.proj ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n T.proj ∧
      IsIsomorphismOver n T.proj Fᶜ ∧ IsClosedSubmanifold n S ∧
      (∀ x ∈ S, RegularAtDim (n := n) S x d) ∧ HasNormalCrossings n S E ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) E ∧
      ∀ (U : Opens X) (B : List (Set U)),
        IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E) →
        (Subtype.val : U → X) ⁻¹' H = (⋃ A ∈ B, A) →
        HasNormalCrossings n (strictTransform n (restrict U T).proj ((Subtype.val : U → X) ⁻¹' W))
          (B.map (strictAlong (restrict U T)) ++
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).E) := by
  let M : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
  have hM : IsInvDomain n M := isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) hE₀
  let Q := H ∪ ⋃ A ∈ E₀, A
  have hQcl : IsClosed Q :=
    hH.1.union (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1)
  have hcl : IsClosed (W \ regularLocus (n := n) W d ∪ Q) :=
    (HironakaEmbeddedReducible.isClosed_diff_regularLocus hWa.isClosed d).union hQcl
  let O : Opens X := ⟨(W \ regularLocus (n := n) W d ∪ Q)ᶜ, hcl.isOpen_compl⟩
  have hHO : Disjoint H (O : Set X) :=
    disjoint_left.mpr fun x hxH hxO => hxO (Or.inr (Or.inl hxH))
  have hEO : ∀ A ∈ E₀, Disjoint A (O : Set X) := by
    intro A hA
    refine disjoint_left.mpr fun x hxA hxO => ?_
    exact hxO (Or.inr (Or.inr (mem_iUnion₂.mpr ⟨A, hA, hxA⟩)))
  have hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d := by
    intro x hxW hxO
    by_contra hnot
    exact hxO (Or.inl ⟨hxW, hnot⟩)
  have hdense : W ⊆ closure (W ∩ O) := subset_closure_inter_compl hpure hQcl hWH
  have hCompact : IsCompact M.cosupp := by
    rw [show M.cosupp = W from cosupp_mk_vanishingIdeal hWa.isClosed E₀]
    exact hK
  obtain ⟨Y₀, T₀, hRes₀, hCan₀, _hHistory₀⟩ :=
    exists_markedStratum_canonical_resolving_tower M hM hCompact hH
  obtain ⟨Y, T, hCan, hTest, hHistory, hAvoid, hSmooth, hReg, hNC, hPair, hAllNC⟩ :=
    exists_embedded_prefix hWa hM hH O hHO hEO hreg hdense T₀ hCan₀ hRes₀
  let F := W \ regularLocus (n := n) W d ∪ W ∩ Q
  have hcos : M.cosupp = W := cosupp_mk_vanishingIdeal hWa.isClosed E₀
  have hover : CentresOver F T := by
    refine centresOver_of_inter_subset (F := M.cosupp) (G := ((O : Set X)ᶜ)) ?_ T
      (centresOver_cosupp M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hTest)
      (centresOver_compl_of_centresAvoid O T hAvoid)
    rintro x ⟨hxW, hxO⟩
    rw [hcos] at hxW
    have hh : x ∈ W \ regularLocus (n := n) W d ∪ Q := not_not.mp hxO
    exact hh.elim Or.inl (fun hxQ => Or.inr ⟨hxW, hxQ⟩)
  have hsuppF := support_exceptionalDivisor_subset_of_centresOver F T hover
  have hsupp := HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop
    M hM.isWellFormed.isSNCDivisor.1 T
  have hexc := HironakaPrincipalization.exceptionalLocus_subset_support T
  have hExcF : T.proj '' exceptionalLocus n T.proj ⊆ F := by
    rintro x ⟨z, hz, rfl⟩
    exact hsuppF (hexc hz)
  refine ⟨Y, T, hCan, hTest, hHistory, isAdmissibleBlowupSequence_proj M F T hTest hover,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hTest).isWellFormed.isSNCDivisor,
    ?_, ?_, HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus
      T.contMDiff_proj hWa.isClosed hReg,
    HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      T.isBlowupSequence hExcF,
    hSmooth, hReg, hNC, hPair, ?_⟩
  · rw [← hsupp]
    exact hexc
  · rw [← hsupp]
    exact hsuppF
  · intro U B hB hUnion
    rw [strictTransform_restricted_tower U T W]
    exact hAllNC U B hB hUnion

end

end Hironaka.HironakaMixedDimensionalBoundaryPure
