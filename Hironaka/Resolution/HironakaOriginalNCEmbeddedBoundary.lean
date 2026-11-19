import Hironaka.Resolution.HironakaOriginalNCMarkedStratumGoodOpen
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumCompactDriver
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumLocalDriver

/-!
# A SAME-prefix embedded resolution with prescribed genuine NC boundary

Original weak permitted image F=Sing_d(W) union (W intersect H).
Original pure regular density and W subset closure(W minus H) remain
literal inputs. Local restrictions use the pure/reducible geometric
identity-principle mother, never irreducibility or connectedness.

The actual first-good-open prefix is RAW canonical for SAME M/H.
An internally constructed actual maximum blowup and NEW joint history
give ONE simultaneous strictW/ALLoldbranches/ALLborn coordinate system.
No pairwise-NC inference, future target certificate, compact whole local
cosupport, global H labelling, G8 OR or G3 scheduling is substituted.

Mathematics/API precede source in
work/hironaka-g9-general-nc-embedded-producers-20261024/.
SOURCE ONLY. GoodOpen is a newly frozen source-only parent; no actual
object, Lean check, Blueprint credit or original G9 closure is claimed.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCEmbeddedBoundary
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
    (hWa : IsComplexAnalyticSubset (n := n) W)
    (hM : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H [])
    (O : Opens X) (hHO : Disjoint H (O : Set X)) {d : ℕ}
    (hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W ∩ O))
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hCan₀ : IsCanonical (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
      (markedStratumHistoryValue (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) H) T₀)
    (hRes₀ : IsGeoResolution (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T₀) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
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
  let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
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
        (fun A hA => False.elim (List.not_mem_nil hA)) hZO hPureO T hCan
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

/-- Original weak-F geometry assembled on ONE actual embedded prefix.
The resolving tower input is obtained INTERNALLY by each public driver. -/
private theorem embedded_geometry_of_resolution {X : CMfd.{u} n} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d))
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H) (hWH : W ⊆ closure (W \ H))
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hCan₀ : IsCanonical (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
      (markedStratumHistoryValue (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) H) T₀)
    (hRes₀ : IsGeoResolution (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T₀) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
    let F := W \ regularLocus (n := n) W d ∪ W ∩ H
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      let E := (geoTransformAlong M T).E
      let S := strictTransform n T.proj W
      IsCanonical M (markedStratumHistoryValue M H) T ∧ IsGeoTestTower M T ∧
      IsOriginalBranchTestTower M H T ∧
      IsAdmissibleBlowupSequence n X [] F Y T.proj E ∧ IsSNCDivisor n E ∧
      exceptionalLocus n T.proj ⊆ (⋃ A ∈ E, A) ∧ (⋃ A ∈ E, A) ⊆ T.proj ⁻¹' F ∧
      T.proj ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n T.proj ∧
      IsIsomorphismOver n T.proj Fᶜ ∧ IsClosedSubmanifold n S ∧
      (∀ x ∈ S, RegularAtDim (n := n) S x d) ∧ HasNormalCrossings n S E ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) E ∧
      ∀ (U : Opens X) (B : List (Set U)), IsSNCDivisor n B →
        (Subtype.val : U → X) ⁻¹' H = (⋃ A ∈ B, A) →
        HasNormalCrossings n (strictTransform n (restrict U T).proj ((Subtype.val : U → X) ⁻¹' W))
          (B.map (strictAlong (restrict U T)) ++
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).E) := by
  let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
  have hM : IsInvDomain n M := isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) NormalCrossings.isSNCDivisor_nil
  have h : IsBoundaryAdaptedCarrier (n := n) H M.E := boundaryAdapted_nil hH
  have hcl : IsClosed (W \ regularLocus (n := n) W d ∪ H) :=
    (HironakaEmbeddedReducible.isClosed_diff_regularLocus hWa.isClosed d).union hH.1
  let O : Opens X := ⟨(W \ regularLocus (n := n) W d ∪ H)ᶜ, hcl.isOpen_compl⟩
  have hHO : Disjoint H (O : Set X) := disjoint_left.mpr fun x hxH hxO => hxO (Or.inr hxH)
  have hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d := by
    intro x hxW hxO
    by_contra hnot
    exact hxO (Or.inl ⟨hxW, hnot⟩)
  have hdense : W ⊆ closure (W ∩ O) := subset_closure_inter_compl hpure hH.1 hWH
  obtain ⟨Y, T, hCan, hTest, hHistory, hAvoid, hSmooth, hReg, hNC, hPair, hAllNC⟩ :=
    exists_embedded_prefix hWa hM h O hHO hreg hdense T₀ hCan₀ hRes₀
  let F := W \ regularLocus (n := n) W d ∪ W ∩ H
  have hcos : M.cosupp = W := cosupp_mk_vanishingIdeal hWa.isClosed []
  have hover : CentresOver F T := by
    refine centresOver_of_inter_subset (F := M.cosupp) (G := ((O : Set X)ᶜ)) ?_ T
      (centresOver_cosupp M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hTest)
      (centresOver_compl_of_centresAvoid O T hAvoid)
    rintro x ⟨hxW, hxO⟩
    rw [hcos] at hxW
    have hh : x ∈ W \ regularLocus (n := n) W d ∪ H := not_not.mp hxO
    exact hh.elim Or.inl (fun hxH => Or.inr ⟨hxW, hxH⟩)
  have hsuppF := support_exceptionalDivisor_subset_of_centresOver F T hover
  have hsupp := HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop
    M hM.isWellFormed.isSNCDivisor.1 T
  have hE0 : M.E = [] := rfl
  rw [hE0] at hsupp
  simp only [List.length_nil, List.drop_zero] at hsupp
  have hexc := HironakaPrincipalization.exceptionalLocus_subset_support T
  have hExcF : T.proj '' exceptionalLocus n T.proj ⊆ F := by
    rintro x ⟨z, hz, rfl⟩
    exact hsuppF (hexc hz)
  refine ⟨Y, T, hCan, hTest, hHistory, isAdmissibleBlowupSequence_proj M F T hTest hover,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hTest).isWellFormed.isSNCDivisor,
    ?_, ?_, HironakaEmbeddedReducible.preimage_diff_regularLocus_subset_exceptionalLocus
      T.contMDiff_proj hWa.isClosed hReg,
    HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence hExcF,
    hSmooth, hReg, hNC, hPair, ?_⟩
  · rw [← hsupp]
    exact hexc
  · rw [← hsupp]
    exact hsuppF
  · intro U B hB hUnion
    rw [strictTransform_restricted_tower U T W]
    exact hAllNC U B (by simpa only [M, MarkedIdeal.pullback, List.map_nil, List.append_nil] using hB) hUnion

/-- Compact W; original pure/dimension/density premises, genuine NC H.
ONE actual prefix gives every weak permitted-image and triple-NC output. -/
theorem exists_generalNC_embedded_of_isCompact {X : CMfd.{u} n} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d))
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H)
    (hWH : W ⊆ closure (W \ H)) (hK : IsCompact W) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
    let F := W \ regularLocus (n := n) W d ∪ W ∩ H
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      let E := (geoTransformAlong M T).E
      let S := strictTransform n T.proj W
      IsCanonical M (markedStratumHistoryValue M H) T ∧ IsGeoTestTower M T ∧
      IsOriginalBranchTestTower M H T ∧
      IsAdmissibleBlowupSequence n X [] F Y T.proj E ∧ IsSNCDivisor n E ∧
      exceptionalLocus n T.proj ⊆ (⋃ A ∈ E, A) ∧ (⋃ A ∈ E, A) ⊆ T.proj ⁻¹' F ∧
      T.proj ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n T.proj ∧
      IsIsomorphismOver n T.proj Fᶜ ∧ IsClosedSubmanifold n S ∧
      (∀ x ∈ S, RegularAtDim (n := n) S x d) ∧ HasNormalCrossings n S E ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) E ∧
      ∀ (U : Opens X) (B : List (Set U)), IsSNCDivisor n B →
        (Subtype.val : U → X) ⁻¹' H = (⋃ A ∈ B, A) →
        HasNormalCrossings n (strictTransform n (restrict U T).proj ((Subtype.val : U → X) ⁻¹' W))
          (B.map (strictAlong (restrict U T)) ++
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).E) := by
  let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
  have hM : IsInvDomain n M := isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) NormalCrossings.isSNCDivisor_nil
  have h : IsBoundaryAdaptedCarrier (n := n) H M.E := boundaryAdapted_nil hH
  have hCompact : IsCompact M.cosupp := by
    rw [show M.cosupp = W from cosupp_mk_vanishingIdeal hWa.isClosed []]
    exact hK
  obtain ⟨Y₀, T₀, hRes₀, hCan₀, _hHistory₀⟩ := exists_markedStratum_canonical_resolving_tower M hM hCompact h
  exact embedded_geometry_of_resolution hWa hd hpure hH hWH T₀ hCan₀ hRes₀

/-- EXACT original open A inside compact K; no compactness of W or its
open trace. Pure/reducible geometric mothers require no connectivity. -/
theorem exists_generalNC_embedded_of_subset_isCompact {X : CMfd.{u} n} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d))
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H)
    (hWH : W ⊆ closure (W \ H)) (A : Opens X) (K : Set X) (hK : IsCompact K) (hAK : (A : Set X) ⊆ K) :
    let WA := (Subtype.val : A → X) ⁻¹' W
    let HA := (Subtype.val : A → X) ⁻¹' H
    let MA : MarkedIdeal n A := ⟨univ, [], vanishingIdeal (n := n) WA, 1⟩
    let F := (Subtype.val : A → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ H)
    ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) A) Y),
      let E := (geoTransformAlong MA T).E
      let S := strictTransform n T.proj WA
      IsCanonical MA (markedStratumHistoryValue MA HA) T ∧ IsGeoTestTower MA T ∧
      IsOriginalBranchTestTower MA HA T ∧
      IsAdmissibleBlowupSequence n A [] F Y T.proj E ∧ IsSNCDivisor n E ∧
      exceptionalLocus n T.proj ⊆ (⋃ B ∈ E, B) ∧ (⋃ B ∈ E, B) ⊆ T.proj ⁻¹' F ∧
      T.proj ⁻¹' ((Subtype.val : A → X) ⁻¹' (W \ regularLocus (n := n) W d)) ⊆ exceptionalLocus n T.proj ∧
      IsIsomorphismOver n T.proj Fᶜ ∧ IsClosedSubmanifold n S ∧
      (∀ x ∈ S, RegularAtDim (n := n) S x d) ∧ HasNormalCrossings n S E ∧
      IsBoundaryAdaptedCarrier (n := n) (strictAlong T HA) E ∧
      ∀ (U : Opens A) (B : List (Set U)), IsSNCDivisor n B →
        (Subtype.val : U → A) ⁻¹' HA = (⋃ L ∈ B, L) →
        HasNormalCrossings n (strictTransform n (restrict U T).proj ((Subtype.val : U → A) ⁻¹' WA))
          (B.map (strictAlong (restrict U T)) ++
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → A) MA) (restrict U T)).E) := by
  let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
  have hM : IsInvDomain n M := isInvDomain_boundary hWa
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd hpure) NormalCrossings.isSNCDivisor_nil
  have h : IsBoundaryAdaptedCarrier (n := n) H M.E := boundaryAdapted_nil hH
  obtain ⟨Y₀, T₀, hRes₀, hCan₀, _hHistory₀, _hPair₀⟩ :=
    exists_markedStratum_resolution_of_subset_isCompact M hM h K hK A hAK
  rw [pullback_val_mk_vanishingIdeal A [] W] at hCan₀ hRes₀
  simp only [List.map_nil] at hCan₀ hRes₀
  let WA := (Subtype.val : A → X) ⁻¹' W
  let HA := (Subtype.val : A → X) ⁻¹' H
  have hWaA : IsComplexAnalyticSubset (n := n) WA :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWa
  have hHA : IsNormalCrossingsCarrier (n := n) HA :=
    isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open A h)
  have hopen := A.isOpen.isOpenMap_subtype_val
  have hpureA : WA ⊆ closure (regularLocus (n := n) WA d) := by
    intro x hx
    have h1 : (x : X) ∈ closure (regularLocus (n := n) W d) := hpure hx
    have h3 : x ∈ closure ((Subtype.val : A → X) ⁻¹' regularLocus (n := n) W d) :=
      (Set.ext_iff.mp (hopen.preimage_closure_eq_closure_preimage continuous_subtype_val _) x).mp h1
    exact closure_mono (fun y hy => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hy) h3
  have hWHA : WA ⊆ closure (WA \ HA) := by
    intro x hx
    have h1 : (x : X) ∈ closure (W \ H) := hWH hx
    have h3 : x ∈ closure ((Subtype.val : A → X) ⁻¹' (W \ H)) :=
      (Set.ext_iff.mp (hopen.preimage_closure_eq_closure_preimage continuous_subtype_val _) x).mp h1
    simpa only [preimage_sdiff] using h3
  have hF : (Subtype.val : A → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ H) =
      WA \ regularLocus (n := n) WA d ∪ WA ∩ HA := by
    rw [preimage_union, preimage_inter, HironakaEmbeddedReducible.preimage_val_diff_regularLocus A W d]
  have hSing : (Subtype.val : A → X) ⁻¹' (W \ regularLocus (n := n) W d) =
      WA \ regularLocus (n := n) WA d := HironakaEmbeddedReducible.preimage_val_diff_regularLocus A W d
  rw [hF, hSing]
  exact embedded_geometry_of_resolution hWaA hd hpureA hHA hWHA T₀ hCan₀ hRes₀

/-- ONE precompact neighbourhood A of compact K and ONE actual prefix,
with the complete original weak-F and simultaneous NC conclusions. -/
theorem exists_generalNC_embedded_local {X : CMfd.{u} n} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d))
    {H : Set X} (hH : IsNormalCrossingsCarrier (n := n) H)
    (hWH : W ⊆ closure (W \ H)) (K : Set X) (hK : IsCompact K) :
    ∃ A : Opens X, K ⊆ A ∧ IsCompact (closure (A : Set X)) ∧
      let WA := (Subtype.val : A → X) ⁻¹' W
      let HA := (Subtype.val : A → X) ⁻¹' H
      let MA : MarkedIdeal n A := ⟨univ, [], vanishingIdeal (n := n) WA, 1⟩
      let F := (Subtype.val : A → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ H)
      ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) A) Y),
        let E := (geoTransformAlong MA T).E
        let S := strictTransform n T.proj WA
        IsCanonical MA (markedStratumHistoryValue MA HA) T ∧ IsGeoTestTower MA T ∧
        IsOriginalBranchTestTower MA HA T ∧
        IsAdmissibleBlowupSequence n A [] F Y T.proj E ∧ IsSNCDivisor n E ∧
        exceptionalLocus n T.proj ⊆ (⋃ B ∈ E, B) ∧ (⋃ B ∈ E, B) ⊆ T.proj ⁻¹' F ∧
        T.proj ⁻¹' ((Subtype.val : A → X) ⁻¹' (W \ regularLocus (n := n) W d)) ⊆ exceptionalLocus n T.proj ∧
        IsIsomorphismOver n T.proj Fᶜ ∧ IsClosedSubmanifold n S ∧
        (∀ x ∈ S, RegularAtDim (n := n) S x d) ∧ HasNormalCrossings n S E ∧
        IsBoundaryAdaptedCarrier (n := n) (strictAlong T HA) E ∧
        ∀ (U : Opens A) (B : List (Set U)), IsSNCDivisor n B →
          (Subtype.val : U → A) ⁻¹' HA = (⋃ L ∈ B, L) →
          HasNormalCrossings n (strictTransform n (restrict U T).proj ((Subtype.val : U → A) ⁻¹' WA))
            (B.map (strictAlong (restrict U T)) ++
              (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → A) MA) (restrict U T)).E) := by
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨A, hAo, hKA, hAc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨A, hAo⟩, hKA, hAc,
    exists_generalNC_embedded_of_subset_isCompact hWa hd hpure hH hWH ⟨A, hAo⟩ (closure A) hAc subset_closure⟩

end
end Hironaka.HironakaOriginalNCEmbeddedBoundary
