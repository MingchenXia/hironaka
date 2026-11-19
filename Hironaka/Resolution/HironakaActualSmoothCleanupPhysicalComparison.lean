import Hironaka.Resolution.HironakaActualSmoothBoundaryCleanup
import Hironaka.Resolution.HironakaOriginalTerminalPhysicalComparison
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalAmbientCanonical
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Resolution.HironakaG3RStoppedOverlap
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaActualSmoothCleanupPhysicalComparison

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings CanonicalCentres HironakaEmbeddedBoundary HironakaActualSmoothBoundaryCleanup
  HironakaOriginalTerminalPhysicalComparison HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaAdmissibleSequence RestrictEmptyTower G3UniverseEmptyAwareCore MarkedIdealBiholomorphism
open HomogenizedGlueingTower (strictAlong strictAlong_step strictAlong_restrict)
open ResolutionDriver (maxLocus)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X : CMfd.{u} n}

private theorem smoothBoundaryMarked_domain {W : Set X} {E : List (Set X)} {d : ℕ}
    (hW : IsClosedSubmanifold n W) (hd : d < n)
    (hPure : ∀ x ∈ W, RegularAtDim (n := n) W x d) (hE : IsSNCDivisor n E) :
    IsInvDomain n (actualSmoothBoundaryMarked W E) :=
  isInvDomain_boundary (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hW)
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure hd (fun x hx => subset_closure (hPure x hx))) hE

private theorem retained_carrier_nonempty {W : Set X} {E : List (Set X)} {d : ℕ}
    (hW : IsClosed W) (hE : IsSNCDivisor n E) (hM : IsInvDomain n (actualSmoothBoundaryMarked W E))
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (hNonempty : W.Nonempty)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (h : ActualSmoothBoundaryCleanupResult W E d hE T) :
    (strictAlong T W).Nonempty := by
  obtain ⟨_,hTest,hAvoid,_,hMarked,hSmooth,_,_,_,_,_,_⟩ := h
  obtain ⟨x,hx,hxGood⟩ := closure_nonempty_iff.mp (hNonempty.mono hDense)
  obtain ⟨y,hy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence x
  have hyGood : T.proj y ∈ actualSmoothBoundaryOpen E hE := by rw [hy]; exact hxGood
  have hCos := (mem_cosupp_iff_of_centresAvoid hW hM (actualSmoothBoundaryOpen E hE) T hTest hAvoid hyGood).mpr
    (hy.symm ▸ hx)
  change y ∈ (geoTransformAlong (actualSmoothBoundaryMarked W E) T).cosupp at hCos
  rw [hMarked,cosupp_mk_vanishingIdeal hSmooth.1] at hCos
  exact ⟨y,hCos⟩

private theorem empty_carrier_cleanup_resolves {E : List (Set X)} {d : ℕ} {hE : IsSNCDivisor n E}
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (h : ActualSmoothBoundaryCleanupResult (∅ : Set X) E d hE T) :
    IsGeoResolution (actualSmoothBoundaryMarked (∅ : Set X) E) T := by
  obtain ⟨_,hTest,_,_,hMarked,hSmooth,_,_,_,_,_,_⟩ := h
  refine ⟨hTest,?_⟩
  rw [hMarked,cosupp_mk_vanishingIdeal hSmooth.1,StepOneEmptyPrefix.strictAlong_empty]

/-- The recorded whole-carrier maximum is one actual last step to a terminal resolution. -/
theorem exists_resolving_last_step {W : Set X} {E : List (Set X)} {d : ℕ}
    (hW : IsClosedSubmanifold n W) (hd : d < n)
    (hPure : ∀ x ∈ W, RegularAtDim (n := n) W x d) (hE : IsSNCDivisor n E)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (h : ActualSmoothBoundaryCleanupResult W E d hE T) :
    ∃ (Z : CMfd.{u} n) (π : Z → Y) (hπ : IsBlowupAlong n (strictAlong T W) π),
      let M := actualSmoothBoundaryMarked W E
      let U := BlowupTower.step T (strictAlong T W) π hπ
      IsCanonical M ((canonicalInvariant.{u} n).inv M) U ∧ IsGeoResolution M U := by
  obtain ⟨hCan,_,_,_,_,hSmooth,hPureS,_,hMax,_,_,_⟩ := h
  have hInterior : interior (strictAlong T W) = ∅ :=
    HironakaEmbeddedReducible.interior_eq_empty_of_pure hd (fun x hx => subset_closure (hPureS x hx))
  obtain ⟨Z,π,hπ⟩ := ResolutionDriver.exists_blowup (strictAlong T W) hSmooth hInterior
  let M := actualSmoothBoundaryMarked W E
  let U := BlowupTower.step T (strictAlong T W) π hπ
  have hCanU : IsCanonical M ((canonicalInvariant.{u} n).inv M) U := ⟨hCan,Or.inr hMax.symm⟩
  have hTestU := (canonicalInvariant.{u} n).isInvValue.isGeoTestTower_of_isCanonical
    (smoothBoundaryMarked_domain hW hd hPure hE) U hCanU
  obtain ⟨hMarked,hSmoothU,_⟩ := actual_smooth_mark_one_test_tower_state W E hW d hPure U hTestU
  refine ⟨Z,π,hπ,hCanU,hTestU,?_⟩
  rw [hMarked,cosupp_mk_vanishingIdeal hSmoothU.1]
  change BlowupStrictSubmanifold.geoStrictTransform π (strictAlong T W) (strictAlong T W) = ∅
  exact BlowupStrictIdeal.geoStrictTransform_self

private theorem emptyAware_prefix_of_nonempty_last {X' A B Y Z : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' A} {T : BlowupTower X B} {C' : Set A} {C : Set B}
    {π' : Y → A} {π : Z → B} {hπ' : IsBlowupAlong n C' π'} {hπ : IsBlowupAlong n C π}
    {χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (hC' : C'.Nonempty) (hC : C.Nonempty)
    (h : EmptyAwareTowerIso Φ (.step T' C' π' hπ') (.step T C π hπ) χ) :
    ∃ ψ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B, EmptyAwareTowerIso Φ T' T ψ := by
  cases h with
  | step h _ _ _ _ _ => exact ⟨_,h⟩
  | leftEmpty _ _ _ _ => exact (hC'.ne_empty rfl).elim
  | rightEmpty _ _ _ _ => exact (hC.ne_empty rfl).elim

/-- Actual stopping histories of the same pure carrier and full list compare up to empty steps. -/
theorem actual_smooth_cleanup_emptyAware_same_input {W : Set X} {E : List (Set X)} {d : ℕ}
    (hW : IsClosedSubmanifold n W) (hd : d < n)
    (hPure : ∀ x ∈ W, RegularAtDim (n := n) W x d) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {Y' Y : CMfd.{u} n}
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (h' : ActualSmoothBoundaryCleanupResult W E d hE T') (h : ActualSmoothBoundaryCleanupResult W E d hE T) :
    ∃ ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T' T ψ := by
  have hn : 0 < n := Nat.zero_lt_of_lt hd
  have hM := smoothBoundaryMarked_domain hW hd hPure hE
  by_cases hEmpty : W = ∅
  · subst W
    exact original_terminal_histories_emptyAware_same_record hn _ hM T' T
      (by simpa only [canonicalInvariant_eq_invFamily hn] using h'.1)
      (by simpa only [canonicalInvariant_eq_invFamily hn] using h.1)
      (empty_carrier_cleanup_resolves T' h') (empty_carrier_cleanup_resolves T h)
  · have hNonempty : W.Nonempty := nonempty_iff_ne_empty.mpr hEmpty
    have hC' := retained_carrier_nonempty hW.1 hE hM hDense hNonempty T' h'
    have hC := retained_carrier_nonempty hW.1 hE hM hDense hNonempty T h
    obtain ⟨Z',π',hπ',hCan',hRes'⟩ := exists_resolving_last_step hW hd hPure hE T' h'
    obtain ⟨Z,π,hπ,hCan,hRes⟩ := exists_resolving_last_step hW hd hPure hE T h
    obtain ⟨χ,hχ⟩ := original_terminal_histories_emptyAware_same_record hn _ hM
      (.step T' (strictAlong T' W) π' hπ') (.step T (strictAlong T W) π hπ)
      (by simpa only [canonicalInvariant_eq_invFamily hn] using hCan')
      (by simpa only [canonicalInvariant_eq_invFamily hn] using hCan) hRes' hRes
    exact emptyAware_prefix_of_nonempty_last hC' hC hχ

/-- Literal open restriction preserves the complete pure smooth stopping history and its full list. -/
theorem actual_smooth_cleanup_restrict {W : Set X} {E : List (Set X)} {d : ℕ}
    (hW : IsClosedSubmanifold n W) (hd : d < n)
    (hPure : ∀ x ∈ W, RegularAtDim (n := n) W x d) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (h : ActualSmoothBoundaryCleanupResult W E d hE T) (U : Opens X) :
    let WU := (Subtype.val : U → X) ⁻¹' W
    let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
    ∃ hEU : IsSNCDivisor n EU, ActualSmoothBoundaryCleanupResult WU EU d hEU (restrict U T) := by
  let WU : Set (CMfd.of (n := n) U) := (Subtype.val : U → X) ⁻¹' W
  let EU : List (Set (CMfd.of (n := n) U)) := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let M := actualSmoothBoundaryMarked W E
  let MU := actualSmoothBoundaryMarked WU EU
  let R := canonicalInvariant.{u} n
  let Q := restrict U T
  have hPull : MarkedIdeal.pullback (Subtype.val : U → X) M = MU := pullback_val_mk_vanishingIdeal U E W
  have hM : IsInvDomain n M := smoothBoundaryMarked_domain hW hd hPure hE
  have hMU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  rw [hPull] at hMU
  have hEU : IsSNCDivisor n EU := hMU.isWellFormed.isSNCDivisor
  have hSup : (Subtype.val : U → X) ⁻¹' (⋃ H ∈ E, H) = ⋃ H ∈ EU, H := preimage_biUnion_list _ _
  have hDenseU : WU ⊆ closure (WU \ ⋃ H ∈ EU, H) := by
    have he := U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ ⋃ H ∈ E, H)
    intro x hx
    have hh := (Set.ext_iff.mp he x).mp (hDense hx)
    change x ∈ closure ((Subtype.val : U → X) ⁻¹' (W \ ⋃ H ∈ E, H)) at hh
    rw [preimage_sdiff,hSup] at hh
    exact hh
  have hPureU (x : U) (hx : x ∈ WU) : RegularAtDim (n := n) WU x d :=
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hPure x.val hx)
  have hWU : IsClosedSubmanifold n WU :=
    ⟨hW.1.preimage continuous_subtype_val,fun x hx => ⟨d,hPureU x hx⟩⟩
  have hGood (x : U) (hx : x ∈ actualSmoothBoundaryOpen EU hEU) :
      x.val ∈ actualSmoothBoundaryOpen E hE := by
    change x ∉ ⋃ H ∈ EU, H at hx
    rw [← hSup] at hx
    exact hx
  have hAvoid := HironakaG3RStoppedOverlap.centresAvoid_restrict U hGood T h.2.2.1
  have hCan := Seq.ResolutionInvariantExt.isCanonical_restrict R hM U T h.1
  rw [hPull] at hCan
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hMU Q hCan
  obtain ⟨hMarked,hSmooth,hPureQ⟩ := actual_smooth_mark_one_test_tower_state WU EU hWU d hPureU Q hTest
  have hStrict : strictAlong Q WU = strictTransform n Q.proj WU :=
    strictAlong_eq_library_of_avoid WU hWU.1 (actualSmoothBoundaryOpen EU hEU) hDenseU Q hAvoid
  have hCos : (geoTransformAlong MU Q).cosupp = strictAlong Q WU := by
    rw [hMarked,cosupp_mk_vanishingIdeal hSmooth.1]
  obtain ⟨Z,π,hπ,hCanLast,_⟩ := exists_resolving_last_step hW hd hPure hE T h
  have hCanLastU := Seq.ResolutionInvariantExt.isCanonical_restrict R hM U
    (.step T (strictAlong T W) π hπ) hCanLast
  rw [hPull] at hCanLastU
  have hTail : strictAlong Q WU = (Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T W :=
    strictAlong_restrict U T W
  have hNext : ((Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T W) = ∅ ∨
      ((Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T W) =
        maxLocus (R.inv MU Q) (geoTransformAlong MU Q).cosupp := hCanLastU.2
  rw [← hTail] at hNext
  have hMax : maxLocus (R.inv MU Q) (geoTransformAlong MU Q).cosupp = strictAlong Q WU := by
    rcases hNext with hEmpty | hMax
    · rw [hCos,hEmpty]
      simp [maxLocus]
    · exact hMax.symm
  have hNC : HasNormalCrossings n (strictAlong Q WU) (geoTransformAlong MU Q).E := by
    rw [← hMax]
    exact (R.isInvValue.isAdmissibleCentre_maxLocus hMU Q hCan hTest).2.2
  have hOverW := centresOver_cosupp MU hMU.isWellFormed.isClosedSubmanifold_N hMU.isWellFormed.isCoherent Q hTest
  rw [show MU.cosupp = WU from cosupp_mk_vanishingIdeal hWU.1 EU] at hOverW
  have hOverE : CentresOver (⋃ H ∈ EU, H) Q := by
    have he := centresOver_compl_of_centresAvoid (actualSmoothBoundaryOpen EU hEU) Q hAvoid
    change CentresOver (((⋃ H ∈ EU, H)ᶜ)ᶜ) Q at he
    simpa only [compl_compl] using he
  have hOver := centresOver_of_inter_subset (Subset.refl (WU ∩ ⋃ H ∈ EU, H)) Q hOverW hOverE
  exact ⟨hEU,hCan,hTest,hAvoid,boundary_steps_of_test_avoid WU EU hWU d hPureU hEU Q hTest hAvoid,
    hMarked,hSmooth,hPureQ,hStrict,hMax,hNC,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hMU Q hTest).isWellFormed.isSNCDivisor,
    isAdmissibleBlowupSequence_proj MU _ Q hTest hOver⟩

open HironakaOriginalBoundaryEmptyFilterComparison
attribute [local instance] Classical.propDecidable

/-- Actual terminal towers compare across pullback and deletion of empty initial boundary slots. -/
theorem terminal_emptyAware_over_filtered_boundary (hn : 0 < n) {X' Y' Y : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (M' : MarkedIdeal n X') (hM : IsInvDomain n M)
    (hN : M'.N = Φ ⁻¹' M.N) (hI : M'.ideal = GermIdeal.pullback (m := n) Φ M.ideal)
    (hd : M'.d = M.d)
    (hB : M'.E.filter (fun H => decide H.Nonempty) =
      (M.E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (hCan' : IsCanonical M' ((canonicalInvariant n).inv M') T')
    (hCan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hRes' : IsGeoResolution M' T') (hRes : IsGeoResolution M T) :
    ∃ ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso Φ T' T ψ := by
  have hCommon : nonemptyBoundary M' = MarkedIdeal.pullback Φ (nonemptyBoundary M) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN hB hI hd
  have hCanF' := (isCanonical_nonemptyBoundary_iff M' T').mpr hCan'
  have hResF' := (isGeoResolution_nonemptyBoundary_iff M' T').mpr hRes'
  rw [hCommon] at hCanF' hResF'
  exact original_terminal_histories_emptyAware_over_pullback hn (nonemptyBoundary M)
    (isInvDomain_nonemptyBoundary M hM) Φ T' T
    (by simpa only [canonicalInvariant_eq_invFamily hn] using hCanF')
    (by simpa only [canonicalInvariant_eq_invFamily hn] using (isCanonical_nonemptyBoundary_iff M T).mpr hCan)
    hResF' ((isGeoResolution_nonemptyBoundary_iff M T).mpr hRes)

/-- Pure actual cleanup towers compare across a prescribed base map and empty boundary slots. -/
theorem actual_smooth_cleanup_emptyAware_over_filtered_boundary {X' Y' Y : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} {E' : List (Set X')} {d : ℕ}
    (hW : IsClosedSubmanifold n W) (hW' : IsClosedSubmanifold n (Φ ⁻¹' W)) (hd : d < n)
    (hPure : ∀ x ∈ W, RegularAtDim (n := n) W x d)
    (hPure' : ∀ x ∈ Φ ⁻¹' W, RegularAtDim (n := n) (Φ ⁻¹' W) x d)
    (hE : IsSNCDivisor n E) (hE' : IsSNCDivisor n E')
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hDense' : Φ ⁻¹' W ⊆ closure ((Φ ⁻¹' W) \ ⋃ H ∈ E', H))
    (hB : E'.filter (fun H => decide H.Nonempty) =
      (E.filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·))
    (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (h' : ActualSmoothBoundaryCleanupResult (Φ ⁻¹' W) E' d hE' T')
    (h : ActualSmoothBoundaryCleanupResult W E d hE T) :
    ∃ ψ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y, EmptyAwareTowerIso Φ T' T ψ := by
  let M := actualSmoothBoundaryMarked W E
  let M' := actualSmoothBoundaryMarked (Φ ⁻¹' W) E'
  have hM : IsInvDomain n M := smoothBoundaryMarked_domain hW hd hPure hE
  have hM' : IsInvDomain n M' := smoothBoundaryMarked_domain hW' hd hPure' hE'
  have hN : M'.N = Φ ⁻¹' M.N := preimage_univ.symm
  have hI : M'.ideal = GermIdeal.pullback (m := n) Φ M.ideal :=
    (HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion
      (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism Φ) W).symm
  have compare {D' D : CMfd.{u} n} :=
    terminal_emptyAware_over_filtered_boundary (Nat.zero_lt_of_lt hd) (Y' := D') (Y := D) Φ M M' hM hN hI rfl hB
  by_cases hEmpty : W = ∅
  · have hRes : IsGeoResolution M T := by
      subst W
      exact empty_carrier_cleanup_resolves T h
    have hRes' : IsGeoResolution M' T' := by
      subst W
      simpa only [M',preimage_empty] using empty_carrier_cleanup_resolves T'
        (by simpa only [preimage_empty] using h')
    exact compare T' T h'.1 h.1 hRes' hRes
  · have hNonempty : W.Nonempty := nonempty_iff_ne_empty.mpr hEmpty
    have hC := retained_carrier_nonempty hW.1 hE hM hDense hNonempty T h
    have hC' := retained_carrier_nonempty hW'.1 hE' hM' hDense' (hNonempty.preimage Φ.surjective) T' h'
    obtain ⟨Z,π,hπ,hCan,hRes⟩ := exists_resolving_last_step hW hd hPure hE T h
    obtain ⟨Z',π',hπ',hCan',hRes'⟩ := exists_resolving_last_step hW' hd hPure' hE' T' h'
    obtain ⟨χ,hχ⟩ := compare (.step T' (strictAlong T' (Φ ⁻¹' W)) π' hπ')
      (.step T (strictAlong T W) π hπ) hCan' hCan hRes' hRes
    exact emptyAware_prefix_of_nonempty_last hC' hC hχ

open MarkedIdealTowerTransport BlowupTowerIsomorphism NormalCrossingsInvariance

/-- Actual rebasing of the pure stopping certificate along a biholomorphism, retaining all stages
and the full pullback boundary. -/
theorem actual_smooth_cleanup_transport {X' Y : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {W : Set X} {E : List (Set X)} {d : ℕ}
    (hW : IsClosedSubmanifold n W) (hd : d < n)
    (hPure : ∀ x ∈ W, RegularAtDim (n := n) W x d) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (T : BlowupTower X Y)
    (h : ActualSmoothBoundaryCleanupResult W E d hE T) :
    ∃ hE' : IsSNCDivisor n (E.map (Φ ⁻¹' ·)),
      ActualSmoothBoundaryCleanupResult (Φ ⁻¹' W) (E.map (Φ ⁻¹' ·)) d hE' (transport Φ T).tower := by
  let W' := Φ ⁻¹' W
  let E' := E.map (Φ ⁻¹' ·)
  let R := canonicalInvariant.{u} n
  let M := actualSmoothBoundaryMarked W E
  let M' := actualSmoothBoundaryMarked W' E'
  let P := transport Φ T
  let Q := P.tower
  let ψ := P.back
  have hM : IsInvDomain n M := smoothBoundaryMarked_domain hW hd hPure hE
  have hPull : MarkedIdeal.pullback Φ M = M' := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · exact preimage_univ
    · rfl
    · exact HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion
        (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism Φ) W
    · rfl
  obtain ⟨hM', hCan, hIso, _, _hRecord, hMax, _, hAvoid⟩ :=
    HironakaOriginalBoundaryEmptyBaseComparison.canonical_transport_dictionary M hM Φ T h.1
  rw [hPull] at hM' hCan hMax
  have hE' : IsSNCDivisor n E' := hM'.isWellFormed.isSNCDivisor
  have hW' : IsClosedSubmanifold n W' := (isClosedSubmanifold_preimage_iff Φ).mpr hW
  have hPure' (x : X') (hx : x ∈ W') : RegularAtDim (n := n) W' x d :=
    (CodimOnePartCanonical.regularAtDim_preimage_iff Φ).mpr (hPure (Φ x) hx)
  have hDense' : W' ⊆ closure (W' \ ⋃ H ∈ E', H) :=
    HironakaOriginalSmoothIntrinsicRegularLoci.boundary_density_preimage
      (HironakaSmoothSubmersionOriginalGlobalFinite.isSubmersion_biholomorphism Φ) W E hDense
  have hOpen : HironakaOriginalBoundaryEmptyBaseComparison.baseOpen Φ (actualSmoothBoundaryOpen E hE) =
      actualSmoothBoundaryOpen E' hE' := by
    apply Opens.ext
    change Φ ⁻¹' (⋃ H ∈ E, H)ᶜ = (⋃ H ∈ E', H)ᶜ
    rw [preimage_compl, preimage_biUnion_list]
  have ha := hAvoid _ h.2.2.1
  rw [hOpen] at ha
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical hM' Q hCan
  obtain ⟨hMarked, hSmooth, hPureQ⟩ := actual_smooth_mark_one_test_tower_state W' E' hW' d hPure' Q ht
  have hStrict : strictAlong Q W' = strictTransform n Q.proj W' :=
    strictAlong_eq_library_of_avoid W' hW'.1 _ hDense' Q ha
  have hStrictMap : strictAlong Q W' = ψ ⁻¹' strictAlong T W :=
    hIso.strictAlong_eq W
  have hMaxQ : maxLocus (R.inv M' Q) (geoTransformAlong M' Q).cosupp = strictAlong Q W' := by
    rw [hMax, h.2.2.2.2.2.2.2.2.1, hStrictMap]
  have hNC : HasNormalCrossings n (strictAlong Q W') (geoTransformAlong M' Q).E := by
    rw [← hMaxQ]
    exact (R.isInvValue.isAdmissibleCentre_maxLocus hM' Q hCan ht).2.2
  have hOver := centresOver_cosupp M' hM'.isWellFormed.isClosedSubmanifold_N hM'.isWellFormed.isCoherent Q ht
  rw [show M'.cosupp = W' from cosupp_mk_vanishingIdeal hW'.1 E'] at hOver
  have hOverE : CentresOver (⋃ H ∈ E', H) Q := by
    have hv := centresOver_compl_of_centresAvoid (actualSmoothBoundaryOpen E' hE') Q ha
    change CentresOver (((⋃ H ∈ E', H)ᶜ)ᶜ) Q at hv
    simpa only [compl_compl] using hv
  exact ⟨hE', hCan, ht, ha, boundary_steps_of_test_avoid W' E' hW' d hPure' hE' Q ht ha,
    hMarked, hSmooth, hPureQ, hStrict, hMaxQ, hNC,
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM' Q ht).isWellFormed.isSNCDivisor,
    isAdmissibleBlowupSequence_proj M' _ Q ht
      (centresOver_of_inter_subset (Subset.refl (W' ∩ ⋃ H ∈ E', H)) Q hOver hOverE)⟩

end
end Hironaka.HironakaActualSmoothCleanupPhysicalComparison
