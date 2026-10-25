/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualInitialFullCompatibility

/-!
# Actual chronological canonical windows and the first sharp local full-value drop

The unchanged original marked input and actual restricted tower define the
value. No equality with a noncanonical global TEST value is asserted. The
original-only endpoint internally supplies every required window over its
first centre. Later-history tracking and higher-dimensional termination remain
open.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaSharpActualFirstFullInvariantDrop
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen InvDomainTowerAlong
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalDistinctDefectPhase HironakaSharpOriginalDistinctTraceUSC
  HironakaSharpOriginalRestrictedDistinctDefectCentre
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualInitialFullCompatibility HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualDynamicDistinctCentre HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualFiniteChronologicalHistory
  NormalCrossings GermIdealOrder CanonicalCentres ResolutionDriver ResolutionInvariantDriver
  RelativePrincipalizationSpan
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

attribute [local irreducible] invFamily

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A genuinely canonical restriction of the SAME original input and tower,
at a point of its actual transformed cosupport. -/
def CanonicalWindowAt (hn : 0 < n) (M : MarkedIdeal n X) (T : BlowupTower X Y) (z : Y) : Prop :=
  ∃ U : Opens X, ∃ hzU : T.proj z ∈ U,
    IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) M)
      ((invFamily hn (n + 1)).inv (MarkedIdeal.pullback (Subtype.val : U → X) M)) (restrict U T) ∧
    (⟨z, hzU⟩ : openPreimage T U) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).cosupp

/-- The partial chronological full value: evaluated on an actual canonical
window, with no fallback value on points outside the domain. -/
def canonicalWindowValue (hn : 0 < n) (M : MarkedIdeal n X) (T : BlowupTower X Y) (z : Y)
    (h : CanonicalWindowAt hn M T z) : ValTy (n + 1) :=
  (invFamily hn (n + 1)).inv
    (MarkedIdeal.pullback (Subtype.val : h.choose → X) M) (restrict h.choose T)
    ⟨z, h.choose_spec.choose⟩

/-- Every actual canonical window gives the defined SAME chronological value. -/
theorem canonicalWindowValue_eq (hn : 0 < n) {M : MarkedIdeal n X}
    (hM : IsInvDomain (n + 1) M) (T : BlowupTower X Y) (z : Y)
    (h : CanonicalWindowAt hn M T z) (U : Opens X) (hzU : T.proj z ∈ U)
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) M)
      ((invFamily hn (n + 1)).inv (MarkedIdeal.pullback (Subtype.val : U → X) M)) (restrict U T)) :
    canonicalWindowValue hn M T z h =
      (invFamily hn (n + 1)).inv (MarkedIdeal.pullback (Subtype.val : U → X) M)
        (restrict U T) ⟨z, hzU⟩ := by
  exact (Seq.StepOneNearby.inv_eq_of_two_opens (invFamily hn (n + 1))
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T
    (isInvDomain_pullback_val h.choose hM) h.choose_spec.choose_spec.1
    (isInvDomain_pullback_val U hM) hcan h.choose_spec.choose hzU
    h.choose_spec.choose_spec.2).1

private theorem original_product_domain (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {d : ℕ} (hd : d + 1 ≤ n)
    (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1)) :
    IsInvDomain (n + 1) (originalMemberProductMarked W E 1) := by
  have h := originalMemberProductMarked_isInvDomain hn hW hE hd hr hdense le_rfl
  exact ⟨h.isWellFormed, fun x hx => by
    obtain ⟨j, hj, hjreg⟩ := h.dimLE x hx
    exact ⟨j, hj.trans (Nat.le_succ n), hjreg⟩, h.one_le_d, h.isNonzeroAlongAt⟩

private theorem maximum_of_bounded_level {Λ : Type*} [LinearOrder Λ]
    (f : X → Λ) (C S : Set X) (x : X) (U : Opens X) (hxU : x ∈ U) (hxC : x ∈ C)
    (hlevel : (Subtype.val : U → X) ⁻¹' C =
      (Subtype.val : U → X) ⁻¹' {y | y ∈ S ∧ f y = f x})
    (hle : ∀ y : U, y.val ∈ S → f y.val ≤ f x)
    (g : U → Λ) (s : Set U) (hs : s = (Subtype.val : U → X) ⁻¹' S)
    (hvalue : ∀ y : U, y.val ∈ S → g y = f y.val) :
    (Subtype.val : U → X) ⁻¹' C = maxLocus g s := by
  have hx : (⟨x, hxU⟩ : U) ∈ (Subtype.val : U → X) ⁻¹' C := hxC
  have hxS : x ∈ S := (hlevel ▸ hx).1
  ext y
  constructor
  · intro hy
    have hyS : y.val ∈ S := (hlevel ▸ hy).1
    have hyval : f y.val = f x := (hlevel ▸ hy).2
    refine ⟨hs.symm ▸ hyS, ?_⟩
    intro q hq
    have hqS : q.val ∈ S := by simpa only [hs, mem_preimage] using hq
    rw [hvalue q hqS, hvalue y hyS, hyval]
    exact hle q hqS
  · rintro ⟨hy, hmax⟩
    have hyS : y.val ∈ S := by simpa only [hs, mem_preimage] using hy
    have hxS' : (⟨x, hxU⟩ : U) ∈ s := hs.symm ▸ hxS
    have hxy := hmax ⟨x, hxU⟩ hxS'
    rw [hvalue ⟨x, hxU⟩ hxS, hvalue y hyS] at hxy
    exact hlevel.symm ▸ ⟨hyS, le_antisymm (hle y hyS) hxy⟩

private theorem original_first_level_windows (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {d : ℕ} (hd : d + 1 ≤ n)
    (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1))
    {C : Set X} (hC : C = maxLocus ((invFamily hn (n + 1)).inv
      (originalMemberProductMarked W E 1) (.refl : BlowupTower X X)) (originalDistinctDefectPhase W E))
    {x : X} (hx : x ∈ C) :
    let M := originalMemberProductMarked W E 1
    let f := (invFamily hn (n + 1)).inv M (.refl : BlowupTower X X)
    ∃ U : Opens X, x ∈ U ∧
      (∀ y : U, y.val ∈ M.cosupp → f y.val ≤ f x) ∧
      (Subtype.val : U → X) ⁻¹' C =
        (Subtype.val : U → X) ⁻¹' {y | y ∈ M.cosupp ∧ f y = f x} := by
  let M := originalMemberProductMarked W E 1
  let R := invFamily.{u} hn (n + 1)
  let f := R.inv M (.refl : BlowupTower X X)
  let Z := originalDistinctDefectPhase W E
  have hM := original_product_domain hn hW hE hdense hd hr
  have hZcos : Z ⊆ M.cosupp := by
    intro y hy
    exact (ordinaryTraceOrder_cosupport_iff hW (isCoherent_originalMemberProduct hn hE)
      (fun _ hz => originalMemberProduct_isNonzeroAlongAt hn hE hdense hz) hy.1 1).mpr (by
        have hlt := hy.2
        omega)
  have hxMax : x ∈ maxLocus f Z := hC ▸ hx
  have hCeq : C = {y | y ∈ Z ∧ f y = f x} := hC.trans (maxLocus_eq_level hxMax)
  have husc := R.isInvValue.usc M hM (.refl : BlowupTower X X) trivial
  rw [geoTransformAlong_refl] at husc
  have hnb : ∀ᶠ y in 𝓝 x, (y ∈ M.cosupp → f y ≤ f x) ∧
      (y ∈ W → f y = f x → y ∈ Z) :=
    (husc x (hZcos hxMax.1)).and
      (eventually_originalDistinctDefectPhase_of_same_invariant hn hW hE 1 hxMax.1)
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp hnb
  let U : Opens X := ⟨V, hVo⟩
  refine ⟨U, hxV, fun y hy => (hV y.property).1 hy, ?_⟩
  ext y
  constructor
  · intro hy
    exact ⟨hZcos (hCeq ▸ hy).1, (hCeq ▸ hy).2⟩
  · rintro ⟨hy, hEq⟩
    exact hCeq.symm ▸ ⟨(hV y.property).2 (M.cosupp_subset_N hy) hEq, hEq⟩

/-- USC and true same-value FIRST saturation internally construct an open
where the sharp centre is the ENTIRE ordinary maximum, not a subset of it. -/
theorem original_first_maximum_windows (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {d : ℕ} (hd : d + 1 ≤ n)
    (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1))
    {C : Set X} (hC : C = maxLocus ((invFamily hn (n + 1)).inv
      (originalMemberProductMarked W E 1) (.refl : BlowupTower X X)) (originalDistinctDefectPhase W E))
    {x : X} (hx : x ∈ C) :
    ∃ U : Opens X, x ∈ U ∧
      (Subtype.val : U → X) ⁻¹' C =
        maxLocus ((invFamily hn (n + 1)).inv
          (MarkedIdeal.pullback (Subtype.val : U → X) (originalMemberProductMarked W E 1))
          (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)))
          (MarkedIdeal.pullback (Subtype.val : U → X) (originalMemberProductMarked W E 1)).cosupp := by
  let M := originalMemberProductMarked W E 1
  let R := invFamily.{u} hn (n + 1)
  have hM := original_product_domain hn hW hE hdense hd hr
  obtain ⟨U, hxU, hbound, hlevel⟩ := original_first_level_windows hn hW hE hdense hd hr hC hx
  have hcos := cosupp_pullback_val M
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) U
  have hv (y : U) (hy : y.val ∈ M.cosupp) :
      R.inv (MarkedIdeal.pullback (Subtype.val : U → X) M)
        (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) y =
        R.inv M (.refl : BlowupTower X X) y.val :=
    R.isInvValue.restrictOpen M hM U (.refl : BlowupTower X X) trivial y hy
  exact ⟨U, hxU, maximum_of_bounded_level _ C M.cosupp x U hxU hx hlevel hbound
    _ _ hcos hv⟩

/-- Every actual new cosupport point over the first sharp centre internally
admits a canonical window; its defined chronological local full value drops. -/
theorem original_first_window_drop (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {d : ℕ} (hd : d + 1 ≤ n)
    (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1))
    {C : Set X} (hC : C = maxLocus ((invFamily hn (n + 1)).inv
      (originalMemberProductMarked W E 1) (.refl : BlowupTower X X)) (originalDistinctDefectPhase W E))
    (hAdm : (originalMemberProductMarked W E 1).IsAdmissibleCentre C)
    {π : Y → X} (hπ : IsBlowupAlong n C π) {z : Y}
    (hz : z ∈ (geoTransformAlong (originalMemberProductMarked W E 1)
      (.step .refl C π hπ)).cosupp) (hzC : π z ∈ C) :
    ∃ hwin : CanonicalWindowAt hn (originalMemberProductMarked W E 1) (.step .refl C π hπ) z,
      canonicalWindowValue hn (originalMemberProductMarked W E 1) (.step .refl C π hπ) z hwin <
        (invFamily hn (n + 1)).inv (originalMemberProductMarked W E 1) .refl (π z) := by
  let M := originalMemberProductMarked W E 1
  let R := invFamily.{u} hn (n + 1)
  let T : BlowupTower X Y := .step .refl C π hπ
  have hM := original_product_domain hn hW hE hdense hd hr
  have hTest : IsGeoTestTower M T := ⟨trivial, hAdm⟩
  obtain ⟨U, hxU, hmax⟩ := original_first_maximum_windows hn hW hE hdense hd hr hC hzC
  have hzU : T.proj z ∈ U := hxU
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let zU : openPreimage T U := ⟨z, hzU⟩
  have hcan : IsCanonical MU (R.inv MU) (restrict U T) := ⟨trivial, Or.inr hmax⟩
  have hcosU : zU ∈ (geoTransformAlong MU (restrict U T)).cosupp := by
    rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
      hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent U T hTest]
    exact hz
  have hwin : CanonicalWindowAt hn M T z := ⟨U, hzU, hcan, hcosU⟩
  have hπU := BlowupRestrictOpen.isBlowupAlong_restrict hπ U
    (U.isOpen.preimage hπ.contMDiff.continuous)
  have hdrop := (R.isInvValue.decrease (X := CMfd.of (n := n) U)
    (Y := CMfd.of (n := n) U) (Z := CMfd.of (n := n) (openPreimage T U))
    MU (isInvDomain_pullback_val U hM)
    (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))
    ((Subtype.val : U → X) ⁻¹' C)
    (fun p : openPreimage T U => (⟨π p.val, p.property⟩ : U)) hπU trivial
    ⟨⟨π z, hxU⟩, hzC⟩ hmax zU hcosU).1
      (show (⟨π z, hxU⟩ : U) ∈ (Subtype.val : U → X) ⁻¹' C from hzC)
  have href := R.isInvValue.restrictOpen M hM U (.refl : BlowupTower X X) trivial
    (⟨π z, hxU⟩ : U) (hAdm.2.1 hzC)
  refine ⟨hwin, ?_⟩
  rw [canonicalWindowValue_eq hn hM T z hwin U hzU hcan]
  exact hdrop.trans_eq href

private theorem first_window_eq_off_centre (hn : 0 < n) {M : MarkedIdeal n X}
    (hM : IsInvDomain (n + 1) M) {C : Set X} (hAdm : M.IsAdmissibleCentre C)
    {π : Y → X} (hπ : IsBlowupAlong n C π) {z : Y}
    (hz : z ∈ (geoTransformAlong M (.step .refl C π hπ)).cosupp) (hzC : π z ∉ C) :
    ∃ hwin : CanonicalWindowAt hn M (.step .refl C π hπ) z,
      canonicalWindowValue hn M (.step .refl C π hπ) z hwin =
        (invFamily hn (n + 1)).inv M .refl (π z) := by
  let R := invFamily.{u} hn (n + 1)
  let T : BlowupTower X Y := .step .refl C π hπ
  let U : Opens X := ⟨Cᶜ, hAdm.1.1.isOpen_compl⟩
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  have hTest : IsGeoTestTower M T := ⟨trivial, hAdm⟩
  have hzU : T.proj z ∈ U := hzC
  let zU : openPreimage T U := ⟨z, hzU⟩
  have hEmpty : (Subtype.val : U → X) ⁻¹' C = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact x.property hx
  have hcan : IsCanonical MU (R.inv MU) (restrict U T) := ⟨trivial, Or.inl hEmpty⟩
  have hcosU : zU ∈ (geoTransformAlong MU (restrict U T)).cosupp := by
    rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
      hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent U T hTest]
    exact hz
  have hwin : CanonicalWindowAt hn M T z := ⟨U, hzU, hcan, hcosU⟩
  have hπU := BlowupRestrictOpen.isBlowupAlong_restrict hπ U
    (U.isOpen.preimage hπ.contMDiff.continuous)
  have heq := R.isInvValue.emptyStep (X := CMfd.of (n := n) U)
    (Y := CMfd.of (n := n) U) (Z := CMfd.of (n := n) (openPreimage T U))
    MU (isInvDomain_pullback_val U hM)
    (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))
    ((Subtype.val : U → X) ⁻¹' C)
    (fun p : openPreimage T U => (⟨π p.val, p.property⟩ : U)) hπU hEmpty trivial zU hcosU
  have hxcos := StepOneWellFounded.proj_mem_cosupp_step hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent (.refl : BlowupTower X X) C π hπ hTest hz
  have href := R.isInvValue.restrictOpen M hM U (.refl : BlowupTower X X) trivial
    (⟨π z, hzU⟩ : U) hxcos
  refine ⟨hwin, ?_⟩
  rw [canonicalWindowValue_eq hn hM T z hwin U hzU hcan]
  exact heq.trans href

/-- The partial value is internally defined on the ENTIRE new original
cosupport, with strict drop over C and exact equality off C. -/
theorem original_first_window_comparison (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {d : ℕ} (hd : d + 1 ≤ n)
    (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1))
    {C : Set X} (hC : C = maxLocus ((invFamily hn (n + 1)).inv
      (originalMemberProductMarked W E 1) (.refl : BlowupTower X X)) (originalDistinctDefectPhase W E))
    (hAdm : (originalMemberProductMarked W E 1).IsAdmissibleCentre C)
    {π : Y → X} (hπ : IsBlowupAlong n C π) {z : Y}
    (hz : z ∈ (geoTransformAlong (originalMemberProductMarked W E 1)
      (.step .refl C π hπ)).cosupp) :
    ∃ hwin : CanonicalWindowAt hn (originalMemberProductMarked W E 1) (.step .refl C π hπ) z,
      (π z ∈ C → canonicalWindowValue hn (originalMemberProductMarked W E 1)
        (.step .refl C π hπ) z hwin <
        (invFamily hn (n + 1)).inv (originalMemberProductMarked W E 1) .refl (π z)) ∧
      (π z ∉ C → canonicalWindowValue hn (originalMemberProductMarked W E 1)
        (.step .refl C π hπ) z hwin =
        (invFamily hn (n + 1)).inv (originalMemberProductMarked W E 1) .refl (π z)) := by
  by_cases hzC : π z ∈ C
  · obtain ⟨hwin, hdrop⟩ := original_first_window_drop hn hW hE hdense hd hr hC hAdm hπ hz hzC
    exact ⟨hwin, fun _ => hdrop, fun h => False.elim (h hzC)⟩
  · obtain ⟨hwin, heq⟩ := first_window_eq_off_centre hn
      (original_product_domain hn hW hE hdense hd hr) hAdm hπ hz hzC
    exact ⟨hwin, fun h => False.elim (hzC h), fun _ => heq⟩

/-- ONLY original inputs choose one actual initial sharp blowup. For its
ENTIRE new original-product cosupport the canonical-window domain is a
conclusion, with strict drop over the centre and equality off it. -/
theorem exists_actual_initial_sharp_blowup_with_local_drop (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (hK : IsCompact W)
    {d : ℕ} (hd : d + 1 ≤ n) (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1))
    (hne : (chronologicalDistinctDefect W E (.refl : BlowupTower X X)).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧
      (originalMemberProductMarked W E 1).IsAdmissibleCentre C ∧
      (currentProductMarked W E (.refl : BlowupTower X X)).IsAdmissibleCentre C ∧
      C ⊆ chronologicalDistinctDefect W E (.refl : BlowupTower X X) ∧
      C ⊆ originalSharpBadLocus (n := n) W E ∧
      (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      IsProperMap π ∧ ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (originalGoodLocus (n := n) W E) ∧
      IsClosedSubmanifold n (strictTransform n π W) ∧
      IsSNCDivisor n (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      C = maxLocus ((invFamily hn (n + 1)).inv
        (currentProductMarked W E (.refl : BlowupTower X X)) .refl)
        (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) ∧
      C = maxLocus ((invFamily hn (n + 1)).inv
        (originalMemberProductMarked W E 1) .refl) (originalDistinctDefectPhase W E) ∧
      ∀ z ∈ (geoTransformAlong (originalMemberProductMarked W E 1) (.step .refl C π hπ)).cosupp,
        ∃ hwin : CanonicalWindowAt hn (originalMemberProductMarked W E 1) (.step .refl C π hπ) z,
          (π z ∈ C → canonicalWindowValue hn (originalMemberProductMarked W E 1)
            (.step .refl C π hπ) z hwin <
            (invFamily hn (n + 1)).inv (originalMemberProductMarked W E 1) .refl (π z)) ∧
          (π z ∉ C → canonicalWindowValue hn (originalMemberProductMarked W E 1)
            (.step .refl C π hπ) z hwin =
            (invFamily hn (n + 1)).inv (originalMemberProductMarked W E 1) .refl (π z)) := by
  obtain ⟨C, Y, π, hCne, hAdm, hActualAdm, hCZ, hBad, hEmb, hπ,
    hProper, hHolo, hIso, hSmooth, hSNC, hMax⟩ :=
    exists_actual_initial_dynamic_sharp_blowup hn hW hE hdense hK hd hr hne
  have hSourceMax := hMax.trans (initial_actual_dynamic_maximum_eq_source hn hW hE hdense hd hr)
  refine ⟨C, Y, π, hπ, hCne, hAdm, hActualAdm, hCZ, hBad, hEmb,
    hProper, hHolo, hIso, hSmooth, hSNC, hMax, hSourceMax, ?_⟩
  intro z hz
  exact original_first_window_comparison hn hW hE hdense hd hr hSourceMax hAdm hπ hz

end
end Hironaka.HironakaSharpActualFirstFullInvariantDrop
