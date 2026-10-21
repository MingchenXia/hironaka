/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFamilyDefectOpenNaturality
import Hironaka.Resolution.HironakaSharpActualDynamicDistinctCentre
import Hironaka.Invariant.ResolutionInvariantSegments

/-!
# Actual chronological product records and dynamic maxima on open sets

The independently propagated original members, their whole relative product,
and the entire ordered born boundary restrict along a genuine history. The
full invariant and its actual distinct maximum consequently have exact open
traces. This does not assert sharp blowup decrease or termination.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaSharpActualDynamicMaximumOpen
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualChronologicalOpenNaturality
  HironakaSharpActualFamilyDefectOpenNaturality HironakaSharpActualDynamicDistinctCentre
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NormalCrossings IdealWeightPowers
  GermIdealOrder DivisorExponentAlong CanonicalCentres ResolutionDriver ResolutionInvariantSegments
open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ} {X : CMfd.{u} n}

private theorem current_template_regular {W : Set X} (hW : IsClosedSubmanifold n W)
    (d : ℕ) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x d) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T →
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
        RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N y d
  | _, .refl, _, _, hy => hreg _ hy
  | _, .step T C π hπ, hT, y, hy => by
    have hw : (geometricTemplate W []).IsWellFormed :=
      ⟨hW, isCoherent_unitIdeal, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT.1
    exact BlowupStrictSubmanifold.regularAtDim_geoStrictTransform hπ hwT.isClosedSubmanifold_N.1
      (current_template_regular hW d hreg T hT.1) hT.2.subset_N hy

/-- Original pure smooth geometry constructs the actual current product
domain after any genuine finite history, without compactness. -/
theorem currentProductMarked_isInvDomain_of_pure (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {d : ℕ} (hd : d + 1 ≤ n) (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T) :
    IsInvDomain (n + 1) (currentProductMarked W E T) := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW, isCoherent_unitIdeal, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT
  obtain ⟨hcP, hnzP, _hprP, _hord⟩ :=
    original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  exact ⟨⟨hwT.isClosedSubmanifold_N, hcP, hwT.isSNCDivisor, hwT.isTransverse⟩,
    fun y hy => ⟨d + 1, hd.trans (Nat.le_succ n), current_template_regular hW (d + 1) hr T hT y hy⟩,
    le_rfl, hnzP⟩

private theorem pullback_unit_open (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (unitIdeal n X) = unitIdeal n U := by
  apply GermIdeal.ext
  funext x g
  apply propext
  rw [mem_pullback_val_iff U isCoherent_unitIdeal]
  exact (holomorphicAt_iff_extendOpens U).symm

/-- Each actual original position restricts as a whole ideal; list order,
empty positions and coincident germ classes are all retained. -/
theorem chronologicalMemberFamily_open (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T) (U : Opens X) :
    (chronologicalMemberFamily W E T).map
        (GermIdeal.pullback (m := n) (Subtype.val : openPreimage T U → Y)) =
      chronologicalMemberFamily (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U T) := by
  simp only [chronologicalMemberFamily, List.map_map]
  apply List.map_congr_left
  intro H hH
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
  exact congrArg MarkedIdeal.ideal
    (original_members_chronological_open hn hW hE hdense i T hT U)

/-- The entire independently formed current product record commutes with
restriction of the actual history, including its complete born boundary. -/
theorem currentProductMarked_open (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T) (U : Opens X) :
    MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (currentProductMarked W E T) =
      currentProductMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
        (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U T) := by
  have hInitial : MarkedIdeal.pullback (Subtype.val : U → X) (geometricTemplate W []) =
      geometricTemplate (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W) [] :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl (pullback_unit_open U) rfl
  have hGeo := geoTransformAlong_restrict U hW isCoherent_unitIdeal T hT
  rw [hInitial] at hGeo
  have hCarrier := congrArg MarkedIdeal.N hGeo
  have hBoundary := congrArg MarkedIdeal.E hGeo
  dsimp only [MarkedIdeal.pullback] at hCarrier hBoundary
  have hN := (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hW isCoherent_unitIdeal T hT).1
  have hc : ∀ I ∈ chronologicalMemberFamily W E T, I.IsCoherent := by
    intro I hI
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hI
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    exact (original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT).2.2.2.1.isCoherent
  have hIdeal := relativeIdealListProduct_open hN (chronologicalMemberFamily W E T) hc
    (openPreimage T U)
  rw [chronologicalMemberFamily_open hn hW hE hdense T hT U, ← hCarrier] at hIdeal
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hCarrier.symm hBoundary.symm hIdeal rfl

/-- The full restarted invariant retains all its entries on the true
chronological distinct defect of the independently restricted history. -/
theorem current_full_value_open (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {d : ℕ} (hd : d + 1 ≤ n) (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T) (U : Opens X) (x : openPreimage T U)
    (hx : x.val ∈ chronologicalDistinctDefect W E T) :
    (invFamily hn (n + 1)).inv
        (currentProductMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
          (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U T)) .refl x =
      (invFamily hn (n + 1)).inv (currentProductMarked W E T) .refl x.val := by
  have hdom := currentProductMarked_isInvDomain_of_pure hn hW hE hdense hd hr T hT
  have hcos : x.val ∈ (currentProductMarked W E T).cosupp := by
    apply (ordinaryTraceOrder_cosupport_iff hdom.isWellFormed.isClosedSubmanifold_N
      hdom.isWellFormed.isCoherent hdom.isNonzeroAlongAt hx.1 1).mpr
    have hlt := hx.2
    rw [← chronological_product_eq_actual_family_product W E T] at hlt
    change 1 ≤ ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) x.val
    omega
  have h := (invFamily hn (n + 1)).isInvValue.restrictOpen (currentProductMarked W E T)
    hdom (openPreimage T U) .refl trivial x hcos
  rwa [currentProductMarked_open hn hW hE hdense T hT U] at h

/-- Meeting the original full dynamic maximum gives its exact restricted
maximum locus, using the actual independently propagated product records. -/
theorem current_dynamic_maximum_open_of_meeting (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {d : ℕ} (hd : d + 1 ≤ n) (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T) (U : Opens X)
    (hne : ((Subtype.val : openPreimage T U → Y) ⁻¹' maxLocus
      ((invFamily hn (n + 1)).inv (currentProductMarked W E T) .refl)
      (chronologicalDistinctDefect W E T)).Nonempty) :
    maxLocus ((invFamily hn (n + 1)).inv
        (currentProductMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
          (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U T)) .refl)
      (chronologicalDistinctDefect (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
        (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U T)) =
      (Subtype.val : openPreimage T U → Y) ⁻¹' maxLocus
        ((invFamily hn (n + 1)).inv (currentProductMarked W E T) .refl)
        (chronologicalDistinctDefect W E T) := by
  rw [chronologicalDistinctDefect_open hn hW hE hdense T hT U]
  exact maxLocus_preimage _
    (fun x hx => current_full_value_open hn hW hE hdense hd hr T hT U x hx) hne

/-- Omitting the entire dynamic maximum strictly lowers every full local
value; the comparison does not replace the true defect by a raw count. -/
theorem current_full_value_lt_of_maximum_trace_empty (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {d : ℕ} (hd : d + 1 ≤ n) (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T) (U : Opens X) {a : Y}
    (ha : a ∈ maxLocus ((invFamily hn (n + 1)).inv (currentProductMarked W E T) .refl)
      (chronologicalDistinctDefect W E T))
    (hempty : (Subtype.val : openPreimage T U → Y) ⁻¹' maxLocus
      ((invFamily hn (n + 1)).inv (currentProductMarked W E T) .refl)
      (chronologicalDistinctDefect W E T) = ∅)
    (x : openPreimage T U)
    (hx : x ∈ chronologicalDistinctDefect (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U T)) :
    (invFamily hn (n + 1)).inv
        (currentProductMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' W)
          (E.map ((Subtype.val : U → X) ⁻¹' ·)) (restrict U T)) .refl x <
      (invFamily hn (n + 1)).inv (currentProductMarked W E T) .refl a := by
  rw [chronologicalDistinctDefect_open hn hW hE hdense T hT U] at hx
  rw [current_full_value_open hn hW hE hdense hd hr T hT U x hx]
  apply lt_of_le_of_ne (ha.2 x.val hx)
  intro heq
  have hmax : x.val ∈ maxLocus
      ((invFamily hn (n + 1)).inv (currentProductMarked W E T) .refl)
      (chronologicalDistinctDefect W E T) :=
    ⟨hx, fun y hy => (ha.2 y hy).trans_eq heq.symm⟩
  have hmem : x ∈ (Subtype.val : openPreimage T U → Y) ⁻¹' maxLocus
      ((invFamily hn (n + 1)).inv (currentProductMarked W E T) .refl)
      (chronologicalDistinctDefect W E T) := hmax
  rw [hempty] at hmem
  exact hmem

end
end Hironaka.HironakaSharpActualDynamicMaximumOpen
