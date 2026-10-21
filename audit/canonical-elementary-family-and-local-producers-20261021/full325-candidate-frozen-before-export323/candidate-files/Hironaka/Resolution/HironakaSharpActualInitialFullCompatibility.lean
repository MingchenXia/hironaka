/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualDynamicMaximumOpen
import Hironaka.Resolution.HironakaSharpActualOriginalDynamicStep
import Hironaka.Resolution.HironakaSharpOriginalRestrictedDistinctDefectBlowup

/-!
# Actual initial sharp maxima and original normal-crossings preservation

The whole actual germ quotient and normalized product are compared with their
original source objects before the full invariant or centre is compared. This
constructs an actual first sharp blowup in every positive carrier dimension.
General full-history decrease and terminal sharp resolution are not inferred.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaSharpActualInitialFullCompatibility
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualDynamicDistinctCentre
  HironakaSharpActualDynamicMaximumOpen HironakaSharpActualCompositeProductResidual
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalRestrictedDistinctDefectCentre HironakaSharpOriginalRestrictedDistinctDefectBlowup
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  NormalCrossings GermIdealOrder DivisorExponentAlong CanonicalCentres ResolutionDriver
  MarkedIdealOperationsAlong IdealWeightPowers RestrictedIdealWeight

open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

/-- Equality of the entire actual initial ideal predicates is exactly equality
of the source trace spans on every holomorphic germ. -/
theorem initial_actual_germ_relation_iff_source_trace (W : Set X) (E : List (Set X))
    (x : X) (i j : Fin E.length) :
    (actualIdealGermSetoid
      (fun a : Fin E.length => (originalRelativeMemberMarked W (E.get a)).ideal) x).r i j ↔
      (traceGermSetoid (n := n) W E x).r i j := by
  constructor
  · intro h g hg
    exact ⟨fun hs => ((h g).mp ⟨hg, hs⟩).2,
      fun hs => ((h g).mpr ⟨hg, hs⟩).2⟩
  · intro h g
    change (HolomorphicAt n g x ∧ traceSpan (n := n) W (E.get i) x g) ↔
      (HolomorphicAt n g x ∧ traceSpan (n := n) W (E.get j) x g)
    exact and_congr_right fun hg => h g hg

/-- The true finite images of proper germ classes agree, without replacing
either quotient by an indexed incidence count. -/
theorem initial_actual_distinct_count_eq_source (W : Set X) (E : List (Set X)) (x : X) :
    actualDistinctProperCount
      (fun a : Fin E.length => (originalRelativeMemberMarked W (E.get a)).ideal) x =
      distinctProperTraceGermCount (n := n) W E x := by
  let F := fun a : Fin E.length => (originalRelativeMemberMarked W (E.get a)).ideal
  have hRel : ∀ i j, (actualIdealGermSetoid F x).r i j ↔
      (traceGermSetoid (n := n) W E x).r i j :=
    initial_actual_germ_relation_iff_source_trace W E x
  let eQ := Quotient.congr (Equiv.refl (Fin E.length)) hRel
  have hProper : actualProperPositions F x = properTraceMembers (n := n) W E x := by
    ext i
    simp only [actualProperPositions, properTraceMembers, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change (¬(HolomorphicAt n (1 : X → ℂ) x ∧ traceSpan (n := n) W (E.get i) x 1)) ↔
      ¬traceSpan (n := n) W (E.get i) x 1
    constructor
    · intro h hs
      exact h ⟨holomorphicAt_const 1, hs⟩
    · intro h hs
      exact h hs.2
  have hmk : Quotient.mk (traceGermSetoid (n := n) W E x) =
      eQ ∘ Quotient.mk (actualIdealGermSetoid F x) := by
    funext i
    exact (Quotient.congr_mk (Equiv.refl (Fin E.length)) hRel i).symm
  change ((actualProperPositions F x).image (Quotient.mk (actualIdealGermSetoid F x))).card =
    ((properTraceMembers (n := n) W E x).image
      (Quotient.mk (traceGermSetoid (n := n) W E x))).card
  rw [← hProper, hmk, ← Finset.image_image, Finset.card_image_of_injective _ eQ.injective]

/-- The entire initial chronological product is the actual carrier restriction
of the original ambient ordered product, retaining all original positions. -/
theorem initial_actual_product_eq_restrictOn_source (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) :
    chronologicalMemberProduct W E (.refl : BlowupTower X X) =
      restrictOn n W (originalMemberProduct (n := n) E) := by
  have hInit := relative_original_product_eq_restrictOn hW
    (E.map (vanishingIdeal (n := n))) (by
      intro I hI
      obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hI
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
      exact VanishingIdealCoherent.isCoherent_vanishingIdeal
        (MonomialPart.isClosedSubmanifold_get hn hE i))
  simpa only [originalMemberProduct, chronologicalMemberProduct, chronologicalMemberFamily,
    chronologicalMarked, originalRelativeMemberMarked, geoTransformAlong, geometricTemplate,
    List.map_map, Function.comp_def] using hInit

/-- The independently defined source and actual initial product records are
equivalent in the entire restricted ideal, with the same mark and empty boundary. -/
theorem source_product_restrictEquiv_actual_initial (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) :
    MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv
      (originalMemberProductMarked W E 1)
      (currentProductMarked W E (.refl : BlowupTower X X)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · change RestrictLe W (originalMemberProduct (n := n) E)
      (chronologicalMemberProduct W E (.refl : BlowupTower X X))
    rw [initial_actual_product_eq_restrictOn_source hn hW hE]
    exact restrictLe_self_restrictOn (isCoherent_originalMemberProduct hn hE)
  · change RestrictLe W (chronologicalMemberProduct W E (.refl : BlowupTower X X))
      (originalMemberProduct (n := n) E)
    rw [initial_actual_product_eq_restrictOn_source hn hW hE]
    exact restrictLe_restrictOn

/-- The literal actual initial defect equals the original FIRST defect in
every carrier dimension, with no curve-order bound. -/
theorem initial_actual_defect_eq_source_first (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) :
    chronologicalDistinctDefect W E (.refl : BlowupTower X X) = originalDistinctDefectPhase W E := by
  ext x
  by_cases hx : x ∈ W
  · have hOrder := ordinaryTraceOrder_restrictOn_eq hW (isCoherent_originalMemberProduct hn hE)
      (fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy) hx
    have hProduct := chronological_product_eq_actual_family_product W E (.refl : BlowupTower X X)
    change (x ∈ W ∧ actualDistinctProperCount
      (fun i : Fin E.length => (originalRelativeMemberMarked W (E.get i)).ideal) x <
        ordinaryTraceOrder W _ x) ↔
      (x ∈ W ∧ distinctProperTraceGermCount (n := n) W E x <
        ordinaryTraceOrder W (originalMemberProduct (n := n) E) x)
    rw [initial_actual_distinct_count_eq_source, ← hProduct,
      initial_actual_product_eq_restrictOn_source hn hW hE, hOrder]
  · exact ⟨fun h => (hx h.1).elim, fun h => (hx h.1).elim⟩

/-- Actual initial dynamic centres belong to the genuine original sharp bad
locus and avoid all original normal-crossings points in every dimension. -/
theorem initial_actual_defect_subset_sharp_bad (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) :
    chronologicalDistinctDefect W E (.refl : BlowupTower X X) ⊆
      originalSharpBadLocus (n := n) W E := by
  rw [initial_actual_defect_eq_source_first hn hW hE hdense]
  exact originalDistinctDefectPhase_subset_sharpBad hn hW hE hdense

/-- The full invariant, not merely its first coordinate, agrees on the same
literal initial defect after the actual restricted-equivalence comparison. -/
theorem source_full_value_eq_actual_initial_on_first_defect (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {d : ℕ} (hd : d + 1 ≤ n) (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1))
    {x : X} (hx : x ∈ originalDistinctDefectPhase W E) :
    (invFamily hn (n + 1)).inv (originalMemberProductMarked W E 1) .refl x =
      (invFamily hn (n + 1)).inv (currentProductMarked W E (.refl : BlowupTower X X)) .refl x := by
  have hb := originalMemberProductMarked_isInvDomain hn hW hE hd hr hdense (q := 1) le_rfl
  have hSource : IsInvDomain (n + 1) (originalMemberProductMarked W E 1) :=
    ⟨hb.isWellFormed, fun y hy => by
      obtain ⟨j, hj, hjreg⟩ := hb.dimLE y hy
      exact ⟨j, hj.trans (Nat.le_succ n), hjreg⟩, hb.one_le_d, hb.isNonzeroAlongAt⟩
  have hActual := currentProductMarked_isInvDomain_of_pure hn hW hE hdense hd hr
    (.refl : BlowupTower X X) trivial
  have hCos : x ∈ (originalMemberProductMarked W E 1).cosupp := by
    apply (ordinaryTraceOrder_cosupport_iff hW hb.isWellFormed.isCoherent
      hb.isNonzeroAlongAt hx.1 1).mpr
    have hlt := hx.2
    change 1 ≤ ordinaryTraceOrder W (originalMemberProduct (n := n) E) x
    omega
  exact (invFamily hn (n + 1)).isInvValue.representative _ _ hSource hActual
    (source_product_restrictEquiv_actual_initial hn hW hE) .refl trivial x hCos

/-- The whole true dynamic maximum equals the original source maximum, with
no maximum-attainment assumption or compactness. -/
theorem initial_actual_dynamic_maximum_eq_source (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {d : ℕ} (hd : d + 1 ≤ n) (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1)) :
    maxLocus ((invFamily hn (n + 1)).inv
      (currentProductMarked W E (.refl : BlowupTower X X)) .refl)
      (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) =
      maxLocus ((invFamily hn (n + 1)).inv (originalMemberProductMarked W E 1) .refl)
        (originalDistinctDefectPhase W E) := by
  rw [initial_actual_defect_eq_source_first hn hW hE hdense]
  have hv := fun x hx => source_full_value_eq_actual_initial_on_first_defect
    hn hW hE hdense hd hr (x := x) hx
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, fun y hy => ?_⟩
    rw [hv y hy, hv x hx]
    exact hmax y hy
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, fun y hy => ?_⟩
    rw [← hv y hy, ← hv x hx]
    exact hmax y hy

/-- Original geometry produces the SAME actual initial dynamic maximum
blowup, with all original boundary admissibility and whole-good preservation. -/
theorem exists_actual_initial_dynamic_sharp_blowup (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (hK : IsCompact W)
    {d : ℕ} (hd : d + 1 ≤ n) (hr : ∀ x ∈ W, RegularAtDim (n := n) W x (d + 1))
    (hne : (chronologicalDistinctDefect W E (.refl : BlowupTower X X)).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X), C.Nonempty ∧
      (originalMemberProductMarked W E 1).IsAdmissibleCentre C ∧
      (currentProductMarked W E (.refl : BlowupTower X X)).IsAdmissibleCentre C ∧
      C ⊆ chronologicalDistinctDefect W E (.refl : BlowupTower X X) ∧
      C ⊆ originalSharpBadLocus (n := n) W E ∧
      (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (originalGoodLocus (n := n) W E) ∧
      IsClosedSubmanifold n (strictTransform n π W) ∧
      IsSNCDivisor n (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      C = maxLocus ((invFamily hn (n + 1)).inv
        (currentProductMarked W E (.refl : BlowupTower X X)) .refl)
        (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) := by
  have hZ := initial_actual_defect_eq_source_first hn hW hE hdense
  have hneSource : (originalDistinctDefectPhase W E).Nonempty := hZ ▸ hne
  obtain ⟨C, Y, π, hCne, hAdm, hCZ, hBad, _hBoundary, _hDis, hEmb, hπ,
    hProper, hHolo, hIso, hSmooth, hSNC, hMax⟩ :=
    exists_actual_original_restrictedDistinctDefect_blowup hn hW hE hd hr hdense hK hneSource
  refine ⟨C, Y, π, hCne, hAdm,
    (source_product_restrictEquiv_actual_initial hn hW hE).isAdmissibleCentre_iff.mp hAdm,
    ?_, hBad, hEmb, hπ, hProper, hHolo, hIso, hSmooth, hSNC, ?_⟩
  · rw [hZ]
    exact hCZ
  · exact hMax.trans (initial_actual_dynamic_maximum_eq_source hn hW hE hdense hd hr).symm

end
end Hironaka.HironakaSharpActualInitialFullCompatibility
