/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveFirstDefectErasure

/-! Genuine full ORIGINAL ambient SNC family on SAME dimension-one original
test histories. No carrier transversality or ambient-strict trace certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveFullAmbientBoundary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveFirstDefectErasure HironakaSharpActualCurveWholeDefectCentre
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalMemberProductDomain HironakaOneDimensionalCanonicalSuperlevels
  RelativePrincipalizationSpan NormalCrossings SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder IdealWeightPowers
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual0dim positive cosupports supply EACH real centre's NC with ANY
independent ambient SNC family BEFORE genuine same-map template admissibility. -/
theorem actual_domain_one_history_ambient_template (M : MarkedIdeal n X) (hM : IsInvDomain 1 M)
    (B : List (Set X)) (hB : IsSNCDivisor n B) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower M T →
      (geoTransformAlong (geometricTemplate (univ : Set X) B) T).N=univ ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) B) T ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) B) T).E
  | _, .refl, _ => ⟨rfl,trivial,hB⟩
  | _, .step T C π hπ, hT => by
    obtain ⟨hNold,hOld,hFold⟩ := actual_domain_one_history_ambient_template M hM B hB T hT.1
    let A := geometricTemplate (univ : Set X) B
    have hwA : A.IsWellFormed :=
      ⟨⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
        isCoherent_unitIdeal,hB,isTransverse_univ_of_isSNCDivisor hB⟩
    have hwOld := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwA T hOld
    have hCur := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT.1
    have hCos := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along
      hCur.isWellFormed.isCoherent hCur.isWellFormed.isClosedSubmanifold_N hCur.one_le_d
    have hDim := dimLE_cosupport_of_isInvDomain hCur
    have hNC := hasNormalCrossings_subset_of_analytic_dimLE_zero hCos hDim hT.2.2.1 hFold
    have hAdm : (geoTransformAlong A T).IsAdmissibleCentre C := by
      refine ⟨hT.2.1,?_,hNC⟩
      change C ⊆ cosupport n _ _ (geoTransformAlong A T).d
      rw [d_geoTransformAlong]
      change C ⊆ cosupport n _ _ 0
      rw [cosupport_zero (fun _ _ hg =>
        RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwOld.isCoherent hg),hNold]
      exact subset_univ C
    have hNew : IsGeoTestTower A (.step T C π hπ) := ⟨hOld,hAdm⟩
    have hwNew := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwA (.step T C π hπ) hNew
    refine ⟨?_,hNew,hwNew.isSNCDivisor⟩
    change BlowupStrictSubmanifold.geoStrictTransform π C (geoTransformAlong A T).N=univ
    rw [hNold,geoStrictTransform_univ hπ]

/-- ONLY original curve geometry internally gives tight original domain1,
then tracks the literal WHOLE ORIGINAL ambient boundary on the SAME prefix. -/
theorem original_curve_history_full_ambient_boundary (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    (geoTransformAlong (geometricTemplate (univ : Set X) E) T).N=univ ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E := by
  have hInit : IsInvDomain 1 (originalMemberProductMarked W E 1) :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  exact actual_domain_one_history_ambient_template _ hInit E hE T hT

/-- The real FIRST-Z-erasing projection retains full ORIGINAL ambient strict
boundary plus all real exceptional positions on the SAME final manifold. -/
theorem exists_original_curve_erasing_step_full_ambient_boundary (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    ∃ (Z : CMfd.{u} n) (π : Z → Y)
      (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E T) π),
      IsProperMap π ∧ ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (chronologicalDistinctDefect W E T)ᶜ ∧
      IsGeoTestTower (originalMemberProductMarked W E 1)
        (.step T (chronologicalDistinctDefect W E T) π hπ) ∧
      IsInvDomain 1 (geoTransformAlong (originalMemberProductMarked W E 1)
        (.step T (chronologicalDistinctDefect W E T) π hπ)) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E)
        (.step T (chronologicalDistinctDefect W E T) π hπ) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) E)
        (.step T (chronologicalDistinctDefect W E T) π hπ)).E ∧
      chronologicalDistinctDefect W E (.step T (chronologicalDistinctDefect W E T) π hπ)=∅ := by
  obtain ⟨Z,π,hπ,hproper,hholo,hiso,hnew,hdom,_hSNC,hZempty⟩ :=
    exists_original_curve_first_defect_erasing_step hn hW hE hdense hr T hT
  obtain ⟨_hN,hAmbient,hWholeSNC⟩ := original_curve_history_full_ambient_boundary hn hW hE hdense hr
    (.step T (chronologicalDistinctDefect W E T) π hπ) hnew
  exact ⟨Z,π,hπ,hproper,hholo,hiso,hnew,hdom,hAmbient,hWholeSNC,hZempty⟩

end
end Hironaka.HironakaSharpActualCurveFullAmbientBoundary
