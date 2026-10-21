/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualRelativeSaturationOpenNaturality
/-! Entire true chronological marked records commute with actual opens.
Actual auxiliary/born lists and EACH indexed original member stay separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualChronologicalOpenNaturality
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualRelativeSaturationOpenNaturality HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalFirstBlowupOpenComparison
  RelativePrincipalizationSpan RestrictedIdealExtension MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen GermIdealPullbackCalculus IdealWeightPowers GermIdealOrder NormalCrossings
variable {n : ℕ} {X : CMfd.{u} n}

/-- WHOLE marked-record equality, not only carrier or germ-at-one-point equality. -/
theorem chronologicalMarked_open (hn : 0<n) (M : MarkedIdeal n X)
    (hw : M.IsWellFormed) (hm : M.d=0)
    (hnz : ∀ x∈M.N,DivisorExponentAlong.IsNonzeroAlongAt M.N M.ideal x)
    (hpr : ∀ x∈M.N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,M.ideal.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) M.N (·=f) x g) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate M.N M.E) T →
      ∀ U : Opens X,
        MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (chronologicalMarked M T)=
          chronologicalMarked (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)
  | _,.refl,_,U => rfl
  | _,.step T C π hπ,hT,U => by
    let A := chronologicalMarked M T
    let V := openPreimage T U
    let AU := chronologicalMarked (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)
    let r := firstBlowupOpenProjection hπ V
    obtain ⟨hwA,hnzA,hprA⟩ := chronologicalMarked_actual_geometry hn M hw hm hnz hpr T hT.1
    obtain ⟨hAN,hAE⟩ := chronologicalMarked_geometric_fields M T
    have hCN : C⊆A.N := by rw [hAN];exact hT.2.subset_N
    have hNC : HasNormalCrossings n C A.E := by rw [hAE];exact hT.2.2.2
    have hadm : A.IsAdmissibleCentre C := by
      refine ⟨hπ.1,?_,hNC⟩
      change C⊆cosupport n A.N A.ideal A.d
      rw [show A.d=0 from chronologicalMarked_zero_mark M hm T,
        cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwA.isCoherent hg)]
      exact hCN
    have hwP := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwA hadm hπ
    have hRecord := geoTransform_pullback_val hwA.isCoherent hπ hwP.isCoherent V (firstBlowupSourceOpen hπ V).isOpen
    have hIdeal := nextRelativeStrict_open hn hwA.isClosedSubmanifold_N hwA.isCoherent hnzA hprA hπ hCN V
    have hIH : MarkedIdeal.pullback (Subtype.val : V → _) A=AU :=
      chronologicalMarked_open hn M hw hm hnz hpr T hT.1 U
    change MarkedIdeal.pullback (Subtype.val : firstBlowupSourceOpen hπ V → _)
        (⟨(A.geoTransform C π).N,(A.geoTransform C π).E,nextRelativeStrict A.N A.ideal C π,0⟩ : MarkedIdeal n _)=
      (⟨(AU.geoTransform ((Subtype.val : V → _) ⁻¹' C) r).N,
        (AU.geoTransform ((Subtype.val : V → _) ⁻¹' C) r).E,
        nextRelativeStrict AU.N AU.ideal ((Subtype.val : V → _) ⁻¹' C) r,0⟩ : MarkedIdeal n _)
    rw [←hIH]
    exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      (congrArg MarkedIdeal.N hRecord).symm (congrArg MarkedIdeal.E hRecord).symm hIdeal rfl

/-- The independently defined restricted relative-member initial record, including its EMPTY auxiliary list. -/
theorem original_relative_member_open {W H : Set X}
    (hW : IsClosedSubmanifold n W) (hH : IsClosedSubmanifold n H) (U : Opens X) :
    MarkedIdeal.pullback (Subtype.val : U → X) (originalRelativeMemberMarked W H)=
      originalRelativeMemberMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) ((Subtype.val : U → X) ⁻¹' H) := by
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  have hRes := isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  apply GermIdeal.ext
  funext x g
  apply propext
  change (GermIdeal.pullback (m := n) (Subtype.val : U → X)
      (restrictOn n W (vanishingIdeal (n := n) H))).mem x g ↔
    (restrictOn n ((Subtype.val : U → X) ⁻¹' W)
      (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))).mem x g
  rw [mem_pullback_val_iff U hRes]
  have hdict := restrictOn_pullback_val_iff U (W := W) (x := x) (F := g) hI
  rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal] at hdict
  exact hdict.symm

/-- ONLY original geometry supplies the whole chronological record dictionary for EACH true original position. -/
theorem original_members_chronological_open (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (i : Fin E.length)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) (U : Opens X) :
    MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T)=
      chronologicalMarked (originalRelativeMemberMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) ((Subtype.val : U → X) ⁻¹' E.get i)) (restrict U T) := by
  obtain ⟨_hN,_hE,hm,hw,hnz,hpr⟩ := original_members_actual_finite_chronological_geometry
    hn hW hE hdense i (.refl : BlowupTower X X) trivial
  have h := chronologicalMarked_open hn (originalRelativeMemberMarked W (E.get i)) hw hm hnz hpr T hT U
  rw [original_relative_member_open hW (MonomialPart.isClosedSubmanifold_get hn hE i) U] at h
  exact h
end
end Hironaka.HironakaSharpActualChronologicalOpenNaturality
