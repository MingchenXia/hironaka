/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalRestrictedDistinctDefectBlowup
import Hironaka.Resolution.HironakaCoherentTransformExtension

/-! Actual original member TOTAL traces on the SAME first sharp blowup and real
greatest-exceptional-factor geometry. Mark-zero whole ideal equality precedes
residual geometry. Arbitrary-colon saturation / chronological STRICT identity
and full modified history are not inferred. Complete source-first BP precedes. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalFirstMemberExceptionalFactor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpOriginalRestrictedDistinctDefectBlowup HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalMemberProduct
  HironakaCoherentTransformExtension MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder NormalCrossings RelativePrincipalizationSpan RestrictedIdealExtension
  MonomialPartAlong InvDomainCompanion DivisorExponentAlong IdealWeightPowers
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual literal record, before choosing any ideal transform or desired dictionary. -/
def memberZeroMarked (W H : Set X) : MarkedIdeal n X := ⟨W,[],vanishingIdeal (n := n) H,0⟩

/-- BOTH whole ideal directions: zero marking has true restricted TOTAL pullback. -/
theorem geoTransform_zeroMark_ideal_eq_restricted_total (M : MarkedIdeal n X) (hm : M.d=0)
    (C : Set X) (π : Y → X) :
    (M.geoTransform C π).ideal=restrictOn n (M.geoTransform C π).N (GermIdeal.pullback (m := n) π M.ideal) := by
  change RestrictedIdealQuotient.colonAlong n (M.geoTransform C π).N (GermIdeal.pullback (m := n) π M.ideal)
    (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d)=_
  rw [hm,idealPow]
  ext x g
  constructor
  · rintro ⟨_hg,hcolon⟩
    have h1 := hcolon (fun _ => 1) (holomorphicAt_const 1)
    simpa only [one_mul] using h1
  · intro hg
    exact ⟨hg.1,fun a ha => restrictOn_mul_left ha hg⟩

/-- Genuine actual per-original-position TOTAL marked record on the actual blowup carrier. -/
def memberTotalMarked (W H C : Set X) (π : Y → X) : MarkedIdeal n Y :=
  (memberZeroMarked W H).geoTransform C π

/-- True residual obtained by actual intrinsic greatest exceptional factor division;
no arbitrary-colon saturation identity is asserted by this definition. -/
def memberExceptionalResidual (W H C : Set X) (π : Y → X) : GermIdeal n Y :=
  let P := memberTotalMarked W H C π
  nonmonomialPartAlong n P.N P.ideal P.E

private theorem actual_member_total_geometry (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hC : IsClosedSubmanifold n C) (hCW : C ⊆ W) (i : Fin E.length) :
    (memberTotalMarked W (E.get i) C π).IsWellFormed ∧
      ∀ y ∈ (memberTotalMarked W (E.get i) C π).N,
        IsNonzeroAlongAt (memberTotalMarked W (E.get i) C π).N
          (memberTotalMarked W (E.get i) C π).ideal y := by
  let M := memberZeroMarked W (E.get i)
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  have hw : M.IsWellFormed := ⟨hW,hI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hadm : M.IsAdmissibleCentre C := by
    refine ⟨hC,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hC⟩
    change C ⊆ cosupport n W (vanishingIdeal (n := n) (E.get i)) 0
    rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
    exact hCW
  exact ⟨GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hadm hπ,
    isNonzeroAlongAt_geoTransform_without_admissibility M hW hI hπ hCW
      (fun _ hy => originalMemberIdeal_isNonzeroAlongAt hE hdense (List.get_mem E i) hy)⟩

/-- Original-only actual SAME first blowup supplies genuine whole per-member total
and greatest-exceptional-factor geometry BEFORE relative strict-saturation identification. -/
theorem exists_actual_original_first_member_exceptional_factor (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1 ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X),IsBlowupAlong n C π ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.invFamily hn (n+1)).inv
        (originalMemberProductMarked W E 1) (.refl : BlowupTower X X)) (originalDistinctDefectPhase W E) ∧
      ∀ i : Fin E.length,
        let P := memberTotalMarked W (E.get i) C π
        let J := memberExceptionalResidual W (E.get i) C π
        P.IsWellFormed ∧ P.ideal=restrictOn n P.N (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (E.get i))) ∧
        (∀ y ∈ P.N,IsNonzeroAlongAt P.N P.ideal y) ∧ J.IsCoherent ∧
        (∀ y ∈ P.N,IsNonzeroAlongAt P.N J y) ∧
        (∀ y ∈ P.N,∀ g,P.ideal.mem y g → ∃ m c,HolomorphicAt n m y ∧
          (monomialPartAlong n P.N P.ideal P.E).mem y m ∧
          (∀ a : Fin P.E.length,y ∈ P.E.get a →
            (idealPow (vanishingIdeal (n := n) (P.E.get a)) (divExpAlong n P.N P.ideal (P.E.get a) y)).mem y m) ∧
          J.mem y c ∧ ∀ᶠ z in 𝓝 y,z ∈ P.N → g z=m z*c z) ∧
        ∀ y ∈ P.N,∀ a : Fin P.E.length,y ∈ P.E.get a → ∃ g,J.mem y g ∧
          ¬IsInSpanOnAt (n := n) P.N ((vanishingIdeal (n := n) (P.E.get a)).mem y) y g := by
  obtain ⟨C,Y,π,_hCne,hCadm,_hCZ,_hbad,hboundary,_hgood,_hemb,hπ,_hproper,_hhol,_hiso,_hstrict,_hSNC,hCeq⟩ :=
    exists_actual_original_restrictedDistinctDefect_blowup hn hW hE hd hreg hdense hcompact hne
  refine ⟨C,Y,π,hπ,hCeq,?_⟩
  intro i
  dsimp only
  let P := memberTotalMarked W (E.get i) C π
  obtain ⟨hw,hnz⟩ := actual_member_total_geometry hn hW hE hdense hπ hCadm.1 (fun _ hx => (hboundary hx).1) i
  have hJ := isCoherent_nonmonomialPartAlong hn hw.isClosedSubmanifold_N hw.isSNCDivisor
    hw.isTransverse hw.isCoherent hnz
  refine ⟨hw,geoTransform_zeroMark_ideal_eq_restricted_total (memberZeroMarked W (E.get i)) rfl C π,
    hnz,hJ,?_,?_,?_⟩
  · intro y hy
    exact isNonzeroAlongAt_nonmonomialPartAlong hn hw.isClosedSubmanifold_N hw.isSNCDivisor hw.isTransverse hw.isCoherent hnz hy
  · intro y hy g hg
    exact exists_mem_nonmonomialPartAlong_mul hn hw.isClosedSubmanifold_N hw.isSNCDivisor hw.isTransverse hw.isCoherent hnz hy hg
  · intro y hy a ha
    exact exists_mem_nonmonomialPartAlong_not hn hw.isClosedSubmanifold_N hw.isSNCDivisor hw.isTransverse hw.isCoherent hnz hy ha

end
end Hironaka.HironakaSharpOriginalFirstMemberExceptionalFactor
