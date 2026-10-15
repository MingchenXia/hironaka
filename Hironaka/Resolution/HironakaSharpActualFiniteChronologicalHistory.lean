/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualChronologicalStrictStep

/-! Real finite histories of iterated NEW-exceptional saturation. Whole ordered
geometry and every empty step are retained. Composite original RAW TOTAL with
ALL accumulated exceptionals stripped remains a separate OPEN comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFiniteChronologicalHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMemberProduct RelativePrincipalizationSpan RestrictedIdealExtension
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings DivisorExponentAlong GermIdealOrder
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual unit/zero-mark geometric template, independent of desired ideal histories. -/
def geometricTemplate (N : Set X) (E : List (Set X)) : MarkedIdeal n X :=
  ⟨N,E,IdealWeightPowers.unitIdeal n X,0⟩

/-- Literal chronological recursion: true old pullback then NEW-exceptional
all-power saturation. The actual geometric ordered list and empty steps remain. -/
def chronologicalMarked (M : MarkedIdeal n X) : {Y : CMfd.{u} n} → BlowupTower X Y → MarkedIdeal n Y
  | _, .refl => M
  | _, .step T C π _ =>
    let A := chronologicalMarked M T
    let P := A.geoTransform C π
    ⟨P.N,P.E,nextRelativeStrict A.N A.ideal C π,0⟩

/-- Genuine geometric fields agree at EVERY actual tower, without a desired
history premise; the ideal recursion cannot change the actual carrier/list. -/
theorem chronologicalMarked_geometric_fields (M : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (chronologicalMarked M T).N=(geoTransformAlong (geometricTemplate M.N M.E) T).N ∧
      (chronologicalMarked M T).E=(geoTransformAlong (geometricTemplate M.N M.E) T).E
  | _, .refl => ⟨rfl,rfl⟩
  | _, .step T C π _ => by
    obtain ⟨hN,hE⟩ := chronologicalMarked_geometric_fields M T
    constructor
    · change BlowupStrictSubmanifold.geoStrictTransform π C (chronologicalMarked M T).N =
        BlowupStrictSubmanifold.geoStrictTransform π C (geoTransformAlong (geometricTemplate M.N M.E) T).N
      rw [hN]
    · change (chronologicalMarked M T).E.map _ ++ [π ⁻¹' C] =
        (geoTransformAlong (geometricTemplate M.N M.E) T).E.map _ ++ [π ⁻¹' C]
      rw [hE]

theorem chronologicalMarked_zero_mark (M : MarkedIdeal n X) (hm : M.d=0) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),(chronologicalMarked M T).d=0
  | _, .refl => hm
  | _, .step _ _ _ _ => rfl

/-- Actual template geometry independently supplies every real next centre's
containment/ENTIRE prior-list NC before genuine chronological ideal induction. -/
theorem chronologicalMarked_actual_geometry (hn : 0 < n) (M : MarkedIdeal n X)
    (hw : M.IsWellFormed) (hm : M.d=0) (hnz : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x)
    (hpr : ∀ x ∈ M.N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,M.ideal.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) M.N (·=f) x g) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate M.N M.E) T →
      (chronologicalMarked M T).IsWellFormed ∧
      (∀ y ∈ (chronologicalMarked M T).N,IsNonzeroAlongAt (chronologicalMarked M T).N (chronologicalMarked M T).ideal y) ∧
      ∀ y ∈ (chronologicalMarked M T).N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ g,(chronologicalMarked M T).ideal.mem y g ↔ HolomorphicAt n g y ∧
          IsInSpanOnAt (n := n) (chronologicalMarked M T).N (·=f) y g
  | _, .refl, _ => ⟨hw,hnz,hpr⟩
  | _, .step T C π hπ, hT => by
    obtain ⟨hwA,hnzA,hprA⟩ := chronologicalMarked_actual_geometry hn M hw hm hnz hpr T hT.1
    let A := chronologicalMarked M T
    obtain ⟨hAN,hAE⟩ := chronologicalMarked_geometric_fields M T
    have hCN : C ⊆ A.N := by rw [hAN]; exact hT.2.subset_N
    have hNC : HasNormalCrossings n C A.E := by rw [hAE]; exact hT.2.2.2
    have hadm : A.IsAdmissibleCentre C := by
      refine ⟨hπ.1,?_,hNC⟩
      change C ⊆ cosupport n A.N A.ideal A.d
      rw [chronologicalMarked_zero_mark M hm T,
        cosupport_zero (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwA.isCoherent hg)]
      exact hCN
    have hwP := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwA hadm hπ
    obtain ⟨_hS,hcohS,hnzS,hprS,_hfactor⟩ := nextRelativeStrict_actual_geometry hn hwA.isClosedSubmanifold_N
      hwA.isCoherent hnzA hprA hπ hCN
    refine ⟨⟨hwP.isClosedSubmanifold_N,hcohS,hwP.isSNCDivisor,hwP.isTransverse⟩,hnzS,?_⟩
    intro y hy
    obtain ⟨f,hf,hgen⟩ := hprS y hy
    exact ⟨f,((hgen f).mp hf).1,hgen⟩

/-- TRUE initial relative member ideal, before any desired history dictionary. -/
def originalRelativeMemberMarked (W H : Set X) : MarkedIdeal n X :=
  ⟨W,[],restrictOn n W (vanishingIdeal (n := n) H),0⟩

/-- ONLY original SNC/density inputs give all actual chronological positions
on EVERY genuine finite geometry history, including literal empty steps. -/
theorem original_members_actual_finite_chronological_geometry (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    A.N=(geoTransformAlong (geometricTemplate W []) T).N ∧
      A.E=(geoTransformAlong (geometricTemplate W []) T).E ∧ A.d=0 ∧ A.IsWellFormed ∧
      (∀ y ∈ A.N,IsNonzeroAlongAt A.N A.ideal y) ∧
      ∀ y ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ g,A.ideal.mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) A.N (·=f) y g := by
  let M := originalRelativeMemberMarked W (E.get i)
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  have hres := isCoherent_restrictOn hI (VanishingIdealCoherent.isCoherent_vanishingIdeal hW)
  have hwM : M.IsWellFormed := ⟨hW,hres,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hnzM : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x := by
    intro x hx
    obtain ⟨g,hg,hfreq⟩ := originalMemberIdeal_isNonzeroAlongAt hE hdense (List.get_mem E i) hx
    exact ⟨g,le_restrictOn hI x g hg,hfreq⟩
  have hprM : ∀ x ∈ M.N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,M.ideal.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) M.N (·=f) x g := by
    intro x _hx
    obtain ⟨f,hf,hgen⟩ := HironakaSharpOriginalProductTraceOrder.exists_originalMember_principal hn hE (List.get_mem E i) x
    refine ⟨f,hf,?_⟩
    intro g
    exact and_congr Iff.rfl (restricted_span_iff_principal hf hgen g)
  obtain ⟨hN,hE'⟩ := chronologicalMarked_geometric_fields M T
  obtain ⟨hwA,hnzA,hprA⟩ := chronologicalMarked_actual_geometry hn M hwM rfl hnzM hprM T hT
  exact ⟨hN,hE',chronologicalMarked_zero_mark M rfl T,hwA,hnzA,hprA⟩

end
end Hironaka.HironakaSharpActualFiniteChronologicalHistory
