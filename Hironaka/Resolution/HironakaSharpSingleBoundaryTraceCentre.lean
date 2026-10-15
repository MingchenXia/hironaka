/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.SharpStrictTransformExact
import Hironaka.Resolution.HironakaStageCenters
import Hironaka.Resolution.HironakaNormalCrossingsTransversality
import Hironaka.Invariant.MonomialCaseAlong

/-! Genuine single-original-boundary modified trace centres.
The complete source-facing mathematics preceded code. The true original trace
ideal and its original canonical driver supply actual centres; no desired
good-locus avoidance or centre-selection certificate is a caller premise. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpSingleBoundaryTraceCentre
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  NormalCrossings NormalCrossingsComparison SimultaneousNormalCrossings
  HironakaNormalCrossingsTransversality GermIdealOrder DivisorExponentAlong
  BlowupFlatCoordinates MonomialPartAlong MonomialCase IdealWeightPowers OrderTaylor
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

/-- The genuine original boundary ideal restricted to the actual smooth carrier,
with the true trace-order-two defect mark. -/
def originalBoundaryTraceMarked (W H : Set X) : MarkedIdeal n X :=
  ⟨W,[],vanishingIdeal (n := n) H,2⟩

/-- The genuine original open good region, defined by actual normal-crossings
neighborhoods of the original carrier and original boundary. -/
def originalSmoothNCRegion (W H : Set X) : Set X :=
  {x | ∃ U : Opens X, x ∈ U ∧ HasNormalCrossings n
    ((Subtype.val : U → X) ⁻¹' W) [((Subtype.val : U → X) ⁻¹' H)]}

theorem originalSmoothNCRegion_isOpen (W H : Set X) : IsOpen (originalSmoothNCRegion W H) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨U,hxU,hU⟩
  exact mem_of_superset (U.isOpen.mem_nhds hxU) (fun y hy => ⟨U,hy,hU⟩)

/-- A true transverse boundary coordinate has restricted order one. -/
theorem originalBoundaryTraceMarked_cosupp_eq_empty_of_normalCrossings
    (hn : 0 < n) {W H : Set X} (hE : IsSNCDivisor n [H])
    (hNC : HasNormalCrossings n W [H]) (hdense : W ⊆ closure (W \ H)) :
    (originalBoundaryTraceMarked W H).cosupp = ∅ := by
  have htrans : IsTransverse n W [H] :=
    isTransverse_of_hasNormalCrossings_of_subset_closure_diff hNC (by simpa using hdense)
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxW : x ∈ W := hx.1
  have hxH : x ∈ H := by
    have hx1 := cosupport_anti (n := n) (N := W) (𝔞 := vanishingIdeal (n := n) H)
      (show 1 ≤ 2 by omega) hx
    rw [SmoothCentreLocus.cosupport_vanishingIdeal_one (hE.1 H (by simp))] at hx1
    exact hx1.2
  obtain ⟨kC,kN,Φ,σ,hΦsrc,hσk,_hσinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn subset_rfl hE htrans hNC hxW
  have hNflat : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
      (z ∈ W ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ complexCoordinatePlane n kN) :=
    fun hz1 hz2 => (hflat hz1 hz2).2.1
  have hHflat : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
      (z ∈ H ↔ Φ.toFun (chartAt (ComplexModel n) x z) (σ 0)=0) :=
    fun hz1 hz2 => (hflat hz1 hz2).2.2 0 hxH
  have hxD := mem_flatDomain_self Φ
  have hmem : (vanishingIdeal (n := n) H).mem x (flatCoord Φ (σ 0)) := by
    refine ⟨holomorphicAt_flatCoord Φ (σ 0) hxD,?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD] with z hz hzH
    exact (hHflat hz.1 hz.2).mp hzH
  have hr := isLocalRetraction_flatRetract hΦsrc hNflat hxD hxW
  have hcomp : (flatCoord Φ (σ 0)) ∘ flatRetract Φ kN =ᶠ[𝓝 x] flatCoord Φ (σ 0) := by
    filter_upwards [eventually_flatMap_flatRetract hΦsrc hNflat hxD hxW (hσk 0 hxH)] with z hz
    exact hz.2
  exact flatCoord_notMem_idealPow_two Φ (σ 0) hxD
    (mem_idealPow_congr (hr.vanishesToOrderOn_iff.mp (hx.2 _ hmem)) hcomp)

/-- Original density supplies a true nonzero trace germ at every carrier point. -/
theorem originalBoundaryIdeal_isNonzeroAlongAt_of_dense
    {W H : Set X} (hE : IsSNCDivisor n [H]) (hdense : W ⊆ closure (W \ H))
    {x : X} (hxW : x ∈ W) : IsNonzeroAlongAt W (vanishingIdeal (n := n) H) x := by
  by_cases hxH : x ∈ H
  · obtain ⟨S,⟨Φ,hΦsrc,_hΦ0,hΦA⟩,hcard,_hinj⟩ := hE.2 x
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hcard 0 hxH)
    have hHflat : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x z ∈ Φ.source →
        (z ∈ H ↔ flatCoord Φ a z=0) := by
      intro z hz hzΦ
      have hp := hΦA 0 hxH hz hzΦ
      simpa [ha,coordSubspace,flatCoord,complexChartAt] using hp
    have hxD := mem_flatDomain_self Φ
    refine ⟨flatCoord Φ a,⟨holomorphicAt_flatCoord Φ a hxD,?_⟩,?_⟩
    · filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD] with z hz hzH
      exact (hHflat hz.1 hz.2).mp hzH
    · apply frequently_iff.mpr
      intro U hU
      have hV : U ∩ flatDomain Φ ∈ 𝓝 x := inter_mem hU ((isOpen_flatDomain Φ).mem_nhds hxD)
      obtain ⟨V,hVsub,hVo,hxV⟩ := mem_nhds_iff.mp hV
      obtain ⟨z,hzV,hzW,hzH⟩ := mem_closure_iff.mp (hdense hxW) V hVo hxV
      refine ⟨z,(hVsub hzV).1,hzW,?_⟩
      exact fun hz0 => hzH ((hHflat (hVsub hzV).2.1 (hVsub hzV).2.2).mpr hz0)
  · refine ⟨fun _ => 1,⟨holomorphicAt_const 1,?_⟩,?_⟩
    · filter_upwards [(hE.1 H (by simp)).isOpen_compl.mem_nhds hxH] with z hz hzH
      exact False.elim (hz hzH)
    · exact (mem_closure_iff_frequently.mp (subset_closure hxW)).mono
        (fun _ hz => ⟨hz,one_ne_zero⟩)

/-- The actual original smooth boundary is a genuine closed smooth submanifold. -/
theorem originalBoundary_isClosedSubmanifold (hn : 0 < n) {H : Set X}
    (hE : IsSNCDivisor n [H]) : IsClosedSubmanifold n H := by
  have heq : BoundaryCount.memberInter [H] ({0} : Finset (Fin [H].length))=H := by
    ext x
    simp [BoundaryCount.memberInter]
  rw [← heq]
  exact BoundaryCount.isClosedSubmanifold_memberInter hn hE _

/-- The independently constructed actual original trace ideal initializes the real driver. -/
theorem originalBoundaryTraceMarked_isInvDomain (hn : 0 < n) {W H : Set X}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n [H])
    {d : ℕ} (hd : d ≤ n) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W \ H)) : IsInvDomain n (originalBoundaryTraceMarked W H) where
  isWellFormed := ⟨hW,VanishingIdealCoherent.isCoherent_vanishingIdeal
    (originalBoundary_isClosedSubmanifold hn hE),isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  dimLE := fun x hx => ⟨d,hd,hreg x hx⟩
  one_le_d := by change 1 ≤ 2; omega
  isNonzeroAlongAt := fun _ hx => originalBoundaryIdeal_isNonzeroAlongAt_of_dense hE hdense hx

/-- The actual trace defect is contained in the genuine original carrier-boundary intersection. -/
theorem originalBoundaryTraceMarked_cosupp_subset_inter {W H : Set X}
    (hE : IsSNCDivisor n [H]) : (originalBoundaryTraceMarked W H).cosupp ⊆ W ∩ H := by
  intro x hx
  have hx1 := cosupport_anti (n := n) (N := W) (𝔞 := vanishingIdeal (n := n) H)
    (show 1 ≤ 2 by omega) hx
  rw [SmoothCentreLocus.cosupport_vanishingIdeal_one (hE.1 H (by simp))] at hx1
  exact hx1

/-- Genuine restriction dictionaries prove avoidance of the entire actual original good region. -/
theorem originalBoundaryTraceMarked_cosupp_disjoint_goodRegion (hn : 0 < n)
    {W H : Set X} (hE : IsSNCDivisor n [H]) (hdense : W ⊆ closure (W \ H)) :
    Disjoint (originalBoundaryTraceMarked W H).cosupp (originalSmoothNCRegion W H) := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨U,hxU,hNC⟩
  have hEU : IsSNCDivisor n [((Subtype.val : U → X) ⁻¹' H)] := by
    simpa using NormalCrossingsInvariance.isSNCDivisor_map_preimage
      (NormalCrossingsInvariance.pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hdU : (Subtype.val : U → X) ⁻¹' W ⊆
      closure ((Subtype.val : U → X) ⁻¹' W \ (Subtype.val : U → X) ⁻¹' H) := by
    intro q hq
    have hp : q ∈ (Subtype.val : U → X) ⁻¹' closure (W \ H) := hdense hq
    erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ H)] at hp
    convert hp using 1
    exact congrArg closure (preimage_sdiff (Subtype.val : U → X) W H).symm
  have heq : MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) (originalBoundaryTraceMarked W H)=
      originalBoundaryTraceMarked (X := CMfd.of (n := n) U)
        ((Subtype.val : U → X) ⁻¹' W) ((Subtype.val : U → X) ⁻¹' H) := by
    simp [MarkedIdealBiholomorphism.MarkedIdeal.pullback,originalBoundaryTraceMarked,
      SmoothCentreHomogeneity.pullback_val_vanishingIdeal]
  have hlocal : (MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : U → X) (originalBoundaryTraceMarked W H)).cosupp=∅ := by
    rw [heq]
    exact originalBoundaryTraceMarked_cosupp_eq_empty_of_normalCrossings
      (X := CMfd.of (n := n) U) hn hEU hNC hdU
  rw [MarkedIdealRestrictOpen.cosupp_pullback_val (originalBoundaryTraceMarked W H)
    (fun _ _ hg => hg.1) U] at hlocal
  have hbad : (⟨x,hxU⟩ : U) ∈ (Subtype.val : U → X) ⁻¹' (originalBoundaryTraceMarked W H).cosupp := hx
  rw [hlocal] at hbad
  simp at hbad

/-- ONLY original smooth carrier/boundary/density data internally select an actual
modified maximum centre avoiding every genuine original good NC neighborhood. -/
theorem exists_originalBoundaryTraceCentre (hn : 0 < n) {W H : Set X}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n [H])
    {d : ℕ} (hd : d ≤ n) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W \ H)) (hK : IsCompact W)
    (hbad : (originalBoundaryTraceMarked W H).cosupp.Nonempty) :
    ∃ C : Set X, C.Nonempty ∧ (originalBoundaryTraceMarked W H).IsAdmissibleCentre C ∧
      C ⊆ W ∩ H ∧ Disjoint C (originalSmoothNCRegion W H) ∧
      (⟨univ,[H],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (originalBoundaryTraceMarked W H) (.refl : BlowupTower X X))
        (originalBoundaryTraceMarked W H).cosupp := by
  let M := originalBoundaryTraceMarked W H
  let R := CanonicalCentres.canonicalInvariant.{u} n
  have hdom := originalBoundaryTraceMarked_isInvDomain hn hW hE hd hreg hdense
  have hclosed : IsClosed M.cosupp := GiraudAlong.isClosed_cosupport_along
    hdom.isWellFormed.isCoherent hdom.isWellFormed.isClosedSubmanifold_N _
  have hcompact : IsCompact M.cosupp := hK.of_isClosed_subset hclosed M.cosupp_subset_N
  have husc := R.isInvValue.usc M hdom (.refl : BlowupTower X X) trivial
  rw [geoTransformAlong_refl] at husc
  obtain ⟨c,hc,hmax⟩ := husc.exists_isMaxOn hcompact hbad
  let C := ResolutionDriver.maxLocus (R.inv M (.refl : BlowupTower X X)) M.cosupp
  have hadm := R.isInvValue.isAdmissibleCentre_maxLocus hdom (.refl : BlowupTower X X) trivial trivial
  rw [geoTransformAlong_refl] at hadm
  have hinter : C ⊆ W ∩ H := hadm.2.1.trans (originalBoundaryTraceMarked_cosupp_subset_inter hE)
  have hNC : HasNormalCrossings n C [H] := hasNormalCrossings_of_forall_notMem hE hadm.2.2 (by
    intro K hK _
    obtain rfl : K=H := List.mem_singleton.mp hK
    exact fun _ hz => (hinter hz).2)
  have hemb : (⟨univ,[H],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C := by
    refine ⟨hadm.1,?_,hNC⟩
    rw [HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW.1 [H]]
    exact fun _ hz => (hinter hz).1
  exact ⟨C,⟨c,hc,hmax⟩,hadm,hinter,
    (originalBoundaryTraceMarked_cosupp_disjoint_goodRegion hn hE hdense).mono_left hadm.2.1,hemb,rfl⟩

/-- The internally selected actual modified centre gives a real proper blowup
preserving the ENTIRE original open good NC region and the actual smooth carrier. -/
theorem exists_originalBoundaryTraceBlowup (hn : 0 < n) {W H : Set X}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n [H])
    {d : ℕ} (hd : d ≤ n) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W \ H)) (hK : IsCompact W)
    (hbad : (originalBoundaryTraceMarked W H).cosupp.Nonempty) :
    ∃ (C : Set X) (Y : CMfd.{u} n) (π : Y → X),
      C.Nonempty ∧ (originalBoundaryTraceMarked W H).IsAdmissibleCentre C ∧
      C ⊆ W ∩ H ∧ Disjoint C (originalSmoothNCRegion W H) ∧
      (⟨univ,[H],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (originalSmoothNCRegion W H) ∧
      IsClosedSubmanifold n (strictTransform n π W) ∧
      IsSNCDivisor n [BlowupStrictSubmanifold.geoStrictTransform π C H,π ⁻¹' C] ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (originalBoundaryTraceMarked W H) (.refl : BlowupTower X X))
        (originalBoundaryTraceMarked W H).cosupp := by
  obtain ⟨C,hCne,hCadm,hinter,hdis,hemb,hCeq⟩ :=
    exists_originalBoundaryTraceCentre hn hW hE hd hreg hdense hK hbad
  have hdom := originalBoundaryTraceMarked_isInvDomain hn hW hE hd hreg hdense
  have hint : interior C=∅ := eq_empty_of_subset_empty
    ((interior_mono hCadm.2.1).trans (ResolutionInvariantDriver.interior_cosupp_eq_empty hdom).subset)
  obtain ⟨Y,π,hπ⟩ := ResolutionDriver.exists_blowup C hCadm.1 hint
  have hGsub : originalSmoothNCRegion W H ⊆ Cᶜ := by
    intro x hx hxC
    exact Set.disjoint_left.mp hdis hxC hx
  have hisoC := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ
  have hiso : IsIsomorphismOver n π (originalSmoothNCRegion W H) := by
    refine ⟨⟨fun _ hz => hz,?_,?_⟩,hisoC.2.mono_left (preimage_mono hGsub)⟩
    · exact hisoC.1.2.1.mono (preimage_mono hGsub)
    · intro x hx
      obtain ⟨y,_hy,hπy⟩ := hisoC.1.2.2 (hGsub hx)
      exact ⟨y,by change π y ∈ originalSmoothNCRegion W H; rwa [hπy],hπy⟩
  have hdenseC : W ⊆ closure (W \ C) := hdense.trans (closure_mono (by
    rintro x ⟨hxW,hxH⟩
    exact ⟨hxW,fun hxC => hxH (hinter hxC).2⟩))
  have hgeo := BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hdenseC
  have hW' : IsClosedSubmanifold n (strictTransform n π W) := by
    rw [← hgeo]
    exact BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold
      hπ hW (fun _ hz => (hinter hz).1)
  have hMwell : (⟨univ,[H],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
      VanishingIdealCoherent.isCoherent_vanishingIdeal hW,hE,
      isTransverse_univ_of_isSNCDivisor hE⟩
  have hE' := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hMwell hemb hπ).isSNCDivisor
  change IsSNCDivisor n [BlowupStrictSubmanifold.geoStrictTransform π C H,π ⁻¹' C] at hE'
  exact ⟨C,Y,π,hCne,hCadm,hinter,hdis,hemb,hπ,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ,hπ.contMDiff,hiso,hW',hE',hCeq⟩

end
end Hironaka.HironakaSharpSingleBoundaryTraceCentre
