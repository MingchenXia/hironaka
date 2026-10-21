/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsTotalIdeal

/-! # Actual NC separation preserves the whole one-branch locus

The actual strict-original branch count never increases over its image in a
higher-stratum blowup. Induction through genuine actual separation towers then
puts every centre over the ORIGINAL intrinsic double locus. Consequently the
actual natural SNC boundary prephase is an isomorphism everywhere outside that
closed double locus, including every original one-branch boundary point.

This is a geometric boundary producer. An arbitrary marked ideal's cosupport,
its ordered lower history and canonical resolution are not inputs or conclusions.
An additional prescribed permitted set must explicitly contain the double locus.
Blueprint: `hironaka-normal-crossings-double-locus-separation-extension.tex`.
-/

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaNormalCrossingsDoubleLocusSeparation

open Hironaka.BlowupSequences
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsBoundarySeparation HironakaNormalCrossingsSeparationChoiceComparison
  BlowupFlatCoordinates BlowupStrictSubmanifold BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal HironakaStageCenters NormalCrossings RestrictEmptyTower
  HironakaAdmissibleSequence HironakaNormalCrossingsTotalIdeal
  HironakaNormalCrossingsBiholomorphicMultiplicity
  HironakaNormalCrossingsOpenRestrictionSeparation

noncomputable section
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

omit [IsComplexManifold n X] in
private theorem branchMultiplicity_congr {H K : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H)
    (hK : IsNormalCrossingsCarrier (n := n) K) (heq : H = K) (x : X) :
    branchMultiplicity hH x = branchMultiplicity hK x := by
  subst K
  rfl

/-- The actual strict-original branch count is bounded by its ORIGINAL count at
the image, rather than merely by the previous global maximum. -/
theorem branchMultiplicity_strict_highest_le_image {H : Set X}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 2 ≤ r)
    (hbound : ∀ x : X, branchMultiplicity hH x ≤ r) {π : Y → X}
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity hH x} π)
    (hp : IsNormalCrossingsCarrier (n := n) (strictTransform n π H)) (z : Y) :
    branchMultiplicity hp z ≤ branchMultiplicity hH (π z) := by
  have heq := geoStrictTransform_highest_eq_strictTransform hH hr hbound hπ
  have hp' : IsNormalCrossingsCarrier (n := n)
      (geoStrictTransform π {x | r ≤ branchMultiplicity hH x} H) := heq.symm ▸ hp
  have hcount := branchMultiplicity_congr hp hp' heq.symm z
  rw [hcount]
  by_cases hz : r ≤ branchMultiplicity hH (π z)
  · have hle := branchMultiplicity_strict_highest_le hH hbound hπ z
    exact hle.trans (by omega)
  · obtain ⟨Φ, -, hΦ0, S, hΦH⟩ := hH.2 (π z)
    obtain ⟨Θ, _, hΘ0, hΘ⟩ := MonomialResolution.exists_chart_comp hπ hz Φ hΦ0
    have hflat : ∀ u ∈ flatDomain Θ,
        u ∈ geoStrictTransform π {x | r ≤ branchMultiplicity hH x} H ↔
          ∃ i ∈ S, flatCoord Θ i u = 0 := by
      intro u hu
      obtain ⟨huC,huΦ,heq⟩ := hΘ hu.1 hu.2
      rw [mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hH.1 huC,
        hΦH (π u) huΦ]
      have hi : ∀ i : Fin n, flatCoord Θ i u = flatCoord Φ i (π u) :=
        fun i => congrArg (fun w : ComplexModel n => w i) heq
      simp_rw [← hi]
    exact le_of_eq ((branchMultiplicity_eq_card hp' Θ hΘ0 S hflat).trans
      (branchMultiplicity_eq_card hH Φ hΦ0 S hΦH).symm)

/-- Every genuine higher-separation tower bounds the entire current original
branch count by the original branch count at the actual composite image. -/
theorem branchMultiplicity_strict_tower_le_image {A : CMfd.{u} n}
    (M : MarkedIdeal n A) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T →
      (hp : IsNormalCrossingsCarrier (n := n) (strictTransform n T.proj H)) →
      ∀ z : D, branchMultiplicity hp z ≤ branchMultiplicity hH (T.proj z)
  | _,.refl,_,hp,z => by
      have hs : strictTransform n (id : A → A) H = H := by
        simp [strictTransform,exceptionalLocus_id,hH.1.closure_eq]
      exact le_of_eq (branchMultiplicity_congr hp hH hs z)
  | _,.step T C π hπ,hc,hp,z => by
      obtain ⟨hh,r,hr,hbound,hceq,_⟩ := hc.2
      have hcur := isNormalCrossingsCarrier_of_boundaryAdapted hh
      have hπ' : IsBlowupAlong n {x | r ≤ branchMultiplicity hcur x} π := hceq ▸ hπ
      have hs : strictTransform n (BlowupTower.step T C π hπ).proj H =
          strictTransform n π (strictTransform n T.proj H) := by
        rw [BlowupTower.proj_step,StrictTransformComposition.strictTransform_comp
          T.contMDiff_proj hπ.contMDiff]
      have hp' : IsNormalCrossingsCarrier (n := n)
          (strictTransform n π (strictTransform n T.proj H)) := hs ▸ hp
      calc
        branchMultiplicity hp z = branchMultiplicity hp' z :=
          branchMultiplicity_congr hp hp' hs z
        _ ≤ branchMultiplicity hcur (π z) :=
          branchMultiplicity_strict_highest_le_image hcur hr hbound hπ' hp' z
        _ ≤ branchMultiplicity hH (T.proj (π z)) :=
          branchMultiplicity_strict_tower_le_image M hH T hc.1 hcur (π z)

/-- All actual higher-separation centres lie over the ORIGINAL intrinsic double
locus; one-branch points on the original carrier are protected as well. -/
theorem centresOver_doubleLocus_of_higherSeparationCentres {A : CMfd.{u} n}
    (M : MarkedIdeal n A) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T →
      CentresOver {x | 2 ≤ branchMultiplicity hH x} T
  | _,.refl,_ => trivial
  | _,.step T C _π _hπ,hc => by
      refine ⟨centresOver_doubleLocus_of_higherSeparationCentres M hH T hc.1,?_⟩
      obtain ⟨hh,r,hr,_,hceq,_⟩ := hc.2
      intro x hx
      have hxcount : r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hh) x := by
        rw [hceq] at hx
        exact hx
      exact (hr.trans hxcount).trans
        (branchMultiplicity_strict_tower_le_image M hH T hc.1
          (isNormalCrossingsCarrier_of_boundaryAdapted hh) x)

/-- The actual higher-separation projection is an isomorphism on the WHOLE
complement of the intrinsic original double locus. -/
theorem isIsomorphismOver_compl_doubleLocus_of_higherSeparationCentres
    {A D : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (T : BlowupTower A D)
    (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
      (strictTransform n R.proj H) (geoTransformAlong M R).E C) T) :
    IsIsomorphismOver n T.proj {x | 2 ≤ branchMultiplicity hH x}ᶜ := by
  let U : TopologicalSpace.Opens A := ⟨{x | 2 ≤ branchMultiplicity hH x}ᶜ,
    (isClosed_branchMultiplicity_superlevel hH 2).isOpen_compl⟩
  have hav := centresAvoid_of_centresOver U
    (F := {x | 2 ≤ branchMultiplicity hH x}) disjoint_compl_left T
    (centresOver_doubleLocus_of_higherSeparationCentres M hH T hc)
  apply HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    T.isBlowupSequence
  simpa [U] using EmbeddedFromResolution.image_exceptionalLocus_subset_compl U T hav

/-- The actual higher centres supply genuine geometric boundary-admissible
steps, retaining the literal boundary and their original double-locus support. -/
theorem higherSeparationCentres_isAdmissibleBlowupSequence_doubleLocus
    {A : CMfd.{u} n} (M : MarkedIdeal n A) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong M R).E C) T →
      IsAdmissibleBlowupSequence n A M.E {x | 2 ≤ branchMultiplicity hH x}
        D T.proj (geoTransformAlong M T).E
  | _,.refl,_ => .refl
  | _,.step T C π hπ,hc => by
      obtain ⟨hh,r,_,hbound,hceq,_⟩ := hc.2
      have hnc : HasNormalCrossings n C (geoTransformAlong M T).E := by
        rw [hceq]
        exact hasNormalCrossings_highest_boundary hh hbound
      exact IsAdmissibleBlowupSequence.step T.proj _ C π
        (higherSeparationCentres_isAdmissibleBlowupSequence_doubleLocus M hH T hc.1)
        hπ hnc (centresOver_doubleLocus_of_higherSeparationCentres M hH
          (.step T C π hπ) hc).2

/-- The actual natural finite SNC prephase protects every original point where
at most one branch meets. No compactness, global branch labels or history is supplied. -/
theorem naturalSeparation_doubleLocus_geometry {A : CMfd.{u} n}
    (M : MarkedIdeal n A) {H : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) :
    let o := naturalSeparation M h
    let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
    o.T.length ≤ n-1 ∧ IsClosedSubmanifold n (strictTransform n o.T.proj H) ∧
      IsTransverse n (strictTransform n o.T.proj H) (geoTransformAlong M o.T).E ∧
      IsSNCDivisor n ((geoTransformAlong M o.T).E ++ [strictTransform n o.T.proj H]) ∧
      IsAdmissibleBlowupSequence n A M.E {x | 2 ≤ branchMultiplicity hH x}
        o.D o.T.proj (geoTransformAlong M o.T).E ∧
      CentresOver {x | 2 ≤ branchMultiplicity hH x} o.T ∧
      IsIsomorphismOver n o.T.proj {x | 2 ≤ branchMultiplicity hH x}ᶜ := by
  let o := naturalSeparation M h
  obtain ⟨hlen,hsm,htrans,hsnc,_,_,_⟩ := naturalSeparation_geometry M h
  exact ⟨hlen,hsm,htrans,hsnc,
    higherSeparationCentres_isAdmissibleBlowupSequence_doubleLocus M
      (isNormalCrossingsCarrier_of_boundaryAdapted h) o.T o.centres,
    centresOver_doubleLocus_of_higherSeparationCentres M
      (isNormalCrossingsCarrier_of_boundaryAdapted h) o.T o.centres,
    isIsomorphismOver_compl_doubleLocus_of_higherSeparationCentres M
      (isNormalCrossingsCarrier_of_boundaryAdapted h) o.T o.centres⟩

private theorem centresOver_mono {A : CMfd.{u} n} {F G : Set A} (hFG : F ⊆ G) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D), CentresOver F T → CentresOver G T
  | _,.refl,_ => trivial
  | _,.step T _ _ _,hc =>
      ⟨centresOver_mono hFG T hc.1,fun _ hx => hFG (hc.2 hx)⟩

/-- A closed prescribed permitted set containing the actual original double
locus supports the SAME internally constructed SNC boundary prephase. -/
theorem naturalSeparation_permitted_geometry {A : CMfd.{u} n}
    (M : MarkedIdeal n A) {H F : Set A}
    (h : IsBoundaryAdaptedCarrier (n := n) H M.E) (hF : IsClosed F)
    (hpermit : {x | 2 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} ⊆ F) :
    let o := naturalSeparation M h
    o.T.length ≤ n-1 ∧ IsClosedSubmanifold n (strictTransform n o.T.proj H) ∧
      IsTransverse n (strictTransform n o.T.proj H) (geoTransformAlong M o.T).E ∧
      IsSNCDivisor n ((geoTransformAlong M o.T).E ++ [strictTransform n o.T.proj H]) ∧
      IsAdmissibleBlowupSequence n A M.E F o.D o.T.proj (geoTransformAlong M o.T).E ∧
      CentresOver F o.T ∧ IsIsomorphismOver n o.T.proj Fᶜ := by
  let o := naturalSeparation M h
  obtain ⟨hlen,hsm,htrans,hsnc,hadm,hcover,_⟩ := naturalSeparation_doubleLocus_geometry M h
  have hFcover := centresOver_mono hpermit o.T hcover
  refine ⟨hlen,hsm,htrans,hsnc,hadm.mono hpermit,hFcover,?_⟩
  let U : TopologicalSpace.Opens A := ⟨Fᶜ,hF.isOpen_compl⟩
  have hav := centresAvoid_of_centresOver U (F := F) disjoint_compl_left o.T hFcover
  apply HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    o.T.isBlowupSequence
  simpa [U] using EmbeddedFromResolution.image_exceptionalLocus_subset_compl U o.T hav

/-- Actual hypersurface regularity is exactly intrinsic one-branch multiplicity.
The reverse direction uses the actual open one-branch neighbourhood, not a
global count-one premise on the original carrier. -/
theorem regularAtDim_iff_branchMultiplicity_eq_one {A : CMfd.{u} n} (hn : 0 < n)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) (x : A) :
    RegularAtDim (n := n) H x (n-1) ↔ branchMultiplicity hH x = 1 := by
  classical
  constructor
  · rintro ⟨_,_,Φ,_hsrc,h0,hflat⟩
    let j : Fin n := ⟨n-1,by omega⟩
    have hnc : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ ({j} : Finset (Fin n)),
        flatCoord Φ i y = 0 := by
      intro y hy
      rw [hflat hy.1 hy.2,NormalCrossingsComparison.mem_complexCoordinatePlane_pred_iff hn]
      simp only [Finset.mem_singleton,exists_eq_left]
      rfl
    rw [branchMultiplicity_eq_card hH Φ h0 {j} hnc,Finset.card_singleton]
  · intro hxcount
    let U : TopologicalSpace.Opens A := ⟨{x | 2 ≤ branchMultiplicity hH x}ᶜ,
      (isClosed_branchMultiplicity_superlevel hH 2).isOpen_compl⟩
    have hxU : x ∈ U := by
      change ¬ 2 ≤ branchMultiplicity hH x
      omega
    have hp := isNormalCrossingsCarrier_of_boundaryAdapted
      (boundaryAdapted_open U (boundaryAdapted_nil hH))
    have hbound : ∀ y : U, branchMultiplicity hp y ≤ 1 := by
      intro y
      rw [branchMultiplicity_open U hH hp]
      have hy : ¬ 2 ≤ branchMultiplicity hH (y : A) := y.2
      omega
    have hxH : (⟨x,hxU⟩ : U) ∈ (Subtype.val : U → A) ⁻¹' H :=
      (branchMultiplicity_pos_iff hH x).mp (by omega)
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp
      (regularAtDim_of_branchMultiplicity_le_one hp hbound hxH)

/-- The intrinsic original double locus equals the actual original hypersurface
singular locus, including all components and without global branch labels. -/
theorem doubleLocus_eq_diff_regularLocus {A : CMfd.{u} n} (hn : 0 < n)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    {x | 2 ≤ branchMultiplicity hH x} = H \ regularLocus (n := n) H (n-1) := by
  ext x
  change 2 ≤ branchMultiplicity hH x ↔ x ∈ H ∧ ¬ RegularAtDim (n := n) H x (n-1)
  constructor
  · intro hx
    refine ⟨(branchMultiplicity_pos_iff hH x).mp (by omega),?_⟩
    intro hreg
    have := (regularAtDim_iff_branchMultiplicity_eq_one hn hH x).mp hreg
    omega
  · rintro ⟨hxH,hxreg⟩
    have hpos := (branchMultiplicity_pos_iff hH x).mpr hxH
    have hne : branchMultiplicity hH x ≠ 1 := by
      intro heq
      exact hxreg ((regularAtDim_iff_branchMultiplicity_eq_one hn hH x).mpr heq)
    omega

/-- The SAME actual original separation is a bounded boundary-admissible NC
prephase supported over the actual original singular locus. Its whole original
inverse image is the union of its internally produced terminal SNC list. -/
theorem originalSeparation_singularLocus_geometry {A : CMfd.{u} n} (hn : 0 < n)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    let o := originalSeparation hH
    let E := (geoTransformAlong (originalMarkedIdeal H) o.T).E
    let F := H \ regularLocus (n := n) H (n-1)
    o.T.length ≤ n-1 ∧ IsAdmissibleBlowupSequence n A [] F o.D o.T.proj E ∧
      IsClosedSubmanifold n (strictTransform n o.T.proj H) ∧
      IsTransverse n (strictTransform n o.T.proj H) E ∧
      IsSNCDivisor n (terminalBoundary hH) ∧
      o.T.proj ⁻¹' H = ⋃ B ∈ terminalBoundary hH, B ∧
      CentresOver F o.T ∧ IsIsomorphismOver n o.T.proj Fᶜ := by
  obtain ⟨hlen,hsm,htrans,hsnc,hadm,hcover,hiso⟩ :=
    naturalSeparation_doubleLocus_geometry (originalMarkedIdeal H) (boundaryAdapted_nil hH)
  have heq : {x | 2 ≤ branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_nil hH)) x} =
      H \ regularLocus (n := n) H (n-1) := doubleLocus_eq_diff_regularLocus hn hH
  rw [heq] at hadm hcover hiso
  exact ⟨hlen,hadm,hsm,htrans,hsnc,preimage_original_eq_terminalBoundary hH,hcover,hiso⟩

end
end Hironaka.HironakaNormalCrossingsDoubleLocusSeparation
