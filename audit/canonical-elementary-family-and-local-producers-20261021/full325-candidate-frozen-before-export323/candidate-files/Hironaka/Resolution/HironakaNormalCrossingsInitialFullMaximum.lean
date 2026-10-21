/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsActualResidual
import Hironaka.Invariant.CanonicalCentres

/-! # Whole FULL canonical maxima at the initial empty NC history

Actual NC flattenings compare the complete original reflexive invariant with
the SAME coordinate model. At a global highest positive branch count, existing
actual highest-stratum coordinates normalize all local branch index sets to the
same last coordinates. This concerns the initial empty boundary/history only;
no later chronological or companion-history alignment is asserted.
Blueprint: `hironaka-normal-crossings-initial-full-maximum-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsInitialFullMaximum

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsBoundarySeparation
  HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsTotalIdeal HironakaNormalCrossingsMarkedAdmissibility
  HironakaNormalCrossingsBiholomorphicMultiplicity HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsActualResidual BlowupFlatCoordinates BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres ResolutionInvariantSpec
  BlowupTowerIsomorphism MarkedIdealBiholomorphism

noncomputable section
variable {n : ℕ}

/-- The whole genuine coordinate-branch union, in the original manifold universe. -/
def coordinateCarrier (S : Finset (Fin n)) : Set (LiftedModel.{u} n) :=
  {w | ∃ i ∈ S, w.down i = 0}

private def translation (w : ComplexModel n) : LocalHolomorphicEquivAt (n := n) w where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := fun z => z-w
  invFun := fun z => z+w
  toFun_holomorphic := (differentiable_id.sub_const w).differentiableOn
  invFun_holomorphic := (differentiable_id.add_const w).differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => sub_add_cancel _ _
  right_inv := fun _ _ => add_sub_cancel_right _ _

/-- Genuine translation and actual nonvanishing neighbourhoods give the whole
coordinate model its NC presentations at every actual model point. -/
theorem coordinateCarrier_isNormalCrossings (S : Finset (Fin n)) :
    IsNormalCrossingsCarrier (n := n) (coordinateCarrier.{u} S) := by
  classical
  refine ⟨?_,fun w => ?_⟩
  · have heq : coordinateCarrier.{u} S = ⋃ i ∈ S, {w : LiftedModel.{u} n | w.down i = 0} := by
      ext w
      simp [coordinateCarrier]
    rw [heq]
    exact isClosed_biUnion_finset fun i _ => isClosed_eq
      ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous.comp continuous_uliftDown)
      continuous_const
  · let Ω : Set (ComplexModel n) := {z | ∀ i ∈ S, w.down i ≠ 0 → z i ≠ 0}
    have hΩ : IsOpen Ω := by
      apply isOpen_iff_mem_nhds.mpr
      intro z hz
      have hev : ∀ i : Fin n, ∀ᶠ z' in 𝓝 z, i ∈ S → w.down i ≠ 0 → z' i ≠ 0 := by
        intro i
        by_cases hi : i ∈ S ∧ w.down i ≠ 0
        · have hz0 := hz i hi.1 hi.2
          filter_upwards [((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous.continuousAt).eventually_ne hz0]
            with z' hz' _ _
          exact hz'
        · exact Eventually.of_forall fun _ hiS hwi => False.elim (hi ⟨hiS,hwi⟩)
      exact (eventually_all.mpr hev).mono fun z' hz' => hz'
    have hwΩ : w.down ∈ Ω := fun _ _ hwi => hwi
    let Φ := (translation w.down).restrict Ω hΩ w.down ⟨mem_univ _,hwΩ⟩
    refine ⟨Φ,fun _ _ => mem_univ _,sub_self _,S.filter (fun i => w.down i = 0),?_⟩
    intro z hz
    constructor
    · rintro ⟨i,hi,hzi⟩
      have hwi : w.down i = 0 := by
        by_contra hwi
        exact (hz.2.2 i hi hwi) hzi
      refine ⟨i,Finset.mem_filter.mpr ⟨hi,hwi⟩,?_⟩
      change z.down i-w.down i = 0
      rw [hzi,hwi,sub_self]
    · rintro ⟨i,hi,hcoord⟩
      obtain ⟨hiS,hwi⟩ := Finset.mem_filter.mp hi
      refine ⟨i,hiS,?_⟩
      change z.down i-w.down i = 0 at hcoord
      simpa only [hwi,sub_zero] using hcoord

variable {A B : CMfd.{u} n}

/-- The whole actual original value at the initial empty history. -/
def initialFullValue (hn : 0 < n) (H : Set A) (x : A) : ValTy (n+1) :=
  (invFamily hn (n+1)).inv (originalMarkedIdeal H) .refl x

private theorem original_domain {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    IsInvDomain (n+1) (originalMarkedIdeal H) := by
  have h := isInvDomain_originalMarkedIdeal hH
  refine ⟨h.isWellFormed,?_,h.one_le_d,h.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨d,hd,hreg⟩ := h.dimLE x hx
  exact ⟨d,hd.trans (Nat.le_succ n),hreg⟩

private theorem original_pullback_open {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (U : TopologicalSpace.Opens A) :
    MarkedIdeal.pullback (Subtype.val : U → A) (originalMarkedIdeal H) =
      originalMarkedIdeal (A := CMfd.of (n := n) U) ((Subtype.val : U → A) ⁻¹' H) := by
  have hp := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U (boundaryAdapted_nil hH))
  have hc : (vanishingIdeal (n := n) ((Subtype.val : U → A) ⁻¹' H)).IsCoherent :=
    (isInvDomain_originalMarkedIdeal (A := CMfd.of (n := n) U) hp).isWellFormed.isCoherent
  have hi := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) U (id : U → U) H
  rw [BlowupControlledTransform.pullback_id hc] at hi
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (𝔪 := MarkedIdeal.pullback (Subtype.val : U → A) (originalMarkedIdeal H))
    (𝔫 := originalMarkedIdeal (A := CMfd.of (n := n) U) ((Subtype.val : U → A) ⁻¹' H)) rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) (Subtype.val : U → A) (vanishingIdeal (n := n) H) =
    vanishingIdeal (n := n) ((Subtype.val : U → A) ⁻¹' H)
  simpa only [Function.comp_id] using hi.symm

private theorem original_pullback_diffeomorph
    (χ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    MarkedIdeal.pullback χ (originalMarkedIdeal H) = originalMarkedIdeal (χ ⁻¹' H) := by
  have hp := isNormalCrossingsCarrier_preimage χ.contMDiff
    (notMem_exceptionalLocus_of_inverse χ.contMDiff χ.symm.contMDiff
      χ.apply_symm_apply χ.symm_apply_apply) hH
  have hc : (vanishingIdeal (n := n) (χ ⁻¹' H)).IsCoherent :=
    (isInvDomain_originalMarkedIdeal hp).isWellFormed.isCoherent
  have hi := pullback_vanishingIdeal_preimage χ.contMDiff χ.symm.contMDiff
    χ.apply_symm_apply χ.symm_apply_apply (g := (id : B → B)) contMDiff_id H
  rw [BlowupControlledTransform.pullback_id hc] at hi
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (𝔪 := MarkedIdeal.pullback χ (originalMarkedIdeal H))
    (𝔫 := originalMarkedIdeal (χ ⁻¹' H)) rfl rfl ?_ rfl
  change GermIdeal.pullback (m := n) χ (vanishingIdeal (n := n) H) = vanishingIdeal (n := n) (χ ⁻¹' H)
  simpa only [Function.comp_id] using hi.symm

private theorem initialFullValue_open (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (U : TopologicalSpace.Opens A)
    (x : U) (hx : (x : A) ∈ H) :
    initialFullValue (A := CMfd.of (n := n) U) hn ((Subtype.val : U → A) ⁻¹' H) x =
      initialFullValue hn H (x : A) := by
  have hcos : (originalMarkedIdeal H).cosupp = H :=
    HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hH.1 []
  have hv := (invFamily hn (n+1)).isInvValue.restrictOpen
    (originalMarkedIdeal H) (original_domain hH) U .refl trivial x
    (by simpa only [geoTransformAlong_refl,hcos] using hx)
  rw [original_pullback_open hH U] at hv
  exact hv

private theorem initialFullValue_diffeomorph (hn : 0 < n)
    (χ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H)
    (x : B) (hx : χ x ∈ H) :
    initialFullValue hn (χ ⁻¹' H) x = initialFullValue hn H (χ x) := by
  have hcos : (originalMarkedIdeal H).cosupp = H :=
    HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hH.1 []
  have hv := (invFamily hn (n+1)).isInvValue.towerIso χ
    (originalMarkedIdeal H) (original_domain hH) .refl .refl χ .refl trivial x
    (by simpa only [geoTransformAlong_refl,hcos] using hx)
  rw [original_pullback_diffeomorph χ hH] at hv
  exact hv

/-- An actual centred NC flattening transports EVERY entry of the original
empty-history invariant to the genuine whole coordinate model at zero. -/
theorem initialFullValue_eq_coordinate_model (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {x : A} (hx : x ∈ H)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (S : Finset (Fin n))
    (hflat : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0) :
    initialFullValue hn H x =
      initialFullValue (A := CMfd.of (n := n) (LiftedModel.{u} n)) hn
        (coordinateCarrier S) (ULift.up (0 : ComplexModel n)) := by
  let U : TopologicalSpace.Opens A := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let T : TopologicalSpace.Opens (ComplexModel n) := ⟨Φ.target,Φ.isOpen_target⟩
  let χ := flatDomainDiffeomorph Φ hsrc
  let px : U := ⟨x,mem_flatDomain_self Φ⟩
  have hzT : (0 : ComplexModel n) ∈ T := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  let pz : LiftedOpen.{u} T := LiftedOpen.mk T 0 hzT
  have hχ : χ px = pz := by
    apply Subtype.ext
    apply ULift.ext
    exact h0
  have hpre : χ ⁻¹' ((Subtype.val : LiftedOpen.{u} T → LiftedModel.{u} n) ⁻¹' coordinateCarrier S) =
      (Subtype.val : U → A) ⁻¹' H := by
    ext p
    change (∃ i ∈ S, flatCoord Φ i (p : A) = 0) ↔ (p : A) ∈ H
    exact (hflat p p.2).symm
  have hmodel := coordinateCarrier_isNormalCrossings.{u} S
  have htrace := isNormalCrossingsCarrier_of_boundaryAdapted
    (boundaryAdapted_open (A := CMfd.of (n := n) (LiftedModel.{u} n))
      (liftedOpens T) (boundaryAdapted_nil hmodel))
  have hχmem : χ px ∈ (Subtype.val : LiftedOpen.{u} T → LiftedModel.{u} n) ⁻¹' coordinateCarrier S := by
    change px ∈ χ ⁻¹' ((Subtype.val : LiftedOpen.{u} T → LiftedModel.{u} n) ⁻¹' coordinateCarrier S)
    rw [hpre]
    exact hx
  have hvalue := initialFullValue_diffeomorph
    (A := CMfd.of (n := n) (LiftedOpen.{u} T)) (B := CMfd.of (n := n) U) hn χ htrace px hχmem
  rw [hpre,hχ] at hvalue
  have hmodelmem : (ULift.up (0 : ComplexModel n) : LiftedModel.{u} n) ∈ coordinateCarrier S := by
    have hh := hχmem
    rw [hχ] at hh
    exact hh
  exact (initialFullValue_open hn hH U px hx).symm.trans
    (hvalue.trans (initialFullValue_open (A := CMfd.of (n := n) (LiftedModel.{u} n))
      hn hmodel (liftedOpens T) pz hmodelmem))

/-- At the actual highest original count, genuine normalized charts compare
the WHOLE initial values through one identical last-coordinate NC model. -/
theorem initialFullValue_eq_of_highest_branch_count (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ z : A, branchMultiplicity hH z ≤ r) {x y : A}
    (hx : r ≤ branchMultiplicity hH x) (hy : r ≤ branchMultiplicity hH y) :
    initialFullValue hn H x = initialFullValue hn H y := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => n-r ≤ i.val)
  obtain ⟨Φ,hsrc,h0,_,hflat⟩ := exists_highest_stratum_branch_adapted_coordinates hH hbound hx
  obtain ⟨Ψ,hsrc',h0',_,hflat'⟩ := exists_highest_stratum_branch_adapted_coordinates hH hbound hy
  have hxH := (branchMultiplicity_pos_iff hH x).mp (hr.trans_le hx)
  have hyH := (branchMultiplicity_pos_iff hH y).mp (hr.trans_le hy)
  have hΦ : ∀ z ∈ flatDomain Φ, z ∈ H ↔ ∃ i ∈ S, flatCoord Φ i z = 0 := by
    intro z hz
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hflat z hz
  have hΨ : ∀ z ∈ flatDomain Ψ, z ∈ H ↔ ∃ i ∈ S, flatCoord Ψ i z = 0 := by
    intro z hz
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hflat' z hz
  exact (initialFullValue_eq_coordinate_model hn hH hxH Φ hsrc h0 S hΦ).trans
    (initialFullValue_eq_coordinate_model hn hH hyH Ψ hsrc' h0' S hΨ).symm

private theorem branchMultiplicity_congr {H K : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hK : IsNormalCrossingsCarrier (n := n) K)
    (heq : H = K) (x : A) : branchMultiplicity hH x = branchMultiplicity hK x := by
  subst K
  rfl

private theorem initial_nmOrd (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (x : A) :
    NonmonomialOrderLocal.nmOrd (originalMarkedIdeal H) x = branchMultiplicity hH x := by
  have hp := isNormalCrossingsCarrier_of_boundaryAdapted
    (HironakaNormalCrossingsOriginalExponents.higherSeparationCentres_pair hH
      (.refl : BlowupTower A A) trivial)
  have hs : strictTransform n (id : A → A) H = H := by
    simp [strictTransform,exceptionalLocus_id,hH.1.closure_eq]
  have hv := higherSeparationCentres_nmOrd hn hH (.refl : BlowupTower A A) trivial x
  change NonmonomialOrderLocal.nmOrd (originalMarkedIdeal H) x = branchMultiplicity hp x at hv
  exact hv.trans (branchMultiplicity_congr hp hH hs x)

private theorem initialFullValue_lt_of_branch_count_lt (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {x y : A}
    (hlt : branchMultiplicity hH x < branchMultiplicity hH y) :
    initialFullValue hn H x < initialFullValue hn H y := by
  have hfirst (z : A) : (ofLex (initialFullValue hn H z)).1 = branchMultiplicity hH z := by
    change NonmonomialOrderLocal.nmOrd (geoTransformAlong (originalMarkedIdeal H) .refl) z = _
    exact initial_nmOrd hn hH z
  change toLex (ofLex (initialFullValue hn H x)) < toLex (ofLex (initialFullValue hn H y))
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl (by rw [hfirst,hfirst]; exact hlt)

/-- At the initial empty history, the ENTIRE original FULL maximum is exactly
the whole highest branch stratum. This is not an all-prefix assertion. -/
theorem initialFullMaximum_eq_highest_stratum (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ x : A, branchMultiplicity hH x ≤ r)
    (hatt : {x | r ≤ branchMultiplicity hH x}.Nonempty) :
    ResolutionDriver.maxLocus (initialFullValue hn H) (originalMarkedIdeal H).cosupp =
      {x | r ≤ branchMultiplicity hH x} := by
  have hcos : (originalMarkedIdeal H).cosupp = H :=
    HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hH.1 []
  obtain ⟨a,ha⟩ := hatt
  have haH := (branchMultiplicity_pos_iff hH a).mp (hr.trans_le ha)
  rw [hcos]
  ext x
  change (x ∈ H ∧ ∀ y ∈ H, initialFullValue hn H y ≤ initialFullValue hn H x) ↔
    r ≤ branchMultiplicity hH x
  constructor
  · rintro ⟨_,hmax⟩
    by_contra hx
    have hlt := initialFullValue_lt_of_branch_count_lt hn hH
      ((Nat.lt_of_not_ge hx).trans_le ha)
    exact (not_lt_of_ge (hmax a haH)) hlt
  · intro hx
    refine ⟨(branchMultiplicity_pos_iff hH x).mp (hr.trans_le hx),fun y _hy => ?_⟩
    by_cases hy : r ≤ branchMultiplicity hH y
    · exact le_of_eq (initialFullValue_eq_of_highest_branch_count hn hH hr hbound hy hx)
    · exact (initialFullValue_lt_of_branch_count_lt hn hH
        ((Nat.lt_of_not_ge hy).trans_le hx)).le

/-- ONLY the original nonempty NC carrier internally produces its true first
FULL canonical blowup, with no compactness or maximum/history certificate. -/
theorem exists_initial_full_canonical_blowup (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hne : H.Nonempty) :
    ∃ r : ℕ, 0 < r ∧ r ≤ n ∧ (∀ x : A, branchMultiplicity hH x ≤ r) ∧
      {x | r ≤ branchMultiplicity hH x}.Nonempty ∧
      {x | r ≤ branchMultiplicity hH x} =
        ResolutionDriver.maxLocus (initialFullValue hn H) (originalMarkedIdeal H).cosupp ∧
      ∃ D : CMfd.{u} n, ∃ π : D → A,
        ∃ hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity hH x} π,
          IsGeoTestTower (originalMarkedIdeal H) (.step .refl _ π hπ) ∧
          IsCanonical (originalMarkedIdeal H) ((invFamily hn (n+1)).inv (originalMarkedIdeal H))
            (.step .refl _ π hπ) := by
  obtain ⟨r,hr,hrn,hbound,hatt,_,_,_⟩ := exists_highest_multiplicity_stratum hH hne
  have hatt' : {x | r ≤ branchMultiplicity hH x}.Nonempty := by
    obtain ⟨x,hx⟩ := hatt
    exact ⟨x,hx.ge⟩
  have hmax := (initialFullMaximum_eq_highest_stratum hn hH hr hbound hatt').symm
  obtain ⟨D,hDtop,hDchart,hDcm,π,hπ⟩ := exists_highest_stratum_blowup hH hr hbound
  let := hDtop
  let := hDchart
  let := hDcm
  have hadm : (originalMarkedIdeal H).IsAdmissibleCentre {x | r ≤ branchMultiplicity hH x} := by
    rw [hmax]
    exact (invFamily hn (n+1)).isInvValue.isAdmissibleCentre_maxLocus
      (original_domain hH) .refl trivial trivial
  exact ⟨r,hr,hrn,hbound,hatt',hmax,CMfd.of (n := n) D,π,hπ,
    ⟨trivial,hadm⟩,⟨trivial,Or.inr hmax⟩⟩

end
end Hironaka.HironakaNormalCrossingsInitialFullMaximum
