/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsDiagonalLiftOrbits

/-! # Finite WHOLE canonical values after the actual first NC step

The entire coordinate model is first proved canonical for canonicalInvariant n.
Actual whole-record/history/cosupport transport moves original open values to
that SAME entire history before any geometric diagonal orbit is used.
Blueprint: `hironaka-normal-crossings-first-step-finite-values-extension.tex`.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaNormalCrossingsFirstStepFiniteValues

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsBoundarySeparation
  HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsTotalIdeal HironakaNormalCrossingsMarkedAdmissibility
  HironakaNormalCrossingsBiholomorphicMultiplicity HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsActualResidual BlowupFlatCoordinates BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres ResolutionInvariantSpec
  BlowupTowerIsomorphism MarkedIdealBiholomorphism HironakaNormalCrossingsInitialFullMaximum

  HironakaNormalCrossingsCanonicalInitialStep HironakaNormalCrossingsFirstStepChartHistory
  HironakaNormalCrossingsDiagonalLiftOrbits BlowupTowerTransforms

noncomputable section
variable {n : ℕ}

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

/-- A true centred translation/nonvanishing chart computes the intrinsic count. -/
theorem coordinateCarrier_branchMultiplicity (S : Finset (Fin n)) (w : LiftedModel.{u} n) :
    branchMultiplicity (coordinateCarrier_isNormalCrossings.{u} S) w =
      (S.filter (fun i => w.down i = 0)).card := by
  classical
  let Ω : Set (ComplexModel n) := {z | ∀ i ∈ S, w.down i ≠ 0 → z i ≠ 0}
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
  apply branchMultiplicity_eq_card (coordinateCarrier_isNormalCrossings.{u} S)
    Φ (sub_self _) (S.filter (fun i => w.down i = 0))
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

abbrev ModelBase (n : ℕ) : CMfd.{u} n := CMfd.of (n := n) (LiftedModel.{u} n)

def lastCoordinates (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => n-r ≤ i.val)

theorem modelNC (r : ℕ) : IsNormalCrossingsCarrier (n := n) (coordinateOriginal.{u} (n := n) r) :=
  coordinateCarrier_isNormalCrossings (lastCoordinates r)

def modelMarked (r : ℕ) : MarkedIdeal n (ModelBase.{u} n) :=
  originalMarkedIdeal (A := ModelBase.{u} n) (coordinateOriginal r)

private theorem model_bound (r : ℕ) (hcard : (lastCoordinates (n := n) r).card = r)
    (w : LiftedModel.{u} n) : branchMultiplicity (modelNC.{u} r) w ≤ r := by
  change branchMultiplicity (coordinateCarrier_isNormalCrossings.{u} (lastCoordinates r)) w ≤ r
  rw [coordinateCarrier_branchMultiplicity]
  exact (Finset.card_filter_le _ _).trans_eq hcard

private theorem model_zero (r : ℕ) (hcard : (lastCoordinates (n := n) r).card = r) :
    r ≤ branchMultiplicity (modelNC.{u} r) (ULift.up (0 : ComplexModel n) : LiftedModel.{u} n) := by
  have hv := coordinateCarrier_branchMultiplicity.{u} (lastCoordinates r) (ULift.up (0 : ComplexModel n))
  have hc : branchMultiplicity (modelNC.{u} r)
      (ULift.up (0 : ComplexModel n) : LiftedModel.{u} n) = (lastCoordinates (n := n) r).card := by
    simpa [coordinateOriginal,lastCoordinates] using hv
  exact (hc.trans hcard).ge

/-- Exact whole model highest stratum, with no supplied invariant equality. -/
theorem model_highest_eq_centre (r : ℕ) (hcard : (lastCoordinates (n := n) r).card = r) :
    {w : LiftedModel.{u} n | r ≤ branchMultiplicity (modelNC.{u} r) w} = entireCentre (n-r) := by
  classical
  ext w
  change r ≤ branchMultiplicity (coordinateCarrier_isNormalCrossings.{u} (lastCoordinates r)) w ↔ _
  rw [coordinateCarrier_branchMultiplicity]
  change r ≤ ((lastCoordinates r).filter (fun i => w.down i = 0)).card ↔
    ∀ i : Fin n, n-r ≤ i.val → w.down i = 0
  constructor
  · intro hw
    have heq : (lastCoordinates r).filter (fun i => w.down i = 0) = lastCoordinates r :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hcard]; exact hw)
    intro i hi
    have hiS : i ∈ lastCoordinates r := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
    have himem : i ∈ (lastCoordinates r).filter (fun j => w.down j = 0) := by
      rw [heq]
      exact hiS
    exact (Finset.mem_filter.mp himem).2
  · intro hw
    have heq : (lastCoordinates r).filter (fun i => w.down i = 0) = lastCoordinates r :=
      Finset.filter_eq_self.mpr fun i hi => hw i (Finset.mem_filter.mp hi).2
    rw [heq,hcard]

variable {A B D : CMfd.{u} n}

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

/-- The ENTIRE fixed model history is first proved canonical for the actual
ambient-dimensional invariant, before its diagonal orbit set is used. -/
theorem coordinate_model_first_isCanonical (hn : 0 < n) {r : ℕ} (hr : 0 < r)
    (hcard : (lastCoordinates (n := n) r).card = r) {σ : D → LiftedModel.{u} n}
    (hσ : IsBlowupAlong n (entireCentre (n-r)) σ) :
    IsCanonical (modelMarked r) ((canonicalInvariant n).inv (modelMarked r)) (entireTower hσ) := by
  have hmax := (model_highest_eq_centre.{u} r hcard).symm.trans
    (canonicalInitialMaximum_eq_highest_stratum (A := ModelBase.{u} n) hn (modelNC.{u} r)
      hr (model_bound r hcard) ⟨ULift.up (0 : ComplexModel n),model_zero r hcard⟩).symm
  exact ⟨trivial,Or.inr hmax⟩

/-- Actual entire model values on its transformed cosupport over zero have a
finite image, using genuine whole record/tower/cosupport laws BEFORE geometric Q. -/
theorem finite_coordinate_first_fibre_values (hn : 0 < n) {r : ℕ} (hr : 0 < r)
    (hcard : (lastCoordinates (n := n) r).card = r) {σ : D → LiftedModel.{u} n}
    (hσ : IsBlowupAlong n (entireCentre (n-r)) σ) :
    (((canonicalInvariant n).inv (modelMarked r) (entireTower hσ)) ''
      {z : D | z ∈ (geoTransformAlong (modelMarked r) (entireTower hσ)).cosupp ∧
        σ z = (ULift.up (0 : ComplexModel n) : LiftedModel.{u} n)}).Finite := by
  let M := modelMarked (n := n) r
  let R := canonicalInvariant n
  let T := entireTower hσ
  have hdom : IsInvDomain n M := isInvDomain_originalMarkedIdeal (modelNC.{u} r)
  have hcan := coordinate_model_first_isCanonical hn hr hcard hσ
  have htest := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
  obtain ⟨Q,hQ,hcover⟩ := exists_finite_geometric_orbit_representatives hσ
  apply (hQ.image (R.inv M T)).subset
  rintro _ ⟨z,⟨hzcos,hz0⟩,rfl⟩
  obtain ⟨a,ha,E,hE,hEQ⟩ := hcover z hz0
  have hset : (diagonalEquiv a ha) ⁻¹' coordinateOriginal r = coordinateOriginal.{u} r :=
    diagonal_preimage_carrier a ha (lastCoordinates r)
  have hM : MarkedIdeal.pullback (diagonalEquiv a ha) M = M := by
    change MarkedIdeal.pullback (diagonalEquiv a ha)
      (originalMarkedIdeal (A := ModelBase.{u} n) (coordinateOriginal r)) = _
    rw [original_pullback_diffeomorph (A := ModelBase.{u} n) (B := ModelBase.{u} n)
      (diagonalEquiv a ha) (modelNC.{u} r),hset]
    rfl
  have hcos := BlowupTowerIsomorphism.IsTowerIso.cosupp_geoTransformAlong
    (X := ModelBase.{u} n) (X' := ModelBase.{u} n) (𝔪 := M) (T' := T) (T := T) (χ := E)
    (diagonalEquiv a ha) hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent hE htest
  rw [hM] at hcos
  have hzE : E z ∈ (geoTransformAlong M T).cosupp := by
    rw [← mem_preimage,hcos.symm]
    exact hzcos
  have hv := R.isInvValue.towerIso (diagonalEquiv a ha) M hdom T T E hE hcan z hzE
  rw [hM] at hv
  exact ⟨E z,hEQ,hv.symm⟩

/-- Actual original chart histories move to the SAME ENTIRE canonical model
before any diagonal normalization; the image is an actual cosupport point over0. -/
theorem exists_highest_chart_entire_canonical_value (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ y : A, branchMultiplicity hH y ≤ r)
    (hcard : (lastCoordinates (n := n) r).card = r)
    {π : D → A} (hπ : IsBlowupAlong n {y | r ≤ branchMultiplicity hH y} π)
    {F : CMfd.{u} n} {σ : F → LiftedModel.{u} n}
    (hσ : IsBlowupAlong n (entireCentre (n-r)) σ)
    (z : D) (hz : z ∈ (geoTransformAlong (originalMarkedIdeal H) (.step .refl _ π hπ)).cosupp)
    (hzC : r ≤ branchMultiplicity hH (π z)) :
    ∃ w : F, σ w = (ULift.up (0 : ComplexModel n) : LiftedModel.{u} n) ∧
      w ∈ (geoTransformAlong (modelMarked r) (entireTower hσ)).cosupp ∧
      (canonicalInvariant n).inv (originalMarkedIdeal H) (.step .refl _ π hπ) z =
        (canonicalInvariant n).inv (modelMarked r) (entireTower hσ) w := by
  obtain ⟨Q,hmarked,hvalue⟩ := exists_highest_chart_history_canonical_value hn hH hr hbound hzC hπ hσ
  let M := originalMarkedIdeal H
  let R := canonicalInvariant n
  let U := chartOpen Q.Φ
  let V := coordinateOpen Q.Φ
  let T : BlowupTower A D := .step .refl _ π hπ
  let mU := MarkedIdeal.pullback (Subtype.val : U → A) M
  let p : openPreimage T U := ⟨z,mem_flatDomain_self Q.Φ⟩
  have hdom : IsInvDomain n M := isInvDomain_originalMarkedIdeal hH
  have hmax := (canonicalInitialMaximum_eq_highest_stratum hn hH hr hbound ⟨π z,hzC⟩).symm
  have hcan : IsCanonical M (R.inv M) T := ⟨trivial,Or.inr hmax⟩
  have htest := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
  have htrace := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_open U (boundaryAdapted_nil hH))
  have hdomU : IsInvDomain n mU := by
    change IsInvDomain n (MarkedIdeal.pullback (Subtype.val : U → A) (originalMarkedIdeal H))
    rw [original_pullback_open hH U]
    exact isInvDomain_originalMarkedIdeal htrace
  have htestU := MarkedIdealRestrictOpen.isGeoTestTower_restrict U
    hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent T htest
  have hpU : p ∈ (geoTransformAlong mU (restrict U T)).cosupp := by
    rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
      hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent U T htest]
    exact hz
  have hcosIso := BlowupTowerIsomorphism.IsTowerIso.cosupp_geoTransformAlong
    (X := CMfd.of (n := n) U) (X' := CMfd.of (n := n) V) (𝔪 := mU)
    (T' := restrict V (entireTower hσ)) (T := restrict U T) (χ := Q.lifted.symm)
    (flatDomainDiffeomorph Q.Φ Q.hsrc).symm hdomU.isWellFormed.isClosedSubmanifold_N
    hdomU.isWellFormed.isCoherent Q.historyIso.symm htestU
  rw [Q.pullback_original] at hcosIso
  have hpV : Q.lifted p ∈ (geoTransformAlong (coordinateDatum Q.Φ r)
      (restrict V (entireTower hσ))).cosupp := by
    have hpInv : Q.lifted.symm (Q.lifted p) ∈
        (geoTransformAlong mU (restrict U T)).cosupp := by
      simpa only [Q.lifted.symm_apply_apply] using hpU
    exact (congrArg (fun S => Q.lifted p ∈ S) hcosIso).mpr hpInv
  have hmodelDom : IsInvDomain n (modelMarked (n := n) r) := isInvDomain_originalMarkedIdeal (modelNC.{u} r)
  have hmodelCan := coordinate_model_first_isCanonical hn hr hcard hσ
  have hmodelTest := R.isInvValue.isGeoTestTower_of_isCanonical hmodelDom (entireTower hσ) hmodelCan
  have hopen : MarkedIdeal.pullback (Subtype.val : V → LiftedModel.{u} n) (modelMarked r) =
      coordinateDatum Q.Φ r := original_pullback_open (A := ModelBase.{u} n) (modelNC.{u} r) V
  have hcosV := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hmodelDom.isWellFormed.isClosedSubmanifold_N hmodelDom.isWellFormed.isCoherent V (entireTower hσ) hmodelTest
  rw [hopen] at hcosV
  have hpGlobal : (Q.lifted p : F) ∈ (geoTransformAlong (modelMarked r) (entireTower hσ)).cosupp := by
    exact (congrArg (fun S => Q.lifted p ∈ S) hcosV).mp hpV
  have hmodelValue := R.isInvValue.restrictOpen (modelMarked r) hmodelDom V (entireTower hσ)
    hmodelCan (Q.lifted p) hpGlobal
  rw [hopen] at hmodelValue
  refine ⟨Q.lifted p,?_,hpGlobal,(hvalue p hz).trans hmodelValue⟩
  have hc := congrArg (Subtype.val : V → LiftedModel.{u} n) (Q.historyIso.proj_comm p)
  change (ULift.up (Q.Φ.toFun (chartAt (ComplexModel n) (π z) (π z))) : LiftedModel.{u} n) =
    σ (Q.lifted p) at hc
  exact hc.symm.trans (congrArg (fun v : ComplexModel n => (ULift.up v : LiftedModel.{u} n)) Q.hzero)

section Initial
variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- Finite actual NC chart types give finite WHOLE initial values for ANY proved
invariant with its natural dimension bound. No compactness or chosen value formula. -/
theorem finite_initialValue_image (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (hnk : n ≤ k) {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    (initialValue R H '' H).Finite := by
  classical
  apply (Set.finite_range (fun S : Finset (Fin n) =>
    initialValue (A := ModelBase.{u} n) R (coordinateCarrier S) (ULift.up (0 : ComplexModel n)))).subset
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨Φ,hsrc,hzero,S,hflat⟩ := hH.2 x
  exact ⟨S,(initialValue_eq_coordinate_model R hnk hH hx Φ hsrc hzero S hflat).symm⟩

end Initial

/-- The actual off-centre first-step branch has finite WHOLE values, by the
proved unchanged-value law and actual projection into the original cosupport. -/
theorem finite_first_off_centre_values (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ y : A, branchMultiplicity hH y ≤ r)
    (hatt : {y : A | r ≤ branchMultiplicity hH y}.Nonempty)
    {π : D → A} (hπ : IsBlowupAlong n {y | r ≤ branchMultiplicity hH y} π) :
    (((canonicalInvariant n).inv (originalMarkedIdeal H) (.step .refl _ π hπ)) ''
      {z : D | z ∈ (geoTransformAlong (originalMarkedIdeal H) (.step .refl _ π hπ)).cosupp ∧
        ¬ r ≤ branchMultiplicity hH (π z)}).Finite := by
  let M := originalMarkedIdeal H
  let R := canonicalInvariant n
  let C : Set A := {y | r ≤ branchMultiplicity hH y}
  let T : BlowupTower A D := .step .refl C π hπ
  have hdom : IsInvDomain n M := isInvDomain_originalMarkedIdeal hH
  have hmax := (canonicalInitialMaximum_eq_highest_stratum hn hH hr hbound hatt).symm
  have hcan : IsCanonical M (R.inv M) T := ⟨trivial,Or.inr hmax⟩
  have htest := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
  apply (finite_initialValue_image R (Nat.le_refl n) hH).subset
  rintro _ ⟨z,⟨hz,hzC⟩,rfl⟩
  have hp := StepOneWellFounded.proj_mem_cosupp_step hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent .refl C π hπ htest hz
  have hcos : M.cosupp = H := HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hH.1 []
  have hpH : π z ∈ H := by
    change π z ∈ M.cosupp at hp
    rwa [hcos] at hp
  have hv := (R.isInvValue.decrease M hdom .refl C π hπ trivial hatt hmax z hz).2 hzC
  exact ⟨π z,hpH,hv.symm⟩

/-- The whole first-step canonical value image is finite. Actual original
geometry internally chooses the SAME entire coordinate model and its blowup. -/
theorem finite_first_canonical_value_image (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ y : A, branchMultiplicity hH y ≤ r)
    (hatt : {y : A | r ≤ branchMultiplicity hH y}.Nonempty)
    {π : D → A} (hπ : IsBlowupAlong n {y | r ≤ branchMultiplicity hH y} π) :
    (((canonicalInvariant n).inv (originalMarkedIdeal H) (.step .refl _ π hπ)) ''
      (geoTransformAlong (originalMarkedIdeal H) (.step .refl _ π hπ)).cosupp).Finite := by
  classical
  obtain ⟨x,hx⟩ := hatt
  have hcard : (lastCoordinates (n := n) r).card = r := by
    obtain ⟨Φ,_,hzero,_,hflatH⟩ := exists_highest_stratum_branch_adapted_coordinates hH hbound hx
    have hflat : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ lastCoordinates r, flatCoord Φ i y = 0 := by
      simpa only [lastCoordinates,Finset.mem_filter,Finset.mem_univ,true_and] using hflatH
    exact (branchMultiplicity_eq_card hH Φ hzero (lastCoordinates r) hflat).symm.trans
      ((hbound x).antisymm hx)
  obtain ⟨F,hFtop,hFchart,hFcm,σ,hσ⟩ := exists_highest_stratum_blowup
    (modelNC.{u} r) hr (model_bound r hcard)
  let := hFtop
  let := hFchart
  let := hFcm
  have hσ' : IsBlowupAlong n (entireCentre (n-r)) σ := by
    rw [← model_highest_eq_centre.{u} r hcard]
    exact hσ
  have hfibre := finite_coordinate_first_fibre_values (D := CMfd.of (n := n) F) hn hr hcard hσ'
  have hoff := finite_first_off_centre_values hn hH hr hbound ⟨x,hx⟩ hπ
  apply (hfibre.union hoff).subset
  rintro _ ⟨z,hz,rfl⟩
  by_cases hzC : r ≤ branchMultiplicity hH (π z)
  · left
    obtain ⟨w,hw0,hwcos,hvalue⟩ := exists_highest_chart_entire_canonical_value
      (F := CMfd.of (n := n) F) hn hH hr hbound hcard hπ hσ' z hz hzC
    exact ⟨w,⟨hwcos,hw0⟩,hvalue.symm⟩
  · right
    exact ⟨z,⟨hz,hzC⟩,rfl⟩

/-- A nonempty ENTIRE first transformed cosupport internally attains its WHOLE
canonicalInvariant n maximum. No compactness or desired maximum certificate. -/
theorem exists_first_canonical_whole_maximum (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ y : A, branchMultiplicity hH y ≤ r)
    (hatt : {y : A | r ≤ branchMultiplicity hH y}.Nonempty)
    {π : D → A} (hπ : IsBlowupAlong n {y | r ≤ branchMultiplicity hH y} π)
    (hne : (geoTransformAlong (originalMarkedIdeal H) (.step .refl _ π hπ)).cosupp.Nonempty) :
    ∃ z ∈ (geoTransformAlong (originalMarkedIdeal H) (.step .refl _ π hπ)).cosupp,
      ∀ y ∈ (geoTransformAlong (originalMarkedIdeal H) (.step .refl _ π hπ)).cosupp,
        (canonicalInvariant n).inv (originalMarkedIdeal H) (.step .refl _ π hπ) y ≤
          (canonicalInvariant n).inv (originalMarkedIdeal H) (.step .refl _ π hπ) z := by
  classical
  let f := (canonicalInvariant n).inv (originalMarkedIdeal H) (.step .refl _ π hπ)
  let C := (geoTransformAlong (originalMarkedIdeal H) (.step .refl _ π hπ)).cosupp
  have hfinite : (f '' C).Finite := finite_first_canonical_value_image hn hH hr hbound hatt hπ
  obtain ⟨z₀,hz₀⟩ := hne
  have hzmem : f z₀ ∈ hfinite.toFinset := by
    apply hfinite.mem_toFinset.mpr
    exact ⟨z₀,hz₀,rfl⟩
  obtain ⟨a,ha,hamax⟩ := Finset.exists_max_image hfinite.toFinset id ⟨f z₀,hzmem⟩
  obtain ⟨z,hz,hza⟩ := hfinite.mem_toFinset.mp ha
  refine ⟨z,hz,fun y hy => ?_⟩
  have hymem : f y ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr ⟨y,hy,rfl⟩
  exact (hamax (f y) hymem).trans_eq hza.symm

/-- From actual original NC geometry, the first canonical test tower is terminal
or internally produces a genuine SECOND blowup of its ENTIRE FULL maximum. -/
theorem first_canonical_step_terminal_or_second (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ y : A, branchMultiplicity hH y ≤ r)
    (hatt : {y : A | r ≤ branchMultiplicity hH y}.Nonempty)
    {π : D → A} (hπ : IsBlowupAlong n {y | r ≤ branchMultiplicity hH y} π) :
    IsGeoResolution (originalMarkedIdeal H) (.step .refl _ π hπ) ∨
      ∃ C : Set D, C.Nonempty ∧ C = ResolutionDriver.maxLocus
        ((canonicalInvariant n).inv (originalMarkedIdeal H) (.step .refl _ π hπ))
        (geoTransformAlong (originalMarkedIdeal H) (.step .refl _ π hπ)).cosupp ∧
        ∃ F : CMfd.{u} n, ∃ σ : F → D, ∃ hσ : IsBlowupAlong n C σ,
          IsGeoTestTower (originalMarkedIdeal H) (.step (.step .refl _ π hπ) C σ hσ) ∧
          IsCanonical (originalMarkedIdeal H) ((canonicalInvariant n).inv (originalMarkedIdeal H))
            (.step (.step .refl _ π hπ) C σ hσ) := by
  classical
  let M := originalMarkedIdeal H
  let R := canonicalInvariant n
  let T : BlowupTower A D := .step .refl _ π hπ
  have hdom : IsInvDomain n M := isInvDomain_originalMarkedIdeal hH
  have hmax := (canonicalInitialMaximum_eq_highest_stratum hn hH hr hbound hatt).symm
  have hcan : IsCanonical M (R.inv M) T := ⟨trivial,Or.inr hmax⟩
  have htest := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
  by_cases hne : (geoTransformAlong M T).cosupp.Nonempty
  · right
    obtain ⟨z,hz,hzmax⟩ := exists_first_canonical_whole_maximum hn hH hr hbound hatt hπ hne
    let C := ResolutionDriver.maxLocus (R.inv M T) (geoTransformAlong M T).cosupp
    have hCne : C.Nonempty := ⟨z,hz,hzmax⟩
    have hC := R.isInvValue.isAdmissibleCentre_maxLocus hdom T hcan htest
    have hCint : interior C = ∅ :=
      ResolutionInvariantDriver.interior_maxLocus_eq_empty hdom T htest (R.inv M T)
    obtain ⟨F,hFtop,hFchart,hFcm,σ,hσ⟩ := BlowupExistence.exists_isBlowupAlong C hC.1 hCint
    let := hFtop
    let := hFchart
    let := hFcm
    exact ⟨C,hCne,rfl,CMfd.of (n := n) F,σ,hσ,⟨htest,hC⟩,⟨hcan,Or.inr rfl⟩⟩
  · exact Or.inl ⟨htest,not_nonempty_iff_eq_empty.mp hne⟩

end
end Hironaka.HironakaNormalCrossingsFirstStepFiniteValues
