/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsCanonicalInitialStep
import Hironaka.Blowup.BlowupUniqueness
import Hironaka.Invariant.ResolutionInvariantSegments

/-! # Actual one-step NC chart history comparison

The blowup universal property constructs actual one-step history isomorphisms.
Highest-stratum NC charts identify BOTH the whole centre and original carrier.
The actual ambient-dimensional canonical value comparison retains the literal
restricted one-step histories; no finite orbit/whole-value image is asserted.
Blueprint: `hironaka-normal-crossings-first-step-chart-history-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsFirstStepChartHistory

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsBoundarySeparation
  HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsTotalIdeal HironakaNormalCrossingsMarkedAdmissibility
  HironakaNormalCrossingsBiholomorphicMultiplicity HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsActualResidual BlowupFlatCoordinates BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres ResolutionInvariantSpec
  BlowupTowerIsomorphism MarkedIdealBiholomorphism HironakaNormalCrossingsInitialFullMaximum

  HironakaNormalCrossingsCanonicalInitialStep BlowupTowerTransforms

noncomputable section
variable {n : ℕ} {A B D F : CMfd.{u} n}

/-- Actual universal comparison constructs the whole one-step history lift. -/
theorem exists_oneStep_isTowerIso
    (χ : A ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ B)
    {C : Set A} {K : Set B} {π : D → A} {σ : F → B}
    (hπ : IsBlowupAlong n C π) (hσ : IsBlowupAlong n K σ)
    (hC : χ ⁻¹' K = C) :
    ∃ e : D ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ F,
      IsTowerIso χ (.step .refl C π hπ) (.step .refl K σ hσ) e := by
  have hσ' := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse
    χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply hσ
  rw [hC] at hσ'
  obtain ⟨e,f,he,hf,hσe,_,hfe,hef⟩ :=
    BlowupUniqueness.exists_biholomorphism_over hπ hσ'
  let E : D ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ F :=
    ⟨⟨e,f,congrFun hfe,congrFun hef⟩,he,hf⟩
  refine ⟨E,IsTowerIso.step .refl hπ hσ E ?_ hC⟩
  intro p
  have hp : χ.symm (σ (e p)) = π p := congrFun hσe p
  exact (χ.apply_symm_apply (σ (e p))).symm.trans (congrArg χ hp)

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

/-- The fixed actual coordinate centre for the last r coordinates. -/
def coordinateCentre (r : ℕ) : Set (LiftedModel.{u} n) :=
  {w | w.down ∈ complexCoordinatePlane n (n-r)}

/-- The whole original coordinate NC carrier with the last r branches. -/
def coordinateOriginal (r : ℕ) : Set (LiftedModel.{u} n) :=
  coordinateCarrier (Finset.univ.filter (fun i : Fin n => n-r ≤ i.val))

def coordinateStep {r : ℕ} {σ : F → LiftedModel.{u} n}
    (hσ : IsBlowupAlong n (coordinateCentre r) σ) :
    BlowupTower (CMfd.of (n := n) (LiftedModel.{u} n)) F := .step .refl _ σ hσ

abbrev chartOpen {x : A}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) :
    TopologicalSpace.Opens A := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩

abbrev coordinateOpen {x : A}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) :
    TopologicalSpace.Opens (LiftedModel.{u} n) :=
  liftedOpens ⟨Φ.target,Φ.isOpen_target⟩

/-- The entire centre trace is identified by the genuine chart equation. -/
theorem chart_preimage_centre {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} {x : A}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hflatC : ∀ y ∈ flatDomain Φ, r ≤ branchMultiplicity hH y ↔
      Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n (n-r)) :
    (flatDomainDiffeomorph Φ hsrc) ⁻¹'
        ((Subtype.val : coordinateOpen Φ → LiftedModel.{u} n) ⁻¹' coordinateCentre r) =
      (Subtype.val : chartOpen Φ → A) ⁻¹' {y | r ≤ branchMultiplicity hH y} := by
  ext p
  exact (hflatC p p.2).symm

/-- The whole original carrier trace, not merely the strict transform. -/
theorem chart_preimage_carrier {H : Set A} {r : ℕ} {x : A}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hflatH : ∀ y ∈ flatDomain Φ, y ∈ H ↔
      ∃ i : Fin n, n-r ≤ i.val ∧ flatCoord Φ i y = 0) :
    (flatDomainDiffeomorph Φ hsrc) ⁻¹'
        ((Subtype.val : coordinateOpen Φ → LiftedModel.{u} n) ⁻¹' coordinateOriginal r) =
      (Subtype.val : chartOpen Φ → A) ⁻¹' H := by
  ext p
  change (∃ i ∈ Finset.univ.filter (fun i : Fin n => n-r ≤ i.val), flatCoord Φ i p = 0) ↔
    (p : A) ∈ H
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using (hflatH p p.2).symm

/-- Literal original marking-one coordinate datum on the actual open target. -/
def coordinateDatum {x : A}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (r : ℕ) :
    MarkedIdeal n (coordinateOpen Φ) :=
  originalMarkedIdeal (A := CMfd.of (n := n) (coordinateOpen Φ))
    ((Subtype.val : coordinateOpen Φ → LiftedModel.{u} n) ⁻¹' coordinateOriginal r)

/-- A real coordinate history comparison; its lifted map and history isomorphism
are constructed by the universal property, not supplied as certificates. -/
structure HighestChartHistory {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (r : ℕ) (x : A)
    {π : D → A} (hπ : IsBlowupAlong n {y | r ≤ branchMultiplicity hH y} π)
    {σ : F → LiftedModel.{u} n} (hσ : IsBlowupAlong n (coordinateCentre r) σ) where
  Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)
  hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target
  hzero : Φ.toFun (chartAt (ComplexModel n) x x) = 0
  hcentre : (flatDomainDiffeomorph Φ hsrc) ⁻¹'
      ((Subtype.val : coordinateOpen Φ → LiftedModel.{u} n) ⁻¹' coordinateCentre r) =
    (Subtype.val : chartOpen Φ → A) ⁻¹' {y | r ≤ branchMultiplicity hH y}
  hcarrier : (flatDomainDiffeomorph Φ hsrc) ⁻¹'
      ((Subtype.val : coordinateOpen Φ → LiftedModel.{u} n) ⁻¹' coordinateOriginal r) =
    (Subtype.val : chartOpen Φ → A) ⁻¹' H
  lifted : CMfd.of (n := n) (openPreimage (.step .refl _ π hπ) (chartOpen Φ))
    ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (coordinateStep hσ) (coordinateOpen Φ))
  historyIso : IsTowerIso (flatDomainDiffeomorph Φ hsrc)
    (restrict (chartOpen Φ) (.step .refl _ π hπ))
    (restrict (coordinateOpen Φ) (coordinateStep hσ)) lifted

/-- The original highest-stratum geometry internally supplies the actual chart
and the actual first-step tower comparison to a fixed genuine model blowup. -/
theorem exists_highest_chart_history {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ y : A, branchMultiplicity hH y ≤ r) {x : A}
    (hx : r ≤ branchMultiplicity hH x) {π : D → A}
    (hπ : IsBlowupAlong n {y | r ≤ branchMultiplicity hH y} π)
    {σ : F → LiftedModel.{u} n} (hσ : IsBlowupAlong n (coordinateCentre r) σ) :
    Nonempty (HighestChartHistory hH r x hπ hσ) := by
  obtain ⟨Φ,hsrc,hzero,hflatC,hflatH⟩ :=
    exists_highest_stratum_branch_adapted_coordinates hH hbound hx
  have hC := chart_preimage_centre hH Φ hsrc hflatC
  have hK := chart_preimage_carrier Φ hsrc hflatH
  have hπU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ (chartOpen Φ)
  have hσV := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hσ (coordinateOpen Φ)
  obtain ⟨e,he⟩ := exists_oneStep_isTowerIso
    (A := CMfd.of (n := n) (chartOpen Φ)) (B := CMfd.of (n := n) (coordinateOpen Φ))
    (D := CMfd.of (n := n) (openPreimage (.step .refl _ π hπ) (chartOpen Φ)))
    (F := CMfd.of (n := n) (openPreimage (coordinateStep hσ) (coordinateOpen Φ)))
    (flatDomainDiffeomorph Φ hsrc) hπU hσV hC
  exact ⟨⟨Φ,hsrc,hzero,hC,hK,e,he⟩⟩

/-- The inverse chart identifies the ENTIRE original marked records, including
whole vanishing ideals, empty old boundary and marking one. -/
theorem HighestChartHistory.pullback_original {H : Set A}
    {hH : IsNormalCrossingsCarrier (n := n) H} {r : ℕ} {x : A} {π : D → A}
    {hπ : IsBlowupAlong n {y | r ≤ branchMultiplicity hH y} π}
    {σ : F → LiftedModel.{u} n} {hσ : IsBlowupAlong n (coordinateCentre r) σ}
    (Q : HighestChartHistory hH r x hπ hσ) :
    MarkedIdeal.pullback (flatDomainDiffeomorph Q.Φ Q.hsrc).symm
      (MarkedIdeal.pullback (Subtype.val : chartOpen Q.Φ → A) (originalMarkedIdeal H)) =
        coordinateDatum Q.Φ r := by
  have htrace := isNormalCrossingsCarrier_of_boundaryAdapted
    (boundaryAdapted_open (chartOpen Q.Φ) (boundaryAdapted_nil hH))
  have hset : (flatDomainDiffeomorph Q.Φ Q.hsrc).symm ⁻¹'
      ((Subtype.val : chartOpen Q.Φ → A) ⁻¹' H) =
      (Subtype.val : coordinateOpen Q.Φ → LiftedModel.{u} n) ⁻¹' coordinateOriginal r := by
    ext p
    change (flatDomainDiffeomorph Q.Φ Q.hsrc).symm p ∈
        (Subtype.val : chartOpen Q.Φ → A) ⁻¹' H ↔ _
    rw [← Q.hcarrier]
    simp
  rw [original_pullback_open hH (chartOpen Q.Φ)]
  have hi := original_pullback_diffeomorph
    (A := CMfd.of (n := n) (chartOpen Q.Φ))
    (B := CMfd.of (n := n) (coordinateOpen Q.Φ))
    (flatDomainDiffeomorph Q.Φ Q.hsrc).symm htrace
  rw [hset] at hi
  exact hi

/-- The SAME whole actual first canonical history is compared with the literal
coordinate OPEN history. The image point is actual, not an asserted orbit model. -/
theorem exists_highest_chart_history_canonical_value (hn : 0 < n) {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r)
    (hbound : ∀ y : A, branchMultiplicity hH y ≤ r) {x : A}
    (hx : r ≤ branchMultiplicity hH x) {π : D → A}
    (hπ : IsBlowupAlong n {y | r ≤ branchMultiplicity hH y} π)
    {σ : F → LiftedModel.{u} n} (hσ : IsBlowupAlong n (coordinateCentre r) σ) :
    ∃ Q : HighestChartHistory hH r x hπ hσ,
      MarkedIdeal.pullback (flatDomainDiffeomorph Q.Φ Q.hsrc).symm
        (MarkedIdeal.pullback (Subtype.val : chartOpen Q.Φ → A) (originalMarkedIdeal H)) =
          coordinateDatum Q.Φ r ∧
      ∀ p : openPreimage (.step .refl _ π hπ) (chartOpen Q.Φ),
        (p : D) ∈ (geoTransformAlong (originalMarkedIdeal H) (.step .refl _ π hπ)).cosupp →
        (canonicalInvariant n).inv (originalMarkedIdeal H) (.step .refl _ π hπ) (p : D) =
          (canonicalInvariant n).inv (coordinateDatum Q.Φ r)
            (restrict (coordinateOpen Q.Φ) (coordinateStep hσ)) (Q.lifted p) := by
  obtain ⟨Q⟩ := exists_highest_chart_history hH hbound hx hπ hσ
  refine ⟨Q,Q.pullback_original,?_⟩
  let M := originalMarkedIdeal H
  let R := canonicalInvariant n
  let U := chartOpen Q.Φ
  let T : BlowupTower A D := .step .refl _ π hπ
  let mU := MarkedIdeal.pullback (Subtype.val : U → A) M
  have hdom : IsInvDomain n M := isInvDomain_originalMarkedIdeal hH
  have hmax : {y | r ≤ branchMultiplicity hH y} =
      ResolutionDriver.maxLocus (R.inv M .refl) M.cosupp :=
    (canonicalInitialMaximum_eq_highest_stratum hn hH hr hbound ⟨x,hx⟩).symm
  have hcan : IsCanonical M (R.inv M) T := ⟨trivial,Or.inr hmax⟩
  have htest := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
  have hcosU : mU.cosupp = (Subtype.val : U → A) ⁻¹' M.cosupp :=
    MarkedIdealRestrictOpen.cosupp_pullback_val M
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        hdom.isWellFormed.isCoherent hg) U
  have hmaxU : (Subtype.val : U → A) ⁻¹' {y | r ≤ branchMultiplicity hH y} =
      ResolutionDriver.maxLocus (R.inv (X := CMfd.of (n := n) U) mU .refl) mU.cosupp := by
    rw [hmax,hcosU]
    apply (ResolutionInvariantSegments.maxLocus_preimage (Subtype.val : U → A) ?_ ?_).symm
    · intro p hp
      exact R.isInvValue.restrictOpen M hdom U .refl trivial p hp
    · refine ⟨⟨x,mem_flatDomain_self Q.Φ⟩,?_⟩
      rw [← hmax]
      exact hx
  have hcanU : IsCanonical mU (R.inv mU) (restrict U T) := ⟨trivial,Or.inr hmaxU⟩
  have htrace := isNormalCrossingsCarrier_of_boundaryAdapted
    (boundaryAdapted_open U (boundaryAdapted_nil hH))
  have hdomU : IsInvDomain n mU := by
    change IsInvDomain n (MarkedIdeal.pullback (Subtype.val : U → A) (originalMarkedIdeal H))
    rw [original_pullback_open hH U]
    exact isInvDomain_originalMarkedIdeal htrace
  intro p hp
  have hpcos : Q.lifted.symm (Q.lifted p) ∈ (geoTransformAlong mU (restrict U T)).cosupp := by
    rw [Q.lifted.symm_apply_apply]
    rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
      hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent U T htest]
    exact hp
  have hv := R.isInvValue.towerIso (flatDomainDiffeomorph Q.Φ Q.hsrc).symm
    mU hdomU (restrict (coordinateOpen Q.Φ) (coordinateStep hσ)) (restrict U T)
    Q.lifted.symm Q.historyIso.symm hcanU (Q.lifted p) hpcos
  rw [Q.pullback_original,Q.lifted.symm_apply_apply] at hv
  have hu := R.isInvValue.restrictOpen M hdom U T hcan p hp
  exact hu.symm.trans hv.symm

end
end Hironaka.HironakaNormalCrossingsFirstStepChartHistory
