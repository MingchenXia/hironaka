/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsDiagonalLiftOrbits
import Hironaka.Analytic.TowerPreimageCompact

/-! # Whole maxima at every actual homogeneous canonical prefix

Exact-prefix automorphism induction retains EMPTY historical positions.
Actual homotheties move every whole value to a fixed proper compact preimage.
No terminal or no-empty-prefix uniqueness is applied to arbitrary prefixes.
Blueprint: `hironaka-homogeneous-canonical-tower-maxima-extension.tex`.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaHomogeneousCanonicalTowerMaxima

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerIsomorphism BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionInvariantSeq
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsMarkedAdmissibility HironakaNormalCrossingsBiholomorphicMultiplicity
  HironakaNormalCrossingsTotalIdeal
  HironakaNormalCrossingsInitialFullMaximum HironakaNormalCrossingsFirstStepChartHistory
  HironakaNormalCrossingsDiagonalLiftOrbits MarkedIdealBiholomorphism

noncomputable section
variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ] {X Y : CMfd.{u} n}

/-- A genuine whole-record/history automorphism preserves the actual cosupport
and the ENTIRE value, with no present-data surrogate. -/
theorem canonical_automorphism_value (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ)
    (M : MarkedIdeal n X) (hdom : IsInvDomain k M)
    (Φ : X ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (hM : MarkedIdeal.pullback Φ M = M) (T : BlowupTower X Y)
    (hcan : IsCanonical M (R.inv M) T)
    (χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y)
    (hiso : IsTowerIso Φ T T χ) (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) :
    χ y ∈ (geoTransformAlong M T).cosupp ∧ R.inv M T (χ y) = R.inv M T y := by
  have ht := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
  have hcos := BlowupTowerIsomorphism.IsTowerIso.cosupp_geoTransformAlong Φ
    hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent hiso ht
  rw [hM] at hcos
  have hyχ : χ y ∈ (geoTransformAlong M T).cosupp :=
    (congrArg (fun S => y ∈ S) hcos).mp hy
  have hv := R.isInvValue.towerIso Φ M hdom T T χ hiso hcan y hyχ
  rw [hM] at hv
  exact ⟨hyχ,hv.symm⟩

/-- The base automorphism lifts along the EXACT actual canonical history.
Both empty and whole-maximum positions are retained by induction. -/
theorem exists_canonical_tower_automorphism (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ)
    (M : MarkedIdeal n X) (hdom : IsInvDomain k M)
    (Φ : X ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (hM : MarkedIdeal.pullback Φ M = M) (T : BlowupTower X Y)
    (hcan : IsCanonical M (R.inv M) T) :
    ∃ χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y, IsTowerIso Φ T T χ := by
  revert hcan
  induction T with
  | refl => exact fun _ => ⟨Φ,.refl⟩
  | @step Y Z T C π hπ ih =>
    rintro ⟨hcan,hC⟩
    obtain ⟨χ,hiso⟩ := ih hcan
    have ht := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
    have hcos := BlowupTowerIsomorphism.IsTowerIso.cosupp_geoTransformAlong Φ
      hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent hiso ht
    rw [hM] at hcos
    have hvalues (p : Y) (hp : χ p ∈ (geoTransformAlong M T).cosupp) :
        R.inv M T p = R.inv M T (χ p) := by
      have hv := R.isInvValue.towerIso Φ M hdom T T χ hiso hcan p hp
      simpa only [hM] using hv
    have hCC : χ ⁻¹' C = C := by
      rcases hC with hC | hC
      · simp only [hC,preimage_empty]
      · rw [hC]
        have hh := ResolutionInvariantSegments.maxLocus_preimage_of_surjective
          (χ := (χ : Y → Y)) χ.toEquiv.surjective hvalues
        rw [← hcos] at hh
        exact hh.symm
    obtain ⟨χ₁,hχ₁⟩ := exists_oneStep_isTowerIso (A := Y) (B := Y) (D := Z) (F := Z) χ hπ hπ hCC
    exact ⟨χ₁,IsTowerIso.step hiso hπ hπ χ₁ (fun p => (hχ₁.proj_comm p).symm) hCC⟩

abbrev CoordinateBase (n : ℕ) : CMfd.{u} n := CMfd.of (n := n) (LiftedModel.{u} n)

def coordinateMarked (S : Finset (Fin n)) : MarkedIdeal n (CoordinateBase.{u} n) :=
  originalMarkedIdeal (A := CoordinateBase.{u} n) (coordinateCarrier S)

private theorem coordinate_domain (S : Finset (Fin n)) (hnk : n ≤ k) :
    IsInvDomain k (coordinateMarked.{u} S) := by
  have h := isInvDomain_originalMarkedIdeal (A := CoordinateBase.{u} n)
    (coordinateCarrier_isNormalCrossings.{u} S)
  refine ⟨h.isWellFormed,?_,h.one_le_d,h.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨d,hd,hreg⟩ := h.dimLE x hx
  exact ⟨d,hd.trans hnk,hreg⟩

variable {A B : CMfd.{u} n}
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


/-- Nonzero homotheties preserve the WHOLE original coordinate marked record. -/
theorem homothety_pullback_original (S : Finset (Fin n)) (c : ℂ) (hc : c ≠ 0) :
    MarkedIdeal.pullback (diagonalEquiv.{u} (fun _ : Fin n => c) (fun _ => hc)) (coordinateMarked S) =
      coordinateMarked.{u} S := by
  change MarkedIdeal.pullback (diagonalEquiv.{u} (fun _ : Fin n => c) (fun _ => hc))
    (originalMarkedIdeal (A := CoordinateBase.{u} n) (coordinateCarrier S)) = _
  rw [original_pullback_diffeomorph (A := CoordinateBase.{u} n) (B := CoordinateBase.{u} n)
    _ (coordinateCarrier_isNormalCrossings.{u} S),diagonal_preimage_carrier]
  rfl

/-- The lifted closed unit ball, an actual fixed compact base set. -/
def baseBall : Set (LiftedModel.{u} n) :=
  (fun v : ComplexModel n => (ULift.up v : LiftedModel.{u} n)) '' Metric.closedBall 0 1

private theorem baseBall_isCompact : IsCompact (baseBall.{u} (n := n)) :=
  (isCompact_closedBall (0 : ComplexModel n) 1).image continuous_uliftUp

/-- The compact representative set is PRODUCED from actual proper preimages;
whole values are moved by actual full-history homothety lifts. -/
theorem exists_compact_value_representatives
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    (S : Finset (Fin n)) {Y : CMfd.{u} n} (T : BlowupTower (CoordinateBase.{u} n) Y)
    (hcan : IsCanonical (coordinateMarked S) (R.inv (coordinateMarked S)) T) :
    ∃ K : Set Y, IsCompact K ∧ K ⊆ (geoTransformAlong (coordinateMarked S) T).cosupp ∧
      ∀ y ∈ (geoTransformAlong (coordinateMarked S) T).cosupp,
        ∃ y' ∈ K, R.inv (coordinateMarked S) T y' = R.inv (coordinateMarked S) T y := by
  let M := coordinateMarked.{u} S
  have hdom := coordinate_domain.{u} S hnk
  have htest := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
  let K := T.proj ⁻¹' baseBall ∩ (geoTransformAlong M T).cosupp
  refine ⟨K,TowerPreimageCompact.isCompact_preimage_inter_cosupp hdom T htest baseBall_isCompact,
    inter_subset_right,?_⟩
  intro y hy
  let v := (T.proj y).down
  let t : ℝ := 1 / (‖v‖ + 1)
  let c : ℂ := t
  have ht : 0 < t := by dsimp [t]; positivity
  have hc : c ≠ 0 := by
    change (t : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt ht)
  let Φ := diagonalEquiv.{u} (fun _ : Fin n => c) (fun _ => hc)
  have hM : MarkedIdeal.pullback Φ M = M := homothety_pullback_original S c hc
  obtain ⟨χ,hiso⟩ := exists_canonical_tower_automorphism R M hdom Φ hM T hcan
  obtain ⟨hyχ,hvalue⟩ := canonical_automorphism_value R M hdom Φ hM T hcan χ hiso y hy
  have hnormc : ‖c‖ = t := by
    change ‖(t : ℂ)‖ = t
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  have hnorm : ‖c • v‖ ≤ 1 := by
    rw [norm_smul,hnormc]
    dsimp [t]
    rw [one_div,mul_comm,← div_eq_mul_inv]
    exact (div_le_one (by positivity : 0 < ‖v‖+1)).mpr (by linarith)
  have hdiag : diagonal (fun _ : Fin n => c) v = c • v := by ext i; rfl
  have hproj : T.proj (χ y) = (ULift.up (c • v) : LiftedModel.{u} n) := by
    have hp := hiso.proj_comm y
    change (ULift.up (diagonal (fun _ : Fin n => c) v) : LiftedModel.{u} n) = T.proj (χ y) at hp
    exact hp.symm.trans (congrArg (fun w : ComplexModel n => (ULift.up w : LiftedModel.{u} n)) hdiag)
  refine ⟨χ y,⟨?_,hyχ⟩,hvalue⟩
  exact ⟨c • v,by simpa only [Metric.mem_closedBall,dist_zero_right] using hnorm,hproj.symm⟩

/-- Every nonempty ACTUAL homogeneous canonical prefix attains its ENTIRE
whole maximum, without compactness of the ambient manifold. -/
theorem homogeneous_maxLocus_nonempty
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    (S : Finset (Fin n)) {Y : CMfd.{u} n} (T : BlowupTower (CoordinateBase.{u} n) Y)
    (hcan : IsCanonical (coordinateMarked S) (R.inv (coordinateMarked S)) T)
    (hne : (geoTransformAlong (coordinateMarked S) T).cosupp.Nonempty) :
    (ResolutionDriver.maxLocus (R.inv (coordinateMarked S) T)
      (geoTransformAlong (coordinateMarked S) T).cosupp).Nonempty := by
  obtain ⟨K,hK,hKsub,hrep⟩ := exists_compact_value_representatives R hnk S T hcan
  have hKne : K.Nonempty := by
    obtain ⟨y,hy⟩ := hne
    obtain ⟨y',hy',_⟩ := hrep y hy
    exact ⟨y',hy'⟩
  have husc := (R.isInvValue.usc (coordinateMarked S) (coordinate_domain S hnk) T hcan).mono hKsub
  obtain ⟨x,hx,hmax⟩ := husc.exists_isMaxOn hK hKne
  refine ⟨x,hKsub hx,fun y hy => ?_⟩
  obtain ⟨y',hy',hv⟩ := hrep y hy
  exact hv.symm.trans_le (hmax y' hy')

/-- Actual whole-full-maximum successor at EVERY nonterminal homogeneous prefix.
This is not a termination assertion. -/
theorem exists_homogeneous_canonical_successor
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    (S : Finset (Fin n)) {Y : CMfd.{u} n} (T : BlowupTower (CoordinateBase.{u} n) Y)
    (hcan : IsCanonical (coordinateMarked S) (R.inv (coordinateMarked S)) T)
    (hne : (geoTransformAlong (coordinateMarked S) T).cosupp.Nonempty) :
    ∃ C : Set Y, C.Nonempty ∧ C = ResolutionDriver.maxLocus (R.inv (coordinateMarked S) T)
      (geoTransformAlong (coordinateMarked S) T).cosupp ∧
      ∃ Z : CMfd.{u} n, ∃ π : Z → Y, ∃ hπ : IsBlowupAlong n C π,
        IsGeoTestTower (coordinateMarked S) (.step T C π hπ) ∧
        IsCanonical (coordinateMarked S) (R.inv (coordinateMarked S)) (.step T C π hπ) := by
  let M := coordinateMarked.{u} S
  have hdom := coordinate_domain.{u} S hnk
  have htest := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
  let C := ResolutionDriver.maxLocus (R.inv M T) (geoTransformAlong M T).cosupp
  have hCne := homogeneous_maxLocus_nonempty R hnk S T hcan hne
  have hC := R.isInvValue.isAdmissibleCentre_maxLocus hdom T hcan htest
  have hCint : interior C = ∅ := ResolutionInvariantDriver.interior_maxLocus_eq_empty hdom T htest (R.inv M T)
  obtain ⟨Z,hZtop,hZchart,hZcm,π,hπ⟩ := BlowupExistence.exists_isBlowupAlong C hC.1 hCint
  let := hZtop
  let := hZchart
  let := hZcm
  exact ⟨C,hCne,rfl,CMfd.of (n := n) Z,π,hπ,⟨htest,hC⟩,⟨hcan,Or.inr rfl⟩⟩

end
end Hironaka.HironakaHomogeneousCanonicalTowerMaxima
