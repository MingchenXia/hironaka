/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaHomogeneousCanonicalResolution

/-! # Entire actual homogeneous histories over every origin neighbourhood

Actual homothety lifts represent EVERY whole prefix value over any genuine
origin neighbourhood. This identifies literal restricted full maxima and
preserves exact empty/nonempty centre slots. No scaling invariance of the
open set, current-incidence surrogate or arbitrary NC globalization is used.
Blueprint: `hironaka-homogeneous-canonical-neighbourhoods-extension.tex`.
-/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaHomogeneousCanonicalNeighbourhoods

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionInvariantSeq ResolutionDriver
  HironakaHomogeneousCanonicalTowerMaxima HironakaHomogeneousCanonicalResolution
  HironakaNormalCrossingsMarkedAdmissibility HironakaNormalCrossingsTotalIdeal
  HironakaNormalCrossingsInitialFullMaximum HironakaNormalCrossingsDiagonalLiftOrbits
  BlowupTowerIsomorphism HironakaNormalCrossingsLocalBranches MarkedIdealBiholomorphism

noncomputable section
variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- The literal origin of the entire lifted coordinate base. -/
def coordinateOrigin : CoordinateBase.{u} n := ULift.up (0 : ComplexModel n)

private theorem coordinate_domain (S : Finset (Fin n)) (hnk : n ≤ k) :
    IsInvDomain k (coordinateMarked.{u} S) := by
  have h := isInvDomain_originalMarkedIdeal (A := CoordinateBase.{u} n)
    (coordinateCarrier_isNormalCrossings.{u} S)
  refine ⟨h.isWellFormed,?_,h.one_le_d,h.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨d,hd,hreg⟩ := h.dimLE x hx
  exact ⟨d,hd.trans hnk,hreg⟩

/-- Every actual whole value is represented over ANY genuine origin
neighbourhood by an actual lift of a suitably small nonzero homothety. -/
theorem exists_value_representative_over_neighbourhood
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    (S : Finset (Fin n)) {Y : CMfd.{u} n} (T : BlowupTower (CoordinateBase.{u} n) Y)
    (hcan : IsCanonical (coordinateMarked S) (R.inv (coordinateMarked S)) T)
    (U : TopologicalSpace.Opens (CoordinateBase.{u} n)) (h0 : coordinateOrigin ∈ U)
    (y : Y) (hy : y ∈ (geoTransformAlong (coordinateMarked S) T).cosupp) :
    ∃ y' : Y, T.proj y' ∈ U ∧ y' ∈ (geoTransformAlong (coordinateMarked S) T).cosupp ∧
      R.inv (coordinateMarked S) T y' = R.inv (coordinateMarked S) T y := by
  let M := coordinateMarked.{u} S
  have hdom := coordinate_domain.{u} S hnk
  let V : Set (ComplexModel n) := (fun v => (ULift.up v : CoordinateBase.{u} n)) ⁻¹'
    (U : Set (CoordinateBase.{u} n))
  have hV : IsOpen V := U.isOpen.preimage continuous_uliftUp
  have h0V : (0 : ComplexModel n) ∈ V := h0
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
  let v := (T.proj y).down
  let a : ℝ := (ε / 2) * (1 / (‖v‖ + 1))
  let c : ℂ := a
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : c ≠ 0 := by
    change (a : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt ha)
  let Φ := diagonalEquiv.{u} (fun _ : Fin n => c) (fun _ => hc)
  have hM : MarkedIdeal.pullback Φ M = M := homothety_pullback_original S c hc
  obtain ⟨χ,hiso⟩ := exists_canonical_tower_automorphism R M hdom Φ hM T hcan
  obtain ⟨hyχ,hvalue⟩ := canonical_automorphism_value R M hdom Φ hM T hcan χ hiso y hy
  have hnormc : ‖c‖ = a := by
    change ‖(a : ℂ)‖ = a
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
  have hratio : ‖v‖ / (‖v‖ + 1) ≤ 1 :=
    (div_le_one (by positivity : 0 < ‖v‖+1)).mpr (by linarith)
  have hnorm : ‖c • v‖ < ε := by
    rw [norm_smul,hnormc]
    calc
      a * ‖v‖ = (ε/2) * (‖v‖ / (‖v‖+1)) := by dsimp [a]; ring
      _ ≤ (ε/2) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ < ε := by linarith
  have hdiag : diagonal (fun _ : Fin n => c) v = c • v := by ext i; rfl
  have hproj : T.proj (χ y) = (ULift.up (c • v) : CoordinateBase.{u} n) := by
    have hp := hiso.proj_comm y
    change (ULift.up (diagonal (fun _ : Fin n => c) v) : CoordinateBase.{u} n) = T.proj (χ y) at hp
    exact hp.symm.trans (congrArg (fun w : ComplexModel n => (ULift.up w : CoordinateBase.{u} n)) hdiag)
  refine ⟨χ y,?_,hyχ,hvalue⟩
  rw [hproj]
  exact hball (by simpa only [Metric.mem_ball,dist_zero_right] using hnorm)

/-- The literal restricted whole maximum is the exact preimage of the
ENTIRE model whole maximum, including the empty-cosupport case. -/
theorem maxLocus_restrict_eq
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    (S : Finset (Fin n)) {Y : CMfd.{u} n} (T : BlowupTower (CoordinateBase.{u} n) Y)
    (hcan : IsCanonical (coordinateMarked S) (R.inv (coordinateMarked S)) T)
    (U : TopologicalSpace.Opens (CoordinateBase.{u} n)) (h0 : coordinateOrigin ∈ U) :
    maxLocus (R.inv (MarkedIdeal.pullback (Subtype.val : U → CoordinateBase n) (coordinateMarked S))
      (restrict U T))
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → CoordinateBase n) (coordinateMarked S))
        (restrict U T)).cosupp =
    (Subtype.val : openPreimage T U → Y) ⁻¹'
      maxLocus (R.inv (coordinateMarked S) T) (geoTransformAlong (coordinateMarked S) T).cosupp := by
  let M := coordinateMarked.{u} S
  have hdom := coordinate_domain.{u} S hnk
  have htest := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
  rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict
    hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent U T htest]
  have hvalue := R.isInvValue.restrictOpen M hdom U T hcan
  ext p
  constructor
  · rintro ⟨hp,hmax⟩
    refine ⟨hp,fun y hy => ?_⟩
    obtain ⟨y',hyU,hycos,hyval⟩ := exists_value_representative_over_neighbourhood R hnk S T hcan U h0 y hy
    have hb := hmax ⟨y',hyU⟩ hycos
    rw [hvalue ⟨y',hyU⟩ hycos,hvalue p hp] at hb
    exact hyval.symm.trans_le hb
  · rintro ⟨hp,hmax⟩
    refine ⟨hp,fun q hq => ?_⟩
    rw [hvalue q hq,hvalue p hp]
    exact hmax q hq

/-- The actual next canonical centre has a nonempty literal trace exactly
when the ENTIRE actual centre is nonempty. Exact empty slots are retained. -/
theorem centreTrace_nonempty_iff
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    (S : Finset (Fin n)) {Y Z : CMfd.{u} n} (T : BlowupTower (CoordinateBase.{u} n) Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hcan : IsCanonical (coordinateMarked S) (R.inv (coordinateMarked S)) (.step T C π hπ))
    (U : TopologicalSpace.Opens (CoordinateBase.{u} n)) (h0 : coordinateOrigin ∈ U) :
    ((Subtype.val : openPreimage T U → Y) ⁻¹' C).Nonempty ↔ C.Nonempty := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,hp⟩
  · intro hCne
    rcases hcan.2 with hC | hC
    · exact (hCne.ne_empty hC).elim
    · obtain ⟨x,hx⟩ := hCne
      have hxmax := hC ▸ hx
      obtain ⟨y,hyU,hycos,hyval⟩ :=
        exists_value_representative_over_neighbourhood R hnk S T hcan.1 U h0 x hxmax.1
      refine ⟨⟨y,hyU⟩,?_⟩
      rw [hC]
      exact ⟨hycos,fun z hz => (hxmax.2 z hz).trans_eq hyval.symm⟩

/-- Weak canonical histories restrict literally, preserving the same exact
empty/full slots; the centre trace theorem separately gives nonemptiness. -/
theorem isCanonical_restrict
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    (S : Finset (Fin n)) {Y : CMfd.{u} n} (T : BlowupTower (CoordinateBase.{u} n) Y)
    (hcan : IsCanonical (coordinateMarked S) (R.inv (coordinateMarked S)) T)
    (U : TopologicalSpace.Opens (CoordinateBase.{u} n)) (h0 : coordinateOrigin ∈ U) :
    IsCanonical (MarkedIdeal.pullback (Subtype.val : U → CoordinateBase n) (coordinateMarked S))
      (R.inv (MarkedIdeal.pullback (Subtype.val : U → CoordinateBase n) (coordinateMarked S))) (restrict U T) := by
  revert hcan
  induction T with
  | refl => exact fun _ => trivial
  | @step Y Z T C π hπ ih =>
    rintro ⟨hcan,hC⟩
    refine ⟨ih hcan,?_⟩
    rcases hC with hC | hC
    · exact Or.inl (by simp only [hC,preimage_empty])
    · exact Or.inr (by rw [hC]; exact (maxLocus_restrict_eq R hnk S T hcan U h0).symm)

/-- Literal restriction preserves EVERY nonempty-centre full-maximum slot
of the given actual entire coordinate canonical segment. -/
theorem isCanonicalSegment_restrict
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    (S : Finset (Fin n)) {Y : CMfd.{u} n} (T : BlowupTower (CoordinateBase.{u} n) Y)
    (hseg : IsCanonicalSegment (coordinateMarked S) (R.inv (coordinateMarked S)) T)
    (U : TopologicalSpace.Opens (CoordinateBase.{u} n)) (h0 : coordinateOrigin ∈ U) :
    IsCanonicalSegment (MarkedIdeal.pullback (Subtype.val : U → CoordinateBase n) (coordinateMarked S))
      (R.inv (MarkedIdeal.pullback (Subtype.val : U → CoordinateBase n) (coordinateMarked S))) (restrict U T) := by
  revert hseg
  induction T with
  | refl => exact fun _ => trivial
  | @step Y Z T C π hπ ih =>
    rintro ⟨hseg,hCne,hCeq⟩
    have hcan := ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment (R.inv (coordinateMarked S)) T hseg
    have hstep : IsCanonical (coordinateMarked S) (R.inv (coordinateMarked S)) (.step T C π hπ) :=
      ⟨hcan,Or.inr hCeq⟩
    refine ⟨ih hseg,(centreTrace_nonempty_iff R hnk S T C π hπ hstep U h0).mpr hCne,?_⟩
    rw [hCeq]
    exact (maxLocus_restrict_eq R hnk S T hcan U h0).symm

/-- The SAME actual internally produced entire canonical resolution restricts
to a nonempty-centre canonical resolution over the supplied genuine neighbourhood.
No incoming resolution or common-history certificate is assumed. -/
theorem exists_common_coordinate_resolution_on_neighbourhood
    (S : Finset (Fin n)) (U : TopologicalSpace.Opens (CoordinateBase.{u} n))
    (h0 : coordinateOrigin ∈ U) :
    ∃ Y : CMfd.{u} n, ∃ T : BlowupTower (CoordinateBase.{u} n) Y,
      IsCanonicalSegment (coordinateMarked S)
        ((CanonicalCentres.canonicalInvariant.{u} n).inv (coordinateMarked S)) T ∧
      IsGeoResolution (coordinateMarked S) T ∧
      IsCanonicalSegment (MarkedIdeal.pullback (Subtype.val : U → CoordinateBase n) (coordinateMarked S))
        ((CanonicalCentres.canonicalInvariant.{u} n).inv
          (MarkedIdeal.pullback (Subtype.val : U → CoordinateBase n) (coordinateMarked S))) (restrict U T) ∧
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U → CoordinateBase n) (coordinateMarked S)) (restrict U T) := by
  obtain ⟨Y,T,hseg,hres⟩ := exists_canonicalInvariant_coordinate_resolution.{u} S
  have hdom := coordinate_domain.{u} S (le_refl n)
  exact ⟨Y,T,hseg,hres,isCanonicalSegment_restrict (CanonicalCentres.canonicalInvariant n) le_rfl S T hseg U h0,
    MarkedIdealRestrictOpen.isGeoResolution_restrict U hdom.isWellFormed.isClosedSubmanifold_N
      hdom.isWellFormed.isCoherent hres⟩

end
end Hironaka.HironakaHomogeneousCanonicalNeighbourhoods
