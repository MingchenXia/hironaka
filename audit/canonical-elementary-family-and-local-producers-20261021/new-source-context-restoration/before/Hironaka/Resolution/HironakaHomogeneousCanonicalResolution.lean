/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaHomogeneousCanonicalTowerMaxima

/-! # Actual finite canonical resolutions of entire coordinate original models

Every-prefix whole maxima are produced internally by actual homothety lifts.
The actual drop law and a genuine well-founded value order construct a literal
finite suffix, retaining the whole given original history. The direct actual
canonicalInvariant n consumer uses the existing WellFoundedLT (ValTy n).
Blueprint: `hironaka-homogeneous-canonical-resolution-extension.tex`.
-/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaHomogeneousCanonicalResolution

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionInvariantSeq ResolutionDriver
  HironakaHomogeneousCanonicalTowerMaxima
  HironakaNormalCrossingsMarkedAdmissibility HironakaNormalCrossingsTotalIdeal
  HironakaNormalCrossingsInitialFullMaximum

noncomputable section
variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ] {X Y Z : CMfd.{u} n}

/-- Actual new cosupport values are strictly below the attained old ENTIRE
maximum, by genuine projection and whole-invariant decrease laws. -/
theorem value_lt_old_maximum_after_blowup
    (R : ResolutionInvariantSeq.ResolutionInvariant n k Λ)
    (M : MarkedIdeal n X) (hdom : IsInvDomain k M) (T : BlowupTower X Y)
    (hcan : IsCanonical M (R.inv M) T) {x : Y}
    (hx : x ∈ maxLocus (R.inv M T) (geoTransformAlong M T).cosupp)
    (π : Z → Y) (hπ : IsBlowupAlong n (maxLocus (R.inv M T) (geoTransformAlong M T).cosupp) π) :
    ∀ z ∈ (geoTransformAlong M (.step T _ π hπ)).cosupp,
      R.inv M (.step T _ π hπ) z < R.inv M T x :=
  StepOneWellFounded.lt_of_isCanonical_step
    (CanonicalCentres.stepDrop_of_isInvValue R.isInvValue hdom) T hcan hx π hπ

private theorem coordinate_domain (S : Finset (Fin n)) (hnk : n ≤ k) :
    IsInvDomain k (coordinateMarked.{u} S) := by
  have h := isInvDomain_originalMarkedIdeal (A := CoordinateBase.{u} n)
    (coordinateCarrier_isNormalCrossings.{u} S)
  refine ⟨h.isWellFormed,?_,h.one_le_d,h.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨d,hd,hreg⟩ := h.dimLE x hx
  exact ⟨d,hd.trans hnk,hreg⟩

/-- A genuine literal finite suffix resolves the SAME original homogeneous
record after the given actual nonempty-centre canonical segment.
No incoming maximum, finite bound, terminal history or chosen model is assumed. -/
theorem exists_homogeneous_resolution_suffix [WellFoundedLT Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    (S : Finset (Fin n)) {Y : CMfd.{u} n} (T : BlowupTower (CoordinateBase.{u} n) Y)
    (hseg : IsCanonicalSegment (coordinateMarked S) (R.inv (coordinateMarked S)) T) :
    ∃ Z : CMfd.{u} n, ∃ U : BlowupTower Y Z,
      IsCanonicalSegment (coordinateMarked S) (R.inv (coordinateMarked S)) (T.append U) ∧
      IsGeoResolution (coordinateMarked S) (T.append U) := by
  let M := coordinateMarked.{u} S
  have hdom := coordinate_domain.{u} S hnk
  suffices h : ∀ a : Λ, ∀ {Y : CMfd.{u} n} (T : BlowupTower (CoordinateBase.{u} n) Y),
      IsCanonicalSegment M (R.inv M) T →
      (∀ y ∈ (geoTransformAlong M T).cosupp, R.inv M T y ≤ a) →
      ∃ Z : CMfd.{u} n, ∃ U : BlowupTower Y Z,
        IsCanonicalSegment M (R.inv M) (T.append U) ∧ IsGeoResolution M (T.append U) by
    have hcan := ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment (R.inv M) T hseg
    by_cases hne : (geoTransformAlong M T).cosupp.Nonempty
    · obtain ⟨x,hx,hmax⟩ := homogeneous_maxLocus_nonempty R hnk S T hcan hne
      exact h _ T hseg hmax
    · exact ⟨Y,.refl,hseg,R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan,
        not_nonempty_iff_eq_empty.mp hne⟩
  intro a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    intro Y T hseg ha
    have hcan := ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment (R.inv M) T hseg
    have htest := R.isInvValue.isGeoTestTower_of_isCanonical hdom T hcan
    by_cases hne : (geoTransformAlong M T).cosupp.Nonempty
    · obtain ⟨C,hCne,rfl,Z,π,hπ,htest',hcan'⟩ :=
        exists_homogeneous_canonical_successor R hnk S T hcan hne
      let C := maxLocus (R.inv M T) (geoTransformAlong M T).cosupp
      let T' := BlowupTower.step T C π hπ
      have hseg' : IsCanonicalSegment M (R.inv M) T' := ⟨hseg,hCne,rfl⟩
      by_cases hne' : (geoTransformAlong M T').cosupp.Nonempty
      · obtain ⟨z,hz,hzmax⟩ := homogeneous_maxLocus_nonempty R hnk S T' hcan' hne'
        obtain ⟨x,hx⟩ := hCne
        have hlt : R.inv M T' z < a :=
          (value_lt_old_maximum_after_blowup R M hdom T hcan hx π hπ z hz).trans_le (ha x hx.1)
        obtain ⟨W,V,hsegV,hresV⟩ := ih _ hlt T' hseg' hzmax
        let P : BlowupTower Y Z := .step .refl C π hπ
        have happend : T.append (P.append V) = T'.append V := by
          rw [← BlowupTower.append_assoc]
          rfl
        exact ⟨W,P.append V,happend.symm ▸ hsegV,happend.symm ▸ hresV⟩
      · exact ⟨Z,.step .refl C π hπ,hseg',htest',not_nonempty_iff_eq_empty.mp hne'⟩
    · exact ⟨Y,.refl,hseg,htest,not_nonempty_iff_eq_empty.mp hne⟩

/-- Actual finite full-maximum canonical resolution of each ENTIRE coordinate
original marking-one model with empty original boundary. -/
theorem exists_homogeneous_canonical_resolution [WellFoundedLT Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ) (hnk : n ≤ k)
    (S : Finset (Fin n)) :
    ∃ Y : CMfd.{u} n, ∃ T : BlowupTower (CoordinateBase.{u} n) Y,
      IsCanonicalSegment (coordinateMarked S) (R.inv (coordinateMarked S)) T ∧
      IsGeoResolution (coordinateMarked S) T := by
  obtain ⟨Y,T,hseg,hres⟩ := exists_homogeneous_resolution_suffix R hnk S .refl trivial
  exact ⟨Y,T,by simpa only [BlowupTower.refl_append] using hseg,
    by simpa only [BlowupTower.refl_append] using hres⟩

/-- Direct actual canonicalInvariant n endpoint: its genuine existing ValTy n
well-founded instance discharges termination. No caller WF certificate and no
comparison with depth n+1 is used. This concerns ENTIRE coordinate models only. -/
theorem exists_canonicalInvariant_coordinate_resolution (S : Finset (Fin n)) :
    ∃ Y : CMfd.{u} n, ∃ T : BlowupTower (CoordinateBase.{u} n) Y,
      IsCanonicalSegment (coordinateMarked S)
        ((CanonicalCentres.canonicalInvariant.{u} n).inv (coordinateMarked S)) T ∧
      IsGeoResolution (coordinateMarked S) T :=
  exists_homogeneous_canonical_resolution (CanonicalCentres.canonicalInvariant.{u} n) le_rfl S

end
end Hironaka.HironakaHomogeneousCanonicalResolution
