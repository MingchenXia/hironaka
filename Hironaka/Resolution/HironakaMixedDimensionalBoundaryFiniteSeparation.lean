import Hironaka.Resolution.HironakaMixedDimensionalBoundaryAssembly
import Hironaka.Resolution.HironakaEmbeddedAnalytic
import Hironaka.Resolution.HironakaOriginalNCMarkedStratumBranchHistory
import Hironaka.Resolution.HironakaG4CompactWholeMonomialMaskPhase

/-!
# Finite pair separation with the same prescribed carrier

Ordinary good-part data retain incidence with both the labelled boundary and
the prescribed carrier. A literal finite induction constructs actual towers
separating a head from every tail part. Whole boundary-only datum equality
lets native and universal original-branch histories compose across the
different actual sum ideals used for individual separation steps.

This module does not resolve the separated parts or close a mixed embedded
resolution endpoint.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaMixedDimensionalBoundaryFiniteSeparation

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism NormalCrossings RestrictedIdealExtension
  RestrictEmptyTower HironakaAdmissibleSequence HironakaAdmissibleCalculus
  HironakaNormalCrossingsBoundaryTransform HironakaOriginalOldBranchOpenHistory
  HironakaOriginalNCOldStratumStrictEquality HironakaOriginalNCMarkedStratumBranchHistory
  HironakaMixedDimensionalBoundaryAssembly HironakaEmbeddedAnalytic
  HironakaSharpActualFiniteChronologicalHistory MemberInterTowerAlong MemberInterLocusAlong
open HomogenizedGlueingTower (strictAlong)

variable {n : ℕ}

/-- Ordinary good-part geometry together with incidence with the same H. -/
def IsRetainedGoodPart {X : CMfd.{u} n}
    (E : List (Set X)) (H G A : Set X) (d : ℕ) : Prop :=
  HironakaEmbeddedAnalytic.IsGoodPart n E G A d ∧ A ∩ H ⊆ G

namespace IsRetainedGoodPart

variable {X : CMfd.{u} n} {E : List (Set X)} {H G A : Set X} {d : ℕ}

/-- Both original incidence conditions give density off the whole boundary. -/
theorem subset_closure_diff_boundary (h : IsRetainedGoodPart E H G A d) :
    A ⊆ closure (A \ (H ∪ ⋃ C ∈ E, C)) := by
  refine h.1.2.2.2.2.2.trans (closure_mono fun x hx => ⟨hx.1, ?_⟩)
  rintro (hxH | hxE)
  · exact hx.2 (h.2 ⟨hx.1, hxH⟩)
  · exact hx.2 (h.1.2.2.2.2.1 ⟨hx.1, hxE⟩)

/-- Every old/born field and the actual strict-H incidence are transported. -/
theorem strictTransform (h : IsRetainedGoodPart E H G A d)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) {E' : List (Set Y)}
    (hAdm : IsAdmissibleBlowupSequence n X E G Y T.proj E')
    (hE : ∀ C ∈ E, IsClosed C) (hH : IsClosed H) :
    IsRetainedGoodPart E' (strictAlong T H) (T.proj ⁻¹' G)
      (strictTransform n T.proj A) d := by
  refine ⟨h.1.strictTransform hAdm hE, ?_⟩
  intro y hy
  exact h.2 ⟨strictTransform_subset_preimage T.contMDiff_proj.continuous h.1.isClosed hy.1,
    strictAlong_subset_preimage T hH hy.2⟩

/-- Cutting a bad set by a set containing the whole current part. -/
theorem inter (h : IsRetainedGoodPart E H G A d) {K : Set X} (hAK : A ⊆ K) :
    IsRetainedGoodPart E H (G ∩ K) A d :=
  ⟨h.1.inter hAK, fun _ hx => ⟨h.2 hx, hAK hx.1⟩⟩

end IsRetainedGoodPart

/-- The whole actual boundary-only datum is retained at every native stage. -/
theorem boundaryGeometry_geoTransformAlong {X Y : CMfd.{u} n}
    (E : List (Set X)) (T : BlowupTower X Y) :
    geoTransformAlong (boundaryGeometry E) T =
      boundaryGeometry (geoTransformAlong (boundaryGeometry E) T).E := by
  change geoTransformAlong (geometricTemplate (univ : Set X) E) T =
    geometricTemplate (univ : Set Y) (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E
  simpa only [HironakaG4CompactWholeMonomialMaskPhase.strict_univ] using
    HironakaG4CompactWholeMonomialMaskPhase.template_current (univ : Set X) E T

private theorem boundaryGeometry_wellFormed {X : CMfd.{u} n}
    {E : List (Set X)} (hE : IsSNCDivisor n E) :
    (boundaryGeometry (X := X) E).IsWellFormed :=
  ⟨⟨isClosed_univ, fun x _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
    IdealWeightPowers.isCoherent_unitIdeal, hE,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩

private theorem centresOver_mono {X : CMfd.{u} n} {F G : Set X} (hFG : F ⊆ G) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver F T → CentresOver G T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, h => ⟨centresOver_mono hFG T h.1, fun _ hx => hFG (h.2 hx)⟩

/-- One internally constructed finite tower separates the head from every
literal tail occurrence, retaining the same original branch histories. -/
theorem exists_retained_boundary_sepOne (m : ℕ) :
    ∀ {X : CMfd.{u} n} (E₀ : List (Set X)) (_hE₀ : IsSNCDivisor n E₀)
      (H : Set X) (_hH : IsBoundaryAdaptedCarrier (n := n) H E₀)
      (G : Set X) (_hG : IsClosed G) (A : Set X) (d : ℕ)
      (_hA : IsRetainedGoodPart E₀ H G A d) (L : List (Set X × ℕ)),
      L.length = m →
      (∀ p ∈ L, IsRetainedGoodPart E₀ H G p.1 p.2) →
      (∀ p ∈ L, A ∩ p.1 ⊆ G) →
      ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
        let D := boundaryGeometry (X := X) E₀
        let E := (geoTransformAlong D T).E
        IsGeoTestTower D T ∧ IsOriginalBranchTestTower D H T ∧
        CentresOver G T ∧ IsSNCDivisor n E ∧
        IsBoundaryAdaptedCarrier (n := n) (strictAlong T H) E ∧
        ∀ p ∈ L, Disjoint (strictTransform n T.proj A) (strictTransform n T.proj p.1) := by
  induction m with
  | zero =>
      intro X E₀ hE₀ H hH G _hG A d _hA L hL _hgood _hinter
      have hNil : L = [] := List.length_eq_zero_iff.mp hL
      subst L
      refine ⟨X, .refl, trivial, ?_, trivial, hE₀, hH, ?_⟩
      · intro U B _hB _hUnion
        trivial
      · intro p hp
        exact False.elim (List.not_mem_nil hp)
  | succ m ih =>
      intro X E₀ hE₀ H hH G hG A d hA L hL hgood hinter
      obtain ⟨q, L', rfl⟩ := List.exists_cons_of_length_eq_add_one hL
      have hL' : L'.length = m := by simpa using hL
      have hq := hgood q (List.mem_cons_self ..)
      have hAq : A ∩ q.1 ⊆ G := hinter q (List.mem_cons_self ..)
      let J := sumIdeal (vanishingIdeal (n := n) A) (vanishingIdeal (n := n) q.1)
      let M : MarkedIdeal n X := ⟨univ, E₀, J, 1⟩
      have hJ : J.IsCoherent :=
        isCoherent_sumIdeal (CartanIrreducible.cartanCoherence A hA.1.1)
          (CartanIrreducible.cartanCoherence q.1 hq.1.1)
      obtain ⟨Y₁, P, hResP, _hCanP, hHistoryP, hAdmP, hSNC₁, _hpb, _hsupp,
          _hsuppZ, _hIso, hAdapt₁, hDisj₁⟩ :=
        exists_retained_boundary_pair_separation hA.1.1 hq.1.1 hA.1.interior_eq_empty
          (hA.1.2.1.inter_right hq.1.isClosed)
          (hA.1.subset_closure_diff_of_inter_subset hAq)
          (hq.1.subset_closure_diff_of_inter_subset (by rw [inter_comm]; exact hAq)) hE₀ hH
      have hDP : IsGeoTestTower (boundaryGeometry E₀) P :=
        boundaryGeometry_test M hE₀ P hResP.1
      have hDHistoryP : IsOriginalBranchTestTower (boundaryGeometry E₀) H P :=
        boundaryGeometry_original_history M H P hHistoryP
      let E₁ := (geoTransformAlong (boundaryGeometry E₀) P).E
      let H₁ := strictAlong P H
      have hEeq : (geoTransformAlong M P).E = E₁ :=
        MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
          (𝔪 := M) (𝔫 := boundaryGeometry E₀) rfl P
      have hSNC₁' : IsSNCDivisor n E₁ := hEeq ▸ hSNC₁
      have hAdapt₁' : IsBoundaryAdaptedCarrier (n := n) H₁ E₁ := hEeq ▸ hAdapt₁
      have hAdmP' : IsAdmissibleBlowupSequence n X E₀ G Y₁ P.proj E₁ := by
        rw [← hEeq]
        exact HironakaAdmissibleSequence.IsAdmissibleBlowupSequence.mono hAq hAdmP
      have hCos : M.cosupp = A ∩ q.1 := by
        change GermIdealOrder.cosupport n univ J 1 = A ∩ q.1
        rw [GermIdealOrder.cosupport_one
          (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hg),
          univ_inter]
        exact HironakaSeparation.zeroLocus_sumIdeal_vanishingIdeal hA.1.isClosed hq.1.isClosed
      have hOverP : CentresOver G P := by
        have hSmall := centresOver_cosupp M
          ⟨isClosed_univ, fun x _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩
          hJ P hResP.1
        rw [hCos] at hSmall
        exact centresOver_mono hAq P hSmall
      let A₁ := strictTransform n P.proj A
      let L₁ : List (Set Y₁ × ℕ) := L'.map fun p => (strictTransform n P.proj p.1, p.2)
      have hA₁ : IsRetainedGoodPart E₁ H₁ (P.proj ⁻¹' G) A₁ d :=
        hA.strictTransform P hAdmP' hE₀.1 hH.1
      have hgood₁ : ∀ p ∈ L₁, IsRetainedGoodPart E₁ H₁ (P.proj ⁻¹' G) p.1 p.2 := by
        intro p hp
        obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
        exact (hgood p₀ (List.mem_cons_of_mem _ hp₀)).strictTransform P hAdmP' hE₀.1 hH.1
      have hinter₁ : ∀ p ∈ L₁, A₁ ∩ p.1 ⊆ P.proj ⁻¹' G := by
        intro p hp
        obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
        intro y hy
        exact hinter p₀ (List.mem_cons_of_mem _ hp₀)
          ⟨strictTransform_subset_preimage P.contMDiff_proj.continuous hA.1.isClosed hy.1,
            strictTransform_subset_preimage P.contMDiff_proj.continuous
              (hgood p₀ (List.mem_cons_of_mem _ hp₀)).1.isClosed hy.2⟩
      obtain ⟨Y₂, Q, hDQ, hDHistoryQ, hOverQ, hSNC₂, hAdapt₂, hDisj₂⟩ :=
        ih E₁ hSNC₁' H₁ hAdapt₁' (P.proj ⁻¹' G) (hG.preimage P.contMDiff_proj.continuous)
          A₁ d hA₁ L₁ (by simp [L₁, hL']) hgood₁ hinter₁
      have hQCurrent : IsGeoTestTower (geoTransformAlong (boundaryGeometry E₀) P) Q := by
        rw [boundaryGeometry_geoTransformAlong E₀ P]
        exact hDQ
      have hHistoryCurrent : IsOriginalBranchTestTower
          (geoTransformAlong (boundaryGeometry E₀) P) (strictAlong P H) Q := by
        rw [boundaryGeometry_geoTransformAlong E₀ P]
        exact hDHistoryQ
      have hAppendTest : IsGeoTestTower (boundaryGeometry E₀) (P.append Q) :=
        (isGeoTestTower_append_iff (boundaryGeometry E₀) P Q).mpr ⟨hDP, hQCurrent⟩
      have hAppendHistory : IsOriginalBranchTestTower (boundaryGeometry E₀) H (P.append Q) :=
        original_history_append_native (boundaryGeometry E₀) (boundaryGeometry_wellFormed hE₀)
          P Q hDP hDHistoryP hHistoryCurrent
      have hFinalE : (geoTransformAlong (boundaryGeometry E₀) (P.append Q)).E =
          (geoTransformAlong (boundaryGeometry E₁) Q).E := by
        rw [geoTransformAlong_append, boundaryGeometry_geoTransformAlong E₀ P]
      refine ⟨Y₂, P.append Q, hAppendTest, hAppendHistory,
        (centresOver_append_iff G P Q).mpr ⟨hOverP, hOverQ⟩, ?_, ?_, ?_⟩
      · rw [hFinalE]
        exact hSNC₂
      · rw [MemberInterLocusAlong.strictAlong_append, hFinalE]
        exact hAdapt₂
      · intro p hp
        rw [BlowupTower.proj_append,
          StrictTransformComposition.strictTransform_comp P.contMDiff_proj Q.contMDiff_proj,
          StrictTransformComposition.strictTransform_comp P.contMDiff_proj Q.contMDiff_proj]
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact (hDisj₁.preimage Q.proj).mono
            (strictTransform_subset_preimage Q.contMDiff_proj.continuous isClosed_closure)
            (strictTransform_subset_preimage Q.contMDiff_proj.continuous isClosed_closure)
        · exact hDisj₂ _ (List.mem_map_of_mem hp')

end

end Hironaka.HironakaMixedDimensionalBoundaryFiniteSeparation
