import Hironaka.Invariant.StepOneSeq

set_option autoImplicit false

/-!
# Actual canonicality reflects from a whole-cosupport open

The input history is an actual ordinary test tower. Its restricted canonical
history on an open containing the ENTIRE initial cosupport produces whole
canonicality by literal prefix induction. The previous whole prefix is proved
canonical before restrictOpen is invoked; empty centres are reflected using
their actual containment in the current cosupport. Nothing is compressed.

This generic transport theorem does not select a natural future phase or add
a caller test/canonical certificate to an original-input algorithm. The
natural birth-window application must internally produce its whole-window
remainder test history from actual phase extension and test locality.

Blueprint: hironaka-original-nc-canonical-open-reflection-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v

namespace Hironaka.HironakaOriginalNCCanonicalOpenReflection

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

private theorem centre_eq_maxLocus_of_open_cover
    {D : Type u} {Λ : Type v} [LinearOrder Λ]
    (O s C : Set D) (f : D → Λ) (g : O → Λ)
    (hs : s ⊆ O) (hC : C ⊆ s)
    (hVal : ∀ p : O, p.val ∈ s → g p = f p.val)
    (hLocal : (Subtype.val : O → D) ⁻¹' C =
      ResolutionDriver.maxLocus g ((Subtype.val : O → D) ⁻¹' s)) :
    C = ResolutionDriver.maxLocus f s := by
  ext y
  constructor
  · intro hyC
    let p : O := ⟨y, hs (hC hyC)⟩
    have hp : p ∈ ResolutionDriver.maxLocus g ((Subtype.val : O → D) ⁻¹' s) := by
      rw [← hLocal]
      exact hyC
    refine ⟨hC hyC, ?_⟩
    intro z hzs
    let pz : O := ⟨z, hs hzs⟩
    have hle := hp.2 pz hzs
    rw [hVal pz hzs, hVal p (hC hyC)] at hle
    exact hle
  · intro hy
    let p : O := ⟨y, hs hy.1⟩
    have hp : p ∈ ResolutionDriver.maxLocus g ((Subtype.val : O → D) ⁻¹' s) := by
      refine ⟨hy.1, ?_⟩
      intro pz hpz
      rw [hVal pz hpz, hVal p hy.1]
      exact hy.2 pz.val hpz
    have hpC : p ∈ (Subtype.val : O → D) ⁻¹' C := by
      rw [hLocal]
      exact hp
    exact hpC

variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual ordinary testness and an actual restricted canonical history on an
open containing the WHOLE cosupport produce canonicality of the SAME whole
tower. Canonicality of each preceding whole prefix is derived BEFORE its
restrictOpen value identity is used. No compactness or empty history is needed. -/
theorem isCanonical_of_restrict_cosupport_cover
    {k : ℕ} {Λ : Type v} [LinearOrder Λ]
    (V : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    (B : MarkedIdeal n X) (hDom : IsInvDomain k B)
    (U : Opens X) (hCover : B.cosupp ⊆ U)
    {Y : CMfd.{u} n} (P : BlowupTower X Y) (hP : IsGeoTestTower B P)
    (hLocal : IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) B)
      (V.inv (MarkedIdeal.pullback (Subtype.val : U → X) B)) (restrict U P)) :
    IsCanonical B (V.inv B) P := by
  revert hP hLocal
  induction P with
  | refl => intro _hP _hLocal; trivial
  | @step Y Z P C π hπ ih =>
    intro hTest hLocal
    obtain ⟨hP, hCentre⟩ : IsGeoTestTower B P ∧
      (geoTransformAlong B P).IsAdmissibleCentre C := hTest
    have hLocalP := hLocal.1
    have hLocalC := hLocal.2
    have hCanP : IsCanonical B (V.inv B) P := ih hP hLocalP
    have hCurrentCover : (geoTransformAlong B P).cosupp ⊆ openPreimage P U := by
      intro y hy
      exact hCover (TransformOffCentre.cosupp_geoTransformAlong_subset B
        hDom.isWellFormed.isClosedSubmanifold_N hDom.isWellFormed.isCoherent P hP hy)
    have hCentreSub : C ⊆ (geoTransformAlong B P).cosupp := hCentre.2.1
    show IsCanonical B (V.inv B) P ∧
      (C = ∅ ∨ C = ResolutionDriver.maxLocus (V.inv B P) (geoTransformAlong B P).cosupp)
    refine ⟨hCanP, ?_⟩
    rcases hLocalC with hEmpty | hMax
    · left
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      let p : openPreimage P U := ⟨y, hCurrentCover (hCentreSub hy)⟩
      have hp : p ∈ (Subtype.val : openPreimage P U → Y) ⁻¹' C := hy
      rw [hEmpty] at hp
      exact hp
    · right
      have hCos : (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) B)
          (restrict U P)).cosupp =
          (Subtype.val : openPreimage P U → Y) ⁻¹' (geoTransformAlong B P).cosupp :=
        ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hDom.isWellFormed.isClosedSubmanifold_N
          hDom.isWellFormed.isCoherent U P hP
      rw [hCos] at hMax
      exact centre_eq_maxLocus_of_open_cover (openPreimage P U)
        (geoTransformAlong B P).cosupp C (V.inv B P)
        (V.inv (MarkedIdeal.pullback (Subtype.val : U → X) B) (restrict U P))
        hCurrentCover hCentreSub
        (fun p hp => V.isInvValue.restrictOpen B hDom U P hCanP p hp) hMax

end
end Hironaka.HironakaOriginalNCCanonicalOpenReflection
