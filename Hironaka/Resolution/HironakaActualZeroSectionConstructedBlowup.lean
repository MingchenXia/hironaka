/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualZeroSectionCentreGeometry
import Hironaka.Resolution.HironakaActualZeroSectionBlowupComparison

/-!
# The actual ambient blowup and whole comparison, from the base blowup alone

The target is the existing BlowupConstruction.BlowupSpace with its genuine
constructed topology and atlas. Its centre's geometry and genuine universal
property are produced internally before applying the prescribed-pair result.
No caller ambient blowup or image-centre/strict-carrier certificate.
Blueprint: hironaka-actual-zero-section-constructed-blowup-extension.tex.
Source-only; no kernel acceptance is claimed.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualZeroSectionConstructedBlowup

noncomputable section

open Hironaka.BlowupSequences HironakaRelativeNormalIdeal
  HironakaActualZeroSectionCentreGeometry HironakaActualZeroSectionBlowupComparison
  BlowupStrictSubmanifold

/-- Grounded OUTPUT for the literal actual constructed ambient blowup.
The internally derived image-centre fact fixes its actual topology/atlas.
This is never a caller comparison or ambient-blowup certificate. -/
def actualConstructedZeroSectionComparisonFor {d t : ℕ} {B : Type}
    [TopologicalSpace B] [ChartedSpace (ComplexModel d) B] [IsComplexManifold d B]
    (C : Set (ComplexModel d)) (p : B → ComplexModel d)
    (hC : IsClosedSubmanifold d C) : Prop :=
  letI : Fact (IsClosedSubmanifold (d+t) ((tangentInclusion d t) '' C)) :=
    ⟨actual_zeroSection_image_closedSubmanifold hC⟩
  let π := BlowupConstruction.blowupProj (d+t) ((tangentInclusion d t) '' C)
  IsBlowupAlong (d+t) ((tangentInclusion d t) '' C) π ∧
    ∃ cs : ChartedSpace (ComplexModel d)
        (geoStrictTransform π ((tangentInclusion d t) '' C) (complexCoordinatePlane (d+t) d)),
      @IsComplexManifold d _ _ cs ∧ actualZeroSectionComparisonFor C p π cs

/-- ONLY the original base blowup is input: internally construct the genuine
ambient blowup, the whole strict carrier's atlas, actual biholomorphism,
both commutations, whole range and entire exceptional ideal-sheaf identity. -/
theorem exists_actual_constructed_zeroSection_blowup_comparison {d t : ℕ} {B : Type}
    [TopologicalSpace B] [ChartedSpace (ComplexModel d) B] [IsComplexManifold d B]
    {C : Set (ComplexModel d)} {p : B → ComplexModel d}
    (hp : IsBlowupAlong d C p) :
    actualConstructedZeroSectionComparisonFor (t := t) C p hp.1 := by
  let : Fact (IsClosedSubmanifold (d+t) ((tangentInclusion d t) '' C)) :=
    ⟨actual_zeroSection_image_closedSubmanifold hp.1⟩
  have hπ : IsBlowupAlong (d+t) ((tangentInclusion d t) '' C)
      (BlowupConstruction.blowupProj (d+t) ((tangentInclusion d t) '' C)) :=
    BlowupConstruction.isBlowupAlong_blowupProj
      (actual_zeroSection_image_interior_eq_empty d t C hp.2.1)
  exact ⟨hπ, exists_actual_zeroSection_blowup_comparison hp hπ⟩

end
end Hironaka.HironakaActualZeroSectionConstructedBlowup
