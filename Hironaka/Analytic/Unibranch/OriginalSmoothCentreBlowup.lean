import Hironaka.Analytic.Unibranch.IntrinsicAnalyticCentreFiniteType
import Hironaka.Analytic.Unibranch.OriginalFiniteIdealBlowupUniversal
import Hironaka.Analytic.Unibranch.SmoothCentreModification

/-!
# Blowups of ordinary smooth centres on arbitrary ORIGINAL complex spaces

The intrinsic ideal is a unit exactly off its analytic centre. Its native
finite type and dense unit locus are derived internally from ordinary centre
geometry. The held dense finite-ideal construction then gives the SAME full
original smooth-centre blowup and an actual one-step finite modification.
No blowup, finite-type/Cartier datum, global embedding or target certificate
is an input. Empty centres and noncompact/nonpure original spaces are included.

Blueprint FIRST: `original-smooth-centre-blowup.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.OriginalSmoothCentreBlowup

open Hironaka HironakaSingularModuleSheafStalk
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreIdealModel
  HironakaIntrinsicReducedCentreOpenPullback HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace SmoothCentreModification

noncomputable section

/-- The ENTIRE actual intrinsic inclusion-stalk image is a unit precisely
off the ordinary analytic centre; no incoming ideal dictionary is required. -/
theorem intrinsic_ideal_unitLocus_eq_compl
    (X : SourceReducedComplexSpace) (C : Set X.obj.left) (hC : X.IsAnalyticSubset C) :
    {x : X.obj.left | LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf
      (intrinsicReducedCentreIdealModule X.obj.left C)
      (intrinsicReducedCentreIdealInclusion X.obj.left C) x) = ⊤} = Cᶜ := by
  ext x
  change intrinsicCentreStalkRange X.obj.left C x = ⊤ ↔ x ∉ C
  constructor
  · intro htop hxC
    have hle := intrinsicCentreStalkRange_le_maximalIdeal X.obj.left C x hxC
    rw [htop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal (X.obj.left.presheaf.stalk x).carrier).ne_top
      (top_le_iff.mp hle)
  · intro hxC
    let U : Opens X.obj.left.toTopCat := ⟨Cᶜ, hC.isClosed.isOpen_compl⟩
    let s : intrinsicReducedCentreSectionIdeal X.obj.left C U :=
      ⟨1, by intro y hy hyC; exact (hy hyC).elim⟩
    apply (Ideal.eq_top_iff_one _).mpr
    refine ⟨TopCat.Presheaf.germ (intrinsicReducedCentreIdealModule X.obj.left C).val.presheaf
      U x hxC s, ?_⟩
    simpa only [s, map_one] using
      intrinsicReducedCentreStalkInclusion_germ X.obj.left C x U hxC s

/-- Ordinary actual ORIGINAL smooth closed-centre geometry produces a genuine
native smooth-centre blowup, a ONE-step finite modification, and its full
off-centre isomorphism. All whole-ideal finite type/rank-one/UP data are derived. -/
theorem exists_smoothCentreBlowup
    (X S : SourceReducedComplexSpace) (i : S ⟶ X)
    (hS : S.IsSmooth) (hi : Topology.IsClosedEmbedding i.hom.left.base)
    (hstalk : ∀ s : S.obj.left, Function.Surjective (i.hom.left.stalkMap s))
    (hC : X.IsAnalyticSubset (range i.hom.left.base))
    (hthin : interior (range i.hom.left.base) = ∅) :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSmoothCentreBlowup p i ∧ IsModification p ∧
      Function.Surjective p.hom.left.base ∧ IsIsoOver p (range i.hom.left.base)ᶜ := by
  classical
  let C : Set X.obj.left := range i.hom.left.base
  let B := intrinsicReducedCentreIdealModule X.obj.left C
  let b := intrinsicReducedCentreIdealInclusion X.obj.left C
  let : B.IsFiniteType :=
    IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType X C hC
  have hunit : {x : X.obj.left | LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤} = Cᶜ :=
    intrinsic_ideal_unitLocus_eq_compl X C hC
  have hDense : Dense {x : X.obj.left | LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤} := by
    rw [hunit]
    exact interior_eq_empty_iff_dense_compl.mp hthin
  let Y := OriginalFiniteIdealBlowup.sourceObject B b hDense
  let p : Y ⟶ X := OriginalFiniteIdealBlowup.projectionMorphism B b hDense
  have hPB : IsProperBimeromorphic p :=
    OriginalFiniteIdealBlowupUniversal.projection_isProperBimeromorphic B b hDense
  have hIdeal : IsIdealBlowup p B b := by
    constructor
    · exact OriginalFiniteIdealBlowupUniversal.projection_ideal_exists_locallyFreeData B b hDense
    · intro A F hF
      obtain ⟨q, hq, huniq⟩ := hF
      let : q.IsLocallyFreeData := hq
      let : ∀ a, Unique (q.generators a).I := fun a => Classical.choice (huniq a)
      exact OriginalFiniteIdealBlowupUniversal.exists_unique_lift_of_locallyFreeData B b hDense A F q
  have hStep : IsSmoothCentreBlowup p i := ⟨hS, hi, hstalk, hC, hthin, hIdeal, hPB⟩
  have hNonunit : EmbeddedIdealBlowupNonunitLocus.nonunitLocus B b = C := by
    ext x
    change (LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) ≠ ⊤) ↔ x ∈ C
    have hx := Set.ext_iff.mp hunit x
    simpa only [mem_ofPred_eq, mem_compl_iff, not_not] using not_congr hx
  have hIso : IsIsoOver p Cᶜ := by
    change IsIsoOver (OriginalFiniteIdealBlowup.projectionMorphism B b hDense) Cᶜ
    rw [← hNonunit]
    unfold OriginalFiniteIdealBlowup.projectionMorphism
    exact EmbeddedIdealBlowupOriginalBimeromorphic.projection_isIsoOver_compl_nonunitLocus
      _ _ _ B b _ _ _
  exact ⟨Y, p, hStep, IsModification.of_step ⟨S, i, hStep⟩,
    OriginalFiniteIdealBlowup.projection_surjective B b hDense, hIso⟩

end

end Hironaka.Analytic.Unibranch.OriginalSmoothCentreBlowup
