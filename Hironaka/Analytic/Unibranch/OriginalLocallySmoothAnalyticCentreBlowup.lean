import Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceSmoothCentres
import Hironaka.Analytic.Unibranch.OriginalSmoothCentreBlowup

/-!
# A native blowup from an ordinary locally smooth original analytic subset

Ordinary local centre geometry derives smoothness of the SAME actual
analytic-subspace factory. The held smooth-centre producer then returns
the SAME native blowup, finite modification and full off-centre isomorphism.
Blueprint FIRST: `original-locally-smooth-analytic-centre-blowup.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalLocallySmoothAnalyticCentreBlowup

open Hironaka Hironaka.BlowupSequences
  SourceReducedComplexSpace OriginalAnalyticClosedSubspaceSmoothCentres
  SmoothCentreModification

noncomputable section

/-- Ordinary raw subset/local smooth geometry gives an ACTUAL original modification step. -/
theorem exists_smoothCentreBlowup_of_local_smooth_centres
    (X : SourceReducedComplexSpace) (S : Set X.obj.left) (hS : X.IsAnalyticSubset S)
    (hthin : interior S = ∅)
    (hGeom : ∀ (x : X.obj.left), x ∈ S →
      ∃ (e : LocalEmbedding X) (O : Opens e.ambient) (C : Set O)
        (_hC : IsClosedSubmanifold e.dim C)
        (_hCW : C ⊆ (Subtype.val : O → e.ambient) ⁻¹' e.carrier)
        (d : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier)),
        (givenWindowMorphism e O).hom.left.base d = x ∧
        (givenWindowMorphism e O).hom.left.base ⁻¹' S =
          (Subtype.val : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) → O) ⁻¹' C) :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSmoothCentreBlowup p (OriginalAnalyticClosedSubspace.inclusion X S hS) ∧
      IsModification p ∧ Function.Surjective p.hom.left.base ∧ IsIsoOver p Sᶜ := by
  let Z := OriginalAnalyticClosedSubspace.sourceObject X S hS
  let i : Z ⟶ X := OriginalAnalyticClosedSubspace.inclusion X S hS
  have hSmooth : Z.IsSmooth := sourceObject_isSmooth_of_local_smooth_centres S hS hGeom
  have hRange : range i.hom.left.base = S := OriginalAnalyticClosedSubspace.inclusion_range X S hS
  have hAnalyticRange : X.IsAnalyticSubset (range i.hom.left.base) :=
    (congrArg (fun T : Set X.obj.left => X.IsAnalyticSubset T) hRange).mpr hS
  have hThinRange : interior (range i.hom.left.base) = ∅ :=
    (congrArg (fun T : Set X.obj.left => interior T) hRange).trans hthin
  obtain ⟨Y, p, hBlowup, hModification, hSurjective, hIso⟩ :=
    OriginalSmoothCentreBlowup.exists_smoothCentreBlowup X Z i hSmooth
      (OriginalAnalyticClosedSubspace.inclusion_isClosedEmbedding X S hS)
      (OriginalAnalyticClosedSubspace.inclusion_stalk_surjective X S hS)
      hAnalyticRange hThinRange
  refine ⟨Y, p, hBlowup, hModification, hSurjective, ?_⟩
  have hComplement : (range i.hom.left.base)ᶜ = Sᶜ :=
    congrArg (fun T : Set X.obj.left => Tᶜ) hRange
  exact (congrArg (fun T : Set X.obj.left => IsIsoOver p T) hComplement).mp hIso

end

end Hironaka.Analytic.Unibranch.OriginalLocallySmoothAnalyticCentreBlowup
