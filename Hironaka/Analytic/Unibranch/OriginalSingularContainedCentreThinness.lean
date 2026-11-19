import Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus
import Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspace

/-! Given actual intrinsic singular containment supplies thinness in the
original space and for the SAME native factory inclusion. No centre or
containment is selected; the held original density engine is reused.
Blueprint FIRST: `original-singular-contained-centre-thinness.tex`. -/

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.Analytic.Unibranch.OriginalSingularContainedCentreThinness

open Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus

noncomputable section

/-- Any actual subset of the SAME original intrinsic singular locus is thin. -/
theorem interior_eq_empty_of_subset_intrinsicSingularLocus
    (X : SourceReducedComplexSpace) (S : Set X.obj.left)
    (hSing : S⊆intrinsicSingularLocus X.obj) :
    interior S=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hs := interior_mono hSing hx
  rw [OriginalIntrinsicSingularLocus.interior_intrinsicSingularLocus_eq_empty X] at hs
  exact hs

/-- Retain the literal native factory inclusion and transport ONLY its actual
range equality; thinness comes from the given original singular containment. -/
theorem factory_range_and_thin_of_subset_intrinsicSingularLocus
    (X : SourceReducedComplexSpace) (S : Set X.obj.left)
    (hS : X.IsAnalyticSubset S)
    (hSing : S⊆intrinsicSingularLocus X.obj) :
    let i := OriginalAnalyticClosedSubspace.inclusion X S hS
    Set.range i.hom.left.base=S ∧
      interior S=∅ ∧ interior (Set.range i.hom.left.base)=∅ := by
  dsimp only
  have hRange := OriginalAnalyticClosedSubspace.inclusion_range X S hS
  have hThin := interior_eq_empty_of_subset_intrinsicSingularLocus X S hSing
  refine ⟨hRange,hThin,?_⟩
  rw [hRange]
  exact hThin

end

end Hironaka.Analytic.Unibranch.OriginalSingularContainedCentreThinness
