import Hironaka.Analytic.Unibranch.HironakaG10ConstructedSumCentre

/-! # Sum centres supported on the actual intersection of ideal supports -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10SupportIntersectionSumCentre

open Hironaka HironakaG10HirIdealGerms HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ConstructedSumCentre
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

/-- If the actual intersection of the flattener support with the nonunit
locus of the second ideal is compact with dense complement, construct the
finite-type sum centre for every sufficiently large exponent. No separate
unit-off-support hypothesis is required. -/
theorem exists_intersection_supported_sumCentre {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (Z : LocalFlattener f)
    (IS : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hIS : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IS)
    (hQ : IsCompact {x : X.obj.left | x ∈ Z.support ∧ IS x ≠ ⊤})
    (hDense : Dense {x : X.obj.left | ¬ (x ∈ Z.support ∧ IS x ≠ ⊤)}) :
    ∃ α : ℕ, ∀ β : ℕ, α ≤ β →
      ∃ (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
        (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
        B.IsFiniteType ∧ nonunitLocus B b ⊆ {x | x ∈ Z.support ∧ IS x ≠ ⊤} ∧
        Dense {x : X.obj.left | LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤} ∧
        IsSumCentreFor B b f β := by
  classical
  let Q : Set X.obj.left := {x | x ∈ Z.support ∧ IS x ≠ ⊤}
  have hQZ : Q ⊆ Z.support := fun _ hx => hx.1
  obtain ⟨α,hα⟩ := exists_constructed_sumCentre f Z IS hIS Q hQ hQZ hDense
  refine ⟨α,fun β hαβ => hα β hαβ ?_⟩
  intro x hxV hxQ
  by_cases hZ : Z.H x = ⊤
  · rw [hZ, sup_top_eq]
  · have hS : IS x = ⊤ := by
      by_contra hS
      exact hxQ ⟨⟨hxV,hZ⟩,hS⟩
    rw [hS, Ideal.top_pow, top_sup_eq]

end Hironaka.Analytic.Unibranch.HironakaG10SupportIntersectionSumCentre
