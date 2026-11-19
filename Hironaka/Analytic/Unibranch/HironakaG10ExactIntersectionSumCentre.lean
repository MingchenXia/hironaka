import Hironaka.Analytic.Unibranch.HironakaG10SupportIntersectionSumCentre

/-! # The exact support of a constructed sum centre -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10ExactIntersectionSumCentre

open Hironaka HironakaG10HirIdealGerms
  HironakaG10GlobalSumIdealModule HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.HironakaG10SourceOpenUniformArtinRees
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

/-- Under compactness and density of the actual support intersection,
construct the sum centre with precisely that nonunit locus. -/
theorem exists_exact_intersection_sumCentre {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (Z : LocalFlattener f)
    (IS : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hIS : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IS)
    (hQ : IsCompact {x : X.obj.left | x ∈ Z.support ∧ IS x ≠ ⊤})
    (hDense : Dense {x : X.obj.left | ¬ (x ∈ Z.support ∧ IS x ≠ ⊤)}) :
    ∃ α : ℕ, ∀ β : ℕ, α ≤ β →
      ∃ (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
        (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
        B.IsFiniteType ∧ nonunitLocus B b = {x | x ∈ Z.support ∧ IS x ≠ ⊤} ∧
        Dense {x : X.obj.left | LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤} ∧
        IsSumCentreFor B b f β := by
  classical
  let : T2Space X.obj.left := X.property.1
  let Q : Set X.obj.left := {x | x ∈ Z.support ∧ IS x ≠ ⊤}
  have hQZ : Q ⊆ Z.support := fun _ hx => hx.1
  have hQV : Q ⊆ Z.V := fun x hx => (hQZ hx).1
  obtain ⟨a,O,hO,hQO,hOV,hAR⟩ :=
    exists_compact_uniform_artinRees_on X Z.V Z.isOpen Z.H IS Z.fg hIS Q hQ hQV
  refine ⟨max a 1,fun β hβ => ?_⟩
  have haβ : a ≤ β := (le_max_left a 1).trans hβ
  have hβ0 : β ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right a 1).trans hβ))
  have htop : ∀ x ∈ Z.V, x ∉ Q → IS x ^ β ⊔ Z.H x = ⊤ := by
    intro x hxV hxQ
    by_cases hZ : Z.H x = ⊤
    · rw [hZ, sup_top_eq]
    · have hS : IS x = ⊤ := by
        by_contra hS
        exact hxQ ⟨⟨hxV,hZ⟩,hS⟩
      rw [hS, Ideal.top_pow, top_sup_eq]
  obtain ⟨B,b,hfinite,hstalk,houtside⟩ :=
    exists_global_sum_ideal_module X.obj.left Z.V Q Z.isOpen hQ.isClosed hQV IS Z.H hIS Z.fg β htop
  let : B.IsFiniteType := hfinite
  have hBQ : nonunitLocus B b ⊆ Q := by
    intro x hx
    by_contra hxQ
    exact hx (houtside x hxQ)
  have hQB : Q ⊆ nonunitLocus B b := by
    intro x hxQ hunit
    let : IsLocalRing (X.obj.left.presheaf.stalk x) := X.obj.left.isLocalRing x
    have hle : IS x ^ β ⊔ Z.H x ≤ IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk x) :=
      sup_le ((Ideal.pow_le_self hβ0).trans (IsLocalRing.le_maximalIdeal hxQ.2))
        (IsLocalRing.le_maximalIdeal hxQ.1.2)
    have hne : IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk x) ≠ ⊤ :=
      (IsLocalRing.maximalIdeal.isMaximal (X.obj.left.presheaf.stalk x)).ne_top
    rw [← hstalk x (hQV hxQ), hunit] at hle
    exact hne (top_le_iff.mp hle)
  have hD : Dense {x : X.obj.left | LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤} :=
    hDense.mono (fun x hx => houtside x hx)
  refine ⟨B,b,hfinite,Set.Subset.antisymm hBQ hQB,hD,fun x hx => ?_⟩
  have hxQ := hBQ hx
  have hZ := Z.H_eq_germFlattener (hQZ hxQ)
  refine ⟨IS x,a,haβ,?_,?_⟩
  · simpa only [HironakaG10ChowUniformArtinRees.IsArtinReesNumber,hZ] using hAR x (hQO hxQ)
  · simpa only [hZ] using hstalk x (hQV hxQ)

end Hironaka.Analytic.Unibranch.HironakaG10ExactIntersectionSumCentre
