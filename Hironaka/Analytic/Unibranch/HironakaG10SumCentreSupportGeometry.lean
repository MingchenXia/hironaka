import Hironaka.Analytic.Unibranch.HironakaG10ExactIntersectionSumCentre

/-! # Compact support geometry for a sum centre -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10SumCentreSupportGeometry

open Hironaka HironakaG10HirIdealGerms HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ExactIntersectionSumCentre
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

/-- If the actual intersection lies in a compact subset of the common
open domain, local finite generation makes the intersection compact.
A dense unit locus of either ideal supplies its dense complement. -/
theorem compact_and_dense_supportIntersection {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (Z : LocalFlattener f)
    (IS : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hIS : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IS)
    (K : Set X.obj.left) (hK : IsCompact K) (hKV : K ⊆ Z.V)
    (hQK : {x : X.obj.left | x ∈ Z.support ∧ IS x ≠ ⊤} ⊆ K)
    (hDense : Dense {x : X.obj.left | IS x = ⊤}) :
    IsCompact {x : X.obj.left | x ∈ Z.support ∧ IS x ≠ ⊤} ∧
      Dense {x : X.obj.left | ¬ (x ∈ Z.support ∧ IS x ≠ ⊤)} := by
  classical
  let : T2Space X.obj.left := X.property.1
  let Q : Set X.obj.left := {x | x ∈ Z.support ∧ IS x ≠ ⊤}
  let U : Set X.obj.left := (Z.V ∩ {x | Z.H x = ⊤}) ∪ (Z.V ∩ {x | IS x = ⊤})
  have hU : IsOpen U := Z.isOpen_inter_eq_top.union (isOpen_inter_eq_top hIS Z.isOpen)
  have hEq : Q = K \ U := by
    ext x
    constructor
    · intro hx
      refine ⟨hQK hx,?_⟩
      rintro (h | h)
      · exact hx.1.2 h.2
      · exact hx.2 h.2
    · rintro ⟨hxK,hxU⟩
      have hxV := hKV hxK
      refine ⟨⟨hxV,?_⟩,?_⟩
      · intro htop
        exact hxU (Or.inl ⟨hxV,htop⟩)
      · intro htop
        exact hxU (Or.inr ⟨hxV,htop⟩)
  have hclosed : IsClosed Q := by
    rw [hEq]
    exact hK.isClosed.inter hU.isClosed_compl
  have hcompact : IsCompact Q := hK.of_isClosed_subset hclosed hQK
  have hdense : Dense Qᶜ := hDense.mono (fun x hx hQx => hQx.2 hx)
  exact ⟨hcompact,hdense⟩

/-- A compact neighborhood of the actual intersection, together with the
ordinary dense unit locus of the second family, supplies the hypotheses of
the constructed exact-support sum centre. -/
theorem exists_sumCentre_of_compact_container {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (Z : LocalFlattener f)
    (IS : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hIS : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IS)
    (K : Set X.obj.left) (hK : IsCompact K) (hKV : K ⊆ Z.V)
    (hQK : {x : X.obj.left | x ∈ Z.support ∧ IS x ≠ ⊤} ⊆ K)
    (hDense : Dense {x : X.obj.left | IS x = ⊤}) :
    ∃ α : ℕ, ∀ β : ℕ, α ≤ β →
      ∃ (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
        (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
        B.IsFiniteType ∧
        nonunitLocus B b = {x | x ∈ Z.support ∧ IS x ≠ ⊤} ∧
        Dense {x : X.obj.left | LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤} ∧
        IsSumCentreFor B b f β := by
  obtain ⟨hcompact, hdense⟩ := compact_and_dense_supportIntersection f Z IS hIS K hK hKV hQK hDense
  exact exists_exact_intersection_sumCentre f Z IS hIS hcompact hdense

/-- The exact-support construction is an actual admissible centre when its
geometric support lies in the non-flat image. -/
theorem exists_admissible_sumCentre_of_compact_container
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (Z : LocalFlattener f)
    (IS : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hIS : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IS)
    (K : Set X.obj.left) (hK : IsCompact K) (hKV : K ⊆ Z.V)
    (hQK : {x : X.obj.left | x ∈ Z.support ∧ IS x ≠ ⊤} ⊆ K)
    (hDense : Dense {x : X.obj.left | IS x = ⊤})
    (hNonflat : {x : X.obj.left | x ∈ Z.support ∧ IS x ≠ ⊤} ⊆ nonflatImage f) :
    ∃ α : ℕ, ∀ β : ℕ, α ≤ β →
      ∃ c : AdmissibleCentre f,
        nonunitLocus c.B c.b = {x | x ∈ Z.support ∧ IS x ≠ ⊤} ∧
        IsSumCentreFor c.B c.b f β := by
  obtain ⟨α, hα⟩ := exists_sumCentre_of_compact_container f Z IS hIS K hK hKV hQK hDense
  refine ⟨α, fun β hβ => ?_⟩
  obtain ⟨B, b, hB, hEq, hUnit, hSum⟩ := hα β hβ
  refine ⟨⟨B, b, hB, hUnit, ?_⟩, hEq, hSum⟩
  simpa only [hEq] using hNonflat

end Hironaka.Analytic.Unibranch.HironakaG10SumCentreSupportGeometry
