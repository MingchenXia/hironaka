import Hironaka.Analytic.Unibranch.HironakaG10SumCentreUniformArtinRees
import Hironaka.Resolution.HironakaG10GlobalSumIdealModule

/-! # Constructed supported sum centres with a uniform exponent -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10ConstructedSumCentre

open Hironaka HironakaG10HirIdealGerms
  HironakaG10GlobalSumIdealModule HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.HironakaG10SourceOpenUniformArtinRees
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

/-- Given compact support control and a dense complement, construct the
actual finite-type sum centre after selecting a uniform Artin--Rees bound.
The support control and density hypotheses remain geometric obligations. -/
theorem exists_constructed_sumCentre {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (Z : LocalFlattener f)
    (IS : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hIS : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IS)
    (Q : Set X.obj.left) (hQ : IsCompact Q) (hQZ : Q ⊆ Z.support)
    (hDense : Dense Qᶜ) :
    ∃ α : ℕ, ∀ β : ℕ, α ≤ β →
      (∀ x ∈ Z.V, x ∉ Q → IS x ^ β ⊔ Z.H x = ⊤) →
      ∃ (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
        (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
        B.IsFiniteType ∧ nonunitLocus B b ⊆ Q ∧
        Dense {x : X.obj.left | LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤} ∧
        IsSumCentreFor B b f β := by
  let : T2Space X.obj.left := X.property.1
  have hQV : Q ⊆ Z.V := fun x hx => (hQZ hx).1
  obtain ⟨α,O,hO,hQO,hOV,hAR⟩ :=
    exists_compact_uniform_artinRees_on X Z.V Z.isOpen Z.H IS Z.fg hIS Q hQ hQV
  refine ⟨α,fun β hαβ htop => ?_⟩
  obtain ⟨B,b,hfinite,hstalk,houtside⟩ :=
    exists_global_sum_ideal_module X.obj.left Z.V Q Z.isOpen hQ.isClosed hQV IS Z.H hIS Z.fg β htop
  let : B.IsFiniteType := hfinite
  have hBQ : nonunitLocus B b ⊆ Q := by
    intro x hx
    by_contra hxQ
    exact hx (houtside x hxQ)
  have hD : Dense {x : X.obj.left | LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤} :=
    hDense.mono (fun x hx => houtside x hx)
  refine ⟨B,b,hfinite,hBQ,hD,fun x hx => ?_⟩
  have hxQ := hBQ hx
  have hZ := Z.H_eq_germFlattener (hQZ hxQ)
  refine ⟨IS x,α,hαβ,?_,?_⟩
  · simpa only [HironakaG10ChowUniformArtinRees.IsArtinReesNumber,hZ] using hAR x (hQO hxQ)
  · simpa only [hZ] using hstalk x (hQV hxQ)

end Hironaka.Analytic.Unibranch.HironakaG10ConstructedSumCentre
