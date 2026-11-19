import Hironaka.Analytic.Unibranch.HironakaG10SourceOpenUniformArtinRees
import Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
import Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum

/-! # Uniform Artin--Rees at an actual tracked sum centre -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10SumCentreUniformArtinRees

open Hironaka HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.HironakaG10SourceOpenUniformArtinRees
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

/-- A compact part of the support of a local flattener admits one exponent
for every sum-centre candidate whose actual nonunit locus lies in that part.
The actual construction and equality of the centre ideal remain inputs. -/
theorem exists_uniform_sumCentre_bound {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (Z : LocalFlattener f)
    (IS : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hIS : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IS)
    (Q : Set X.obj.left) (hQ : IsCompact Q) (hQZ : Q ⊆ Z.support)
    (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (hBQ : nonunitLocus B b ⊆ Q) :
    ∃ α : ℕ, ∀ β : ℕ, α ≤ β →
      (∀ x ∈ nonunitLocus B b,
        LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) =
          IS x ^ β ⊔ Z.H x) → IsSumCentreFor B b f β := by
  have hQV : Q ⊆ Z.V := fun x hx => (hQZ hx).1
  obtain ⟨α,O,hO,hQO,hOV,hAR⟩ :=
    exists_compact_uniform_artinRees_on X Z.V Z.isOpen Z.H IS Z.fg hIS Q hQ hQV
  refine ⟨α,fun β hαβ hB x hx => ?_⟩
  have hxQ := hBQ hx
  have hZ := Z.H_eq_germFlattener (hQZ hxQ)
  refine ⟨IS x,α,hαβ,?_,?_⟩
  · simpa only [HironakaG10ChowUniformArtinRees.IsArtinReesNumber, hZ] using hAR x (hQO hxQ)
  · simpa only [hZ] using hB x hx

end Hironaka.Analytic.Unibranch.HironakaG10SumCentreUniformArtinRees
