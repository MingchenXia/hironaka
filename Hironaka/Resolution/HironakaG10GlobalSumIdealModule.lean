import Hironaka.Resolution.HironakaG10FiniteIdealFamilyArithmetic
import Hironaka.Resolution.HironakaG10PNIdealModule

/-! # A finite-type module for a compactly supported sum ideal -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.HironakaG10GlobalSumIdealModule

open HironakaG10HirIdealGerms HironakaG10FiniteIdealFamilyArithmetic
  HironakaG10PNIdealModule HironakaSingularModuleSheafStalk

noncomputable section

/-- If the nonunit locus of `I^m + K` lies in a closed subset of its
open domain, the unit extension is represented by an actual finite-type
ideal module on the whole locally ringed space, with all its stalk ideals. -/
theorem exists_global_sum_ideal_module (X : LocallyRingedSpace.{0})
    (V Q : Set X) (hV : IsOpen V) (hQ : IsClosed Q) (hQV : Q ⊆ V)
    (I K : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hI : IsLocallyFinitelyGeneratedOn X V I) (hK : IsLocallyFinitelyGeneratedOn X V K)
    (m : ℕ) (htop : ∀ x ∈ V, x ∉ Q → I x ^ m ⊔ K x = ⊤) :
    ∃ (B : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf))
      (b : B ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf)),
      B.IsFiniteType ∧
      (∀ x ∈ V, LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b x) =
        I x ^ m ⊔ K x) ∧
      (∀ x ∉ Q, LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b x) = ⊤) := by
  let J : ∀ x : X, Ideal (X.presheaf.stalk x) := fun x => I x ^ m ⊔ K x
  let A := extendByUnit V J
  have hJ : IsLocallyFinitelyGeneratedOn X V J :=
    isLocallyFinitelyGeneratedOn_sup V (fun x => I x ^ m) K
      (isLocallyFinitelyGeneratedOn_pow V I hI m) hK
  have hA := isLocallyFinitelyGenerated_extendByUnit V Q hV hQ hQV J hJ htop
  let R := X.toSheafedSpace.sheaf
  have hAR : IsLocallyFinitelyGeneratedIn R A := hA
  refine ⟨familyModule R A,familyInclusion R A,familyModule_isFiniteType R A hAR,?_,?_⟩
  · intro x hx
    rw [familyInclusion_stalk_range R A hAR x]
    change extendByUnit V J x = _
    simp only [extendByUnit, hx, ↓reduceIte, J]
  · intro x hx
    rw [familyInclusion_stalk_range R A hAR x]
    change extendByUnit V J x = ⊤
    by_cases hxV : x ∈ V
    · simpa only [extendByUnit, hxV, ↓reduceIte, J] using htop x hxV hx
    · simp only [extendByUnit, hxV, ↓reduceIte]

end

end Hironaka.HironakaG10GlobalSumIdealModule
