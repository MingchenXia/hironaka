import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Genuine common-open sections from the ORIGINAL finite family of generic points
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationGenericSectionSpread

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME original generic-field map commutes with each actual smaller-open inclusion. -/
theorem genericFactor_homOfLE {S : Scheme.{u}} [IsIntegral S]
    {V U : S.Opens} (hVU : V ≤ U) (hη : genericPoint S ∈ V) :
    V.fromSpecStalkOfMem (genericPoint S) hη ≫ S.homOfLE hVU =
      U.fromSpecStalkOfMem (genericPoint S) (hVU hη) := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- The actual original function-field point maps to the SAME original generic point of the open. -/
theorem genericFactor_closedPoint {S : Scheme.{u}} [IsIntegral S]
    (V : S.Opens) (hη : genericPoint S ∈ V) :
    V.fromSpecStalkOfMem (genericPoint S) hη (IsLocalRing.closedPoint S.functionField) =
      (⟨genericPoint S, hη⟩ : V) := by
  apply Subtype.ext
  have H := congrArg (fun m : Spec S.functionField ⟶ S =>
    m (IsLocalRing.closedPoint S.functionField)) (Scheme.Opens.fromSpecStalkOfMem_ι V
      (genericPoint S) hη)
  simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint, Scheme.Opens.ι_apply] using H

/-- All actual original generic maps spread on ONE internally chosen original dense base open. -/
theorem exists_common_spread {X S : Scheme.{u}} [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFiniteType f] {ι : Type u} [Finite ι]
    (φ : ι → (Spec S.functionField ⟶ X))
    (hφ : ∀ i, φ i ≫ f = S.fromSpecStalk (genericPoint S)) :
    ∃ (V : S.Opens) (hη : genericPoint S ∈ V) (σ : ι → (V.toScheme ⟶ X)),
      Dense (V : Set S) ∧ (∀ i, σ i ≫ f = V.ι) ∧
      ∀ i, V.fromSpecStalkOfMem (genericPoint S) hη ≫ σ i = φ i := by
  have hspread (i : ι) := spread_out_of_isGermInjective' (𝟙 S) f (φ i)
    (by simpa using hφ i)
  choose U hηU σ hgeneric hstruct using hspread
  let V := ⨅ i, U i
  have hη : genericPoint S ∈ V := by
    change genericPoint S ∈ ((⨅ i, U i : S.Opens) : Set S)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hηU
  let τ : ι → (V.toScheme ⟶ X) := fun i => S.homOfLE (iInf_le U i) ≫ σ i
  refine ⟨V, hη, τ, V.isOpen.dense ⟨genericPoint S, hη⟩, ?_, ?_⟩
  · intro i
    dsimp [τ]
    rw [Category.assoc, hstruct, Category.comp_id, Scheme.homOfLE_ι]
  · intro i
    have hfactor : V.fromSpecStalkOfMem (genericPoint S) hη ≫
        S.homOfLE (iInf_le U i) = (U i).fromSpecStalkOfMem (genericPoint S) (hηU i) := by
      apply (cancel_mono (U i).ι).mp
      rw [Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι]
    dsimp [τ]
    rw [← Category.assoc, hfactor, ← hgeneric]

/-- The same original relative map constructs its actual native restricted section. -/
def relativeSection {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (σ : V.toScheme ⟶ X) (hσ : σ ≫ f = V.ι) :
    V.toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
  pullback.lift σ (𝟙 V.toScheme) (by simpa using hσ) ≫ (pullbackRestrictIsoRestrict f V).hom

/-- The ENTIRE actual original ambient-map triangle. -/
theorem relativeSection_fst {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (σ : V.toScheme ⟶ X) (hσ : σ ≫ f = V.ι) :
    relativeSection f V σ hσ ≫ (f ⁻¹ᵁ V).ι = σ := by
  simp [relativeSection, Category.assoc]

/-- The ENTIRE actual restricted-family section identity. -/
theorem relativeSection_snd {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (σ : V.toScheme ⟶ X) (hσ : σ ≫ f = V.ι) :
    relativeSection f V σ hσ ≫ (f ∣_ V) = 𝟙 V.toScheme := by
  simp [relativeSection, Category.assoc]

/-- Every value retains the SAME actual original ambient map. -/
theorem relativeSection_apply {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (σ : V.toScheme ⟶ X) (hσ : σ ≫ f = V.ι) (v : V) :
    (f ⁻¹ᵁ V).ι (relativeSection f V σ hσ v) = σ v := by
  exact congrArg (fun m : V.toScheme ⟶ X => m v) (relativeSection_fst f V σ hσ)

/-- ORIGINAL separatedness makes this SAME genuine restricted section closed. -/
theorem relativeSection_isClosedImmersion {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (V : S.Opens) (σ : V.toScheme ⟶ X) (hσ : σ ≫ f = V.ι) :
    IsClosedImmersion (relativeSection f V σ hσ) := by
  let : IsClosedImmersion (relativeSection f V σ hσ ≫ (f ∣_ V)) := by
    rw [relativeSection_snd]
    infer_instance
  exact IsClosedImmersion.of_comp (relativeSection f V σ hσ) (f ∣_ V)

end Hironaka.Geometry.CurveFibrationGenericSectionSpread
