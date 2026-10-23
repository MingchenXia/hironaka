import DeJongAlterations.StableModificationBridge.NativeIdealModules
import DeJongAlterations.StableModificationBridge.SurjectiveBaseChangeKernel
import DeJongAlterations.StableModification.Cohomology.BaseChange
import Mathlib.RingTheory.Ideal.Operations

/-! The SAME actual affine ideal section sequence is internally exact under original quotient pullback. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.ClosedIdealAffineLayer

open CategoryTheory Opposite AlgebraicGeometry
open StableModification StableModification.Cohomology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : Scheme.{u}}

/-- The SAME original ideal containment gives the WHOLE native module inclusion on every open. -/
def idealInclusion {J I : X.IdealSheafData} (hJI : J ≤ I) : J.dja_toModules ⟶ I.dja_toModules :=
  ⟨PresheafOfModules.Submodule.homOfLE (show J.dja_toSubmodule ≤ I.dja_toSubmodule from
    fun _W _s hs U hU => hJI U (hs U hU))⟩

variable (N I : X.IdealSheafData) [IsLocallyNoetherian X]

/-- The WHOLE original affine pullback is surjective and has EXACTLY the intrinsic original product-ideal kernel. -/
theorem affine_pullback (U : X.affineOpens) :
    Function.Surjective (pullbackSection N.subschemeι I.dja_toModules U) ∧
      ∀ s : Γ(I.dja_toModules, U),
        pullbackSection N.subschemeι I.dja_toModules U s = 0 ↔
          (I.dja_toModulesSectionsEquiv U s : Γ(X, U)) ∈ (N * I).ideal U := by
  let : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) I.dja_toModules :=
    I.dja_isFinitePresentation_toModules
  let : I.dja_toModules.IsQuasicoherent := inferInstance
  let : Algebra Γ(X, U) Γ(N.subscheme, N.subschemeι ⁻¹ᵁ U) := (N.subschemeι.app U).hom.toAlgebra
  let : Module Γ(X, U)
      Γ((Scheme.Modules.pullback N.subschemeι).obj I.dja_toModules, N.subschemeι ⁻¹ᵁ U) :=
    Module.compHom _ (N.subschemeι.app U).hom
  let : IsScalarTower Γ(X, U) Γ(N.subscheme, N.subschemeι ⁻¹ᵁ U)
      Γ((Scheme.Modules.pullback N.subschemeι).obj I.dja_toModules, N.subschemeι ⁻¹ᵁ U) :=
    ⟨fun r b t => mul_smul (N.subschemeι.app U r) b t⟩
  have hθ : algebraMap Γ(X, U) Γ(N.subscheme, N.subschemeι ⁻¹ᵁ U) =
      (N.subschemeι.appLE U (N.subschemeι ⁻¹ᵁ U) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    rfl
  let f := pullbackSectionLinear (f := N.subschemeι) I.dja_toModules (hUV := le_rfl) hθ
  have hf : IsBaseChange Γ(N.subscheme, N.subschemeι ⁻¹ᵁ U) f :=
    isBaseChange_pullbackSectionLinear N.subschemeι I.dja_toModules U.2
      (U.2.preimage N.subschemeι) le_rfl hθ
  have hfapp (s : Γ(I.dja_toModules, U)) :
      f s = pullbackSection N.subschemeι I.dja_toModules U s := by
    change ((Scheme.Modules.pullback N.subschemeι).obj I.dja_toModules).presheaf.map (𝟙 _) _ = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hsurj : Function.Surjective f :=
    SurjectiveBaseChangeKernel.surjective hf (N.subschemeι_app_surjective U)
  constructor
  · intro t
    obtain ⟨s, hs⟩ := hsurj t
    exact ⟨s, (hfapp s).symm.trans hs⟩
  · intro s
    rw [← hfapp, SurjectiveBaseChangeKernel.eq_zero_iff_mem_kernel_smul hf
      (N.subschemeι_app_surjective U)]
    change s ∈ RingHom.ker (N.subschemeι.app U).hom •
      (⊤ : Submodule Γ(X, U) Γ(I.dja_toModules, U)) ↔ _
    rw [N.ker_subschemeι_app U]
    let e := I.dja_toModulesSectionsEquiv U
    have hmap := Submodule.comap_smul_top_of_surjective (N.ideal U) e.toLinearMap e.surjective
    rw [LinearMap.ker_eq_bot.mpr e.injective, sup_bot_eq] at hmap
    have he : s ∈ N.ideal U • (⊤ : Submodule Γ(X, U) Γ(I.dja_toModules, U)) ↔
        e s ∈ N.ideal U • (⊤ : Submodule Γ(X, U) (I.ideal U)) := by
      change _ ↔ s ∈ Submodule.comap e.toLinearMap (N.ideal U • ⊤)
      rw [hmap]
    exact he.trans (Submodule.mem_smul_top_iff (N.ideal U) (I.ideal U) (e s))

/-- The actual original ideal-product inclusion and WHOLE pullback give the complete native affine exact sequence. -/
theorem affine_exact (U : X.affineOpens) :
    Function.Exact
      ((idealInclusion (show N * I ≤ I from fun _W => Ideal.mul_le_right)).app U)
      (pullbackSection N.subschemeι I.dja_toModules U) ∧
    Function.Injective
      ((idealInclusion (show N * I ≤ I from fun _W => Ideal.mul_le_right)).app U) ∧
    Function.Surjective (pullbackSection N.subschemeι I.dja_toModules U) := by
  obtain ⟨hsurj, hker⟩ := affine_pullback N I U
  refine ⟨?_, ?_, hsurj⟩
  · intro s
    rw [hker s]
    constructor
    · intro hs
      let a : (N * I).ideal U := ⟨(I.dja_toModulesSectionsEquiv U s : Γ(X, U)), hs⟩
      refine ⟨((N * I).dja_toModulesSectionsEquiv U).symm a, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨t, rfl⟩
      exact ((N * I).dja_toModulesSectionsEquiv U t).property
  · intro a b h
    apply Subtype.ext
    exact congrArg (fun t : Γ(I.dja_toModules, U) =>
      (I.dja_toModulesSectionsEquiv U t : Γ(X, U))) h

end DeJongAlterations.StableModificationBridge.ClosedIdealAffineLayer
