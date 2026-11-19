import Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentContinuous
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10NilpotentInvertiblePerturbation
open Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentContinuous
noncomputable section

theorem invertible_sub_nilpotent_parameter_perturbation
    {A E : Type*} [CommRing A] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Module A E] (I : Ideal A) (B : E →L[ℂ] E) (hB : B.IsInvertible)
    (BInvA : Module.End A E) (hInv : ∀ x, BInvA x = B.inverse x)
    (deltaA : Module.End A E) (delta : E →L[ℂ] E)
    (hdelta : ∀ x, deltaA x = delta x) (hnil : ∃ n : ℕ, I ^ n = ⊥)
    (himage : ∀ x, deltaA x ∈ I • (⊤ : Submodule A E)) :
    (B - delta).IsInvertible := by
  let uA : Module.End A E := BInvA.comp deltaA
  let u : E →L[ℂ] E := B.inverse.comp delta
  have hu (x : E) : uA x = u x := by
    change BInvA (deltaA x) = B.inverse (delta x)
    rw [hInv,hdelta]
  have himageU (x : E) : uA x ∈ I • (⊤ : Submodule A E) := by
    have hmap : (I • (⊤ : Submodule A E)).map BInvA ≤ I • (⊤ : Submodule A E) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right I le_top
    exact hmap (Submodule.mem_map_of_mem (himage x))
  have hU := isInvertible_id_sub_of_parameter_nilpotent I uA u hu hnil himageU
  have heq : B.comp (.id ℂ E - u) = B - delta := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, map_sub]
    change B x - B (B.inverse (delta x)) = B x - delta x
    rw [hB.self_apply_inverse]
  obtain ⟨eB,heB⟩ := hB
  obtain ⟨eU,heU⟩ := hU
  refine ⟨eU.trans eB, ?_⟩
  rw [← heq]
  ext x
  change eB (eU x) = B ((.id ℂ E - u) x)
  rw [← heB, ← heU]
  rfl
end
end Hironaka.Analytic.Unibranch.HironakaG10NilpotentInvertiblePerturbation
