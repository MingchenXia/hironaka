import Hironaka.Analytic.Unibranch.HironakaG10SchurSectionStalk
import Hironaka.Coherence.OkaGermBridge
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10TranslatedScalarIdeal
open Hironaka Hironaka HolGerm OkaGermBridge OkaRelationSheaf
noncomputable section
variable {E₁ E₀ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]

theorem translated_scalar_germ_ideal_eq (d : ℕ) (p : ComplexModel d)
    (S T : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hS : ∀ᶠ s in 𝓝 p, DifferentiableAt ℂ S s)
    (hT : ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ T s)
    (hEq : T =ᶠ[𝓝 (0 : ComplexModel d)] fun s => S (p+s)) :
    Ideal.span (Set.range fun q : E₁ × (E₀ →L[ℂ] ℂ) =>
      let L := q.2.comp (ContinuousLinearMap.apply ℂ E₀ q.1)
      HolGerm.mk (L ∘ T) (hT.mono fun _ h => L.differentiableAt.comp _ h)) =
    Ideal.span (Set.range fun q : E₁ × (E₀ →L[ℂ] ℂ) =>
      let L := q.2.comp (ContinuousLinearMap.apply ℂ E₀ q.1)
      germAt p (L ∘ S)) := by
  have hs (q : E₁ × (E₀ →L[ℂ] ℂ)) :
      let L := q.2.comp (ContinuousLinearMap.apply ℂ E₀ q.1)
      HolGerm.mk (L ∘ T) (hT.mono fun _ h => L.differentiableAt.comp _ h) = germAt p (L ∘ S) := by
    dsimp only
    let L := q.2.comp (ContinuousLinearMap.apply ℂ E₀ q.1)
    have hh : HolAt (L ∘ S) p := hS.mono fun _ h => L.differentiableAt.comp _ h
    rw [germAt_of_holAt hh]
    apply HolGerm.mk_eq_mk_iff.mpr
    filter_upwards [hEq] with s hs
    exact congrArg L hs
  congr 1
  ext g
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨q,(hs q).symm⟩
  · rintro ⟨q,rfl⟩
    exact ⟨q,hs q⟩
end
end Hironaka.Analytic.Unibranch.HironakaG10TranslatedScalarIdeal
