import Hironaka.Analytic.Unibranch.HironakaG10SchurScalarZeroLocus
import Hironaka.Resolution.HironakaG10FlatRelationLift
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10ScalarGermSupport
open Hironaka Hironaka
  HolGerm OkaGermBridge OkaRelationSheaf HironakaG10FlatRelationLift
noncomputable section
variable {E₁ E₀ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]

theorem scalar_germ_ideal_ne_top_iff_operator_zero (d : ℕ) (p : ComplexModel d)
    (S : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hS : ∀ᶠ s in 𝓝 p, DifferentiableAt ℂ S s) :
    (Ideal.span (Set.range fun q : E₁ × (E₀ →L[ℂ] ℂ) =>
      let L := q.2.comp (ContinuousLinearMap.apply ℂ E₀ q.1)
      germAt p (L ∘ S)) : Ideal (HolGerm (ComplexModel d))) ≠ ⊤ ↔ S p = 0 := by
  let J : Ideal (HolGerm (ComplexModel d)) := Ideal.span (Set.range fun q : E₁ × (E₀ →L[ℂ] ℂ) =>
    let L := q.2.comp (ContinuousLinearMap.apply ℂ E₀ q.1)
    germAt p (L ∘ S))
  have hh (q : E₁ × (E₀ →L[ℂ] ℂ)) :
      HolAt ((q.2.comp (ContinuousLinearMap.apply ℂ E₀ q.1)) ∘ S) p :=
    hS.mono fun _ h => (q.2.comp (ContinuousLinearMap.apply ℂ E₀ q.1)).differentiableAt.comp _ h
  change J ≠ ⊤ ↔ S p = 0
  constructor
  · intro hJ
    apply ContinuousLinearMap.ext
    intro v
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
    intro ell
    have hm : germAt p ((ell.comp (ContinuousLinearMap.apply ℂ E₀ v)) ∘ S) ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) :=
      (IsLocalRing.le_maximalIdeal hJ) (Ideal.subset_span ⟨(v,ell),rfl⟩)
    have he := (HolGerm.mem_maximalIdeal_iff _).mp hm
    rw [HironakaG10FlatRelationLift.eval_germAt (hh (v,ell))] at he
    simpa using he
  · intro hzero
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    apply Ideal.span_le.mpr
    rintro _ ⟨q,rfl⟩
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    rw [HironakaG10FlatRelationLift.eval_germAt (hh q)]
    change q.2 (S p q.1) = 0
    rw [hzero]
    simp
end
end Hironaka.Analytic.Unibranch.HironakaG10ScalarGermSupport
