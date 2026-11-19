import Hironaka.Resolution.HironakaG10SmoothBaseMatrixFlatness

/-! The original holomorphic product-germ projection is flat. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Set
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10SmoothProjectionFlat
open Hironaka Hironaka
  HolGerm OkaRelationSheaf HironakaRelativeNormalIdeal HironakaG10FlatResolutionStart
  HironakaG10HirChartFlattener HironakaG10LinearCurveMatrixPullback
  HironakaG10SmoothBaseMatrixFlatness
noncomputable section

/-- The actual germ homomorphism induced by the smooth product projection is flat. -/
theorem tangentPullback_flat (d t : ℕ) : (tangentPullback d t).toRingHom.Flat := by
  let F : Fin 1 → Fin 0 → ComplexModel (d+t) → ℂ := fun _ j => Fin.elim0 j
  let G : Fin 0 → Fin 0 → ComplexModel (d+t) → ℂ := fun j => Fin.elim0 j
  have hF : ∀ i j, HolAt (F i j) 0 := fun _ j => Fin.elim0 j
  have hG : ∀ j k, HolAt (G j k) 0 := fun j => Fin.elim0 j
  have hcomp : ∀ i k, ∀ᶠ x in 𝓝 (0 : ComplexModel (d+t)), ∑ j, F i j x * G j k x = 0 :=
    fun _ k => Fin.elim0 k
  have hfib : ∀ v : Fin 0 → ComplexModel t → ℂ,
      IsRelationAt (fun i j z => F i j (HironakaActualCentreJointJets.actualJointNormalInclusion d t z)) 0 v →
      IsCombinationAt (columns (fun j k z => G j k (HironakaActualCentreJointJets.actualJointNormalInclusion d t z))) 0 v := by
    intro v hv
    refine ⟨fun k => Fin.elim0 k, ?_, ?_⟩
    · intro k; exact Fin.elim0 k
    · intro j; exact Fin.elim0 j
  have hflat := chartMap_entryIdeal_flat_of_specialFibreExact d t F G hF hG hcomp hfib
  have hI : entryIdeal d t F = ⊥ := by
    apply Ideal.span_eq_bot.mpr
    rintro _ ⟨j,hj⟩
    exact Fin.elim0 j
  rw [hI] at hflat
  let B := HolGerm (ComplexModel (d+t))
  have hquotFlat : (RingEquiv.quotientBot B).toRingHom.Flat :=
    RingHom.Flat.of_bijective (RingEquiv.quotientBot B).bijective
  have hcompFlat := hflat.comp hquotFlat
  have heq : (RingEquiv.quotientBot B).toRingHom.comp (chartMap d t ⊥) = (tangentPullback d t).toRingHom := by
    ext r
    simp [chartMap, B]
  rw [heq] at hcompFlat
  exact hcompFlat
end
end Hironaka.Analytic.Unibranch.HironakaG10SmoothProjectionFlat
