import Hironaka.Analytic.RegularDirectionDense
import Hironaka.Resolution.HironakaHolomorphicJetChartInvariance

/-!
# Linear curves detect germs and the zero ideal on a smooth base

The actual whole-germ composition homomorphisms to one-dimensional smooth
germs jointly detect nonzero germs.  Consequently they detect whether an
arbitrary ideal is zero.  The zero direction and dimension zero are included;
there is no radicality or finite-generation assumption on the ideal.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Hironaka.HironakaG10LinearGermDetection

open HironakaHolomorphicJetChartInvariance

noncomputable section

/-- Some actual linear-curve pullback of a nonzero smooth-base germ is
nonzero, including in dimension zero. -/
theorem exists_compAlgHom_ne_zero {d : ℕ} (h : HolGerm (ComplexModel d))
    (hne : h ≠ 0) :
    ∃ L : ComplexModel 1 →L[ℂ] ComplexModel d,
      compAlgHom L (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero h ≠ 0 := by
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk h
  have hnonzero : ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel d), f z = 0 := by
    intro hz
    apply hne
    rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
    exact hz
  obtain ⟨w, _, hw⟩ := RegularDirectionDense.exists_forall_regularAlong'
    (g := fun _ : Unit => f) (fun _ => hf) (fun _ => hnonzero)
    (0 : ComplexModel d) (δ := 1) zero_lt_one
  let L : ComplexModel 1 →L[ℂ] ComplexModel d :=
    (EuclideanSpace.proj (0 : Fin 1)).smulRight w
  refine ⟨L, ?_⟩
  intro hz
  rw [compAlgHom_mk, ← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff] at hz
  let σ : ℂ →L[ℂ] ComplexModel 1 :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))
  have hσ : Tendsto σ (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using σ.continuous.tendsto (0 : ℂ)
  apply hw ()
  filter_upwards [hσ.eventually hz] with t ht
  simpa [L, σ, Function.comp_def, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, PiLp.single_apply] using ht

/-- If every actual linear-curve image of a whole ideal is zero, the ideal
itself is zero.  Neither radicality nor finite generation is required. -/
theorem ideal_eq_bot_of_forall_linear_map_eq_bot {d : ℕ}
    (H : Ideal (HolGerm (ComplexModel d)))
    (hH : ∀ L : ComplexModel 1 →L[ℂ] ComplexModel d,
      Ideal.map
        (compAlgHom L (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero).toRingHom
        H = ⊥) : H = ⊥ := by
  apply le_antisymm
  · intro h hh
    rw [Ideal.mem_bot]
    by_contra hne
    obtain ⟨L, hL⟩ := exists_compAlgHom_ne_zero h hne
    apply hL
    have hmem := Ideal.mem_map_of_mem
      (compAlgHom L (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero).toRingHom hh
    rw [hH L] at hmem
    exact Ideal.mem_bot.mp hmem
  · exact bot_le

/-- Linear curves jointly detect the zero ideal of the actual smooth-base
holomorphic germ ring. -/
theorem ideal_eq_bot_iff_forall_linear_map_eq_bot {d : ℕ}
    (H : Ideal (HolGerm (ComplexModel d))) :
    H = ⊥ ↔ ∀ L : ComplexModel 1 →L[ℂ] ComplexModel d,
      Ideal.map
        (compAlgHom L (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero).toRingHom
        H = ⊥ := by
  constructor
  · rintro rfl L
    exact Ideal.map_bot
  · exact ideal_eq_bot_of_forall_linear_map_eq_bot H

end

end Hironaka.HironakaG10LinearGermDetection
