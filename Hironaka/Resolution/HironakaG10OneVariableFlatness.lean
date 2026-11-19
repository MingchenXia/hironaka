import Hironaka.Analytic.HolomorphicZeroSetThin
import Hironaka.Analytic.RegularDirection
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Actual module flatness over the one-variable holomorphic germ ring

Every nonzero germ is a coordinate power times a unit, so every ideal is
principal.  For an arbitrary module over this actual ring, coordinate scalar
multiplication is injective exactly when the module is flat.  The principal
ideal property is supplied locally, without registering a new global instance.
The multivariable local flatness criterion is a separate result.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace Hironaka.HironakaG10OneVariableFlatness

noncomputable section

/-- The germ of the coordinate on the one-dimensional smooth base. -/
def coordinate : HolGerm ℂ :=
  HolGerm.mk id (Eventually.of_forall fun _ => differentiableAt_id)

theorem coordinate_ne_zero : coordinate ≠ 0 := by
  intro h
  have hz : ∀ᶠ z in 𝓝 (0 : ℂ), z = 0 := by
    exact HolGerm.mk_eq_mk_iff.mp (h.trans HolGerm.mk_zero.symm)
  have hz' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z = 0 := hz.filter_mono nhdsWithin_le_nhds
  obtain ⟨z, hz, hzne⟩ := (hz'.and
    (self_mem_nhdsWithin : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0)).exists
  exact hzne hz

/-- The finite order of a nonzero analytic germ gives its exact coordinate
power times a unit; neither a chosen valuation nor a DVR premise is needed. -/
theorem exists_eq_coordinate_pow_mul_unit (g : HolGerm ℂ) (hg : g ≠ 0) :
    ∃ (n : ℕ) (u : HolGerm ℂ), IsUnit u ∧ g = coordinate ^ n * u := by
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
  have hne : ¬ f =ᶠ[𝓝 (0 : ℂ)] 0 := by
    intro h
    apply hg
    rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
    exact h
  obtain ⟨r, hr, hfr⟩ := Metric.eventually_nhds_iff_ball.mp hf
  have ha : AnalyticAt ℂ f 0 :=
    (show DifferentiableOn ℂ f (ball (0 : ℂ) r) from
      fun z hz => (hfr z hz).differentiableWithinAt).analyticOnNhd isOpen_ball 0 (mem_ball_self hr)
  obtain ⟨n, u, hu, hu0, heq⟩ := ha.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hud : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ u z :=
    hu.eventually_analyticAt.mono fun _ hz => hz.differentiableAt
  refine ⟨n, HolGerm.mk u hud, (HolGerm.isUnit_iff_eval_ne_zero _).mpr hu0, ?_⟩
  rw [coordinate, ← HolGerm.mk_pow, ← HolGerm.mk_mul]
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards [heq] with z hz
  simpa only [sub_zero, smul_eq_mul, id_eq] using hz

/-- Every ideal of the actual one-variable germ ring is principal, by
choosing the least coordinate exponent occurring with a unit factor. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (HolGerm ℂ) := by
  classical
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · subst I
    infer_instance
  let Q : ℕ → Prop := fun n => ∃ u : HolGerm ℂ, IsUnit u ∧ coordinate ^ n * u ∈ I
  have hQ : ∃ n, Q n := by
    obtain ⟨g, hgI, hg⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨n, u, hu, hgu⟩ := exists_eq_coordinate_pow_mul_unit g hg
    exact ⟨n, u, hu, hgu ▸ hgI⟩
  let m := Nat.find hQ
  obtain ⟨u, hu, hmu⟩ := Nat.find_spec hQ
  have hmI : coordinate ^ m ∈ I := by
    rcases hu with ⟨u, rfl⟩
    have h := I.mul_mem_right (↑u⁻¹ : HolGerm ℂ) hmu
    simpa only [mul_assoc, Units.mul_inv, mul_one] using h
  refine ⟨⟨coordinate ^ m, le_antisymm ?_ ?_⟩⟩
  · intro g hgI
    by_cases hg : g = 0
    · simpa only [hg] using (Ideal.span {coordinate ^ m}).zero_mem
    obtain ⟨n, v, hv, hgv⟩ := exists_eq_coordinate_pow_mul_unit g hg
    have hmn : m ≤ n := Nat.find_min' hQ ⟨v, hv, hgv ▸ hgI⟩
    have hpow : coordinate ^ n = coordinate ^ m * coordinate ^ (n - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hmn]
    rw [hgv, hpow, mul_assoc]
    exact (Ideal.span {coordinate ^ m}).mul_mem_right _
      (Ideal.subset_span (mem_singleton _))
  · apply Ideal.span_le.mpr
    rintro _ rfl
    exact hmI

variable {M : Type*} [AddCommGroup M] [Module (HolGerm ℂ) M]

/-- Over the actual one-variable analytic local ring, coordinate regularity
is equivalent to module flatness, for arbitrary modules and fibre dimension. -/
theorem flat_iff_coordinate_smul_injective :
    Module.Flat (HolGerm ℂ) M ↔ Function.Injective (fun x : M => coordinate • x) := by
  constructor
  · intro hflat
    let _ := hflat
    exact Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero coordinate_ne_zero)
  · intro hreg
    have hpow : ∀ n : ℕ, ∀ x : M, coordinate ^ n • x = 0 → x = 0 := by
      intro n
      induction n with
      | zero => intro x hx; simpa only [pow_zero, one_smul] using hx
      | succ n ih =>
        intro x hx
        rw [pow_succ, mul_smul] at hx
        have hx' := ih (coordinate • x) hx
        exact hreg (by simpa only [smul_zero] using hx')
    have htf : Module.IsTorsionFree (HolGerm ℂ) M :=
      Module.IsTorsionFree.of_smul_eq_zero fun g x hx => by
        by_cases hg : g = 0
        · exact Or.inl hg
        obtain ⟨n, u, hu, hgu⟩ := exists_eq_coordinate_pow_mul_unit g hg
        have hux : u • x = 0 := hpow n (u • x) (by rwa [hgu, mul_smul] at hx)
        rcases hu with ⟨u, rfl⟩
        refine Or.inr ?_
        calc
          x = (↑u⁻¹ : HolGerm ℂ) • ((↑u : HolGerm ℂ) • x) := by
            rw [smul_smul, Units.inv_mul, one_smul]
          _ = 0 := by rw [hux, smul_zero]
    let _ : IsPrincipalIdealRing (HolGerm ℂ) := isPrincipalIdealRing
    exact Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
      (Submodule.isTorsionFree_iff_torsion_eq_bot.mp htf)

end

end Hironaka.HironakaG10OneVariableFlatness
