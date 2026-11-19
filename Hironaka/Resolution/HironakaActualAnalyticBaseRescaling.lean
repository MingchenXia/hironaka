import Hironaka.Resolution.HironakaHolomorphicJetMonomialSpan

/-! Genuine rescaling of ANY original analytic base map, including s=0.
BP FIRST: hironaka-actual-analytic-base-rescaling.tex. No factor certificate. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology
namespace Hironaka.HironakaActualAnalyticBaseRescaling
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan

private theorem coordinate_holomorphic {n : ℕ} (i : Fin n) :
    OkaRelationSheaf.HolAt (fun z : ComplexModel n => z i) 0 :=
  Eventually.of_forall fun _ =>
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt

/- Only finite representative readback of the existing true Hadamard mother;
no separate mathematical credit for the inherited decomposition. -/
private theorem exists_coordinate_functions {e d : ℕ}
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v)
    (hφ0 : φ 0 = 0) :
    ∃ H : Fin d → Fin e → ComplexModel e → ℂ,
      (∀ k i, ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ (H k i) v) ∧
      ∀ k, ∀ᶠ v in 𝓝 (0 : ComplexModel e), φ v k = ∑ i, v i * H k i v := by
  have hcoord (k : Fin d) : OkaRelationSheaf.HolAt (fun v => φ v k) 0 := by
    filter_upwards [hφ] with v hv
    exact (EuclideanSpace.proj k : ComplexModel d →L[ℂ] ℂ).differentiableAt.comp v hv
  let g (k : Fin d) := HolGerm.mk (fun v => φ v k) (hcoord k)
  choose h hh using fun k : Fin d => exists_coordinate_decomposition (g k)
  choose H hH hEq using fun k i => HolGerm.exists_eq_mk (h k i)
  refine ⟨H, hH, ?_⟩
  intro k
  have hz : HolGerm.eval (g k) = 0 := by
    change φ 0 k = 0
    rw [hφ0]
    rfl
  have he := hh k
  simp only [hz, map_zero, zero_add] at he
  simp_rw [hEq] at he
  have hsum : OkaRelationSheaf.HolAt (fun v : ComplexModel e => ∑ i, v i * H k i v) 0 :=
    eventually_differentiableAt_sum Finset.univ fun i =>
      eventually_differentiableAt_mul (coordinate_holomorphic i) (hH k i)
  have hs : HolGerm.mk (fun v : ComplexModel e => ∑ i, v i * H k i v) hsum =
      ∑ i, coordinateGerm i * HolGerm.mk (H k i) (hH k i) := by
    rw [HolGerm.mk_sum Finset.univ _
      (fun i => eventually_differentiableAt_mul (coordinate_holomorphic i) (hH k i))]
    exact Finset.sum_congr rfl fun i _ => HolGerm.mk_mul _ _ _ _
  exact HolGerm.mk_eq_mk_iff.mp (he.trans hs.symm)

/-- The actual same-map rescaling is holomorphic on a genuine common ball,
with no division by the scaling parameter and no supplied factor. -/
theorem exists_holomorphic_base_rescaling (d e L : ℕ)
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v)
    (hφ0 : φ 0 = 0) (hL : 0 < L) :
    ∃ (Φ : ComplexModel e × ℂ → ComplexModel d) (R : ℝ),
      0 < R ∧ DifferentiableOn ℂ Φ (ball 0 R) ∧ Φ 0 = 0 ∧
      ∀ p ∈ ball (0 : ComplexModel e × ℂ) R, φ (p.2 ^ L • p.1) = p.2 ^ L • Φ p := by
  obtain ⟨H, hH, he⟩ := exists_coordinate_functions φ hφ hφ0
  let S : ComplexModel e × ℂ → ComplexModel e := fun p => p.2 ^ L • p.1
  have hS : Differentiable ℂ S := by
    have hs : Differentiable ℂ (fun p : ComplexModel e × ℂ => p.2) := differentiable_snd
    have hv : Differentiable ℂ (fun p : ComplexModel e × ℂ => p.1) := differentiable_fst
    exact (hs.pow L).smul hv
  have hS0 : S 0 = 0 := by
    simp only [S, Prod.fst_zero, Prod.snd_zero, zero_pow (Nat.ne_of_gt hL), zero_smul]
  have hSt : Tendsto S (𝓝 (0 : ComplexModel e × ℂ)) (𝓝 (0 : ComplexModel e)) := by
    simpa only [hS0] using hS.continuous.tendsto (0 : ComplexModel e × ℂ)
  let Φ : ComplexModel e × ℂ → ComplexModel d := fun p =>
    (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin d)).symm (fun k => ∑ i, p.1 i * H k i (S p))
  have hΦ0 : Φ 0 = 0 := by
    ext k
    simp [Φ]
  have hΦhol : ∀ᶠ p in 𝓝 (0 : ComplexModel e × ℂ), DifferentiableAt ℂ Φ p := by
    have hall := eventually_all.mpr fun k => eventually_all.mpr fun i => hSt.eventually (hH k i)
    filter_upwards [hall] with p hp
    apply (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin d)).symm.differentiableAt.comp p
    apply differentiableAt_pi.mpr
    intro k
    convert (HasFDerivAt.sum (u := Finset.univ) fun i _ =>
      (((EuclideanSpace.proj i : ComplexModel e →L[ℂ] ℂ).differentiableAt.comp p
        differentiableAt_fst).mul ((hp k i).comp p (hS p))).hasFDerivAt).differentiableAt using 1
    funext q
    simp only [Finset.sum_apply, Pi.mul_apply, Function.comp_apply]
    rfl
  have hIdentity : ∀ᶠ p in 𝓝 (0 : ComplexModel e × ℂ), φ (S p) = p.2 ^ L • Φ p := by
    filter_upwards [hSt.eventually (eventually_all.mpr he)] with p hp
    ext k
    change φ (S p) k = p.2 ^ L * ∑ i, p.1 i * H k i (S p)
    rw [hp k, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (p.2 ^ L * p.1 i) * H k i (S p) = p.2 ^ L * (p.1 i * H k i (S p))
    ring
  obtain ⟨R, hR, hall⟩ := Metric.eventually_nhds_iff_ball.mp (hΦhol.and hIdentity)
  refine ⟨Φ, R, hR, ?_, hΦ0, ?_⟩
  · intro p hp
    exact (hall p hp).1.differentiableWithinAt
  · intro p hp
    exact (hall p hp).2

end
end Hironaka.HironakaActualAnalyticBaseRescaling
