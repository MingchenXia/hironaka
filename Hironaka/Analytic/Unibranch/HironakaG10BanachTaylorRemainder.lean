import Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-! # Finite Banach-valued Taylor expansion and its whole jet remainder -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorRemainder
open Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor

/-- The finite normalized Taylor sum of the actual Banach-valued family. -/
noncomputable def taylorPartial {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (f : X → B) (N : ℕ) (z : X) : B :=
  ∑ j ∈ Finset.range N, (Nat.factorial j : ℂ)⁻¹ •
    (iteratedFDeriv ℂ j f 0) (fun _ => z)

/-- All actual derivatives below the truncation degree of the original
  Banach-valued family minus its finite Taylor sum vanish. -/
theorem iteratedFDeriv_sub_taylorPartial_eq_zero
    {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (f : X → B) (hf : ∀ᶠ z in 𝓝 (0 : X), DifferentiableAt ℂ f z) (N j : ℕ) (hj : j < N) :
    iteratedFDeriv ℂ j (f - taylorPartial f N) 0 = 0 := by
  let p : FormalMultilinearSeries ℂ X B := fun k =>
    (Nat.factorial k : ℂ)⁻¹ • iteratedFDeriv ℂ k f 0
  let q : FormalMultilinearSeries ℂ X B := fun k => if k < N then p k else 0
  have hfinite : ∀ k, N ≤ k → q k = 0 := by
    intro k hk
    dsimp [q]
    rw [if_neg (by omega)]
  have hpoly : HasFiniteFPowerSeriesOnBall (taylorPartial f N) q 0 N ⊤ := by
    apply HasFiniteFPowerSeriesOnBall.mk' hfinite (by simp)
    intro z _
    rw [zero_add z]
    dsimp [taylorPartial]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [q,p]
    rw [if_pos (Finset.mem_range.mp hk)]
    rfl
  have hp : HasFPowerSeriesAt f p 0 := has_normalized_powerSeriesAt f hf
  obtain ⟨r,hsub⟩ := hp.sub hpoly.toHasFPowerSeriesOnBall.hasFPowerSeriesAt
  apply ContinuousMultilinearMap.ext
  intro v
  rw [hsub.iteratedFDeriv_eq_sum_of_completeSpace v]
  have hq : (p-q) j = 0 := by
    change p j - q j = 0
    dsimp [q]
    rw [if_pos hj,sub_self]
  simp only [hq,zero_apply,Finset.sum_const_zero]

end Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorRemainder
