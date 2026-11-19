import Hironaka.Analytic.Unibranch.HironakaG10BanachBilinearJetVanishing

/-! # Reducing bilinear jets to actual finite Taylor polynomials -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10BilinearTaylorReduction
open Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorRemainder
  Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor
  Hironaka.Analytic.Unibranch.HironakaG10BanachBilinearJetVanishing

theorem taylorPartial_contDiffAt
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (f : X → E) (N : ℕ) :
    ContDiffAt ℂ ⊤ (taylorPartial f N) 0 := by
  let p : FormalMultilinearSeries ℂ X E := fun k =>
    (Nat.factorial k : ℂ)⁻¹ • iteratedFDeriv ℂ k f 0
  let q : FormalMultilinearSeries ℂ X E := fun k => if k < N then p k else 0
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
  exact hpoly.toHasFPowerSeriesOnBall.hasFPowerSeriesAt.analyticAt.contDiffAt

/-- Low derivatives of a bilinear product are determined by the actual finite
  Taylor polynomials of its two holomorphic factors. -/
theorem iteratedFDeriv_bilinear_taylorPartial
    {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (B : E →L[ℂ] F →L[ℂ] G) (f : X → E) (g : X → F)
    (hf : ∀ᶠ z in 𝓝 (0 : X), DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 (0 : X), DifferentiableAt ℂ g z)
    (N n : ℕ) (hn : n < N) :
    iteratedFDeriv ℂ n (fun x => B (f x) (g x)) 0 =
      iteratedFDeriv ℂ n (fun x => B (taylorPartial f N x) (taylorPartial g N x)) 0 := by
  let Fp := taylorPartial f N
  let Gp := taylorPartial g N
  have hfC : ContDiffAt ℂ ⊤ f 0 := (has_normalized_powerSeriesAt f hf).analyticAt.contDiffAt
  have hgC : ContDiffAt ℂ ⊤ g 0 := (has_normalized_powerSeriesAt g hg).analyticAt.contDiffAt
  have hFC : ContDiffAt ℂ ⊤ Fp 0 := taylorPartial_contDiffAt f N
  have hGC : ContDiffAt ℂ ⊤ Gp 0 := taylorPartial_contDiffAt g N
  have hleft := iteratedFDeriv_bilinear_eq_zero_of_left B (f-Fp) g
    (hfC.sub hFC) hgC N n hn (fun j hj => iteratedFDeriv_sub_taylorPartial_eq_zero f hf N j hj)
  have hright := iteratedFDeriv_bilinear_eq_zero_of_left B.flip (g-Gp) Fp
    (hgC.sub hGC) hFC N n hn (fun j hj => iteratedFDeriv_sub_taylorPartial_eq_zero g hg N j hj)
  have hp1 : ContDiffAt ℂ ⊤ (fun x => B (f x) (g x)) 0 :=
    (B.contDiff.contDiffAt.comp 0 hfC).clm_apply hgC
  have hp2 : ContDiffAt ℂ ⊤ (fun x => B (Fp x) (g x)) 0 :=
    (B.contDiff.contDiffAt.comp 0 hFC).clm_apply hgC
  have hp3 : ContDiffAt ℂ ⊤ (fun x => B (Fp x) (Gp x)) 0 :=
    (B.contDiff.contDiffAt.comp 0 hFC).clm_apply hGC
  have heq1 : (fun x => B ((f-Fp) x) (g x)) =
      (fun x => B (f x) (g x)) - (fun x => B (Fp x) (g x)) := by
    funext x
    simp only [Pi.sub_apply, map_sub, sub_apply]
  have heq2 : (fun x => B.flip ((g-Gp) x) (Fp x)) =
      (fun x => B (Fp x) (g x)) - (fun x => B (Fp x) (Gp x)) := by
    funext x
    simp only [Pi.sub_apply, map_sub, sub_apply, ContinuousLinearMap.flip_apply]
  rw [heq1, iteratedFDeriv_sub_apply (hp1.of_le (by simp)) (hp2.of_le (by simp)), sub_eq_zero] at hleft
  rw [heq2, iteratedFDeriv_sub_apply (hp2.of_le (by simp)) (hp3.of_le (by simp)), sub_eq_zero] at hright
  exact hleft.trans hright

end Hironaka.Analytic.Unibranch.HironakaG10BilinearTaylorReduction
