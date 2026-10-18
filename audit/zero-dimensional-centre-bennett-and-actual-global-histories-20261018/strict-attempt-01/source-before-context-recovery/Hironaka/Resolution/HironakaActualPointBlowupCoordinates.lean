/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualPointBlowupCoordinates
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupLocalSurjectivity BlowupFibreDirection BlowupSNCTransform
  HironakaActualAnalyticBlowupTaylor
variable {n : ℕ}

/-- The true point monomial map is the actual analytic point chart after genuine recentering. -/
theorem actual_point_monomial_recentre (j : Fin n) (v w : ComplexModel n) (hv : v j=0) :
    monomial 0 j w=actualAnalyticBlowupMap univ j (fun i => v i) (w-v) := by
  ext i
  by_cases hij : i=j
  · subst i
    simp [monomial_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hv]
  · simp [monomial_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hij,hv]
    ring

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The complex chart differential is genuinely injective when the actual monomial lift is a local inverse. -/
theorem fderiv_complex_monomial_inverse_injective {x : X}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)} {k : ℕ} {j : Fin n}
    {O : Set Y} (hO : IsOpen O) {W : Y → ComplexModel n}
    (hWs : ∀ y ∈ O, ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ W y)
    (hWmem : ∀ y ∈ O, W y ∈ monomialDomain Φ k j)
    {ℓ : LiftedOpen.{u} (monomialDomain Φ k j) → Y}
    (hℓs : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ℓ)
    (hℓW : ∀ y ∈ O, ∀ hw : W y ∈ monomialDomain Φ k j, ℓ (LiftedOpen.mk _ (W y) hw)=y)
    {z : Y} (hz : z ∈ O) :
    Function.Injective (fderiv ℂ (fun ζ => W ((chartAt (ComplexModel n) z).symm ζ))
      (chartAt (ComplexModel n) z z)) := by
  have hd := differentiableAt_chart_comp (hWs z hz)
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  by_contra hv0
  apply fderiv_monomialInverse_ne_zero hO hWs hWmem hℓs hℓW hz hv0
  rw [hd.fderiv_restrictScalars ℝ]
  exact hv

/-- Actual point-centre polynomial coordinates are constructed from the original blowup and regularity alone. -/
theorem exists_actual_point_blowup_coordinates {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (z : Y) (hCz : RegularAtDim (n := n) C (π z) 0) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z)))
      (j : Fin n) (b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z)),
      Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0 ∧
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z)=0 ∧ b j=0 ∧
      ∀ u : Y, u ∈ (chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z u ∈ Θ.source →
        π u ∈ flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel n) (π z) (π u))=
          actualAnalyticBlowupMap univ j b (Θ.toFun (chartAt (ComplexModel n) z u)) := by
  obtain ⟨_,_,Φ,hΦsrc,hΦ0,hflat⟩ := hCz
  change Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0 at hΦ0
  have hzflat : π z ∈ flatDomain Φ := mem_flatDomain_self Φ
  obtain ⟨j,hj,O,hO,hzO,W,hWs,hWeq,hℓW,_⟩ :=
    exists_monomialLocalInverse hπ hΦsrc hflat hzflat
  obtain ⟨ℓ,⟨hℓs,hℓπ⟩,_⟩ := existsUnique_monomialLift hπ hΦsrc hflat hj
  have hWmem : ∀ y ∈ O, W y ∈ monomialDomain Φ 0 j := by
    intro y hy
    change monomial 0 j (W y) ∈ Φ.target
    rw [(hWeq y hy).2]
    exact Φ.mapsTo_toFun (hWeq y hy).1.2
  have hFinj := fderiv_complex_monomial_inverse_injective hO hWs hWmem hℓs
    (hℓW ℓ hℓs hℓπ) hzO
  obtain ⟨Θ,hΘsrc,hΘ0,hΘeq⟩ := exists_recentred_coords hO hWs hzO hFinj
  have hWj : W z j=0 := by
    have he := congrArg (fun w : ComplexModel n => w j) (hWeq z hzO).2
    simpa [monomial_apply,hΦ0] using he
  refine ⟨Φ,j,(fun i => W z i),Θ,hΦsrc,hΦ0,hΘsrc,hΘ0,hWj,?_⟩
  intro y hy hyΘ
  obtain ⟨hyO,hcoord⟩ := hΘeq hy hyΘ
  change Θ.toFun (chartAt (ComplexModel n) z y)=W y-W z at hcoord
  refine ⟨(hWeq y hyO).1,?_⟩
  rw [hcoord,← actual_point_monomial_recentre j (W z) (W y) hWj]
  exact (hWeq y hyO).2.symm

end
end Hironaka.HironakaActualPointBlowupCoordinates
