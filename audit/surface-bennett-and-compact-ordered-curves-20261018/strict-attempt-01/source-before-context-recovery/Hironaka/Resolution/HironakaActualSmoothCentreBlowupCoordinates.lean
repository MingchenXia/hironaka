/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointBlowupCoordinates

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSmoothCentreBlowupCoordinates
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupLocalSurjectivity BlowupFibreDirection BlowupSNCTransform
  HironakaActualAnalyticBlowupTaylor HironakaActualPointBlowupCoordinates
variable {n : ℕ}

/-- The true normal monomial map recentres without changing any original tangent coordinate. -/
theorem actual_smooth_centre_monomial_recentre (k : ℕ) (j : Fin n) (v w : ComplexModel n)
    (hvt : ∀ i : Fin n, i.val < k → v i=0) (hvj : v j=0) :
    monomial k j w=actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j (fun i => v i) (w-v) := by
  ext i
  by_cases hi : k ≤ i.val
  · by_cases hij : i=j
    · subst i
      simp [monomial_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi,hvj]
    · simp [monomial_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi,hij,hvj]
      ring
  · have hvi := hvt i (by omega)
    simp [monomial_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi,hvi]

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The original full blowup and actual centre regularity alone produce the entire normal-form square and SAME centre flattening. -/
theorem exists_actual_smooth_centre_blowup_coordinates {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (z : Y) (k : ℕ) (hCz : RegularAtDim (n := n) C (π z) k) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z)))
      (j : Fin n) (b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z)),
      Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0 ∧
      (∀ u : X, u ∈ (chartAt (ComplexModel n) (π z)).source →
        chartAt (ComplexModel n) (π z) u ∈ Φ.source →
        (u ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) u) ∈ complexCoordinatePlane n k)) ∧
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z)=0 ∧ k ≤ j.val ∧
      (∀ i : Fin n, i.val < k → b i=0) ∧ b j=0 ∧
      ∀ u : Y, u ∈ (chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z u ∈ Θ.source →
        π u ∈ flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel n) (π z) (π u))=
          actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b (Θ.toFun (chartAt (ComplexModel n) z u)) := by
  obtain ⟨_,_,Φ,hΦsrc,hΦ0,hflat⟩ := hCz
  change Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0 at hΦ0
  have hzflat : π z ∈ flatDomain Φ := mem_flatDomain_self Φ
  obtain ⟨j,hj,O,hO,hzO,W,hWs,hWeq,hℓW,_⟩ :=
    exists_monomialLocalInverse hπ hΦsrc hflat hzflat
  obtain ⟨ℓ,⟨hℓs,hℓπ⟩,_⟩ := existsUnique_monomialLift hπ hΦsrc hflat hj
  have hWmem : ∀ y ∈ O, W y ∈ monomialDomain Φ k j := by
    intro y hy
    change monomial k j (W y) ∈ Φ.target
    rw [(hWeq y hy).2]
    exact Φ.mapsTo_toFun (hWeq y hy).1.2
  have hFinj := fderiv_complex_monomial_inverse_injective hO hWs hWmem hℓs
    (hℓW ℓ hℓs hℓπ) hzO
  obtain ⟨Θ,hΘsrc,hΘ0,hΘeq⟩ := exists_recentred_coords hO hWs hzO hFinj
  have hWj : W z j=0 := by
    have he := congrArg (fun w : ComplexModel n => w j) (hWeq z hzO).2
    simpa [monomial_apply,hΦ0] using he
  have hWt : ∀ i : Fin n, i.val < k → W z i=0 := by
    intro i hi
    have he := congrArg (fun w : ComplexModel n => w i) (hWeq z hzO).2
    simpa [monomial_apply,not_le.mpr hi,hΦ0] using he
  refine ⟨Φ,j,(fun i => W z i),Θ,hΦsrc,hΦ0,(fun u hu huΦ => hflat hu huΦ),hΘsrc,hΘ0,hj,hWt,hWj,?_⟩
  intro y hy hyΘ
  obtain ⟨hyO,hcoord⟩ := hΘeq hy hyΘ
  change Θ.toFun (chartAt (ComplexModel n) z y)=W y-W z at hcoord
  refine ⟨(hWeq y hyO).1,?_⟩
  rw [hcoord,← actual_smooth_centre_monomial_recentre k j (W z) (W y) hWt hWj]
  exact (hWeq y hyO).2.symm

end
end Hironaka.HironakaActualSmoothCentreBlowupCoordinates
