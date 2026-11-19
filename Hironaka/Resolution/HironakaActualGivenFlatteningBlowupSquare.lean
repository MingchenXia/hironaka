import Hironaka.Blowup.BlowupSNCTransform
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor

/-! A genuine native blowup produces its recentred monomial square for ANY
given source flattening. The given source coordinates are retained exactly;
the exceptional owner, direction and target coordinates are all outputs.
No target chart, desired square, target ideal or HS compatibility is supplied.

This lower geometric block does not yet assemble the model strict ideal or
the pointed inherited family, and does not close the historical phase. -/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaActualGivenFlatteningBlowupSquare

noncomputable section

open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupLocalSurjectivity BlowupSNCTransform HironakaActualAnalyticBlowupTaylor

variable {n : ℕ}

private theorem given_flattening_monomial_recentre
    (k : ℕ) (j : Fin n) (v w : ComplexModel n)
    (hvt : ∀ i : Fin n, i.val < k → v i = 0) (hvj : v j = 0) :
    monomial k j w = actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j
      (fun i => v i) (w - v) := by
  ext i
  by_cases hi : k ≤ i.val
  · by_cases hij : i = j
    · subst i
      simp [monomial_apply, actualAnalyticBlowupMap_apply,
        actualAnalyticBlowupCoordinate, hi, hvj]
    · simp [monomial_apply, actualAnalyticBlowupMap_apply,
        actualAnalyticBlowupCoordinate, hi, hij, hvj]
      ring
  · have hvi := hvt i (by omega)
    simp [monomial_apply, actualAnalyticBlowupMap_apply,
      actualAnalyticBlowupCoordinate, hi, hvi]

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The actual native blowup retains an arbitrary SAME source flattening and
internally constructs its bounded direction, legal normal owner, recentred
target coordinates and entire local polynomial square. -/
theorem exists_actual_given_flattening_blowup_square
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (x : X) (q : Y) (hq : π q = x) (k : ℕ)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n k)) :
    ∃ j : Fin n, k ≤ j.val ∧ ∃ (b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) q q)),
      (∀ i : Fin n, i.val < k → b i = 0) ∧ b j = 0 ∧
      (∀ i : Fin n, k ≤ i.val → i ≠ j → ‖b i‖ ≤ 1) ∧
      Θ.source ⊆ (chartAt (ComplexModel n) q).target ∧
      Θ.toFun (chartAt (ComplexModel n) q q) = 0 ∧
      ∀ y : Y, y ∈ (chartAt (ComplexModel n) q).source →
        chartAt (ComplexModel n) q y ∈ Θ.source →
          π y ∈ flatDomain Φ ∧
          Φ.toFun (chartAt (ComplexModel n) x (π y)) =
            actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b
              (Θ.toFun (chartAt (ComplexModel n) q y)) := by
  have hqflat : π q ∈ flatDomain Φ := by
    rw [hq]
    exact mem_flatDomain_self Φ
  obtain ⟨j, hj, O, hO, hqO, W, hWs, hWeq, hℓW, hbound⟩ :=
    exists_monomialLocalInverse hπ hΦsrc hflat hqflat
  have hWmem : ∀ y ∈ O, W y ∈ monomialDomain Φ k j := by
    intro y hy
    change monomial k j (W y) ∈ Φ.target
    rw [(hWeq y hy).2]
    exact Φ.mapsTo_toFun (hWeq y hy).1.2
  obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, _⟩ := existsUnique_monomialLift hπ hΦsrc hflat hj
  have hFinj := injective_fderiv_of_monomialInverse hO hWs hWmem hℓs
    (hℓW ℓ hℓs hℓπ) hqO
  obtain ⟨Θ, hΘsrc, hΘ0, hΘeq⟩ := exists_recentred_coords hO hWs hqO hFinj
  have hWj : W q j = 0 := by
    have he := congrArg (fun w : ComplexModel n => w j) (hWeq q hqO).2
    simpa [monomial_apply, hq, hΦ0] using he
  have hWt : ∀ i : Fin n, i.val < k → W q i = 0 := by
    intro i hi
    have he := congrArg (fun w : ComplexModel n => w i) (hWeq q hqO).2
    simpa [monomial_apply, not_le.mpr hi, hq, hΦ0] using he
  refine ⟨j, hj, (fun i => W q i), Θ, hWt, hWj, hbound, hΘsrc, hΘ0, ?_⟩
  intro y hy hyΘ
  obtain ⟨hyO, hcoord⟩ := hΘeq hy hyΘ
  change Θ.toFun (chartAt (ComplexModel n) q y) = W y - W q at hcoord
  refine ⟨(hWeq y hyO).1, ?_⟩
  rw [hcoord, ← given_flattening_monomial_recentre k j (W q) (W y) hWt hWj]
  exact (hWeq y hyO).2.symm

end

end Hironaka.HironakaActualGivenFlatteningBlowupSquare
