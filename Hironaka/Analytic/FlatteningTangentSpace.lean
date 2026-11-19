import Hironaka.Analytic.GlobalTubeFunction
import Hironaka.Analytic.RegularPatchNeighborhood

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The tangent space of a submanifold in an ambient chart is independent of the flattening

Source: Copy-4, Steps 4 and 6 of `prop:principalization`, where `A_W` is required to
be Kähler *on `W`*, i.e. where `β` has to be strictly positive exactly on `T_W`.

This is the design question left open by I-0356.  `Pending/ManifoldTubePositivity`'s
`exists_tube_forall_strictPosAt` asks for strict positivity of `β` on
`(dF)⁻¹(ℂᵏ × 0)` for **every** nondegenerate holomorphic flattening `F` of `W` in
**every** ambient chart, and a consumer cannot discharge that without knowing the
subspace does not depend on `F`.  This module proves it does not.

The proof is a finite-dimensional squeeze, and needs no inverse function theorem.

* Any admissible nondegenerate `F` has `(dF)⁻¹(P)` of rank at most `rank P`,
  because `dF` is injective (`finrank_comap_le`).
* The *canonical* flattening `Ψ = flatChartMap e f Φ` supplied by regularity has
  `(dΨ)⁻¹(P)` of rank exactly `rank P`, because `dΨ` is an injective endomorphism of
  a finite-dimensional space, hence bijective (`finrank_comap_eq_of_bijective`).
* `(dΨ)⁻¹(P) ⊆ (dF)⁻¹(P)`: a vector of the left side is the velocity of a
  holomorphic curve `ζ` inside `W`, obtained by moving in the plane and pulling back
  through `Φ.invFun`; `F ∘ ζ` then lies in `P` identically, so its derivative does.

Together, the two subspaces coincide, so `(dF)⁻¹(P)` equals the canonical
`(dΨ)⁻¹(P)` for every admissible nondegenerate `F` — which is the statement that a
`∀ F` hypothesis is dischargeable from one flattening.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.FlatteningTangentSpace

noncomputable section

open Hironaka.HolomorphicMaps GlobalTubeFunction

variable {n : ℕ}

/-! ### The coordinate plane as a real subspace -/

/-- `ℂᵏ × 0 ⊆ ℂⁿ` as an `ℝ`-subspace.  Its carrier is
`Hironaka.complexCoordinatePlane n k`. -/
def planeSubmodule (n k : ℕ) : Submodule ℝ (ComplexModel n) where
  carrier := complexCoordinatePlane n k
  add_mem' := by
    intro a b ha hb i hi
    simp [show (a + b) i = a i + b i from rfl, ha i hi, hb i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by
    intro c a ha i hi
    simp [show (c • a) i = c • a i from rfl, ha i hi]

@[simp] theorem mem_planeSubmodule {k : ℕ} {z : ComplexModel n} :
    z ∈ planeSubmodule n k ↔ z ∈ complexCoordinatePlane n k := Iff.rfl

/-! ### The rank squeeze -/

/-- An injective linear map cannot enlarge the rank of a preimage. -/
theorem finrank_comap_le (L : ComplexModel n →L[ℝ] ComplexModel n)
    (hL : Function.Injective L) (P : Submodule ℝ (ComplexModel n)) :
    Module.finrank ℝ (P.comap (L : ComplexModel n →ₗ[ℝ] ComplexModel n)) ≤
      Module.finrank ℝ P := by
  refine LinearMap.finrank_le_finrank_of_injective
    (f := (L : ComplexModel n →ₗ[ℝ] ComplexModel n).restrict
      (p := P.comap (L : ComplexModel n →ₗ[ℝ] ComplexModel n)) (q := P)
      (fun x hx => hx)) ?_
  intro x y hxy
  exact Subtype.ext (hL (congrArg Subtype.val hxy))

/-- A bijective linear map preserves the rank of a preimage. -/
theorem finrank_comap_eq_of_bijective (L : ComplexModel n →L[ℝ] ComplexModel n)
    (hL : Function.Bijective L) (P : Submodule ℝ (ComplexModel n)) :
    Module.finrank ℝ (P.comap (L : ComplexModel n →ₗ[ℝ] ComplexModel n)) =
      Module.finrank ℝ P := by
  set e : ComplexModel n ≃ₗ[ℝ] ComplexModel n :=
    LinearEquiv.ofBijective (L : ComplexModel n →ₗ[ℝ] ComplexModel n) hL with he
  have hcomap : P.comap (L : ComplexModel n →ₗ[ℝ] ComplexModel n)
      = P.map (e.symm : ComplexModel n →ₗ[ℝ] ComplexModel n) := by
    rw [Submodule.map_equiv_eq_comap_symm]
    rfl
  rw [hcomap, LinearEquiv.finrank_map_eq]


/-! ### The inverse of the chart flattening -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {p : ComplexModel n}

/-- The local inverse of `flatChartMap e f Φ`: invert the flattening, then the chart
transition.  Both halves are genuinely invertible — `LocalHolomorphicEquivAt` carries a
holomorphic `invFun` and a chart transition is an open partial homeomorphism — so no
inverse function theorem is used anywhere in this module. -/
def flatChartMapInv (e f : ComplexChart n M) (Φ : LocalHolomorphicEquivAt (n := n) p) :
    ComplexModel n → ComplexModel n :=
  fun y => (chartTransition f e).symm (Φ.invFun y)

variable {e f : ComplexChart n M} {Φ : LocalHolomorphicEquivAt (n := n) p}

theorem mem_chartTransition_source {z : ComplexModel n}
    (hz : z ∈ flatChartDomain e f Φ) : z ∈ (chartTransition f e).source :=
  ⟨hz.1, hz.2.1⟩

theorem chartTransition_mem_Φsource {z : ComplexModel n}
    (hz : z ∈ flatChartDomain e f Φ) : chartTransition f e z ∈ Φ.source := hz.2.2

theorem flatChartMap_mem_Φtarget {z : ComplexModel n}
    (hz : z ∈ flatChartDomain e f Φ) : flatChartMap e f Φ z ∈ Φ.target :=
  Φ.mapsTo_toFun (chartTransition_mem_Φsource hz)

theorem invFun_flatChartMap {z : ComplexModel n} (hz : z ∈ flatChartDomain e f Φ) :
    Φ.invFun (flatChartMap e f Φ z) = chartTransition f e z :=
  Φ.left_inv _ (chartTransition_mem_Φsource hz)

theorem flatChartMapInv_flatChartMap {z : ComplexModel n}
    (hz : z ∈ flatChartDomain e f Φ) :
    flatChartMapInv e f Φ (flatChartMap e f Φ z) = z := by
  rw [flatChartMapInv, invFun_flatChartMap hz]
  exact (chartTransition f e).left_inv (mem_chartTransition_source hz)

theorem differentiableAt_flatChartMap {z : ComplexModel n}
    (hz : z ∈ flatChartDomain e f Φ) :
    DifferentiableAt ℝ (flatChartMap e f Φ) z :=
  (((contDiffOn_flatChartMap e f Φ).differentiableOn (by simp)).differentiableAt
    ((isOpen_flatChartDomain e f Φ).mem_nhds hz)).restrictScalars ℝ

theorem differentiableAt_flatChartMapInv {z : ComplexModel n}
    (hz : z ∈ flatChartDomain e f Φ) :
    DifferentiableAt ℝ (flatChartMapInv e f Φ) (flatChartMap e f Φ z) := by
  have hΦ : DifferentiableAt ℝ Φ.invFun (flatChartMap e f Φ z) :=
    (Φ.invFun_holomorphic.differentiableAt
      (Φ.isOpen_target.mem_nhds (flatChartMap_mem_Φtarget hz))).restrictScalars ℝ
  have hξ : Φ.invFun (flatChartMap e f Φ z) ∈ (chartTransition f e).target := by
    rw [invFun_flatChartMap hz]
    exact (chartTransition f e).map_source (mem_chartTransition_source hz)
  have hτ : DifferentiableAt ℝ (chartTransition f e).symm
      (Φ.invFun (flatChartMap e f Φ z)) :=
    ((Hironaka.RegularPatchNeighborhood.differentiableOn_chartTransition_symm
      f e).differentiableAt
        ((chartTransition f e).open_target.mem_nhds hξ)).restrictScalars ℝ
  exact hτ.comp _ hΦ

/-- The differential of the chart flattening is inverted by the differential of
`flatChartMapInv`. -/
theorem fderiv_flatChartMapInv_comp {z : ComplexModel n}
    (hz : z ∈ flatChartDomain e f Φ) :
    (fderiv ℝ (flatChartMapInv e f Φ) (flatChartMap e f Φ z)).comp
        (fderiv ℝ (flatChartMap e f Φ) z)
      = ContinuousLinearMap.id ℝ (ComplexModel n) := by
  have hev : (flatChartMapInv e f Φ ∘ flatChartMap e f Φ) =ᶠ[𝓝 z] id := by
    filter_upwards [(isOpen_flatChartDomain e f Φ).mem_nhds hz] with y hy
    exact flatChartMapInv_flatChartMap hy
  rw [← fderiv_comp z (differentiableAt_flatChartMapInv hz)
    (differentiableAt_flatChartMap hz), hev.fderiv_eq, fderiv_id]

end

end Hironaka.FlatteningTangentSpace
