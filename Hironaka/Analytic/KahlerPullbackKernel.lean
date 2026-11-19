import Hironaka.Analytic.ClosedFormPullback
import Hironaka.Analytic.HermitianGeometry
import Hironaka.Analytic.PositivityPerturbation
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Null directions of a pulled-back Kähler form

For a holomorphic map `f : V → M` and a Hermitian form `ω` on `M`, the pullback `f^* ω`
satisfies, in the preferred chart at `y`, `(f^* ω)(v, iv) = 0` exactly when the holomorphic
differential `df_y v` vanishes (`quad_pullback_eq_zero_iff`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.KahlerPullbackKernel

open Hironaka.HolomorphicMaps PositivityPerturbation

noncomputable section

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem quad_pullback_eq_zero_iff {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {α : SmoothRealForm n M 2} (hα : α.IsHermitian) (y : V) (v : ComplexModel k) :
    quad ((SmoothRealForm.pullback hf α).coeff (complexChartAt (n := k) y)
      (chartAt (ComplexModel k) y y)) v = 0 ↔
      mfderiv 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) f y v = 0 := by
  set e := complexChartAt (n := k) y
  set d := complexChartAt (n := n) (f y)
  have hz : chartAt (ComplexModel k) y y ∈ coordinateDomain f e d := by
    refine ⟨e.val.map_source (mem_complexChartAt_source y), ?_⟩
    show f (e.val.symm (e.val y)) ∈ d.val.source
    rw [e.val.left_inv (mem_complexChartAt_source y)]
    exact mem_complexChartAt_source (f y)
  set L := fderiv ℝ (coordinateMap f e d) (chartAt (ComplexModel k) y y)
  have hL : ∀ w, L w = mfderiv 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) f y w := by
    intro w
    have hd : DifferentiableAt ℂ (coordinateMap f e d) (chartAt (ComplexModel k) y y) :=
      (HolomorphicMaps.coordinateMap_contDiffAt hf e d hz).differentiableAt (by simp)
    have hmd : MDifferentiableAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) f y :=
      (hf y).mdifferentiableAt (by simp)
    rw [hmd.mfderiv]
    simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
    change fderiv ℝ (coordinateMap f e d) (chartAt (ComplexModel k) y y) w =
      fderiv ℂ (coordinateMap f e d) (chartAt (ComplexModel k) y y) w
    rw [hd.fderiv_restrictScalars ℝ]
    rfl
  have hcoord : coordinateMap f e d (chartAt (ComplexModel k) y y) = chartAt (ComplexModel n) (f y) (f y) := by
    show d.val (f (e.val.symm (e.val y))) = _
    rw [e.val.left_inv (mem_complexChartAt_source y)]
    rfl
  have hvec : (⇑L ∘ (![v, Complex.I • v] : Fin 2 → ComplexModel k)) =
      ![L v, Complex.I • L v] := by
    funext i
    fin_cases i
    · rfl
    · exact HolomorphicMaps.coordinateMap_fderiv_map_smul_complex hf e d hz Complex.I v
  have key : quad ((SmoothRealForm.pullback hf α).coeff e (chartAt (ComplexModel k) y y)) v =
      α.coeff d (chartAt (ComplexModel n) (f y) (f y)) ![L v, Complex.I • L v] := by
    unfold quad
    rw [SmoothRealForm.pullback_coeff hf α e d hz,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, hvec, hcoord]
  rw [key]
  have hpos := (hα d (chartAt (ComplexModel n) (f y) (f y))
    (d.val.map_source (mem_complexChartAt_source (f y)))).2
  constructor
  · intro h0
    by_contra hne
    have hLv : L v ≠ 0 := by rw [hL v]; exact hne
    exact (hpos (L v) hLv).ne' h0
  · intro h0
    have hLv : L v = 0 := by rw [hL v]; exact h0
    rw [hLv, smul_zero]
    exact α.coeff d _ |>.map_eq_zero_of_eq ![0, 0] (i := 0) (j := 1) (by simp) (by decide)

end

end Hironaka.KahlerPullbackKernel
