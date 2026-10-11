/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOrder
import Hironaka.Resolution.HironakaSmoothPullbackDerivatives
import Hironaka.Analytic.StokesSingularLocusAnalytic
import Hironaka.Invariant.MonomialPart
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothSubmersionJacobian
open Hironaka.HolomorphicIdealSheaves
open HironakaSmoothSubmersionOrder HironakaSmoothPullbackDerivatives
open Hironaka

noncomputable section
variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X]
 [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
 [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
variable {f : Y → X} {y : Y}
/-- The actual original-chart derivative has an internally constructed continuous complex linear right inverse. -/
theorem exists_chartDerivative_rightInverse
 (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
 (hhol : ∀ z, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f z)
 (e : ComplexChart n X) (e' : ComplexChart m Y)
 (hy : y ∈ e'.val.source) (hfy : f y ∈ e.val.source) :
 ∃ R : ComplexModel n →L[ℂ] ComplexModel m,
   (fderiv ℂ (e.val ∘ f ∘ e'.val.symm) (e'.val y)).comp R =
     ContinuousLinearMap.id ℂ (ComplexModel n) := by
 obtain ⟨s, hsbase, hsh, hsection⟩ := exists_holomorphic_localSection hf
 let p := e'.val y
 let q := e.val (f y)
 let F := e.val ∘ f ∘ e'.val.symm
 let S := e'.val ∘ s ∘ e.val.symm
 have hSbase : S q = p := by
   simp only [S, q, p, Function.comp_apply, e.val.left_inv hfy, hsbase]
 have hsd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m)
     s (e.val.symm q) := by
   simpa only [q, e.val.left_inv hfy] using hsh.self_of_nhds
 have hss : s (e.val.symm q) ∈ e'.val.source := by
   simpa only [q, e.val.left_inv hfy, hsbase] using hy
 have hS : DifferentiableAt ℂ S q := by
   rw [← mdifferentiableAt_iff_differentiableAt]
   exact (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel m)) e'.property hss).comp q
     (hsd.comp q (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n))
       e.property (e.val.map_source hfy)))
 have hF : DifferentiableAt ℂ F p :=
   (eventually_differentiableAt_chartMap e e' hhol hy hfy).self_of_nhds
 have hT : Tendsto e.val.symm (𝓝 q) (𝓝 (f y)) := by
   have h := e.val.continuousAt_symm (e.val.map_source hfy)
   simpa only [q, ContinuousAt, e.val.left_inv hfy] using h
 have hsT : Tendsto (s ∘ e.val.symm) (𝓝 q) (𝓝 y) := by
   have h := (hsh.self_of_nhds.continuousAt.tendsto).comp hT
   simpa only [hsbase] using h
 have hFS : F ∘ S =ᶠ[𝓝 q] id := by
   filter_upwards [hsT.eventually (e'.val.open_source.mem_nhds hy),
     hT.eventually hsection, e.val.open_target.mem_nhds (e.val.map_source hfy)] with z hzs hzi hzt
   simp only [Function.comp_apply, id_eq] at hzs hzi
   simp only [F, S, Function.comp_apply, id_eq]
   rw [e'.val.left_inv hzs, hzi, e.val.right_inv hzt]
 have hD : fderiv ℂ (F ∘ S) q = fderiv ℂ id q := hFS.fderiv_eq
 rw [fderiv_comp q (by simpa only [hSbase] using hF) hS, hSbase] at hD
 refine ⟨fderiv ℂ S q, ?_⟩
 simpa only [F, p, fderiv_id] using hD
/-- The genuine holomorphic submersion has surjective derivative in any original charts. -/
theorem chartDerivative_surjective
 (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
 (hhol : ∀ z, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f z)
 (e : ComplexChart n X) (e' : ComplexChart m Y)
 (hy : y ∈ e'.val.source) (hfy : f y ∈ e.val.source) :
 Function.Surjective (fderiv ℂ (e.val ∘ f ∘ e'.val.symm) (e'.val y)) := by
 obtain ⟨R, hR⟩ := exists_chartDerivative_rightInverse hf hhol e e' hy hfy
 intro v
 refine ⟨R v, ?_⟩
 exact congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L v) hR

private theorem linearIndependent_coordinate_rows
 (D : ComplexModel m →L[ℂ] ComplexModel n) (hD : Function.Surjective D) :
 LinearIndependent ℂ (fun i : Fin n => (EuclideanSpace.proj i).comp D) := by
 classical
 rw [Fintype.linearIndependent_iff]
 intro c hc i
 obtain ⟨v, hv⟩ := hD (EuclideanSpace.single i 1)
 have he := congrArg (fun L : ComplexModel m →L[ℂ] ℂ => L v) hc
 simpa [sum_apply, smul_apply,
   ContinuousLinearMap.comp_apply, hv, PiLp.single_apply] using he

/-- Actual source coordinate columns give a nonzero original-chart Jacobian minor. -/
theorem exists_nonzero_chartJacobian_minor
 (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
 (hhol : ∀ z, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f z)
 (e : ComplexChart n X) (e' : ComplexChart m Y)
 (hy : y ∈ e'.val.source) (hfy : f y ∈ e.val.source) :
 ∃ cols : Fin n → Fin m,
  (Matrix.of fun i j => fderiv ℂ (e.val ∘ f ∘ e'.val.symm) (e'.val y)
    (EuclideanSpace.single (cols j) 1) i).det ≠ 0 := by
 have hL := linearIndependent_coordinate_rows
   (fderiv ℂ (e.val ∘ f ∘ e'.val.symm) (e'.val y))
   (chartDerivative_surjective hf hhol e e' hy hfy)
 obtain ⟨cols, hcols⟩ := StokesSingularLocusAnalytic.exists_cols_det_ne_zero hL
 exact ⟨cols, hcols⟩

/-- The determinant of an actual finite matrix of scalar holomorphic germs is holomorphic. -/
theorem holomorphicAt_matrix_det
 (A : X → Matrix (Fin m) (Fin m) ℂ) (x : X)
 (hA : ∀ i j, HolomorphicAt n (fun z => A z i j) x) :
 HolomorphicAt n (fun z => (A z).det) x := by
 classical
 have he : (fun z => (A z).det) = fun z =>
   ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ i : Fin m, A z (σ i) i := by
   funext z
   exact Matrix.det_apply _
 rw [he]
 refine HolomorphicAt.sum Finset.univ fun σ _ => ?_
 have hp := MonomialPart.holomorphicAt_finset_prod Finset.univ
   (fun i _ => hA (σ i) i)
 convert (holomorphicAt_const (n := n) (x := x)
   ((Equiv.Perm.sign σ : ℤ) : ℂ)).mul hp using 1
 funext z
 simp only [Units.smul_def, zsmul_eq_mul]

/-- An internally selected actual Jacobian minor is holomorphic and stays nonzero near the original point. -/
theorem exists_holomorphic_nonzero_chartJacobian_minor
 (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y)
 (hhol : ∀ z, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f z)
 (e : ComplexChart n X) (e' : ComplexChart m Y)
 (hy : y ∈ e'.val.source) (hfy : f y ∈ e.val.source) :
 ∃ cols : Fin n → Fin m,
  let D := fun p => (Matrix.of fun i j =>
    chainCoeff e e' f (EuclideanSpace.single (cols j) 1) i p).det
  D y ≠ 0 ∧ HolomorphicAt m D y ∧ ∀ᶠ p in 𝓝 y, D p ≠ 0 := by
 obtain ⟨cols, hc⟩ := exists_nonzero_chartJacobian_minor hf hhol e e' hy hfy
 let A : Y → Matrix (Fin n) (Fin n) ℂ := fun p => Matrix.of fun i j =>
   chainCoeff e e' f (EuclideanSpace.single (cols j) 1) i p
 have hA : ∀ i j, HolomorphicAt m (fun p => A p i j) y := fun i j =>
   holomorphicAt_chainCoeff e e' hhol hy hfy _ _
 have hd := holomorphicAt_matrix_det A y hA
 refine ⟨cols, hc, hd, ?_⟩
 exact hd.continuousAt.eventually (isOpen_ne.mem_nhds hc)

end
end Hironaka.HironakaSmoothSubmersionJacobian
