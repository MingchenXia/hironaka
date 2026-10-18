/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor
import Hironaka.Blowup.BlowupSequences
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPointBlowupExceptionalLocus
noncomputable section
open Hironaka.BlowupSequences HironakaActualAnalyticBlowupTaylor
variable {n : ℕ}

/-- Coordinate-wise actual manifold differential, obtained from the true polynomial derivative. -/
theorem mfderiv_actual_point_blowup_apply (e : Fin n) (b : Fin n → ℂ)
    (z v : ComplexModel n) (i : Fin n) :
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ)
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
        (actualAnalyticBlowupMap Set.univ e b) z v)=
      if i=e then v e else v e*(b i+z i)+z e*v i := by
  rw [mfderiv_eq_fderiv]
  have hmap := differentiable_actualAnalyticBlowupMap Set.univ e b z
  have hchain : HasFDerivAt
      (fun w : ComplexModel n => actualAnalyticBlowupMap Set.univ e b w i)
      ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).comp
        (fderiv ℂ (actualAnalyticBlowupMap Set.univ e b) z)) z :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.comp z hmap.hasFDerivAt
  by_cases hi : i=e
  · have he : (fun w : ComplexModel n => actualAnalyticBlowupMap Set.univ e b w i)=
        (fun w : ComplexModel n => w e) := by
      funext w
      simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi]
    rw [he] at hchain
    have hL := hchain.unique (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).hasFDerivAt
    have hv := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v) hL
    rw [if_pos hi]
    exact hv
  · have he : (fun w : ComplexModel n => actualAnalyticBlowupMap Set.univ e b w i)=
        (fun w : ComplexModel n => w e*(b i+w i)) := by
      funext w
      simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi]
    rw [he] at hchain
    have hs : HasFDerivAt (fun w : ComplexModel n => b i+w i)
        (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ) z := by
      have hs0 : HasFDerivAt (fun w : ComplexModel n => b i+w i)
          (0+(EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ)) z :=
        (hasFDerivAt_const (x := z) (b i)).add
          (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).hasFDerivAt
      simpa only [zero_add] using hs0
    have hp : HasFDerivAt (fun w : ComplexModel n => w e*(b i+w i))
        (z e • (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ)+
          (b i+z i) • (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ)) z :=
      (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.mul hs
    have hL := hchain.unique hp
    have hv := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v) hL
    rw [if_neg hi]
    calc
      _ = z e*v i+(b i+z i)*v e := hv
      _ = _ := by ring

/-- In dimension at least two an actual nonzero standard vector lies in the true differential kernel. -/
theorem exists_actual_point_blowup_nonzero_kernel (hn : 2 ≤ n) (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) (hz : z e=0) :
    ∃ v : ComplexModel n, v ≠ 0 ∧
      mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
        (actualAnalyticBlowupMap Set.univ e b) z v=0 := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j,hj⟩ := exists_ne e
  let v : ComplexModel n := PiLp.single 2 j 1
  have hve : v e=0 := by simp [v,Ne.symm hj]
  have hv : v ≠ 0 := by
    intro h
    have hzero := congrArg (fun w : ComplexModel n => w j) h
    simp [v] at hzero
  refine ⟨v,hv,?_⟩
  rw [mfderiv_eq_fderiv]
  change @Eq (ComplexModel n) ((fderiv ℂ (actualAnalyticBlowupMap Set.univ e b) z) v) 0
  ext i
  have hc := mfderiv_actual_point_blowup_apply e b z v i
  rw [mfderiv_eq_fderiv] at hc
  simp only [hve,hz,zero_mul,add_zero,ite_self] at hc
  exact hc

/-- The original exceptional locus really contains the exceptional coordinate hyperplane for n≥2. -/
theorem mem_exceptionalLocus_actual_point_blowup_of_coordinate_eq_zero
    (hn : 2 ≤ n) (e : Fin n) (b : Fin n → ℂ) (z : ComplexModel n) (hz : z e=0) :
    z ∈ exceptionalLocus n (actualAnalyticBlowupMap Set.univ e b) := by
  obtain ⟨v,hv,hvzero⟩ := exists_actual_point_blowup_nonzero_kernel hn e b z hz
  intro hbij
  apply hv
  exact hbij.1 (hvzero.trans (map_zero _).symm)

/-- With a single true coordinate, the actual point chart is literally the identity. -/
theorem actual_point_blowup_one_eq_id (e : Fin 1) (b : Fin 1 → ℂ) :
    actualAnalyticBlowupMap Set.univ e b=id := by
  funext z
  ext i
  have hi : i=e := Subsingleton.elim _ _
  simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hi]

/-- The original differential-defined exceptional locus is empty in the genuine one-dimensional case. -/
theorem exceptionalLocus_actual_point_blowup_one (e : Fin 1) (b : Fin 1 → ℂ) :
    exceptionalLocus 1 (actualAnalyticBlowupMap Set.univ e b)=∅ := by
  rw [actual_point_blowup_one_eq_id]
  ext z
  simp [exceptionalLocus,Function.bijective_id]

/-- Closed original sets have their genuine geometric strict transform unchanged in dimension one. -/
theorem strictTransform_actual_point_blowup_one (e : Fin 1) (b : Fin 1 → ℂ)
    (A : Set (ComplexModel 1)) (hA : IsClosed A) :
    strictTransform 1 (actualAnalyticBlowupMap Set.univ e b) A=A := by
  rw [strictTransform,exceptionalLocus_actual_point_blowup_one,actual_point_blowup_one_eq_id,
    sdiff_empty,preimage_id,hA.closure_eq]

end
end Hironaka.HironakaActualPointBlowupExceptionalLocus
