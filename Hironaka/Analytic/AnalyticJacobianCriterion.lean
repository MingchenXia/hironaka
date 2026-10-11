/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Analytic.AnalyticJacobianSingularCore

import Hironaka.Analytic.JacobianMinors

set_option autoImplicit false

/-!
# A sound local Jacobian criterion

The minor construction in `AnalyticJacobianSingularCore` produces analytic
candidates for rank-defect loci.  This file records the direction that the
present API proves without adding a false singular-locus assertion: if the
*whole local set* is the zero locus of a finite family and the differentials of
that family are independent at the chosen point, then the set is locally
flattened to the expected coordinate plane.

A nonzero minor of an arbitrary, possibly redundant family cannot by itself
imply this conclusion.  For example, `(x,y)` has a nonzero `1 × 1` minor at
the origin while its common zero set in `ℂ²` has dimension zero, not one.
Thus the local zero-locus equality below is essential; it is precisely the
coherent-ideal / complete-intersection datum currently absent from
`LocalDecomposition`.
-/

open Set

namespace Hironaka.AnalyticJacobianCriterion

open Hironaka.RegularLocusDense AnalyticLocalStatement

open Hironaka

noncomputable section

variable {n : ℕ}

/-- A local complete-intersection presentation with independent differentials
produces a biholomorphic flattening at the specified point.  This is the
pointwise (rather than dense-existential) direction of the analytic implicit
function theorem needed by a Jacobian criterion. -/
theorem exists_flattening_of_localCompleteIntersection
    {S N : Set (ComplexModel n)} {q : ComplexModel n} {R : ℕ}
    {g : Fin R → ComplexModel n → ℂ}
    (hN : IsOpen N) (hqN : q ∈ N) (hqS : q ∈ S)
    (hg : ∀ r, DifferentiableOn ℂ (g r) N)
    (hzero : ∀ z ∈ N, z ∈ S ↔ ∀ r, g r z = 0)
    (hli : LinearIndependent ℂ (fun r => fderiv ℂ (g r) q)) :
    ∃ Φ : LocalHolomorphicEquivAt (n := n) q,
      Φ.source ⊆ N ∧ Φ.toFun q = 0 ∧
        ∀ z ∈ Φ.source,
          z ∈ S ↔ Φ.toFun z ∈ complexCoordinatePlane n (n - R) := by
  let hind : HasIndependentVanishing S q R :=
    ⟨g, N, hN, hqN, hg, fun r z hz => (hzero z hz.1).mp hz.2 r, hli⟩
  have hR : R ≤ n := hind.le
  obtain ⟨φ, hφd, hφ0, -, hφplane, hinj⟩ :=
    exists_coordinates_of_linearIndependent hR hN hqN hg
      (fun r => (hzero q hqN).mp hqS r) hli
  obtain ⟨Φ, hΦN, hΦF, -⟩ :=
    exists_localHolomorphicEquivAt hN hqN (differentiableOn_assemble hφd) hinj
  refine ⟨Φ, hΦN, ?_, ?_⟩
  · rw [hΦF]
    ext k
    simp [assemble_apply, hφ0]
  · intro z hz
    rw [hΦF, hφplane]
    exact hzero z (hΦN hz)


variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A local analytic presentation whose *entire* equation family has
independent differentials gives a certified `RegularAtDim` witness.  The
condition is intentionally on all generators: a rank condition on a selected
subfamily merely places the analytic set inside a smooth manifold and cannot
identify its dimension without a local complete-intersection hypothesis. -/
theorem regularAtDim_of_presentation_fullRank
    {S : Set M} {x : M} (P : ComplexAnalyticPresentationAt (n := n) S x)
    (hxS : x ∈ S)
    (hli : LinearIndependent ℂ (fun i =>
      fderiv ℂ (P.generator i) ((complexChartAt (n := n) x).val x))) :
    RegularAtDim (n := n) S x (n - P.generatorCount) := by
  let e := (complexChartAt (n := n) x).val
  let B : Set (ComplexModel n) := {z | e.symm z ∈ S}
  have hxe : x ∈ e.source := mem_complexChartAt_source x
  have hqN : e x ∈ P.coordinateNeighborhood := P.center_mem_coordinateNeighborhood
  have hqB : e x ∈ B := by
    change e.symm (e x) ∈ S
    rw [e.left_inv hxe]
    exact hxS
  have hzero : ∀ z ∈ P.coordinateNeighborhood,
      z ∈ B ↔ ∀ i, P.generator i z = 0 := by
    intro z hz
    have hzt : z ∈ e.target := P.coordinateNeighborhood_subset_target hz
    have h := P.zeroLocus (e.map_target hzt) (by rw [e.right_inv hzt]; exact hz)
    rwa [e.right_inv hzt] at h
  obtain ⟨Φ, hΦN, hΦ0, hΦflat⟩ :=
    exists_flattening_of_localCompleteIntersection
      P.isOpen_coordinateNeighborhood hqN hqB P.generator_holomorphic hzero hli
  refine ⟨Nat.sub_le _ _, hxS, Φ,
    hΦN.trans P.coordinateNeighborhood_subset_target, hΦ0, ?_⟩
  intro y hy hyΦ
  have h := hΦflat (e y) hyΦ
  simpa [B, e.left_inv hy] using h



/-- A nonzero square Jacobian minor using every member of an equation family
forces independence of its differentials.  This is the elementary linear
algebra bridge from a genuine full-row-rank minor to the local implicit
function theorem. -/
theorem linearIndependent_of_fullJacobianMinor_ne_zero
    {R : ℕ} {q : ComplexModel n} {g : Fin R → ComplexModel n → ℂ}
    (cols : Fin R → Fin n)
    (hminor : AnalyticJacobianSingularCore.jacobianMinor g (fun a => a) cols q ≠ 0) :
    LinearIndependent ℂ (fun a => fderiv ℂ (g a) q) := by
  let evalCols : (ComplexModel n →L[ℂ] ℂ) →ₗ[ℂ] (Fin R → ℂ) :=
    { toFun := fun L b => L (AnalyticJacobianSingularCore.coordinateDirection (cols b))
      map_add' := by
        intro L K
        ext b
        simp
      map_smul' := by
        intro c L
        ext b
        simp }
  let J : Matrix (Fin R) (Fin R) ℂ := Matrix.of fun a b =>
    fderiv ℂ (g a) q (AnalyticJacobianSingularCore.coordinateDirection (cols b))
  change J.det ≠ 0 at hminor
  apply LinearIndependent.of_comp evalCols
  change LinearIndependent ℂ (fun a : Fin R => J a)
  exact Matrix.linearIndependent_rows_of_det_ne_zero hminor

/-- The full-row-rank Jacobian direction for the project's actual local
analytic presentations.  No assertion is made for a selected minor of a
redundant presentation: here every generator is one row of the nonzero square
minor, so the preceding linear algebra theorem supplies the needed independent
differentials. -/
theorem regularAtDim_of_presentation_fullJacobianMinor_ne_zero
    {S : Set M} {x : M} (P : ComplexAnalyticPresentationAt (n := n) S x)
    (hxS : x ∈ S) (cols : Fin P.generatorCount → Fin n)
    (hminor : AnalyticJacobianSingularCore.jacobianMinor P.generator (fun a => a) cols
      ((complexChartAt (n := n) x).val x) ≠ 0) :
    RegularAtDim (n := n) S x (n - P.generatorCount) := by
  apply regularAtDim_of_presentation_fullRank P hxS
  exact linearIndependent_of_fullJacobianMinor_ne_zero cols hminor


/-- The full-row-rank criterion applied directly to one local-decomposition
branch.  The hypothesis `hp` is explicit because the current
`LocalDecomposition` interface does not record that every listed representative
contains its centre. -/
theorem regularAtDim_localPiece_of_fullJacobianMinor_ne_zero
    {A : Set M} {p : M} (D : LocalDecomposition (n := n) A p) (i : Fin D.count)
    (hp : p ∈ D.piece i) (cols : Fin (D.eqnCount i) → Fin n)
    (hminor : AnalyticJacobianSingularCore.jacobianMinor (D.eqn i) (fun a => a) cols
      ((complexChartAt (n := n) p).val p) ≠ 0) :
    RegularAtDim (n := n) (D.piece i) p (n - D.eqnCount i) := by
  let e := (complexChartAt (n := n) p).val
  let P : ComplexAnalyticPresentationAt (n := n) (D.piece i) p :=
    { generatorCount := D.eqnCount i
      generator := D.eqn i
      coordinateNeighborhood := e '' D.nbhd
      isOpen_coordinateNeighborhood :=
        e.isOpen_image_of_subset_source D.isOpen_nbhd D.nbhd_subset_source
      center_mem_coordinateNeighborhood := mem_image_of_mem e D.mem_nbhd
      coordinateNeighborhood_subset_target := fun z hz => by
        obtain ⟨y, hy, rfl⟩ := hz
        exact e.map_source (D.nbhd_subset_source hy)
      generator_holomorphic := D.eqn_holomorphic i
      zeroLocus := by
        intro y hy hyN
        obtain ⟨y', hyW, hy'e⟩ := hyN
        have hyW' : y ∈ D.nbhd := by
          rwa [← e.injOn (D.nbhd_subset_source hyW) hy hy'e]
        exact D.mem_piece_iff i y hyW' }
  have hreg := regularAtDim_of_presentation_fullJacobianMinor_ne_zero P hp cols (by
    simpa [P, e] using hminor)
  simpa [P] using hreg

/-- A nonzero `1 × 1` Jacobian minor is a sufficient regularity criterion for
an honest local hypersurface presentation.  Unlike a minor from a redundant
multi-equation presentation, this conclusion has the correct dimension
because the zero-locus equality has exactly one equation. -/
theorem regularAtDim_of_localHypersurfaceMinor_ne_zero
    {S : Set M} {x : M} {N : Set (ComplexModel n)}
    (f : ComplexModel n → ℂ)
    (hN : IsOpen N) (hqN : (complexChartAt (n := n) x).val x ∈ N)
    (hNtarget : N ⊆ (complexChartAt (n := n) x).val.target)
    (hf : DifferentiableOn ℂ f N)
    (hzero : ∀ {y : M},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ N →
        (y ∈ S ↔ f ((complexChartAt (n := n) x).val y) = 0))
    (hxS : x ∈ S) (j : Fin n)
    (hminor : fderiv ℂ f ((complexChartAt (n := n) x).val x)
      (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0) :
    RegularAtDim (n := n) S x (n - 1) := by
  let P : ComplexAnalyticPresentationAt (n := n) S x :=
    { generatorCount := 1
      generator := fun _ => f
      coordinateNeighborhood := N
      isOpen_coordinateNeighborhood := hN
      center_mem_coordinateNeighborhood := hqN
      coordinateNeighborhood_subset_target := hNtarget
      generator_holomorphic := fun _ => hf
      zeroLocus := fun hy hyN => by
        simpa using hzero hy hyN }
  have hli : LinearIndependent ℂ (fun _ : Fin 1 =>
      fderiv ℂ f ((complexChartAt (n := n) x).val x)) := by
    rw [linearIndependent_unique_iff]
    intro hzeroDeriv
    apply hminor
    rw [hzeroDeriv]
    rfl
  have hreg := regularAtDim_of_presentation_fullRank P hxS (by
    simpa [P] using hli)
  simpa [P] using hreg

end

end Hironaka.AnalyticJacobianCriterion
