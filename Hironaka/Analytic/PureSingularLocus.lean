import Hironaka.Analytic.GeometricPureDimensionBound
import Hironaka.Analytic.GeometricPureDimension
import Hironaka.Analytic.ThinDimensionBoundPredecessor
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.StokesSingularLocusAnalytic
import Hironaka.Analytic.ThinDimensionDrop

set_option autoImplicit false

/-!
# The singular locus of a pure-dimensional analytic set

Blueprint `rem:pure-singular-locus` (Demailly, *Complex analytic and differential geometry*, II.4.31),
step M6 of the route to Remmert's proper mapping theorem (`blueprint/src/remmert.tex`).

Let `A` be an analytic subset of pure dimension `k` (every regular point has dimension `k`) of a
complex manifold of dimension `n`.  The proofs of `StokesSingularLocusAnalytic`, written for a
closed irreducible subvariety, use irreducibility only through pure dimensionality; here they are
run for `A`:

* `regularAtDim_of_minor_ne_zero_of_isPureDim`: in the preferred chart at `x`, if Cartan
  generators `sᵢ` of the ideal of `A` have a nonzero `(n - k)`-minor of their Jacobian at a point
  `y ∈ A`, then `A` is regular of dimension `k` at `y` (the converse is the general
  `StokesSingularLocusAnalytic.le_finrank_span_fderiv_of_regularAtDim`);
* `isComplexAnalyticSubset_diff_regularLocus`: `A_sing = A \ A_reg` is analytic, cut out near every
  point by the `sᵢ` and all `(n - k)`-minors of their Jacobian;
* `dimLE_diff_regularLocus`: `dim A_sing ≤ k - 1` (`A_sing` has empty interior in `A` because the
  regular points are dense, `ThinDimensionDrop.dimLE_pred_of_thin`).

Sorry-free.
-/

open Set Filter Module
open scoped Topology Manifold

namespace Hironaka.PureSingularLocus

open AnalyticJacobianSingularCore StokesSingularLocusAnalytic AnalyticDimensionBasics

open Hironaka

noncomputable section

variable {n : ℕ}

section Manifold

open RegularPatchNeighborhood RegularLocusDense HolomorphicIdealSheaves

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A nonzero maximal Jacobian minor at a point of a pure-dimensional set forces regularity**
(`demailly-cadg:II.4.31`).  In the preferred chart at `x`, let `sᵢ` cut out `A` (of pure dimension
`k`) on an open set `U`.  If an `(n - k)`-minor of the Jacobian of the `sᵢ` is nonzero at a point
`y ∈ A ∩ U`, then `A` is regular of dimension `k` at `y`. -/
theorem regularAtDim_of_minor_ne_zero_of_isPureDim {A : Set M} {k : ℕ} (hk : k ≤ n)
    (hpure : IsPureDim (n := n) A k) (x : M)
    {U : Set M} (hU : IsOpen U) {N : ℕ} {s : Fin N → M → ℂ}
    (hs : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) U)
    (hzero : ∀ y ∈ U, (y ∈ A ↔ ∀ i, s i y = 0))
    {y : M} (hyU : y ∈ U) (hye : y ∈ (complexChartAt (n := n) x).val.source)
    (hyV : y ∈ A) (rows : Fin (n - k) → Fin N) (cols : Fin (n - k) → Fin n)
    (hminor : jacobianMinor (fun i w => s i ((complexChartAt (n := n) x).val.symm w)) rows cols
      ((complexChartAt (n := n) x).val y) ≠ 0) :
    RegularAtDim (n := n) A y k := by
  classical
  set e := (complexChartAt (n := n) x).val with he
  set g : Fin N → ComplexModel n → ℂ := fun i w => s i (e.symm w) with hg
  set W : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' U with hW
  have hWo : IsOpen W := e.isOpen_inter_preimage_symm hU
  have hqt : e y ∈ e.target := e.map_source hye
  have hsq : e.symm (e y) = y := e.left_inv hye
  have hqW : e y ∈ W := ⟨hqt, by rw [mem_preimage, hsq]; exact hyU⟩
  have hgd : ∀ i, DifferentiableOn ℂ (g i) W := fun i z hz =>
    (differentiableAt_chart (complexChartAt (n := n) x) hz.1
      ((hs i).mdifferentiableAt (hU.mem_nhds hz.2))).differentiableWithinAt
  have hWV : ∀ z ∈ W, (e.symm z ∈ A ↔ ∀ i, g i z = 0) := fun z hz => hzero _ hz.2
  have hyg : ∀ i, g i (e y) = 0 := (hWV _ hqW).mp (by rw [hsq]; exact hyV)
  -- the selected equations have independent differentials and cut out a manifold `Z ⊇ V`
  have hli : LinearIndependent ℂ (fun a => fderiv ℂ (g (rows a)) (e y)) :=
    AnalyticJacobianCriterion.linearIndependent_of_fullJacobianMinor_ne_zero
      (g := fun a => g (rows a)) cols hminor
  obtain ⟨Φ, hΦW, hΦ0, hΦflat⟩ :=
    AnalyticJacobianCriterion.exists_flattening_of_localCompleteIntersection
      (S := {z | ∀ a, g (rows a) z = 0}) hWo hqW (fun a => hyg (rows a))
      (fun a => hgd (rows a)) (fun z _ => Iff.rfl) hli
  have hnk : n - (n - k) = k := by omega
  rw [hnk] at hΦflat
  -- a ball `D` of the plane on which `V ∩ Z` is read
  have h0t : coordinateInclusion n k 0 ∈ Φ.target := by
    rw [map_zero, ← hΦ0]; exact Φ.mapsTo_toFun Φ.center_mem_source
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp
    (Φ.isOpen_target.preimage (coordinateInclusion n k).continuous) 0 h0t
  set D : Set (ComplexModel k) := Metric.ball 0 ρ with hD
  have hinvS : ∀ w ∈ D, Φ.invFun (coordinateInclusion n k w) ∈ Φ.source := fun w hw =>
    Φ.mapsTo_invFun (hball hw)
  set G : Fin N → ComplexModel k → ℂ := fun i w => g i (Φ.invFun (coordinateInclusion n k w))
    with hG
  have hGd : ∀ i, DifferentiableOn ℂ (G i) D := fun i =>
    (hgd i).comp (Φ.invFun_holomorphic.comp (coordinateInclusion n k).differentiableOn
      fun w hw => hball hw) fun w hw => hΦW (hinvS w hw)
  have h0D : (0 : ComplexModel k) ∈ D := Metric.mem_ball_self hρ
  have hinv0 : Φ.invFun (coordinateInclusion n k 0) = e y := by
    rw [map_zero, ← hΦ0, Φ.left_inv _ Φ.center_mem_source]
  have h0DV : (0 : ComplexModel k) ∈ {w | ∀ i, G i w = 0} := fun i => by
    simp only [hG, hinv0]; exact hyg i
  -- a regular point of `V ∩ Z` read on the ball, of some dimension `j ≤ k`
  obtain ⟨w₁, ⟨⟨hw₁DV, hw₁D⟩, -⟩, j, hjk, Φ₁, hΦ₁D, -, hΦ₁flat⟩ :=
    exists_flattening_of_isZeroLocus (n := k) Metric.isOpen_ball Metric.isOpen_ball hGd
      (fun w _ => Iff.rfl) h0DV h0D h0D
  set p := Φ.invFun (coordinateInclusion n k w₁) with hp
  have hpΦ : p ∈ Φ.source := hinvS w₁ hw₁D
  have hΦp : Φ.toFun p = coordinateInclusion n k w₁ := Φ.right_inv _ (hball hw₁D)
  set Θ := RegularAtDimTransport.LocalHolomorphicEquivAt.comp
    (Φ.restrict univ isOpen_univ p ⟨hpΦ, trivial⟩) (extendLHE hk Φ₁) hΦp with hΘ
  have hΘflat : ∀ z ∈ Θ.source,
      (e.symm z ∈ A ↔ Θ.toFun z ∈ complexCoordinatePlane n j) := by
    intro z hz
    have hzΦ : z ∈ Φ.source := hz.1.1
    have hzW : z ∈ W := hΦW hzΦ
    have hz1 : coordinateProjection n k (Φ.toFun z) ∈ Φ₁.source := hz.2
    change _ ↔ extendFirst k Φ₁.toFun (Φ.toFun z) ∈ _
    rw [extendFirst_mem_plane_iff hk hjk, hWV z hzW]
    constructor
    · intro hz0
      have hZ : Φ.toFun z ∈ complexCoordinatePlane n k :=
        (hΦflat z hzΦ).mp fun a => hz0 (rows a)
      refine ⟨(hΦ₁flat _ hz1).mp fun i => ?_, hZ⟩
      simp only [hG]
      rw [coordinateInclusion_coordinateProjection hZ, Φ.left_inv z hzΦ]
      exact hz0 i
    · rintro ⟨h1, hZ⟩ i
      have h2 := (hΦ₁flat _ hz1).mpr h1 i
      simp only [hG] at h2
      rwa [coordinateInclusion_coordinateProjection hZ, Φ.left_inv z hzΦ] at h2
  -- that point is a regular point of `V` of dimension `j`, so `j = dim V`
  have hpe : p ∈ e.target := (hΦW hpΦ).1
  have hy₁ : RegularAtDim (n := n) A (e.symm p) j := by
    refine regularAtDim_of_flattening_of_mem (x := x) (le_trans hjk hk) Θ ?_
      ((hWV p (hΦW hpΦ)).mpr fun i => hw₁DV i) (e.map_target hpe) ?_
    · intro y' hy' hy'Θ
      have h := hΘflat (e y') hy'Θ
      rwa [e.left_inv hy'] at h
    · rw [e.right_inv hpe]; exact Θ.center_mem_source
  have hjk' : j = k := hpure _ _ hy₁
  -- so `V ∩ Z` has interior in the ball, and by the identity theorem it is the whole ball
  have hsub : ∀ w ∈ Φ₁.source, ∀ i, G i w = 0 := fun w hw =>
    (hΦ₁flat w hw).mpr (by
      rw [hjk']; intro i hi; exact absurd i.2 (not_lt.mpr hi))
  have hDall : ∀ w ∈ D, ∀ i, G i w = 0 := fun w hw i =>
    eqOn_zero_of_isOpen_convex Metric.isOpen_ball (convex_ball 0 ρ) (hGd i) Φ₁.isOpen_source
      (fun w' hw' => (hΦ₁D hw').1) ⟨w₁, Φ₁.center_mem_source⟩ (fun w' hw' => hsub w' hw' i) hw
  -- near `e y`, `V` is exactly `Z`
  set O : Set (ComplexModel n) := Φ.source ∩ Φ.toFun ⁻¹' (coordinateProjection n k ⁻¹' D)
    with hO
  have hOo : IsOpen O := Φ.toFun_holomorphic.continuousOn.isOpen_inter_preimage
    Φ.isOpen_source (Metric.isOpen_ball.preimage (coordinateProjection n k).continuous)
  have hqO : e y ∈ O := ⟨Φ.center_mem_source, by simp [hΦ0, h0D]⟩
  have hOflat : ∀ z ∈ O, (e.symm z ∈ A ↔ Φ.toFun z ∈ complexCoordinatePlane n k) := by
    intro z hz
    rw [hWV z (hΦW hz.1)]
    constructor
    · intro h0; exact (hΦflat z hz.1).mp fun a => h0 (rows a)
    · intro hZ i
      have h2 := hDall _ hz.2 i
      simp only [hG] at h2
      rwa [coordinateInclusion_coordinateProjection hZ, Φ.left_inv z hz.1] at h2
  refine regularAtDim_of_flattening_of_mem (x := x) hk
    (Φ.restrict O hOo (e y) ⟨Φ.center_mem_source, hqO⟩) ?_ hyV hye ⟨Φ.center_mem_source, hqO⟩
  intro y' hy' hy'O
  have h := hOflat (e y') hy'O.2
  rwa [e.left_inv hy'] at h

/-- **The singular locus of a pure-dimensional analytic set is analytic** (`demailly-cadg:II.4.31`),
assuming `k ≤ n`: in the preferred chart at any point it is cut out by Cartan generators `sᵢ` of the
ideal of `A` and all `(n - k)`-minors of their Jacobian. -/
theorem isComplexAnalyticSubset_diff_regularLocus_of_le {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {k : ℕ} (hk : k ≤ n) (hpure : IsPureDim (n := n) A k) :
    IsComplexAnalyticSubset (n := n) (A \ regularLocus (n := n) A k) := by
  classical
  intro x
  obtain ⟨U, hU, hxU, N, s, hs, hspan, hzeroU⟩ :=
    StokesSingularLocus.exists_cartanGenerators hA hA.isClosed x
  set e := (complexChartAt (n := n) x).val with he
  set g : Fin N → ComplexModel n → ℂ := fun i w => s i (e.symm w) with hg
  set W : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' U with hW
  have hWo : IsOpen W := e.isOpen_inter_preimage_symm hU
  have hgd : ∀ i, DifferentiableOn ℂ (g i) W := fun i z hz =>
    (differentiableAt_chart (complexChartAt (n := n) x) hz.1
      ((hs i).mdifferentiableAt (hU.mem_nhds hz.2))).differentiableWithinAt
  have hxe : x ∈ e.source := mem_complexChartAt_source x
  refine ⟨{ generatorCount := N + Fintype.card (JacobianMinorIndex N n (n - k))
            generator := Fin.addCases g (jacobianMinorGenerator (n := n) (r := n - k) g)
            coordinateNeighborhood := W
            isOpen_coordinateNeighborhood := hWo
            center_mem_coordinateNeighborhood :=
              ⟨e.map_source hxe, by rw [mem_preimage, e.left_inv hxe]; exact hxU⟩
            coordinateNeighborhood_subset_target := inter_subset_left
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · intro a
    refine Fin.addCases ?_ ?_ a
    · intro j; simpa using hgd j
    · intro j
      simpa using differentiableOn_jacobianMinorGenerator (n := n) (r := n - k) hWo hgd j
  · intro y hye hyW
    have hyU : y ∈ U := by
      have := hyW.2
      rwa [mem_preimage, e.left_inv hye] at this
    have hgy : ∀ i, g i ((complexChartAt (n := n) x).val y) = s i y := fun i => by
      simp only [hg]
      rw [he, (complexChartAt (n := n) x).val.left_inv hye]
    rw [Fin.forall_fin_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    constructor
    · rintro ⟨hyV, hyreg⟩
      refine ⟨fun i => by rw [hgy]; exact (hzeroU y hyU).mp hyV i, fun b => ?_⟩
      by_contra hb
      exact hyreg (regularAtDim_of_minor_ne_zero_of_isPureDim hk hpure x hU hs hzeroU hyU hye hyV _ _ hb)
    · rintro ⟨hs0, hminor⟩
      have hyV := (hzeroU y hyU).mpr fun i => by rw [← hgy]; exact hs0 i
      refine ⟨hyV, fun hreg => ?_⟩
      obtain ⟨rows, cols, hrc⟩ := exists_minor_ne_zero_of_le_finrank _
        (le_finrank_span_fderiv_of_regularAtDim hU hs hspan hzeroU (complexChartAt (n := n) x)
          hyU hye hreg)
      apply hrc
      have h := hminor ((Fintype.equivFin (JacobianMinorIndex N n (n - k))) (rows, cols))
      simpa [jacobianMinorGenerator, jacobianMinor, hg] using h

/-- **The singular locus of a pure-dimensional analytic set is analytic.** -/
theorem isComplexAnalyticSubset_diff_regularLocus {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {k : ℕ} (hpure : IsPureDim (n := n) A k) :
    IsComplexAnalyticSubset (n := n) (A \ regularLocus (n := n) A k) := by
  by_cases hk : k ≤ n
  · exact isComplexAnalyticSubset_diff_regularLocus_of_le hA hk hpure
  · -- no regular point of dimension `k > n` exists, so `A` has no regular point, so `A = ∅`
    have hA0 : A = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
      obtain ⟨y, -, j, hy⟩ := exists_regularAtDim_mem_nhds hA hx univ_mem
      have hj := hpure y j hy
      exact hk (hj ▸ hy.1)
    rw [hA0, empty_sdiff]
    exact isComplexAnalyticSubset_empty

/-- **`A_sing` has empty interior in `A`**: an open set meeting `A` only in singular points
does not meet `A`. -/
theorem thin_diff_regularLocus {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) {k : ℕ}
    (hpure : IsPureDim (n := n) A k) (O : Set M) (hO : IsOpen O)
    (hOA : O ∩ A ⊆ A \ regularLocus (n := n) A k) : O ∩ A = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨y, hyO, j, hy⟩ := exists_regularAtDim_mem_nhds hA hx.2 (hO.mem_nhds hx.1)
  have hyk : RegularAtDim (n := n) A y k := hpure y j hy ▸ hy
  exact (hOA ⟨hyO, hy.2.1⟩).2 hyk

/-- **`dim A_sing ≤ k - 1`.** -/
theorem dimLE_diff_regularLocus {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) {k : ℕ}
    (hpure : IsPureDim (n := n) A k) :
    DimLE (n := n) (A \ regularLocus (n := n) A k) (k - 1) :=
  ThinDimensionDrop.dimLE_pred_of_thin hA sdiff_subset (thin_diff_regularLocus hA hpure)
    hpure.dimLE

end Manifold

end

end Hironaka.PureSingularLocus
