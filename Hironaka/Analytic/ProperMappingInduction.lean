/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.ProperImageIrreducible
import Hironaka.Analytic.GlobalComponents

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Remmert's proper mapping theorem: the induction on the dimension

Blueprint `rem:proper-mapping` (Demailly, *Complex analytic and differential geometry*, II.8.8).
The steps of the simultaneous induction that do not involve the Remmert--Stein theorem:

* `properImageStatement_zero`: `(R_0)`.  An analytic set of dimension `≤ 0` is discrete
  (`AnalyticDimensionBasics.not_accPt_of_locDimLE_zero`), so near every point of `Y` its image is
  the image of a compact discrete, hence finite, set; finite sets are analytic.
* `properImageStatement_succ`: `(R_m)` and `(RS_{m+1})` give `(R_{m+1})`.  Near a point of `Y` the
  compact set `A ∩ F⁻¹ K` meets only finitely many global irreducible components of `A`
  (`GlobalComponents`), each of dimension `≤ m + 1` with `F` proper on it, whose images are
  analytic by `ProperImageIrreducible`; a finite union of analytic sets is analytic.
* `properImageStatement_of_remmertStein`: if `(R_m)` for manifolds in `Type` gives `(RS_{m+1})` both
  in `Type` and in `Type u₂`, then `(R_m)` holds for all `m` and all manifolds `X : Type u₁`,
  `Y : Type u₂`.

Sorry-free.
-/

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.ProperMappingInduction

open AnalyticDimensionBasics RemmertStatements ConstantRankImage
  ProperImageIrreducible GlobalComponents DimensionMonotone FibreDimensionLowerBound

universe u₁ u₂

/-- A finite set is analytic. -/
theorem isComplexAnalyticSubset_of_finite {k : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y] {T : Set Y} (hT : T.Finite) :
    IsComplexAnalyticSubset (n := k) T := by
  have h := isComplexAnalyticSubset_biUnion (n := k) hT.toFinset
    (S := fun y => ({y} : Set Y)) fun y _ => isComplexAnalyticSubset_singleton y
  have hset : (⋃ y ∈ hT.toFinset, ({y} : Set Y)) = T := by
    ext y
    simp
  rwa [hset] at h

/-- **`(R_0)`.** -/
theorem properImageStatement_zero : ProperImageStatement.{u₁, u₂} 0 := by
  intro n k X _ _ _ Y _ _ _ F hF A hA hdim hprop
  have : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace (ComplexModel k) Y
  have hdisc : IsDiscrete A := isDiscrete_iff_nhdsNE.mpr fun x hx => by
    have h := not_accPt_of_locDimLE_zero hA hx (hdim.locDimLE x)
    rw [AccPt, not_neBot] at h
    exact h
  intro y
  obtain ⟨K, hKc, hKy⟩ := exists_compact_mem_nhds y
  have hfin : (A ∩ F ⁻¹' K).Finite := (hprop K hKc).finite (hdisc.mono inter_subset_left)
  have hT : IsComplexAnalyticSubset (n := k) (F '' (A ∩ F ⁻¹' K)) :=
    isComplexAnalyticSubset_of_finite (hfin.image F)
  refine nonempty_presentation_of_inter_eq isOpen_interior (mem_interior_iff_mem_nhds.mpr hKy)
    ?_ (hT y).some
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hz⟩
    exact ⟨⟨x, ⟨hx, (interior_subset hz : F x ∈ K)⟩, rfl⟩, hz⟩
  · rintro ⟨⟨x, hx, rfl⟩, hz⟩
    exact ⟨⟨x, hx.1, rfl⟩, hz⟩

/-- **`(R_m)` and `(RS_{m+1})` give `(R_{m+1})`.** -/
theorem properImageStatement_succ {m : ℕ} (hR : ProperImageStatement.{u₁, u₂} m)
    (hRS : RemmertSteinStatement.{u₂} (m + 1)) : ProperImageStatement.{u₁, u₂} (m + 1) := by
  intro n k X _ _ _ Y _ _ _ F hF A hA hdim hprop
  have : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace (ComplexModel k) Y
  have hR' : ProperImageStatement.{u₁, u₂} (m + 1 - 1) := by rwa [Nat.add_sub_cancel]
  have hcomp : ∀ C ∈ globalComponents (n := n) A,
      IsComplexAnalyticSubset (n := k) (F '' C) := by
    intro C hC
    have hCA := subset_of_mem_globalComponents hA hC
    have hCirr := isComplexAnalyticallyIrreducible_of_mem_globalComponents hA hC
    refine isComplexAnalyticSubset_image_of_irreducible hR' hRS hF hCirr
      (DimLE.anti hA hCA hdim) fun K hK => ?_
    exact (hprop K hK).of_isClosed_subset
      (hCirr.analytic.isClosed.inter (hK.isClosed.preimage hF.continuous))
      (inter_subset_inter_left _ hCA)
  intro y
  obtain ⟨K, hKc, hKy⟩ := exists_compact_mem_nhds y
  have hfinI := (locallyFinite_globalComponents hA).finite_nonempty_inter_compact (hprop K hKc)
  set t := hfinI.toFinset with ht
  have hT : IsComplexAnalyticSubset (n := k) (⋃ C ∈ t, F '' (C : Set X)) :=
    isComplexAnalyticSubset_biUnion t fun C _ => hcomp C C.2
  refine nonempty_presentation_of_inter_eq isOpen_interior (mem_interior_iff_mem_nhds.mpr hKy)
    ?_ (hT y).some
  ext z
  simp only [mem_inter_iff, mem_iUnion, mem_image, exists_prop]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hz⟩
    refine ⟨?_, hz⟩
    rw [← sUnion_globalComponents hA] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    refine ⟨⟨C, hC⟩, ?_, x, hxC, rfl⟩
    rw [ht, Set.Finite.mem_toFinset]
    exact ⟨x, hxC, ⟨subset_of_mem_globalComponents hA hC hxC, (interior_subset hz : F x ∈ K)⟩⟩
  · rintro ⟨⟨C, -, x, hxC, rfl⟩, hz⟩
    exact ⟨⟨x, subset_of_mem_globalComponents hA C.2 hxC, rfl⟩, hz⟩

/-- **The induction.**  If `(R_m)` in `Type` gives `(RS_{m+1})` in `Type` and in `Type u₂`, then
`(R_m)` holds for every `m` and all manifolds `X : Type u₁`, `Y : Type u₂`. -/
theorem properImageStatement_of_remmertStein
    (hRS₀ : ∀ m, ProperImageStatement.{0, 0} m → RemmertSteinStatement.{0} (m + 1))
    (hRS : ∀ m, ProperImageStatement.{0, 0} m → RemmertSteinStatement.{u₂} (m + 1)) :
    ∀ m, ProperImageStatement.{u₁, u₂} m := by
  have h₀ : ∀ m, ProperImageStatement.{0, 0} m := by
    intro m
    induction m with
    | zero => exact properImageStatement_zero
    | succ m ih => exact properImageStatement_succ ih (hRS₀ m ih)
  intro m
  induction m with
  | zero => exact properImageStatement_zero
  | succ m ih => exact properImageStatement_succ ih (hRS m (h₀ m))

end Hironaka.ProperMappingInduction
