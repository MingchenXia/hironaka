/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsDoubleLocusSeparation
import Hironaka.MarkedIdeal.GeoTransformWellFormed

/-! # Actual old-branch superlevels avoid born boundary and preserve cosupport

Genuine coordinate perturbations keep all old branch coordinates zero while
avoiding every actual boundary member. Closed actual current cosupport then
propagates at ANY mark; no stronger exceptional-power shortcut is assumed.
The original double-locus cosupport premise is explicit and qualified.
Blueprint: `hironaka-normal-crossings-boundary-avoidance-extension.tex`.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsBoundaryAvoidance

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsHighestStratumBlowup HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsBoundarySeparation HironakaNormalCrossingsDoubleLocusSeparation
  BlowupFlatCoordinates BlowupStrictSubmanifold BlowupTowerTransforms NormalCrossings MarkedIdeals
  MarkedIdeals.MarkedIdeal GermIdealOrder

noncomputable section
variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Every genuine intrinsic old-branch superlevel is approximated by its
actual points outside the whole boundary, with all branch labels intrinsic. -/
theorem branch_superlevel_subset_closure_off_boundary
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E) (r : ℕ) :
    {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} ⊆
      closure ({x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} \ ⋃ A ∈ E, A) := by
  classical
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  intro x hx
  obtain ⟨Φ,S,B,hsrc,h0,hflat,hB,hinj,hE⟩ := h.2.2 x
  have hrS : r ≤ S.card := hx.trans_eq (branchMultiplicity_eq_card hH Φ h0 S hflat)
  let v : ComplexModel n := WithLp.toLp 2 (fun i : Fin n => if i ∈ S then (0 : ℂ) else 1)
  have ht0 : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv := tendsto_flatInverse Φ (mem_flatDomain_self Φ)
  rw [h0] at hinv
  have hcurve : Tendsto (fun t : ℂ => t • v) (𝓝 0) (𝓝 (0 : ComplexModel n)) := by
    have hc : Continuous (fun t : ℂ => t • v) := continuous_id.smul continuous_const
    simpa using hc.tendsto (0 : ℂ)
  have hlimit := hinv.comp hcurve
  have hevE : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ i : Fin E.length, x ∉ E.get i →
      (chartAt (ComplexModel n) x).symm (Φ.invFun (t • v)) ∉ E.get i := by
    apply eventually_all.mpr
    intro i
    by_cases hxi : x ∈ E.get i
    · exact Eventually.of_forall fun _ hnot => False.elim (hnot hxi)
    · have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
          (chartAt (ComplexModel n) x).symm (Φ.invFun (t • v)) ∉ E.get i :=
        mem_nhdsWithin_of_mem_nhds
          (hlimit ((h.2.1 _ (List.get_mem E i)).isOpen_compl.mem_nhds hxi))
      exact hev.mono fun _ ht _ => ht
  rw [mem_closure_iff_nhds]
  intro U hU
  have hevT : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • v ∈ Φ.target :=
    mem_nhdsWithin_of_mem_nhds (hcurve (Φ.isOpen_target.mem_nhds ht0))
  have hevU : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      (chartAt (ComplexModel n) x).symm (Φ.invFun (t • v)) ∈ U :=
    mem_nhdsWithin_of_mem_nhds (hlimit hU)
  obtain ⟨t,htT,htU,htE,htne⟩ := (hevT.and (hevU.and (hevE.and self_mem_nhdsWithin))).exists
  obtain ⟨hdom,hcoord⟩ := flatInverse_mem Φ htT hsrc
  refine ⟨_,htU,?_,?_⟩
  · have heq : branchMultiplicity hH
        ((chartAt (ComplexModel n) x).symm (Φ.invFun (t • v))) = S.card := by
      rw [branchMultiplicity_eq_filter_card hH Φ S hflat hdom]
      have hfilter : S.filter (fun i => flatCoord Φ i
          ((chartAt (ComplexModel n) x).symm (Φ.invFun (t • v))) = 0) = S := by
        apply Finset.filter_eq_self.mpr
        intro i hi
        change Φ.toFun (chartAt (ComplexModel n) x _) i = 0
        rw [hcoord]
        change t * (if i ∈ S then (0 : ℂ) else 1) = 0
        simp only [if_pos hi,mul_zero]
      rw [hfilter]
    exact hrS.trans_eq heq.symm
  · intro hyE
    obtain ⟨A,hA,hyA⟩ := mem_iUnion₂.mp hyE
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hA
    by_cases hxi : x ∈ E.get i
    · obtain ⟨j,hBj⟩ := Finset.card_eq_one.mp (hB i hxi).1
      have hjB : j ∈ B i := by rw [hBj]; exact Finset.mem_singleton_self j
      have hjS : j ∉ S := fun hj => Finset.disjoint_left.mp (hB i hxi).2 hj hjB
      have hz := ((hE i hxi _ hdom).mp hyA) j hjB
      rw [hcoord] at hz
      change t * (if j ∈ S then (0 : ℂ) else 1) = 0 at hz
      simp only [if_neg hjS,mul_one] at hz
      exact htne hz
    · exact htE i hxi hyA

/-- At every mark, the SAME actual coherent current cosupport propagates from
the off-boundary old-branch superlevel to its entire intrinsic superlevel. -/
theorem branch_superlevel_subset_cosupp_of_off_boundary
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) (r : ℕ)
    (hoff : {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} \ ⋃ A ∈ M.E, A ⊆ M.cosupp) :
    {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} ⊆ M.cosupp :=
  (branch_superlevel_subset_closure_off_boundary h r).trans
    (closure_minimal hoff (GiraudAlong.isClosed_cosupport_along hI hN M.d))

private theorem branchMultiplicity_congr {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {H K : Set Y}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hK : IsNormalCrossingsCarrier (n := n) K)
    (heq : H = K) (x : Y) : branchMultiplicity hH x = branchMultiplicity hK x := by
  subst K
  rfl

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The SAME original ideal at its ACTUAL mark admits the highest old-branch
step, and the actual transformed double locus stays in its LITERAL controlled
cosupport. Original D2 cosupport is explicit; no exceptional-power input is used. -/
theorem highest_step_doubleLocus_subset_controlled_cosupport
    (M : MarkedIdeal n X) (hN : M.N = univ) (hw : M.IsWellFormed)
    {H : Set X} (h : IsBoundaryAdaptedCarrier (n := n) H M.E) {r : ℕ} (hr : 2 ≤ r)
    (hbound : ∀ x : X, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    {π : Y → X}
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π)
    (hD2 : {x | 2 ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} ⊆ M.cosupp) :
    let C := {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let hp := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_strict_highest h hbound hπ)
    M.IsAdmissibleCentre C ∧ {z | 2 ≤ branchMultiplicity hp z} ⊆
      cosupport n univ (BlowupControlledTransform.controlledTransform hπ M.ideal M.d) M.d := by
  dsimp only
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  let C := {x | r ≤ branchMultiplicity hH x}
  have hC : M.IsAdmissibleCentre C :=
    ⟨isClosedSubmanifold_highest_superlevel hH hbound,
      fun x hx => hD2 (hr.trans hx),hasNormalCrossings_highest_boundary h hbound⟩
  have hpair' : IsBoundaryAdaptedCarrier (n := n) (geoStrictTransform π C H) (M.geoTransform C π).E :=
    boundaryAdapted_strict_highest h hbound hπ
  have hw' := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hw hC hπ
  let hH' := isNormalCrossingsCarrier_of_boundaryAdapted hpair'
  have hD2' : {z | 2 ≤ branchMultiplicity hH' z} ⊆ (M.geoTransform C π).cosupp := by
    apply branch_superlevel_subset_cosupp_of_off_boundary (M.geoTransform C π)
      hw'.isCoherent hw'.isClosedSubmanifold_N hpair' 2
    rintro z ⟨hz,hzE⟩
    have hEex : π ⁻¹' C ∈ (M.geoTransform C π).E := by
      change π ⁻¹' C ∈ M.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
    have hzC : π z ∉ C := fun hzc => hzE (mem_iUnion₂.mpr ⟨π ⁻¹' C,hEex,hzc⟩)
    have heq := geoStrictTransform_highest_eq_strictTransform hH hr hbound hπ
    have hp : IsNormalCrossingsCarrier (n := n) (strictTransform n π H) := heq ▸ hH'
    have hzc : 2 ≤ branchMultiplicity hp z :=
      hz.trans_eq (branchMultiplicity_congr hH' hp heq z)
    have himage : 2 ≤ branchMultiplicity hH (π z) :=
      hzc.trans (branchMultiplicity_strict_highest_le_image hH hr hbound hπ hp z)
    exact TransformOffCentre.mem_cosupp_geoTransform_of_mem_cosupp M hw.isClosedSubmanifold_N.1 hπ hzC (hD2 himage)
  refine ⟨hC,fun z hz => ?_⟩
  have hz' := hD2' hz
  change z ∈ cosupport n (M.geoTransform C π).N (M.geoTransform C π).ideal (M.geoTransform C π).d at hz'
  rw [geoTransform_N_eq_univ hN hπ,geoTransform_ideal_eq_controlledTransform hN hw.isCoherent hπ,
    geoTransform_d] at hz'
  exact hz'

end
end Hironaka.HironakaNormalCrossingsBoundaryAvoidance
