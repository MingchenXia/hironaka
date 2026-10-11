import Hironaka.Analytic.HolomorphicFlatteningRecenter
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaNormalCrossingsLocalBranches
import Hironaka.Resolution.HironakaNormalCrossingsBranchOverlap
import Hironaka.Analytic.RankDegeneracy

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-!
# Intrinsic highest-multiplicity strata of general normal crossings

Actual chart branch bijections produce an intrinsic count. Genuine chart
transitions produce its exact nearby values, its closed superlevels, and
the whole highest stratum as a closed smooth centre of codimension r.
No compactness, global branch labels or supplied smooth centre are inputs.
Containment in an additional marked ideal cosupport is a separate obligation.
Blueprint: `hironaka-normal-crossings-multiplicity-strata-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaNormalCrossingsMultiplicityStrata

open Hironaka.BlowupSequences BlowupFlatCoordinates
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsBranchOverlap
  RegularAtDimTransport RegularPatchPullback RankDegeneracy

open Hironaka

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private def preferredFlattening {H : Set M} (hH : IsNormalCrossingsCarrier (n := n) H)
    (x : M) := Classical.choose (hH.2 x)

private def preferredBranches {H : Set M} (hH : IsNormalCrossingsCarrier (n := n) H)
    (x : M) : Finset (Fin n) :=
  Classical.choose (Classical.choose_spec (hH.2 x)).2.2

/-- The number of actual distinct local branches, independent of their ordering. -/
def branchMultiplicity {H : Set M} (hH : IsNormalCrossingsCarrier (n := n) H) (x : M) : ℕ :=
  (preferredBranches hH x).card

/-- Every actual centred normal-crossing flattening computes the intrinsic count. -/
theorem branchMultiplicity_eq_card {H : Set M} (hH : IsNormalCrossingsCarrier (n := n) H)
    {x : M} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (S : Finset (Fin n))
    (hΦH : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0) :
    branchMultiplicity hH x = S.card := by
  have hspec := Classical.choose_spec (hH.2 x)
  have hbr := Classical.choose_spec hspec.2.2
  obtain ⟨σ, hcard, -⟩ := exists_original_branch_equiv_intersections
    (preferredFlattening hH x) Φ hspec.2.1 hΦ0 (preferredBranches hH x) S hbr hΦH
  exact hcard

omit [IsComplexManifold n M] in
theorem branchMultiplicity_le {H : Set M} (hH : IsNormalCrossingsCarrier (n := n) H) (x : M) :
    branchMultiplicity hH x ≤ n := by
  have h := Finset.card_le_card (Finset.subset_univ (preferredBranches hH x))
  simpa [branchMultiplicity] using h

theorem branchMultiplicity_pos_iff {H : Set M} (hH : IsNormalCrossingsCarrier (n := n) H) (x : M) :
    0 < branchMultiplicity hH x ↔ x ∈ H := by
  have hspec := Classical.choose_spec (hH.2 x)
  have hbr := Classical.choose_spec hspec.2.2
  rw [hbr x (mem_flatDomain_self (preferredFlattening hH x))]
  change 0 < (preferredBranches hH x).card ↔
    ∃ j ∈ preferredBranches hH x, flatCoord (preferredFlattening hH x) j x = 0
  have hz : ∀ j : Fin n, flatCoord (preferredFlattening hH x) j x = 0 := by
    intro j
    change (Classical.choose (hH.2 x)).toFun (chartAt (ComplexModel n) x x) j = 0
    rw [hspec.2.1]
    rfl
  simp only [hz, and_true, Finset.card_pos]
  rfl

/-- The actual chart transition and original inverse produce translated coordinates
at every point of the original flattening domain. -/
private theorem exists_recentred_flattening {x y : M}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hy : y ∈ flatDomain Φ) {O : Set M} (hO : IsOpen O) (hyO : y ∈ O)
    (hOsub : O ⊆ flatDomain Φ) :
    ∃ Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) y y),
      Θ.source ⊆ (chartAt (ComplexModel n) y).target ∧
      Θ.toFun (chartAt (ComplexModel n) y y) = 0 ∧
      ∀ z ∈ flatDomain Θ, z ∈ O ∧
        Θ.toFun (chartAt (ComplexModel n) y z) =
          Φ.toFun (chartAt (ComplexModel n) x z) - Φ.toFun (chartAt (ComplexModel n) x y) := by
  let e := chartAt (ComplexModel n) y
  let d := chartAt (ComplexModel n) x
  let N : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' O
  let F : ComplexModel n → ComplexModel n := fun z => d (e.symm z)
  have hNo : IsOpen N := e.isOpen_inter_preimage_symm hO
  have hyN : e y ∈ N := ⟨e.map_source (mem_chart_source _ y), by
    rw [mem_preimage, e.left_inv (mem_chart_source _ y)]; exact hyO⟩
  have hFd : DifferentiableOn ℂ F N := by
    intro z hz
    have hd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) d (e.symm z) :=
      mdifferentiableAt_chart (hOsub hz.2).1
    exact (mdifferentiableAt_iff_differentiableAt.mp
      (hd.comp z (mdifferentiableAt_chart_symm hz.1))).differentiableWithinAt
  have hFinj : Function.Injective (fderiv ℂ F (e y)) :=
    injective_fderiv_transition (complexChartAt (n := n) y) (complexChartAt (n := n) x)
      (mem_chart_source _ y) hy.1
  obtain ⟨Ψ, hΨN, hΨF, -⟩ := exists_localHolomorphicEquivAt hNo hyN hFd hFinj
  have hΨy : Ψ.toFun (e y) = d y := by
    rw [hΨF]; change d (e.symm (e y)) = d y
    rw [e.left_inv (mem_chart_source _ y)]
  let Φy := recenter Φ (d y) hy.2
  let Θ := subConst (LocalHolomorphicEquivAt.comp Ψ Φy hΨy) (Φ.toFun (d y))
  refine ⟨Θ, fun z hz => (hΨN hz.1).1, ?_, ?_⟩
  · change Φ.toFun (Ψ.toFun (e y)) - Φ.toFun (d y) = 0
    rw [hΨy, sub_self]
  · intro z hz
    have hzO := (hΨN hz.2.1).2
    change e.symm (e z) ∈ O at hzO
    rw [e.left_inv hz.1] at hzO
    refine ⟨hzO, ?_⟩
    change Φ.toFun (Ψ.toFun (e z)) - Φ.toFun (d y) = Φ.toFun (d z) - Φ.toFun (d y)
    rw [hΨF]
    change Φ.toFun (d (e.symm (e z))) - Φ.toFun (d y) = _
    rw [e.left_inv hz.1]

/-- The exact intrinsic count throughout an actual original chart domain. -/
theorem branchMultiplicity_eq_filter_card {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) {x : M}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (S : Finset (Fin n))
    (hΦH : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0)
    {y : M} (hy : y ∈ flatDomain Φ) :
    branchMultiplicity hH y = (S.filter fun i => flatCoord Φ i y = 0).card := by
  classical
  have hne : ∀ᶠ z in 𝓝 y, ∀ i ∈ S, flatCoord Φ i y ≠ 0 → flatCoord Φ i z ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ S ∧ flatCoord Φ i y ≠ 0
    · filter_upwards [(holomorphicAt_flatCoord Φ i hy).continuousAt.eventually
        (isOpen_ne.mem_nhds hi.2)] with z hz
      exact fun _ _ => hz
    · exact Eventually.of_forall fun z hiS hiy => False.elim (hi ⟨hiS, hiy⟩)
  have hdom : ∀ᶠ z in 𝓝 y, z ∈ flatDomain Φ := (isOpen_flatDomain Φ).mem_nhds hy
  obtain ⟨O, hOsub, hOo, hyO⟩ := mem_nhds_iff.mp (hdom.and hne)
  obtain ⟨Θ, -, hΘ0, hΘ⟩ := exists_recentred_flattening Φ hy hOo hyO
    (fun z hz => (hOsub hz).1)
  let T := S.filter fun i => flatCoord Φ i y = 0
  apply branchMultiplicity_eq_card hH Θ hΘ0 T
  intro z hz
  obtain ⟨hzO, hcoords⟩ := hΘ z hz
  have hzΦ := (hOsub hzO).1
  rw [hΦH z hzΦ]
  constructor
  · rintro ⟨i, hiS, hiz⟩
    have hiy : flatCoord Φ i y = 0 := by
      by_contra hiy
      exact (hOsub hzO).2 i hiS hiy hiz
    refine ⟨i, Finset.mem_filter.mpr ⟨hiS, hiy⟩, ?_⟩
    have heq := congrArg (fun w : ComplexModel n => w i) hcoords
    change flatCoord Θ i z = flatCoord Φ i z - flatCoord Φ i y at heq
    rw [heq, hiz, hiy, sub_self]
  · rintro ⟨i, hiT, hiz⟩
    obtain ⟨hiS, hiy⟩ := Finset.mem_filter.mp hiT
    refine ⟨i, hiS, ?_⟩
    have heq := congrArg (fun w : ComplexModel n => w i) hcoords
    change flatCoord Θ i z = flatCoord Φ i z - flatCoord Φ i y at heq
    rwa [hiz, hiy, sub_zero, eq_comm] at heq

/-- Intrinsic count superlevels are closed even without compactness. -/
theorem isClosed_branchMultiplicity_superlevel {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) (r : ℕ) :
    IsClosed {y | r ≤ branchMultiplicity hH y} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨Φ, -, hΦ0, S, hΦH⟩ := hH.2 x
  have hcard := branchMultiplicity_eq_card hH Φ hΦ0 S hΦH
  have hlt : S.card < r := by
    change ¬ r ≤ branchMultiplicity hH x at hx
    rw [hcard] at hx
    omega
  apply Filter.mem_of_superset ((isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ))
  intro y hy
  change ¬ r ≤ branchMultiplicity hH y
  rw [branchMultiplicity_eq_filter_card hH Φ S hΦH hy]
  have hle := Finset.card_filter_le S (fun i => flatCoord Φ i y = 0)
  omega

/-- Every positive branch-count superlevel lies in the original carrier. -/
theorem branchMultiplicity_superlevel_subset {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ} (hr : 0 < r) :
    {y | r ≤ branchMultiplicity hH y} ⊆ H := by
  intro y hy
  exact (branchMultiplicity_pos_iff hH y).mp (hr.trans_le hy)

/-- At a point of a globally highest count, the whole intrinsic level is the
intersection of the actual original branches on the entire chart domain. -/
theorem highest_superlevel_flattening {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ y : M, branchMultiplicity hH y ≤ r) {x : M}
    (hx : r ≤ branchMultiplicity hH x)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (S : Finset (Fin n))
    (hΦH : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0) :
    S.card = r ∧ ∀ y ∈ flatDomain Φ,
      (r ≤ branchMultiplicity hH y ↔ ∀ i ∈ S, flatCoord Φ i y = 0) := by
  classical
  have hcard : S.card = r := by
    rw [← branchMultiplicity_eq_card hH Φ hΦ0 S hΦH]
    exact (hbound x).antisymm hx
  refine ⟨hcard, fun y hy => ?_⟩
  rw [branchMultiplicity_eq_filter_card hH Φ S hΦH hy, ← hcard]
  constructor
  · intro hle
    exact Finset.card_filter_eq_iff.mp
      ((Finset.card_filter_le S _).antisymm hle)
  · intro hzero
    rw [Finset.filter_eq_self.mpr hzero]

private theorem linearIndependent_coordinate_rows {ι : Type*} [Fintype ι]
    {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    (σ : ι → Fin n) (hσ : Function.Injective σ) :
    LinearIndependent ℂ (fun i => fderiv ℂ (fun z => Φ.toFun z (σ i)) p) := by
  classical
  have hd := Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have hsurj : Function.Surjective (fderiv ℂ Φ.toFun p) := by
    have h := surjective_fderiv_shifted Φ
    simpa only [fderiv_comp_add_right, zero_add] using h
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  obtain ⟨v, hv⟩ := hsurj (AnalyticJacobianSingularCore.coordinateDirection (σ i))
  have hrow : ∀ j, fderiv ℂ (fun z => Φ.toFun z (σ j)) p v = if j = i then 1 else 0 := by
    intro j
    have hc := fderiv_comp (𝕜 := ℂ) (g := (EuclideanSpace.proj (σ j) : ComplexModel n →L[ℂ] ℂ))
      p (EuclideanSpace.proj (σ j) : ComplexModel n →L[ℂ] ℂ).differentiableAt hd
    rw [ContinuousLinearMap.fderiv] at hc
    have hc' := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v) hc
    change fderiv ℂ (fun z => Φ.toFun z (σ j)) p v = _ at hc'
    simpa [ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj, hv,
      AnalyticJacobianSingularCore.coordinateDirection, hσ.eq_iff] using hc'
  have heq := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v) ha
  simpa [sum_apply, smul_apply, hrow] using heq

/-- The actual original coordinate intersections internally produce regularity
of the entire highest-count locus at every one of its points. -/
theorem regularAtDim_highest_superlevel {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ y : M, branchMultiplicity hH y ≤ r) {x : M}
    (hx : r ≤ branchMultiplicity hH x) :
    RegularAtDim (n := n) {y | r ≤ branchMultiplicity hH y} x (n - r) := by
  classical
  obtain ⟨Φ, hsrc, hΦ0, S, hΦH⟩ := hH.2 x
  obtain ⟨hcard, hflat⟩ := highest_superlevel_flattening hH hbound hx Φ hΦ0 S hΦH
  let σ : Fin (Fintype.card S) → Fin n := fun a => ((Fintype.equivFin S).symm a).1
  have hσ : Function.Injective σ := fun a b hab =>
    (Fintype.equivFin S).symm.injective (Subtype.ext hab)
  let P : ComplexAnalyticPresentationAt (n := n) {y | r ≤ branchMultiplicity hH y} x :=
    { generatorCount := Fintype.card S
      generator := fun a z => Φ.toFun z (σ a)
      coordinateNeighborhood := Φ.source
      isOpen_coordinateNeighborhood := Φ.isOpen_source
      center_mem_coordinateNeighborhood := Φ.center_mem_source
      coordinateNeighborhood_subset_target := hsrc
      generator_holomorphic := fun a =>
        (EuclideanSpace.proj (σ a) : ComplexModel n →L[ℂ] ℂ).differentiableOn.comp
          Φ.toFun_holomorphic (fun _ _ => mem_univ _)
      zeroLocus := by
        intro y hye hyΦ
        change r ≤ branchMultiplicity hH y ↔ ∀ a, flatCoord Φ (σ a) y = 0
        rw [hflat y ⟨hye, hyΦ⟩]
        constructor
        · intro hy a
          exact hy (σ a) ((Fintype.equivFin S).symm a).2
        · intro hy i hi
          have h := hy ((Fintype.equivFin S) ⟨i, hi⟩)
          simpa [σ, flatCoord] using h }
  have hreg := AnalyticJacobianCriterion.regularAtDim_of_presentation_fullRank P hx
    (linearIndependent_coordinate_rows Φ σ hσ)
  have hR : P.generatorCount = r := by
    change Fintype.card S = r
    simpa using hcard
  rwa [hR] at hreg

/-- The globally highest intrinsic count produces a genuine closed smooth centre. -/
theorem isClosedSubmanifold_highest_superlevel {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) {r : ℕ}
    (hbound : ∀ y : M, branchMultiplicity hH y ≤ r) :
    IsClosedSubmanifold n {y | r ≤ branchMultiplicity hH y} :=
  ⟨isClosed_branchMultiplicity_superlevel hH r,
    fun _ hx => ⟨n - r, regularAtDim_highest_superlevel hH hbound hx⟩⟩

/-- Finite actual branch values internally produce an attained positive global
maximum and its whole nonempty closed smooth locus, without compactness. -/
theorem exists_highest_multiplicity_stratum {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) (hne : H.Nonempty) :
    ∃ r : ℕ, 0 < r ∧ r ≤ n ∧
      (∀ y : M, branchMultiplicity hH y ≤ r) ∧
      {y | branchMultiplicity hH y = r}.Nonempty ∧
      IsClosedSubmanifold n {y | branchMultiplicity hH y = r} ∧
      (∀ y, branchMultiplicity hH y = r →
        RegularAtDim (n := n) {z | branchMultiplicity hH z = r} y (n - r)) ∧
      {y | branchMultiplicity hH y = r} ⊆ H := by
  classical
  obtain ⟨c, hc⟩ := hne
  let V := range (branchMultiplicity hH)
  have hVfin : V.Finite := (finite_Iic n).subset fun v ⟨x, hv⟩ => hv ▸ branchMultiplicity_le hH x
  obtain ⟨r, ⟨x, hx⟩, hrmax⟩ := Set.exists_max_image V id hVfin ⟨branchMultiplicity hH c, mem_range_self _⟩
  have hbound : ∀ y : M, branchMultiplicity hH y ≤ r := fun y => hrmax _ (mem_range_self _)
  have hr : 0 < r := ((branchMultiplicity_pos_iff hH c).mpr hc).trans_le (hbound c)
  have heq : {y | branchMultiplicity hH y = r} = {y | r ≤ branchMultiplicity hH y} := by
    ext y
    exact ⟨fun hy => hy.ge, fun hy => (hbound y).antisymm hy⟩
  refine ⟨r, hr, hx ▸ branchMultiplicity_le hH x, hbound, ⟨x, hx⟩, ?_, ?_, ?_⟩
  · rw [heq]
    exact isClosedSubmanifold_highest_superlevel hH hbound
  · intro y hy
    rw [heq]
    exact regularAtDim_highest_superlevel hH hbound hy.ge
  · rw [heq]
    exact branchMultiplicity_superlevel_subset hH hr

end
end Hironaka.HironakaNormalCrossingsMultiplicityStrata
