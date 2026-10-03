/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneBridge
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.MarkedIdeal.TransformOffCentre
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The maximum value drops along canonical segments; well-founded values resolve

Sources: Włodarczyk 2005 (arXiv `hiron.tex`), end of the proof of the resolution theorem (the centres are the
maximum loci of the invariant, and blowing up the maximum locus lowers the maximum); Bierstone--Milman 2008 §7;
Kollár 2007 §3.4.

Let `inv` be a value function along the towers over `X` and `𝔪` a marked ideal. If, after a step of a canonical
segment (the centre empty or the maximum locus), every point of the cosupport lies over the cosupport, its value
drops over the centre and is unchanged off it (`StepDrop`, the properties (3) and (4) of `hir:centre-function`
together), then after a nonempty centre `C` (the maximum locus, with value `λ`) **every value of every canonical
extension is `< λ`**, by induction along the extension.

Consequences:
* a resolution invariant (`ResolutionInvariantExt.ResolutionInvariant`) has `StepDrop` along its canonical segments,
  and, **if its values are well-founded, it resolves every marked ideal of its domain over a compact base without
  property (8)**;
* the masked Step 1 value `stepOneInvM R 𝔍` has `StepDrop` for the marked ideals of the domain of maximal order
  (from `StepOneBridge`), and, **if the values `Λ` of the lower invariant `R` are well-founded, it resolves every
  such marked ideal over a compact base, by a canonical segment** (`ℕ ×ₗ WithTop Λ` is then well-founded). Nothing
  of property (8), of `R` or of the Step 1 value, is used.

This is independent of the decision on property (8): the drop is needed under each of its options.

## Main results

* `StepDrop`, `lt_of_mem_maxLocus`: the drop of the maximum;
* `proj_mem_cosupp_step`: along a multiple test blow-up the points of the cosupport lie over the cosupport;
* `isAdmissibleCentre_maxLocus_stepOneInvM`: for the masked Step 1 value.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneWellFounded

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneValueMasked Hironaka.MarkedIdealRestrictOpen Hironaka.ResolutionInvariantOrder Hironaka.HomogenizedIdealAlong
open Hironaka.ResolutionDriver (maxLocus IsCanonicalSegment isCanonicalSegment_step_iff)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
open Hironaka.ResolutionInvariantDriver (isAdmissibleCentre_of_pullback_val_top maxLocus_eq_level interior_maxLocus_eq_empty isCanonical_of_isCanonicalSegment)

noncomputable section

variable {n : ℕ}

/-! ### The drop of the maximum along canonical segments -/

section Drop

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

variable (𝔪 : MarkedIdeal n X) (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) in
/-- **The drop property of one step of a canonical segment**: if the step along `C` extends a canonical segment (`C` empty
or the maximum locus), every point `z` of the cosupport after the step lies over the cosupport, its value is smaller than
that of `π z` if `π z ∈ C` and equal to it otherwise (properties (3) and (4) of `hir:centre-function` together). -/
def StepDrop : Prop :=
  ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
    IsCanonical 𝔪 inv (.step T C π hπ) → ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
      π z ∈ (geoTransformAlong 𝔪 T).cosupp ∧
        (π z ∈ C → inv (.step T C π hπ) z < inv T (π z)) ∧ (π z ∉ C → inv (.step T C π hπ) z = inv T (π z))

/-- **Order lemma**: a value which is smaller than that of a point of the maximum locus, or equal to that of a point of
`s` off the maximum locus, is smaller than the maximum. -/
theorem lt_of_mem_maxLocus {Y Z : Type*} {f : Y → Λ} {s : Set Y} {g : Z → Λ} {π : Z → Y} {x₀ : Y}
    (hx₀ : x₀ ∈ maxLocus f s) {z : Z} (hz : π z ∈ s)
    (hdec : (π z ∈ maxLocus f s → g z < f (π z)) ∧ (π z ∉ maxLocus f s → g z = f (π z))) : g z < f x₀ := by
  by_cases hzC : π z ∈ maxLocus f s
  · exact (hdec.1 hzC).trans_le (hx₀.2 _ hzC.1)
  · rw [hdec.2 hzC]
    have hnot : ¬ ∀ y' ∈ s, f y' ≤ f (π z) := fun h => hzC ⟨hz, h⟩
    push Not at hnot
    obtain ⟨y', hy', hlt⟩ := hnot
    exact hlt.trans_le (hx₀.2 y' hy')

/-- **Along a multiple test blow-up the points of the cosupport lie over the cosupport**, one step at a time (over the
centre, the centre lies in the cosupport; off it, `TransformOffCentre.mem_cosupp_geoTransform_iff`). -/
theorem proj_mem_cosupp_step {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower 𝔪 (.step T C π hπ)) {z : Z} (hz : z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp) :
    π z ∈ (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hTT
  by_cases hzC : π z ∈ C
  · exact hC.2.1 hzC
  · exact (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong 𝔪 T) hNT.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) hπ hzC).mp hz

end Drop

end

end Hironaka.StepOneWellFounded
