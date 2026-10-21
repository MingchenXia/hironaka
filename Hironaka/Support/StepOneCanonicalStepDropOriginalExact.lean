/- Complete original prerequisites; statements and mathematical proofs unchanged. -/
import Hironaka.Invariant.StepOneWellFounded

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneWellFounded

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValueMasked Hironaka.MarkedIdealRestrictOpen
  Hironaka.ResolutionInvariantOrder Hironaka.HomogenizedIdealAlong
open Hironaka.ResolutionDriver (maxLocus IsCanonicalSegment isCanonicalSegment_step_iff)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
open Hironaka.ResolutionInvariantDriver (isAdmissibleCentre_of_pullback_val_top maxLocus_eq_level
  interior_maxLocus_eq_empty isCanonical_of_isCanonicalSegment)

noncomputable section

variable {n : ℕ}

/-! ### The drop of the maximum along canonical segments -/

section Drop

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- **The maximum drops along canonical segments**: let the step along `C` follow a canonical segment `T`, `C` the maximum
locus of `inv T` on the cosupport, and `x₀ ∈ C`.  Along every canonical segment extending this step, every value on the
cosupport is smaller than the value of `x₀`, the maximum at `T`. -/
theorem lt_of_isCanonical_append {𝔪 : MarkedIdeal n X} {inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}
    (hdrop : StepDrop 𝔪 inv) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hC : C = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) {x₀ : Y} (hx₀ : x₀ ∈ C) :
    ∀ {W : CMfd.{u} n} (S : BlowupTower Z W), IsCanonical 𝔪 inv ((BlowupTower.step T C π hπ).append S) →
      ∀ z ∈ (geoTransformAlong 𝔪 ((BlowupTower.step T C π hπ).append S)).cosupp,
        inv ((BlowupTower.step T C π hπ).append S) z < inv T x₀
  | _, .refl, hcan, z, hz => by
      obtain ⟨hpz, h1, h2⟩ := hdrop T C π hπ hcan z hz
      subst hC
      exact lt_of_mem_maxLocus hx₀ hpz ⟨h1, h2⟩
  | _, .step S C' π' hπ', hcan, z, hz => by
      obtain ⟨hpz, h1, h2⟩ := hdrop _ C' π' hπ' hcan z hz
      have ih := lt_of_isCanonical_append hdrop T C π hπ hC hx₀ S hcan.1 (π' z) hpz
      by_cases hz' : π' z ∈ C'
      · exact (h1 hz').trans ih
      · exact (h2 hz').trans_lt ih

/-- **The one-step drop** (the hypothesis `hdec` of `ResolutionDriver.exists_isGeoResolution_of_wellFounded_invariant`):
blowing up the maximum locus after a canonical segment, every value on the new cosupport is smaller than the maximum. -/
theorem lt_of_isCanonical_step {𝔪 : MarkedIdeal n X} {inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}
    (hdrop : StepDrop 𝔪 inv) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsCanonical 𝔪 inv T)
    {x₀ : Y} (hx₀ : x₀ ∈ maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) (π : Z → Y)
    (hπ : IsBlowupAlong n (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π) :
    ∀ z ∈ (geoTransformAlong 𝔪 (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ)).cosupp,
      inv (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ) z < inv T x₀ :=
  lt_of_isCanonical_append hdrop T _ π hπ rfl hx₀ BlowupTower.refl
    (⟨hT, Or.inr rfl⟩ : IsCanonical 𝔪 inv T ∧ (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp = ∅ ∨
      maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp))
end Drop
end
end Hironaka.StepOneWellFounded
