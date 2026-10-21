import TranscendentalNakamaye.Pending.StepOneBridge
import TranscendentalNakamaye.Pending.ResolutionInvariantDriver

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The maximum value drops along canonical segments; well-founded values resolve

Blueprint `hir:step-one-well-founded` (`blueprint/src/hironaka.tex`, Hironaka phase H4, a piece of
`hir:maximal-order-step`).  Sources: Włodarczyk 2005 (arXiv `hiron.tex`), end of the proof of the resolution theorem (the
centres are the maximum loci of the invariant, and blowing up the maximum locus lowers the maximum); Bierstone--Milman 2008
§7; Kollár 2007 §3.4.

Let `inv` be a value function along the towers over `X` and `𝔪` a marked ideal.  If, after a step of a canonical segment
(the centre empty or the maximum locus), every point of the cosupport lies over the cosupport, its value drops over the
centre and is unchanged off it (`StepDrop`, the properties (3) and (4) of `hir:centre-function` together), then after a
nonempty centre `C` (the maximum locus, with value `λ`) **every value of every canonical extension is `< λ`**
(`lt_of_isCanonical_append`), by induction along the extension.  The one-step case is the hypothesis `hdec` of the driver
`ResolutionDriver.exists_isGeoResolution_of_wellFounded_invariant`.

Consequences:
* a resolution invariant (`ResolutionInvariantExt.ResolutionInvariant`) has `StepDrop` along its canonical segments, and,
  **if its values are well-founded, it resolves every marked ideal of its domain over a compact base without property
  (8)** (`exists_isGeoResolution_of_wellFoundedLT`);
* the masked Step 1 value `stepOneInvM R 𝔍` has `StepDrop` for the marked ideals of the domain of maximal order
  (`stepDrop_stepOneInvM`, from `StepOneBridge`), and, **if the values `Λ` of the lower invariant `R` are well-founded, it
  resolves every such marked ideal over a compact base, by a canonical segment** (`exists_isGeoResolution_stepOneInvM`;
  `ℕ ×ₗ WithTop Λ` is then well-founded).  Nothing of property (8), of `R` or of the Step 1 value, is used.

This is independent of the decision on property (8) (inbox I-1139): the drop is needed under each of its options.

## Main results

* `StepDrop`, `lt_of_mem_maxLocus`, `lt_of_isCanonical_append`, `lt_of_isCanonical_step`: the drop of the maximum;
* `proj_mem_cosupp_step`: along a multiple test blow-up the points of the cosupport lie over the cosupport;
* `stepDrop_of_resolutionInvariant`, `exists_isGeoResolution_of_wellFoundedLT`: for resolution invariants;
* `stepDrop_stepOneInvM`, `stepOneInvM_lt_of_isCanonical_append`, `isAdmissibleCentre_maxLocus_stepOneInvM`,
  `exists_isGeoResolution_stepOneInvM`: for the masked Step 1 value.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace TranscendentalNakamaye.Pending.StepOneWellFounded

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
open TranscendentalNakamaye.Pending.BlowupTowers TranscendentalNakamaye.Pending.BlowupTowerTransforms
  TranscendentalNakamaye.Pending.MarkedIdeals TranscendentalNakamaye.Pending.MarkedIdeals.MarkedIdeal
  TranscendentalNakamaye.Pending.StepOneValueMasked TranscendentalNakamaye.Pending.MarkedIdealRestrictOpen
  TranscendentalNakamaye.Pending.ResolutionInvariantOrder TranscendentalNakamaye.Pending.HomogenizedIdealAlong
open TranscendentalNakamaye.Pending.ResolutionDriver (maxLocus IsCanonicalSegment isCanonicalSegment_step_iff
  exists_isGeoResolution_of_wellFounded_invariant)
open TranscendentalNakamaye.Pending.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open TranscendentalNakamaye.Pending.ResolutionInvariantExt (ResolutionInvariant)
open TranscendentalNakamaye.Pending.ResolutionInvariantDriver (isAdmissibleCentre_of_pullback_val_top maxLocus_eq_level
  interior_maxLocus_eq_empty isCanonical_of_isCanonicalSegment)

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

/-! ### Resolution invariants -/

section Invariant

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **A resolution invariant has the drop property** along its canonical segments (fields (3) and (4)). -/
theorem stepDrop_of_resolutionInvariant (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) : StepDrop 𝔪 (R.inv 𝔪) := by
  intro Y Z T C π hπ hcan z hz
  have hTs := ResolutionInvariantExt.isGeoTestTower_of_isCanonical R h _ hcan
  obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (R.inv 𝔪) T ∧
      (C = ∅ ∨ C = maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
  refine ⟨proj_mem_cosupp_step h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T C π hπ hTs hz, ?_⟩
  rcases hC with hC | hC
  · refine ⟨fun hzC => ?_, fun _ => R.emptyStep 𝔪 h T C π hπ hC hT z hz⟩
    rw [hC] at hzC
    exact absurd hzC (notMem_empty _)
  · by_cases hne : C.Nonempty
    · exact R.decrease 𝔪 h T C π hπ hT hne hC z hz
    · have hC0 : C = ∅ := not_nonempty_iff_eq_empty.mp hne
      refine ⟨fun hzC => ?_, fun _ => R.emptyStep 𝔪 h T C π hπ hC0 hT z hz⟩
      rw [hC0] at hzC
      exact absurd hzC (notMem_empty _)

/-- **With well-founded values, a resolution invariant resolves every marked ideal of its domain over a compact base,
by a canonical segment, without property (8)**: `ResolutionDriver.exists_isGeoResolution_of_wellFounded_invariant`, with
(1), (2), the empty interior of the maximum locus and the one-step drop (`lt_of_isCanonical_step`). -/
theorem exists_isGeoResolution_of_wellFoundedLT [CompactSpace X] [WellFoundedLT Λ]
    (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonicalSegment 𝔪 (R.inv 𝔪) T ∧ IsGeoResolution 𝔪 T := by
  refine exists_isGeoResolution_of_wellFounded_invariant 𝔪 (R.inv 𝔪) ?_ ?_ ?_ ?_
  · intro Y T _ hT
    have hwf := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT).isWellFormed
    exact GiraudAlong.isClosed_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N _
  · intro Y T hcan _
    exact R.usc 𝔪 h T (isCanonical_of_isCanonicalSegment _ T hcan)
  · intro Y T hcan hT _
    exact ⟨ResolutionInvariantExt.isAdmissibleCentre_maxLocus R h T (isCanonical_of_isCanonicalSegment _ T hcan) hT,
      interior_maxLocus_eq_empty h T hT _⟩
  · intro Y T hcan _ x₀ hx₀ Z π hπ
    exact lt_of_isCanonical_step (stepDrop_of_resolutionInvariant R h) T
      (isCanonical_of_isCanonicalSegment _ T hcan) hx₀ π hπ

end Invariant

/-! ### The masked Step 1 value -/

section StepOne

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}
variable (R : ResolutionInvariant.{u, v} n (k - 1) Λ) (𝔍 : MarkedIdeal n X)

/-- **The masked Step 1 value has the drop property** along its canonical segments, for the marked ideals of the domain of
maximal order (`StepOneBridge.decrease_field`, `StepOneBridge.emptyStep_field`). -/
theorem stepDrop_stepOneInvM (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) :
    StepDrop 𝔍 (stepOneInvM R 𝔍) := by
  intro Y Z T C π hπ hcan z hz
  have hTs := (StepOneBridge.isGeoTestTower_of_isCanonical R 𝔍 h hmax hn _ hcan).2.1
  obtain ⟨hT, hC⟩ : IsCanonical 𝔍 (stepOneInvM R 𝔍) T ∧
      (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := hcan
  refine ⟨proj_mem_cosupp_step h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T C π hπ hTs hz, ?_⟩
  rcases hC with hC | hC
  · refine ⟨fun hzC => ?_, fun _ => StepOneBridge.emptyStep_field R 𝔍 h hmax hn T C π hπ hC hT z hz⟩
    rw [hC] at hzC
    exact absurd hzC (notMem_empty _)
  · exact StepOneBridge.decrease_field R 𝔍 h hmax hn T C π hπ hT hC z hz

/-- **The maximum of the masked Step 1 value drops along canonical segments**: after a step along the maximum locus `C`
of a canonical segment `T`, every value on the cosupport of every canonical extension is smaller than the maximum at
`T` (the value at any `x₀ ∈ C`). -/
theorem stepOneInvM_lt_of_isCanonical_append (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hn : 0 < n) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hC : C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) {x₀ : Y} (hx₀ : x₀ ∈ C)
    {W : CMfd.{u} n} (S : BlowupTower Z W)
    (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) ((BlowupTower.step T C π hπ).append S)) :
    ∀ z ∈ (geoTransformAlong 𝔍 ((BlowupTower.step T C π hπ).append S)).cosupp,
      stepOneInvM R 𝔍 ((BlowupTower.step T C π hπ).append S) z < stepOneInvM R 𝔍 T x₀ :=
  lt_of_isCanonical_append (stepDrop_stepOneInvM R 𝔍 h hmax hn) T C π hπ hC hx₀ S hcan

/-- **The maximum locus of the masked Step 1 value is an admissible centre of `𝔍_T`** along its canonical segments
(`StepOneBridge.admissible_field` on the whole last stage, with the maximum as the level). -/
theorem isAdmissibleCentre_maxLocus_stepOneInvM (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hn : 0 < n) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T) :
    (geoTransformAlong 𝔍 T).IsAdmissibleCentre (maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := by
  by_cases hne : (maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hadm := StepOneBridge.admissible_field R 𝔍 h hmax hn T hcan ⊤ (stepOneInvM R 𝔍 T y₀)
      (fun y hy _ => hy₀.2 y hy)
    rw [← maxLocus_eq_level hy₀] at hadm
    have hT := (StepOneBridge.isGeoTestTower_of_isCanonical R 𝔍 h hmax hn T hcan).2.1
    have hcoh := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT).isCoherent
    exact isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg) hadm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **With well-founded lower values, the masked Step 1 value resolves every marked ideal of the domain of maximal order
over a compact base, by a canonical segment** (`ResolutionDriver.exists_isGeoResolution_of_wellFounded_invariant` with
values in `ℕ ×ₗ WithTop Λ`, well-founded with `Λ`; properties (1), (2), (3), (4) of the Step 1 value; nothing of (8)). -/
theorem exists_isGeoResolution_stepOneInvM [CompactSpace X] [WellFoundedLT Λ] (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonicalSegment 𝔍 (stepOneInvM R 𝔍) T ∧ IsGeoResolution 𝔍 T := by
  refine exists_isGeoResolution_of_wellFounded_invariant 𝔍 (stepOneInvM R 𝔍) ?_ ?_ ?_ ?_
  · intro Y T _ hT
    have hwf := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT).isWellFormed
    exact GiraudAlong.isClosed_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N _
  · intro Y T hcan _
    exact StepOneBridge.usc_field R 𝔍 h hmax hn T (isCanonical_of_isCanonicalSegment _ T hcan)
  · intro Y T hcan hT _
    exact ⟨isAdmissibleCentre_maxLocus_stepOneInvM R 𝔍 h hmax hn T (isCanonical_of_isCanonicalSegment _ T hcan),
      interior_maxLocus_eq_empty h T hT _⟩
  · intro Y T hcan _ x₀ hx₀ Z π hπ
    exact lt_of_isCanonical_step (stepDrop_stepOneInvM R 𝔍 h hmax hn) T
      (isCanonical_of_isCanonicalSegment _ T hcan) hx₀ π hπ

end StepOne

end

end TranscendentalNakamaye.Pending.StepOneWellFounded
