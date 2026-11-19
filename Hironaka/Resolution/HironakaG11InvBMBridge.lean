import Hironaka.Resolution.HironakaG11InvBMAdmissible
import Hironaka.Invariant.StepOneWellFounded

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's Step 1 value: properties (1)--(4) for the marked ideal itself, and resolution (plan module 8, part 3)

Blueprint: `hironaka-g11-inv-bm-max-order.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §1 module 8.
Sources: Bierstone--Milman 2008, §5 Step I (the marked ideal of maximal order is resolved by the canonical centres of its
lower-dimensional problem and of its special loci) and §7; the skeleton is W's `StepOneBridge` and `StepOneWellFounded`.

The properties of `stepOneInvBM R 𝔍` were proved along the canonical segments of `J̄ = 𝓒_N(𝓗_N(𝔍))`
(`HironakaG11InvBMUSC`, `HironakaG11InvBMAdmissible`).  For `𝔍` in the domain, `J̄` and `𝔍` are equivalent
(`StepOneBridge.barMarked_wEquiv`), so the two notions of canonical segment agree and properties (1)--(4) hold in the shape of
the fields of `MaxOrderValue.IsMaxOrderValue` (`admissible_field`, `usc_field`, `decrease_field`, `emptyStep_field`).  With
the drop property this gives, for well-founded lower values, **a resolution of every marked ideal of the domain of maximal
order over a compact base by a canonical segment of Bierstone--Milman's Step 1 value** (`exists_isGeoResolution_stepOneInvBM`).
Everything is under the anchor change `AnchorChangeBM 𝔍 R` (plan module 6), an explicit hypothesis.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMBridge

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValue Hironaka.StepOneLowerDomain
  Hironaka.HomogenizedIdealAlong Hironaka.MarkedIdealBiholomorphism
  Hironaka.MarkedIdealRestrictOpen Hironaka.ResolutionInvariantOrder
  Hironaka.HironakaG11InvBMMask Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG11InvBMCanonicalTail Hironaka.HironakaG11InvBMAdmissible
  Hironaka.StepOneWellFounded
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv E_geoTransformAlong_eq)
open Hironaka.ResolutionDriver (maxLocus IsCanonicalSegment
  exists_isGeoResolution_of_wellFounded_invariant)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
open Hironaka.ResolutionInvariantDriver (isAdmissibleCentre_of_pullback_val_top maxLocus_eq_level
  interior_maxLocus_eq_empty isCanonical_of_isCanonicalSegment)

noncomputable section

variable {n : ℕ}

section Bridge

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n (k - 1) Λ)
  (𝔍 : MarkedIdeal n X)

/-- **The canonical segments of `stepOneInvBM R 𝔍` for `𝔍` and for `J̄` agree** (`𝔍` in the domain, of maximal order, given the
anchor change). -/
theorem isCanonical_iff (hAC : AnchorChangeBM 𝔍 R) (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hn : 0 < n) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsCanonical 𝔍 (stepOneInvBM R 𝔍) T ↔ IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
      have ih := isCanonical_iff hAC h hmax hn T
      have hW := StepOneBridge.barMarked_wEquiv 𝔍 h
      have hcos : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T →
          (geoTransformAlong (barMarked 𝔍) T).cosupp = (geoTransformAlong 𝔍 T).cosupp := fun hc =>
        (hW.2 T).2 (isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h.isWellFormed h.one_le_d hn hmax h.dimLE T hc)
      show (IsCanonical 𝔍 (stepOneInvBM R 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp)) ↔
        (IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp))
      constructor
      · rintro ⟨hc, hC⟩
        have hc' := ih.mp hc
        exact ⟨hc', by rw [hcos hc']; exact hC⟩
      · rintro ⟨hc', hC⟩
        exact ⟨ih.mpr hc', by rw [← hcos hc']; exact hC⟩

/-- Canonical segments of `stepOneInvBM R 𝔍` for `𝔍` are multiple test blow-ups of `J̄` and of `𝔍`, and along them the
cosupports of `J̄_T` and `𝔍_T` agree. -/
theorem isGeoTestTower_of_isCanonical (hAC : AnchorChangeBM 𝔍 R) (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T) :
    IsGeoTestTower (barMarked 𝔍) T ∧ IsGeoTestTower 𝔍 T ∧
      (geoTransformAlong (barMarked 𝔍) T).cosupp = (geoTransformAlong 𝔍 T).cosupp := by
  have hW := StepOneBridge.barMarked_wEquiv 𝔍 h
  have hJ := isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h.isWellFormed h.one_le_d hn hmax h.dimLE T
    ((isCanonical_iff R 𝔍 hAC h hmax hn T).mp hcan)
  exact ⟨hJ, (hW.2 T).1.mp hJ, (hW.2 T).2 hJ⟩

/-- **Property (1), the field `admissible`** (given the anchor change). -/
theorem admissible_field (hAC : AnchorChangeBM 𝔍 R) (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T) (W : Opens Y) (l : ℕ ×ₗ WithTop Λ)
    (hle : ∀ y ∈ (geoTransformAlong 𝔍 T).cosupp, y ∈ W → stepOneInvBM R 𝔍 T y ≤ l) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong 𝔍 T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔍 T).cosupp ∧ stepOneInvBM R 𝔍 T y = l}) := by
  have hcanJ := (isCanonical_iff R 𝔍 hAC h hmax hn T).mp hcan
  obtain ⟨hJT, hT, hcos⟩ := isGeoTestTower_of_isCanonical R 𝔍 hAC h hmax hn T hcan
  rw [← hcos] at hle ⊢
  have hadm := stepOneInvBM_admissible 𝔍 R hAC h.isWellFormed h.one_le_d hn hmax h.dimLE T hJT hcanJ W l hle
  have hJ := isWellFormed_barMarked 𝔍 h.isWellFormed
  obtain ⟨-, hcJ⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hJT
  obtain ⟨-, hc𝔍⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong h.isWellFormed.isClosedSubmanifold_N
    h.isWellFormed.isCoherent T hT
  exact (StepOneBridge.isAdmissibleCentre_pullback_val_iff_of_eq hcJ hc𝔍
    (E_geoTransformAlong_eq (StepOneBridge.barMarked_wEquiv 𝔍 h).1 T) hcos W _).mp hadm

/-- **Property (2), the field `usc`** (given the anchor change). -/
theorem usc_field (hAC : AnchorChangeBM 𝔍 R) (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hn : 0 < n) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T) :
    IsInvUSCOn (stepOneInvBM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp := by
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 hAC h hmax hn T hcan).2.2]
  exact stepOneInvBM_usc_of_isCanonical 𝔍 R hAC h.isWellFormed h.one_le_d hn hmax h.dimLE T
    ((isCanonical_iff R 𝔍 hAC h hmax hn T).mp hcan)

/-- **Property (3), the field `decrease`** (given the anchor change; `C ≠ ∅` not needed). -/
theorem decrease_field (hAC : AnchorChangeBM 𝔍 R) (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hn : 0 < n) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T)
    (hC : C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) :
    ∀ z ∈ (geoTransformAlong 𝔍 (.step T C π hπ)).cosupp,
      (π z ∈ C → stepOneInvBM R 𝔍 (.step T C π hπ) z < stepOneInvBM R 𝔍 T (π z)) ∧
      (π z ∉ C → stepOneInvBM R 𝔍 (.step T C π hπ) z = stepOneInvBM R 𝔍 T (π z)) := by
  have hcanS : IsCanonical 𝔍 (stepOneInvBM R 𝔍) (.step T C π hπ) :=
    (⟨hcan, Or.inr hC⟩ : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T ∧
      (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp))
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 hAC h hmax hn _ hcanS).2.2]
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 hAC h hmax hn T hcan).2.2] at hC
  exact stepOneInvBM_decrease_of_isCanonical 𝔍 R hAC h.isWellFormed h.one_le_d hn hmax h.dimLE T C π hπ
    ((isCanonical_iff R 𝔍 hAC h hmax hn T).mp hcan) hC

/-- **Property (4), the field `emptyStep`** (given the anchor change). -/
theorem emptyStep_field (hAC : AnchorChangeBM 𝔍 R) (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (hn : 0 < n) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hC : C = ∅) (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T) :
    ∀ z ∈ (geoTransformAlong 𝔍 (.step T C π hπ)).cosupp,
      stepOneInvBM R 𝔍 (.step T C π hπ) z = stepOneInvBM R 𝔍 T (π z) := by
  have hcanS : IsCanonical 𝔍 (stepOneInvBM R 𝔍) (.step T C π hπ) :=
    (⟨hcan, Or.inl hC⟩ : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T ∧
      (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp))
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 hAC h hmax hn _ hcanS).2.2]
  exact stepOneInvBM_emptyStep_of_isCanonical 𝔍 R hAC h.isWellFormed h.one_le_d hn hmax h.dimLE T C π hπ hC
    ((isCanonical_iff R 𝔍 hAC h hmax hn T).mp hcan)

end Bridge

/-! ### The drop of the maximum and resolution -/

section Resolution

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}
variable (R : ResolutionInvariant.{u, v} n (k - 1) Λ) (𝔍 : MarkedIdeal n X)

/-- **Bierstone--Milman's Step 1 value has the drop property** along its canonical segments, for the marked ideals of the
domain of maximal order (given the anchor change). -/
theorem stepDrop_stepOneInvBM (hAC : AnchorChangeBM 𝔍 R) (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) : StepDrop 𝔍 (stepOneInvBM R 𝔍) := by
  intro Y Z T C π hπ hcan z hz
  have hTs := (isGeoTestTower_of_isCanonical R 𝔍 hAC h hmax hn _ hcan).2.1
  obtain ⟨hT, hC⟩ : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T ∧
      (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := hcan
  refine ⟨proj_mem_cosupp_step h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T C π hπ hTs hz, ?_⟩
  rcases hC with hC | hC
  · refine ⟨fun hzC => ?_, fun _ => emptyStep_field R 𝔍 hAC h hmax hn T C π hπ hC hT z hz⟩
    rw [hC] at hzC
    exact absurd hzC (notMem_empty _)
  · exact decrease_field R 𝔍 hAC h hmax hn T C π hπ hT hC z hz

/-- **The maximum of Bierstone--Milman's Step 1 value drops along canonical segments** (given the anchor change). -/
theorem stepOneInvBM_lt_of_isCanonical_append (hAC : AnchorChangeBM 𝔍 R) (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) (hC : C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp)
    {x₀ : Y} (hx₀ : x₀ ∈ C) {W : CMfd.{u} n} (S : BlowupTower Z W)
    (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) ((BlowupTower.step T C π hπ).append S)) :
    ∀ z ∈ (geoTransformAlong 𝔍 ((BlowupTower.step T C π hπ).append S)).cosupp,
      stepOneInvBM R 𝔍 ((BlowupTower.step T C π hπ).append S) z < stepOneInvBM R 𝔍 T x₀ :=
  lt_of_isCanonical_append (stepDrop_stepOneInvBM R 𝔍 hAC h hmax hn) T C π hπ hC hx₀ S hcan

/-- **The maximum locus of Bierstone--Milman's Step 1 value is an admissible centre of `𝔍_T`** along its canonical segments
(given the anchor change). -/
theorem isAdmissibleCentre_maxLocus (hAC : AnchorChangeBM 𝔍 R) (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) T) :
    (geoTransformAlong 𝔍 T).IsAdmissibleCentre (maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := by
  by_cases hne : (maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hadm := admissible_field R 𝔍 hAC h hmax hn T hcan ⊤ (stepOneInvBM R 𝔍 T y₀) (fun y hy _ => hy₀.2 y hy)
    rw [← maxLocus_eq_level hy₀] at hadm
    have hT := (isGeoTestTower_of_isCanonical R 𝔍 hAC h hmax hn T hcan).2.1
    have hcoh := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT).isCoherent
    exact isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg) hadm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Resolution by Bierstone--Milman's Step 1 value** (given the anchor change): with well-founded lower values, every
marked ideal of the domain of maximal order over a compact base is resolved by a canonical segment of `stepOneInvBM R 𝔍`
(properties (1)--(4); nothing of property (8)). -/
theorem exists_isGeoResolution_stepOneInvBM [CompactSpace X] [WellFoundedLT Λ] (hAC : AnchorChangeBM 𝔍 R)
    (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonicalSegment 𝔍 (stepOneInvBM R 𝔍) T ∧ IsGeoResolution 𝔍 T := by
  refine exists_isGeoResolution_of_wellFounded_invariant 𝔍 (stepOneInvBM R 𝔍) ?_ ?_ ?_ ?_
  · intro Y T _ hT
    have hwf := (InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT).isWellFormed
    exact GiraudAlong.isClosed_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N _
  · intro Y T hcan _
    exact usc_field R 𝔍 hAC h hmax hn T (isCanonical_of_isCanonicalSegment _ T hcan)
  · intro Y T hcan hT _
    exact ⟨isAdmissibleCentre_maxLocus R 𝔍 hAC h hmax hn T (isCanonical_of_isCanonicalSegment _ T hcan),
      interior_maxLocus_eq_empty h T hT _⟩
  · intro Y T hcan _ x₀ hx₀ Z π hπ
    exact lt_of_isCanonical_step (stepDrop_stepOneInvBM R 𝔍 hAC h hmax hn) T
      (isCanonical_of_isCanonicalSegment _ T hcan) hx₀ π hπ

end Resolution

end

end Hironaka.HironakaG11InvBMBridge
