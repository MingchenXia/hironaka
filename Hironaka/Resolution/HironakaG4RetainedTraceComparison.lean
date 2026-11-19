import Hironaka.Resolution.HironakaG4RetainedTraceHead
import Hironaka.Resolution.HironakaG4RetainedCrestPhaseFilterEmptyOld
import Hironaka.Resolution.HironakaG4RetainedDefectFilterEmptyOld
import Hironaka.Resolution.HironakaG4RetainedCrestPhysicalComparison
import Hironaka.Resolution.HironakaG3EmptyAwareFilteredBoundary
import Hironaka.Resolution.HironakaG3AppendEmptyTailComparison
import Hironaka.Resolution.HironakaG8DisjointPhaseMerge

/-! Physical comparison of finite ordered retained traces. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedTraceComparison
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport HomogenizedGlueingTower
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  RestrictEmptyTower G3UniverseEmptyAwareCore HironakaG3EmptyAwareOldSlots
  HironakaG3EmptyAwareBornSlots HironakaG3EmptyAwareFilteredBoundary
  HironakaG3AppendEmptyTailComparison HironakaG8DisjointPhaseMerge
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaG4RetainedDefectRelativeDecrease HironakaG4OrderedRetainedDefectTrace
  HironakaG4RetainedTraceHead HironakaG4OrderedDefectStamp HironakaG4OrderedCrestEmptyBorn
  HironakaG4RetainedCrestPhysicalComparison HironakaG4RetainedCrestPhaseFilterEmptyOld
  HironakaG4RetainedDefectFilterEmptyOld
  HironakaG4PreparedCentreCoordinates HironakaActualRetainedBornResidualHistory
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ}

abbrev liveBorn {A : Type u} (B : List (Set A)) := B.filter fun H => decide H.Nonempty

private def RetainedTraceComparableBelow (hn : 0 < n) (k : ℕ) : Prop :=
  ∀ {X Y₁ Y₂ : CMfd.{u} n} {N : Set X} {old₁ old₂ born₁ born₂ : List (Set X)},
    NativeRetainedGeometry N old₁ born₁ → NativeRetainedGeometry N old₂ born₂ →
    liveBorn old₁ = liveBorn old₂ → liveBorn born₁ = liveBorn born₂ →
    ∀ {μ₁ μ₂ : WithTop RetainedStampRank} {T₁ : BlowupTower X Y₁} {T₂ : BlowupTower X Y₂}
      (R₁ : OrderedRetainedDefectTrace hn N old₁ born₁ μ₁ T₁)
      (R₂ : OrderedRetainedDefectTrace hn N old₂ born₂ μ₂ T₂),
      R₁.phaseCount + R₂.phaseCount < k →
      ∃ ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
        EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ ψ

theorem native_geometry_rebase {X X' : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
    (g : NativeRetainedGeometry N old born)
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    NativeRetainedGeometry (φ ⁻¹' N) (old.map (φ ⁻¹' ·)) (born.map (φ ⁻¹' ·)) := by
  refine ⟨(MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff φ).mpr g.carrier, ?_,
    isTransverse_preimage (pullsBackCoordinates φ) g.born_transverse, ?_⟩
  · simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates φ) φ.continuous g.full
  · intro z hz
    have h := preimage_mono (f := φ) g.dense hz
    change z ∈ φ.toHomeomorph ⁻¹' closure (N \ ⋃ H ∈ old ++ born,H) at h
    rw [φ.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage φ.toHomeomorph.continuous] at h
    change z ∈ closure ((φ : X' → X) ⁻¹' (N \ ⋃ H ∈ old ++ born,H)) at h
    rw [preimage_sdiff,HironakaEmbeddedBoundary.preimage_biUnion_list,List.map_append] at h
    exact h

private theorem retained_carrier_and_born_of_emptyAware
    {X X' A A' : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
    (g : NativeRetainedGeometry N old born)
    {N' : Set X'} {born' : List (Set X')}
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (hN : N' = φ ⁻¹' N)
    (hBorn : liveBorn born' = (liveBorn born).map (φ ⁻¹' ·))
    {P' : BlowupTower X' A'} {P : BlowupTower X A}
    {β : A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    (hP : EmptyAwareTowerIso φ P' P β) :
    let C' := geoTransformAlong (geometricTemplate N' born') P'
    let C := geoTransformAlong (geometricTemplate N born) P
    C'.N = β ⁻¹' C.N ∧
      liveBorn C'.E = (liveBorn C.E).map (β ⁻¹' ·) := by
  intro C' C
  refine ⟨?_, ?_⟩
  · dsimp only [C',C]
    rw [N_geoTransformAlong,N_geoTransformAlong]
    exact hN ▸ emptyAware_strictAlong_eq hP N g.carrier.1
  · dsimp only [C',C]
    apply full_boundary_transport_of_filtered_initial hP
    · rw [filter_map_bijection φ φ.surjective]
      exact hBorn
    · exact fun H hH => g.full.1 H (List.mem_append_right _ hH)

/-- A physical comparison transports the current carrier and every
literal old slot. The chronological born boundary agrees after removing
empty slots. -/
theorem retained_inputs_of_emptyAware
    {X X' A A' : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
    (g : NativeRetainedGeometry N old born)
    {N' : Set X'} {old' born' : List (Set X')}
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (hN : N' = φ ⁻¹' N) (hOld : old' = old.map (φ ⁻¹' ·))
    (hBorn : liveBorn born' = (liveBorn born).map (φ ⁻¹' ·))
    {P' : BlowupTower X' A'} {P : BlowupTower X A}
    {β : A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    (hP : EmptyAwareTowerIso φ P' P β) :
    let C' := geoTransformAlong (geometricTemplate N' born') P'
    let C := geoTransformAlong (geometricTemplate N born) P
    C'.N = β ⁻¹' C.N ∧ old'.map (strictAlong P') = (old.map (strictAlong P)).map (β ⁻¹' ·) ∧
      liveBorn C'.E = (liveBorn C.E).map (β ⁻¹' ·) := by
  intro C' C
  obtain ⟨hc, hb⟩ := retained_carrier_and_born_of_emptyAware g hN hBorn hP
  refine ⟨hc, ?_, hb⟩
  rw [hOld]
  exact emptyAware_old_boundary_eq hP old (fun H hH => g.full.1 H (List.mem_append_left _ hH))

/-- Literal old slots can carry different empty entries on the common base.
A physical comparison still transports all the surviving old slots and all
the surviving chronological born slots, in their respective orders. -/
theorem retained_filtered_inputs_of_emptyAware
    {X X' A A' : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
    (g : NativeRetainedGeometry N old born)
    {N' : Set X'} {old' born' : List (Set X')}
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    (hN : N' = φ ⁻¹' N) (hOld : liveBorn old' = (liveBorn old).map (φ ⁻¹' ·))
    (hBorn : liveBorn born' = (liveBorn born).map (φ ⁻¹' ·))
    {P' : BlowupTower X' A'} {P : BlowupTower X A}
    {β : A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    (hP : EmptyAwareTowerIso φ P' P β) :
    let C' := geoTransformAlong (geometricTemplate N' born') P'
    let C := geoTransformAlong (geometricTemplate N born) P
    C'.N = β ⁻¹' C.N ∧
      liveBorn (old'.map (strictAlong P')) = (liveBorn (old.map (strictAlong P))).map (β ⁻¹' ·) ∧
      liveBorn C'.E = (liveBorn C.E).map (β ⁻¹' ·) := by
  intro C' C
  have hOld' : liveBorn old' = liveBorn (old.map (φ ⁻¹' ·)) := by
    unfold liveBorn at *
    rwa [filter_map_bijection φ φ.surjective]
  have ho := full_boundary_transport_of_filtered_initial hP
    (geometricTemplate N' old') (geometricTemplate N old) hOld'
    (fun H hH => g.full.1 H (List.mem_append_left _ hH))
  simp only [HironakaG3EmptyAwareFullBoundary.boundary_decomp,
    List.filter_append, List.map_append, emptyAware_born_boundary hP] at ho
  obtain ⟨hc, hb⟩ := retained_carrier_and_born_of_emptyAware g hN hBorn hP
  exact ⟨hc, List.append_cancel_right ho, hb⟩

private theorem compare_aligned_ordered_retained_below {hn : 0 < n} {k : ℕ}
    (ih : RetainedTraceComparableBelow.{u} hn k)
    {X X' Z Z' : CMfd.{u} n}
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {N' : Set X'} {old' born' : List (Set X')} (g' : NativeRetainedGeometry N' old' born')
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (hN : N' = φ ⁻¹' N) (hOld : liveBorn old' = (liveBorn old).map (φ ⁻¹' ·))
    (hBorn : liveBorn born' = (liveBorn born).map (φ ⁻¹' ·))
    {μ' μ : WithTop RetainedStampRank} {T' : BlowupTower X' Z'} {T : BlowupTower X Z}
    (R' : OrderedRetainedDefectTrace hn N' old' born' μ' T')
    (R : OrderedRetainedDefectTrace hn N old born μ T)
    (hCount : R'.phaseCount + R.phaseCount < k) :
    ∃ χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z, EmptyAwareTowerIso φ T' T χ := by
  have hBorn' : liveBorn born' = liveBorn (born.map (φ ⁻¹' ·)) := by
    unfold liveBorn at *
    rwa [filter_map_bijection φ φ.surjective]
  have hOld' : liveBorn old' = liveBorn (old.map (φ ⁻¹' ·)) := by
    unfold liveBorn at *
    rwa [filter_map_bijection φ φ.surjective]
  let S := transport φ T
  let Rφ := R.rebase φ g
  let R₀ : OrderedRetainedDefectTrace hn N' (old.map (φ ⁻¹' ·)) (born.map (φ ⁻¹' ·)) μ S.tower :=
    hN.symm ▸ Rφ
  have hCount₀ : R₀.phaseCount = R.phaseCount :=
    phaseCount_cast hN.symm rfl rfl rfl Rφ
  have gφ := native_geometry_rebase g φ
  rw [←hN] at gφ
  obtain ⟨χ,hχ⟩ := ih g' gφ hOld' hBorn' R' R₀ (by rwa [hCount₀])
  refine ⟨χ.trans S.back,?_⟩
  simpa only [Diffeomorph.refl_trans] using
    G3UniverseEmptyAwareCore.trans hχ (emptyAware_of_isTowerIso (transport_isTowerIso φ T))

set_option maxHeartbeats 900000 in
private theorem compare_actual_tails {hn : 0 < n} {k : ℕ} (ih : RetainedTraceComparableBelow.{u} hn k)
    {X A₁ A₂ Z₁ Z₂ : CMfd.{u} n} {N : Set X} {old₁ old₂ born₁ born₂ : List (Set X)}
    (g₁ : NativeRetainedGeometry N old₁ born₁) (g₂ : NativeRetainedGeometry N old₂ born₂)
    (hOld : liveBorn old₁ = liveBorn old₂) (hBorn : liveBorn born₁ = liveBorn born₂)
    {P₁ : BlowupTower X A₁} {P₂ : BlowupTower X A₂}
    (h₁ : IsGeoTestTower (geometricTemplate N born₁) P₁)
    (h₂ : IsGeoTestTower (geometricTemplate N born₂) P₂)
    (hF₁ : IsGeoTestTower (geometricTemplate (univ : Set X) (old₁ ++ born₁)) P₁)
    (hF₂ : IsGeoTestTower (geometricTemplate (univ : Set X) (old₂ ++ born₂)) P₂)
    {β : A₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A₂}
    (hP : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) P₁ P₂ β)
    {S₁ : BlowupTower A₁ Z₁} {S₂ : BlowupTower A₂ Z₂} {μ₁ μ₂ : WithTop RetainedStampRank}
    (R₁ : OrderedRetainedDefectTrace hn (geoTransformAlong (geometricTemplate N born₁) P₁).N
      (old₁.map (strictAlong P₁)) (geoTransformAlong (geometricTemplate N born₁) P₁).E μ₁ S₁)
    (R₂ : OrderedRetainedDefectTrace hn (geoTransformAlong (geometricTemplate N born₂) P₂).N
      (old₂.map (strictAlong P₂)) (geoTransformAlong (geometricTemplate N born₂) P₂).E μ₂ S₂)
    (hCount : R₁.phaseCount + R₂.phaseCount < k) :
    ∃ χ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂,
      EmptyAwareTowerIso β S₁ S₂ χ := by
  let M₁ := geometricTemplate N born₁
  let M₂ := geometricTemplate N born₂
  let C₁ := geoTransformAlong M₁ P₁
  let C₂ := geoTransformAlong M₂ P₂
  let L₁ := old₁.map (strictAlong P₁)
  let L₂ := old₂.map (strictAlong P₂)
  let ref := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hInitOld : liveBorn old₁ = (liveBorn old₂).map (ref ⁻¹' ·) := by
    change liveBorn old₁ = (liveBorn old₂).map id
    rw [List.map_id,hOld]
  have hInitBorn : liveBorn born₁ = (liveBorn born₂).map (ref ⁻¹' ·) := by
    change liveBorn born₁ = (liveBorn born₂).map id
    rw [List.map_id,hBorn]
  obtain ⟨hN,hO,hB⟩ := retained_filtered_inputs_of_emptyAware g₂ rfl hInitOld hInitBorn hP
  have hG₁ := actual_retained_born_recorded_residual_dictionary hn g₁.carrier g₁.full
    g₁.born_transverse g₁.dense P₁ h₁ hF₁
  have hG₂ := actual_retained_born_recorded_residual_dictionary hn g₂.carrier g₂.full
    g₂.born_transverse g₂.dense P₂ h₂ hF₂
  let g₁' : NativeRetainedGeometry C₁.N L₁ C₁.E :=
    ⟨hG₁.1,hG₁.2.1,hG₁.2.2.1,hG₁.2.2.2.1⟩
  have g₂' : NativeRetainedGeometry C₂.N L₂ C₂.E :=
    ⟨hG₂.1,hG₂.2.1,hG₂.2.2.1,hG₂.2.2.2.1⟩
  exact compare_aligned_ordered_retained_below ih g₂' g₁' β hN hO hB R₁ R₂ hCount


private theorem compare_actual_append {X A₁ A₂ Y₁ Y₂ Z₁ Z₂ : CMfd.{u} n}
    {T₁ : BlowupTower X Y₁} {T₂ : BlowupTower X Y₂}
    {P₁ : BlowupTower X A₁} {P₂ : BlowupTower X A₂}
    {S₁ : BlowupTower A₁ Z₁} {S₂ : BlowupTower A₂ Z₂}
    {e₁ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₁}
    {e₂ : Y₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂}
    (h₁ : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ (P₁.append S₁) e₁)
    (h₂ : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₂ (P₂.append S₂) e₂)
    {β : A₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A₂}
    {χ : Z₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂}
    (hP : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) P₁ P₂ β)
    (hS : EmptyAwareTowerIso β S₁ S₂ χ) :
    ∃ ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ ψ := by
  refine ⟨(e₁.trans χ).trans e₂.symm,?_⟩
  have h := G3UniverseEmptyAwareCore.trans
    (G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso h₁) (emptyAware_append hP hS))
    (emptyAware_of_isTowerIso h₂.symm)
  simpa only [Diffeomorph.refl_trans,Diffeomorph.symm_refl] using h

private theorem isEmptyTower_of_empty_support {X : CMfd.{u} n} :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver (∅ : Set X) T → IsEmptyTower T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, h => by
    have hc := h.2
    rw [preimage_empty] at hc
    exact ⟨isEmptyTower_of_empty_support T h.1,subset_empty_iff.mp hc⟩

private theorem empty_phase_of_empty_footprint {hn : 0 < n} {X Y : CMfd.{u} n}
    {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y}
    (P : RetainedDefectCrestPhase hn N old born T)
    (h : ¬P.footprint.Nonempty) : IsEmptyTower T :=
  isEmptyTower_of_empty_support T (Set.not_nonempty_iff_eq_empty.mp h ▸ P.centresOver)

private def reflHeadContinuation {hn : 0 < n} {X Y : CMfd.{u} n}
    {N : Set X} {old born : List (Set X)} {μ : WithTop RetainedStampRank}
    {T : BlowupTower X Y} (R : OrderedRetainedDefectTrace hn N old born μ T) :
    OrderedRetainedDefectTrace hn
      (geoTransformAlong (geometricTemplate N born) (.refl : BlowupTower X X)).N
      (old.map (strictAlong (.refl : BlowupTower X X)))
      (geoTransformAlong (geometricTemplate N born) (.refl : BlowupTower X X)).E μ T :=
  (List.map_id old).symm ▸ R

private theorem reflHeadContinuation_phaseCount {hn : 0 < n} {X Y : CMfd.{u} n}
    {N : Set X} {old born : List (Set X)} {μ : WithTop RetainedStampRank}
    {T : BlowupTower X Y} (R : OrderedRetainedDefectTrace hn N old born μ T) :
    (reflHeadContinuation R).phaseCount = R.phaseCount := by
  exact phaseCount_cast rfl (List.map_id old).symm rfl rfl R

set_option maxHeartbeats 700000 in
private theorem compare_skipping_right {hn : 0 < n} {k : ℕ} (ih : RetainedTraceComparableBelow.{u} hn k)
    {X Y₁ Y₂ A₂ Z₂ : CMfd.{u} n} {N : Set X} {old₁ old₂ born₁ born₂ : List (Set X)}
    (g₁ : NativeRetainedGeometry N old₁ born₁) (g₂ : NativeRetainedGeometry N old₂ born₂)
    (hOld : liveBorn old₁ = liveBorn old₂) (hBorn : liveBorn born₁ = liveBorn born₂)
    {P₂ : BlowupTower X A₂} (hEmpty : IsEmptyTower P₂)
    (hQ₂ : IsGeoTestTower (geometricTemplate N born₂) P₂)
    (hFull₂ : IsGeoTestTower (geometricTemplate (univ : Set X) (old₂ ++ born₂)) P₂)
    {T₁ : BlowupTower X Y₁} {T₂ : BlowupTower X Y₂} {S₂ : BlowupTower A₂ Z₂}
    {e₂ : Y₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂}
    (hI₂ : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₂ (P₂.append S₂) e₂)
    {μ₁ μ₂ : WithTop RetainedStampRank}
    (R₁ : OrderedRetainedDefectTrace hn N old₁ born₁ μ₁ T₁)
    (R₂ : OrderedRetainedDefectTrace hn (geoTransformAlong (geometricTemplate N born₂) P₂).N
      (old₂.map (strictAlong P₂)) (geoTransformAlong (geometricTemplate N born₂) P₂).E μ₂ S₂)
    (hCount : R₁.phaseCount + R₂.phaseCount < k) :
    ∃ ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ ψ := by
  let P₁ : BlowupTower X X := .refl
  obtain ⟨β,hβ⟩ := emptyAware_append_empty_tail P₁ P₂ hEmpty
  have hP : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) P₁ P₂ β.symm := by
    simpa only [P₁,BlowupTower.refl_append,Diffeomorph.symm_refl] using G3UniverseEmptyAwareCore.symm hβ
  have hI₁ : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ (P₁.append T₁)
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y₁ ∞) := by
    simpa only [P₁,BlowupTower.refl_append] using IsTowerIso.refl_self T₁
  have hCount' : (reflHeadContinuation R₁).phaseCount + R₂.phaseCount < k := by
    rwa [reflHeadContinuation_phaseCount]
  obtain ⟨χ,hχ⟩ := compare_actual_tails ih g₁ g₂ hOld hBorn (P₁ := P₁) trivial hQ₂ trivial hFull₂ hP
    (reflHeadContinuation R₁) R₂ hCount'
  exact compare_actual_append hI₁ hI₂ hP hχ


private theorem native_geometry_filter_old {X : CMfd.{u} n} {N : Set X}
    {old born : List (Set X)} (g : NativeRetainedGeometry N old born) :
    NativeRetainedGeometry N (liveBorn old) born := by
  have hSub : (liveBorn old ++ born).Sublist (old ++ born) := List.filter_sublist.append_right born
  refine ⟨g.carrier, isSNCDivisor_of_sublist g.full hSub, g.born_transverse,
    g.dense.trans (closure_mono ?_)⟩
  intro x hx
  refine ⟨hx.1, fun h => hx.2 ?_⟩
  simp only [mem_iUnion, exists_prop] at h ⊢
  obtain ⟨H, hH, hxH⟩ := h
  exact ⟨H, hSub.subset hH, hxH⟩

private theorem retained_defect_eq_of_filtered_inputs {X : CMfd.{u} n}
    (hn : 0 < n) {N : Set X} {old₁ old₂ born₁ born₂ : List (Set X)}
    (g₁ : NativeRetainedGeometry N old₁ born₁) (g₂ : NativeRetainedGeometry N old₂ born₂)
    (hOld : liveBorn old₁ = liveBorn old₂) (hBorn : liveBorn born₁ = liveBorn born₂) :
    actualFamilyDistinctDefect N (oldResidualPart N old₁ born₁) =
      actualFamilyDistinctDefect N (oldResidualPart N old₂ born₂) := by
  have h₁ := actualFamilyDistinctDefect_filter_empty_boundaries hn g₁.carrier g₁.full
    g₁.born_transverse g₁.dense
  have h₂ := actualFamilyDistinctDefect_filter_empty_boundaries hn g₂.carrier g₂.full
    g₂.born_transverse g₂.dense
  change actualFamilyDistinctDefect N (oldResidualPart N (liveBorn old₁) (liveBorn born₁)) = _ at h₁
  rw [hOld, hBorn] at h₁
  exact h₁.symm.trans h₂

/-- Attainment and the common pointwise ordered rank force each normalized
phase to choose the same crest. -/
private theorem realized_crest_compare_same_old {X Y₁ Y₂ : CMfd.{u} n}
    (hn : 0 < n) {N : Set X} {old born₁ born₂ : List (Set X)}
    (g₁ : NativeRetainedGeometry N old born₁) (g₂ : NativeRetainedGeometry N old born₂)
    (hBorn : liveBorn born₁ = liveBorn born₂)
    {T₁ : BlowupTower X Y₁} {T₂ : BlowupTower X Y₂}
    (P₁ : RetainedDefectCrestPhase hn N old born₁ T₁)
    (P₂ : RetainedDefectCrestPhase hn N old born₂ T₂)
    (hLive₁ : P₁.footprint.Nonempty) (hLive₂ : P₂.footprint.Nonempty) :
    ∃ ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ ψ := by
  have hDef := retained_defect_eq_of_filtered_inputs hn g₁ g₂ rfl hBorn
  have h₁ := (retainedDefect_and_rank_filter_empty_born N old born₁).2
  have h₂ := (retainedDefect_and_rank_filter_empty_born N old born₂).2
  change retainedDefectOrderedRank N old (liveBorn born₁) = _ at h₁
  rw [hBorn] at h₁
  have hRank := h₁.symm.trans h₂
  obtain ⟨x, hx⟩ := hLive₁
  obtain ⟨y, hy⟩ := hLive₂
  obtain ⟨hxd, hxr⟩ := (P₁.footprint_iff x).mp hx
  obtain ⟨hyd, hyr⟩ := (P₂.footprint_iff y).mp hy
  change retainedDefectOrderedRank N old born₁ x = P₁.rank at hxr
  change retainedDefectOrderedRank N old born₂ y = P₂.rank at hyr
  have hPQ : P₁.rank ≤ P₂.rank := by
    rw [← hxr, congrFun hRank x]
    exact P₂.rank_bound x (hDef ▸ hxd)
  have hQP : P₂.rank ≤ P₁.rank := by
    rw [← hyr, ← congrFun hRank y]
    exact P₁.rank_bound y (hDef.symm ▸ hyd)
  exact retained_crest_emptyAware_of_rank_eq hn g₁.carrier g₁.full g₂.full
    g₁.born_transverse g₂.born_transverse g₁.dense g₂.dense hBorn P₁ P₂ (le_antisymm hPQ hQP)

private theorem realized_crest_compare_filtered {X Y₁ Y₂ : CMfd.{u} n}
    (hn : 0 < n) {N : Set X} {old₁ old₂ born₁ born₂ : List (Set X)}
    (g₁ : NativeRetainedGeometry N old₁ born₁) (g₂ : NativeRetainedGeometry N old₂ born₂)
    (hOld : liveBorn old₁ = liveBorn old₂) (hBorn : liveBorn born₁ = liveBorn born₂)
    {T₁ : BlowupTower X Y₁} {T₂ : BlowupTower X Y₂}
    (P₁ : RetainedDefectCrestPhase hn N old₁ born₁ T₁)
    (P₂ : RetainedDefectCrestPhase hn N old₂ born₂ T₂)
    (hLive₁ : P₁.footprint.Nonempty) (hLive₂ : P₂.footprint.Nonempty) :
    ∃ ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ ψ := by
  obtain ⟨Q₁, hF₁, _, _⟩ := exists_filterEmptyOldRetainedCrestPhase g₁.carrier g₁.full
    g₁.born_transverse g₁.dense P₁ hLive₁
  obtain ⟨Q₂, hF₂, _, _⟩ := exists_filterEmptyOldRetainedCrestPhase g₂.carrier g₂.full
    g₂.born_transverse g₂.dense P₂ hLive₂
  have compare_on_common_old {O : List (Set X)} (hO : O = liveBorn old₁)
      (g : NativeRetainedGeometry N O born₂)
      (Q : RetainedDefectCrestPhase hn N O born₂ T₂) (hQ : Q.footprint.Nonempty) :
      ∃ ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
        EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ ψ := by
    subst O
    exact realized_crest_compare_same_old hn (native_geometry_filter_old g₁) g hBorn
      Q₁ Q (hF₁ ▸ hLive₁) hQ
  exact compare_on_common_old hOld.symm (native_geometry_filter_old g₂) Q₂ (hF₂ ▸ hLive₂)


set_option maxHeartbeats 1200000 in
private theorem compare_retained_below {hn : 0 < n} :
    ∀ k, RetainedTraceComparableBelow.{u} hn k := by
  intro k
  induction k with
  | zero =>
    intro X Y₁ Y₂ N old₁ old₂ born₁ born₂ g₁ g₂ hOld hBorn μ₁ μ₂ T₁ T₂ R₁ R₂ hCount
    exact (Nat.not_lt_zero _ hCount).elim
  | succ k ih =>
    intro X Y₁ Y₂ N old₁ old₂ born₁ born₂ g₁ g₂ hOld hBorn μ₁ μ₂ T₁ T₂ R₁ R₂ hCount
    have hDef := retained_defect_eq_of_filtered_inputs hn g₁ g₂ hOld hBorn
    generalize hCount₁ : R₁.phaseCount = k₁ at hCount
    generalize hCount₂ : R₂.phaseCount = k₂ at hCount
    have H₁ : OrderedRetainedTraceHead hn N old₁ born₁ μ₁ T₁ k₁ :=
      hCount₁ ▸ orderedRetainedTraceHead R₁
    have H₂ : OrderedRetainedTraceHead hn N old₂ born₂ μ₂ T₂ k₂ :=
      hCount₂ ▸ orderedRetainedTraceHead R₂
    cases H₁ with
    | done no₁ e₁ hI₁ =>
      cases H₂ with
      | done _no₂ e₂ hI₂ =>
        refine ⟨e₁.trans e₂.symm,?_⟩
        simpa only [Diffeomorph.symm_refl,Diffeomorph.refl_trans] using
          G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso hI₁) (emptyAware_of_isTowerIso hI₂.symm)
      | phase P₂ S₂ p₂ _b₂ test₂ full₂ STrace₂ e₂ hI₂ =>
        have hEmpty := empty_phase_of_empty_footprint p₂ fun ⟨x, hx⟩ => by
          have hd := ((p₂.footprint_iff x).mp hx).1
          rw [←hDef,no₁] at hd
          exact hd.elim
        exact compare_skipping_right ih g₁ g₂ hOld hBorn hEmpty test₂ full₂ hI₂ R₁ STrace₂ (by omega)
    | phase P₁ S₁ p₁ _b₁ test₁ full₁ STrace₁ e₁ hI₁ =>
      cases H₂ with
      | done no₂ e₂ hI₂ =>
        have hEmpty := empty_phase_of_empty_footprint p₁ fun ⟨x, hx⟩ => by
          have hd := ((p₁.footprint_iff x).mp hx).1
          rw [hDef,no₂] at hd
          exact hd.elim
        obtain ⟨ψ,hψ⟩ :=
          compare_skipping_right ih g₂ g₁ hOld.symm hBorn.symm hEmpty test₁ full₁ hI₁ R₂ STrace₁ (by omega)
        exact ⟨ψ.symm,by simpa only [Diffeomorph.symm_refl] using G3UniverseEmptyAwareCore.symm hψ⟩
      | phase P₂ S₂ p₂ _b₂ test₂ full₂ STrace₂ e₂ hI₂ =>
        by_cases hLive₁ : p₁.footprint.Nonempty
        · by_cases hLive₂ : p₂.footprint.Nonempty
          · obtain ⟨β,hβ⟩ := realized_crest_compare_filtered hn g₁ g₂ hOld hBorn p₁ p₂ hLive₁ hLive₂
            obtain ⟨χ,hχ⟩ := compare_actual_tails ih g₁ g₂ hOld hBorn test₁ test₂ full₁ full₂ hβ
              STrace₁ STrace₂ (by omega)
            exact compare_actual_append hI₁ hI₂ hβ hχ
          · exact compare_skipping_right ih g₁ g₂ hOld hBorn
              (empty_phase_of_empty_footprint p₂ hLive₂) test₂ full₂ hI₂ R₁ STrace₂ (by omega)
        · obtain ⟨ψ,hψ⟩ := compare_skipping_right ih g₂ g₁ hOld.symm hBorn.symm
            (empty_phase_of_empty_footprint p₁ hLive₁) test₁ full₁ hI₁ R₂ STrace₁ (by omega)
          exact ⟨ψ.symm,by simpa only [Diffeomorph.symm_refl] using G3UniverseEmptyAwareCore.symm hψ⟩

/-- On a common base, retained traces with the same ordered live old and
born boundaries compare on the actual towers, allowing empty stages. -/
theorem compare_filtered_ordered_retained_traces {hn : 0 < n}
    {X Y₁ Y₂ : CMfd.{u} n} {N : Set X} {old₁ old₂ born₁ born₂ : List (Set X)}
    (g₁ : NativeRetainedGeometry N old₁ born₁) (g₂ : NativeRetainedGeometry N old₂ born₂)
    (hOld : liveBorn old₁ = liveBorn old₂) (hBorn : liveBorn born₁ = liveBorn born₂)
    {μ₁ μ₂ : WithTop RetainedStampRank} {T₁ : BlowupTower X Y₁} {T₂ : BlowupTower X Y₂}
    (R₁ : OrderedRetainedDefectTrace hn N old₁ born₁ μ₁ T₁)
    (R₂ : OrderedRetainedDefectTrace hn N old₂ born₂ μ₂ T₂) :
    ∃ ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ ψ :=
  compare_retained_below (R₁.phaseCount + R₂.phaseCount + 1)
    g₁ g₂ hOld hBorn R₁ R₂ (Nat.lt_succ_self _)

/-- Any two finite ordered retained histories on the same physical source
compare stage by stage, allowing empty centres on either side and
preserving every ordered original boundary position. -/
theorem compare_ordered_retained_traces {hn : 0 < n}
    {X Y₁ Y₂ : CMfd.{u} n} {N : Set X} {old born₁ born₂ : List (Set X)}
    (g₁ : NativeRetainedGeometry N old born₁) (g₂ : NativeRetainedGeometry N old born₂)
    (hBorn : liveBorn born₁ = liveBorn born₂)
    {μ₁ μ₂ : WithTop RetainedStampRank} {T₁ : BlowupTower X Y₁} {T₂ : BlowupTower X Y₂}
    (R₁ : OrderedRetainedDefectTrace hn N old born₁ μ₁ T₁)
    (R₂ : OrderedRetainedDefectTrace hn N old born₂ μ₂ T₂) :
    ∃ ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T₁ T₂ ψ :=
  compare_filtered_ordered_retained_traces g₁ g₂ rfl hBorn R₁ R₂

/-- Compare ordered retained traces on literal overlap bases identified
by a biholomorphism. The surviving old and born slots match in order. -/
theorem compare_aligned_filtered_ordered_retained_traces {hn : 0 < n} {X X' Z Z' : CMfd.{u} n}
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {N' : Set X'} {old' born' : List (Set X')} (g' : NativeRetainedGeometry N' old' born')
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (hN : N' = φ ⁻¹' N) (hOld : liveBorn old' = (liveBorn old).map (φ ⁻¹' ·))
    (hBorn : liveBorn born' = (liveBorn born).map (φ ⁻¹' ·))
    {μ' μ : WithTop RetainedStampRank} {T' : BlowupTower X' Z'} {T : BlowupTower X Z}
    (R' : OrderedRetainedDefectTrace hn N' old' born' μ' T')
    (R : OrderedRetainedDefectTrace hn N old born μ T) :
    ∃ χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z, EmptyAwareTowerIso φ T' T χ :=
  compare_aligned_ordered_retained_below
    (compare_retained_below (R'.phaseCount + R.phaseCount + 1)) g g' φ hN hOld hBorn R' R (Nat.lt_succ_self _)

/-- Compare two ordered traces on biholomorphically matched literal
carrier and old boundary, allowing the empty born slots to differ. -/
theorem compare_aligned_ordered_retained_traces {hn : 0 < n} {X X' Z Z' : CMfd.{u} n}
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {N' : Set X'} {old' born' : List (Set X')} (g' : NativeRetainedGeometry N' old' born')
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (hN : N' = φ ⁻¹' N) (hOld : old' = old.map (φ ⁻¹' ·))
    (hBorn : liveBorn born' = (liveBorn born).map (φ ⁻¹' ·))
    {μ' μ : WithTop RetainedStampRank} {T' : BlowupTower X' Z'} {T : BlowupTower X Z}
    (R' : OrderedRetainedDefectTrace hn N' old' born' μ' T')
    (R : OrderedRetainedDefectTrace hn N old born μ T) :
    ∃ χ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z, EmptyAwareTowerIso φ T' T χ :=
  compare_aligned_filtered_ordered_retained_traces g g' φ hN
    (by rw [hOld]; exact filter_map_bijection φ φ.surjective _) hBorn R' R

end
end Hironaka.HironakaG4RetainedTraceComparison
