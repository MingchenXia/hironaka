import Hironaka.Resolution.HironakaG8NativeSimultaneousTerminal
import Hironaka.Resolution.HironakaG8NativeUniformClockRank
import Hironaka.Resolution.HironakaG8NativeBoundaryComparison

/-! Comparing complete synchronized native phases on the common
filtered ambient boundary, retaining each window's literal clock. -/

set_option autoImplicit false
set_option maxHeartbeats 3800000

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeFilteredSimultaneousTerminal

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealBiholomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaStageCenters HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  NormalCrossings HironakaG8NativeRelativeClearing HironakaG8NativeSimultaneousCentre
  HironakaG8NativeSimultaneousTerminal HironakaG8NativeUniformClockRank
  HironakaG3EmptyAwareHistory HironakaOriginalBoundaryEmptyFilterComparison
  HironakaG8NativeBoundaryComparison HironakaSmoothSubmersionOriginalAmbientCanonical

variable {n : ℕ} {X Y Z : CMfd.{0} n} {I J : Type}
variable {W D : Set X} {E F : List (Set X)} {H : ℕ → ℕ}

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)
local notation "ref" B => Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B ∞
local notation "inv" => ResolutionInvariantSeq.ResolutionInvariant.inv (canonicalInvariant n)
local notation "original[" W ";" E "]" =>
  (MarkedIdeal.mk univ E (vanishingIdeal (n := n) W) 1 : MarkedIdeal n _)

/-- The ambient filter is computed once, before restricting any native
record. Every remaining slot keeps its original position relative to
the other retained slots, including slots empty on one window only. -/
def NativeWindows.filterAmbientEmpty (A : NativeWindows X I W E H D) :
    NativeWindows X I W (E.filter (fun B => decide B.Nonempty)) H D where
  openSet := A.openSet
  record i := withMappedBoundary (A.record i) ((Subtype.val : A.openSet i → X) ⁻¹' ·)
    (E.filter (fun B => decide B.Nonempty))
  domain i := by
    have hList : ((E.filter (fun B => decide B.Nonempty)).map ((Subtype.val : A.openSet i → X) ⁻¹' ·)).Sublist
        (A.record i).E := by
      rw [A.boundary]
      exact List.Sublist.map _ List.filter_sublist
    exact ⟨NormalCrossingsComparison.isWellFormed_withE (A.domain i).isWellFormed hList,
      (A.domain i).dimLE,(A.domain i).one_le_d,(A.domain i).isNonzeroAlongAt⟩
  native i := A.native i
  boundary _ := rfl
  exponent := A.exponent
  positive := A.positive
  mark := A.mark
  commonMark i := A.commonMark i
  covers := A.covers

private theorem filterAmbientEmpty_powered (A : NativeWindows X I W E H D) (i : I) :
    (NativeWindows.filterAmbientEmpty A).powered i =
      withMappedBoundary (A.powered i) ((Subtype.val : A.openSet i → X) ⁻¹' ·)
        (E.filter (fun B => decide B.Nonempty)) := rfl

private theorem withMappedBoundary_powered (A : NativeWindows X I W E H D) (i : I) :
    withMappedBoundary (A.powered i) ((Subtype.val : A.openSet i → X) ⁻¹' ·) E = A.powered i :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl (A.boundary i).symm rfl rfl

/-- Removing only globally empty initial slots leaves the same actual
terminal history, including the simultaneous centres across windows. -/
theorem NativeSynchronizedTerminal.filterAmbientEmpty (hn : 0 < n)
    {A : NativeWindows X I W E H D} {T : BlowupTower X Y}
    (hT : NativeSynchronizedTerminal A T) :
    NativeSynchronizedTerminal (NativeWindows.filterAmbientEmpty A) T := by
  have hSupport {Y' : CMfd.{0} n} (S : BlowupTower X Y') (i : I) :
      (geoTransformAlong (A.powered i) (restrict (A.openSet i) S)).cosupp =
        (geoTransformAlong ((NativeWindows.filterAmbientEmpty A).powered i)
          (restrict (A.openSet i) S)).cosupp := by
    have h := mapped_global_empty_filter_cosupp (A.powered i)
      ((Subtype.val : A.openSet i → X) ⁻¹' ·) preimage_empty E (restrict (A.openSet i) S)
    rw [withMappedBoundary_powered A i,← filterAmbientEmpty_powered A i] at h
    exact h.symm
  have hOrder {Y' : CMfd.{0} n} (S : BlowupTower X Y') (i j : I)
      (y : openPreimage S (A.openSet i)) (z : openPreimage S (A.openSet j)) :
      inv (A.powered i) (restrict (A.openSet i) S) y < inv (A.powered j) (restrict (A.openSet j) S) z ↔
        inv ((NativeWindows.filterAmbientEmpty A).powered i) (restrict (A.openSet i) S) y <
          inv ((NativeWindows.filterAmbientEmpty A).powered j) (restrict (A.openSet j) S) z := by
    have h := mapped_global_empty_filter_order_iff hn n (A.powered i) (A.powered j)
      ((Subtype.val : A.openSet i → X) ⁻¹' ·) ((Subtype.val : A.openSet j → X) ⁻¹' ·)
      preimage_empty preimage_empty E (restrict (A.openSet i) S) (restrict (A.openSet j) S) y z
    dsimp only at h
    rw [withMappedBoundary_powered A i,withMappedBoundary_powered A j,
      ← filterAmbientEmpty_powered A i,← filterAmbientEmpty_powered A j] at h
    simp only [canonicalInvariant_eq_invFamily hn]
    exact h.symm
  refine ⟨(isGeoTestTower_nonemptyBoundary_iff original[W;E] T).mpr hT.test,
    hT.singular,?_,simultaneousStages_of_same_order hSupport (fun S i j y z _ _ => hOrder S i j y z)
      T hT.simultaneous,fun i => (hSupport T i).symm.trans (hT.terminal i)⟩
  intro i
  have h := canonical_mapped_global_empty_filter_iff hn n (A.powered i)
    ((Subtype.val : A.openSet i → X) ⁻¹' ·) preimage_empty E (restrict (A.openSet i) T)
  dsimp only at h
  rw [withMappedBoundary_powered A i,← filterAmbientEmpty_powered A i] at h
  change IsCanonical ((NativeWindows.filterAmbientEmpty A).powered i)
    (inv ((NativeWindows.filterAmbientEmpty A).powered i)) (restrict (A.openSet i) T)
  simp only [canonicalInvariant_eq_invFamily hn]
  exact h.mpr (by simpa only [canonicalInvariant_eq_invFamily hn] using hT.canonical i)

private theorem native_terminal_cast_boundary {A : NativeWindows X I W E H D}
    {T : BlowupTower X Y} (h : E = F) (hT : NativeSynchronizedTerminal A T) :
    NativeSynchronizedTerminal (h ▸ A : NativeWindows X I W F H D) T := by
  subst F
  exact hT

/-- Complete same-profile towers compare on a common actual ambient
base when the original boundaries differ by globally empty positions.
All local rank comparisons use the same ambient slot mask. -/
theorem native_simultaneous_terminal_emptyAware_of_filtered_boundary (hn : 0 < n)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (hSame : E.filter (fun B => decide B.Nonempty) = F.filter (fun B => decide B.Nonempty))
    {A : NativeWindows X I W E H D} {B : NativeWindows X J W F H D}
    {T : BlowupTower X Y} {S : BlowupTower X Z}
    (hT : NativeSynchronizedTerminal A T) (hS : NativeSynchronizedTerminal B S) :
    ∃ χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z, EmptyAwareTowerIso (ref X) T S χ := by
  have hE' := NormalCrossingsComparison.isSNCDivisor_of_sublist hE
    (List.filter_sublist (p := fun B : Set X => decide B.Nonempty))
  have hNot' : ∀ B ∈ E.filter (fun B => decide B.Nonempty), ∀ x ∈ D, x ∈ B →
      ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W :=
    fun B hB => hNot B (List.mem_of_mem_filter hB)
  let B' : NativeWindows X J W (E.filter (fun B => decide B.Nonempty)) H D :=
    hSame.symm ▸ NativeWindows.filterAmbientEmpty B
  have hS' : NativeSynchronizedTerminal B' S :=
    native_terminal_cast_boundary hSame.symm (NativeSynchronizedTerminal.filterAmbientEmpty hn hS)
  exact native_simultaneous_terminal_emptyAware hn hW hE' hExact hNot'
    (NativeSynchronizedTerminal.filterAmbientEmpty hn hT) hS'

end
end Hironaka.HironakaG8NativeFilteredSimultaneousTerminal
