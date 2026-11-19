import Hironaka.Resolution.HironakaG8ParallelStepReadback
import Hironaka.Resolution.HironakaG34CanonicalLocalEquivariance
import Hironaka.Resolution.HironakaOriginalTerminalProjectionUniqueness

/-! Exact marked-record readback through a finite tape of parallel rounds. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FiniteParallelReadback
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HironakaG34CanonicalLocalEquivariance
  HironakaG8ParallelStepReadback

variable {n : ℕ} {X : CMfd.{0} n}

/-- A local tape records an actual blowup (possibly empty) in every round.
At each round its centre is the exact selected/empty trace under the
already matched prefixes. No comparison of the new stages is supplied. -/
inductive SelectedParallelTape (U : Opens X) {A : CMfd.{0} n} (P₀ : BlowupTower X A) :
    {Y Z : CMfd.{0} n} → BlowupTower X Y → BlowupTower (CMfd.of (n := n) U) Z → Prop
  | start : SelectedParallelTape U P₀ P₀ (restrict U P₀)
  | round {Y Z Y' Z' : CMfd.{0} n}
      {P : BlowupTower X Y} {S : BlowupTower (CMfd.of (n := n) U) Z}
      (hPrev : SelectedParallelTape U P₀ P S)
      {ι : Type} {C : ι → Set Y} {π : Y' → Y}
      (hπ : IsBlowupAlong n (⋃ i, C i) π) (selected : Option ι)
      (hTrace : (Subtype.val : openPreimage P U → Y) ⁻¹' (⋃ i, C i) =
        selected.elim ∅ (fun i => (Subtype.val : openPreimage P U → Y) ⁻¹' C i))
      {D : Set Z} {ρ : Z' → Z} (hρ : IsBlowupAlong n D ρ)
      (hLocal : ∀ e : CMfd.of (n := n) (openPreimage P U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) (restrict U P) S e →
        e ⁻¹' D = selected.elim ∅ (fun i => (Subtype.val : openPreimage P U → Y) ⁻¹' C i)) :
      SelectedParallelTape U P₀ (.step P (⋃ i, C i) π hπ) (.step S D ρ hρ)

/-- To extend a tape, it suffices to compare its chosen local centre
with the trace under one already known prefix comparison. -/
theorem SelectedParallelTape.round_of_known_prefix
    {U : Opens X} {A Y Z Y' Z' : CMfd.{0} n} {P₀ : BlowupTower X A}
    {P : BlowupTower X Y} {S : BlowupTower (CMfd.of (n := n) U) Z}
    (hPrev : SelectedParallelTape U P₀ P S)
    {ι : Type} {C : ι → Set Y} {π : Y' → Y}
    (hπ : IsBlowupAlong n (⋃ i, C i) π) (selected : Option ι)
    (hTrace : (Subtype.val : openPreimage P U → Y) ⁻¹' (⋃ i, C i) =
      selected.elim ∅ (fun i => (Subtype.val : openPreimage P U → Y) ⁻¹' C i))
    {D : Set Z} {ρ : Z' → Z} (hρ : IsBlowupAlong n D ρ)
    {e : CMfd.of (n := n) (openPreimage P U) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (hIso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) (restrict U P) S e)
    (hLocal : e ⁻¹' D = selected.elim ∅ (fun i => (Subtype.val : openPreimage P U → Y) ⁻¹' C i)) :
    SelectedParallelTape U P₀ (.step P (⋃ i, C i) π hπ) (.step S D ρ hρ) := by
  refine .round hPrev hπ selected hTrace hρ ?_
  intro e' he'
  have hEq := HironakaOriginalTerminalProjectionUniqueness.biholomorphisms_eq_of_actual_proj_eq S e' e
    (fun x => (he'.proj_comm x).symm.trans (hIso.proj_comm x))
  rwa [hEq]

/-- At each successor, uniqueness of the blowup along the corresponding
centre supplies the new endpoint map and extends the strict tower iso. -/
theorem SelectedParallelTape.exists_strict_comparison
    {U : Opens X} {A Y Z : CMfd.{0} n} {P₀ : BlowupTower X A}
    {P : BlowupTower X Y} {S : BlowupTower (CMfd.of (n := n) U) Z}
    (h : SelectedParallelTape U P₀ P S) :
    ∃ e : CMfd.of (n := n) (openPreimage P U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) (restrict U P) S e := by
  induction h with
  | start => exact ⟨_,IsTowerIso.refl_self _⟩
  | @round Y Z Y' Z' P S hPrev ι C π hπ selected hTrace D ρ hρ hLocal ih =>
    obtain ⟨e,hIso⟩ := ih
    have heq := (hLocal e hIso).trans hTrace.symm
    have hπ' := BlowupRestrictOpen.isBlowupAlong_restrict hπ (openPreimage P U)
      ((openPreimage P U).isOpen.preimage hπ.contMDiff.continuous)
    exact exists_isTowerIso_step hIso hπ' hρ heq

/-- Original TEST and the whole ordered geometric transform commute with
the single strict comparison of the entire finite local tape. -/
theorem SelectedParallelTape.original_test_and_marked_record
    {U : Opens X} {A Y Z : CMfd.{0} n} {P₀ : BlowupTower X A}
    {P : BlowupTower X Y} {S : BlowupTower (CMfd.of (n := n) U) Z}
    (h : SelectedParallelTape U P₀ P S) (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : IsGeoTestTower M P) :
    let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
    ∃ e : CMfd.of (n := n) (openPreimage P U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) (restrict U P) S e ∧
      IsGeoTestTower MU S ∧
      MarkedIdeal.pullback (Subtype.val : openPreimage P U → Y) (geoTransformAlong M P) =
        MarkedIdeal.pullback e (geoTransformAlong MU S) := by
  dsimp only
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  obtain ⟨e,hIso⟩ := h.exists_strict_comparison
  have hMU := IsWellFormed.pullback_val hM U
  have hLocal := isGeoTestTower_restrict U hM.isClosedSubmanifold_N hM.isCoherent P hTest
  have hId : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) MU = MU :=
    ContactCanonicalAlong.pullback_id MU hMU.isCoherent
  have hTests := IsTowerIso.isGeoTestTower_iff (𝔪 := MU) _ hMU.isClosedSubmanifold_N hMU.isCoherent hIso
  rw [hId] at hTests
  have hS := hTests.mp hLocal
  have hExact := IsTowerIso.geoTransformAlong_eq (𝔪 := MU) _ hMU.isClosedSubmanifold_N hMU.isCoherent hIso hS
  rw [hId,geoTransformAlong_restrict U hM.isClosedSubmanifold_N hM.isCoherent P hTest] at hExact
  exact ⟨e,hIso,hS,hExact⟩

end Hironaka.HironakaG8FiniteParallelReadback
