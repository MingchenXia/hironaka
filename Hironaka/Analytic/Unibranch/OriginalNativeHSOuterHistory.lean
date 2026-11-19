import Hironaka.Analytic.Unibranch.OriginalNativeHSPhaseHistory

/-! Actual compact native outer-HS runs, retaining every actual phase and
physical native arrow for the LITERAL fixed original invariant family.
Blueprint FIRST: original-native-hs-outer-history.tex.
No noncompact, independent-choice, smooth or reset-boundary claim. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSOuterHistory
noncomputable section
open Hironaka Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11SingularCentreModification HironakaG11HSPhaseInduction
  HironakaG11StrictTransformTowers OriginalNativeHSPhaseHistory

/-- Data of the actual chronological native arrows, refining the held predicate. -/
inductive PhysicalHistory : SourceReducedComplexSpace → SourceReducedComplexSpace → Type 1
  | nil (X : SourceReducedComplexSpace) : PhysicalHistory X X
  | snoc {X Y Z : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
      (p : Z ⟶ Y) (hp : IsSingularCentreStep p) : PhysicalHistory X Z

namespace PhysicalHistory

def projection {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y) : Y ⟶ X :=
  match Y, h with
  | _, .nil _ => 𝟙 X
  | _, .snoc k p _ => p ≫ k.projection
termination_by structural h

def length {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y) : ℕ :=
  match h with
  | .nil _ => 0
  | .snoc k _ _ => k.length + 1
termination_by structural h

def append {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y) :
    {Z : SourceReducedComplexSpace} → PhysicalHistory Y Z → PhysicalHistory X Z
  | _, .nil _ => h
  | _, .snoc k p hp => .snoc (h.append k) p hp

theorem projection_append {X Y Z : SourceReducedComplexSpace}
    (h : PhysicalHistory X Y) (k : PhysicalHistory Y Z) :
    (h.append k).projection = k.projection ≫ h.projection := by
  induction k with
  | nil => simp only [append, projection, Category.id_comp]
  | snoc k p hp ih =>
      change p ≫ (h.append k).projection = (p ≫ k.projection) ≫ h.projection
      rw [ih, Category.assoc]

theorem length_append {X Y Z : SourceReducedComplexSpace}
    (h : PhysicalHistory X Y) (k : PhysicalHistory Y Z) :
    (h.append k).length = h.length + k.length := by
  induction k with
  | nil => simp only [append, length, Nat.add_zero]
  | snoc k p hp ih =>
      change (h.append k).length + 1 = h.length + (k.length + 1)
      rw [ih, Nat.add_assoc]

theorem singularModification {X Y : SourceReducedComplexSpace} (h : PhysicalHistory X Y) :
    IsSingularCentreModification h.projection := by
  induction h with
  | nil => exact .id X
  | snoc h p hp ih => exact .cons p h.projection hp ih

end PhysicalHistory

/-- Exactly an ordinary compact original reduced analytic space. -/
structure CompactSource where
  space : SourceReducedComplexSpace
  compact : CompactSpace space.obj.left

attribute [instance] CompactSource.compact

/-- Ordinary maximal singular point; no current centre or endpoint field. -/
structure Start (C : CompactSource) where
  point : C.space.obj.left
  singular : point ∈ intrinsicSingularLocus C.space.obj
  maximal : ∀ x ∈ intrinsicSingularLocus C.space.obj,
    toLex (originalStalkHS C.space x) ≤ toLex (originalStalkHS C.space point)

/-- The actual ordinary point is chosen internally from nonsmoothness. -/
def chooseStart (C : CompactSource) (hns : ¬C.space.IsSmooth) : Start C :=
  let h := OriginalCompactIntrinsicHSProfiles.exists_original_compact_singular_hs_lex_maximum C.space hns
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

namespace Start
variable {C : CompactSource} (S : Start C)

/-- SAME internally generated original minimal native windows. -/
def windows := OriginalNativeHSPhaseHistory.windows C.space S.point S.singular S.maximal

/-- Fixed literal original family, not a newly chosen existential invariant. -/
def invariant := originalInvariant (originalStalkHS C.space S.point 1 - 1)

def stage (m : ℕ) := S.windows.nativeStage S.invariant m

def clock : ℕ := S.windows.clock S.invariant

/-- SAME actual terminal phase source with derived compactness. -/
abbrev next : CompactSource :=
  ⟨(S.stage S.clock).Y, S.windows.terminal_compact S.invariant⟩

def projection : S.next.space ⟶ C.space := (S.stage S.clock).q

theorem drop :
    letI := S.next.compact
    Multiset.IsDershowitzMannaLT (singHSValues S.next.space).val (singHSValues C.space).val := by
  let := S.next.compact
  exact S.windows.terminal_drop S.invariant S.point S.singular rfl

/-- All physical prefixes of the chosen phase, not just its endpoint. -/
def physicalHistory : (m : ℕ) → PhysicalHistory C.space (S.stage m).Y
  | 0 => .nil C.space
  | m + 1 => .snoc (physicalHistory m) (S.windows.step S.invariant m)
      (S.windows.step_singular S.invariant m)

theorem physicalHistory_projection : ∀ m, (S.physicalHistory m).projection = (S.stage m).q
  | 0 => rfl
  | m + 1 => by
      change S.windows.step S.invariant m ≫ (S.physicalHistory m).projection = _
      rw [physicalHistory_projection m]
      exact (S.windows.step_projection S.invariant m).symm

theorem physicalHistory_length : ∀ m, (S.physicalHistory m).length = m
  | 0 => rfl
  | m + 1 => by
      change (S.physicalHistory m).length + 1 = m + 1
      rw [physicalHistory_length m]

end Start

/-- Actual retained phase recursion; each next object is the SAME phase source. -/
inductive Run : CompactSource → Type 1
  | done (C : CompactSource) (smooth : C.space.IsSmooth) : Run C
  | phase {C : CompactSource} (start : Start C) (tail : Run start.next) : Run C

namespace Run

def endpoint {C : CompactSource} (r : Run C) : SourceReducedComplexSpace :=
  match r with
  | .done C _ => C.space
  | .phase _ tail => tail.endpoint
termination_by structural r

def projection {C : CompactSource} (r : Run C) : r.endpoint ⟶ C.space :=
  match r with
  | .done C _ => 𝟙 C.space
  | .phase S tail => tail.projection ≫ S.projection
termination_by structural r

def phaseCount {C : CompactSource} (r : Run C) : ℕ :=
  match r with
  | .done _ _ => 0
  | .phase _ tail => 1 + tail.phaseCount
termination_by structural r

def stepCount {C : CompactSource} (r : Run C) : ℕ :=
  match r with
  | .done _ _ => 0
  | .phase S tail => S.clock + tail.stepCount
termination_by structural r

/-- Concatenate the SAME actual arrows, retaining every phase clock. -/
def physicalHistory {C : CompactSource} (r : Run C) : PhysicalHistory C.space r.endpoint :=
  match r with
  | .done C _ => .nil C.space
  | .phase S tail => (S.physicalHistory S.clock).append tail.physicalHistory
termination_by structural r

theorem physicalHistory_length {C : CompactSource} (r : Run C) :
    r.physicalHistory.length = r.stepCount := by
  induction r with
  | done C h => rfl
  | phase S tail ih =>
      dsimp only [Start.next] at *
      change ((S.physicalHistory S.clock).append tail.physicalHistory).length = S.clock + tail.stepCount
      rw [PhysicalHistory.length_append, S.physicalHistory_length, ih]

theorem physicalHistory_projection {C : CompactSource} (r : Run C) :
    r.physicalHistory.projection = r.projection := by
  induction r with
  | done C h => rfl
  | phase S tail ih =>
      dsimp only [Start.next] at *
      change ((S.physicalHistory S.clock).append tail.physicalHistory).projection =
        tail.projection ≫ S.projection
      rw [PhysicalHistory.projection_append, ih, S.physicalHistory_projection]
      rfl

theorem source_smooth {C : CompactSource} (r : Run C) : r.endpoint.IsSmooth := by
  induction r with
  | done C h => exact h
  | phase S tail ih => exact ih

end Run

/-- Genuine well-founded construction from ordinary compact original input. -/
theorem exists_run (C : CompactSource) : Nonempty (Run C) := by
  classical
  let : WellFoundedLT HSValue := HironakaG11BennettStabilization.hsStabilization
  suffices h : ∀ (M : Multiset HSValue) (D : CompactSource),
      (singHSValues D.space).val = M → Nonempty (Run D) by
    exact h _ C rfl
  intro M
  induction M using (Multiset.wellFounded_isDershowitzMannaLT (α := HSValue)).induction with
  | _ M ih =>
    intro D hDM
    by_cases hsm : D.space.IsSmooth
    · exact ⟨.done D hsm⟩
    let S := chooseStart D hsm
    let := S.next.compact
    have hlt := S.drop
    rw [hDM] at hlt
    obtain ⟨tail⟩ := ih _ hlt S.next rfl
    exact ⟨.phase S tail⟩

/-- An actual finite run; no unproved independence of this choice is asserted. -/
def run (C : CompactSource) : Run C := (exists_run C).some

namespace Run
variable {C : CompactSource} (r : Run C)

theorem singularModification : IsSingularCentreModification r.projection := by
  rw [← r.physicalHistory_projection]
  exact r.physicalHistory.singularModification

theorem originalReg : IsIsoOver r.projection (intrinsicRegularLocus C.space.obj) :=
  r.singularModification.isIsoOver_intrinsicRegularLocus

theorem proper : IsProperMap r.projection.hom.left.base := r.singularModification.isProperMap

theorem surjective : Function.Surjective r.projection.hom.left.base := r.singularModification.surjective

theorem source_compact : CompactSpace r.endpoint.obj.left := r.singularModification.source_compact

theorem dense_originalReg : Dense (r.projection.hom.left.base ⁻¹' intrinsicRegularLocus C.space.obj) :=
  r.singularModification.dense_preimage_intrinsicRegularLocus

theorem resolution : IsResolution r.projection := r.singularModification.isResolution r.source_smooth

theorem scalar : r.projection.hom.left ≫ C.space.obj.hom = r.endpoint.obj.hom :=
  Over.w r.projection.hom

end Run
end
end Hironaka.Analytic.Unibranch.OriginalNativeHSOuterHistory
