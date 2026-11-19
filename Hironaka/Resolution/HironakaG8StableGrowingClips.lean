import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Resolution.HironakaActualLocallyFiniteBoundary
import Hironaka.Resolution.HironakaG8EmptyStageOverlapComparisons
import Hironaka.Resolution.HironakaActualLocallyFiniteHistoryComparison

/-! Strict comparison of protected finite cuts of one growing history. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8StableGrowingClips

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail ResolutionInvariantSeq
  HironakaLocallyFiniteResolutionSequence ResolutionInvariantExt RestrictEmptyTower
  HironakaG8EmptyStageOverlapComparisons HironakaSharpActualCurveEmptyPadding

variable {n : ℕ} {X : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- The literal protected prefix, padded in the original clock, compares
strictly to the actual later stage. -/
theorem exists_strict_protected_prefix_extension (s : GrowingSeq X) (O : Opens X)
    (N r : ℕ)
    (hAvoid : ∀ k, N ≤ k → Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (O : Set X))) :
    ∃ e : CMfd.of (n := n) (openPreimage (s.stage N).2 O)
        ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage (s.stage (N+r)).2 O),
      IsTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) O) ∞)
        ((restrict O (s.stage N).2).append
          (identityEmptyTail (CMfd.of (n := n) (openPreimage (s.stage N).2 O)) r))
        (restrict O (s.stage (N+r)).2) e := by
  have hLen : (tailTower s N r).length = r := by
    induction r with
    | zero => rfl
    | succ r ih => simpa only [tailTower, BlowupTower.length_step] using congrArg Nat.succ ih
  let A := CMfd.of (n := n) (openPreimage (s.stage N).2 O)
  let S := restrict (openPreimage (s.stage N).2 O) (tailTower s N r)
  have hEmpty : IsEmptyTower S :=
    (isEmptyTower_restrict_iff _ _).mpr (centresAvoid_tailTower s N O hAvoid r)
  obtain ⟨e,he⟩ := strict_comparison_of_empty_towers (Diffeomorph.refl 𝓘c A ∞)
    (identityEmptyTail A r) S (identityEmptyTail_isEmptyTower A r) hEmpty
    (by simpa only [S, identityEmptyTail_length, length_restrict] using hLen.symm)
  have hHead := (IsTowerIso.refl_self (restrict O (s.stage N).2)).append he
  have hSplit := isTowerIso_restrict_append O (s.stage N).2 (tailTower s N r)
  let P (T : BlowupTower X (s.stage (N+r)).1) : Prop :=
    ∃ e : A ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage T O),
      IsTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) O) ∞)
        ((restrict O (s.stage N).2).append (identityEmptyTail A r)) (restrict O T) e
  have hP : P ((s.stage N).2.append (tailTower s N r)) :=
    ⟨_, BlowupTowerSplitIso.IsTowerIso.congr_base (hHead.trans hSplit.symm) (fun _ => rfl)⟩
  exact (congrArg P (append_tailTower s N r)).mp hP

/-- Two cuts of the SAME protected original history compare strictly after
padding only to their prescribed common original clock. -/
theorem exists_strict_stable_prefix_comparison (s : GrowingSeq X) (O : Opens X)
    (N J L : ℕ)
    (hN : ∀ k, N ≤ k → Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (O : Set X)))
    (hJ : ∀ k, J ≤ k → Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (O : Set X)))
    (hNL : N ≤ L) (hJL : J ≤ L) :
    ∃ e : CMfd.of (n := n) (openPreimage (s.stage N).2 O)
        ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage (s.stage J).2 O),
      IsTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) O) ∞)
        ((restrict O (s.stage N).2).append
          (identityEmptyTail (CMfd.of (n := n) (openPreimage (s.stage N).2 O)) (L-N)))
        ((restrict O (s.stage J).2).append
          (identityEmptyTail (CMfd.of (n := n) (openPreimage (s.stage J).2 O)) (L-J))) e := by
  have hN' := exists_strict_protected_prefix_extension s O N (L-N) hN
  have hJ' := exists_strict_protected_prefix_extension s O J (L-J) hJ
  have hEqN : N + (L-N) = L := by omega
  have hEqJ : J + (L-J) = L := by omega
  rw [hEqN] at hN'
  rw [hEqJ] at hJ'
  obtain ⟨eN,heN⟩ := hN'
  obtain ⟨eJ,heJ⟩ := hJ'
  exact ⟨_, BlowupTowerSplitIso.IsTowerIso.congr_base (heN.trans heJ.symm) (fun _ => rfl)⟩

end Hironaka.HironakaG8StableGrowingClips
