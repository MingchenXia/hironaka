import Hironaka.Resolution.HironakaG4OrderedPieceMerge
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareOpenRestriction
import Hironaka.Resolution.HironakaG3UniverseLiftRestrict

/-! Literal restriction retains the ordered disjoint-piece certificate. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
universe u v

namespace Hironaka.HironakaG4OrderedPieceRestriction

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  BlowupTowerIsoTail RestrictEmptyTower G3UniverseEmptyAwareCore MaxLocusLocal
  HironakaSharpActualCurveComparisonRestriction HironakaG3CentresOverGenericFactor
  HironakaG4OrderedPieceMerge

private theorem nested_restrict_isTowerIso {n : ℕ} {X Y : CMfd.{u} n}
    (O : Opens X) (H : Opens O) (I : Opens X) (hIO : I ≤ O)
    (hH : ∀ z : O, z ∈ H ↔ z.val ∈ I) (T : BlowupTower X Y) :
    ∃ η : (CMfd.of (n := n) (openPreimage (restrict O T) H)) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      (CMfd.of (n := n) (openPreimage T I)),
      IsTowerIso (nestedDiffeo O H I hH hIO) (restrict H (restrict O T)) (restrict I T) η := by
  have heq : H = nestedOpens O I := by ext z; exact hH z
  subst H
  refine ⟨_, BlowupTowerSplitIso.IsTowerIso.congr_base (isTowerIso_restrict_nestedOpens hIO T) ?_⟩
  intro z
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- The piece certificate survives literal restriction of the prefix,
piece chart, and physical appended tail. -/
theorem piecePhase_restrict {n : ℕ} {X A Y Z : CMfd.{u} n} {F : Set X} {V : Opens X}
    {S : BlowupTower X Y} {P : BlowupTower X A} {Q : BlowupTower A Z}
    (h : PiecePhase F V S P Q) (O : Opens X) :
    PiecePhase ((Subtype.val : O → X) ⁻¹' F) (nestedOpens O V) (restrict O S)
      (restrict O P) (restrict (openPreimage P O) Q) := by
  let I := O ⊓ V
  let U := nestedOpens O V
  let V₀ := nestedOpens V I
  let B := openPreimage P O
  let C := openPreimage P V
  let J := openPreimage P I
  let L := openPreimage (restrict O P) U
  have hIB : J ≤ B := openPreimage_mono P inf_le_left
  have hIC : J ≤ C := openPreimage_mono P inf_le_right
  have hU (z : O) : z ∈ U ↔ z.val ∈ I :=
    ⟨fun hz => ⟨z.property, hz⟩, And.right⟩
  have hL (z : B) : z ∈ L ↔ z.val ∈ J := by
    change ((restrict O P).proj z).val ∈ V ↔ P.proj z.val ∈ I
    rw [proj_restrict]
    exact ⟨fun hz => ⟨z.property, hz⟩, And.right⟩
  obtain ⟨β, hβ, χ, hχ⟩ := h.compare
  let C₀ := preimageOpen β V₀
  have hC (z : C) : z ∈ C₀ ↔ z.val ∈ J := by
    change (β z).val ∈ I ↔ P.proj z.val ∈ I
    rw [hβ, proj_restrict]
  let b := nestedDiffeo (n := n) B L J hL hIB
  let c := nestedDiffeo (n := n) C C₀ J hC hIC
  let a := nestedDiffeo (n := n) O U I hU inf_le_left
  let v := nestedOpensDiffeo (n := n) (show I ≤ V from inf_le_right)
  let β₀ := openRestriction β C₀ V₀ rfl
  let α := ((b.trans c.symm).trans β₀).trans (v.trans a.symm)
  have hFO : (restrict O P).proj ⁻¹' ((Subtype.val : O → X) ⁻¹' F) =
      (Subtype.val : B → A) ⁻¹' (P.proj ⁻¹' F) := by
    ext z
    change ((restrict O P).proj z).val ∈ F ↔ P.proj z.val ∈ F
    rw [proj_restrict]
  have hOver := centresOver_restrict B (P.proj ⁻¹' F) Q h.footprint
  refine ⟨hFO.symm ▸ hOver, α, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    change (β (c.symm (b z))).val = (((restrict U (restrict O P)).proj z).val).val
    rw [hβ, proj_restrict V P]
    rw [proj_restrict U (restrict O P), proj_restrict O P]
    rfl
  · obtain ⟨η₁, hη₁⟩ := nested_restrict_isTowerIso B L J hIB hL Q
    obtain ⟨η₂, hη₂⟩ := nested_restrict_isTowerIso C C₀ J hIC hC Q
    obtain ⟨η₃, hη₃⟩ := nested_restrict_isTowerIso O U I inf_le_left hU S
    have hη₄ := isTowerIso_restrict_nestedOpens (show I ≤ V from inf_le_right) S
    have hχ₀ := IsTowerIso.open_restriction hχ V₀
    exact ⟨_, ((hη₁.trans hη₂.symm).trans hχ₀).trans (hη₄.trans hη₃.symm)⟩

theorem orderedPieceMerge_restrict {n : ℕ} {X Z : CMfd.{u} n} {ι : Type v}
    {F : ι → Set X} {V : ι → Opens X} {Y : ι → CMfd.{u} n} {S : ∀ i, BlowupTower X (Y i)}
    {ls : List ι} {T : BlowupTower X Z} (h : OrderedPieceMerge F V Y S ls T) (O : Opens X) :
    OrderedPieceMerge (fun i => (Subtype.val : O → X) ⁻¹' F i) (fun i => nestedOpens O (V i))
      (fun i => CMfd.of (n := n) (openPreimage (S i) O)) (fun i => restrict O (S i))
      ls (restrict O T) := by
  induction h with
  | nil => exact .nil
  | @snoc ls i A B Z P Q T η previous phase iso ih =>
    have hIso := (IsTowerIso.open_restriction iso O).trans (isTowerIso_restrict_append O P Q)
    have hOut := BlowupTowerSplitIso.IsTowerIso.congr_base hIso
      (Φ' := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) O ∞) fun _ => rfl
    exact .snoc ih (piecePhase_restrict phase O) hOut

end
end Hironaka.HironakaG4OrderedPieceRestriction
