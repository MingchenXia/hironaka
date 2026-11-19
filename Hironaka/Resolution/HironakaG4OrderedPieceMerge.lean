import Hironaka.Resolution.HironakaG4SupportedPieceComparison
import Hironaka.Resolution.HironakaG8DisjointPhaseMerge
import Hironaka.Resolution.HironakaG3ClosedFootprintTransportedTower
import Hironaka.Resolution.HironakaOriginalOldBranchEmptyProjection
import Hironaka.Resolution.HironakaG3AppendEmptyTailComparison

/-! Actual disjoint-piece merges with a prescribed chronological order. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
universe u v

namespace Hironaka.HironakaG4OrderedPieceMerge

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  BlowupTowerIsoTail RestrictEmptyTower G3UniverseEmptyAwareCore G3UniverseEmptyAwareOpenRestriction
  HironakaSharpActualCurveComparisonRestriction HironakaG3CentresOverGenericFactor
  HironakaActualProcessedAllMasksDrop MarkedIdealTowerTransport
  HironakaG4SupportedPieceComparison HironakaG8DisjointPhaseMerge HironakaG3ClosedFootprintTransportedTower
  HironakaOriginalOldBranchEmptyProjection HironakaG3AppendEmptyTailComparison

/-- A real tail over the new piece and its physical identification on the
piece window. The base map is the actual previous projection there. -/
structure PiecePhase {n : ℕ} {X A Y Z : CMfd.{u} n} (F : Set X) (V : Opens X)
    (S : BlowupTower X Y) (P : BlowupTower X A) (Q : BlowupTower A Z) : Prop where
  footprint : CentresOver (P.proj ⁻¹' F) Q
  compare :
    ∃ β : (CMfd.of (n := n) (openPreimage P V)) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (CMfd.of (n := n) V),
      (∀ y, β y = (restrict V P).proj y) ∧
      ∃ ψ : (CMfd.of (n := n) (openPreimage Q (openPreimage P V))) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
          (CMfd.of (n := n) (openPreimage S V)),
        IsTowerIso β (restrict (openPreimage P V) Q) (restrict V S) ψ

/-- Each stored merge step extends the earlier prefix by one labelled
supported piece. The labels are stored newest first. -/
inductive OrderedPieceMerge {n : ℕ} {X : CMfd.{u} n} {ι : Type v}
    (F : ι → Set X) (V : ι → Opens X) (Y : ι → CMfd.{u} n) (S : ∀ i, BlowupTower X (Y i)) :
    List ι → {Z : CMfd.{u} n} → BlowupTower X Z → Prop
  | nil : OrderedPieceMerge F V Y S [] (.refl : BlowupTower X X)
  | snoc {ls : List ι} {i : ι} {A B Z : CMfd.{u} n} {P : BlowupTower X A}
      {Q : BlowupTower A B} {T : BlowupTower X Z}
      {η : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ B}
      (previous : OrderedPieceMerge F V Y S ls P) (phase : PiecePhase (F i) (V i) (S i) P Q)
      (iso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) T (P.append Q) η) :
      OrderedPieceMerge F V Y S (i :: ls) T

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Compare two physical piece tails over an already compared prefix, using
the supplied comparisons on the corresponding isolating opens. -/
theorem piecePhase_emptyAware {n : ℕ} {X₁ X₂ A₁ A₂ Y₁ Y₂ Z₁ Z₂ : CMfd.{u} n}
    (e : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂) {V : Opens X₂} {F : Set X₂}
    (hFV : F ⊆ V) {P₁ : BlowupTower X₁ A₁} {P₂ : BlowupTower X₂ A₂}
    {β : A₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A₂}
    (hP : EmptyAwareTowerIso e P₁ P₂ β)
    {S₁ : BlowupTower X₁ Y₁} {S₂ : BlowupTower X₂ Y₂}
    {ψ : (CMfd.of (n := n) (openPreimage S₁ (preimageOpen e V))) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      (CMfd.of (n := n) (openPreimage S₂ V))}
    (hS : EmptyAwareTowerIso (openRestriction e (preimageOpen e V) V rfl)
      (restrict (preimageOpen e V) S₁) (restrict V S₂) ψ)
    {Q₁ : BlowupTower A₁ Z₁} {Q₂ : BlowupTower A₂ Z₂}
    (h₁ : PiecePhase (e ⁻¹' F) (preimageOpen e V) S₁ P₁ Q₁)
    (h₂ : PiecePhase F V S₂ P₂ Q₂) :
    ∃ χ : Z₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z₂, EmptyAwareTowerIso β Q₁ Q₂ χ := by
  let V₁ := preimageOpen e V
  let B₁ := openPreimage P₁ V₁
  let B₂ := openPreimage P₂ V
  let τ := openRestriction e V₁ V rfl
  have hB : (B₁ : Set A₁) = β ⁻¹' (B₂ : Set A₂) := emptyAware_openPreimage_eq hP V
  let β₀ := openRestriction β B₁ B₂ hB
  obtain ⟨a₁, ha₁, η₁, hη₁⟩ := h₁.compare
  obtain ⟨a₂, ha₂, η₂, hη₂⟩ := h₂.compare
  have hMap : a₁.trans (τ.trans a₂.symm) = β₀ := by
    apply Diffeomorph.ext
    intro y
    apply a₂.injective
    have hp := (emptyAware_proj_comm (emptyAware_open_restriction hP V) y).symm
    change τ ((restrict V₁ P₁).proj y) = (restrict V P₂).proj (β₀ y) at hp
    change a₂ (a₂.symm (τ (a₁ y))) = a₂ (β₀ y)
    rw [a₂.apply_symm_apply, ha₁ y, ha₂ (β₀ y)]
    exact hp
  have hLocal := G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso hη₁)
    (G3UniverseEmptyAwareCore.trans hS (emptyAware_of_isTowerIso hη₂.symm))
  change EmptyAwareTowerIso (a₁.trans (τ.trans a₂.symm)) (restrict B₁ Q₁) (restrict B₂ Q₂) _ at hLocal
  rw [hMap] at hLocal
  have hF : P₁.proj ⁻¹' (e ⁻¹' F) = β ⁻¹' (P₂.proj ⁻¹' F) := by
    ext z
    change e (P₁.proj z) ∈ F ↔ P₂.proj (β z) ∈ F
    rw [emptyAware_proj_comm hP z]
  have hOver := h₁.footprint
  rw [hF] at hOver
  exact emptyAware_extends_of_matching_open β B₁ B₂ hB (P₂.proj ⁻¹' F)
    (fun _ hz => hFV hz) Q₁ Q₂ hOver h₂.footprint hLocal

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Corresponding piece comparisons give a comparison of the complete
actual mergers when the same list orders both histories. -/
theorem orderedPieceMerge_emptyAware {n : ℕ} {X₁ X₂ Z₁ Z₂ : CMfd.{u} n} {ι : Type v}
    (e : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (F : ι → Set X₂) (V : ι → Opens X₂) (hFV : ∀ i, F i ⊆ V i)
    {Y₁ : ι → CMfd.{u} n} {Y₂ : ι → CMfd.{u} n}
    {S₁ : ∀ i, BlowupTower X₁ (Y₁ i)} {S₂ : ∀ i, BlowupTower X₂ (Y₂ i)}
    (hPiece : ∀ i, ∃ ψ : (CMfd.of (n := n) (openPreimage (S₁ i) (preimageOpen e (V i))))
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
          (CMfd.of (n := n) (openPreimage (S₂ i) (V i))),
        EmptyAwareTowerIso (openRestriction e (preimageOpen e (V i)) (V i) rfl)
          (restrict (preimageOpen e (V i)) (S₁ i)) (restrict (V i) (S₂ i)) ψ)
    {ls : List ι} {T₁ : BlowupTower X₁ Z₁} {T₂ : BlowupTower X₂ Z₂}
    (h₁ : OrderedPieceMerge (fun i => e ⁻¹' F i) (fun i => preimageOpen e (V i)) Y₁ S₁ ls T₁)
    (h₂ : OrderedPieceMerge F V Y₂ S₂ ls T₂) :
    ∃ ψ : Z₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z₂, EmptyAwareTowerIso e T₁ T₂ ψ := by
  induction h₂ generalizing Z₁ with
  | nil =>
    cases h₁
    exact ⟨e, .refl⟩
  | @snoc ls i A₂ B₂ Z₂ P₂ Q₂ T₂ η₂ hP₂ hQ₂ hIso₂ ih =>
    cases h₁ with
    | @snoc _ _ A₁ B₁ _ P₁ Q₁ _ η₁ hP₁ hQ₁ hIso₁ =>
      obtain ⟨β, hβ⟩ := ih hP₁
      obtain ⟨ψ, hψ⟩ := hPiece i
      obtain ⟨χ, hχ⟩ := piecePhase_emptyAware e (hFV i) hβ hψ hQ₁ hQ₂
      refine ⟨η₁.trans (χ.trans η₂.symm), ?_⟩
      simpa only [Diffeomorph.symm_refl, Diffeomorph.refl_trans, Diffeomorph.trans_refl] using
        G3UniverseEmptyAwareCore.trans (emptyAware_of_isTowerIso hIso₁)
          (G3UniverseEmptyAwareCore.trans (emptyAware_append hβ hχ) (emptyAware_of_isTowerIso hIso₂.symm))

theorem orderedPieceMerge_centresOver {n : ℕ} {X Z : CMfd.{u} n} {ι : Type v}
    {F : ι → Set X} {V : ι → Opens X} {Y : ι → CMfd.{u} n} {S : ∀ i, BlowupTower X (Y i)}
    {ls : List ι} {T : BlowupTower X Z} (h : OrderedPieceMerge F V Y S ls T) :
    CentresOver (⋃ i ∈ ls, F i) T := by
  induction h with
  | nil => trivial
  | @snoc ls i A B Z P Q T η previous phase iso ih =>
    have hEq : (⋃ j ∈ i :: ls, F j) = (⋃ j ∈ ls, F j) ∪ F i := by
      ext x
      simp only [List.mem_cons, mem_iUnion, mem_union]
      constructor
      · rintro ⟨j, (rfl | hj), hx⟩
        · exact Or.inr hx
        · exact Or.inl ⟨j, hj, hx⟩
      · rintro (⟨j, hj, hx⟩ | hx)
        · exact ⟨j, Or.inr hj, hx⟩
        · exact ⟨i, Or.inl rfl, hx⟩
    rw [hEq]
    have hOver : CentresOver ((⋃ j ∈ ls, F j) ∪ F i) (P.append Q) :=
      (centresOver_append_iff _ P Q).mpr
        ⟨centresOver_mono_local subset_union_left P ih,
          centresOver_mono_local (preimage_mono subset_union_right) Q phase.footprint⟩
    simpa only [Diffeomorph.coe_refl, preimage_id] using centresOver_of_isTowerIso iso _ hOver

end
end Hironaka.HironakaG4OrderedPieceMerge
