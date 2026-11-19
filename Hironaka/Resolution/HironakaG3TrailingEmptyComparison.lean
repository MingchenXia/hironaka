import Hironaka.Resolution.HironakaG3AmbientIsomorphicHistory
import Hironaka.Resolution.HironakaNormalCrossingsOpenRestrictionSeparation

/-! Comparison after one genuine final empty intrinsic and ambient blowup. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3TrailingEmptyComparison
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaG3ControlledHistorySubsetTransport
  HironakaG3AmbientHistoryComparison BlowupTowerIsomorphism

/-- One final empty step may be removed when comparing ambient endpoints:
the produced biholomorphism commutes with the original projection and
identifies the actual lower endpoint embeddings through the empty blowup. -/
theorem exists_comparison_after_one_trailing_empty_step
    {d t : ℕ} {X : CMfd.{0} (d+t)} {P Q R : CMfd.{0} d}
    {Y Z Y₂ : CMfd.{0} (d+t)} {N : Set X} {B : List (Set X)}
    {J : GermIdeal (d+t) X} {ι : P → X} {M : MarkedIdeal d P}
    {T : BlowupTower P Q} {U : BlowupTower X Y} {U₂ : BlowupTower X Y₂}
    {ρ : R → Q} (hρ : IsBlowupAlong d (∅ : Set Q) ρ)
    {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong (d+t) C π)
    {η' : R → Z} {η₂ : Q → Y₂}
    (hStep : CoupledHistory N B J ι M (.step T ∅ ρ hρ) (.step U C π hπ) η')
    (hOther : CoupledHistory N B J ι M T U₂ η₂) :
    ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ Y₂,
      (∀ z, U₂.proj (e z) = (U.step C π hπ).proj z) ∧
      (∀ r, e (η' r) = η₂ (ρ r)) := by
  cases hStep with
  | step hPrev hCentre hSq _hEnd =>
    have hC : C = ∅ := by simpa only [image_empty] using hCentre
    have hπempty : IsBlowupAlong (d+t) (∅ : Set Y) π := by rw [← hC]; exact hπ
    obtain ⟨β,hIso,hβη⟩ := exists_ambient_comparison_of_same_lower_history hPrev hOther
    obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπempty
    let e := φ.trans β
    refine ⟨e,?_,?_⟩
    · intro z
      have h := hIso.proj_comm (φ z)
      change U.proj (φ z) = U₂.proj (β (φ z)) at h
      change U₂.proj (β (φ z)) = U.proj (π z)
      simpa only [hφ z] using h.symm
    · intro r
      have hs := congrFun hSq r
      change π (η' r) = _ at hs
      change β (φ (η' r)) = η₂ (ρ r)
      rw [hφ, hs]
      exact hβη (ρ r)

end
end Hironaka.HironakaG3TrailingEmptyComparison
