import Hironaka.Resolution.HironakaG3AmbientStepComparison

/-! Ambient comparison of two actual lifts of the same lower finite history. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3AmbientHistoryComparison
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  SubmanifoldChartedSpace HironakaDisjointFiniteControlledHistory
  HironakaG3ControlledHistorySubsetTransport
  HironakaActualClosedContactBlowupRestriction MarkedIdealBiholomorphism
  HironakaG3AmbientStepComparison

open BlowupTowerIsomorphism

theorem exists_ambient_comparison_of_same_lower_history
    {d t : ℕ} {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d}
    {Y₁ : CMfd.{0} (d+t)} {N : Set X} {B : List (Set X)}
    {J : GermIdeal (d+t) X} {ι : P → X} {M : MarkedIdeal d P}
    {T : BlowupTower P Q} {U₁ : BlowupTower X Y₁} {η₁ : Q → Y₁}
    (h₁ : CoupledHistory N B J ι M T U₁ η₁) :
    ∀ {Y₂ : CMfd.{0} (d+t)} {U₂ : BlowupTower X Y₂} {η₂ : Q → Y₂},
      CoupledHistory N B J ι M T U₂ η₂ →
      ∃ χ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ Y₂,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel (d+t)) X ∞) U₁ U₂ χ ∧
        ∀ q, χ (η₁ q) = η₂ q := by
  induction h₁ with
  | refl h =>
    intro Y₂ U₂ η₂ h₂
    cases h₂ with
    | refl h₂ =>
      refine ⟨Diffeomorph.refl 𝓘(ℂ,ComplexModel (d+t)) X ∞, IsTowerIso.refl, ?_⟩
      intro q
      rfl
  | @step Q₁ R₁ Y₁ Z₁ T₁ U₁ η₁ η₁new C C₁ ρ π₁ hρ hπ₁ hprev hCentre hSq hEnd ih =>
    intro Y₂ U₂ η₂ h₂
    cases h₂ with
    | @step Q₂ R₂ Y₂ Z₂ T₂ U₂ η₂old η₂new C₂ C₂old ρ₂ π₂ hρ₂ hπ₂ hprev₂ hCentre₂ hSq₂ hEnd₂ =>
      obtain ⟨β,hβiso,hβη⟩ := ih hprev₂
      obtain ⟨_hc, hr, _hI, _hN, _hSNC, _hTr, F, hF, _hProj, _hIdeal, _hBoundary⟩ :=
        endpoint_of_coupledHistory hprev
      let := chartedSpace (Nat.le_add_right d t) hr
      let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
      have hF₂ : (fun q => β (F q).val) = η₂old := by
        funext q
        rw [congrFun hF q, hβη]
      have hπ₁' : IsBlowupAlong (d+t) ((fun q => (F q).val) '' C) π₁ := by
        rw [hF, ← hCentre]
        exact hπ₁
      have hπ₂' : IsBlowupAlong (d+t) ((fun q => β (F q).val) '' C) π₂ := by
        rw [hF₂, ← hCentre₂]
        exact hπ₂
      have hSq₁' : π₁ ∘ η₁new = (fun q => (F q).val) ∘ ρ := by
        rw [hF]
        exact hSq
      have hSq₂' : π₂ ∘ η₂ = (fun q => β (F q).val) ∘ ρ := by
        rw [hF₂]
        exact hSq₂
      obtain ⟨_hc₁, hr₁, _hI₁, _hN₁, _hSNC₁, _hTr₁, F₁, hF₁, _hP₁, _hId₁, _hB₁⟩ := hEnd
      obtain ⟨_hc₂, hr₂, _hI₂, _hN₂, _hSNC₂, _hTr₂, F₂, hF₂new, _hP₂, _hId₂, _hB₂⟩ := hEnd₂
      let := chartedSpace (Nat.le_add_right d t) hr₁
      let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr₁
      let := chartedSpace (Nat.le_add_right d t) hr₂
      let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr₂
      have hη₁new : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ η₁new := by
        rw [← hF₁]
        exact (contMDiff_val (Nat.le_add_right d t) hr₁).comp F₁.contMDiff
      have hη₂new : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ η₂ := by
        rw [← hF₂new]
        exact (contMDiff_val (Nat.le_add_right d t) hr₂).comp F₂.contMDiff
      obtain ⟨χ,hχ,hχη⟩ := exists_comparison_of_same_lower_step hr F β C ρ hρ
        π₁ π₂ hπ₁' hπ₂' η₁new η₂ hη₁new hη₂new hSq₁' hSq₂'
      have hCiso : β ⁻¹' C₂old = C₁ := by
        rw [hCentre, hCentre₂]
        ext y
        constructor
        · rintro ⟨q, hq, heq⟩
          exact ⟨q, hq, β.injective ((hβη q).trans heq)⟩
        · rintro ⟨q, hq, rfl⟩
          exact ⟨q, hq, (hβη q).symm⟩
      exact ⟨χ, IsTowerIso.step hβiso hπ₁ hπ₂ χ hχ hCiso, hχη⟩

end
end Hironaka.HironakaG3AmbientHistoryComparison
