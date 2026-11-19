import Hironaka.Resolution.HironakaG3AmbientHistoryComparison
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3AmbientIsomorphicHistory
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaG3ControlledHistorySubsetTransport
  HironakaActualClosedContactBlowupRestriction MarkedIdealBiholomorphism
  HironakaG3AmbientStepComparison BlowupTowerIsomorphism

/-- Isomorphic intrinsic histories have isomorphic ambient lifts, preserving the actual lower embeddings. -/
theorem exists_ambient_comparison_of_isomorphic_lower_histories
    {d t : ℕ} {X : CMfd.{0} (d+t)} {P₁ P₂ Q₁ Q₂ : CMfd.{0} d}
    (Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂)
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (hT : IsTowerIso Φ T₁ T₂ ψ) :
    ∀ {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
      {ι₁ : P₁ → X} {ι₂ : P₂ → X} {M₁ : MarkedIdeal d P₁} {M₂ : MarkedIdeal d P₂}
      {Y₁ Y₂ : CMfd.{0} (d+t)} {U₁ : BlowupTower X Y₁} {U₂ : BlowupTower X Y₂}
      {η₁ : Q₁ → Y₁} {η₂ : Q₂ → Y₂},
      (∀ p, ι₂ (Φ p) = ι₁ p) →
      CoupledHistory N B J ι₁ M₁ T₁ U₁ η₁ → CoupledHistory N B J ι₂ M₂ T₂ U₂ η₂ →
      ∃ β : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ Y₂,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel (d+t)) X ∞) U₁ U₂ β ∧
        ∀ q, β (η₁ q) = η₂ (ψ q) := by
  induction hT with
  | refl =>
    intro N B J ι₁ ι₂ M₁ M₂ Y₁ Y₂ U₁ U₂ η₁ η₂ hι h₁ h₂
    cases h₁ with
    | refl h₁ =>
      cases h₂ with
      | refl h₂ =>
        refine ⟨Diffeomorph.refl 𝓘(ℂ,ComplexModel (d+t)) X ∞, IsTowerIso.refl, ?_⟩
        intro q
        exact (hι q).symm
  | @step Q₁ Q₂ R₁ R₂ T₁ T₂ ψold hPrev C₁ ρ₁ hρ₁ C₂ ρ₂ hρ₂ ψnew hComm hCentre ih =>
    intro N B J ι₁ ι₂ M₁ M₂ Z₁ Z₂ U₁ U₂ η₁ η₂ hι h₁ h₂
    cases h₁ with
    | @step _ _ Y₁ _ _ U₁old η₁old _ _ C₁amb _ π₁amb _ hπ₁amb hprev₁ hC₁ hSq₁ hEnd₁ =>
      cases h₂ with
      | @step _ _ Y₂ _ _ U₂old η₂old _ _ C₂amb _ π₂amb _ hπ₂amb hprev₂ hC₂ hSq₂ hEnd₂ =>
        obtain ⟨β,hβiso,hβη⟩ := ih hι hprev₁ hprev₂
        obtain ⟨_hc, hr, _hI, _hN, _hSNC, _hTr, F, hF, _hProj, _hIdeal, _hBoundary⟩ :=
          endpoint_of_coupledHistory hprev₁
        let := chartedSpace (Nat.le_add_right d t) hr
        let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
        have hF₂ : (fun q => β (F q).val) = η₂old ∘ ψold := by
          funext q
          change β (F q).val = η₂old (ψold q)
          rw [congrFun hF q, hβη]
        have hCimage : ψold '' C₁ = C₂ := by
          ext q
          constructor
          · rintro ⟨p,hp,rfl⟩
            have : p ∈ ψold ⁻¹' C₂ := by rw [hCentre]; exact hp
            exact this
          · intro hq
            refine ⟨ψold.symm q, ?_, ψold.apply_symm_apply q⟩
            rw [← hCentre]
            change ψold (ψold.symm q) ∈ C₂
            rw [ψold.apply_symm_apply]
            exact hq
        have hImage : (fun q => β (F q).val) '' C₁ = η₂old '' C₂ := by
          rw [hF₂]
          change (fun q => η₂old (ψold q)) '' C₁ = η₂old '' C₂
          simpa only [image_image] using congrArg (fun A => η₂old '' A) hCimage
        have hπ₁' : IsBlowupAlong (d+t) ((fun q => (F q).val) '' C₁) π₁amb := by
          rw [hF, ← hC₁]
          exact hπ₁amb
        have hπ₂' : IsBlowupAlong (d+t) ((fun q => β (F q).val) '' C₁) π₂amb := by
          rw [hImage, ← hC₂]
          exact hπ₂amb
        have hSq₁' : π₁amb ∘ η₁ = (fun q => (F q).val) ∘ ρ₁ := by
          rw [hF]
          exact hSq₁
        have hSq₂' : π₂amb ∘ (η₂ ∘ ψnew) = (fun q => β (F q).val) ∘ ρ₁ := by
          funext q
          have h := congrFun hSq₂ (ψnew q)
          change π₂amb (η₂ (ψnew q)) = η₂old (ρ₂ (ψnew q)) at h
          rw [hComm q] at h
          have hF₂q : β (F (ρ₁ q)).val = η₂old (ψold (ρ₁ q)) := congrFun hF₂ (ρ₁ q)
          exact h.trans hF₂q.symm
        obtain ⟨_hc₁, hr₁, _hI₁, _hN₁, _hSNC₁, _hTr₁, F₁, hF₁, _hP₁, _hId₁, _hB₁⟩ := hEnd₁
        obtain ⟨_hc₂, hr₂, _hI₂, _hN₂, _hSNC₂, _hTr₂, F₂, hF₂new, _hP₂, _hId₂, _hB₂⟩ := hEnd₂
        let := chartedSpace (Nat.le_add_right d t) hr₁
        let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr₁
        let := chartedSpace (Nat.le_add_right d t) hr₂
        let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr₂
        have hη₁ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ η₁ := by
          rw [← hF₁]
          exact (contMDiff_val (Nat.le_add_right d t) hr₁).comp F₁.contMDiff
        have hη₂ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ η₂ := by
          rw [← hF₂new]
          exact (contMDiff_val (Nat.le_add_right d t) hr₂).comp F₂.contMDiff
        obtain ⟨χ,hχ,hχη⟩ := exists_comparison_of_same_lower_step hr F β C₁ ρ₁ hρ₁
          π₁amb π₂amb hπ₁' hπ₂' η₁ (η₂ ∘ ψnew) hη₁ (hη₂.comp ψnew.contMDiff) hSq₁' hSq₂'
        have hCiso : β ⁻¹' C₂amb = C₁amb := by
          rw [hC₁,hC₂,← hImage]
          ext y
          constructor
          · rintro ⟨q,hq,heq⟩
            exact ⟨q,hq,(congrFun hF q).symm.trans (β.injective heq)⟩
          · rintro ⟨q,hq,rfl⟩
            exact ⟨q,hq,congrArg β (congrFun hF q)⟩
        exact ⟨χ, IsTowerIso.step hβiso hπ₁amb hπ₂amb χ hχ hCiso, hχη⟩

end
end Hironaka.HironakaG3AmbientIsomorphicHistory
