import Hironaka.Resolution.HironakaG3EmptySuffixComparison

/-! Comparison of coupled lifts under matched and inserted empty stages. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3EmptyAwareHistory
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaG3ControlledHistorySubsetTransport
  HironakaActualClosedContactBlowupRestriction MarkedIdealBiholomorphism
  HironakaG3AmbientStepComparison BlowupTowerIsomorphism

/-- Physical matching steps plus either-side empty insertions. -/
inductive EmptyAwareTowerIso {d : ℕ} {P₁ P₂ : CMfd.{u} d}
    (Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂) :
    {Q₁ Q₂ : CMfd.{u} d} → BlowupTower P₁ Q₁ → BlowupTower P₂ Q₂ →
      (Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂) → Prop
  | refl : EmptyAwareTowerIso Φ .refl .refl Φ
  | step {Q₁ Q₂ R₁ R₂ : CMfd.{u} d} {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
      {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
      (h : EmptyAwareTowerIso Φ T₁ T₂ ψ)
      {C₁ : Set Q₁} {ρ₁ : R₁ → Q₁} (hρ₁ : IsBlowupAlong d C₁ ρ₁)
      {C₂ : Set Q₂} {ρ₂ : R₂ → Q₂} (hρ₂ : IsBlowupAlong d C₂ ρ₂)
      (ψnew : R₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ R₂)
      (hComm : ∀ p, ρ₂ (ψnew p) = ψ (ρ₁ p)) (hCentre : ψ ⁻¹' C₂ = C₁) :
      EmptyAwareTowerIso Φ (.step T₁ C₁ ρ₁ hρ₁) (.step T₂ C₂ ρ₂ hρ₂) ψnew
  | leftEmpty {Q₁ Q₂ R₁ : CMfd.{u} d} {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
      {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
      (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) {ρ : R₁ → Q₁}
      (hρ : IsBlowupAlong d (∅ : Set Q₁) ρ)
      (φ : R₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₁) (hφ : ∀ z, φ z = ρ z) :
      EmptyAwareTowerIso Φ (.step T₁ ∅ ρ hρ) T₂ (φ.trans ψ)
  | rightEmpty {Q₁ Q₂ R₂ : CMfd.{u} d} {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
      {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
      (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) {ρ : R₂ → Q₂}
      (hρ : IsBlowupAlong d (∅ : Set Q₂) ρ)
      (φ : R₂ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂) (hφ : ∀ z, φ z = ρ z) :
      EmptyAwareTowerIso Φ T₁ (.step T₂ ∅ ρ hρ) (ψ.trans φ.symm)

/-- Every physical isomorphism of towers is an empty-aware comparison. -/
theorem emptyAware_of_isTowerIso {d : ℕ} {P₁ P₂ Q₁ Q₂ : CMfd.{u} d}
    {Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂}
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (h : IsTowerIso Φ T₁ T₂ ψ) : EmptyAwareTowerIso Φ T₁ T₂ ψ := by
  induction h with
  | refl => exact .refl
  | step h hρ₁ hρ₂ ψnew hComm hCentre ih =>
    exact .step ih hρ₁ hρ₂ ψnew hComm hCentre

/-- Empty-aware comparisons commute with the original-base projections. -/
theorem emptyAware_proj_comm {d : ℕ} {P₁ P₂ Q₁ Q₂ : CMfd.{u} d}
    {Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂}
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) : ∀ q, T₂.proj (ψ q) = Φ (T₁.proj q) := by
  induction h with
  | refl => intro q; rfl
  | @step Q₁ Q₂ R₁ R₂ T₁ T₂ ψ h C₁ ρ₁ hρ₁ C₂ ρ₂ hρ₂ ψnew hComm hCentre ih =>
    intro q
    change T₂.proj (ρ₂ (ψnew q)) = Φ (T₁.proj (ρ₁ q))
    rw [hComm q]
    exact ih (ρ₁ q)
  | @leftEmpty Q₁ Q₂ R₁ T₁ T₂ ψ h ρ hρ φ hφ ih =>
    intro q
    change T₂.proj (ψ (φ q)) = Φ (T₁.proj (ρ q))
    rw [← hφ q]
    exact ih (φ q)
  | @rightEmpty Q₁ Q₂ R₂ T₁ T₂ ψ h ρ hρ φ hφ ih =>
    intro q
    change T₂.proj (ρ (φ.symm (ψ q))) = Φ (T₁.proj q)
    rw [← hφ, φ.apply_symm_apply]
    exact ih q

/-- Every genuine empty blowup can be inserted on the left. -/
theorem exists_emptyAware_left {d : ℕ} {P₁ P₂ Q₁ Q₂ R₁ : CMfd.{0} d}
    {Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂}
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) {ρ : R₁ → Q₁}
    (hρ : IsBlowupAlong d (∅ : Set Q₁) ρ) :
    ∃ φ : R₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₁,
      (∀ z, φ z = ρ z) ∧ EmptyAwareTowerIso Φ (.step T₁ ∅ ρ hρ) T₂ (φ.trans ψ) := by
  obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hρ
  exact ⟨φ,hφ,.leftEmpty h hρ φ hφ⟩

/-- Every genuine empty blowup can be inserted on the right. -/
theorem exists_emptyAware_right {d : ℕ} {P₁ P₂ Q₁ Q₂ R₂ : CMfd.{0} d}
    {Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂}
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) {ρ : R₂ → Q₂}
    (hρ : IsBlowupAlong d (∅ : Set Q₂) ρ) :
    ∃ φ : R₂ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂,
      (∀ z, φ z = ρ z) ∧ EmptyAwareTowerIso Φ T₁ (.step T₂ ∅ ρ hρ) (ψ.trans φ.symm) := by
  obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hρ
  exact ⟨φ,hφ,.rightEmpty h hρ φ hφ⟩

/-- Empty-aware lower comparisons induce ambient endpoint comparisons. -/
theorem exists_ambient_comparison_of_empty_aware_lower_histories {d t : ℕ} {X : CMfd.{0} (d+t)} {P₁ P₂ Q₁ Q₂ : CMfd.{0} d}
    (Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂)
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (hT : EmptyAwareTowerIso Φ T₁ T₂ ψ) :
    ∀ {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
      {ι₁ : P₁ → X} {ι₂ : P₂ → X} {M₁ : MarkedIdeal d P₁} {M₂ : MarkedIdeal d P₂}
      {Y₁ Y₂ : CMfd.{0} (d+t)} {U₁ : BlowupTower X Y₁} {U₂ : BlowupTower X Y₂}
      {η₁ : Q₁ → Y₁} {η₂ : Q₂ → Y₂},
      (∀ p, ι₂ (Φ p) = ι₁ p) →
      CoupledHistory N B J ι₁ M₁ T₁ U₁ η₁ → CoupledHistory N B J ι₂ M₂ T₂ U₂ η₂ →
      ∃ β : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ Y₂,
        (∀ y, U₂.proj (β y) = U₁.proj y) ∧ ∀ q, β (η₁ q) = η₂ (ψ q) := by
  induction hT with
  | refl =>
    intro N B J ι₁ ι₂ M₁ M₂ Y₁ Y₂ U₁ U₂ η₁ η₂ hι h₁ h₂
    cases h₁ with
    | refl h₁ =>
      cases h₂ with
      | refl h₂ =>
        refine ⟨Diffeomorph.refl 𝓘(ℂ,ComplexModel (d+t)) X ∞, ?_, ?_⟩
        · intro y
          rfl
        · intro q
          exact (hι q).symm
  | @step Q₁ Q₂ R₁ R₂ T₁ T₂ ψold hPrev C₁ ρ₁ hρ₁ C₂ ρ₂ hρ₂ ψnew hComm hCentre ih =>
    intro N B J ι₁ ι₂ M₁ M₂ Z₁ Z₂ U₁ U₂ η₁ η₂ hι h₁ h₂
    cases h₁ with
    | @step _ _ Y₁ _ _ U₁old η₁old _ _ C₁amb _ π₁amb _ hπ₁amb hprev₁ hC₁ hSq₁ hEnd₁ =>
      cases h₂ with
      | @step _ _ Y₂ _ _ U₂old η₂old _ _ C₂amb _ π₂amb _ hπ₂amb hprev₂ hC₂ hSq₂ hEnd₂ =>
        obtain ⟨β,hβproj,hβη⟩ := ih hι hprev₁ hprev₂
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
        refine ⟨χ, ?_, hχη⟩
        intro z
        change U₂old.proj (π₂amb (χ z)) = U₁old.proj (π₁amb z)
        rw [hχ]
        exact hβproj (π₁amb z)
  | @leftEmpty Q₁ Q₂ R₁ T₁ T₂ ψold hPrev ρ hρ φ hφ ih =>
    intro N B J ι₁ ι₂ M₁ M₂ Z₁ Y₂ U₁ U₂ η₁ η₂ hι h₁ h₂
    cases h₁ with
    | @step _ _ Yprev _ _ Uprev ηprev _ _ Camb _ πamb _ hπamb hprev hC hSq hEnd =>
      obtain ⟨β,hProj,hEmb⟩ := ih hι hprev h₂
      have hCamb : Camb = ∅ := by simpa only [image_empty] using hC
      have hπempty : IsBlowupAlong (d+t) (∅ : Set Yprev) πamb := by rw [← hCamb]; exact hπamb
      obtain ⟨θ,hθ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπempty
      let βnew := θ.trans β
      refine ⟨βnew,?_,?_⟩
      · intro y
        change U₂.proj (β (θ y)) = Uprev.proj (πamb y)
        simpa only [hθ y] using hProj (θ y)
      · intro q
        have hs := congrFun hSq q
        change πamb (η₁ q) = ηprev (ρ q) at hs
        change β (θ (η₁ q)) = η₂ (ψold (φ q))
        rw [hθ,hs,hφ]
        exact hEmb (ρ q)
  | @rightEmpty Q₁ Q₂ R₂ T₁ T₂ ψold hPrev ρ hρ φ hφ ih =>
    intro N B J ι₁ ι₂ M₁ M₂ Y₁ Z₂ U₁ U₂ η₁ η₂ hι h₁ h₂
    cases h₂ with
    | @step _ _ Yprev _ _ Uprev ηprev _ _ Camb _ πamb _ hπamb hprev hC hSq hEnd =>
      obtain ⟨β,hProj,hEmb⟩ := ih hι h₁ hprev
      have hCamb : Camb = ∅ := by simpa only [image_empty] using hC
      have hπempty : IsBlowupAlong (d+t) (∅ : Set Yprev) πamb := by rw [← hCamb]; exact hπamb
      obtain ⟨θ,hθ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπempty
      let βnew := β.trans θ.symm
      refine ⟨βnew,?_,?_⟩
      · intro y
        change Uprev.proj (πamb (θ.symm (β y))) = U₁.proj y
        rw [← hθ, θ.apply_symm_apply]
        exact hProj y
      · intro q
        change θ.symm (β (η₁ q)) = η₂ (φ.symm (ψold q))
        apply θ.injective
        change θ (θ.symm (β (η₁ q))) = θ (η₂ (φ.symm (ψold q)))
        rw [θ.apply_symm_apply, hθ]
        have hs := congrFun hSq (φ.symm (ψold q))
        change πamb (η₂ (φ.symm (ψold q))) = ηprev (ρ (φ.symm (ψold q))) at hs
        rw [hs, ← hφ, φ.apply_symm_apply]
        exact hEmb q

end
end Hironaka.HironakaG3EmptyAwareHistory
