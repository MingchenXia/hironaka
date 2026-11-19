import Hironaka.Resolution.HironakaG3CoupledOpenRestriction
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3GeometricLiftComparison
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaG3EmptyAwareHistory
  HironakaG3AmbientStepComparison HironakaActualNativeSectionFiniteHistory

def GeomEndpoint {d t : ℕ} {Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)} (η : Q → Y) : Prop :=
  ∃ (S : Set Y) (hr : ∀ y ∈ S, RegularAtDim (n := d+t) S y d),
    letI := chartedSpace (Nat.le_add_right d t) hr
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
    ∃ F : Q ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ S, (fun q => (F q).val) = η

inductive GeomCoupled {d t : ℕ} {X : CMfd.{0} (d+t)} {P : CMfd.{0} d} (ι : P → X) :
    {Q : CMfd.{0} d} → {Y : CMfd.{0} (d+t)} → BlowupTower P Q → BlowupTower X Y → (Q → Y) → Prop
  | refl (h : GeomEndpoint ι) : GeomCoupled ι .refl .refl ι
  | step {Q R : CMfd.{0} d} {Y Z : CMfd.{0} (d+t)} {T : BlowupTower P Q} {U : BlowupTower X Y}
      {η : Q → Y} {η' : R → Z} {C : Set Q} {C' : Set Y} {ρ : R → Q} {π : Z → Y}
      {hρ : IsBlowupAlong d C ρ} {hπ : IsBlowupAlong (d+t) C' π}
      (previous : GeomCoupled ι T U η) (centre : C' = η '' C) (square : π ∘ η' = η ∘ ρ)
      (endpoint : GeomEndpoint η') : GeomCoupled ι (.step T C ρ hρ) (.step U C' π hπ) η'

theorem geom_endpoint {d t : ℕ} {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)}
    {ι : P → X} {T : BlowupTower P Q} {U : BlowupTower X Y} {η : Q → Y}
    (h : GeomCoupled ι T U η) : GeomEndpoint η := by
  cases h with
  | refl h => exact h
  | step _ _ _ h => exact h

/-- Every native geometric lift supplies its actual stagewise coupled
history, with literal inclusions at all contacts. -/
theorem geomCoupled_of_native_lift {d t : ℕ} {X : CMfd.{0} (d+t)}
    {N : Set X} {hNc : IsClosed N} {hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d}
    {B : List (Set X)} {Y : CMfd.{0} (d+t)} {U : BlowupTower X Y}
    {S : Set Y} {hSc : IsClosed S} {hS : ∀ y ∈ S, RegularAtDim (n := d+t) S y d}
    {T : BlowupTower (nativeManifold (Nat.le_add_right d t) N hN)
      (nativeManifold (Nat.le_add_right d t) S hS)}
    (h : Lift (Nat.le_add_right d t) N hNc hN B U S hSc hS T) :
    GeomCoupled (Subtype.val : N → X) T U (Subtype.val : S → Y) := by
  induction h with
  | refl =>
    let := chartedSpace (Nat.le_add_right d t) hN
    let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    apply GeomCoupled.refl
    exact ⟨N,hN,Diffeomorph.refl 𝓘(ℂ,ComplexModel d) N ∞,rfl⟩
  | @step Y Z U S hSc hS T h D hD hint π hπ hNC ih =>
    apply GeomCoupled.step ih rfl rfl
    let := chartedSpace (Nat.le_add_right d t) (strictRegular hSc hS D π hπ)
    let := isComplexManifold_chartedSpace (Nat.le_add_right d t) (strictRegular hSc hS D π hπ)
    exact ⟨_,strictRegular hSc hS D π hπ,
      Diffeomorph.refl 𝓘(ℂ,ComplexModel d) _ ∞,rfl⟩

/-- Empty-aware comparisons lift using only actual geometric endpoint data. -/
theorem compare_geom_lifts {d t : ℕ} {X₁ X₂ : CMfd.{0} (d+t)} {P₁ P₂ Q₁ Q₂ : CMfd.{0} d}
    (Ξ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ X₂)
    (Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂)
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (hT : EmptyAwareTowerIso Φ T₁ T₂ ψ) :
    ∀ {ι₁ : P₁ → X₁} {ι₂ : P₂ → X₂}
      {Y₁ Y₂ : CMfd.{0} (d+t)} {U₁ : BlowupTower X₁ Y₁} {U₂ : BlowupTower X₂ Y₂}
      {η₁ : Q₁ → Y₁} {η₂ : Q₂ → Y₂},
      (∀ p, Ξ (ι₁ p) = ι₂ (Φ p)) → GeomCoupled ι₁ T₁ U₁ η₁ → GeomCoupled ι₂ T₂ U₂ η₂ →
      ∃ β : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ Y₂,
        (∀ y, U₂.proj (β y) = Ξ (U₁.proj y)) ∧ ∀ q, β (η₁ q) = η₂ (ψ q) := by
  induction hT with
  | refl =>
    intro ι₁ ι₂ Y₁ Y₂ U₁ U₂ η₁ η₂ hι h₁ h₂
    cases h₁ with
    | refl h₁ =>
      cases h₂ with
      | refl h₂ =>
        refine ⟨Ξ, ?_, ?_⟩
        · intro y
          rfl
        · intro q
          exact hι q
  | @step Q₁ Q₂ R₁ R₂ T₁ T₂ ψold hPrev C₁ ρ₁ hρ₁ C₂ ρ₂ hρ₂ ψnew hComm hCentre ih =>
    intro ι₁ ι₂ Z₁ Z₂ U₁ U₂ η₁ η₂ hι h₁ h₂
    cases h₁ with
    | @step _ _ Y₁ _ _ U₁old η₁old _ _ C₁amb _ π₁amb _ hπ₁amb hprev₁ hC₁ hSq₁ hEnd₁ =>
      cases h₂ with
      | @step _ _ Y₂ _ _ U₂old η₂old _ _ C₂amb _ π₂amb _ hπ₂amb hprev₂ hC₂ hSq₂ hEnd₂ =>
        obtain ⟨β,hβproj,hβη⟩ := ih hι hprev₁ hprev₂
        obtain ⟨_S, hr, F, hF⟩ :=
          geom_endpoint hprev₁
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
        obtain ⟨_S₁, hr₁, F₁, hF₁⟩ := hEnd₁
        obtain ⟨_S₂, hr₂, F₂, hF₂new⟩ := hEnd₂
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
        change U₂old.proj (π₂amb (χ z)) = Ξ (U₁old.proj (π₁amb z))
        rw [hχ]
        exact hβproj (π₁amb z)
  | @leftEmpty Q₁ Q₂ R₁ T₁ T₂ ψold hPrev ρ hρ φ hφ ih =>
    intro ι₁ ι₂ Z₁ Y₂ U₁ U₂ η₁ η₂ hι h₁ h₂
    cases h₁ with
    | @step _ _ Yprev _ _ Uprev ηprev _ _ Camb _ πamb _ hπamb hprev hC hSq hEnd =>
      obtain ⟨β,hProj,hEmb⟩ := ih hι hprev h₂
      have hCamb : Camb = ∅ := by simpa only [image_empty] using hC
      have hπempty : IsBlowupAlong (d+t) (∅ : Set Yprev) πamb := by rw [← hCamb]; exact hπamb
      obtain ⟨θ,hθ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπempty
      let βnew := θ.trans β
      refine ⟨βnew,?_,?_⟩
      · intro y
        change U₂.proj (β (θ y)) = Ξ (Uprev.proj (πamb y))
        simpa only [hθ y] using hProj (θ y)
      · intro q
        have hs := congrFun hSq q
        change πamb (η₁ q) = ηprev (ρ q) at hs
        change β (θ (η₁ q)) = η₂ (ψold (φ q))
        rw [hθ,hs,hφ]
        exact hEmb (ρ q)
  | @rightEmpty Q₁ Q₂ R₂ T₁ T₂ ψold hPrev ρ hρ φ hφ ih =>
    intro ι₁ ι₂ Y₁ Z₂ U₁ U₂ η₁ η₂ hι h₁ h₂
    cases h₂ with
    | @step _ _ Yprev _ _ Uprev ηprev _ _ Camb _ πamb _ hπamb hprev hC hSq hEnd =>
      obtain ⟨β,hProj,hEmb⟩ := ih hι h₁ hprev
      have hCamb : Camb = ∅ := by simpa only [image_empty] using hC
      have hπempty : IsBlowupAlong (d+t) (∅ : Set Yprev) πamb := by rw [← hCamb]; exact hπamb
      obtain ⟨θ,hθ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπempty
      let βnew := β.trans θ.symm
      refine ⟨βnew,?_,?_⟩
      · intro y
        change Uprev.proj (πamb (θ.symm (β y))) = Ξ (U₁.proj y)
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
end Hironaka.HironakaG3GeometricLiftComparison
