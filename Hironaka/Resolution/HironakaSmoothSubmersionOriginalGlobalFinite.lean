/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalTerminalFiniteIdentification
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalCompactTerminal
/-! Genuine smooth Cartesian arrows on original global terminal manifolds.
Complete mathematics preceded code. The actual finite histories are geometrical
inputs to the general comparison; a compact target internally supplies both
histories even for an arbitrary noncompact source. -/
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalGlobalFinite
noncomputable section
open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowerTransforms CanonicalCentres HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalFiniteIdentification HironakaSmoothSubmersionOriginalTerminalFunctor
  HironakaSmoothSubmersionOriginalTerminalSubmersion HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionOriginalCompactTerminal HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionComposition
  HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionOrderedChoiceImageTrace
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold
variable {n m : ℕ} {X D C : CMfd.{u} n} {Y E Z : CMfd.{u} m}

theorem isSubmersion_biholomorphism
    (η : D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ C) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ η := by
  simpa only [id_comp] using isSubmersion_precompose_biholomorphism
    (Manifold.IsSubmersion.id (I := 𝓘(ℂ,ComplexModel n)) (M := C)) η

theorem isSubmersion_biholomorphic_conjugate {g : E → D}
    (hg : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g)
    (η : Z ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E)
    (θ : D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ C) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (θ ∘ g ∘ η) :=
  isSubmersion_composition (isSubmersion_biholomorphism θ)
    (isSubmersion_precompose_biholomorphism hg η)

section OriginalFinite
variable {f : Y → X}
  (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
  (M : MarkedIdeal n X) (hM : IsInvDomain n M)
  (S : BlowupTower Y E) (T : BlowupTower X D)
  (hscan : IsCanonical (markedPullback (m := m) f M)
    ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
  (htcan : IsCanonical M ((canonicalInvariant n).inv M) T)
  (hsres : IsGeoResolution (markedPullback (m := m) f M) S) (htres : IsGeoResolution M T)

/-- This arrow acts on the fixed original global manifolds, with genuine
finite histories identified by their actual local gluing comparisons. -/
def originalGlobalFiniteSmoothMap :
    originalTerminalManifold (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM) →
      originalTerminalManifold M hM :=
  (originalTerminalFiniteBiholomorphism M hM T htcan htres).symm ∘
    terminalSmoothMap hf M hM S T hscan htcan hsres htres ∘
      originalTerminalFiniteBiholomorphism (markedPullback (m := m) f M)
        (original_ambient_domain_pullback hf M hM) S hscan hsres

theorem originalGlobalFiniteSmoothMap_properties :
    let hN := original_ambient_domain_pullback hf M hM
    let G := originalGlobalFiniteSmoothMap hf M hM S T hscan htcan hsres htres
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ z, originalTerminalGluedProjection M hM (G z)=
        f (originalTerminalGluedProjection (markedPullback (m := m) f M) hN z)) ∧
      HolomorphicSquarePullback f G
        (originalTerminalGluedProjection (markedPullback (m := m) f M) hN)
        (originalTerminalGluedProjection M hM) := by
  dsimp only
  let hN := original_ambient_domain_pullback hf M hM
  let η := originalTerminalFiniteBiholomorphism (markedPullback (m := m) f M) hN S hscan hsres
  let θ := originalTerminalFiniteBiholomorphism M hM T htcan htres
  let g := terminalSmoothMap hf M hM S T hscan htcan hsres htres
  have hG := terminalSmoothMap_properties hf M hM S T hscan htcan hsres htres
  have hη : ∀ z, S.proj (η z)=originalTerminalGluedProjection (markedPullback (m := m) f M) hN z :=
    originalTerminalFiniteBiholomorphism_proj _ hN S hscan hsres
  have hθ : ∀ z, T.proj (θ z)=originalTerminalGluedProjection M hM z :=
    originalTerminalFiniteBiholomorphism_proj M hM T htcan htres
  refine ⟨isSubmersion_biholomorphic_conjugate hG.1 η θ.symm,?_,?_⟩
  · intro z
    have hp := hθ (θ.symm (g (η z)))
    rw [θ.apply_symm_apply] at hp
    exact hp.symm.trans ((hG.2.1 (η z)).trans (congrArg f (hη z)))
  · intro k W a b ha hb hcone
    obtain ⟨w,hw,huniq⟩ := hG.2.2 k W a (θ ∘ b) ha (θ.contMDiff.comp hb)
      (fun z => (hcone z).trans (hθ (b z)).symm)
    refine ⟨η.symm ∘ w,⟨η.symm.contMDiff.comp hw.1,?_,?_⟩,?_⟩
    · intro z
      have hp := hη (η.symm (w z))
      rw [η.apply_symm_apply] at hp
      exact hp.symm.trans (hw.2.1 z)
    · intro z
      change θ.symm (g (η (η.symm (w z))))=b z
      have hwg : g (w z)=θ (b z) := hw.2.2 z
      rw [η.apply_symm_apply,hwg,θ.symm_apply_apply]
    · intro v hv
      have hvtarget : ∀ z, g (η (v z))=θ (b z) := by
        intro z
        have h := congrArg θ (hv.2.2 z)
        change θ (θ.symm (g (η (v z))))=θ (b z) at h
        rw [θ.apply_symm_apply] at h
        exact h
      have he : η ∘ v=w := huniq (η ∘ v)
        ⟨η.contMDiff.comp hv.1,fun z => (hη (v z)).trans (hv.2.1 z),hvtarget⟩
      funext z
      apply η.injective
      change η (v z)=η (η.symm (w z))
      rw [η.apply_symm_apply]
      exact congrFun he z


end OriginalFinite

/-- No source compactness or source finite-history input: actual smooth
pullback of the entire finite target history internally supplies both. -/
theorem originalFiniteSmoothSourceHistory_properties {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T : BlowupTower X D) (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr : IsGeoResolution M T) :
    let P := chosenActualTower defaultSmoothBlowupChoices hf T
    IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) P.2.1 ∧
      IsGeoResolution (markedPullback (m := m) f M) P.2.1 := by
  dsimp only
  let P := chosenActualTower defaultSmoothBlowupChoices hf T
  have h := P.2.2.property
  have htest := (IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed hr.1).1
  have hcos := IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed hr.1
  refine ⟨IsActualTowerPullback.original_ambient_canonical h M hM hc,htest,?_⟩
  rw [hcos,hr.2,preimage_empty]

/-- Original compact TARGET internally supplies an actual arrow on the fixed
original global manifolds, even for a noncompact original source. -/
def originalCompactGlobalSmoothMap [CompactSpace X] {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    originalTerminalManifold (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM) →
      originalTerminalManifold M hM :=
  let T := compactCanonicalTower M hM
  let hc := compactCanonicalTower_isCanonical M hM
  let hr := T.2.property.2
  let S := chosenActualTower defaultSmoothBlowupChoices hf T.2.val
  let hS := originalFiniteSmoothSourceHistory_properties hf M hM T.2.val hc hr
  originalGlobalFiniteSmoothMap hf M hM S.2.1 T.2.val hS.1 hc hS.2 hr

theorem originalCompactGlobalSmoothMap_properties [CompactSpace X] {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    let hN := original_ambient_domain_pullback hf M hM
    let G := originalCompactGlobalSmoothMap hf M hM
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ z, originalTerminalGluedProjection M hM (G z)=
        f (originalTerminalGluedProjection (markedPullback (m := m) f M) hN z)) ∧
      HolomorphicSquarePullback f G
        (originalTerminalGluedProjection (markedPullback (m := m) f M) hN)
        (originalTerminalGluedProjection M hM) := by
  dsimp only
  let T := compactCanonicalTower M hM
  let hc := compactCanonicalTower_isCanonical M hM
  let hr := T.2.property.2
  let S := chosenActualTower defaultSmoothBlowupChoices hf T.2.val
  let hS := originalFiniteSmoothSourceHistory_properties hf M hM T.2.val hc hr
  exact originalGlobalFiniteSmoothMap_properties hf M hM S.2.1 T.2.val hS.1 hc hS.2 hr

end
end Hironaka.HironakaSmoothSubmersionOriginalGlobalFinite
