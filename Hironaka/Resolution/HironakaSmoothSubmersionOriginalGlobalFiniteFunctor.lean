/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalFinite
/-! Intrinsic whole global terminal smooth arrows and finite-history independence.
Complete three-node mathematics preceded code. Actual finite source geometry,
not a uniqueness certificate, reduces two global Cartesian arrows to the genuine
finite tower projection theorem; a compact target supplies all histories. -/
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalGlobalFiniteFunctor
noncomputable section
open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowerTransforms CanonicalCentres HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalFiniteIdentification HironakaSmoothSubmersionOriginalTerminalFunctor
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionOriginalCompactTerminal
  HironakaSmoothSubmersionOriginalGlobalFinite HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCartesianTowerChoiceComparison HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceBaseChange
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold
variable {n m : ℕ} {X D D' : CMfd.{u} n} {Y E E' Z : CMfd.{u} m}

private theorem holomorphicSquarePullback_precompose_biholomorphism {f : Y → X} {g : Z → D}
    (p : Z → Y) (s : E → Y) (t : D → X)
    (η : E ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ Z)
    (hη : ∀ y, p (η y)=s y) (hU : HolomorphicSquarePullback f g p t) :
    HolomorphicSquarePullback f (g ∘ η) s t := by
  intro k W a b ha hb hcone
  obtain ⟨w,hw,huniq⟩ := hU k W a b ha hb hcone
  refine ⟨η.symm ∘ w,⟨η.symm.contMDiff.comp hw.1,?_,?_⟩,?_⟩
  · intro y
    exact (hη (η.symm (w y))).symm.trans (by rw [η.apply_symm_apply]; exact hw.2.1 y)
  · intro y
    change g (η (η.symm (w y)))=b y
    rw [η.apply_symm_apply]
    exact hw.2.2 y
  · intro v hv
    have he : η ∘ v=w := huniq (η ∘ v)
      ⟨η.contMDiff.comp hv.1,fun y => (hη (v y)).trans (hv.2.1 y),hv.2.2⟩
    funext y
    apply η.injective
    change η (v y)=η (η.symm (w y))
    rw [η.apply_symm_apply]
    exact congrFun he y

/-- A genuine source finite history gives whole intrinsic uniqueness on the
same original global manifolds. Existence is supplied by the earlier producer. -/
theorem originalGlobalSmoothMap_eq {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (S : BlowupTower Y E)
    (hscan : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
    (hsres : IsGeoResolution (markedPullback (m := m) f M) S)
    (a b : originalTerminalManifold (markedPullback (m := m) f M)
      (original_ambient_domain_pullback hf M hM) → originalTerminalManifold M hM)
    (ha : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ a)
    (hb : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (hpa : ∀ z, originalTerminalGluedProjection M hM (a z)=
      f (originalTerminalGluedProjection (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM) z))
    (hpb : ∀ z, originalTerminalGluedProjection M hM (b z)=
      f (originalTerminalGluedProjection (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM) z))
    (hUa : HolomorphicSquarePullback f a
      (originalTerminalGluedProjection (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM))
      (originalTerminalGluedProjection M hM))
    (hUb : HolomorphicSquarePullback f b
      (originalTerminalGluedProjection (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM))
      (originalTerminalGluedProjection M hM)) : a=b := by
  let hN := original_ambient_domain_pullback hf M hM
  let η := originalTerminalFiniteBiholomorphism (markedPullback (m := m) f M) hN S hscan hsres
  have hp : ∀ y, originalTerminalGluedProjection (markedPullback (m := m) f M) hN (η.symm y)=S.proj y := by
    intro y
    have h := originalTerminalFiniteBiholomorphism_proj (markedPullback (m := m) f M) hN
      S hscan hsres (η.symm y)
    change S.proj (η (η.symm y))=originalTerminalGluedProjection (markedPullback (m := m) f M) hN (η.symm y) at h
    rw [η.apply_symm_apply] at h
    exact h.symm
  have he : a ∘ η.symm=b ∘ η.symm := final_holomorphic_pullback_map_eq S
    (originalTerminalGluedProjection M hM) _ _ (ha.comp η.symm.contMDiff) (hb.comp η.symm.contMDiff)
    (fun y => (hpa (η.symm y)).trans (congrArg f (hp y)))
    (fun y => (hpb (η.symm y)).trans (congrArg f (hp y)))
    (holomorphicSquarePullback_precompose_biholomorphism _ S.proj _ η.symm hp hUa)
    (holomorphicSquarePullback_precompose_biholomorphism _ S.proj _ η.symm hp hUb)
  funext z
  have h := congrFun he (η z)
  simpa only [comp_apply,η.symm_apply_apply] using h

theorem originalGlobalFiniteSmoothMap_choice_independent {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower Y E) (T : BlowupTower X D)
    (S' : BlowupTower Y E') (T' : BlowupTower X D')
    (hscan : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
    (htcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hscan' : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S')
    (htcan' : IsCanonical M ((canonicalInvariant n).inv M) T')
    (hsres : IsGeoResolution (markedPullback (m := m) f M) S) (htres : IsGeoResolution M T)
    (hsres' : IsGeoResolution (markedPullback (m := m) f M) S') (htres' : IsGeoResolution M T') :
    originalGlobalFiniteSmoothMap hf M hM S T hscan htcan hsres htres=
      originalGlobalFiniteSmoothMap hf M hM S' T' hscan' htcan' hsres' htres' := by
  have hG := originalGlobalFiniteSmoothMap_properties hf M hM S T hscan htcan hsres htres
  have hG' := originalGlobalFiniteSmoothMap_properties hf M hM S' T' hscan' htcan' hsres' htres'
  exact originalGlobalSmoothMap_eq hf M hM S hscan hsres _ _
    hG.1.contMDiff hG'.1.contMDiff hG.2.1 hG'.2.1 hG.2.2 hG'.2.2

theorem existsUnique_originalCompactGlobalSmoothMap [CompactSpace X] {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    let hN := original_ambient_domain_pullback hf M hM
    ∃! G : originalTerminalManifold (markedPullback (m := m) f M) hN → originalTerminalManifold M hM,
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ z, originalTerminalGluedProjection M hM (G z)=
        f (originalTerminalGluedProjection (markedPullback (m := m) f M) hN z)) ∧
      HolomorphicSquarePullback f G
        (originalTerminalGluedProjection (markedPullback (m := m) f M) hN)
        (originalTerminalGluedProjection M hM) := by
  dsimp only
  have hG := originalCompactGlobalSmoothMap_properties hf M hM
  refine ⟨originalCompactGlobalSmoothMap hf M hM,hG,?_⟩
  intro g hg
  let T := compactCanonicalTower M hM
  let S := chosenActualTower defaultSmoothBlowupChoices hf T.2.val
  have hS := originalFiniteSmoothSourceHistory_properties hf M hM T.2.val
    (compactCanonicalTower_isCanonical M hM) T.2.property.2
  exact originalGlobalSmoothMap_eq hf M hM S.2.1 hS.1 hS.2 g _
    hg.1.contMDiff hG.1.contMDiff hg.2.1 hG.2.1 hg.2.2 hG.2.2

end
end Hironaka.HironakaSmoothSubmersionOriginalGlobalFiniteFunctor
