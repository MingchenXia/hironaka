/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalTerminalSubmersion
import Hironaka.Resolution.HironakaOriginalTerminalProjectionUniqueness
import Hironaka.Resolution.HironakaSmoothSubmersionComposition
/-! Intrinsic original finite terminal smooth maps and functor laws.
Complete four-node mathematics preceded proofs. Actual square uniqueness
constructs both genuine inverse maps before using actual projection geometry.
-/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalTerminalFunctor
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionComposition
  HironakaSmoothSubmersionOriginalTerminalSubmersion HironakaOriginalTerminalProjectionUniqueness
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m ℓ : ℕ} {X D : CMfd.{u} n} {Y E : CMfd.{u} m} {Z F : CMfd.{u} ℓ}

theorem holomorphicSquarePullback_pasting {f : Y → X} {h : Z → Y}
    {a : E → D} {b : F → E} (p : E → Y) (q : F → Z) (t : D → X)
    (hh : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ b)
    (hcomm : ∀ z, p (b z) = h (q z))
    (hU₁ : HolomorphicSquarePullback f a p t)
    (hU₂ : HolomorphicSquarePullback h b q p) :
    HolomorphicSquarePullback (f ∘ h) (a ∘ b) q t := by
  intro k W u v hu hv hcone
  obtain ⟨w,hw,huniq⟩ := hU₁ k W (h ∘ u) v (hh.comp hu) hv hcone
  obtain ⟨r,hr,huniqr⟩ := hU₂ k W u w hu hw.1 (fun z => (hw.2.1 z).symm)
  refine ⟨r,⟨hr.1,hr.2.1,fun z => (congrArg a (hr.2.2 z)).trans (hw.2.2 z)⟩,?_⟩
  intro s hs
  have he : b ∘ s = w := huniq (b ∘ s)
    ⟨hb.comp hs.1,fun z => (hcomm (s z)).trans (congrArg h (hs.2.1 z)),hs.2.2⟩
  exact huniqr s ⟨hs.1,hs.2.1,fun z => congrFun he z⟩

theorem final_holomorphic_pullback_map_eq {f : Y → X}
    (S : BlowupTower Y E) (t : D → X) (a b : E → D)
    (ha : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ a)
    (hb : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ b)
    (hpa : ∀ z, t (a z) = f (S.proj z)) (hpb : ∀ z, t (b z) = f (S.proj z))
    (hU₁ : HolomorphicSquarePullback f a S.proj t)
    (hU₂ : HolomorphicSquarePullback f b S.proj t) : a = b := by
  obtain ⟨v,hv,_⟩ := hU₁ m E S.proj b S.contMDiff_proj hb (fun z => (hpb z).symm)
  obtain ⟨w,hw,_⟩ := hU₂ m E S.proj a S.contMDiff_proj ha (fun z => (hpa z).symm)
  have hwv : w ∘ v = id :=
    (hU₂ m E S.proj b S.contMDiff_proj hb (fun z => (hpb z).symm)).unique
      ⟨hw.1.comp hv.1,fun z => (hw.2.1 (v z)).trans (hv.2.1 z),
        fun z => (hw.2.2 (v z)).trans (hv.2.2 z)⟩
      ⟨contMDiff_id,fun _ => rfl,fun _ => rfl⟩
  have hvw : v ∘ w = id :=
    (hU₁ m E S.proj a S.contMDiff_proj ha (fun z => (hpa z).symm)).unique
      ⟨hv.1.comp hw.1,fun z => (hv.2.1 (w z)).trans (hw.2.1 z),
        fun z => (hv.2.2 (w z)).trans (hw.2.2 z)⟩
      ⟨contMDiff_id,fun _ => rfl,fun _ => rfl⟩
  let η : E ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ E :=
    { toEquiv := ⟨v,w,fun z => congrFun hwv z,fun z => congrFun hvw z⟩
      contMDiff_toFun := hv.1
      contMDiff_invFun := hw.1 }
  have he : η = Diffeomorph.refl 𝓘(ℂ, ComplexModel m) E ∞ :=
    biholomorphisms_eq_of_actual_proj_eq S η _ hv.2.1
  funext z
  have hz := hv.2.2 z
  change a (η z) = b z at hz
  rw [he] at hz
  exact hz

def terminalSmoothMap {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower Y E) (T : BlowupTower X D)
    (hscan : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
    (htcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hsres : IsGeoResolution (markedPullback (m := m) f M) S)
    (htres : IsGeoResolution M T) : E → D :=
  Classical.choose (original_terminal_final_submersion_cartesian
    defaultSmoothBlowupChoices hf M hM S T hscan htcan hsres htres)

theorem terminalSmoothMap_properties {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower Y E) (T : BlowupTower X D)
    (hscan : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
    (htcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hsres : IsGeoResolution (markedPullback (m := m) f M) S)
    (htres : IsGeoResolution M T) :
    let g := terminalSmoothMap hf M hM S T hscan htcan hsres htres
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      (∀ z, T.proj (g z) = f (S.proj z)) ∧
      HolomorphicSquarePullback f g S.proj T.proj :=
  Classical.choose_spec (original_terminal_final_submersion_cartesian
    defaultSmoothBlowupChoices hf M hM S T hscan htcan hsres htres)

theorem terminalSmoothMap_unique {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower Y E) (T : BlowupTower X D)
    (hscan : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
    (htcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hsres : IsGeoResolution (markedPullback (m := m) f M) S)
    (htres : IsGeoResolution M T) (g : E → D)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hp : ∀ z, T.proj (g z) = f (S.proj z))
    (hU : HolomorphicSquarePullback f g S.proj T.proj) :
    g = terminalSmoothMap hf M hM S T hscan htcan hsres htres := by
  have hG := terminalSmoothMap_properties hf M hM S T hscan htcan hsres htres
  exact final_holomorphic_pullback_map_eq S T.proj g _ hg hG.1.contMDiff hp hG.2.1 hU hG.2.2

theorem existsUnique_original_terminal_submersion_cartesian {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower Y E) (T : BlowupTower X D)
    (hscan : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
    (htcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hsres : IsGeoResolution (markedPullback (m := m) f M) S)
    (htres : IsGeoResolution M T) :
    ∃! g : E → D, Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      (∀ z, T.proj (g z) = f (S.proj z)) ∧
      HolomorphicSquarePullback f g S.proj T.proj := by
  refine ⟨terminalSmoothMap hf M hM S T hscan htcan hsres htres,
    terminalSmoothMap_properties hf M hM S T hscan htcan hsres htres,?_⟩
  intro g hg
  exact terminalSmoothMap_unique hf M hM S T hscan htcan hsres htres g
    hg.1.contMDiff hg.2.1 hg.2.2

theorem whole_markedPullback_id (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
    markedPullback (m := n) (id : X → X) M = M := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · change M.E.map id = M.E
    exact List.map_id M.E
  · exact BlowupControlledTransform.pullback_id hI
  · rfl

theorem terminalSmoothMap_identity (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T : BlowupTower X D)
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T) (hr : IsGeoResolution M T) :
    let hpid := whole_markedPullback_id M hM.isWellFormed.isCoherent
    terminalSmoothMap (Manifold.IsSubmersion.id (I := 𝓘(ℂ, ComplexModel n))) M hM T T
      (hpid.symm ▸ hc) hc (hpid.symm ▸ hr) hr = id := by
  dsimp only
  symm
  apply terminalSmoothMap_unique
  · exact contMDiff_id
  · exact fun _ => rfl
  · intro k W a b _hb hb hcone
    refine ⟨b,⟨hb,fun z => (hcone z).symm,fun _ => rfl⟩,?_⟩
    intro w hw
    funext z
    exact hw.2.2 z

theorem terminalSmoothMap_composition {f : Y → X} {h : Z → Y}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ h)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (R : BlowupTower Z F) (S : BlowupTower Y E) (T : BlowupTower X D)
    (hRcan : IsCanonical (markedPullback (m := ℓ) (f ∘ h) M)
      ((canonicalInvariant ℓ).inv (markedPullback (m := ℓ) (f ∘ h) M)) R)
    (hScan : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
    (hTcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hRres : IsGeoResolution (markedPullback (m := ℓ) (f ∘ h) M) R)
    (hSres : IsGeoResolution (markedPullback (m := m) f M) S)
    (hTres : IsGeoResolution M T) :
    let hN := original_ambient_domain_pullback hf M hM
    let hrec := whole_markedPullback_comp hf.contMDiff hh.contMDiff M hM.isWellFormed.isCoherent
    terminalSmoothMap hf M hM S T hScan hTcan hSres hTres ∘
      terminalSmoothMap hh (markedPullback (m := m) f M) hN R S
        (hrec ▸ hRcan) hScan (hrec ▸ hRres) hSres =
      terminalSmoothMap (isSubmersion_composition hf hh) M hM R T hRcan hTcan hRres hTres := by
  dsimp only
  let hN := original_ambient_domain_pullback hf M hM
  let hrec := whole_markedPullback_comp hf.contMDiff hh.contMDiff M hM.isWellFormed.isCoherent
  have hA := terminalSmoothMap_properties hf M hM S T hScan hTcan hSres hTres
  have hB := terminalSmoothMap_properties hh (markedPullback (m := m) f M) hN R S
    (hrec ▸ hRcan) hScan (hrec ▸ hRres) hSres
  have hC := terminalSmoothMap_properties (isSubmersion_composition hf hh) M hM R T
    hRcan hTcan hRres hTres
  exact final_holomorphic_pullback_map_eq R T.proj _ _
    (hA.1.contMDiff.comp hB.1.contMDiff) hC.1.contMDiff
    (fun z => (hA.2.1 _).trans (congrArg f (hB.2.1 z))) hC.2.1
    (holomorphicSquarePullback_pasting S.proj R.proj T.proj hh.contMDiff hB.1.contMDiff
      hB.2.1 hA.2.2 hB.2.2) hC.2.2

end
end Hironaka.HironakaSmoothSubmersionOriginalTerminalFunctor
