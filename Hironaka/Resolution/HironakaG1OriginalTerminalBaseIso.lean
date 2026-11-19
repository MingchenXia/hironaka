import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalFunctor

/-! # Actual terminal isomorphism over an actual base biholomorphism

The forward map is the HELD actual global smooth arrow for the SAME explicit
canonical family. Its holomorphic inverse is constructed by the HELD genuine
Cartesian universal property. Existing record transport and functor laws are
consumed unchanged. No global native cleanup assignment is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG1OriginalTerminalBaseIso

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionOriginalGlobalMap HironakaSmoothSubmersionOriginalTerminalSubmersion
  HironakaSmoothSubmersionOriginalGlobalFunctor HironakaSmoothSubmersionOrderedChoiceImageTrace
open ResolutionInvariantSpec (IsInvDomain)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem base_isSubmersion
    (f : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f :=
  isSubmersion_precompose_biholomorphism
    (Manifold.IsSubmersion.id (I := 𝓘(ℂ, ComplexModel n)) (M := X)) f

/-- ONLY ordinary base biholomorphism and marked input/domain construct the
actual terminal isomorphism; the forward map is the held global smooth map. -/
def originalTerminalBaseIso
    (f : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    originalTerminalManifold (markedPullback (m := n) f M)
        (original_ambient_domain_pullback (base_isSubmersion f) M hM)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ originalTerminalManifold M hM := by
  let hf := base_isSubmersion f
  let N := markedPullback (m := n) f M
  let hN := original_ambient_domain_pullback hf M hM
  let G := originalGlobalSmoothMap hf M hM
  have hGhol := originalGlobalSmoothMap_contMDiff hf M hM
  have hGproj := originalGlobalSmoothMap_proj hf M hM
  have hU := originalGlobalSmoothMap_cartesian hf M hM
  let hex := (hU n (originalTerminalManifold M hM)
    (f.symm ∘ originalTerminalGluedProjection M hM) id
    (f.symm.contMDiff.comp (originalTerminalGluedProjection_contMDiff M hM)) contMDiff_id
    (fun z => f.apply_symm_apply (originalTerminalGluedProjection M hM z))).exists
  let H := Classical.choose hex
  have hH := Classical.choose_spec hex
  have hleft : H ∘ G = id :=
    (hU n (originalTerminalManifold N hN) (originalTerminalGluedProjection N hN) G
      (originalTerminalGluedProjection_contMDiff N hN) hGhol (fun z => (hGproj z).symm)).unique
      ⟨hH.1.comp hGhol, fun z => by
        change originalTerminalGluedProjection N hN (H (G z)) = originalTerminalGluedProjection N hN z
        exact (hH.2.1 (G z)).trans
          ((congrArg f.symm (hGproj z)).trans (f.symm_apply_apply _)), fun z => hH.2.2 (G z)⟩
      ⟨contMDiff_id, fun _ => rfl, fun _ => rfl⟩
  exact
    { toEquiv := ⟨G, H, fun z => congrFun hleft z, hH.2.2⟩
      contMDiff_toFun := hGhol
      contMDiff_invFun := hH.1 }

/-- No replacement forward arrow was chosen. -/
theorem originalTerminalBaseIso_apply
    (f : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (z : originalTerminalManifold (markedPullback (m := n) f M)
      (original_ambient_domain_pullback (base_isSubmersion f) M hM)) :
    originalTerminalBaseIso f M hM z = originalGlobalSmoothMap (base_isSubmersion f) M hM z := rfl

/-- The SAME actual entire projection square over the original base map. -/
theorem originalTerminalBaseIso_proj
    (f : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (z : originalTerminalManifold (markedPullback (m := n) f M)
      (original_ambient_domain_pullback (base_isSubmersion f) M hM)) :
    originalTerminalGluedProjection M hM (originalTerminalBaseIso f M hM z) =
      f (originalTerminalGluedProjection (markedPullback (m := n) f M)
        (original_ambient_domain_pullback (base_isSubmersion f) M hM) z) :=
  originalGlobalSmoothMap_proj (base_isSubmersion f) M hM z

/-- The ENTIRE terminal total ideal is transported, before radicals/supports. -/
theorem originalTerminalBaseIso_wholeIdeal
    (f : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    GermIdeal.pullback (m := n) (originalTerminalBaseIso f M hM)
        (GermIdeal.pullback (m := n) (originalTerminalGluedProjection M hM) M.ideal) =
      GermIdeal.pullback (m := n)
        (originalTerminalGluedProjection (markedPullback (m := n) f M)
          (original_ambient_domain_pullback (base_isSubmersion f) M hM))
        (GermIdeal.pullback (m := n) f M.ideal) := by
  erw [← coherent_pullback_comp (originalTerminalGluedProjection_contMDiff M hM)
    (originalTerminalBaseIso f M hM).contMDiff M.ideal hM.isWellFormed.isCoherent]
  have he : originalTerminalGluedProjection M hM ∘ originalTerminalBaseIso f M hM =
      f ∘ originalTerminalGluedProjection (markedPullback (m := n) f M)
        (original_ambient_domain_pullback (base_isSubmersion f) M hM) :=
    funext (originalTerminalBaseIso_proj f M hM)
  rw [he]
  exact coherent_pullback_comp f.contMDiff (originalTerminalGluedProjection_contMDiff _ _)
    M.ideal hM.isWellFormed.isCoherent

/-- Actual WHOLE marked-record equality identifies the actual terminal source
before the held-family base isomorphism; no terminal comparison is supplied. -/
def originalTerminalMarkedRecordIso
    (f : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (N : MarkedIdeal n Y) (hN : IsInvDomain n N) (he : N = markedPullback (m := n) f M) :
    originalTerminalManifold N hN
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ originalTerminalManifold M hM :=
  (terminalRecordEquiv N (markedPullback (m := n) f M) hN
    (original_ambient_domain_pullback (base_isSubmersion f) M hM) he).trans
    (originalTerminalBaseIso f M hM)

/-- Full whole-record transport retains the original actual projection square. -/
theorem originalTerminalMarkedRecordIso_proj
    (f : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (N : MarkedIdeal n Y) (hN : IsInvDomain n N) (he : N = markedPullback (m := n) f M)
    (z : originalTerminalManifold N hN) :
    originalTerminalGluedProjection M hM (originalTerminalMarkedRecordIso f M hM N hN he z) =
      f (originalTerminalGluedProjection N hN z) := by
  change originalTerminalGluedProjection M hM
    (originalTerminalBaseIso f M hM (terminalRecordEquiv N _ hN _ he z)) = _
  rw [originalTerminalBaseIso_proj, terminalRecordEquiv_proj]

/-- The entire actual source-record ideal is retained after its internally
constructed whole-record identification and terminal base isomorphism. -/
theorem originalTerminalMarkedRecordIso_wholeIdeal
    (f : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (N : MarkedIdeal n Y) (hN : IsInvDomain n N) (he : N = markedPullback (m := n) f M) :
    GermIdeal.pullback (m := n) (originalTerminalMarkedRecordIso f M hM N hN he)
        (GermIdeal.pullback (m := n) (originalTerminalGluedProjection M hM) M.ideal) =
      GermIdeal.pullback (m := n) (originalTerminalGluedProjection N hN) N.ideal := by
  subst N
  exact originalTerminalBaseIso_wholeIdeal f M hM

end
end Hironaka.HironakaG1OriginalTerminalBaseIso
