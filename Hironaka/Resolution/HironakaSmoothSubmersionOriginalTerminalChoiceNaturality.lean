/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalTerminalFunctor
/-! Actual finite smooth terminal maps commute with independent terminal histories.
Complete three-node mathematics preceded proofs. Genuine universal transport
constructs all lifts before intrinsic original final-map uniqueness is consumed. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalTerminalChoiceNaturality
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaOriginalTerminalProjectionUniqueness
  HironakaSmoothSubmersionOriginalTerminalFunctor
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X D D' : CMfd.{u} n} {Y E E' : CMfd.{u} m}

theorem holomorphicSquarePullback_biholomorphic_transport {f : Y → X} {g : E → D}
    (p : E → Y) (p' : E' → Y) (t : D → X) (t' : D' → X)
    (η : E' ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel m)⟯ E)
    (θ : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D)
    (hp : ∀ z, p (η z)=p' z) (ht : ∀ z, t (θ z)=t' z)
    (hU : HolomorphicSquarePullback f g p t) :
    HolomorphicSquarePullback f (θ.symm ∘ g ∘ η) p' t' := by
  intro k W a b ha hb hcone
  obtain ⟨w,hw,huniq⟩ := hU k W a (θ ∘ b) ha (θ.contMDiff.comp hb)
    (fun z => (hcone z).trans (ht (b z)).symm)
  refine ⟨η.symm ∘ w,⟨η.symm.contMDiff.comp hw.1,?_,?_⟩,?_⟩
  · intro z
    change p' (η.symm (w z))=a z
    rw [← hp,η.apply_symm_apply]
    exact hw.2.1 z
  · intro z
    change θ.symm (g (η (η.symm (w z))))=b z
    rw [η.apply_symm_apply,hw.2.2]
    exact θ.symm_apply_apply (b z)
  · intro v hv
    have he : η ∘ v=w := huniq (η ∘ v)
      ⟨η.contMDiff.comp hv.1,fun z => (hp (v z)).trans (hv.2.1 z),?_⟩
    · funext z
      apply η.injective
      change η (v z)=η (η.symm (w z))
      rw [η.apply_symm_apply]
      exact congrFun he z
    · intro z
      have hz := congrArg θ (hv.2.2 z)
      change θ (θ.symm (g (η (v z))))=θ (b z) at hz
      rw [θ.apply_symm_apply] at hz
      exact hz

theorem holomorphicSquarePullback_biholomorphic_identity
    (p : D → X) (p' : D' → X)
    (η : D' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D)
    (hp : ∀ z, p (η z)=p' z) :
    HolomorphicSquarePullback (id : X → X) η p' p := by
  intro k W a b _ha hb hcone
  refine ⟨η.symm ∘ b,⟨η.symm.contMDiff.comp hb,?_,?_⟩,?_⟩
  · intro z
    change p' (η.symm (b z))=a z
    rw [← hp,η.apply_symm_apply]
    exact (hcone z).symm
  · intro z
    exact η.apply_symm_apply (b z)
  · intro w hw
    funext z
    apply η.injective
    change η (w z)=η (η.symm (b z))
    rw [η.apply_symm_apply]
    exact hw.2.2 z

theorem terminalSmoothMap_identity_independent_histories
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T' : BlowupTower X D') (T : BlowupTower X D)
    (hc' : IsCanonical M ((canonicalInvariant n).inv M) T')
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr' : IsGeoResolution M T') (hr : IsGeoResolution M T) :
    let hid := whole_markedPullback_id M hM.isWellFormed.isCoherent
    terminalSmoothMap (Manifold.IsSubmersion.id (I := 𝓘(ℂ,ComplexModel n))) M hM T' T
      (hid.symm ▸ hc') hc (hid.symm ▸ hr') hr =
      ambientTerminalComparison M hM T' T hc' hc hr' hr := by
  dsimp only
  symm
  apply terminalSmoothMap_unique
  · exact (ambientTerminalComparison M hM T' T hc' hc hr' hr).contMDiff
  · exact ambientTerminalComparison_proj M hM T' T hc' hc hr' hr
  · exact holomorphicSquarePullback_biholomorphic_identity T.proj T'.proj _
      (ambientTerminalComparison_proj M hM T' T hc' hc hr' hr)

theorem terminalSmoothMap_independent_history_naturality {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S' : BlowupTower Y E') (S : BlowupTower Y E)
    (T' : BlowupTower X D') (T : BlowupTower X D)
    (hsc' : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S')
    (hsc : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
    (htc' : IsCanonical M ((canonicalInvariant n).inv M) T')
    (htc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hsr' : IsGeoResolution (markedPullback (m := m) f M) S')
    (hsr : IsGeoResolution (markedPullback (m := m) f M) S)
    (htr' : IsGeoResolution M T') (htr : IsGeoResolution M T) :
    let hN := original_ambient_domain_pullback hf M hM
    let η := ambientTerminalComparison (markedPullback (m := m) f M) hN S' S hsc' hsc hsr' hsr
    let θ := ambientTerminalComparison M hM T' T htc' htc htr' htr
    θ ∘ terminalSmoothMap hf M hM S' T' hsc' htc' hsr' htr' =
      terminalSmoothMap hf M hM S T hsc htc hsr htr ∘ η := by
  dsimp only
  let hN := original_ambient_domain_pullback hf M hM
  let η := ambientTerminalComparison (markedPullback (m := m) f M) hN S' S hsc' hsc hsr' hsr
  let θ := ambientTerminalComparison M hM T' T htc' htc htr' htr
  let g := terminalSmoothMap hf M hM S T hsc htc hsr htr
  have hη : ∀ z, S.proj (η z)=S'.proj z :=
    ambientTerminalComparison_proj (markedPullback (m := m) f M) hN S' S hsc' hsc hsr' hsr
  have hθ : ∀ z, T.proj (θ z)=T'.proj z :=
    ambientTerminalComparison_proj M hM T' T htc' htc htr' htr
  have hg := terminalSmoothMap_properties hf M hM S T hsc htc hsr htr
  have he : θ.symm ∘ g ∘ η=terminalSmoothMap hf M hM S' T' hsc' htc' hsr' htr' := by
    apply terminalSmoothMap_unique
    · exact θ.symm.contMDiff.comp (hg.1.contMDiff.comp η.contMDiff)
    · intro z
      change T'.proj (θ.symm (g (η z)))=f (S'.proj z)
      rw [← hθ,θ.apply_symm_apply,hg.2.1,hη]
    · exact holomorphicSquarePullback_biholomorphic_transport S.proj S'.proj T.proj T'.proj
        η θ hη hθ hg.2.2
  funext z
  change θ (terminalSmoothMap hf M hM S' T' hsc' htc' hsr' htr' z)=g (η z)
  rw [← he]
  exact θ.apply_symm_apply (g (η z))

end
end Hironaka.HironakaSmoothSubmersionOriginalTerminalChoiceNaturality
