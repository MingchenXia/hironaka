/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalTerminalCartesian
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
/-! Actual Cartesian submersions on independently given original terminal spaces.
Complete three-node mathematics preceded proofs. Genuine source chart pullback
preserves the actual fixed-complement submersion presentations.
-/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaSmoothSubmersionOriginalTerminalSubmersion
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionOriginalTerminalCartesian
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y E Z : CMfd.{u} m}

theorem biholomorphic_chart_pullback_mem_maximalAtlas
    (η : E ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ Z)
    (a : OpenPartialHomeomorph Z (ComplexModel m))
    (ha : a ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel m) ∞ Z) :
    η.toHomeomorph.toOpenPartialHomeomorph.trans a ∈
      IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel m) ∞ E := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas ha).comp η.contMDiff.contMDiffOn
      (fun _ hy => hy.2)
  · exact (η.symm.contMDiff.contMDiffOn (s := univ)).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas ha).mono inter_subset_left) (fun _ _ => trivial)

private theorem submersionAtOfComplement_precompose_biholomorphism
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F] {g : Z → D} {y : E}
    (η : E ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ Z)
    (hg : Manifold.IsSubmersionAtOfComplement F
      𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g (η y)) :
    Manifold.IsSubmersionAtOfComplement F
      𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (g ∘ η) y := by
  let a := η.toHomeomorph.toOpenPartialHomeomorph.trans hg.domChart
  refine Manifold.IsSubmersionAtOfComplement.mk_of_charts hg.equiv a hg.codChart
    ⟨by trivial,hg.mem_domChart_source⟩ hg.mem_codChart_source
    (biholomorphic_chart_pullback_mem_maximalAtlas η hg.domChart hg.domChart_mem_maximalAtlas)
    hg.codChart_mem_maximalAtlas (fun _ hy => hg.source_subset_preimage_source hy.2) ?_
  intro w hw
  have hw' : w ∈ a.target := by simpa only [mfld_simps] using hw
  have hwa : w ∈ (hg.domChart.extend 𝓘(ℂ, ComplexModel m)).target := by
    simpa only [mfld_simps] using hw'.1
  change hg.codChart (g (η (η.symm (hg.domChart.symm w)))) = (hg.equiv w).1
  rw [η.apply_symm_apply]
  exact hg.writtenInCharts hwa

theorem isSubmersion_precompose_biholomorphism {g : Z → D}
    (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g)
    (η : E ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ Z) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (g ∘ η) :=
  Manifold.IsSubmersionOfComplement.isSubmersion (F := hg.complement)
    (fun y => submersionAtOfComplement_precompose_biholomorphism η
      (hg.isSubmersionOfComplement_complement (η y)))

private theorem actual_biholomorphic_pullback_universal {f : Y → X} {g : Z → D}
    (p : Z → Y) (s : E → Y) (t : D → X)
    (η : E ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ Z)
    (hη : ∀ y, p (η y) = s y) (hU : HolomorphicSquarePullback f g p t) :
    HolomorphicSquarePullback f (g ∘ η) s t := by
  intro ℓ W a b ha hb hcone
  obtain ⟨w,hw,huniq⟩ := hU ℓ W a b ha hb hcone
  refine ⟨η.symm ∘ w,⟨η.symm.contMDiff.comp hw.1,?_,?_⟩,?_⟩
  · intro y
    exact (hη (η.symm (w y))).symm.trans (by
      rw [η.apply_symm_apply]
      exact hw.2.1 y)
  · intro y
    change g (η (η.symm (w y))) = b y
    rw [η.apply_symm_apply]
    exact hw.2.2 y
  · intro v hv
    have he : η ∘ v = w := huniq (η ∘ v)
      ⟨η.contMDiff.comp hv.1,fun y => (hη (v y)).trans (hv.2.1 y),hv.2.2⟩
    funext y
    apply η.injective
    change η (v y) = η (η.symm (w y))
    rw [η.apply_symm_apply]
    exact congrFun he y

theorem original_terminal_final_submersion_cartesian {f : Y → X}
    (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower Y E) (T : BlowupTower X D)
    (hscan : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
    (htcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hsres : IsGeoResolution (markedPullback (m := m) f M) S)
    (htres : IsGeoResolution M T) :
    ∃ g : E → D, Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      (∀ y, T.proj (g y) = f (S.proj y)) ∧
      HolomorphicSquarePullback f g S.proj T.proj := by
  let P := chosenActualTower β hf T
  obtain ⟨_hc,_hr,η,hη⟩ :=
    original_terminal_source_actual_cartesian_comparison β hf M hM S T hscan htcan hsres htres
  have h := P.2.2.property
  exact ⟨P.2.2.val ∘ η,isSubmersion_precompose_biholomorphism h.isSubmersion η,
    fun y => (h.proj_comm (η y)).trans (congrArg f (hη y)),
    actual_biholomorphic_pullback_universal P.2.1.proj S.proj T.proj η hη h.universal⟩

end
end Hironaka.HironakaSmoothSubmersionOriginalTerminalSubmersion
