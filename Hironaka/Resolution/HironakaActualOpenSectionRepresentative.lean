/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOpenZeroSectionDifferentials
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOpenSectionRepresentative
noncomputable section
open Hironaka.HolomorphicIdealSheaves MarkedIdeals
 MarkedIdealOperationsAlong.MarkedIdeal RelativePrincipalizationSpan
 GermIdealPullbackCalculus InvertibleIdealQuotient
 HironakaActualOpenZeroSectionDifferentials
 HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
 [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem restrictEquiv_retraction (A : Set M) (E : List (Set M)) (d : ℕ)
    (r : M → M)
    (hr : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ r)
    (hfix : ∀x∈A,r x=x) (J : GermIdeal n M)
    (hJ : ∀x g,J.mem x g → HolomorphicAt n g x) :
    RestrictEquiv (⟨A,E,J,d⟩ : MarkedIdeal n M)
      (⟨A,E,GermIdeal.pullback (m := n) r J,d⟩ : MarkedIdeal n M) := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · intro x hx g hg
    have hgr : HolomorphicAt n (g ∘ r) x :=
      (show HolomorphicAt n g (r x) by rw [hfix x hx]; exact hJ x g hg).comp_contMDiff (Eventually.of_forall fun y => hr.contMDiffAt)
    have hp : (GermIdeal.pullback (m := n) r J).mem x (g ∘ r) := by
      apply GermIdeal.mem_pullback_iff.mpr
      apply isInSpanAt_self _ hgr
      exact ⟨g,by simpa only [hfix x hx] using hg,rfl⟩
    apply IsInSpanOnAt.congr_right (W := A) (IsInSpanAt.restrict (isInSpanAt_self hp hgr))
    exact Eventually.of_forall fun y hy => by simp only [Function.comp_apply,hfix y hy]
  · intro x hx g hg
    have hspan := GermIdeal.mem_pullback_iff.mp hg
    apply IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict hspan)
    rintro _ ⟨a,ha,rfl⟩
    have ha' : J.mem x a := by simpa only [hfix x hx] using ha
    apply IsInSpanOnAt.congr_right (W := A) (IsInSpanAt.restrict (isInSpanAt_self ha' (hJ x a ha')))
    exact Eventually.of_forall fun y hy => by simp only [Function.comp_apply,hfix y hy]

theorem restrictEquiv_actual_open_section {k : ℕ} (U : Opens (ComplexModel k))
    (A : Set U) (E : List (Set (productOpen U))) (d : ℕ)
    (J : GermIdeal (k+1) (productOpen U))
    (hJ : ∀x g,J.mem x g → HolomorphicAt (k+1) g x) :
    RestrictEquiv (⟨liftedCarrier A,E,J,d⟩ : MarkedIdeal (k+1) (productOpen U))
      (⟨liftedCarrier A,E,GermIdeal.pullback (m := k+1)
        (zeroSection U ∘ projection U) J,d⟩ : MarkedIdeal (k+1) (productOpen U)) := by
  apply restrictEquiv_retraction _ _ _ _
    ((zeroSection_contMDiff U).comp (projection_contMDiff U)) ?_ J hJ
  intro z hz
  apply Subtype.ext
  change tangentInclusion k 1 (tangentProjection k 1 z.val)=z.val
  have hq : HironakaActualCentreJointJets.actualJointNormalProjection k 1 z.val=0 := hz.2
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hq,map_zero,add_zero]
    using (HironakaActualIntrinsicStableAmbientIso.join_projections (n := k) (m := 1) z.val)
end
end Hironaka.HironakaActualOpenSectionRepresentative
