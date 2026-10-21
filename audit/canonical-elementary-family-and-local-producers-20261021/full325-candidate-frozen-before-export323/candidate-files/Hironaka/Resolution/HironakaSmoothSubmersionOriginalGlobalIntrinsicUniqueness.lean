/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalSubmersion
/-! Genuine arbitrary-target whole original intrinsic uniqueness. Complete
blueprint preceded code. Each candidate restricts through real saturated source
ranges to the SAME actual finite source tower; intrinsic finite geometry proves
equality. The global producer has only original inputs. -/
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalGlobalIntrinsicUniqueness
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms CanonicalCentres
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalLocalBiholomorphism HironakaSmoothSubmersionOriginalSourceChartMap
  HironakaSmoothSubmersionOriginalGlobalMap HironakaSmoothSubmersionOriginalGlobalSubmersion
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOriginalTerminalFunctor
open ResolutionInvariantSpec (IsInvDomain)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold
variable {m n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
section Original
variable (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
  (M : MarkedIdeal n X) (hM : IsInvDomain n M)
private abbrev A := actualLocalTerminalAtlas (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM)

/-- A genuine candidate's whole Cartesian square restricts through the
actual original saturated source range to its actual finite source chart. -/
theorem originalGlobalCartesianMap_sourceChart_cartesian
    (g : originalTerminalManifold (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM) → originalTerminalManifold M hM)
    (hU : HolomorphicSquarePullback f g
      (originalTerminalGluedProjection (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM))
      (originalTerminalGluedProjection M hM)) (i : Y) :
    HolomorphicSquarePullback (originalSourceChartBaseMap hf M hM i)
      (g ∘ originalTerminalLocalInclusion (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM) i)
      ((A hf M hM).tower i).proj (originalTerminalGluedProjection M hM) := by
  intro k W a b ha hb hcone
  let N := markedPullback (m := m) f M
  let hN := original_ambient_domain_pullback hf M hM
  obtain ⟨w,hw,huniq⟩ := hU k W (Subtype.val ∘ a) b
    (contMDiff_subtype_val.comp ha) hb hcone
  have hrange (z : W) : w z ∈ originalTerminalLocalRangeOpen N hN i := by
    change w z ∈ range (originalTerminalLocalInclusion N hN i)
    rw [originalTerminalLocalInclusion_range]
    change originalTerminalGluedProjection N hN (w z) ∈ (A hf M hM).openSet i
    rw [hw.2.1 z]
    exact (a z).property
  let q : W → originalTerminalLocalRangeOpen N hN i := fun z => ⟨w z,hrange z⟩
  let r : W → (A hf M hM).finalSpace i := (originalTerminalLocalBiholomorphism N hN i).symm ∘ q
  have hq : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel m) ∞ q :=
    BlowupRestrictOpen.contMDiff_opens_mk hw.1 hrange
  have hr : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel m) ∞ r :=
    (originalTerminalLocalBiholomorphism N hN i).symm.contMDiff.comp hq
  have hinc (z : W) : originalTerminalLocalInclusion N hN i (r z)=w z :=
    originalTerminalLocalHomeomorphism_inverse_point N hN i (q z)
  refine ⟨r,⟨hr,?_,?_⟩,?_⟩
  · intro z
    apply Subtype.ext
    have hp := originalTerminalGluedProjection_local N hN i (r z)
    rw [hinc z] at hp
    exact hp.symm.trans (hw.2.1 z)
  · intro z
    exact (congrArg g (hinc z)).trans (hw.2.2 z)
  · intro v hv
    have he : (originalTerminalLocalInclusion N hN i) ∘ v=w := huniq _
      ⟨(originalTerminalLocalInclusion_contMDiff N hN i).comp hv.1,
        fun z => (originalTerminalGluedProjection_local N hN i (v z)).trans (congrArg Subtype.val (hv.2.1 z)),hv.2.2⟩
    funext z
    apply (originalTerminalLocalInclusion_openEmbedding N hN i).injective
    exact (congrFun he z).trans (hinc z).symm

/-- Whole intrinsic comparison uses ONLY original chart geometry, with no
whole source finite history and no compactness. Candidates are actual arrows. -/
theorem originalGlobalSmoothCartesianMap_eq
    (a b : originalTerminalManifold (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM) → originalTerminalManifold M hM)
    (ha : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ a)
    (hb : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b)
    (hpa : ∀ z, originalTerminalGluedProjection M hM (a z)=f
      (originalTerminalGluedProjection (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM) z))
    (hpb : ∀ z, originalTerminalGluedProjection M hM (b z)=f
      (originalTerminalGluedProjection (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM) z))
    (hUa : HolomorphicSquarePullback f a
      (originalTerminalGluedProjection (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM))
      (originalTerminalGluedProjection M hM))
    (hUb : HolomorphicSquarePullback f b
      (originalTerminalGluedProjection (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM))
      (originalTerminalGluedProjection M hM)) : a=b := by
  let N := markedPullback (m := m) f M
  let hN := original_ambient_domain_pullback hf M hM
  have hlocal (i : Y) : a ∘ originalTerminalLocalInclusion N hN i=b ∘ originalTerminalLocalInclusion N hN i :=
    final_holomorphic_pullback_map_eq ((A hf M hM).tower i) (originalTerminalGluedProjection M hM) _ _
      (ha.comp (originalTerminalLocalInclusion_contMDiff N hN i))
      (hb.comp (originalTerminalLocalInclusion_contMDiff N hN i))
      (fun y => (hpa _).trans (congrArg f (originalTerminalGluedProjection_local N hN i y)))
      (fun y => (hpb _).trans (congrArg f (originalTerminalGluedProjection_local N hN i y)))
      (originalGlobalCartesianMap_sourceChart_cartesian hf M hM a hUa i)
      (originalGlobalCartesianMap_sourceChart_cartesian hf M hM b hUb i)
  funext z
  obtain ⟨i,y,rfl⟩ := originalTerminalLocalInclusion_jointly_surjective N hN z
  exact congrFun (hlocal i) y

/-- ONLY original hf/M/domain construct the unique entire original smooth
Cartesian arrow, with neither original source nor original target compact. -/
theorem existsUnique_originalGlobalSmoothMap :
    let hN := original_ambient_domain_pullback hf M hM
    ∃! G : originalTerminalManifold (markedPullback (m := m) f M) hN → originalTerminalManifold M hM,
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ G ∧
      (∀ z, originalTerminalGluedProjection M hM (G z)=f
        (originalTerminalGluedProjection (markedPullback (m := m) f M) hN z)) ∧
      HolomorphicSquarePullback f G
        (originalTerminalGluedProjection (markedPullback (m := m) f M) hN)
        (originalTerminalGluedProjection M hM) := by
  dsimp only
  refine ⟨originalGlobalSmoothMap hf M hM,
    ⟨originalGlobalSmoothMap_isSubmersion hf M hM,originalGlobalSmoothMap_proj hf M hM,originalGlobalSmoothMap_cartesian hf M hM⟩,?_⟩
  intro g hg
  exact originalGlobalSmoothCartesianMap_eq hf M hM g _ hg.1.contMDiff
    (originalGlobalSmoothMap_contMDiff hf M hM) hg.2.1 (originalGlobalSmoothMap_proj hf M hM)
    hg.2.2 (originalGlobalSmoothMap_cartesian hf M hM)
end Original
end
end Hironaka.HironakaSmoothSubmersionOriginalGlobalIntrinsicUniqueness
