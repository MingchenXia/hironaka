/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalSourceChartCompatibility
/-! Entire arbitrary-target original global holomorphic Cartesian arrows.
Complete mathematics preceded code. Actual source overlap equality descends the
real gluing. Genuine saturated ranges and actual full source-chart squares
construct and glue every global cone lift; no global certificates are inputs. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalGlobalMap
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms CanonicalCentres
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalLocalBiholomorphism HironakaSmoothSubmersionOriginalSourceChartMap
  HironakaSmoothSubmersionOriginalSourceChartCompatibility HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionOrderedChoiceBaseChange
open ResolutionInvariantSpec (IsInvDomain)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold
variable {m n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}
section Original
variable (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
  (M : MarkedIdeal n X) (hM : IsInvDomain n M)

private abbrev N := markedPullback (m := m) f M
include hf hM in
private theorem hN : IsInvDomain m (N (f := f) M) := original_ambient_domain_pullback hf M hM
private abbrev A := actualLocalTerminalAtlas (N (f := f) M) (hN hf M hM)

private def localContinuousMap (i : Y) : ContinuousMap ((A hf M hM).finalSpace i) (originalTerminalManifold M hM) :=
  ⟨originalSourceChartSmoothMap hf M hM i,(originalSourceChartSmoothMap_contMDiff hf M hM i).continuous⟩

private theorem localContinuousMap_compatible (ij : Y × Y) :
    (originalTerminalGlueData (N (f := f) M) (hN hf M hM)).toGlueData.diagram.fst ij ≫
      TopCat.ofHom (localContinuousMap hf M hM ij.1)=
    (originalTerminalGlueData (N (f := f) M) (hN hf M hM)).toGlueData.diagram.snd ij ≫
      TopCat.ofHom (localContinuousMap hf M hM ij.2) := by
  rcases ij with ⟨i,j⟩
  ext y
  exact originalSourceChartSmoothMap_overlap hf M hM i j y

private def globalContinuousMap : ContinuousMap (originalTerminalGluedSpace (N (f := f) M) (hN hf M hM))
    (originalTerminalManifold M hM) :=
  (Multicoequalizer.desc (originalTerminalGlueData (N (f := f) M) (hN hf M hM)).toGlueData.diagram
    (TopCat.of (originalTerminalManifold M hM)) (fun i => TopCat.ofHom (localContinuousMap hf M hM i))
    (localContinuousMap_compatible hf M hM)).hom

/-- ONLY original hf/M/domain: the entire SAME original source gluing descends
into the SAME original target terminal manifold, without compactness. -/
def originalGlobalSmoothMap :
    originalTerminalManifold (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM) →
      originalTerminalManifold M hM := globalContinuousMap hf M hM

theorem originalGlobalSmoothMap_local (i : Y) (y : (A hf M hM).finalSpace i) :
    originalGlobalSmoothMap hf M hM (originalTerminalLocalInclusion (N (f := f) M) (hN hf M hM) i y)=
      originalSourceChartSmoothMap hf M hM i y := by
  have h := Multicoequalizer.π_desc
    (originalTerminalGlueData (N (f := f) M) (hN hf M hM)).toGlueData.diagram
    (TopCat.of (originalTerminalManifold M hM)) (fun i => TopCat.ofHom (localContinuousMap hf M hM i))
    (localContinuousMap_compatible hf M hM) i
  exact congrArg (fun g : (originalTerminalGlueData (N (f := f) M) (hN hf M hM)).U i ⟶
    TopCat.of (originalTerminalManifold M hM) => g y) h

theorem originalGlobalSmoothMap_proj
    (z : originalTerminalManifold (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM)) :
    originalTerminalGluedProjection M hM (originalGlobalSmoothMap hf M hM z)=
      f (originalTerminalGluedProjection (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM) z) := by
  obtain ⟨i,y,rfl⟩ := originalTerminalLocalInclusion_jointly_surjective (N (f := f) M) (hN hf M hM) z
  exact (congrArg (originalTerminalGluedProjection M hM) (originalGlobalSmoothMap_local hf M hM i y)).trans
    ((originalSourceChartSmoothMap_proj hf M hM i y).trans
      (congrArg f (originalTerminalGluedProjection_local (N (f := f) M) (hN hf M hM) i y)).symm)

theorem originalGlobalSmoothMap_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (originalGlobalSmoothMap hf M hM) := by
  intro z
  obtain ⟨i,y,rfl⟩ := originalTerminalLocalInclusion_jointly_surjective (N (f := f) M) (hN hf M hM) z
  let U := originalTerminalLocalRangeOpen (N (f := f) M) (hN hf M hM) i
  have he : (originalGlobalSmoothMap hf M hM) ∘
      (Subtype.val : U → originalTerminalManifold (N (f := f) M) (hN hf M hM))=
        (originalSourceChartSmoothMap hf M hM i) ∘
          (originalTerminalLocalBiholomorphism (N (f := f) M) (hN hf M hM) i).symm := by
    funext q
    have hi := originalTerminalLocalHomeomorphism_inverse_point (N (f := f) M) (hN hf M hM) i q
    exact (congrArg (originalGlobalSmoothMap hf M hM) hi).symm.trans (originalGlobalSmoothMap_local hf M hM i _)
  have hh : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞
      ((originalGlobalSmoothMap hf M hM) ∘
        (Subtype.val : U → originalTerminalManifold (N (f := f) M) (hN hf M hM))) := by
    rw [he]
    exact (originalSourceChartSmoothMap_contMDiff hf M hM i).comp
      (originalTerminalLocalBiholomorphism (N (f := f) M) (hN hf M hM) i).symm.contMDiff
  exact contMDiffAt_subtype_iff.mp
    (hh ⟨originalTerminalLocalInclusion (N (f := f) M) (hN hf M hM) i y,⟨y,rfl⟩⟩)

private def sourcePointInverse (i : Y)
    (z : originalTerminalManifold (N (f := f) M) (hN hf M hM))
    (hz : originalTerminalGluedProjection (N (f := f) M) (hN hf M hM) z ∈ (A hf M hM).openSet i) :
    (A hf M hM).finalSpace i :=
  (originalTerminalLocalBiholomorphism (N (f := f) M) (hN hf M hM) i).symm
    ⟨z,by
      change z ∈ range (originalTerminalLocalInclusion (N (f := f) M) (hN hf M hM) i)
      rw [originalTerminalLocalInclusion_range]
      exact hz⟩

private theorem sourcePointInverse_inclusion (i : Y)
    (z : originalTerminalManifold (N (f := f) M) (hN hf M hM))
    (hz : originalTerminalGluedProjection (N (f := f) M) (hN hf M hM) z ∈ (A hf M hM).openSet i) :
    originalTerminalLocalInclusion (N (f := f) M) (hN hf M hM) i (sourcePointInverse hf M hM i z hz)=z :=
  originalTerminalLocalHomeomorphism_inverse_point (N (f := f) M) (hN hf M hM) i _

private theorem sourcePointInverse_proj (i : Y)
    (z : originalTerminalManifold (N (f := f) M) (hN hf M hM))
    (hz : originalTerminalGluedProjection (N (f := f) M) (hN hf M hM) z ∈ (A hf M hM).openSet i) :
    (((A hf M hM).tower i).proj (sourcePointInverse hf M hM i z hz)).val=
      originalTerminalGluedProjection (N (f := f) M) (hN hf M hM) z := by
  have h := originalTerminalGluedProjection_local (N (f := f) M) (hN hf M hM) i (sourcePointInverse hf M hM i z hz)
  rw [sourcePointInverse_inclusion] at h
  exact h.symm

private theorem sourcePointInverse_target (i : Y)
    (z : originalTerminalManifold (N (f := f) M) (hN hf M hM))
    (hz : originalTerminalGluedProjection (N (f := f) M) (hN hf M hM) z ∈ (A hf M hM).openSet i) :
    originalSourceChartSmoothMap hf M hM i (sourcePointInverse hf M hM i z hz)=originalGlobalSmoothMap hf M hM z := by
  have h := originalGlobalSmoothMap_local hf M hM i (sourcePointInverse hf M hM i z hz)
  rw [sourcePointInverse_inclusion] at h
  exact h.symm

theorem originalGlobalSmoothMap_cartesian :
    HolomorphicSquarePullback f (originalGlobalSmoothMap hf M hM)
      (originalTerminalGluedProjection (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM))
      (originalTerminalGluedProjection M hM) := by
  intro k W a b ha hb hcone
  let C := A hf M hM
  let O (i : Y) : Opens W := ⟨a ⁻¹' (C.openSet i : Set Y),(C.openSet i).isOpen.preimage ha.continuous⟩
  have hcover : ∀ z : W, ∃ i, z ∈ O i := fun z => ⟨a z,C.point_mem (a z)⟩
  let ai (i : Y) : O i → C.openSet i := fun z => ⟨a z.val,z.property⟩
  have hai (i : Y) : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel m) ∞ (ai i) :=
    BlowupRestrictOpen.contMDiff_opens_mk (ha.comp contMDiff_subtype_val) (fun z => z.property)
  have hex (i : Y) : ∃ r : O i → C.finalSpace i,
      ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel m) ∞ r ∧
      (∀ z, (C.tower i).proj (r z)=ai i z) ∧
      ∀ z, originalSourceChartSmoothMap hf M hM i (r z)=b z.val :=
    ((originalSourceChartSmoothMap_cartesian hf M hM i) k (CMfd.of (n := k) (O i)) (ai i)
      (b ∘ Subtype.val) (hai i) (hb.comp contMDiff_subtype_val) (fun z => hcone z.val)).exists
  choose r hr using hex
  let rglobal (i : Y) : O i → originalTerminalManifold (N (f := f) M) (hN hf M hM) :=
    (originalTerminalLocalInclusion (N (f := f) M) (hN hf M hM) i) ∘ r i
  have hsource (i : Y) (z : O i) :
      originalTerminalGluedProjection (N (f := f) M) (hN hf M hM) (rglobal i z)=a z.val :=
    (originalTerminalGluedProjection_local (N (f := f) M) (hN hf M hM) i (r i z)).trans
      (congrArg Subtype.val ((hr i).2.1 z))
  have htarget (i : Y) (z : O i) : originalGlobalSmoothMap hf M hM (rglobal i z)=b z.val :=
    (originalGlobalSmoothMap_local hf M hM i (r i z)).trans ((hr i).2.2 z)
  have hcompat : ∀ i j z hzi hzj, rglobal i ⟨z,hzi⟩=rglobal j ⟨z,hzj⟩ := by
    intro i j z hzi hzj
    let q := rglobal j ⟨z,hzj⟩
    have hq : originalTerminalGluedProjection (N (f := f) M) (hN hf M hM) q ∈ C.openSet i := by
      rw [hsource j ⟨z,hzj⟩]
      exact hzi
    let x := sourcePointInverse hf M hM i q hq
    have hp : (C.tower i).proj (r i ⟨z,hzi⟩)=(C.tower i).proj x := by
      apply Subtype.ext
      exact (congrArg Subtype.val ((hr i).2.1 ⟨z,hzi⟩)).trans
        ((hsource j ⟨z,hzj⟩).symm.trans (sourcePointInverse_proj hf M hM i q hq).symm)
    have ht : originalSourceChartSmoothMap hf M hM i (r i ⟨z,hzi⟩)=originalSourceChartSmoothMap hf M hM i x :=
      ((hr i).2.2 ⟨z,hzi⟩).trans
        ((sourcePointInverse_target hf M hM i q hq).trans (htarget j ⟨z,hzj⟩)).symm
    have he := holomorphicSquarePullback_jointInjective (originalSourceChartSmoothMap_cartesian hf M hM i)
      (originalSourceChartSmoothMap_proj hf M hM i) (r i ⟨z,hzi⟩) x hp ht
    exact (congrArg (originalTerminalLocalInclusion (N (f := f) M) (hN hf M hM) i) he).trans
      (sourcePointInverse_inclusion hf M hM i q hq)
  let L := holomorphicOpenCoverGlue O rglobal hcompat hcover
  have hLhol : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel m) ∞ L :=
    holomorphicOpenCoverGlue_contMDiff (B := originalTerminalManifold (N (f := f) M) (hN hf M hM)) O rglobal hcompat hcover
      (fun i => (originalTerminalLocalInclusion_contMDiff (N (f := f) M) (hN hf M hM) i).comp (hr i).1)
  have hLlocal (i : Y) (z : O i) : L z.val=rglobal i z := holomorphicOpenCoverGlue_local O rglobal hcompat hcover i z
  refine ⟨L,⟨hLhol,?_,?_⟩,?_⟩
  · intro z
    obtain ⟨i,hi⟩ := hcover z
    rw [hLlocal i ⟨z,hi⟩]
    exact hsource i ⟨z,hi⟩
  · intro z
    obtain ⟨i,hi⟩ := hcover z
    rw [hLlocal i ⟨z,hi⟩]
    exact htarget i ⟨z,hi⟩
  · intro v hv
    funext z
    obtain ⟨i,hi⟩ := hcover z
    have hvi : originalTerminalGluedProjection (N (f := f) M) (hN hf M hM) (v z) ∈ C.openSet i := by
      rw [hv.2.1 z]
      exact hi
    let x := sourcePointInverse hf M hM i (v z) hvi
    have hp : (C.tower i).proj (r i ⟨z,hi⟩)=(C.tower i).proj x := by
      apply Subtype.ext
      exact (congrArg Subtype.val ((hr i).2.1 ⟨z,hi⟩)).trans
        ((hv.2.1 z).symm.trans (sourcePointInverse_proj hf M hM i (v z) hvi).symm)
    have ht : originalSourceChartSmoothMap hf M hM i (r i ⟨z,hi⟩)=originalSourceChartSmoothMap hf M hM i x :=
      ((hr i).2.2 ⟨z,hi⟩).trans
        ((sourcePointInverse_target hf M hM i (v z) hvi).trans (hv.2.2 z)).symm
    have he := holomorphicSquarePullback_jointInjective (originalSourceChartSmoothMap_cartesian hf M hM i)
      (originalSourceChartSmoothMap_proj hf M hM i) (r i ⟨z,hi⟩) x hp ht
    rw [hLlocal i ⟨z,hi⟩]
    exact (sourcePointInverse_inclusion hf M hM i (v z) hvi).symm.trans
      (congrArg (originalTerminalLocalInclusion (N (f := f) M) (hN hf M hM) i) he).symm

end Original
end
end Hironaka.HironakaSmoothSubmersionOriginalGlobalMap
