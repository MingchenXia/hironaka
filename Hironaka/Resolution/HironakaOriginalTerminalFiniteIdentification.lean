/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalTerminalLocalBiholomorphism
/-! Actual finite canonical terminal histories identify the original global terminal
manifold by genuine original overlap comparisons. Complete mathematics preceded
code. No caller local maps, overlap or global identification certificates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Topology Function IsManifold
open scoped Manifold ContDiff Topology
open CategoryTheory CategoryTheory.Limits
universe u
namespace Hironaka.HironakaOriginalTerminalFiniteIdentification
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms CanonicalCentres MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalLocalBiholomorphism HironakaOriginalTerminalOpenComparison
  HironakaOriginalTerminalOverlapComparison HironakaOriginalTerminalOverlapRestriction
  HironakaOriginalTerminalProjectionUniqueness MaxLocusLocal
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold
variable {n : ℕ} {X D : CMfd.{u} n}

private def fullLocalFinalDiffeomorphism {U : Opens X}
    (S : BlowupTower (CMfd.of (n := n) U) D) :
    D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage S (nestedOpens U (U ⊓ (⊤ : Opens X)))) where
  toFun y := ⟨y,⟨(S.proj y).property,trivial⟩⟩
  invFun y := y.val
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
    (V := openPreimage S (nestedOpens U (U ⊓ (⊤ : Opens X))))
    contMDiff_id (fun y => ⟨(S.proj y).property,trivial⟩)
  contMDiff_invFun := contMDiff_subtype_val

private def finiteTopRangeDiffeomorphism (T : BlowupTower X D) (U : Opens X) :
    CMfd.of (n := n) (openPreimage (restrict (⊤ : Opens X) T) (nestedOpens (⊤ : Opens X) (U ⊓ (⊤ : Opens X))))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U) := by
  have hf : ∀ y : openPreimage (restrict (⊤ : Opens X) T) (nestedOpens (⊤ : Opens X) (U ⊓ (⊤ : Opens X))),
      y.val.val ∈ openPreimage T U := by
    intro y
    have hy : ((restrict (⊤ : Opens X) T).proj y.val).val ∈ U := y.property.1
    rw [proj_restrict] at hy
    exact hy
  have hi : ∀ y : openPreimage T U,
      (⟨y.val,show T.proj y.val ∈ (⊤ : Opens X) from trivial⟩ : openPreimage T (⊤ : Opens X)) ∈
        openPreimage (restrict (⊤ : Opens X) T) (nestedOpens (⊤ : Opens X) (U ⊓ (⊤ : Opens X))) := by
    intro y
    change ((restrict (⊤ : Opens X) T).proj _).val ∈ U ⊓ (⊤ : Opens X)
    rw [proj_restrict]
    exact ⟨y.property,trivial⟩
  exact {
    toFun y := ⟨y.val.val,hf y⟩
    invFun y := ⟨⟨y.val,trivial⟩,hi y⟩
    left_inv _ := rfl
    right_inv _ := rfl
    contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
      (contMDiff_subtype_val.comp contMDiff_subtype_val) hf
    contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk
      (BlowupRestrictOpen.contMDiff_opens_mk (V := openPreimage T (⊤ : Opens X))
        contMDiff_subtype_val (fun _ => trivial)) hi }

section FiniteHistory
variable (M : MarkedIdeal n X) (hM : IsInvDomain n M) (T : BlowupTower X D)
  (hc : IsCanonical M ((canonicalInvariant n).inv M) T) (hr : IsGeoResolution M T)

private def finiteTerminalRawComparison (i : X) :
    CMfd.of (n := n) (openPreimage ((actualLocalTerminalAtlas M hM).tower i)
      (nestedOpens ((actualLocalTerminalAtlas M hM).openSet i)
        (((actualLocalTerminalAtlas M hM).openSet i) ⊓ (⊤ : Opens X))))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
    CMfd.of (n := n) (openPreimage (restrict (⊤ : Opens X) T)
      (nestedOpens (⊤ : Opens X) (((actualLocalTerminalAtlas M hM).openSet i) ⊓ (⊤ : Opens X)))) :=
  let hT := original_terminal_open_history_data M hM T hc hr (⊤ : Opens X)
  commonOpenTerminalComparison M hM inf_le_left inf_le_right
    ((actualLocalTerminalAtlas M hM).tower i) (restrict (⊤ : Opens X) T)
    ((actualLocalTerminalAtlas M hM).canonical i) hT.2.1
    ((actualLocalTerminalAtlas M hM).terminal i) hT.2.2

/-- Real local final space to the literal finite whole projection preimage. -/
def finiteTerminalLocalComparison (i : X) :
    (actualLocalTerminalAtlas M hM).finalSpace i
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T ((actualLocalTerminalAtlas M hM).openSet i)) :=
  ((fullLocalFinalDiffeomorphism ((actualLocalTerminalAtlas M hM).tower i)).trans
    (finiteTerminalRawComparison M hM T hc hr i)).trans
      (finiteTopRangeDiffeomorphism T ((actualLocalTerminalAtlas M hM).openSet i))

theorem finiteTerminalLocalComparison_proj (i : X) (y : (actualLocalTerminalAtlas M hM).finalSpace i) :
    T.proj (finiteTerminalLocalComparison M hM T hc hr i y).val=
      (((actualLocalTerminalAtlas M hM).tower i).proj y).val := by
  let hT := original_terminal_open_history_data M hM T hc hr (⊤ : Opens X)
  have hp := commonOpenTerminalComparison_proj M hM inf_le_left
    inf_le_right ((actualLocalTerminalAtlas M hM).tower i) (restrict (⊤ : Opens X) T)
    ((actualLocalTerminalAtlas M hM).canonical i) hT.2.1
    ((actualLocalTerminalAtlas M hM).terminal i) hT.2.2
    (fullLocalFinalDiffeomorphism ((actualLocalTerminalAtlas M hM).tower i) y)
  rw [proj_restrict] at hp
  exact hp

theorem finiteTerminalLocalComparison_transition (i j : X) (y : originalTerminalOverlapOpen M hM i j) :
    (finiteTerminalLocalComparison M hM T hc hr j (originalTerminalTransition M hM i j y).val).val=
      (finiteTerminalLocalComparison M hM T hc hr i y.val).val := by
  let A := actualLocalTerminalAtlas M hM
  let R := restrict (⊤ : Opens X) T
  let hR := original_terminal_open_history_data M hM T hc hr (⊤ : Opens X)
  let yp : openPreimage (A.tower i) (nestedOpens (A.openSet i) (A.openSet i ⊓ A.openSet j)) :=
    ⟨y.val,⟨((A.tower i).proj y.val).property,y.property⟩⟩
  obtain ⟨z,hz,hco⟩ := original_pairwise_terminal_triple_transition M hM
    (A.openSet i) (A.openSet j) (⊤ : Opens X) (A.tower i) (A.tower j) R
    (A.canonical i) (A.canonical j) hR.2.1 (A.terminal i) (A.terminal j) hR.2.2 yp trivial
  have hz' : z.val=(originalTerminalTransition M hM i j y).val :=
    hz.trans (originalTerminalTransition_pair_point M hM i j y).symm
  have he := congrArg (fun q : openPreimage T (⊤ : Opens X) => q.val) hco
  change ((finiteTerminalRawComparison M hM T hc hr j z).val).val=
    ((finiteTerminalRawComparison M hM T hc hr i
      (fullLocalFinalDiffeomorphism (A.tower i) y.val)).val).val at he
  change ((finiteTerminalRawComparison M hM T hc hr j
    (fullLocalFinalDiffeomorphism (A.tower j) (originalTerminalTransition M hM i j y).val)).val).val=_
  have hzp : z=fullLocalFinalDiffeomorphism (A.tower j) (originalTerminalTransition M hM i j y).val :=
    Subtype.ext hz'
  rw [← hzp]
  exact he


private theorem contMDiffAt_of_open_restriction {m : ℕ} {A : CMfd.{u} n} {B : CMfd.{u} m}
    (U : Opens A) (g : A → B)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ (g ∘ (Subtype.val : U → A)))
    (x : U) : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ g x.val := by
  exact contMDiffAt_subtype_iff.mp (hg x)

private def finiteTerminalLocalMap (i : X) : ContinuousMap ((actualLocalTerminalAtlas M hM).finalSpace i) D :=
  ⟨fun y => (finiteTerminalLocalComparison M hM T hc hr i y).val,
    continuous_subtype_val.comp (finiteTerminalLocalComparison M hM T hc hr i).contMDiff.continuous⟩

private theorem finiteTerminalLocalMap_compatible (ij : X × X) :
    (originalTerminalGlueData M hM).toGlueData.diagram.fst ij ≫
      TopCat.ofHom (finiteTerminalLocalMap M hM T hc hr ij.1)=
    (originalTerminalGlueData M hM).toGlueData.diagram.snd ij ≫
      TopCat.ofHom (finiteTerminalLocalMap M hM T hc hr ij.2) := by
  rcases ij with ⟨i,j⟩
  ext y
  exact (finiteTerminalLocalComparison_transition M hM T hc hr i j y).symm

/-- The literal original gluing descends to this actual finite history. -/
def finiteTerminalToHistory : ContinuousMap (originalTerminalGluedSpace M hM) D :=
  (Multicoequalizer.desc (originalTerminalGlueData M hM).toGlueData.diagram (TopCat.of D)
    (fun i => TopCat.ofHom (finiteTerminalLocalMap M hM T hc hr i))
    (finiteTerminalLocalMap_compatible M hM T hc hr)).hom

theorem finiteTerminalToHistory_local (i : X) (y : (actualLocalTerminalAtlas M hM).finalSpace i) :
    finiteTerminalToHistory M hM T hc hr (originalTerminalLocalInclusion M hM i y)=
      (finiteTerminalLocalComparison M hM T hc hr i y).val := by
  have h := Multicoequalizer.π_desc (originalTerminalGlueData M hM).toGlueData.diagram (TopCat.of D)
    (fun i => TopCat.ofHom (finiteTerminalLocalMap M hM T hc hr i))
    (finiteTerminalLocalMap_compatible M hM T hc hr) i
  exact congrArg (fun f : (originalTerminalGlueData M hM).U i ⟶ TopCat.of D => f y) h

theorem finiteTerminalToHistory_proj (z : originalTerminalManifold M hM) :
    T.proj (finiteTerminalToHistory M hM T hc hr z)=originalTerminalGluedProjection M hM z := by
  obtain ⟨i,y,rfl⟩ := originalTerminalLocalInclusion_jointly_surjective M hM z
  rw [finiteTerminalToHistory_local,finiteTerminalLocalComparison_proj,originalTerminalGluedProjection_local]
  rfl

theorem finiteTerminalToHistory_bijective : Bijective (finiteTerminalToHistory M hM T hc hr) := by
  constructor
  · intro z w he
    have hp : originalTerminalGluedProjection M hM z=originalTerminalGluedProjection M hM w :=
      (finiteTerminalToHistory_proj M hM T hc hr z).symm.trans
        ((congrArg T.proj he).trans (finiteTerminalToHistory_proj M hM T hc hr w))
    let i := originalTerminalGluedProjection M hM z
    have hz : z ∈ range (originalTerminalLocalInclusion M hM i) := by
      rw [originalTerminalLocalInclusion_range]
      exact (actualLocalTerminalAtlas M hM).point_mem i
    have hw : w ∈ range (originalTerminalLocalInclusion M hM i) := by
      rw [originalTerminalLocalInclusion_range]
      change originalTerminalGluedProjection M hM w ∈ (actualLocalTerminalAtlas M hM).openSet i
      rw [← hp]
      exact (actualLocalTerminalAtlas M hM).point_mem i
    obtain ⟨y,hy⟩ := hz
    obtain ⟨v,hv⟩ := hw
    have hvals : (finiteTerminalLocalComparison M hM T hc hr i y).val=
        (finiteTerminalLocalComparison M hM T hc hr i v).val := by
      rw [← finiteTerminalToHistory_local,← finiteTerminalToHistory_local]
      exact (congrArg (finiteTerminalToHistory M hM T hc hr) hy).trans
        (he.trans (congrArg (finiteTerminalToHistory M hM T hc hr) hv).symm)
    exact hy.symm.trans ((congrArg (originalTerminalLocalInclusion M hM i)
      ((finiteTerminalLocalComparison M hM T hc hr i).injective (Subtype.ext hvals))).trans hv)
  · intro d
    let i := T.proj d
    let q : openPreimage T ((actualLocalTerminalAtlas M hM).openSet i) :=
      ⟨d,(actualLocalTerminalAtlas M hM).point_mem i⟩
    refine ⟨originalTerminalLocalInclusion M hM i
      ((finiteTerminalLocalComparison M hM T hc hr i).symm q),?_⟩
    rw [finiteTerminalToHistory_local,Diffeomorph.apply_symm_apply]

private def finiteTerminalEquiv : originalTerminalManifold M hM ≃ D :=
  Equiv.ofBijective (finiteTerminalToHistory M hM T hc hr) (finiteTerminalToHistory_bijective M hM T hc hr)

theorem finiteTerminalToHistory_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (finiteTerminalToHistory M hM T hc hr : originalTerminalManifold M hM → D) := by
  intro z
  obtain ⟨i,y,rfl⟩ := originalTerminalLocalInclusion_jointly_surjective M hM z
  let U := originalTerminalLocalRangeOpen M hM i
  have he : (finiteTerminalToHistory M hM T hc hr) ∘ (Subtype.val : U → originalTerminalManifold M hM)=
      (Subtype.val : openPreimage T ((actualLocalTerminalAtlas M hM).openSet i) → D) ∘
        (finiteTerminalLocalComparison M hM T hc hr i) ∘ (originalTerminalLocalBiholomorphism M hM i).symm := by
    funext q
    have hi : originalTerminalLocalInclusion M hM i
        ((originalTerminalLocalBiholomorphism M hM i).symm q)=q.val :=
      originalTerminalLocalHomeomorphism_inverse_point M hM i q
    exact (congrArg (finiteTerminalToHistory M hM T hc hr) hi).symm.trans
      (finiteTerminalToHistory_local M hM T hc hr i _)
  have hh : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      ((finiteTerminalToHistory M hM T hc hr) ∘ (Subtype.val : U → originalTerminalManifold M hM)) := by
    rw [he]
    exact contMDiff_subtype_val.comp
      ((finiteTerminalLocalComparison M hM T hc hr i).contMDiff.comp
        (originalTerminalLocalBiholomorphism M hM i).symm.contMDiff)
  exact contMDiffAt_of_open_restriction U _ hh ⟨originalTerminalLocalInclusion M hM i y,⟨y,rfl⟩⟩

theorem finiteTerminalEquiv_symm_local (i : X)
    (q : openPreimage T ((actualLocalTerminalAtlas M hM).openSet i)) :
    (finiteTerminalEquiv M hM T hc hr).symm q.val=
      originalTerminalLocalInclusion M hM i ((finiteTerminalLocalComparison M hM T hc hr i).symm q) := by
  apply (finiteTerminalEquiv M hM T hc hr).injective
  rw [Equiv.apply_symm_apply]
  change q.val=finiteTerminalToHistory M hM T hc hr _
  rw [finiteTerminalToHistory_local,Diffeomorph.apply_symm_apply]

private theorem finiteTerminalEquiv_symm_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (finiteTerminalEquiv M hM T hc hr).symm := by
  intro d
  let i := T.proj d
  let U := openPreimage T ((actualLocalTerminalAtlas M hM).openSet i)
  have he : (finiteTerminalEquiv M hM T hc hr).symm ∘ (Subtype.val : U → D)=
      (originalTerminalLocalInclusion M hM i) ∘ (finiteTerminalLocalComparison M hM T hc hr i).symm :=
    funext (finiteTerminalEquiv_symm_local M hM T hc hr i)
  have hh : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      ((finiteTerminalEquiv M hM T hc hr).symm ∘ (Subtype.val : U → D)) := by
    rw [he]
    exact (originalTerminalLocalInclusion_contMDiff M hM i).comp
      (finiteTerminalLocalComparison M hM T hc hr i).symm.contMDiff
  exact contMDiffAt_of_open_restriction U _ hh ⟨d,(actualLocalTerminalAtlas M hM).point_mem i⟩

/-- The original global manifold, with its actual fixed atlas, is identified
with this actual finite terminal history; both regularities are proved. -/
def originalTerminalFiniteBiholomorphism :
    originalTerminalManifold M hM ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ D where
  toEquiv := finiteTerminalEquiv M hM T hc hr
  contMDiff_toFun := finiteTerminalToHistory_contMDiff M hM T hc hr
  contMDiff_invFun := finiteTerminalEquiv_symm_contMDiff M hM T hc hr

theorem originalTerminalFiniteBiholomorphism_proj (z : originalTerminalManifold M hM) :
    T.proj (originalTerminalFiniteBiholomorphism M hM T hc hr z)=originalTerminalGluedProjection M hM z :=
  finiteTerminalToHistory_proj M hM T hc hr z

end FiniteHistory
end
end Hironaka.HironakaOriginalTerminalFiniteIdentification
