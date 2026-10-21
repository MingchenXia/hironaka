/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalNonpureCanonicalResolution
import Hironaka.Resolution.HironakaEmbeddedResolution

/-!
# The original full-dimensional elementary identity branch

Actual full-dimensional irreducible carriers are open and closed. Their
identity resolution and its arbitrary smooth Cartesian pullback retain the
entire initial boundary, with no nonzero vanishing-ideal domain assertion.
Blueprint: `hironaka-original-full-dimension-identity-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFullDimensionIdentity
noncomputable section
open Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  NormalCrossings BlowupTowers HironakaAdmissibleSequence
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionOrderedChoiceBaseChange
variable {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m}

/-- An open carrier uses no coordinate equations in the actual SNC coordinates. -/
theorem isTransverse_of_isOpen (W : Set X) (hW : IsOpen W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) : IsTransverse n W E := by
  have hu : IsTransverse n (univ : Set X) E := by
    intro x _
    obtain ⟨S,⟨Φ,hsrc,h0,hcoord⟩,hcard,_hinj⟩ := hE.2 x
    refine ⟨∅,S,⟨Φ,hsrc,h0,?_⟩,?_⟩
    · rintro (_ | i) hx y hy hyΦ
      · simp [coordSubspace]
      · exact hcoord i hx hy hyΦ
    · intro i hi
      exact ⟨hcard i hi,Finset.disjoint_empty_right _⟩
  apply CodimOneAdmissibleAlong.isTransverse_of_forall_eventually
  intro x hx
  refine ⟨univ,mem_univ x,?_,hu⟩
  filter_upwards [hW.mem_nhds hx] with y hy
  exact iff_of_true hy (mem_univ y)

private theorem regular_of_isOpen (W : Set X) (hW : IsOpen W) (x : X) (hx : x ∈ W) :
    RegularAtDim (n := n) W x n :=
  RegularPointDimension.regularAtDim_of_inter_eq hW hx (by simp)
    (AnalyticIrreducibleComponents.regularAtDim_univ x)

/-- Genuine full-dimensional input supplies the complete identity branch and
its SAME actual Cartesian smooth pullback, including the whole boundary. -/
theorem full_dimension_identity_smooth_square
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hdim : V.dim = n)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    let T : BlowupTower X X := .refl
    T.length = 0 ∧ strictTransform n T.proj V.carrier = V.carrier ∧
      IsClosedConnectedSubmanifold n (strictTransform n T.proj V.carrier) V.dim ∧
      IsTransverse n (strictTransform n T.proj V.carrier) E ∧
      HasNormalCrossings n (strictTransform n T.proj V.carrier) E ∧
      singularLocus V = ∅ ∧ exceptionalLocus n T.proj = ∅ ∧
      IsAdmissibleBlowupSequence n X E ∅ X T.proj E ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ Surjective T.proj ∧ IsIsomorphismOver n T.proj (univ : Set X) ∧
      ∀ {m : ℕ} (Y : CMfd.{u} m) (b : Y → X)
        (_hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b),
        let Q : BlowupTower Y Y := .refl
        let E' := E.map (b ⁻¹' ·)
        IsActualTowerPullback b Q T b ∧ Q.length = 0 ∧ IsSNCDivisor m E' ∧
          strictTransform m Q.proj (b ⁻¹' V.carrier) = b ⁻¹' V.carrier ∧
          strictTransform m Q.proj (b ⁻¹' V.carrier) = b ⁻¹' strictTransform n T.proj V.carrier ∧
          IsClosedSubmanifold m (strictTransform m Q.proj (b ⁻¹' V.carrier)) ∧
          (∀ y ∈ strictTransform m Q.proj (b ⁻¹' V.carrier),
            RegularAtDim (n := m) (strictTransform m Q.proj (b ⁻¹' V.carrier)) y m) ∧
          IsTransverse m (strictTransform m Q.proj (b ⁻¹' V.carrier)) E' ∧
          HasNormalCrossings m (strictTransform m Q.proj (b ⁻¹' V.carrier)) E' ∧
          exceptionalLocus m Q.proj = ∅ ∧
          IsAdmissibleBlowupSequence m Y E' ∅ Y Q.proj E' ∧
          ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel m) ∞ Q.proj ∧
          IsProperMap Q.proj ∧ Surjective Q.proj ∧ IsIsomorphismOver m Q.proj (univ : Set Y) ∧
          HolomorphicSquarePullback b b Q.proj T.proj := by
  dsimp only
  have hV := EmbeddedFromResolution.isClosedConnectedSubmanifold_of_dim_eq V hdim
  have hVo : IsOpen V.carrier :=
    AnalyticIrreducibleComponents.isOpen_of_forall_regularAtDim_self hV.2.2
  have hst : strictTransform n (BlowupTower.refl : BlowupTower X X).proj V.carrier = V.carrier := by
    change strictTransform n (id : X → X) V.carrier = V.carrier
    simp [strictTransform,exceptionalLocus_id,V.isClosed_carrier.closure_eq]
  have htrans := isTransverse_of_isOpen V.carrier hVo E hE
  have hiso : IsIsomorphismOver n (id : X → X) (univ : Set X) := by
    simpa using HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      (IsBlowupSequence.refl (n := n) (X := X)) (A := (∅ : Set X)) (by simp [exceptionalLocus_id])
  refine ⟨rfl,hst,?_,?_,?_,?_,exceptionalLocus_id,IsAdmissibleBlowupSequence.refl,
    contMDiff_id,isProperMap_id,surjective_id,hiso,?_⟩
  · simpa only [hst,hdim] using hV
  · simpa only [hst] using htrans
  · simpa only [hst] using htrans.hasNormalCrossings
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply hx.2
    change RegularAtDim (n := n) V.carrier x V.dim
    simpa only [hdim] using hV.2.2 x hx.1
  · intro m Y b hb
    have hWo := hVo.preimage hb.contMDiff.continuous
    have hWc := V.isClosed_carrier.preimage hb.contMDiff.continuous
    have hQst : strictTransform m (BlowupTower.refl : BlowupTower Y Y).proj (b ⁻¹' V.carrier) = b ⁻¹' V.carrier := by
      change strictTransform m (id : Y → Y) (b ⁻¹' V.carrier) = b ⁻¹' V.carrier
      rw [strictTransform,exceptionalLocus_id,Set.preimage_id,Set.sdiff_empty,hWc.closure_eq]
    have hE' := HironakaSmoothSubmersionNormalCrossings.isSNCDivisor_preimage_submersion hb E hE
    have ht := isTransverse_of_isOpen (b ⁻¹' V.carrier) hWo _ hE'
    have hr := regular_of_isOpen (b ⁻¹' V.carrier) hWo
    have ha : IsActualTowerPullback b (BlowupTower.refl : BlowupTower Y Y)
        (BlowupTower.refl : BlowupTower X X) b := .refl hb
    have hi : IsIsomorphismOver m (id : Y → Y) (univ : Set Y) := by
      simpa using HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
        (IsBlowupSequence.refl (n := m) (X := Y)) (A := (∅ : Set Y)) (by simp [exceptionalLocus_id])
    refine ⟨ha,rfl,hE',hQst,?_,?_,?_,?_,?_,exceptionalLocus_id,
      IsAdmissibleBlowupSequence.refl,contMDiff_id,isProperMap_id,surjective_id,hi,ha.universal⟩
    · rw [hQst,hst]
    · rw [hQst]
      exact ⟨hWc,fun y hy => ⟨m,hr y hy⟩⟩
    · simpa only [hQst] using hr
    · simpa only [hQst] using ht
    · simpa only [hQst] using ht.hasNormalCrossings
end
end Hironaka.HironakaOriginalFullDimensionIdentity
