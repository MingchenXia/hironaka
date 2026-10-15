/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionAdaptedProductCoordinates
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeControlledTower
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionRelativeDifferentialIdeals
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupFlatCoordinates HironakaSmoothSubmersionAdaptedProductCoordinates
  DerivativeIdealAlong DerivativeIdealAlongCoherent HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeOrder
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionGermIdealColon
  HironakaSmoothSubmersionComposition GermIdealPullbackCalculus GiraudAlong
  RelativePrincipalizationSpan InvertibleIdealQuotient HomogenizedIdealAlong
  HomogenizedEquivalence MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
  CoefficientIdeal HomogenizedGlueing
noncomputable section

def actualTargetProjectionLinear (n t : ℕ) : ComplexModel (n+t) →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.snd ℂ (ComplexModel t) (ComplexModel n)).comp
    (fibreFirstSplit n t).toContinuousLinearMap

theorem actualTargetProjectionLinear_apply (n t : ℕ) (w : ComplexModel (n+t)) :
    actualTargetProjectionLinear n t w = adaptedTargetProjection n t w := rfl

def actualTargetIndex (n t : ℕ) (j : Fin n) : Fin (n+t) := ⟨t+j.val,by omega⟩

theorem rotateBlocks_target_eq (n t : ℕ) (j : Fin n) :
    rotateBlocks n t (Fin.castAdd t j) = actualTargetIndex n t j := by
  apply Fin.ext
  exact rotateBlocks_target n t j

theorem actualTargetProjectionLinear_single_target (n t : ℕ) (j : Fin n) :
    actualTargetProjectionLinear n t (EuclideanSpace.single (actualTargetIndex n t j) (1 : ℂ)) =
      EuclideanSpace.single j (1 : ℂ) := by
  ext i
  rw [actualTargetProjectionLinear_apply,adaptedTargetProjection_apply,rotateBlocks_target_eq]
  simp [actualTargetIndex,Fin.ext_iff]

theorem actualTargetProjectionLinear_single_fibre (n t : ℕ) (i : Fin (n+t)) (hi : i.val < t) :
    actualTargetProjectionLinear n t (EuclideanSpace.single i (1 : ℂ)) = 0 := by
  ext j
  rw [actualTargetProjectionLinear_apply,adaptedTargetProjection_apply,rotateBlocks_target_eq]
  have hij : actualTargetIndex n t j ≠ i := fun h => by
    have hv := congrArg Fin.val h
    change t+j.val = i.val at hv
    omega
  simp [hij]

theorem exists_targetIndex_of_fibre_le (n t : ℕ) (i : Fin (n+t)) (hi : t ≤ i.val) :
    ∃ j : Fin n, actualTargetIndex n t j = i := by
  refine ⟨⟨i.val-t,by omega⟩,?_⟩
  apply Fin.ext
  change t+(i.val-t) = i.val
  omega

variable {n t : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} (n+t)} {f : Y → X} {y : Y}

theorem adaptedCoordinates_inverse_projection
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (w : ComplexModel (n+t)) (hw : w ∈ (adaptedCoordinates hf Φ h0).target) :
    f (flatInv (adaptedCoordinates hf Φ h0) w) =
      flatInv Φ (actualTargetProjectionLinear n t w) := by
  let Ψ := adaptedCoordinates hf Φ h0
  obtain ⟨hsrc,hzero,hd⟩ := adaptedCoordinates_dictionary hf Φ h0
  let z := flatInv Ψ w
  obtain ⟨hz,hzcoord⟩ := flatInverse_mem Ψ hw hsrc
  change Ψ.toFun (chartAt (ComplexModel (n+t)) y z) = w at hzcoord
  have hforward := hd z hz
  have hcoord : actualTargetProjectionLinear n t w =
      Φ.toFun (chartAt (ComplexModel n) (f y) (f z)) := by
    ext j
    rw [actualTargetProjectionLinear_apply,adaptedTargetProjection_apply]
    have hh := hforward.2 j
    change Ψ.toFun (chartAt (ComplexModel (n+t)) y z)
      (rotateBlocks n t (Fin.castAdd t j)) = Φ.toFun (chartAt (ComplexModel n) (f y) (f z)) j at hh
    rw [hzcoord] at hh
    exact hh
  change f z = _
  rw [hcoord]
  change f z = (chartAt (ComplexModel n) (f y)).symm
    (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (f y) (f z))))
  rw [Φ.left_inv _ hforward.1.2]
  exact ((chartAt (ComplexModel n) (f y)).left_inv hforward.1.1).symm

theorem adaptedCoordinates_flatMap_projection
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (z : Y) (hz : z ∈ flatDomain (adaptedCoordinates hf Φ h0)) :
    actualTargetProjectionLinear n t (flatMap (adaptedCoordinates hf Φ h0) z) = flatMap Φ (f z) := by
  ext j
  rw [actualTargetProjectionLinear_apply,adaptedTargetProjection_apply]
  exact (adaptedCoordinates_dictionary hf Φ h0).2.2 z hz |>.2 j

theorem adaptedCoordinates_fderiv_original_comp
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target)
    (F : X → ℂ) (z : Y) (hz : z ∈ flatDomain (adaptedCoordinates hf Φ h0))
    (hF : HolomorphicAt n F (f z)) :
    fderiv ℂ ((F ∘ f) ∘ flatInv (adaptedCoordinates hf Φ h0))
        (flatMap (adaptedCoordinates hf Φ h0) z) =
      (fderiv ℂ (F ∘ flatInv Φ) (flatMap Φ (f z))).comp (actualTargetProjectionLinear n t) := by
  let Ψ := adaptedCoordinates hf Φ h0
  have hd := (adaptedCoordinates_dictionary hf Φ h0).2.2 z hz
  have heq : ((F ∘ f) ∘ flatInv Ψ) =ᶠ[𝓝 (flatMap Ψ z)]
      (F ∘ flatInv Φ) ∘ actualTargetProjectionLinear n t := by
    filter_upwards [Ψ.isOpen_target.mem_nhds (flatMap_mem_target hz)] with w hw
    change F (f (flatInv Ψ w)) = F (flatInv Φ (actualTargetProjectionLinear n t w))
    rw [adaptedCoordinates_inverse_projection hf Φ h0 w hw]
  have hFd : DifferentiableAt ℂ (F ∘ flatInv Φ) (flatMap Φ (f z)) :=
    differentiableAt_comp_flatInv (flatMap_mem_target hd.1) hΦsrc
      (by rw [flatInv_flatMap hd.1]; exact hF)
  have hFd' : DifferentiableAt ℂ (F ∘ flatInv Φ)
      (actualTargetProjectionLinear n t (flatMap Ψ z)) := by
    rw [adaptedCoordinates_flatMap_projection hf Φ h0 z hz]
    exact hFd
  have hchain := (hFd'.hasFDerivAt.comp (flatMap Ψ z)
    (actualTargetProjectionLinear n t).hasFDerivAt).fderiv
  rw [adaptedCoordinates_flatMap_projection hf Φ h0 z hz] at hchain
  rw [heq.fderiv_eq]
  exact hchain

theorem adaptedCoordinates_flatPartial_target
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target)
    (F : X → ℂ) (z : Y)
    (hz : z ∈ flatDomain (adaptedCoordinates (hf.isSubmersionAt y) Φ h0))
    (hF : HolomorphicAt n F (f z)) (j : Fin n) :
    flatPartial (adaptedCoordinates (hf.isSubmersionAt y) Φ h0) (actualTargetIndex n t j) (F ∘ f) z =
      flatPartial Φ j F (f z) := by
  have hd := (adaptedCoordinates_dictionary (hf.isSubmersionAt y) Φ h0).2.2 z hz
  have hFp : HolomorphicAt (n+t) (F ∘ f) z :=
    hF.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiff.contMDiffAt)
  rw [flatPartial_eq hz hFp,flatPartial_eq hd.1 hF,
    adaptedCoordinates_fderiv_original_comp (hf.isSubmersionAt y) Φ h0 hΦsrc F z hz hF,
    ContinuousLinearMap.comp_apply,actualTargetProjectionLinear_single_target]

theorem adaptedCoordinates_flatPartial_fibre
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target)
    (F : X → ℂ) (z : Y)
    (hz : z ∈ flatDomain (adaptedCoordinates (hf.isSubmersionAt y) Φ h0))
    (hF : HolomorphicAt n F (f z)) (i : Fin (n+t)) (hi : i.val < t) :
    flatPartial (adaptedCoordinates (hf.isSubmersionAt y) Φ h0) i (F ∘ f) z = 0 := by
  have hFp : HolomorphicAt (n+t) (F ∘ f) z :=
    hF.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiff.contMDiffAt)
  rw [flatPartial_eq hz hFp,
    adaptedCoordinates_fderiv_original_comp (hf.isSubmersionAt y) Φ h0 hΦsrc F z hz hF,
    ContinuousLinearMap.comp_apply,actualTargetProjectionLinear_single_fibre n t i hi,map_zero]

theorem adaptedCoordinates_flatCoord_target
    (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f y)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (z : Y) (hz : z ∈ flatDomain (adaptedCoordinates hf Φ h0)) (j : Fin n) :
    flatCoord (adaptedCoordinates hf Φ h0) (actualTargetIndex n t j) z = flatCoord Φ j (f z) := by
  rw [← rotateBlocks_target_eq]
  exact (adaptedCoordinates_dictionary hf Φ h0).2.2 z hz |>.2 j

theorem holomorphicAt_derivFamilyAlong {r k : ℕ}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (G : Fin r → X → ℂ) {x : X} (hx : x ∈ flatDomain Φ)
    (hG : ∀ i, HolomorphicAt n (G i) x) (c : Fin r ⊕ Fin n ⊕ (Fin r × Fin n)) :
    HolomorphicAt n (derivFamilyAlong Φ k G c) x := by
  rcases c with i | j | ij
  · exact hG i
  · by_cases hj : k ≤ j.val
    · simpa [derivFamilyAlong,hj] using holomorphicAt_flatCoord Φ j hx
    · simpa [derivFamilyAlong,hj] using holomorphicAt_const (n := n) (x := x) (0 : ℂ)
  · by_cases hj : ij.2.val < k
    · simpa [derivFamilyAlong,hj] using holomorphicAt_flatPartial ij.2 hx (hG ij.1)
    · simpa [derivFamilyAlong,hj] using holomorphicAt_const (n := n) (x := x) (0 : ℂ)

theorem target_derivFamilyAlong_in_source_span {r k : ℕ}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target)
    (G : Fin r → X → ℂ) (z : Y)
    (hz : z ∈ flatDomain (adaptedCoordinates (hf.isSubmersionAt y) Φ h0))
    (hG : ∀ i, HolomorphicAt n (G i) (f z))
    (c : Fin r ⊕ Fin n ⊕ (Fin r × Fin n)) :
    IsInSpanAt (n := n+t)
      (· ∈ range (derivFamilyAlong (adaptedCoordinates (hf.isSubmersionAt y) Φ h0)
        (t+k) (fun i => G i ∘ f))) z (derivFamilyAlong Φ k G c ∘ f) := by
  let Ψ := adaptedCoordinates (hf.isSubmersionAt y) Φ h0
  have hGp : ∀ i, HolomorphicAt (n+t) (G i ∘ f) z := fun i =>
    (hG i).comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiff.contMDiffAt)
  have hself : ∀ d, IsInSpanAt (n := n+t) (· ∈ range (derivFamilyAlong Ψ (t+k)
      (fun i => G i ∘ f))) z (derivFamilyAlong Ψ (t+k) (fun i => G i ∘ f) d) :=
    fun d => isInSpanAt_self ⟨d,rfl⟩ (by
      rcases d with i | j | ij
      · exact hGp i
      · by_cases hj : t+k ≤ j.val
        · simpa [derivFamilyAlong,hj] using holomorphicAt_flatCoord Ψ j hz
        · simpa [derivFamilyAlong,hj] using holomorphicAt_const (n := n+t) (x := z) (0 : ℂ)
      · by_cases hj : ij.2.val < t+k
        · simpa [derivFamilyAlong,hj] using holomorphicAt_flatPartial ij.2 hz (hGp ij.1)
        · simpa [derivFamilyAlong,hj] using holomorphicAt_const (n := n+t) (x := z) (0 : ℂ))
  rcases c with i | j | ij
  · exact hself (.inl i)
  · by_cases hj : k ≤ j.val
    · have hshift : t+k ≤ (actualTargetIndex n t j).val := by
        change t+k ≤ t+j.val
        omega
      apply DerivativeIdeal.isInSpanAt_congr (hself (.inr (.inl (actualTargetIndex n t j))))
      filter_upwards [(isOpen_flatDomain Ψ).mem_nhds hz] with w hw
      simp only [derivFamilyAlong,hj,hshift,if_pos,Function.comp_apply]
      exact adaptedCoordinates_flatCoord_target (hf.isSubmersionAt y) Φ h0 w hw j
    · simpa only [derivFamilyAlong,if_neg hj,Function.comp_def] using
        (BlowupStrictIdeal.isInSpanAt_zero (n := n+t) (x := z)
          (S := (· ∈ range (derivFamilyAlong Ψ (t+k) (fun i => G i ∘ f)))))
  · by_cases hj : ij.2.val < k
    · have hshift : (actualTargetIndex n t ij.2).val < t+k := by
        change t+ij.2.val < t+k
        omega
      apply DerivativeIdeal.isInSpanAt_congr (hself (.inr (.inr (ij.1,actualTargetIndex n t ij.2))))
      filter_upwards [(isOpen_flatDomain Ψ).mem_nhds hz,hf.contMDiff.continuous.continuousAt.eventually (hG ij.1).eventually_nhds] with w hw hGw
      simp only [derivFamilyAlong,hj,hshift,if_pos,Function.comp_apply]
      exact adaptedCoordinates_flatPartial_target hf Φ h0 hΦsrc (G ij.1) w hw hGw ij.2
    · simpa only [derivFamilyAlong,if_neg hj,Function.comp_def] using
        (BlowupStrictIdeal.isInSpanAt_zero (n := n+t) (x := z)
          (S := (· ∈ range (derivFamilyAlong Ψ (t+k) (fun i => G i ∘ f)))))

theorem source_derivFamilyAlong_in_target_span {r k : ℕ}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target)
    (G : Fin r → X → ℂ) (z : Y)
    (hz : z ∈ flatDomain (adaptedCoordinates (hf.isSubmersionAt y) Φ h0))
    (hG : ∀ i, HolomorphicAt n (G i) (f z))
    (c : Fin r ⊕ Fin (n+t) ⊕ (Fin r × Fin (n+t))) :
    IsInSpanAt (n := n+t) (· ∈ range (fun d => derivFamilyAlong Φ k G d ∘ f)) z
      (derivFamilyAlong (adaptedCoordinates (hf.isSubmersionAt y) Φ h0)
        (t+k) (fun i => G i ∘ f) c) := by
  let Ψ := adaptedCoordinates (hf.isSubmersionAt y) Φ h0
  have hd := (adaptedCoordinates_dictionary (hf.isSubmersionAt y) Φ h0).2.2 z hz
  have hself : ∀ d, IsInSpanAt (n := n+t)
      (· ∈ range (fun d => derivFamilyAlong Φ k G d ∘ f)) z (derivFamilyAlong Φ k G d ∘ f) :=
    fun d => isInSpanAt_self ⟨d,rfl⟩
      ((holomorphicAt_derivFamilyAlong Φ G hd.1 hG d).comp_contMDiff
        (Eventually.of_forall fun _ => hf.contMDiff.contMDiffAt))
  rcases c with i | j | ij
  · exact hself (.inl i)
  · by_cases hj : t+k ≤ j.val
    · obtain ⟨j',hjj'⟩ := exists_targetIndex_of_fibre_le n t j (by omega)
      have hk : k ≤ j'.val := by
        have hv := congrArg Fin.val hjj'
        change t+j'.val = j.val at hv
        omega
      apply DerivativeIdeal.isInSpanAt_congr (hself (.inr (.inl j')))
      filter_upwards [(isOpen_flatDomain Ψ).mem_nhds hz] with w hw
      simp only [derivFamilyAlong,if_pos hj,if_pos hk,Function.comp_apply]
      rw [← hjj']
      exact (adaptedCoordinates_flatCoord_target (hf.isSubmersionAt y) Φ h0 w hw j').symm
    · simpa only [derivFamilyAlong,if_neg hj] using
        (BlowupStrictIdeal.isInSpanAt_zero (n := n+t) (x := z)
          (S := (· ∈ range (fun d => derivFamilyAlong Φ k G d ∘ f))))
  · by_cases hj : ij.2.val < t+k
    · by_cases ht : ij.2.val < t
      · apply DerivativeIdeal.isInSpanAt_congr
          (BlowupStrictIdeal.isInSpanAt_zero (n := n+t) (x := z)
            (S := (· ∈ range (fun d => derivFamilyAlong Φ k G d ∘ f))))
        filter_upwards [(isOpen_flatDomain Ψ).mem_nhds hz,
          hf.contMDiff.continuous.continuousAt.eventually (hG ij.1).eventually_nhds] with w hw hGw
        simp only [derivFamilyAlong,if_pos hj]
        exact (adaptedCoordinates_flatPartial_fibre hf Φ h0 hΦsrc (G ij.1) w hw hGw ij.2 ht).symm
      · obtain ⟨j',hjj'⟩ := exists_targetIndex_of_fibre_le n t ij.2 (by omega)
        have hk : j'.val < k := by
          have hv := congrArg Fin.val hjj'
          change t+j'.val = ij.2.val at hv
          omega
        apply DerivativeIdeal.isInSpanAt_congr (hself (.inr (.inr (ij.1,j'))))
        filter_upwards [(isOpen_flatDomain Ψ).mem_nhds hz,
          hf.contMDiff.continuous.continuousAt.eventually (hG ij.1).eventually_nhds] with w hw hGw
        simp only [derivFamilyAlong,if_pos hj,if_pos hk,Function.comp_apply]
        rw [← hjj']
        exact (adaptedCoordinates_flatPartial_target hf Φ h0 hΦsrc (G ij.1) w hw hGw j').symm
    · simpa only [derivFamilyAlong,if_neg hj] using
        (BlowupStrictIdeal.isInSpanAt_zero (n := n+t) (x := z)
          (S := (· ∈ range (fun d => derivFamilyAlong Φ k G d ∘ f))))

theorem derivFamilyAlong_pullback_spans_iff {r k : ℕ}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (h0 : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target)
    (G : Fin r → X → ℂ) (z : Y)
    (hz : z ∈ flatDomain (adaptedCoordinates (hf.isSubmersionAt y) Φ h0))
    (hG : ∀ i, HolomorphicAt n (G i) (f z)) (F : Y → ℂ) :
    IsInSpanAt (n := n+t) (· ∈ range (fun d => derivFamilyAlong Φ k G d ∘ f)) z F ↔
      IsInSpanAt (n := n+t) (· ∈ range (derivFamilyAlong
        (adaptedCoordinates (hf.isSubmersionAt y) Φ h0) (t+k) (fun i => G i ∘ f))) z F := by
  constructor
  · intro h
    apply IsInSpanAt.trans ?_ h
    rintro _ ⟨c,rfl⟩
    exact target_derivFamilyAlong_in_source_span hf Φ h0 hΦsrc G z hz hG c
  · intro h
    apply IsInSpanAt.trans ?_ h
    rintro _ ⟨c,rfl⟩
    exact source_derivFamilyAlong_in_target_span hf Φ h0 hΦsrc G z hz hG c

theorem pullback_derivIdealAlong_add
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (I : GermIdeal n X) (hI : I.IsCoherent) (N : Set X) (hN : IsClosedSubmanifold n N) :
    GermIdeal.pullback (m := n+t) f (derivIdealAlong N I) =
      derivIdealAlong (f ⁻¹' N) (GermIdeal.pullback (m := n+t) f I) := by
  classical
  have hNp := isClosedSubmanifold_preimage_submersion hf hN
  have hIp := isCoherent_pullback hf.contMDiff hI
  have hDp := isCoherent_derivIdealAlong hIp hNp
  have hD := isCoherent_derivIdealAlong hI hN
  have hfat : ∀ {z : Y}, ∀ᶠ w in 𝓝 z,
      ContMDiffAt 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ f w :=
    fun {_} => Eventually.of_forall fun _ => hf.contMDiff.contMDiffAt
  ext y F
  by_cases hyN : f y ∈ N
  · obtain ⟨k,_,_,Φ,hΦsrc,h0,hflat⟩ := hN.2 (f y) hyN
    obtain ⟨U,hU,hyU,r,G,hG,hgen⟩ := hI (f y)
    let W := U ∩ flatDomain Φ
    have hW : IsOpen W := hU.inter (isOpen_flatDomain Φ)
    have hyW : f y ∈ W := ⟨hyU,mem_flatDomain_self Φ⟩
    have hGh : ∀ i z, z ∈ W → HolomorphicAt n (G i) z :=
      fun i z hz => holomorphicAt_of_mdifferentiableOn hU (hG i) hz.1
    let Ψ := adaptedCoordinates (hf.isSubmersionAt y) Φ h0
    have hΨsrc := (adaptedCoordinates_dictionary (hf.isSubmersionAt y) Φ h0).1
    have hΨflat : ∀ {z : Y}, z ∈ (chartAt (ComplexModel (n+t)) y).source →
        chartAt (ComplexModel (n+t)) y z ∈ Ψ.source →
        (z ∈ f ⁻¹' N ↔ Ψ.toFun (chartAt (ComplexModel (n+t)) y z) ∈
          complexCoordinatePlane (n+t) (t+k)) := by
      intro z hz hzΨ
      exact adaptedCoordinates_whole_centre (hf.isSubmersionAt y) Φ h0 N k
        (fun w hw => hflat hw.1 hw.2) z ⟨hz,hzΨ⟩
    let V := f ⁻¹' W ∩ flatDomain Ψ
    have hV : IsOpen V := (hW.preimage hf.contMDiff.continuous).inter (isOpen_flatDomain Ψ)
    have hyV : y ∈ V := ⟨hyW,mem_flatDomain_self Ψ⟩
    have hGV : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ℂ) (G i ∘ f) V := by
      intro i z hz
      exact ((hGh i (f z) hz.1).comp_contMDiff hfat).self_of_nhds.mdifferentiableWithinAt
    have hgenV : ∀ z ∈ V, ∀ H : Y → ℂ,
        (GermIdeal.pullback (m := n+t) f I).mem z H ↔
          IsInSpanAt (n := n+t) (· ∈ range (fun i => G i ∘ f)) z H := by
      intro z hz H
      exact FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
        hfat I G (fun i => hGh i (f z) hz.1) (hgen (f z) hz.1.1) H
    have hDt : ∀ a : X → ℂ, (derivIdealAlong N I).mem (f y) a ↔
        IsInSpanAt (n := n) (· ∈ range (derivFamilyAlong Φ k G)) (f y) a :=
      fun a => derivIdealAlong_mem_iff_of_generators hΦsrc hflat hW inter_subset_right
        (fun i => (hG i).mono inter_subset_left)
        (fun z hz => hgen z hz.1) hyW a
    have hDs := derivIdealAlong_mem_iff_of_generators hΨsrc hΨflat hV inter_subset_right
      hGV hgenV hyV F
    have hDtHol : ∀ c, HolomorphicAt n (derivFamilyAlong Φ k G c) (f y) :=
      holomorphicAt_derivFamilyAlong Φ G hyW.2 (fun i => hGh i (f y) hyW)
    have hPB : (GermIdeal.pullback (m := n+t) f (derivIdealAlong N I)).mem y F ↔
        IsInSpanAt (n := n+t) (· ∈ range (fun c => derivFamilyAlong Φ k G c ∘ f)) y F := by
      constructor
      · intro h
        apply IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp h)
        rintro _ ⟨a,ha,rfl⟩
        apply IsInSpanAt.mono ?_ (isInSpanAt_comp hf.contMDiff ((hDt a).mp ha))
        rintro _ ⟨b,⟨c,rfl⟩,rfl⟩
        exact ⟨c,rfl⟩
      · intro h
        apply GermIdeal.mem_pullback_iff.mpr
        apply IsInSpanAt.mono ?_ h
        rintro _ ⟨c,rfl⟩
        exact ⟨derivFamilyAlong Φ k G c,
          (hDt _).mpr (isInSpanAt_self ⟨c,rfl⟩ (hDtHol c)),rfl⟩
    exact hPB.trans ((derivFamilyAlong_pullback_spans_iff hf Φ h0 hΦsrc G y hyV.2
      (fun i => hGh i (f y) hyW) F).trans hDs.symm)
  · constructor
    · intro h
      exact derivIdealAlong_mem_of_notMem hNp.1 hyN
        (holomorphicAt_of_mem_coherent _ (isCoherent_pullback hf.contMDiff hD) h)
    · intro h
      have hF := holomorphicAt_of_mem_coherent _ hDp h
      apply GermIdeal.mem_pullback_iff.mpr
      apply isInSpanAt_of_eq_mul
        (show ∃ a, (derivIdealAlong N I).mem (f y) a ∧ (fun _ : Y => (1 : ℂ)) = a ∘ f from
          ⟨fun _ => 1,derivIdealAlong_mem_of_notMem hN.1 hyN (holomorphicAt_const 1),rfl⟩)
        hF hF
      exact Eventually.of_forall fun _ => (mul_one _).symm

theorem pullback_derivIdealAlong {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (I : GermIdeal n X) (hI : I.IsCoherent) (N : Set X) (hN : IsClosedSubmanifold n N) :
    GermIdeal.pullback (m := m) f (derivIdealAlong N I) =
      derivIdealAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) := by
  by_cases hY : Nonempty Y
  · obtain ⟨y⟩ := hY
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le
      (HironakaSmoothSubmersionMonomialOrdering.dimension_le_of_submersionAt (hf.isSubmersionAt y))
    exact pullback_derivIdealAlong_add hf I hI N hN
  · have : IsEmpty Y := not_nonempty_iff.mp hY
    ext y F
    exact (IsEmpty.false y).elim

theorem pullback_iterDerivIdealAlong {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (I : GermIdeal n X) (hI : I.IsCoherent) (N : Set X) (hN : IsClosedSubmanifold n N) (j : ℕ) :
    GermIdeal.pullback (m := m) f (iterDerivIdealAlong N I j) =
      iterDerivIdealAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change GermIdeal.pullback (m := m) f (derivIdealAlong N (iterDerivIdealAlong N I j)) =
        derivIdealAlong (f ⁻¹' N) (iterDerivIdealAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) j)
      rw [pullback_derivIdealAlong hf _ (isCoherent_iterDerivIdealAlong hI hN j) N hN,ih]

theorem pullback_tangentIdealAlong {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (I : GermIdeal n X) (hI : I.IsCoherent) (N : Set X) (hN : IsClosedSubmanifold n N) (μ : ℕ) :
    GermIdeal.pullback (m := m) f (tangentIdealAlong N I μ) =
      tangentIdealAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) μ :=
  pullback_iterDerivIdealAlong hf I hI N hN (μ-1)

theorem pullback_homogenizedIdealAlong {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (I : GermIdeal n X) (hI : I.IsCoherent) (N : Set X) (hN : IsClosedSubmanifold n N) (μ : ℕ) :
    GermIdeal.pullback (m := m) f (homogenizedIdealAlong N I μ) =
      homogenizedIdealAlong (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) μ := by
  unfold homogenizedIdealAlong homSum
  rw [pullback_finSumIdeal hf.contMDiff _ _ (fun i _ =>
    IdealWeightPowers.isCoherent_mul (isCoherent_iterDerivIdealAlong hI hN i)
      (isCoherent_idealPow (isCoherent_tangentIdealAlong hI hN μ) i))]
  apply finSumIdeal_congr
  intro i _
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hf.contMDiff
    (isCoherent_iterDerivIdealAlong hI hN i) (isCoherent_idealPow (isCoherent_tangentIdealAlong hI hN μ) i),
    HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hf.contMDiff
      (isCoherent_tangentIdealAlong hI hN μ),
    pullback_iterDerivIdealAlong hf I hI N hN i,pullback_tangentIdealAlong hf I hI N hN μ]

theorem pullback_homMarkedAlong {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N) :
    markedPullback (m := m) f (homMarkedAlong M) = homMarkedAlong (markedPullback (m := m) f M) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  exact pullback_homogenizedIdealAlong hf M.ideal hI M.N hN M.d

theorem pullback_coeffMarkedAlong {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N) :
    markedPullback (m := m) f (coeffMarkedAlong M) = coeffMarkedAlong (markedPullback (m := m) f M) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := m) f
      (finSumIdeal (fun i => idealPow (iterDerivIdealAlong M.N M.ideal i)
        (sumExp (fun j => M.d-j) M.d i)) M.d) =
    finSumIdeal (fun i => idealPow (iterDerivIdealAlong (f ⁻¹' M.N)
      (GermIdeal.pullback (m := m) f M.ideal) i) (sumExp (fun j => M.d-j) M.d i)) M.d
  rw [pullback_finSumIdeal hf.contMDiff _ _
    (fun i _ => isCoherent_idealPow (isCoherent_iterDerivIdealAlong hI hN i) _)]
  apply finSumIdeal_congr
  intro i _
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hf.contMDiff
    (isCoherent_iterDerivIdealAlong hI hN i),pullback_iterDerivIdealAlong hf M.ideal hI M.N hN i]

theorem homMarkedAlong_cosupp_preimage {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N) :
    (homMarkedAlong (markedPullback (m := m) f M)).cosupp = f ⁻¹' (homMarkedAlong M).cosupp := by
  rw [← pullback_homMarkedAlong hf M hI hN]
  exact cosupport_preimage_eq hf (isCoherent_homMarkedAlong hI hN) (homMarkedAlong M).N
    (homMarkedAlong M).d

theorem coeffMarkedAlong_cosupp_preimage {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N) :
    (coeffMarkedAlong (markedPullback (m := m) f M)).cosupp = f ⁻¹' (coeffMarkedAlong M).cosupp := by
  rw [← pullback_coeffMarkedAlong hf M hI hN]
  exact cosupport_preimage_eq hf (isCoherent_coeffMarkedAlong hI hN) (coeffMarkedAlong M).N
    (coeffMarkedAlong M).d

end
end Hironaka.HironakaSmoothSubmersionRelativeDifferentialIdeals
