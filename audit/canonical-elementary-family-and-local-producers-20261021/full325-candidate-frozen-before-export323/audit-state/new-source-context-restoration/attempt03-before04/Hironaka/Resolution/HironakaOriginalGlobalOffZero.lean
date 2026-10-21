/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalGlobalPrincipalization
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Analytic.HolomorphicLocalInverse

/-! Genuine off-zero geometry on the same original global terminal manifold.
The original local finite towers internally supply surjectivity and off-zero
geometry; the true global projection is retained throughout. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaOriginalGlobalOffZero

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalLocalBiholomorphism HironakaOriginalGlobalPrincipalization

open ResolutionInvariantSpec (IsInvDomain)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

variable {n : ℕ} {X : CMfd.{u} n}

/-- The original atlas index at a base point and its true finite terminal tower
internally give a preimage under the same whole global projection. -/
theorem originalTerminalGluedProjection_surjective (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    Surjective (originalTerminalGluedProjection M hM : originalTerminalManifold M hM → X) := by
  intro x
  let A := actualLocalTerminalAtlas M hM
  obtain ⟨y, hy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective
    (A.tower x).isBlowupSequence ⟨x, A.point_mem x⟩
  refine ⟨originalTerminalLocalInclusion M hM x y, ?_⟩
  rw [originalTerminalGluedProjection_local]
  exact congrArg Subtype.val hy

/-- The actual original finite local terminal projection is an isomorphism off
the true restricted original zero locus. -/
theorem originalLocalTerminalProjection_isIsomorphismOffZero
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) (i : X) :
    IsIsomorphismOver n ((actualLocalTerminalAtlas M hM).tower i).proj
      ((Subtype.val : (actualLocalTerminalAtlas M hM).openSet i → X) ⁻¹' M.ideal.zeroLocus)ᶜ := by
  let A := actualLocalTerminalAtlas M hM
  let M' := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : A.openSet i → X) M
  have hcoh := hM.isWellFormed.isCoherent
  have hcoh' : M'.ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcoh
  have hN' : M'.N = univ := by
    change (Subtype.val : A.openSet i → X) ⁻¹' M.N = univ
    rw [hN, preimage_univ]
  have hpb := MarkedIdeal.pullback_eq_exceptionalDivisor_of_isGeoResolution M' hN' hcoh' hd
    (A.tower i) (A.terminal i)
  have hsupp : (BlowupTowerTransforms.exceptionalDivisor (A.tower i)).support =
      (A.tower i).proj ⁻¹' ((Subtype.val : A.openSet i → X) ⁻¹' M.ideal.zeroLocus) := by
    rw [EffectiveDivisor.support, ← hpb,
      BlowupExceptionalDivisor.zeroLocus_pullback (A.tower i).contMDiff_proj hcoh']
    change (A.tower i).proj ⁻¹'
      (GermIdeal.pullback (m := n) (Subtype.val : A.openSet i → X) M.ideal).zeroLocus = _
    rw [BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val hcoh]
  apply HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    (A.tower i).isBlowupSequence
  rintro x ⟨y, hy, rfl⟩
  have h := HironakaPrincipalization.exceptionalLocus_subset_support (A.tower i) hy
  rw [hsupp] at h
  exact h

/-- On a noncompact original base, the same actual global terminal projection is
bijective and unramified over the complement of the true original ideal. -/
theorem originalTerminalGluedProjection_isIsomorphismOffZero
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) :
    IsIsomorphismOver n
      (originalTerminalGluedProjection M hM : originalTerminalManifold M hM → X) M.ideal.zeroLocusᶜ := by
  let A := actualLocalTerminalAtlas M hM
  refine ⟨⟨fun z hz => hz, ?_, ?_⟩, ?_⟩
  · intro z hz w hw hp
    obtain ⟨i, y, rfl⟩ := originalTerminalLocalInclusion_jointly_surjective M hM z
    have hwrange : w ∈ range (originalTerminalLocalInclusion M hM i) := by
      rw [originalTerminalLocalInclusion_range]
      change originalTerminalGluedProjection M hM w ∈ A.openSet i
      rw [← hp, originalTerminalGluedProjection_local]
      exact ((A.tower i).proj y).property
    obtain ⟨v, rfl⟩ := hwrange
    rw [originalTerminalGluedProjection_local, originalTerminalGluedProjection_local] at hp
    change originalTerminalGluedProjection M hM (originalTerminalLocalInclusion M hM i y) ∈
      M.ideal.zeroLocusᶜ at hz
    change originalTerminalGluedProjection M hM (originalTerminalLocalInclusion M hM i v) ∈
      M.ideal.zeroLocusᶜ at hw
    rw [originalTerminalGluedProjection_local] at hz hw
    apply congrArg (originalTerminalLocalInclusion M hM i)
    exact (originalLocalTerminalProjection_isIsomorphismOffZero M hM hN hd i).1.2.1 hz hw
      (Subtype.ext hp)
  · intro x hx
    obtain ⟨z, hz⟩ := originalTerminalGluedProjection_surjective M hM x
    refine ⟨z, ?_, hz⟩
    change originalTerminalGluedProjection M hM z ∈ M.ideal.zeroLocusᶜ
    rw [hz]
    exact hx
  · apply disjoint_left.mpr
    intro z hz hex
    obtain ⟨i, y, rfl⟩ := originalTerminalLocalInclusion_jointly_surjective M hM z
    change originalTerminalGluedProjection M hM (originalTerminalLocalInclusion M hM i y) ∈
      M.ideal.zeroLocusᶜ at hz
    rw [originalTerminalGluedProjection_local] at hz
    have hlocal : y ∉ exceptionalLocus n (A.tower i).proj :=
      fun h => disjoint_left.mp
        (originalLocalTerminalProjection_isIsomorphismOffZero M hM hN hd i).2 hz h
    have hmap :
        (originalTerminalGluedProjection M hM : originalTerminalManifold M hM → X) ∘
            (originalTerminalLocalInclusion M hM i) =
          (Subtype.val : A.openSet i → X) ∘ (A.tower i).proj :=
      funext (originalTerminalGluedProjection_local M hM i)
    have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (Subtype.val : A.openSet i → X) := contMDiff_subtype_val
    have hcomp : y ∈ exceptionalLocus n
        ((originalTerminalGluedProjection M hM : originalTerminalManifold M hM → X) ∘
          (originalTerminalLocalInclusion M hM i)) := by
      erw [exceptionalLocus_comp
        ((originalTerminalGluedProjection_contMDiff M hM).mdifferentiable (by simp))
        ((originalTerminalLocalInclusion_contMDiff M hM i).mdifferentiable (by simp))]
      exact Or.inr hex
    rw [hmap] at hcomp
    rw [exceptionalLocus_comp (hval.mdifferentiable (by simp))
      ((A.tower i).contMDiff_proj.mdifferentiable (by simp)),
      HironakaBaseChange.exceptionalLocus_val, preimage_empty, union_empty] at hcomp
    exact hlocal hcomp

/-- The actual original off-zero target open. -/
def originalTerminalOffZeroBaseOpen (M : MarkedIdeal n X) (hM : IsInvDomain n M) : Opens X :=
  ⟨M.ideal.zeroLocusᶜ, (OrderTaylor.isClosed_zeroLocus_of_isCoherent hM.isWellFormed.isCoherent).isOpen_compl⟩

/-- The genuine inverse-image open inside the same original global manifold. -/
def originalTerminalOffZeroSourceOpen (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    Opens (originalTerminalManifold M hM) :=
  ⟨(originalTerminalGluedProjection M hM) ⁻¹' M.ideal.zeroLocusᶜ,
    (originalTerminalOffZeroBaseOpen M hM).isOpen.preimage (originalTerminalGluedProjection M hM).continuous⟩

private def offZeroProjection (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    originalTerminalOffZeroSourceOpen M hM → originalTerminalOffZeroBaseOpen M hM :=
  fun q => ⟨originalTerminalGluedProjection M hM q.val, q.property⟩

private theorem offZeroProjection_bijective
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) :
    Bijective (offZeroProjection M hM) := by
  have hi := originalTerminalGluedProjection_isIsomorphismOffZero M hM hN hd
  constructor
  · intro q q' h
    apply Subtype.ext
    exact hi.1.2.1 q.property q'.property (congrArg Subtype.val h)
  · intro p
    obtain ⟨z, hz, hp⟩ := hi.1.2.2 p.property
    exact ⟨⟨z, hz⟩, Subtype.ext hp⟩

private def offZeroEquiv
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) :
    originalTerminalOffZeroSourceOpen M hM ≃ originalTerminalOffZeroBaseOpen M hM :=
  Equiv.ofBijective (offZeroProjection M hM) (offZeroProjection_bijective M hM hN hd)

private theorem offZeroProjection_contMDiff (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (offZeroProjection M hM) :=
  BlowupRestrictOpen.contMDiff_opens_mk
    ((originalTerminalGluedProjection_contMDiff M hM).comp contMDiff_subtype_val)
    (fun q => q.property)

private theorem offZeroEquiv_symm_contMDiff
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (offZeroEquiv M hM hN hd).symm := by
  intro q
  let e := offZeroEquiv M hM hN hd
  let z := (e.symm q).val
  have hz : z ∉ exceptionalLocus n
      (originalTerminalGluedProjection M hM : originalTerminalManifold M hM → X) :=
    fun h => disjoint_left.mp
      (originalTerminalGluedProjection_isIsomorphismOffZero M hM hN hd).2 (e.symm q).property h
  have hp : originalTerminalGluedProjection M hM z = q.val :=
    congrArg Subtype.val (e.apply_symm_apply q)
  obtain ⟨V, s, hV, hzV, _, hPs, hs, _⟩ :=
    HolomorphicLocalInverse.exists_localInverse (originalTerminalGluedProjection_contMDiff M hM) hz
  have hqV : q.val ∈ V := by rw [← hp]; exact hzV
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : originalTerminalOffZeroBaseOpen M hM → X) := contMDiff_subtype_val
  have hlocal : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (s ∘ (Subtype.val : originalTerminalOffZeroBaseOpen M hM → X)) q :=
    (hs q.val hqV).comp q hval.contMDiffAt
  have heq : (fun p : originalTerminalOffZeroBaseOpen M hM => (e.symm p).val) =ᶠ[𝓝 q]
      s ∘ (Subtype.val : originalTerminalOffZeroBaseOpen M hM → X) := by
    filter_upwards [(hV.preimage continuous_subtype_val).mem_nhds hqV] with p hpV
    have hsp : s p.val ∈
        (originalTerminalGluedProjection M hM) ⁻¹' M.ideal.zeroLocusᶜ := by
      change originalTerminalGluedProjection M hM (s p.val) ∈ M.ideal.zeroLocusᶜ
      rw [hPs p.val hpV]
      exact p.property
    exact (originalTerminalGluedProjection_isIsomorphismOffZero M hM hN hd).1.2.1
      (e.symm p).property hsp
      ((congrArg Subtype.val (e.apply_symm_apply p)).trans (hPs p.val hpV).symm)
  exact (ContMDiffAt.subtypeVal_comp_iff (originalTerminalOffZeroSourceOpen M hM) e.symm q).mp
    (hlocal.congr_of_eventuallyEq heq)

/-- The true original open complements are genuinely biholomorphic, with both
holomorphic directions proved for the same original global projection. -/
def originalTerminalOffZeroBiholomorphism
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1) :
    CMfd.of (n := n) (originalTerminalOffZeroSourceOpen M hM)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (originalTerminalOffZeroBaseOpen M hM) where
  toEquiv := offZeroEquiv M hM hN hd
  contMDiff_toFun := offZeroProjection_contMDiff M hM
  contMDiff_invFun := offZeroEquiv_symm_contMDiff M hM hN hd

theorem originalTerminalOffZeroBiholomorphism_point
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hN : M.N = univ) (hd : M.d = 1)
    (q : originalTerminalOffZeroSourceOpen M hM) :
    (originalTerminalOffZeroBiholomorphism M hM hN hd q).val =
      originalTerminalGluedProjection M hM q.val := rfl

end

end Hironaka.HironakaOriginalGlobalOffZero
