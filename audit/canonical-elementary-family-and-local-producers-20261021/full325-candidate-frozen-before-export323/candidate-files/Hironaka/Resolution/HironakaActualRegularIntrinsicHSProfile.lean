/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualHSConstantSingularCentre
import Hironaka.Resolution.HironakaSmoothCentreRelativeIdeal

/-! Genuine regular intrinsic all-order HS profiles and the original pure-dimensional lower bound. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualRegularIntrinsicHSProfile
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalActualBaseJetDimension
  HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreRelativeIdeal HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaActualHSSingularBlowupRestart AnalyticDimensionBasics BlowupTowers

/-- Actual plane trace carries the WHOLE original ambient maximal-power quotient, retaining its true kernel. -/
theorem actualPlaneTrace_comap_maximalIdeal_pow (d t s : ℕ) :
    Ideal.comap (planeTrace d t).toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ s) =
      normalIdeal d t ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s := by
  have hm : Ideal.map (planeTrace d t).toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s) =
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ s := by
    rw [Ideal.map_pow,IsLocalRing.map_maximalIdeal_of_surjective _ (planeTrace_surjective d t)]
  rw [← hm,Ideal.comap_map_of_surjective (planeTrace d t).toRingHom (planeTrace_surjective d t)]
  change IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s ⊔
    RingHom.ker (planeTrace d t).toRingHom = _
  rw [← normalIdeal_eq_ker_planeTrace,sup_comm]

/-- The genuine reduced plane ambient jet quotient has the SAME original base complex algebra. -/
def actualPlaneAmbientJetAlgEquiv (d t s : ℕ) :
    (HolGerm (ComplexModel (d+t)) ⧸
      (normalIdeal d t ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s)) ≃ₐ[ℂ]
      (HolGerm (ComplexModel d) ⧸ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ s) := by
  let f := (Ideal.Quotient.mkₐ ℂ (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ s)).comp (planeTrace d t)
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp (planeTrace_surjective d t)
  have hk : RingHom.ker f.toRingHom =
      normalIdeal d t ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s := by
    change Ideal.comap (planeTrace d t).toRingHom
      (RingHom.ker (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ s))) = _
    rw [Ideal.mk_ker,actualPlaneTrace_comap_maximalIdeal_pow]
  exact (Ideal.quotientEquivAlgOfEq ℂ hk.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hf)

/-- EVERY original ambient numerator keeps its actual original plane trace in the whole quotient. -/
theorem actualPlaneAmbientJetAlgEquiv_mk (d t s : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    actualPlaneAmbientJetAlgEquiv d t s
      (Ideal.Quotient.mk (normalIdeal d t ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ s) g) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ s) (planeTrace d t g) := by
  rfl

/-- The EXISTING actual plane Hilbert--Samuel profile is the true binomial at EVERY order. -/
theorem hilbertSamuelValue_actual_normalIdeal (d t ℓ : ℕ) :
    hilbertSamuelValue (normalIdeal d t) ℓ = (d+ℓ).choose d := by
  change Module.finrank ℂ (HolGerm (ComplexModel (d+t)) ⧸
    (normalIdeal d t ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ (ℓ+1))) = _
  rw [(actualPlaneAmbientJetAlgEquiv d t (ℓ+1)).toLinearEquiv.finrank_eq,actualBaseJetDimension]

/-- ONLY true original nonlinear regular geometry constructs the entire reduced original HS profile. -/
theorem hilbertSamuelAt_actual_regular_sum {d t : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]
    {W : Set M} {x : M} (hreg : RegularAtDim (n := d+t) W x d) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := d+t) W) x ℓ = (d+ℓ).choose d := by
  obtain ⟨Φ,_hsrc,h0,_hflat,hI,_hp,_hq,_hf⟩ := exists_regular_relative_ideal W x hreg
  unfold hilbertSamuelAt
  rw [hI]
  exact (actualAmbientHS_eq_of_genuineAlgEquiv (flatteningGermEquiv _ Φ h0)
    (normalIdeal d t) ℓ).trans (hilbertSamuelValue_actual_normalIdeal d t ℓ)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The SAME genuine original regular profile in arbitrary ambient notation. -/
theorem hilbertSamuelAt_actual_regular {W : Set M} {x : M} {d : ℕ} (hd : d ≤ n)
    (hreg : RegularAtDim (n := n) W x d) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = (d+ℓ).choose d := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hd
  exact hilbertSamuelAt_actual_regular_sum hreg ℓ

/-- ONLY original analyticity and genuine purity bound EVERY original intrinsic HS order from below. -/
theorem actual_pure_intrinsic_hs_binomial_lower_bound {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) W d) {x : M} (hx : x ∈ W) (ℓ : ℕ) :
    (d+ℓ).choose d ≤ hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ := by
  have hc := (isComplexAnalyticSubset_hilbertSamuelAt_superlevel
    (vanishingIdeal (n := n) W) (CartanIrreducible.cartanCoherence W hW) ℓ ((d+ℓ).choose d)).isClosed
  have hr : regularLocus (n := n) W d ⊆
      {y | (d+ℓ).choose d ≤ hilbertSamuelAt (vanishingIdeal (n := n) W) y ℓ} := by
    intro y hy
    change (d+ℓ).choose d ≤ hilbertSamuelAt (vanishingIdeal (n := n) W) y ℓ
    rw [hilbertSamuelAt_actual_regular hd hy ℓ]
  exact closure_minimal hr hc (actualPure_subset_closure_regularLocus hW hpure hx)

/-- The ENTIRE minimal original profile detects true regularity of an actual pure carrier point. -/
theorem actual_pure_regular_iff_intrinsic_hs_binomial {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) W d) {x : M} (hx : x ∈ W) :
    RegularAtDim (n := n) W x d ↔
      ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = (d+ℓ).choose d := by
  constructor
  · intro hr ℓ
    exact hilbertSamuelAt_actual_regular hd hr ℓ
  · intro h
    by_contra hnr
    have hs := HironakaHilbertSamuelTangentValue.singularLocus_eq_first_hilbertSamuel_superlevel hW hd hpure
    have hh := ((Set.ext_iff.mp hs x).mp ⟨hx,hnr⟩).2
    rw [h 1,Nat.choose_succ_self_right] at hh
    omega

/-- Actual regular strict-transform points, INCLUDING exceptional ones, have EVERY original intrinsic HS order nonincreasing. -/
theorem actual_blowup_intrinsic_hs_nonincreasing_at_regular_strict_point
    {X Y : CMfd.{u} n} {W C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hW : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d ≤ n) (hpure : IsPureDim (n := n) W d) {y : Y}
    (hreg : RegularAtDim (n := n) (strictTransform n π W) y d) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) y ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := n) W) (π y) ℓ := by
  rw [hilbertSamuelAt_actual_regular hd hreg ℓ]
  exact actual_pure_intrinsic_hs_binomial_lower_bound hW hd hpure
    (closure_minimal sdiff_subset (hW.isClosed.preimage hπ.contMDiff.continuous) hreg.2.1) ℓ

end
end Hironaka.HironakaActualRegularIntrinsicHSProfile
