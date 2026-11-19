import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartier
import Hironaka.Blowup.BlowupIsomorphismOff

/-!
# Actual singular Cartier ideals force dense off-centre source points

Pointwise actual quotient-stalk regular principal data exclude every nonempty
relative open source subset mapping into the centre. This gives density and
continuous uniqueness of singular-source blowup lifts. No ambient pullback
invertibility, smoothness or integral-domain condition on the source is used.

Blueprint: `hironaka-singular-subspace-blowup-cartier-density.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierDensity

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue
  HironakaSingularSubspaceBlowupCartier

noncomputable section

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
  {C : Set M} {G : N → M} {S : Set N}

omit [IsComplexManifold n M] [IsComplexManifold m N] in
private theorem pulled_mem_vanishes_on_preimage (hG : Continuous G) (x : N) (f : N → ℂ)
    (hf : (GermIdeal.pullback (m := m) G (vanishingIdeal (n := n) C)).mem x f) :
    ∀ᶠ z in 𝓝 x, G z ∈ C → f z = 0 := by
  obtain ⟨_, K, s, a, hs, _, hsum⟩ := hf
  have hzero : ∀ i, ∀ᶠ z in 𝓝 x, G z ∈ C → s i z = 0 := by
    intro i
    obtain ⟨b, hb, hsb⟩ := hs i
    filter_upwards [hG.continuousAt.eventually hb.2] with z hz hzC
    rw [hsb]
    exact hz hzC
  filter_upwards [hsum, eventually_all.mpr hzero] with z hz hz' hzC
  rw [hz]
  exact Finset.sum_eq_zero fun i _ => by rw [hz' i hzC, mul_zero]

omit [IsComplexManifold n M] in
/-- The SAME whole actual restricted pulled centre ideal becomes zero at a
point with a genuine relative source neighbourhood mapping into the centre. -/
theorem actual_pulled_centre_ideal_eq_bot_of_relative_centre_neighbourhood
    (hG : Continuous G) (x : S)
    (hcentre : ∀ᶠ z in 𝓝 x.val, z ∈ S → G z ∈ C) :
    Ideal.map ((actualSubspaceInclusion (n := m) S).stalkMap x).hom
      (actualWholeSheafStalkIdeal
        (GermIdeal.pullback (m := m) G (vanishingIdeal (n := n) C)) x.val) = ⊥ := by
  apply (Ideal.map_eq_bot_iff_le_ker _).mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨f, hf, hmem, rfl⟩
  rw [actualSubspaceInclusion_stalk_kernel]
  apply (actualOriginalGerm_mem_vanishingIdeal_iff S x.val f hf).mpr
  refine ⟨hf, ?_⟩
  filter_upwards [hcentre, pulled_mem_vanishes_on_preimage hG x.val f hmem] with z hz hz' hzS
  exact hz' (hz hzS)

omit [IsComplexManifold n M] in
/-- Regular principal generators for the original actual restricted pulled
ideal at every singular source stalk force the centre complement to be dense. -/
theorem dense_compl_centre_of_actual_cartier (hG : Continuous G)
    (hCart : ∀ x : S,
      ∃ alpha : ((actualSubspaceSheaf (n := m) S).presheaf.stalk x).carrier,
        IsRegular alpha ∧
        Ideal.map ((actualSubspaceInclusion (n := m) S).stalkMap x).hom
          (actualWholeSheafStalkIdeal
            (GermIdeal.pullback (m := m) G (vanishingIdeal (n := n) C)) x.val) =
          Ideal.span {alpha}) :
    Dense {x : S | G x.val ∉ C} := by
  have hempty : interior {x : S | G x.val ∈ C} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨U, hU, hUV⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp
      (isOpen_interior : IsOpen (interior {x : S | G x.val ∈ C}))
    have hxU : x.val ∈ U := by
      change x ∈ (Subtype.val : S → N) ⁻¹' U
      rw [hUV]
      exact hx
    have hcentre : ∀ᶠ z in 𝓝 x.val, z ∈ S → G z ∈ C := by
      filter_upwards [hU.mem_nhds hxU] with z hz hzS
      have hzV : (⟨z, hzS⟩ : S) ∈ interior {x : S | G x.val ∈ C} := by
        rw [← hUV]
        exact hz
      have hzC : (⟨z, hzS⟩ : S) ∈ {x : S | G x.val ∈ C} := interior_subset hzV
      exact hzC
    obtain ⟨alpha, hreg, hspan⟩ := hCart x
    have hbot := actual_pulled_centre_ideal_eq_bot_of_relative_centre_neighbourhood
      (n := n) (m := m) hG x hcentre
    have halpha : alpha = 0 := by
      have hm : alpha ∈ Ideal.span {alpha} := Ideal.subset_span (mem_singleton _)
      rw [← hspan, hbot] at hm
      exact hm
    have h01 : (0 : ((actualSubspaceSheaf (n := m) S).presheaf.stalk x).carrier) = 1 :=
      hreg.left (by simp [halpha])
    have h01C : (0 : ℂ) = 1 := by
      simpa only [map_zero, map_one] using congrArg (actualSubspaceStalkEval (n := m) S x) h01
    exact zero_ne_one h01C
  simpa only [Set.compl_ofPred, not_not] using interior_eq_empty_iff_dense_compl.mp hempty

section Uniqueness

variable {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {π : Y → M}

/-- The actual Cartier condition also supplies continuous uniqueness on the
singular source, using the original blowup's off-centre injectivity. -/
theorem continuous_lift_unique_of_actual_cartier (hπ : IsBlowupAlong n C π)
    (hG : Continuous G)
    (hCart : ∀ x : S,
      ∃ alpha : ((actualSubspaceSheaf (n := m) S).presheaf.stalk x).carrier,
        IsRegular alpha ∧
        Ideal.map ((actualSubspaceInclusion (n := m) S).stalkMap x).hom
          (actualWholeSheafStalkIdeal
            (GermIdeal.pullback (m := m) G (vanishingIdeal (n := n) C)) x.val) =
          Ideal.span {alpha})
    {L₁ L₂ : S → Y} (hL₁ : Continuous L₁) (hL₂ : Continuous L₂)
    (hπL₁ : ∀ x, π (L₁ x) = G x.val) (hπL₂ : ∀ x, π (L₂ x) = G x.val) :
    L₁ = L₂ := by
  have hdense := dense_compl_centre_of_actual_cartier hG hCart
  have hsub : {x : S | G x.val ∉ C} ⊆ {x : S | L₁ x = L₂ x} := by
    intro x hx
    apply (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hπ).1.2.1
    · change π (L₁ x) ∉ C
      rwa [hπL₁]
    · change π (L₂ x) ∉ C
      rwa [hπL₂]
    · exact (hπL₁ x).trans (hπL₂ x).symm
  have hclosed : IsClosed {x : S | L₁ x = L₂ x} := isClosed_eq hL₁ hL₂
  have hall : Set.univ ⊆ {x : S | L₁ x = L₂ x} := by
    rw [← hdense.closure_eq]
    exact closure_minimal hsub hclosed
  exact funext fun x => hall (mem_univ x)

end Uniqueness

end

end Hironaka.HironakaSingularSubspaceBlowupCartierDensity
