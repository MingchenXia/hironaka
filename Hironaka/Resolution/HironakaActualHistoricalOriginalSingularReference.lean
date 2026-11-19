import Hironaka.Resolution.HironakaActualWholeHSSingularity
import Hironaka.Resolution.HironakaGeneralSingularCentreCodimension

/-! The SAME ORIGINAL nonsmooth HS reference remains singular at every
actual native analytic stage, even across different ambient manifolds.
The actual CURRENT marked cut derives WHOLE singular-centre containment,
normal codimension >=2 and all-order centre constancy; no purity is used. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualHistoricalOriginalSingularReference
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualWholeHSSingularity HironakaGeneralSingularCentreCodimension
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaHolomorphicPointJets HironakaActualRegularIntrinsicHSProfile
  HironakaActualReferenceHSSingularCentre
  HironakaEmbeddedAnalytic InvertibleIdealQuotient BlowupExceptionalDivisor MarkedIdeals

variable {m n : ℕ} {X₀ : Type u} {X : Type v}
  [TopologicalSpace X₀] [ChartedSpace (ComplexModel m) X₀] [IsComplexManifold m X₀]
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The true entire profile reflects actual regularity to the ORIGINAL
reference across different native analytic sets and ambient dimensions. -/
theorem actual_original_regular_of_current_entire_hs_equal
    (W₀ : Set X₀) (hW₀ : IsComplexAnalyticSubset (n:=m) W₀) (a₀ : X₀)
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W) (x : X) (d : ℕ)
    (hReg : RegularAtDim (n:=n) W x d)
    (hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ) :
    RegularAtDim (n:=m) W₀ a₀ d := by
  apply (regularAtDim_iff_intrinsic_hs_binomial hW₀ a₀ d).mpr
  intro ℓ
  exact (hHS ℓ).symm.trans ((regularAtDim_iff_intrinsic_hs_binomial hW x d).mp hReg ℓ)

/-- The ORIGINAL intrinsically singular profile cannot be regular on ANY
later actual analytic set. Actual support follows from the true HS0 value. -/
theorem actual_original_singular_profile_locus_subset_current_singular
    (W₀ : Set X₀) (hW₀ : IsComplexAnalyticSubset (n:=m) W₀) (a₀ : X₀)
    (ha₀ : a₀∈singularSet (n:=m) W₀)
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W) :
    {x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ}⊆singularSet (n:=n) W := by
  intro x hx
  have ha:=mem_singularSet_iff.mp ha₀
  have hcoh₀:=CartanIrreducible.cartanCoherence W₀ hW₀
  have hz₀:=zeroLocus_vanishingIdeal (n:=m) hW₀.isClosed
  have ha0 : 1≤hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ 0:=
    (one_le_hilbertSamuelAt_zero_iff _ hcoh₀ a₀).mpr (hz₀.symm ▸ ha.1)
  have hcoh:=CartanIrreducible.cartanCoherence W hW
  have hz:=zeroLocus_vanishingIdeal (n:=n) hW.isClosed
  have hx0 : 1≤hilbertSamuelAt (vanishingIdeal (n:=n) W) x 0 := by
    rw [hx 0]
    exact ha0
  have hxW : x∈W:=hz ▸ (one_le_hilbertSamuelAt_zero_iff _ hcoh x).mp hx0
  apply mem_singularSet_iff.mpr
  refine ⟨hxW,fun d hd=>?_⟩
  exact ha.2 d (actual_original_regular_of_current_entire_hs_equal W₀ hW₀ a₀ W hW x d hd hx)

/-- The ACTUAL current-stage Q cut and original nonsmooth reference derive
the WHOLE intrinsic singular-centre law, source codimension and all-order
centre constancy. No singular-centre/codimension/HS-on-centre cert is input. -/
theorem actual_original_reference_current_cut_centre_geometry
    (W₀ : Set X₀) (hW₀ : IsComplexAnalyticSubset (n:=m) W₀) (a₀ : X₀)
    (ha₀ : a₀∈singularSet (n:=m) W₀)
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (Q : MarkedIdeal n X)
    (hCut : Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ})
    (C : Set X) (hC : C⊆Q.cosupp) (x : X) (c : ℕ) (hReg : RegularAtDim (n:=n) C x c) :
    C⊆singularSet (n:=n) W ∧ c+2≤n ∧
      ∀y∈C,∀z∈C,∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) y ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) z ℓ := by
  have hProfiles (y : X) (hy : y∈C) : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) y ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ := by
    have h:=hC hy
    rw [hCut] at h
    exact h
  have hSing : C⊆singularSet (n:=n) W:=fun y hy=>
    actual_original_singular_profile_locus_subset_current_singular W₀ hW₀ a₀ ha₀ W hW (hProfiles y hy)
  refine ⟨hSing,regular_intrinsic_singular_centre_add_two_le hW hSing hReg,?_⟩
  intro y hy z hz ℓ
  exact (hProfiles y hy ℓ).trans (hProfiles z hz ℓ).symm

end
end Hironaka.HironakaActualHistoricalOriginalSingularReference
