import Hironaka.Analytic.PrincipalizationSourceDataReduction
import Hironaka.Analytic.CollarWeightComparison
import Hironaka.Analytic.AmbientPhiQLowerBound
import Hironaka.MarkedIdeal.IdealWeightLowerBound
import Hironaka.Blowup.ExceptionalWeightFactorization
import Hironaka.Analytic.IdealComparisonResidual

set_option autoImplicit false

/-!
# Upstream Copy-4 Step-5 reduction for principalization

The source interface for `prop:principalization` must live upstream of
`PrincipalizationData`.  The more convenient pre-collar normal form is defined
downstream, so importing it into that interface would create an import cycle.
This module instead records the same Step-6 core fields directly, except for
its collar field, and reconstructs that field from the Step-5 calculations in
Copy-4.

Thus the source boundary is not the finished compact-collar conclusion, nor
the pulled-back `eq:QM-lower`: it contains the exceptional divisor weights,
the ambient `eq:phiQ-lower`, the two ideal/divisor comparisons, and the
residual ideal presentation.  The exceptional calculation, residual lower
bound off the strict transform, pullback, and conversion to
`PrincipalizationStepSixAnchoredData` are source-free.

Source: Copy-4, `prop:principalization`, Steps 3--6
(`source/main-Nulllocus.tex:1854-1996`).
-/

open Set
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.PrincipalizationCopy4StepFiveCoreReduction

open Hironaka.AnalyticGluingData Hironaka.NonKahlerLocus
  Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
  PrincipalizationGluingLocalAssembly PrincipalizationSourceDataReduction
  CollarWeightComparison AmbientPhiQLowerBound IdealWeightLowerBound
  ThetaPshConvexCombination IdealWeightComparison IdealWeightPowers
  ExceptionalWeightFactorization IdealComparisonResidual

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The data of Copy-4's `eq:PhiR-lower` before its numerical coefficient is
turned into a singularity comparison.  The analytic presentations and the
power containment are the inputs of Rückert's Nullstellensatz; the displayed
lower bound is reconstructed below. -/
structure AmbientPhiRLowerSource (n : ℕ) (base : Type u)
    [TopologicalSpace base] [ChartedSpace (ComplexModel n) base]
    [IsComplexManifold n base] [CompactSpace base] (A : Real)
    (PhiR psiIV psij : base -> EReal) where
  c : ℚ
  cR : ℚ
  cR_pos : 0 < cR
  idealIV : GermIdeal n base
  idealj : GermIdeal n base
  idealR : GermIdeal n base
  psiR : base -> EReal
  IV_presentation : HasAnalyticSingularitiesOfType (n := n) psiIV c idealIV
  j_presentation : HasAnalyticSingularitiesOfType (n := n) psij c idealj
  R_presentation : HasAnalyticSingularitiesOfType (n := n) psiR c idealR
  PhiR_presentation : HasAnalyticSingularitiesOfType (n := n) PhiR (cR * c) idealR
  power : ℕ
  power_pos : 0 < power
  power_containment : (idealPow (idealIV.mul idealj) power).Le idealR
  A_def : A = cR * (power : Real)

/-- The power containment in `AmbientPhiRLowerSource` yields precisely
`eq:PhiR-lower`.  No Step-5 comparison is assumed as a field. -/
theorem AmbientPhiRLowerSource.moreSingularOn
    {base : Type u} [TopologicalSpace base] [ChartedSpace (ComplexModel n) base]
    [IsComplexManifold n base] [CompactSpace base] {A : Real}
    {PhiR psiIV psij : base -> EReal}
    (d : AmbientPhiRLowerSource n base A PhiR psiIV psij) :
    MoreSingularOn (fun y => (A : EReal) * (psiIV y + psij y)) PhiR univ := by
  have hmul := hasAnalyticSingularitiesOfType_mul d.IV_presentation d.j_presentation
  have hpow := hasAnalyticSingularitiesOfType_pow hmul d.power
  have hstep : MoreSingularOn (fun y => d.power • (psiIV y + psij y)) d.psiR univ :=
    moreSingularOn_univ_of_le hpow d.R_presentation d.power_containment
  have hcR : (0 : ℝ) ≤ (d.cR : ℝ) := by exact_mod_cast d.cR_pos.le
  have hscaled := moreSingularOn_smul hcR hstep
  have hPhiR : MoreSingularOn (fun y => ((d.cR : ℝ) : EReal) * d.psiR y) PhiR univ :=
    (sameSingularityTypeOn_univ_of_eq_type
      (hasAnalyticSingularitiesOfType_smul d.cR_pos d.R_presentation)
      d.PhiR_presentation).1
  rw [d.A_def]
  refine (MoreSingularOn.of_le fun y _ => le_of_eq ?_).trans (hscaled.trans hPhiR)
  rw [nsmul_eq_coe_mul, EReal.coe_mul, mul_assoc]

/-- The factorization data behind Copy-4's `eq:IV-H`, stated before either of
its two singularity comparisons is extracted. -/
structure AmbientIVLowerSource (n : ℕ) (base target : Type u)
    [TopologicalSpace base] [ChartedSpace (ComplexModel n) base]
    [IsComplexManifold n base] [TopologicalSpace target]
    [ChartedSpace (ComplexModel n) target] [IsComplexManifold n target]
    (pi : target -> base)
    (psiIV : base -> EReal) (psiH psiIW : target -> EReal) where
  c : ℚ
  pi_smooth : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ pi
  idealIV : GermIdeal n base
  idealH : GermIdeal n target
  idealIW : GermIdeal n target
  IV_presentation : HasAnalyticSingularitiesOfType (n := n) psiIV c idealIV
  H_presentation : HasAnalyticSingularitiesOfType (n := n) psiH c idealH
  IW_presentation : HasAnalyticSingularitiesOfType (n := n) psiIW c idealIW
  factorization : GermIdeal.pullback (m := n) pi idealIV = idealH.mul idealIW

/-- The ideal factorization in `AmbientIVLowerSource` supplies the direction
of `eq:IV-H` used to remove the residual ideal weight on a collar. -/
theorem AmbientIVLowerSource.moreSingularOn
    {base target : Type u} [TopologicalSpace base]
    [ChartedSpace (ComplexModel n) base] [IsComplexManifold n base]
    [TopologicalSpace target] [ChartedSpace (ComplexModel n) target]
    [IsComplexManifold n target] [CompactSpace target]
    {pi : target -> base} {psiIV : base -> EReal} {psiH psiIW : target -> EReal}
    (d : AmbientIVLowerSource n base target pi psiIV psiH psiIW) :
    MoreSingularOn (fun y => psiH y + psiIW y) (fun y => psiIV (pi y)) univ :=
  (sameSingularityTypeOn_univ_comp_add_of_pullback_eq_mul d.pi_smooth
    d.IV_presentation d.H_presentation d.IW_presentation d.factorization).2

/-- The factorization data behind the divisor/ideal comparison
`ψ_{\widetilde G_M} ≤ ψ_{\mathfrak B_M} ∘ π + O(1)`.  As with the other
Step-5 lower bounds, the comparison itself is derived rather than stored. -/
structure AmbientGMLowerSource (n : ℕ) (base target : Type u)
    [TopologicalSpace base] [ChartedSpace (ComplexModel n) base]
    [IsComplexManifold n base] [TopologicalSpace target]
    [ChartedSpace (ComplexModel n) target] [IsComplexManifold n target]
    (pi : target -> base) (psiBM : base -> EReal) (psiGM : target -> EReal) where
  c : ℚ
  pi_smooth : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ pi
  idealBM : GermIdeal n base
  idealGM : GermIdeal n target
  BM_presentation : HasAnalyticSingularitiesOfType (n := n) psiBM c idealBM
  GM_presentation : HasAnalyticSingularitiesOfType (n := n) psiGM c idealGM
  factorization : GermIdeal.pullback (m := n) pi idealBM = idealGM

/-- The raw ideal equality in `AmbientGMLowerSource` is the Step-5 comparison
between the divisor weight and the pullback ideal weight. -/
theorem AmbientGMLowerSource.moreSingularOn
    {base target : Type u} [TopologicalSpace base]
    [ChartedSpace (ComplexModel n) base] [IsComplexManifold n base]
    [TopologicalSpace target] [ChartedSpace (ComplexModel n) target]
    [IsComplexManifold n target] [CompactSpace target]
    {pi : target -> base} {psiBM : base -> EReal} {psiGM : target -> EReal}
    (d : AmbientGMLowerSource n base target pi psiBM psiGM) :
    MoreSingularOn psiGM (fun y => psiBM (pi y)) univ := by
  have hsame : SameSingularityTypeOn (psiBM ∘ pi) psiGM univ := by
    refine sameSingularityTypeOn_univ_comp_pullback d.pi_smooth d.BM_presentation ?_
    rw [d.factorization]
    exact d.GM_presentation
  exact hsame.2

/-- Copy-4's Step-3--5 local data before the collar field is derived.  The
first ten fields are exactly `PrincipalizationStepSixCoreData` apart from its
collar.  The remaining fields are `eq:def-DLY`, the exceptional-weight
comparison preceding `eq:QM-lower`, and `eq:QM-lower` on each compact collar. -/
structure Copy4StepFiveCoreData
    (theta : ClosedRealOneOneForm n M) (W : Set M) (phiG : M -> EReal) where
  y : M
  U : Set M
  beta : ClosedRealOneOneForm n M
  sigma : M -> Real
  rho : M -> EReal
  smooth_sigma : ChartSmooth (n := n) sigma
  dominates_beta : DominatesKahlerFormOn beta (fun x => (sigma x : EReal)) U
  positive_correction : IsThetaPshPotentialOn (theta - beta).val rho U
  smooth_rho_at_y : IsSmoothNear (n := n) rho y
  point_mem : y ∈ W
  open_neighbourhood : IsOpen U
  transform_subset : W ⊆ U
  psiDres : M -> EReal
  psiE : M -> EReal
  chi : M -> EReal
  phiQpi : M -> EReal
  psiD : M -> EReal
  rhs : M -> EReal
  tau : Real
  correction_eq : rho = fun x => psiD x + chi x
  divisor_split : ∀ x, psiD x = psiDres x + (tau : EReal) * psiE x
  polar_split : ∀ x, phiG x = phiQpi x + (tau : EReal) * psiE x
  exceptional_weight_comparison :
    MoreSingularOn (fun x => psiDres x + chi x) rhs univ
  ambient_lower_comparison : ∀ Lambda : Set M, IsCompact Lambda ->
    Lambda ⊆ U \ W -> MoreSingularOn rhs phiQpi Lambda

/-- The two Step-5 comparisons produce the compact collar in the normalized
core, and hence the full anchored Step-6 datum. -/
def Copy4StepFiveCoreData.toAnchoredData
    {theta : ClosedRealOneOneForm n M} {W : Set M} {phiG : M -> EReal}
    (d : Copy4StepFiveCoreData theta W phiG) :
    PrincipalizationStepSixAnchoredData theta W phiG where
  core :=
    { y := d.y
      U := d.U
      β := d.beta
      σ := d.sigma
      ρ := d.rho
      smooth_σ := d.smooth_sigma
      dominates_β := d.dominates_beta
      positive_correction := d.positive_correction
      smooth_ρ_at_y := d.smooth_rho_at_y
      collar := by
        intro Lambda hLambda hLambdaUW
        rw [d.correction_eq]
        exact moreSingularOn_collar d.divisor_split d.polar_split
          d.exceptional_weight_comparison
          (d.ambient_lower_comparison Lambda hLambda hLambdaUW) }
  point_mem := d.point_mem
  open_neighbourhood := d.open_neighbourhood
  transform_subset := d.transform_subset

/-- Nonempty Step-5 core data suffice for the complete anchored data consumed
by the source-free local gluing assembly. -/
theorem nonempty_anchoredData_of_nonempty_copy4StepFiveCoreData
    {theta : ClosedRealOneOneForm n M} {W : Set M} {phiG : M -> EReal}
    (h : Nonempty (Copy4StepFiveCoreData theta W phiG)) :
    Nonempty (PrincipalizationStepSixAnchoredData theta W phiG) := by
  obtain ⟨d⟩ := h
  exact ⟨d.toAnchoredData⟩

/-- The primitive Step-5 presentation from the manuscript.  It replaces both
the already-combined exceptional-weight comparison and the compact
`eq:QM-lower` by their displayed inputs: five bounded divisor weights,
coefficient inequalities, the ambient convex-current lower bound, two
ideal/divisor comparisons, and the residual ideal presentation. -/
structure Copy4StepFiveExceptionalWeightData
    (theta : ClosedRealOneOneForm n M) (W : Set M) (phiG : M -> EReal) where
  y : M
  U : Set M
  beta : ClosedRealOneOneForm n M
  sigma : M -> Real
  rho : M -> EReal
  smooth_sigma : ChartSmooth (n := n) sigma
  dominates_beta : DominatesKahlerFormOn beta (fun x => (sigma x : EReal)) U
  positive_correction : IsThetaPshPotentialOn (theta - beta).val rho U
  smooth_rho_at_y : IsSmoothNear (n := n) rho y
  point_mem : y ∈ W
  open_neighbourhood : IsOpen U
  transform_subset : W ⊆ U
  psiDres : M -> EReal
  psiE : M -> EReal
  chi : M -> EReal
  phiQpi : M -> EReal
  psiD : M -> EReal
  psiGM : M -> EReal
  psiHfix : M -> EReal
  psiPmov : M -> EReal
  psiPF : M -> EReal
  psiJ : M -> EReal
  psiH : M -> EReal
  tau : Real
  lev : Real
  L : Real
  C : Real
  A : Real
  KGM : Real
  KHfix : Real
  KPmov : Real
  KPF : Real
  KJ : Real
  correction_eq : rho = fun x => psiD x + chi x
  divisor_split : ∀ x, psiD x = psiDres x + (tau : EReal) * psiE x
  polar_split : ∀ x, phiG x = phiQpi x + (tau : EReal) * psiE x
  hL : 0 < L
  hLlev : L < lev
  hA : 0 ≤ A
  hCA : L * A ≤ C - 1
  bound_GM : ∀ x, psiGM x ≤ (KGM : EReal)
  bound_Hfix : ∀ x, psiHfix x ≤ (KHfix : EReal)
  bound_Pmov : ∀ x, psiPmov x ≤ (KPmov : EReal)
  bound_PF : ∀ x, psiPF x ≤ (KPF : EReal)
  bound_J : ∀ x, psiJ x ≤ (KJ : EReal)
  divisor_weight : MoreSingularOn psiDres
    (fun x => ((1 / lev : Real) : EReal) * psiGM x
      + (((C - 1) / lev : Real) : EReal) * psiPmov x
      + ((C / lev : Real) : EReal) * psiPF x) univ
  correction_weight : MoreSingularOn chi
    (fun x => (((C - 1) / lev : Real) : EReal) * (psiJ x + psiHfix x)) univ
  H_weight : MoreSingularOn (fun x => psiHfix x + psiPmov x + psiPF x) psiH univ
  /-- The ambient data before it is pulled back to the collar.  This replaces
  the finished `eq:QM-lower` conclusion by the actual `eq:phiQ-lower`, its two
  divisor/ideal comparisons, and a presentation of the residual ideal. -/
  base : Type u
  [base_topology : TopologicalSpace base]
  [base_charted : ChartedSpace (ComplexModel n) base]
  [base_complex : IsComplexManifold n base]
  [base_compact : CompactSpace base]
  pi : M -> base
  psiBM : base -> EReal
  psiIV : base -> EReal
  psij : base -> EReal
  UM : base -> EReal
  PhiR : base -> EReal
  ambientUM_lower : MoreSingularOn
    (fun x => ((1 / lev : Real) : EReal) * psiBM x) UM univ
  ambientPhiR_source : @AmbientPhiRLowerSource n base base_topology base_charted
    base_complex base_compact A PhiR psiIV psij
  phiQpi_def : ∀ x, phiQpi x =
    convexComb (1 - L / lev) UM PhiR (pi x)
  psiJ_def : ∀ x, psiJ x = psij (pi x)
  ambientGM_source : AmbientGMLowerSource n base M pi psiBM psiGM
  psiIW : M -> EReal
  psiIW_coefficient : ℚ
  psiIW_ideal : GermIdeal n M
  psiIW_presentation : HasAnalyticSingularitiesOfType (n := n) psiIW
    psiIW_coefficient psiIW_ideal
  psiIW_zeroLocus : psiIW_ideal.zeroLocus = W
  ambientIV_source : AmbientIVLowerSource n base M pi psiIV psiH psiIW

/-- The exceptional-weight calculation is an internal theorem: it converts
the primitive Copy-4 Step-5 data to the two-comparison core used by the collar
reconstruction. -/
def Copy4StepFiveExceptionalWeightData.toCoreData
    {theta : ClosedRealOneOneForm n M} {W : Set M} {phiG : M -> EReal}
    [CompactSpace M]
    (d : Copy4StepFiveExceptionalWeightData theta W phiG) :
    Copy4StepFiveCoreData theta W phiG where
  y := d.y
  U := d.U
  beta := d.beta
  sigma := d.sigma
  rho := d.rho
  smooth_sigma := d.smooth_sigma
  dominates_beta := d.dominates_beta
  positive_correction := d.positive_correction
  smooth_rho_at_y := d.smooth_rho_at_y
  point_mem := d.point_mem
  open_neighbourhood := d.open_neighbourhood
  transform_subset := d.transform_subset
  psiDres := d.psiDres
  psiE := d.psiE
  chi := d.chi
  phiQpi := d.phiQpi
  psiD := d.psiD
  rhs := fun x => (((1 - d.L / d.lev) / d.lev : Real) : EReal) * d.psiGM x
    + ((d.L * d.A / d.lev : Real) : EReal) * (d.psiH x + d.psiJ x)
  tau := d.tau
  correction_eq := d.correction_eq
  divisor_split := d.divisor_split
  polar_split := d.polar_split
  exceptional_weight_comparison :=
    moreSingularOn_exceptionalWeightSum d.hL d.hLlev d.hA d.hCA
      d.bound_GM d.bound_Hfix d.bound_Pmov d.bound_PF d.bound_J
      d.divisor_weight d.correction_weight d.H_weight
  ambient_lower_comparison := by
    intro Lambda hLambda hLambdaUW
    have hlev : 0 < d.lev := lt_trans d.hL d.hLlev
    have hB1 : 0 ≤ (1 - d.L / d.lev) / d.lev := by
      apply div_nonneg
      · exact sub_nonneg.mpr ((div_lt_one hlev).mpr d.hLlev).le
      · exact hlev.le
    have hB2 : 0 ≤ d.L * d.A / d.lev := by
      exact div_nonneg (mul_nonneg d.hL.le d.hA) hlev.le
    have hphiQ : MoreSingularOn
        (fun x => (((1 - d.L / d.lev) / d.lev : Real) : EReal) * d.psiBM x
          + ((d.L * d.A / d.lev : Real) : EReal) * (d.psiIV x + d.psij x))
        (convexComb (1 - d.L / d.lev) d.UM d.PhiR) univ :=
      @moreSingularOn_phiQ_lower d.base d.base_topology d.UM d.PhiR d.psiBM
        d.psiIV d.psij d.L d.lev d.A d.hL d.hLlev d.ambientUM_lower
          (@AmbientPhiRLowerSource.moreSingularOn n d.base d.base_topology
            d.base_charted d.base_complex d.base_compact d.A d.PhiR d.psiIV d.psij
            d.ambientPhiR_source)
    obtain ⟨K, hK⟩ := exists_le_on_of_isCompact_disjoint_zeroLocus
      d.psiIW_presentation hLambda (by
        rw [d.psiIW_zeroLocus]
        exact Set.disjoint_left.mpr fun x hxLambda hxW => (hLambdaUW hxLambda).2 hxW)
    have hQM : MoreSingularOn
        (fun x => (((1 - d.L / d.lev) / d.lev : Real) : EReal) * d.psiGM x
          + ((d.L * d.A / d.lev : Real) : EReal) * (d.psiH x + d.psij (d.pi x)))
        (fun x => convexComb (1 - d.L / d.lev) d.UM d.PhiR (d.pi x)) Lambda :=
      moreSingularOn_ambientLowerBound hB1 hB2 hphiQ
        (@AmbientGMLowerSource.moreSingularOn n d.base M d.base_topology d.base_charted
          d.base_complex _ _ _ _ d.pi d.psiBM d.psiGM d.ambientGM_source)
        (@AmbientIVLowerSource.moreSingularOn n d.base M d.base_topology d.base_charted
          d.base_complex _ _ _ _ d.pi d.psiIV d.psiH d.psiIW d.ambientIV_source) hK
    refine (MoreSingularOn.of_le fun x _ => ?_).trans hQM |>.trans
      (MoreSingularOn.of_le fun x _ => le_of_eq (d.phiQpi_def x).symm)
    exact le_of_eq (by rw [d.psiJ_def x])

/-- The primitive exceptional-weight data therefore suffice for the complete
anchored Step-6 data without assuming the combined Step-5 inequality. -/
theorem nonempty_anchoredData_of_nonempty_copy4StepFiveExceptionalWeightData
    {theta : ClosedRealOneOneForm n M} {W : Set M} {phiG : M -> EReal}
    [CompactSpace M]
    (h : Nonempty (Copy4StepFiveExceptionalWeightData theta W phiG)) :
    Nonempty (PrincipalizationStepSixAnchoredData theta W phiG) := by
  obtain ⟨d⟩ := h
  exact ⟨d.toCoreData.toAnchoredData⟩

end

end Hironaka.PrincipalizationCopy4StepFiveCoreReduction
