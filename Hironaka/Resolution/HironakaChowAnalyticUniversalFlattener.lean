import Hironaka.Resolution.HironakaChowAnalyticPullbackCoefficientIdeal
import Hironaka.Resolution.HironakaChowSameDivisionQuotientFlatness

/-! One ORIGINAL local analytic coefficient ideal before ALL target maps/ideals.
Uses the genuine SAME-family whole-ideal producer and ANY actual SAME division
quotient criterion. No tensor realization or proper/global flattening claim.
BP FIRST: hironaka-g10-analytic-universal-flattener.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology
namespace Hironaka.HironakaChowAnalyticUniversalFlattener
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaActualAnalyticBaseChangeCoefficients
  HironakaChowOriginalFlattenerCoefficients
  HironakaChowAnalyticPullbackCoefficientIdeal
  HironakaChowSameDivisionQuotientFlatness

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/-- ORIGINAL I alone chooses ONE finitely generated p before ALL analytic maps and target ideals. -/
theorem exists_original_analytic_universal_flattening_ideal
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ p : Ideal (HolGerm (ComplexModel d)), p.FG ∧
      ∀ (e : ℕ) (φ : ComplexModel e → ComplexModel d)
        (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
        (a : Ideal (HolGerm (ComplexModel e))),
        Module.Flat (HolGerm (ComplexModel e) ⧸ a)
          (HolGerm (ComplexModel (e+t)) ⧸
            (Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I ⊔
              Ideal.map (tangentPullback e t).toRingHom a)) ↔
        Ideal.map (compAlgHom φ hφ hφ0).toRingHom p ≤ a := by
  obtain ⟨P,eA,hEA,hFG,_hOriginal⟩ := exists_original_quotient_flattening_ideal d t I
  refine ⟨coefficientIdeal d t I eA,hFG,?_⟩
  intro e φ hφ hφ0 a
  obtain ⟨PB,eB,_hFib,_hWeight,_hBound,_hLift,hEB,_hRnat,_hWhole,hCoeff⟩ :=
    exists_base_changed_coefficient_ideal d e t I P eA hEA φ hφ hφ0
  rw [← hCoeff]
  exact flat_original_quotient_iff e t _ PB eB hEB a

end
end Hironaka.HironakaChowAnalyticUniversalFlattener
