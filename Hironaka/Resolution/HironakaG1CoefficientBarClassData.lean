import Hironaka.Resolution.HironakaG1GenericPositiveClassData
import Hironaka.Resolution.HironakaActualInitialNonmonomialCoefficientBoundary
import Hironaka.Resolution.HironakaG8HomStable

/-! Whole true-mark coefficient/bar class data from ordinary local pairs.
The coefficient support gap supplies normalized exponents internally.
Blueprint FIRST: hironaka-g1-coefficient-bar-class-data.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1CoefficientBarClassData
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HomogenizedIdealAlong CoefficientIdeal DivisorExponentAlong GermIdealOrder HironakaG8LocalHistory
  HironakaActualCoefficientDivisorExponentGap HironakaG8GapNormalizedExponent
  HironakaG8CoefficientBoundaryLocal HironakaG8HomStable
  HironakaActualInitialNonmonomialCoefficientBoundary StepOneValue

/-- The WHOLE actual coefficient ideal supplies its own marked support gap. -/
theorem coefficient_hasCosupportGap {n k : ℕ} {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain k P) : HasCosupportGap (coeffMarkedAlong P) := by
  intro x _hx hx
  have hgap := coefficient_restriction_cosupport_gap P hP.isWellFormed.isClosedSubmanifold_N
    hP.isWellFormed.isCoherent hP.one_le_d P.N (subset_refl P.N)
  change x ∈ cosupport n P.N (coeffMarkedAlong P).ideal (coeffMarkedAlong P).d
  rw [←hgap]
  exact hx

/-- Ordinary local source data produce the actual whole coefficient
domains, carrier/boundary equality, local relation and normalized exponents. -/
theorem coefficient_class_data {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : P.N = Q.N) (hL : LocWPEquiv P Q) :
    let C := coeffMarkedAlong P
    let D := coeffMarkedAlong Q
    IsInvDomain k C ∧ IsInvDomain l D ∧ C.N = D.N ∧ C.E = D.E ∧ LocWPEquiv C D ∧
      (∀ H ∈ C.E, ∀ x ∈ C.cosupp, x ∈ H →
        D.d * divExpAlong n C.N C.ideal H x = C.d * divExpAlong n D.N D.ideal H x) := by
  let C := coeffMarkedAlong P
  let D := coeffMarkedAlong Q
  have hC : IsInvDomain k C := coefficient_isInvDomain P hP
  have hD : IsInvDomain l D := coefficient_isInvDomain Q hQ
  have hCN : C.N = D.N := hN
  have hCE : C.E = D.E := hL.wEquiv.1
  have hCL : LocWPEquiv C D :=
    ((coefficient_local_any_boundary P hP).symm.trans hL).trans (coefficient_local_any_boundary Q hQ)
  have hgapC : HasCosupportGap C := coefficient_hasCosupportGap P hP
  have hgapD : HasCosupportGap D := coefficient_hasCosupportGap Q hQ
  refine ⟨hC,hD,hCN,hCE,hCL,?_⟩
  change ∀ H ∈ C.E, ∀ x ∈ C.cosupp, x ∈ H →
    D.d * divExpAlong n C.N C.ideal H x = C.d * divExpAlong n D.N D.ideal H x
  intro H hH x hx hxH
  obtain ⟨i,hi⟩ := List.get_of_mem hH
  have hHD : H ∈ D.E := hCE ▸ hH
  obtain ⟨j,hj⟩ := List.get_of_mem hHD
  have hExp := normalized_exponent_of_cosupport_gap hn C D hC hD hCN hCL hgapC hgapD
    i j (hi.trans hj.symm) (C.cosupp_subset_N hx) (hi.symm ▸ hxH)
  simpa only [hi,hj] using hExp

/-- The SAME original whole homogenized-coefficient bar records carry
the derived class data at their actual native coefficient-product marks. -/
theorem bar_class_data {n k l : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : P.N = Q.N) (hL : LocWPEquiv P Q) :
    let C := barMarked P
    let D := barMarked Q
    IsInvDomain k C ∧ IsInvDomain l D ∧ C.N = D.N ∧ C.E = D.E ∧ LocWPEquiv C D ∧
      (∀ H ∈ C.E, ∀ x ∈ C.cosupp, x ∈ H →
        D.d * divExpAlong n C.N C.ideal H x = C.d * divExpAlong n D.N D.ideal H x) := by
  have hHP := hom_isInvDomain P hP
  have hHQ := hom_isInvDomain Q hQ
  have hHL : LocWPEquiv (homMarkedAlong P) (homMarkedAlong Q) :=
    ((hom_local_any_boundary P hP).symm.trans hL).trans (hom_local_any_boundary Q hQ)
  exact coefficient_class_data hn (homMarkedAlong P) (homMarkedAlong Q) hHP hHQ hN hHL

end
end Hironaka.HironakaG1CoefficientBarClassData
