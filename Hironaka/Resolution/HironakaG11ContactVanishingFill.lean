import Hironaka.Resolution.HironakaG11ResidualCoefficientNonzero
import Hironaka.Resolution.HironakaG8CaseTContactPair
import Hironaka.MarkedIdeal.CodimOneSupport

set_option autoImplicit false

/-! If one contact coefficient vanishes along its carrier, equal
cosupport and equal dimensions identify the two local carrier germs. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ContactVanishingFill
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers DivisorExponentAlong MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaG8LocalHistory HironakaG11InvBMClass GiraudAlong

/-- Equal cosupports and carrier dimensions force equal carrier germs when
the first coherent ideal vanishes identically along its carrier germ. -/
theorem eventually_carriers_equal_of_coefficient_vanishes
    {n : ℕ} {X : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : P.IsWellFormed)
    (hcos : P.cosupp = Q.cosupp) (hdim : SameCarrierDim P Q)
    {y : X} (hy : y ∈ P.cosupp) (hnz : ¬ IsNonzeroAlongAt P.N P.ideal y) :
    ∀ᶠ z in 𝓝 y, z ∈ P.N ↔ z ∈ Q.N := by
  have hzero := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt hP.isCoherent hnz
  have hsub : ∀ᶠ z in 𝓝 y, z ∈ P.N → z ∈ Q.N := by
    filter_upwards [hzero] with z hz hzP
    have hzc : z ∈ P.cosupp := ⟨hzP,fun g hg => ⟨fun _ => 0,zero_mem_idealPow _ z P.d,hz g hg⟩⟩
    exact Q.cosupp_subset_N (hcos ▸ hzc)
  obtain ⟨k,hPk⟩ := hP.isClosedSubmanifold_N.2 y (P.cosupp_subset_N hy)
  have hQk : RegularAtDim (n := n) Q.N y k := (hdim y hy k).mp hPk
  have hback : ∀ᶠ z in 𝓝 y, z ∈ Q.N → z ∈ P.N :=
    CodimOneSupport.eventually_mem_of_locDimGE
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hP.isClosedSubmanifold_N)
      hQk hsub (AnalyticDimensionBasics.locDimGE_of_regularAtDim hPk)
  exact (hsub.and hback).mono fun _ h => ⟨h.1,h.2⟩


/-- In the vanishing branch, every closed-list trace condition is shared
by the two carrier germs. -/
theorem trace_iff_of_coefficient_vanishes
    {n : ℕ} {X : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : P.IsWellFormed) (hcos : P.cosupp = Q.cosupp) (hdim : SameCarrierDim P Q)
    {y : X} (hy : y ∈ P.cosupp) (hnz : ¬ IsNonzeroAlongAt P.N P.ideal y)
    (H : Set X) (S : List (Set X)) :
    (∀ᶠ z in 𝓝 y, z ∈ P.N → z ∈ H → ∀ D ∈ S, z ∈ D) ↔
      (∀ᶠ z in 𝓝 y, z ∈ Q.N → z ∈ H → ∀ D ∈ S, z ∈ D) := by
  have hcar := eventually_carriers_equal_of_coefficient_vanishes P Q hP hcos hdim hy hnz
  constructor
  · intro h
    filter_upwards [h,hcar] with z hz hc hzQ hzH
    exact hz (hc.mpr hzQ) hzH
  · intro h
    filter_upwards [h,hcar] with z hz hc hzP hzH
    exact hz (hc.mp hzP) hzH

end Hironaka.HironakaG11ContactVanishingFill
