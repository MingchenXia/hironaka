import Hironaka.Resolution.HironakaG4WindowResidualTrace
import Hironaka.Analytic.GeneratorMultiplicityOne
import Hironaka.Invariant.InvDomainMemberRestriction
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent

/-! A principal equation of an SNC member has nonzero first jet in any actual flat chart. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4SmoothMemberJet
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings NormalCrossingsComparison BlowupFlatCoordinates GiraudAlong DerivativeIdeal
  DerivativeIdealAlongCoherent GeneratorMultiplicityOne InvDomainMemberRestriction
  MonomialPart RelativePrincipalizationSpan BoundaryCount SimultaneousNormalCrossings

variable {n : ℕ} {X : CMfd.{u} n}

/-- An actual principal equation for an incident SNC member has a nonzero
model derivative in any centered holomorphic chart. -/
theorem smooth_member_principal_flat_jet_ne_zero (hn : 0 < n)
    {L : List (Set X)} {H : Set X} {x : X} (hL : IsSNCDivisor n L) (hHL : H ∈ L)
    (hxH : x ∈ H) {f : X → ℂ} (hf : HolomorphicAt n f x)
    (hF : ∀ g, (vanishingIdeal (n := n) H).mem x g ↔ IsInSpanAt (n := n) (· = f) x g)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    f x = 0 ∧ fderiv ℂ (f ∘ flatInv Φ) 0 ≠ 0 := by
  have hfmem : (vanishingIdeal (n := n) H).mem x f := (hF f).mpr
    (isInSpanAt_eq_iff.mpr ⟨hf, 1, holomorphicAt_const 1, Eventually.of_forall fun _ => by simp⟩)
  have hf0 : f x = 0 := hfmem.2.self_of_nhds hxH
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hHL
  have heq : memberInter L {i} = H := by
    calc memberInter L {i} = L.get i := by ext y; simp [memberInter]
         _ = H := hi
  have hmem : x ∈ memberInter L {i} := by rw [heq]; exact hxH
  have hregU : RegularAtDim (n := n) (univ : Set X) x n := AnalyticIrreducibleComponents.regularAtDim_univ x
  obtain ⟨j, hj, hjreg⟩ := exists_regularAtDim_inter_memberInter_lt hn hL
    (isTransverse_univ_of_isSNCDivisor hL) (show ({i} : Finset (Fin L.length)).Nonempty by simp)
    (show x ∈ (univ : Set X) ∩ memberInter L {i} from ⟨mem_univ _, hmem⟩) hregU
  have hreg : RegularAtDim (n := n) H x j := by
    simpa only [Set.univ_inter, heq] using hjreg
  obtain ⟨e, v, he, hne⟩ := exists_chartDeriv_ne_zero_of_vanishingIdeal_eq_span hreg hj hf hF
  refine ⟨hf0, ?_⟩
  intro hzero
  have hsum := chartDeriv_eq_sum_flat hsrc e v he (mem_flatDomain_self Φ) hf
  have hflat0 : flatMap Φ x = 0 := h0
  rw [hflat0, hzero] at hsum
  simp at hsum
  exact hne hsum

end
end Hironaka.HironakaG4SmoothMemberJet
