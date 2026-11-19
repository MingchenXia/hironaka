import Hironaka.Resolution.HironakaG11BirthTraceTransfer
import Hironaka.Resolution.HironakaG11IntrinsicTangentTransfer

set_option autoImplicit false

/-! Above-mark directrix comparison transfers an actual local birth trace. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11BirthTraceDirectrix
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold BlowupSpaceTangent MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GermIdealOrder DivisorExponentAlong HironakaG8LocalHistory
  HironakaG11InvBMClass HironakaG11IntrinsicTangentTransfer HironakaG11BirthTraceTransfer

/-- For locally weakly equivalent source records, actual birth-trace
containment transfers to the other carrier when the coefficient order is
above the mark on nearby centre points and both coefficient germs are nonzero. -/
theorem birth_trace_transfer_of_above_mark
    {n : ℕ} {X Y : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (h : LocWPEquiv P Q) (hP : IsClosedSubmanifold n P.N) (hQ : IsClosedSubmanifold n Q.N)
    (hIP : P.ideal.IsCoherent) (hIQ : Q.ideal.IsCoherent) (hE : IsSNCDivisor n P.E)
    (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {C H : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hH : IsClosedSubmanifold n H) (hCP : C ⊆ P.N) (hCQ : C ⊆ Q.N)
    {p : Y} (hp : p ∈ geoStrictTransform π C P.N) (hpC : π p ∈ C)
    (hCH : ∀ᶠ x in 𝓝 (π p), x ∈ C → x ∈ H)
    (htrace : ∀ᶠ q in 𝓝 p, q ∈ geoStrictTransform π C P.N → π q ∈ C →
      q ∈ geoStrictTransform π C H)
    (hdata : ∀ᶠ x in 𝓝 (π p), x ∈ C → x ∈ P.cosupp ∧
      IsNonzeroAlongAt P.N P.ideal x ∧ IsNonzeroAlongAt Q.N Q.ideal x ∧
      x ∈ cosupport n P.N P.ideal (P.d+1)) :
    ∀ᶠ q in 𝓝 p, q ∈ geoStrictTransform π C Q.N → π q ∈ C →
      q ∈ geoStrictTransform π C H := by
  apply birth_trace_germ_transfer hπ hP hQ hH hCP hCQ hp hpC hCH htrace
  filter_upwards [hdata,hCH] with x hx hxH hxC htan
  obtain ⟨hcos,hp,hq,hord⟩ := hx hxC
  exact (tangent_le_iff_of_locWPEquiv_order_gt P Q h hP hQ hIP hIQ hE hd1 hd hdim
    hcos hp hq hord (hxH hxC)).mp htan

end Hironaka.HironakaG11BirthTraceDirectrix
