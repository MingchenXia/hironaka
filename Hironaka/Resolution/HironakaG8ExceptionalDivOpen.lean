import Hironaka.Resolution.HironakaG11InvBMExceptionalTerm
import Hironaka.Resolution.HironakaG11InvBMLowerDomainSucc
import Hironaka.Invariant.MonomialInvariantFunctorialAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
/-! # Exceptional-term divisibility on an open subset -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8ExceptionalDivOpen
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  GermIdealOrder DivisorExponentAlong HironakaG11InvBMLower HironakaG11InvBMExceptionalTerm
  MarkedIdealOperationsAlong.MarkedIdeal

/-- Divisibility of an exceptional sum by a boundary member is unchanged
when all sets and ideals are restricted to an open neighbourhood. -/
theorem isDivNearAlong_exceptionalTermBM_pullback_val_iff
    {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (W : Opens M) {S : List (Set M)} (hS : ∀ H ∈ S, IsClosedSubmanifold n H) (hSne : S ≠ [])
    (N H : Set M) (e k : ℕ) (x : W) :
    IsDivNearAlong n ((Subtype.val : W → M) ⁻¹' N)
      (exceptionalTermBM (n := n) (S.map ((Subtype.val : W → M) ⁻¹' ·)) e)
      ((Subtype.val : W → M) ⁻¹' H) k x ↔
    IsDivNearAlong n N (exceptionalTermBM (n := n) S e) H k x.val := by
  have hhol := hol_of_isCoherent (HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hS e)
  have hcos : ∀ j, cosupport n ((Subtype.val : W → M) ⁻¹' N)
      (GermIdeal.pullback (m := n) (Subtype.val : W → M) (exceptionalTermBM (n := n) S e)) j =
      (Subtype.val : W → M) ⁻¹' cosupport n N (exceptionalTermBM (n := n) S e) j :=
    fun j => cosupp_pullback_val (⟨N, [], exceptionalTermBM (n := n) S e, j⟩ : MarkedIdeal n M) hhol W
  have hmap : Filter.map (Subtype.val : W → M) (𝓝 x) = 𝓝 x.val :=
    map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ (W : Set M)) x.2 (W.isOpen.mem_nhds x.2)
  rw [← pullback_val_exceptionalTermBM W hS hSne]
  exact MonomialInvariantFunctorialAlong.isDivNearAlong_pullback_iff hcos hmap H k

end
end Hironaka.HironakaG8ExceptionalDivOpen
