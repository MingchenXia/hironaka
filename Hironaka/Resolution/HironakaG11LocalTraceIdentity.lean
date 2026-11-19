import Hironaka.Resolution.HironakaG11LocalTraceTransport
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen

set_option autoImplicit false

/-! At an endpoint over a local well-formed test, the strict carrier and a
strict boundary member meet as the strict transform of their initial trace. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11LocalTraceIdentity
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  BoundaryCount MemberInterTowerAlong DivisorExponentAlong HironakaG11InvBMLower
  HironakaG8SuccExponents HironakaG11LocalTraceTransport

/-- The boundary-trace identity on a local test gives membership in the
literal ambient strict transform of the carrier--boundary intersection. -/
theorem mem_strictAlong_inter_of_local_test
    {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (U : Opens X)
    (hM : (MarkedIdeal.pullback (Subtype.val : U → X) M).IsWellFormed)
    (D : Set X) (hD : D ∈ M.E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T))
    {y : Y} (hyU : T.proj y ∈ U)
    (hyN : y ∈ strictAlong T M.N) (hyD : y ∈ strictAlong T D) :
    y ∈ strictAlong T (M.N ∩ D) := by
  let R := MarkedIdeal.pullback (Subtype.val : U → X) M
  have hmem : (Subtype.val : U → X) ⁻¹' D ∈ R.E := by
    change (Subtype.val : U → X) ⁻¹' D ∈ M.E.map (fun H => (Subtype.val : U → X) ⁻¹' H)
    exact List.mem_map.mpr ⟨D,hD,rfl⟩
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hmem
  have htrace := strictAlong_inter_memberInter R hM ({i} : Finset (Fin R.E.length)) (restrict U T) hT
  have htrace' : strictAlong (restrict U T) (R.N ∩ R.E.get i) =
      (geoTransformAlong R (restrict U T)).N ∩ strictAlong (restrict U T) (R.E.get i) := by
    simpa [BoundaryCount.memberInter] using htrace
  have hRN : R.N = (Subtype.val : U → X) ⁻¹' M.N := rfl
  rw [hRN, hi, ← preimage_inter, strictAlong_restrict U T (M.N ∩ D),
    N_geoTransformAlong, hRN, strictAlong_restrict U T M.N,
    strictAlong_restrict U T D] at htrace'
  have hz : (⟨y,hyU⟩ : openPreimage T U) ∈
      (Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T (M.N ∩ D) := by
    rw [htrace']
    exact ⟨hyN,hyD⟩
  exact hz


/-- Local birth-trace density and the literal local test rule out the
actual ambient exceptional-term divisibility after the suffix. -/
theorem not_div_of_local_trace_density
    {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (U V : Opens X)
    (hM : (MarkedIdeal.pullback (Subtype.val : U → X) M).IsWellFormed)
    (D H : Set X) (hD : D ∈ M.E) (hH : IsClosed H)
    (hDense : ((Subtype.val : V → X) ⁻¹' (M.N ∩ D)) ⊆
      closure (((Subtype.val : V → X) ⁻¹' (M.N ∩ D)) \
        ((Subtype.val : V → X) ⁻¹' H)))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T))
    {S : List (Set Y)} (hS : ∀ K ∈ S, IsClosed K)
    (hmem : strictAlong T H ∈ S) (e : ℕ) {y : Y}
    (hyU : T.proj y ∈ U) (hyV : T.proj y ∈ V)
    (hyN : y ∈ strictAlong T M.N) (hyD : y ∈ strictAlong T D) :
    ¬ IsDivNearAlong n (strictAlong T M.N) (exceptionalTermBM (n := n) S e)
      (strictAlong T D) 1 y := by
  have hytrace := mem_strictAlong_inter_of_local_test M U hM D hD T hT hyU hyN hyD
  have hcl := strictAlong_dense_off_over_open (M.N ∩ D) H hH V hDense T hyV hytrace
  intro hdiv
  obtain ⟨q,hqdiv,hqtrace,hqH⟩ := (mem_closure_iff_nhds.mp hcl) _ hdiv
  have hqN : q ∈ strictAlong T M.N := strictAlong_mono T inter_subset_left hqtrace
  have hqD : q ∈ strictAlong T D := strictAlong_mono T inter_subset_right hqtrace
  have hqCos := hqdiv hqN hqD
  exact hqH (mem_of_mem_cosupport_one_exceptionalTermBM (Y := Y) (S := S) (e := e) hS hqCos _ hmem)

end Hironaka.HironakaG11LocalTraceIdentity
