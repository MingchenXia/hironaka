import Hironaka.Resolution.HironakaG11LocalTraceIdentity
/-! # Trace density along a literal geometric test -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8TestTraceIdentity
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal BoundaryCount MemberInterTowerAlong
  DivisorExponentAlong HironakaG11InvBMLower HironakaG8SuccExponents HironakaG11LocalTraceTransport

/-- For a literal test, the carrier--member trace is the strict transform of
the initial trace. -/
theorem mem_strictAlong_inter_of_test
    {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (D : Set X) (hD : D ∈ M.E) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    {y : Y} (hyN : y ∈ strictAlong T M.N) (hyD : y ∈ strictAlong T D) :
    y ∈ strictAlong T (M.N ∩ D) := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hD
  have ht := strictAlong_inter_memberInter M hM ({i} : Finset (Fin M.E.length)) T hT
  have ht' : strictAlong T (M.N ∩ M.E.get i) =
      (geoTransformAlong M T).N ∩ strictAlong T (M.E.get i) := by
    simpa [BoundaryCount.memberInter] using ht
  rw [hi, N_geoTransformAlong] at ht'
  rw [ht']
  exact ⟨hyN, hyD⟩

/-- A dense initial trace escaping one selected exceptional-sum member rules
out its divisibility after any literal test suffix, without assumptions that
the suffix centres avoid that member. -/
theorem not_div_of_trace_density
    {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (V : Opens X) (D H : Set X) (hD : D ∈ M.E) (hH : IsClosed H)
    (hDense : ((Subtype.val : V → X) ⁻¹' (M.N ∩ D)) ⊆
      closure (((Subtype.val : V → X) ⁻¹' (M.N ∩ D)) \ ((Subtype.val : V → X) ⁻¹' H)))
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    {S : List (Set Y)} (hS : ∀ K ∈ S, IsClosed K)
    (hmem : strictAlong T H ∈ S) (e : ℕ) {y : Y}
    (hyV : T.proj y ∈ V) (hyN : y ∈ strictAlong T M.N) (hyD : y ∈ strictAlong T D) :
    ¬ IsDivNearAlong n (strictAlong T M.N) (exceptionalTermBM (n := n) S e)
      (strictAlong T D) 1 y := by
  have hytrace := mem_strictAlong_inter_of_test M hM D hD T hT hyN hyD
  have hcl := strictAlong_dense_off_over_open (M.N ∩ D) H hH V hDense T hyV hytrace
  intro hdiv
  obtain ⟨q,hqdiv,hqtrace,hqH⟩ := (mem_closure_iff_nhds.mp hcl) _ hdiv
  have hqN : q ∈ strictAlong T M.N := strictAlong_mono T inter_subset_left hqtrace
  have hqD : q ∈ strictAlong T D := strictAlong_mono T inter_subset_right hqtrace
  have hqCos := hqdiv hqN hqD
  exact hqH (mem_of_mem_cosupport_one_exceptionalTermBM (Y := Y) (S := S) (e := e) hS hqCos _ hmem)

end
end Hironaka.HironakaG8TestTraceIdentity
