import Hironaka.Resolution.HironakaG11TraceGermReflection

set_option autoImplicit false

/-! Local source containments persist along literal strict-transform towers. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11TraceGermTransport
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HomogenizedGlueingTower MemberInterTowerAlong MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG8TestTraceIdentity HironakaG11TraceGermReflection
  HironakaG11TraceGermDichotomy HironakaG11LocalTraceTransport
  BoundaryCount MemberInterAlong DivisorExponentAlong

/-- An inclusion of source germs persists as an inclusion of strict
transform germs at every endpoint over the source point. -/
theorem strictAlong_eventually_subset_of_eventually_subset
    {n : ℕ} {X Y : CMfd.{0} n} {A K : Set X} (T : BlowupTower X Y) {y : Y}
    (hsource : ∀ᶠ x in 𝓝 (T.proj y), x ∈ A → x ∈ K) :
    ∀ᶠ z in 𝓝 y, z ∈ strictAlong T A → z ∈ strictAlong T K := by
  obtain ⟨U,hUsub,hUopen,hyU⟩ := mem_nhds_iff.mp hsource
  let V : Opens X := ⟨U,hUopen⟩
  have hsub : ((Subtype.val : V → X) ⁻¹' A) ⊆ ((Subtype.val : V → X) ⁻¹' K) :=
    fun x hx => hUsub x.property hx
  have htr := strictAlong_mono (restrict V T) hsub
  rw [strictAlong_restrict V T A,strictAlong_restrict V T K] at htr
  filter_upwards [(openPreimage T V).isOpen.mem_nhds hyU] with z hz hzA
  exact htr (show (⟨z,hz⟩ : openPreimage T V) ∈
    (Subtype.val : openPreimage T V → Y) ⁻¹' strictAlong T A from hzA)

/-- Source trace-germ containment implies the corresponding transformed
carrier--boundary trace lies in the transformed old member near the endpoint. -/
theorem final_trace_germ_contained_of_initial
    {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (D K : Set X) (hD : D ∈ M.E) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) {y : Y}
    (hsource : ∀ᶠ x in 𝓝 (T.proj y), x ∈ M.N ∩ D → x ∈ K) :
    ∀ᶠ z in 𝓝 y, z ∈ strictAlong T M.N → z ∈ strictAlong T D → z ∈ strictAlong T K := by
  filter_upwards [strictAlong_eventually_subset_of_eventually_subset T hsource] with z hz hzN hzD
  exact hz (mem_strictAlong_inter_of_test M hM D hD T hT hzN hzD)


/-- For a well-formed literal test, smooth source trace containment is
reflected and preserved by the suffix at the actual endpoint. -/
theorem final_trace_germ_iff_initial
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (D K : Set X) (hD : D ∈ M.E) (hK : IsClosedSubmanifold n K)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) {y : Y}
    (hyN : y ∈ strictAlong T M.N) (hyD : y ∈ strictAlong T D) :
    (∀ᶠ z in 𝓝 y, z ∈ strictAlong T M.N → z ∈ strictAlong T D → z ∈ strictAlong T K) ↔
      (∀ᶠ x in 𝓝 (T.proj y), x ∈ M.N ∩ D → x ∈ K) := by
  constructor
  · intro hfinal
    obtain ⟨i,hi⟩ := List.get_of_mem hD
    have hA : IsClosedSubmanifold n (M.N ∩ D) := by
      have h := isClosedSubmanifold_inter_memberInter hn hM.isClosedSubmanifold_N.1
        hM.isSNCDivisor hM.isTransverse {i}
      rwa [memberInter_singleton,hi] at h
    have hyA := mem_strictAlong_inter_of_test M hM D hD T hT hyN hyD
    have hqA : T.proj y ∈ M.N ∩ D := strictAlong_subset_preimage T hA.1 hyA
    by_contra hnot
    obtain ⟨V,hqV,hDense⟩ := exists_local_dense_off_of_not_contained hA hK hqA hnot
    have hcl := strictAlong_dense_off_over_open (M.N ∩ D) K hK.1 V hDense T hqV hyA
    obtain ⟨z,hzfinal,hzA,hzK⟩ := (mem_closure_iff_nhds.mp hcl) _ hfinal
    exact hzK (hzfinal (strictAlong_mono T inter_subset_left hzA) (strictAlong_mono T inter_subset_right hzA))
  · exact final_trace_germ_contained_of_initial M hM D K hD T hT

end Hironaka.HironakaG11TraceGermTransport
