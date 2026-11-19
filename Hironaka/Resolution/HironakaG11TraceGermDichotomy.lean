import Hironaka.Resolution.HironakaG11LocalTraceTransport
import Hironaka.Resolution.HironakaG8DomainExponents
import Hironaka.Coherence.VanishingIdealCoherent

set_option autoImplicit false

/-! A smooth trace and a smooth old member have a local containment/density
dichotomy, suitable for transporting source trace information through an
arbitrary actual suffix. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11TraceGermDichotomy
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  DivisorExponentAlong GiraudAlong NormalCrossings HironakaG8DomainExponents

/-- If a smooth trace is not locally contained in a smooth closed member,
then on an open neighbourhood of the point it is dense away from that
member. -/
theorem exists_local_dense_off_of_not_contained
    {n : ℕ} {X : CMfd.{0} n} {A K : Set X}
    (hA : IsClosedSubmanifold n A) (hK : IsClosedSubmanifold n K)
    {q : X} (hqA : q ∈ A) (hnot : ¬ ∀ᶠ x in 𝓝 q, x ∈ A → x ∈ K) :
    ∃ U : Opens X, q ∈ U ∧
      ((Subtype.val : U → X) ⁻¹' A) ⊆
        closure (((Subtype.val : U → X) ⁻¹' A) \ ((Subtype.val : U → X) ⁻¹' K)) := by
  have hc := VanishingIdealCoherent.isCoherent_vanishingIdeal hK
  have hnz : IsNonzeroAlongAt A (vanishingIdeal (n := n) K) q := by
    by_contra hz
    have hzero := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt hc hz
    apply hnot
    filter_upwards [hzero] with z hz hzA
    have hcos : z ∈ cosupport n A (vanishingIdeal (n := n) K) 1 :=
      ⟨hzA,fun g hg => ⟨fun _ => 0,zero_mem_idealPow _ z 1,hz g hg⟩⟩
    rw [SmoothCentreLocus.cosupport_vanishingIdeal_one hK.1] at hcos
    exact hcos.2
  let M : MarkedIdeal n X := ⟨A,[],vanishingIdeal (n := n) K,1⟩
  have hM : M.IsWellFormed := ⟨hA,hc,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hA⟩
  let U : Opens X := domOpen M hA
  have hdM : 1 ≤ M.d := by change 1 ≤ 1; omega
  have hqU : q ∈ U := (mem_domOpen_iff (P := M) hA hc hdM hqA).mpr hnz
  refine ⟨U,hqU,?_⟩
  intro x hxA
  have hxNZ : IsNonzeroAlongAt A (vanishingIdeal (n := n) K) (x : X) :=
    (mem_domOpen_iff (P := M) hA hc hdM hxA).mp x.property
  obtain ⟨g,hg,hfreq⟩ := hxNZ
  have hcl : (x : X) ∈ closure (A \ K) := by
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨z,⟨⟨hzA,hzne⟩,hzK⟩,hzV⟩ := ((hfreq.and_eventually hg.2).and_eventually hV).exists
    exact ⟨z,hzV,hzA,fun hz => hzne (hzK hz)⟩
  have hEq : (Subtype.val : U → X) ⁻¹' closure (A \ K) =
      closure ((Subtype.val : U → X) ⁻¹' (A \ K)) :=
    U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val _
  have hxcl : x ∈ (Subtype.val : U → X) ⁻¹' closure (A \ K) := hcl
  rw [hEq] at hxcl
  simpa only [preimage_sdiff] using hxcl

end Hironaka.HironakaG11TraceGermDichotomy
