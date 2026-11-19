import Hironaka.Resolution.HironakaG8CaseTBoundaryReorder
import Hironaka.Resolution.HironakaG8CaseTLocalReorder

/-!
# Tangent order comparison with transverse ambient carriers

The common hypersurface-frame open, exact boundary slot permutation and
singleton-cut comparison combine on the original records. The ambient
carriers are explicit source data.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseTAmbientComparison
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen NormalCrossings NormalCrossingsInvariance DivisorExponentAlong GermIdealOrder
  HironakaG8LocalHistory HironakaG8CaseTCommonRemainder HironakaG8CaseTBoundaryReorder
  HironakaG8CaseTLocalReorder
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaG8ClassStepHistory (OrdAgreeBelowAt)
open HironakaStepOneZeroContactRemainderGlueing (isNonzeroAlongAt_pullback_val_iff)

/-- A selected tangent member gives the original order agreement on a common
open when each carrier is a hypersurface in an SNC-transverse ambient carrier. -/
theorem ordAgreeBelowAt_of_transverse_ambient_carriers
    {n m : ℕ} {X : CMfd.{u} n} (P Q : MarkedIdeal n X)
    (h : LocWPEquiv P Q) (hNP : IsClosedSubmanifold n P.N)
    (hNQ : IsClosedSubmanifold n Q.N) (hIP : P.ideal.IsCoherent)
    (hIQ : Q.ideal.IsCoherent) (hE : IsSNCDivisor n P.E)
    (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {x : X} (hx : x ∈ P.cosupp)
    (hxP : IsNonzeroAlongAt P.N P.ideal x)
    (hxQ : IsNonzeroAlongAt Q.N Q.ideal x)
    (hP : RegularAtDim (n := n) P.N x m) (hQ : RegularAtDim (n := n) Q.N x m)
    (NP NQ : Set X) (hNPdim : RegularAtDim (n := n) NP x (m+1))
    (hNQdim : RegularAtDim (n := n) NQ x (m+1))
    (hPsub : P.N ⊆ NP) (hQsub : Q.N ⊆ NQ)
    (hTransP : IsTransverse n NP P.E) (hTransQ : IsTransverse n NQ P.E)
    (i : Fin P.E.length) (hH : IsClosedSubmanifold n (P.E.get i)) (hxH : x ∈ P.E.get i)
    (hTP : x ∈ cosupport n P.N (vanishingIdeal (n := n) (P.E.get i)) 2)
    (hTQ : x ∈ cosupport n Q.N (vanishingIdeal (n := n) (P.E.get i)) 2) :
    OrdAgreeBelowAt P Q x := by
  obtain ⟨U, hxU, hSU, hPU, hQU⟩ :=
    exists_common_remainder_transverse_open hP hQ hNPdim hNQdim hPsub hQsub
      P.E hE hTransP hTransQ i hxH hTP hTQ
  let p : U := ⟨x, hxU⟩
  let L := P.E.get i :: P.E.eraseIdx i.val
  let P' : MarkedIdeal n X := { P with E := L }
  let Q' : MarkedIdeal n X := { Q with E := L }
  let A := MarkedIdeal.pullback (Subtype.val : U → X) P'
  let B := MarkedIdeal.pullback (Subtype.val : U → X) Q'
  let H : Set U := (Subtype.val : U → X) ⁻¹' P.E.get i
  let G : List (Set U) := (P.E.eraseIdx i.val).map ((Subtype.val : U → X) ⁻¹' ·)
  have hL : LocWPEquiv P' Q' := locWPEquiv_get_cons_eraseIdx h i
  have hR : LocWPEquiv (X := CMfd.of (n := n) U) A B := LocEquiv.restrict hL U
  have hSNC' : IsSNCDivisor n P'.E := isSNCDivisor_get_cons_eraseIdx P.E i hE
  have hSNCU : IsSNCDivisor n A.E :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hSNC'
  have hcohP : A.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hIP
  have hcohQ : B.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hIQ
  have hwA : ({ A with E := G } : MarkedIdeal n (CMfd.of (n := n) U)).IsWellFormed :=
    ⟨BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNP U, hcohP, hSU, hPU⟩
  have hwB : ({ B with E := G } : MarkedIdeal n (CMfd.of (n := n) U)).IsWellFormed :=
    ⟨BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNQ U, hcohQ, hSU, hQU⟩
  have hholP : ∀ y f, P'.ideal.mem y f → HolomorphicAt n f y :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIP hf
  have hholQ : ∀ y f, Q'.ideal.mem y f → HolomorphicAt n f y :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIQ hf
  have hpA : p ∈ A.cosupp := by
    rw [cosupp_pullback_val P' hholP U]
    exact hx
  have hdimU : SameCarrierDim (X := CMfd.of (n := n) U) A B :=
    HironakaG8SpecialLoci.sameCarrierDim_pullback_val hholP hdim U
  have hnzA : IsNonzeroAlongAt A.N A.ideal p :=
    (isNonzeroAlongAt_pullback_val_iff hIP U p).mpr hxP
  have hnzB : IsNonzeroAlongAt B.N B.ideal p :=
    (isNonzeroAlongAt_pullback_val_iff hIQ U p).mpr hxQ
  have htA : p ∈ cosupport n A.N (vanishingIdeal (n := n) H) 2 :=
    (HironakaG8CaseNOpenTransport.cosupport_vanishingIdeal_pullback_val P.N (P.E.get i) U p).mpr hTP
  have htB : p ∈ cosupport n B.N (vanishingIdeal (n := n) H) 2 :=
    (HironakaG8CaseNOpenTransport.cosupport_vanishingIdeal_pullback_val Q.N (P.E.get i) U p).mpr hTQ
  have hAgreement := HironakaG8CaseTSingleCutOrder.ordAgreeBelowAt_of_single_tangent_cut
    (X := CMfd.of (n := n) U) A B G H hR rfl hSNCU (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hH U)
    hwA hwB hd hd1 hdimU hpA hnzA hnzB htA htB
  intro e he
  have hAcos := cosupp_pullback_val (⟨P.N, L, P.ideal, e⟩ : MarkedIdeal n X) hholP U
  have hBcos := cosupp_pullback_val (⟨Q.N, L, Q.ideal, e⟩ : MarkedIdeal n X) hholQ U
  have hPoint := hAgreement e he
  change p ∈ cosupport n A.N A.ideal e ↔ p ∈ cosupport n B.N B.ideal e at hPoint
  change p ∈ (MarkedIdeal.pullback (Subtype.val : U → X)
    (⟨P.N, L, P.ideal, e⟩ : MarkedIdeal n X)).cosupp ↔
    p ∈ (MarkedIdeal.pullback (Subtype.val : U → X)
    (⟨Q.N, L, Q.ideal, e⟩ : MarkedIdeal n X)).cosupp at hPoint
  rw [hAcos, hBcos] at hPoint
  exact hPoint

end
end Hironaka.HironakaG8CaseTAmbientComparison
