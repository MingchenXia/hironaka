import Hironaka.Resolution.HironakaG8ScaledCompanionLocal
import Hironaka.Resolution.HironakaG8CompanionScaledHistory
import Hironaka.Resolution.HironakaG8LocalCompanion
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaG8ScaledCompanionStageOpen
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec InvDomainTowerAlong
  DivisorExponentAlong NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase
  HironakaG8LocalHistory HironakaG8ScaledExponentHistory HironakaG8ScaledCompanionLocal
  HironakaG8CompanionScaledHistory HironakaG8LocalCompanion HironakaCoherentTransformExtension
  GermIdealOrder RelativePrincipalizationSpan

/-- Cross-scaled incident exponents restrict to arbitrary open subsets. -/
theorem scaled_incident_exponents_pullback {n : ℕ} {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X)
    (hP : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x)
    (hQ : ∀ x g, Q.ideal.mem x g → HolomorphicAt n g x)
    (h : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (U : Opens X) :
    let P' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) P
    let Q' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → X) Q
    ∀ H ∈ P'.E, ∀ x ∈ P'.cosupp, x ∈ H →
      Q'.d * divExpAlong n P'.N P'.ideal H x = P'.d * divExpAlong n Q'.N Q'.ideal H x := by
  dsimp only
  intro H' hH' y hy hyH'
  obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
  have hcosP : ∀ e, cosupport n ((Subtype.val : U → X) ⁻¹' P.N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) P.ideal) e = (Subtype.val : U → X) ⁻¹' cosupport n P.N P.ideal e :=
    fun e => MarkedIdealRestrictOpen.cosupp_pullback_val (⟨P.N, [], P.ideal, e⟩ : MarkedIdeal n X) hP U
  have hcosQ : ∀ e, cosupport n ((Subtype.val : U → X) ⁻¹' Q.N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) Q.ideal) e = (Subtype.val : U → X) ⁻¹' cosupport n Q.N Q.ideal e :=
    fun e => MarkedIdealRestrictOpen.cosupp_pullback_val (⟨Q.N, [], Q.ideal, e⟩ : MarkedIdeal n X) hQ U
  have hmap : Filter.map (Subtype.val : U → X) (𝓝 y) = 𝓝 (y : X) :=
    map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ (U : Set X)) y.2 (U.isOpen.mem_nhds y.2)
  have hy' : (y : X) ∈ P.cosupp := by
    have h1 := MarkedIdealRestrictOpen.cosupp_pullback_val P hP U
    have h2 : y ∈ (MarkedIdeal.pullback (Subtype.val : U → X) P).cosupp := hy
    rw [h1] at h2
    exact h2
  change Q.d * divExpAlong n ((Subtype.val : U → X) ⁻¹' P.N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) P.ideal)
      ((Subtype.val : U → X) ⁻¹' H) y =
    P.d * divExpAlong n ((Subtype.val : U → X) ⁻¹' Q.N) (GermIdeal.pullback (m := n) (Subtype.val : U → X) Q.ideal)
      ((Subtype.val : U → X) ⁻¹' H) y
  rw [MonomialInvariantFunctorialAlong.divExpAlong_pullback hcosP hmap H,
    MonomialInvariantFunctorialAlong.divExpAlong_pullback hcosQ hmap H]
  exact h H hH y hy' hyH'

/-- At every actual common test stage, companions of the restricted transforms
at cross-scaled positive orders are locally equivalent on any smaller order open. -/
theorem scaled_companions_local_stage_open {n k l : ℕ} (hn : 0<n) {X Y : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : Q.N=P.N) (hE : Q.E=P.E) (hL : LocWPEquiv P Q)
    (hInitial : ∀ H ∈ P.E, ∀ y ∈ P.cosupp, y ∈ H →
      Q.d * divExpAlong n P.N P.ideal H y = P.d * divExpAlong n Q.N Q.ideal H y)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T)
    {oP oQ : ℕ} (hoP : 1≤oP) (hOrder : Q.d*oP=P.d*oQ)
    (U : Opens Y) (hU : U ≤ ordMask (geoTransformAlong P T) oP) :
    let P' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U→Y) (geoTransformAlong P T)
    let Q' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U→Y) (geoTransformAlong Q T)
    LocWPEquiv (companionOf n P' oP) (companionOf n Q' oQ) := by
  let PT := geoTransformAlong P T
  let QT := geoTransformAlong Q T
  have hTQ : IsGeoTestTower Q T := (hL.wEquiv.2 T).1.mp hT
  have hPT := isInvDomain_geoTransformAlong hP T hT
  have hQT := isInvDomain_geoTransformAlong hQ T hTQ
  have hL' := (hL.geoTransformAlong T hT).restrict U
  have hNP : QT.N=PT.N := geoTransformAlong_N_eq_of_N_eq hN T
  have hExp := scaled_exponents_of_initial_agreement P Q hP hQ hN hE hL hInitial T hT
  have hExp' := scaled_incident_exponents_pullback PT QT
    (fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hPT.isWellFormed.isCoherent hg)
    (fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hQT.isWellFormed.isCoherent hg)
    (by simpa only [PT,QT,d_geoTransformAlong] using hExp) U
  let P' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U→Y) PT
  let Q' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U→Y) QT
  have hP' : IsInvDomain k P' := isInvDomain_pullback_val U hPT
  have hQ' : IsInvDomain l Q' := isInvDomain_pullback_val U hQT
  have hN' : Q'.N=P'.N := by change (Subtype.val : U→Y) ⁻¹' QT.N = (Subtype.val : U→Y) ⁻¹' PT.N; rw [hNP]
  have hBound : ∀ x ∈ P'.cosupp, x ∉ ordGe P' (oP+1) := by
    intro x _ hx
    have hx' : (x : Y) ∈ ordGe PT (oP+1) :=
      (mem_ordGe_pullback_val_iff hn hPT.isWellFormed hPT.isNonzeroAlongAt U (oP+1) x).mp hx
    exact (mem_ordMask_iff hn hPT.isWellFormed hPT.isNonzeroAlongAt oP x).mp (hU x.2) hx'
  exact scaled_companions_local hn P' Q' hP' hQ' hN' hL' hExp' hoP (by simpa [P',Q',PT,QT,MarkedIdeal.pullback,d_geoTransformAlong] using hOrder) hBound
/-- At an actual positive-order head, the intersection of the independently
chosen order masks contains the head and carries locally equivalent companions. -/
theorem scaled_companions_local_actual_mask_inter {n k l : ℕ} (hn : 0<n) {X Y : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : Q.N=P.N) (hE : Q.E=P.E) (hL : LocWPEquiv P Q)
    (hInitial : ∀ H ∈ P.E, ∀ y ∈ P.cosupp, y ∈ H →
      Q.d * divExpAlong n P.N P.ideal H y = P.d * divExpAlong n Q.N Q.ideal H y)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T)
    (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp)
    (ho : 1 ≤ nmOrd (geoTransformAlong P T) y) :
    let PT := geoTransformAlong P T
    let QT := geoTransformAlong Q T
    let oP := nmOrd PT y
    let oQ := nmOrd QT y
    let U := ordMask PT oP ⊓ ordMask QT oQ
    let P' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U→Y) PT
    let Q' := MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U→Y) QT
    y ∈ U ∧ LocWPEquiv (companionOf n P' oP) (companionOf n Q' oQ) := by
  let PT := geoTransformAlong P T
  let QT := geoTransformAlong Q T
  have hTQ : IsGeoTestTower Q T := (hL.wEquiv.2 T).1.mp hT
  have hPT := isInvDomain_geoTransformAlong hP T hT
  have hQT := isInvDomain_geoTransformAlong hQ T hTQ
  have hyQ : y ∈ QT.cosupp := (hL.geoTransformAlong T hT).wEquiv.cosupp_eq ▸ hy
  have hScale := HironakaG8ScaledNonmonomialHistory.scaled_nmOrd_of_initial_exponents
    hn P Q hP hQ hN hE hL hInitial T hT y hy
  have hyPmask : y ∈ ordMask PT (nmOrd PT y) := by
    apply (mem_ordMask_iff hn hPT.isWellFormed hPT.isNonzeroAlongAt _ y).mpr
    intro h
    have h' := (mem_ordGe_iff hPT.isWellFormed hPT.isNonzeroAlongAt (PT.cosupp_subset_N hy) _).mp h
    change nmOrd PT y + 1 ≤ nmOrd PT y at h'
    omega
  have hyQmask : y ∈ ordMask QT (nmOrd QT y) := by
    apply (mem_ordMask_iff hn hQT.isWellFormed hQT.isNonzeroAlongAt _ y).mpr
    intro h
    have h' := (mem_ordGe_iff hQT.isWellFormed hQT.isNonzeroAlongAt (QT.cosupp_subset_N hyQ) _).mp h
    change nmOrd QT y + 1 ≤ nmOrd QT y at h'
    omega
  refine ⟨⟨hyPmask,hyQmask⟩, ?_⟩
  exact scaled_companions_local_stage_open hn P Q hP hQ hN hE hL hInitial T hT ho hScale _ inf_le_left

end
end Hironaka.HironakaG8ScaledCompanionStageOpen
