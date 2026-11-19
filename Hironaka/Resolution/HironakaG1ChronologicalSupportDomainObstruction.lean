import Hironaka.Resolution.HironakaG1ChronologicalSupportDimensionSplit

/-! The supported special branch obstructs every selected domain at the literal positive head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1ChronologicalSupportDomainObstruction

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSpec CanonicalCentres
  HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime BoundaryCount
  InvDomainMemberRestriction InvDomainTowerAlong MemberInterLocusAlong
  GermIdealOrder RelativePrincipalizationSpan AnalyticDimensionBasics
  HironakaG8LocalHistory HironakaG8HomStable HironakaG8MemberLoci HironakaCoherentTransformExtension
  HironakaG1RecursiveMemberValueTransport HironakaG1ChronologicalCompanionSuffix
  HironakaG1ChronologicalSupportDimensionSplit

set_option maxHeartbeats 1200000 in
/-- Positive saturation on a genuine tested head makes the supported
selected ideal vanish identically along its selected carrier germ. No
restriction through the anchor at that head can be a finite domain. -/
theorem positive_special_head_no_selected_domain {n l : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (R : MarkedIdeal n X) (hR : IsInvDomain l R)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked R) H) (p : Y)
    (hPos : 0 < level R H p) (hSp : IsSpecial R H p)
    (V : Opens Y) (hpV : p ∈ V) :
    let Q := positiveMemberOn R H p V
    let z : V := ⟨p,hpV⟩
    z ∈ Q.cosupp ∧ (∀ᶠ x in 𝓝 z, x ∈ Q.N → x ∈ Q.cosupp) ∧
      ∀ k : ℕ, ¬ IsInvDomain k Q := by
  intro Q z
  let B := geoTransformAlong (barMarked R) H
  let E₀ := origMembers R H
  let I := membersThrough B.E E₀ p
  let P := memberRestrict B I
  have hB := isInvDomain_geoTransformAlong (isInvDomain_barMarked R hR) H hH
  have hP := isWellFormed_memberRestrict hn hB.isWellFormed I
  have hOrig : ∀ F ∈ E₀, F ∈ B.E := fun _ h => List.mem_of_mem_take h
  have hsp : p ∈ memberInterLocus B.N E₀ B.cosupp := by
    rcases hSp with ⟨h0,_⟩ | ⟨_,hSp⟩
    · exact (Nat.ne_of_gt hPos h0).elim
    · exact hSp
  obtain ⟨hp, hSat⟩ := mem_memberInterLocus_iff.mp hsp
  have hCos := cosupp_memberRestrict hB.isWellFormed hB.one_le_d I
  have hpP : p ∈ P.cosupp := by
    change p ∈ (memberRestrict B I).cosupp
    rw [hCos, show I = membersThrough B.E E₀ p by rfl,
      memberInter_membersThrough hOrig]
    exact ⟨hp, fun _ _ h => h⟩
  have hNear : ∀ᶠ x in 𝓝 p, x ∈ P.N → x ∈ P.cosupp := by
    filter_upwards [hSat] with x hx hxN
    change x ∈ B.N ∩ memberInter B.E I at hxN
    have hE := hxN.2
    rw [show I = membersThrough B.E E₀ p by rfl, memberInter_membersThrough hOrig] at hE
    change x ∈ (memberRestrict B I).cosupp
    rw [hCos]
    exact ⟨hx hxN.1 hE, hxN.2⟩
  have hPull : Q.cosupp = (Subtype.val : V → Y) ⁻¹' P.cosupp :=
    cosupp_pullback_val P
      (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hP.isCoherent h) V
  have hz : z ∈ Q.cosupp := hPull ▸ hpP
  have hQSat : ∀ᶠ x in 𝓝 z, x ∈ Q.N → x ∈ Q.cosupp := by
    have ht : Tendsto (Subtype.val : V → Y) (𝓝 z) (𝓝 p) :=
      continuous_subtype_val.continuousAt
    filter_upwards [ht.eventually hNear] with x hx hxQ
    exact hPull ▸ hx hxQ
  refine ⟨hz,hQSat,fun k hD => ?_⟩
  obtain ⟨g,hg,hFreq⟩ := hD.isNonzeroAlongAt z (Q.cosupp_subset_N hz)
  obtain ⟨x,⟨hxN,hne⟩,hm,hx⟩ :=
    (hFreq.and_eventually ((HomogenizedGlueing.eventually_mem hD.isWellFormed.isCoherent hg).and hQSat)).exists
  exact hne ((vanishesToOrderOn_one_iff hxN
    (GermIdeal.IsCoherent.holomorphicAt_mem hD.isWellFormed.isCoherent hm)).mp
    (((hx hxN).2 g hm).mono hD.one_le_d))

set_option maxHeartbeats 1400000 in
/-- The full-dimensional supported branch excludes even arbitrary
selected windows at the genuine run head. Strict dimension drop produces
the supported native domain locally. -/
theorem chronological_support_domain_iff_dim_drop {n k b : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J R : MarkedIdeal n X) (hJ : IsInvDomain (k+2) J)
    (hR : IsInvDomain (k+1) R) (hClass : LocWPEquiv J R) (hCar : R.N ⊆ J.N)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hCan : IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) J) T)
    (y : Y) (hy : y ∈ (geoTransformAlong J T).cosupp)
    (hLevel : level J T y = b+1) (hNS : ¬ IsSpecial J T y) :
    let r := regimeRun (stepRegime J (b+1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let A := geoTransformAlong (barMarked J) H
    let B := geoTransformAlong (barMarked R) H
    let Q := memberRestrict B (membersThrough B.E (origMembers R H) p)
    ∃ d, RegularAtDim (n := n) Q.N p d ∧
      ((∃ W : Opens (split T r).1, p ∈ W ∧ IsInvDomain k (positiveMemberOn R H p W)) ↔
        ¬ LocDimGE (n := n) (Q.N ∩ A.cosupp) p d) ∧
      (LocDimGE (n := n) (Q.N ∩ A.cosupp) p d →
        ∀ W : Opens (split T r).1, p ∈ W → ∀ q, ¬ IsInvDomain q (positiveMemberOn R H p W)) := by
  intro r H S p A B Q
  obtain ⟨hH, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    positive_companion_chronological_suffix (k := k+1) hn J hJ hMax T hCan y hy hLevel hNS
  have hJH := ((bar_local_any_boundary J hJ).wEquiv.2 H).1.mpr hH
  have hRH := (hClass.wEquiv.2 H).1.mp hJH
  have hRB := ((bar_local_any_boundary R hR).wEquiv.2 H).1.mp hRH
  obtain ⟨hT, _, hCos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (invFamily hn (k+1))
    J hJ hMax hn T hCan
  have hyBar : y ∈ (geoTransformAlong (barMarked J) T).cosupp := hCos.symm ▸ hy
  have hReg := StepOneValueMasked.stepRegime_and_mem_cosupp_head J hJ.isWellFormed T hT hyBar hNS
  rw [hLevel] at hReg
  have hlR : level R H p = b+1 := (level_eq_of_E_eq hClass.wEquiv.1 H p).symm.trans hReg.1.1
  obtain ⟨d,hd,hSp,hRegular⟩ := chronological_support_dimension_domain_split hn J R hJ hR
    hClass hCar hMax T hCan y hy hLevel hNS
  have hNo (h : LocDimGE (n := n) (Q.N ∩ A.cosupp) p d)
      (W : Opens (split T r).1) (hp : p ∈ W) (q : ℕ) :
      ¬ IsInvDomain q (positiveMemberOn R H p W) :=
    (positive_special_head_no_selected_domain hn R hR H hRB p
      (hlR.symm ▸ Nat.succ_pos b) (hSp.mpr h) W hp).2.2 q
  refine ⟨d,hd, ⟨?_,?_⟩, hNo⟩
  · rintro ⟨W,hp,hD⟩ h
    exact hNo h W hp k hD
  · intro h
    obtain ⟨W,hp,_,_,hDom⟩ := hRegular.mp h
    exact ⟨W,hp,(hDom W le_rfl).2⟩

#print axioms positive_special_head_no_selected_domain
#print axioms chronological_support_domain_iff_dim_drop

end Hironaka.HironakaG1ChronologicalSupportDomainObstruction
