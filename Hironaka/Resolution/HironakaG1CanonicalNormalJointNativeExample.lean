import Hironaka.Resolution.HironakaG1CanonicalNormalGeneralExample
import Hironaka.Resolution.HironakaActualSectionBoundaryDimension
import Hironaka.Analytic.SNCGlobalPrimeComponents

/-! A common depth-one value on the contact and the native selected record. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1CanonicalNormalJointNativeExample
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealOperationsAlong
  RelativePrincipalizationSpan GermIdealPullbackCalculus GermIdealOrder RestrictedIdealExtension
  RestrictLeCalculus ResolutionInvariantSpec CanonicalCentres GeneralValue GeneralCompare
  StepOneValue StepOneValueMasked StepOneLowerDomain BoundaryCount
  CompanionReductionAlong CompanionRebase NonmonomialOrderLocal CompanionOpen NonmonomialOrderTail NonmonomialOrderRegime
  HomogenizedIdealAlong CodimOneSupportAlong HironakaG8MixedOrderInvariance
  HironakaSharpOriginalProductTraceOrder HironakaActualSectionBoundaryDimension

/-- The depth-one value of the order-two, level-zero special branch. -/
def orderTwoSpecialValue : ValTy 1 :=
  toLex (2, Sum.inrₗ (↑(toLex (0, (⊤ : WithTop (ValTy 0))) : ℕ ×ₗ WithTop (ValTy 0))))

private theorem singleton_regular {n : ℕ} {X : CMfd.{0} n} (x : X) :
    RegularAtDim (n := n) ({x} : Set X) x 0 := by
  let e := complexChartAt (n := n) x
  let q := e.val x
  let Φ : LocalHolomorphicEquivAt (n := n) q := {
    source := e.val.target
    target := (fun w : ComplexModel n => w + q) ⁻¹' e.val.target
    isOpen_source := e.val.open_target
    isOpen_target := e.val.open_target.preimage (continuous_id.add_const q)
    center_mem_source := e.val.map_source (mem_complexChartAt_source x)
    toFun := fun z => z - q
    invFun := fun z => z + q
    toFun_holomorphic := (differentiable_id.sub_const q).differentiableOn
    invFun_holomorphic := (differentiable_id.add_const q).differentiableOn
    mapsTo_toFun := by intro z hz; simpa only [mem_preimage, sub_add_cancel] using hz
    mapsTo_invFun := fun _ hw => hw
    left_inv := fun z _ => sub_add_cancel z q
    right_inv := fun z _ => add_sub_cancel_right z q }
  refine ⟨Nat.zero_le n, mem_singleton _, Φ, Subset.rfl, sub_self q, ?_⟩
  intro y hy _
  constructor
  · intro hyx
    rw [mem_singleton_iff.mp hyx]
    change q - q ∈ complexCoordinatePlane n 0
    rw [sub_self]
    intro i _
    rfl
  · intro hz
    have heq : e.val y - q = 0 := by
      ext i
      exact hz i (Nat.zero_le _)
    exact mem_singleton_iff.mpr (e.val.injOn hy (mem_complexChartAt_source x) (sub_eq_zero.mp heq))

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- An isolated order-two point on a smooth curve reads the finite
companion letter with a top lower coordinate. -/
theorem initial_orderTwoSpecial_value {n : ℕ} {X : CMfd.{0} n}
    (hn : 0 < n) (J : MarkedIdeal n X) (hJ : IsInvDomain 1 J)
    (hd : J.d = 1) (hE : J.E = []) (p : X)
    (hCos : J.cosupp = {p}) (hReg : RegularAtDim (n := n) J.N p 1)
    (hOrd : nmOrd J p = 2) :
    (invFamily hn 1).inv J (BlowupTower.refl (X := X)) p = orderTwoSpecialValue := by
  let T : BlowupTower X X := .refl
  have hCuts (r : ℕ) : ordGe J r = cosupport n J.N J.ideal r := by
    have he : J = ordinaryTraceMarked J.N J.ideal :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl hE rfl hd
    rw [← ordGe_ordinaryTraceMarked_eq_cosupport (X := X) J.N J.ideal hJ.isWellFormed.isCoherent, ← he]
  have hp2 : p ∈ ordGe J 2 :=
    mem_ordGe_of_succ_le (q := 1) (by rw [hOrd])
  have hSingleton2 : cosupport n J.N J.ideal 2 = {p} := by
    apply Subset.antisymm
    · have h := cosupport_anti (N := J.N) (𝔞 := J.ideal) (by decide : 1 ≤ 2)
      have he : cosupport n J.N J.ideal 1 = {p} := by
        rw [← hd]
        exact hCos
      rwa [he] at h
    · rw [singleton_subset_iff, ← hCuts]
      exact hp2
  have hEmpty : ordGe J 3 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx2 : x ∈ cosupport n J.N J.ideal 2 := by
      exact cosupport_anti (by decide : 2 ≤ 3) (hCuts 3 ▸ hx)
    have hxp : x = p := mem_singleton_iff.mp (hSingleton2 ▸ hx2)
    have hFin := exists_notMem_ordGe hJ.isWellFormed hJ.isNonzeroAlongAt (ordGe_subset_N J 3 hx)
    have h3 := succ_le_nmOrd_of_mem hFin hx
    rw [hxp, hOrd] at h3
    exact (by decide : ¬ 3 ≤ 2) h3
  let W := ordMask (M := X) J 2
  have hpW : p ∈ W := by
    change p ∈ (closure (ordGe J 3))ᶜ
    simp [hEmpty]
  let q : W := ⟨p, hpW⟩
  let Y := CMfd.of (n := n) W
  let C : MarkedIdeal n Y := compAt (X := X) J 2 T
  let J' : MarkedIdeal n Y := MarkedIdeal.pullback (Subtype.val : W → X) J
  have hC : IsInvDomain 1 C := isInvDomain_compAt (X := X) hn (by decide) T hJ
  have hE' : J'.E = [] := by change J.E.map _ = []; rw [hE]; rfl
  have hD' : J'.d = 1 := hd
  have hCeq : C = (⟨J'.N, [], restrictOn n J'.N J'.ideal, 2⟩ : MarkedIdeal n Y) := by
    change companionOf n (M := Y) J' 2 = _
    simp only [companionOf, companionAlong, hD', Nat.reduceLT, if_false, hE',
      nonmonomialPartAlong_nil_eq_restrictOn]
  have hJ'I : J'.ideal.IsCoherent := isCoherent_pullback contMDiff_subtype_val hJ.isWellFormed.isCoherent
  have hCert : C.cosupp = cosupport n J'.N J'.ideal 2 := by
    rw [hCeq]
    exact Subset.antisymm (cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hJ'I) 2)
      (cosupport_subset_of_restrictLe restrictLe_restrictOn 2)
  have hCCos : C.cosupp = {q} := by
    rw [hCert]
    let K : MarkedIdeal n X := ⟨J.N, [], J.ideal, 2⟩
    have hHol : ∀ x g, K.ideal.mem x g → HolomorphicAt n g x :=
      fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ.isWellFormed.isCoherent hg
    change (MarkedIdeal.pullback (Subtype.val : W → X) K).cosupp = _
    rw [cosupp_pullback_val K hHol W]
    change (Subtype.val : W → X) ⁻¹' cosupport n J.N J.ideal 2 = _
    rw [hSingleton2]
    ext z
    exact ⟨fun hz => Subtype.ext hz, fun hz => congrArg Subtype.val hz⟩
  have hCN : RegularAtDim (n := n) (barMarked (X := Y) C).N q 1 := by
    change RegularAtDim (n := n) C.N q 1
    rw [hCeq]
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hReg
  have hBar : (barMarked (X := Y) C).cosupp = {q} :=
    (cosupp_barMarked (X := Y) C hC.isWellFormed hC.one_le_d).trans hCCos
  let T' : BlowupTower Y Y := .refl
  have hLevel : level C T' q = 0 := by
    have he : origMembers C T' = [] := by simp [origMembers, hCeq]
    unfold level
    rw [he]
    simp [boundaryCount]
  have hSpec : IsSpecial C T' q := Or.inl ⟨hLevel, by
    refine ⟨0, hCN, ?_⟩
    change RegularAtDim (n := n) (barMarked (X := Y) C).cosupp q 0
    rw [hBar]
    exact singleton_regular (X := Y) q⟩
  let R := invFamily hn 0
  let F := fun {A : CMfd.{0} n} (K : MarkedIdeal n A) {B : CMfd.{0} n}
    (S : BlowupTower A B) (z : B) => Seq.StepOneValueMasked.stepOneInvM R K S z
  have hStep : F C T' q = toLex (0, (⊤ : WithTop (ValTy 0))) := by
    change Seq.StepOneValueMasked.stepOneInvL R C (lowerMarkedM C) T' q = _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R C _ T' hSpec, hLevel]
  change genInv (X := X) F J T p = _
  rw [genInv_of_nmOrd_ne_zero (X := X) F J T (show nmOrd (geoTransformAlong J T) p = 2 from hOrd) (by decide)]
  change toLex (2, Sum.inrₗ (genLowerValue (X := X) F J 2 T T p)) = _
  have hLower := genLowerValue_eq_of_mem (X := X) (T₀ := T) (T₁ := T) (y := p) F J hpW
  have hFinal := hLower.trans (congrArg (fun w : ℕ ×ₗ WithTop (ValTy 0) =>
    (↑w : WithTop (ℕ ×ₗ WithTop (ValTy 0)))) hStep)
  exact congrArg (fun w : WithTop (ℕ ×ₗ WithTop (ValTy 0)) =>
    (toLex (2, Sum.inrₗ w) : ValTy 1)) hFinal

open HironakaG1CanonicalNormalGeneralExample HironakaG1PositiveNormalJointExample
  HironakaG1PositiveNormalNonspecialExample HironakaG1NormalFiniteRecodingExample
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG8LocalHistory
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionInitialBar
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeInvariantDomain HironakaActualSectionBoundaryGeometry
  HironakaRelativeNormalIdeal HironakaActualRelativeNormalGeometry
  HironakaActualCoherentWeightedCoefficientMarked InvertibleIdealQuotient
  ContactStageKept HomogenizedGlueingTower CoefficientIdealRestriction NormalCrossings
  HironakaDisjointZeroCoordinateInitialRecoding
  TangentDirectionAlong DivisorExponentAlong

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev D : Set U := (Subtype.val : U → ComplexModel 2) ⁻¹' firstCoordinateDivisor
private abbrev H : Set X := projection U ⁻¹' D
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private abbrev S : MarkedIdeal 3 X := sectionMarked sourceRecord
private abbrev T : BlowupTower X X := .refl
private abbrev O := lowerMask P 1 T p
private abbrev M := CMfd.of (n := 3) O
private abbrev L : MarkedIdeal 3 M := lowerMarkedM P 1 T p
private abbrev e : BlowupTower M M := .refl
private abbrev t : M → ℂ := relativeNormalCoordinate U ∘ Subtype.val
private abbrev W : Opens M := ⊤
private abbrev Y := CMfd.of (n := 3) W
private abbrev C : MarkedIdeal 3 Y := contactMarkedKept L t e W

private theorem P_dom : IsInvDomain 3 P := properNormalMarked_isInvDomain sourceRecord sourceRecord_domain
private theorem S_dom : IsInvDomain 2 S :=
  section_projected_domain 2 sourceRecord.N sourceRecord.E sourceRecord.ideal sourceRecord.d sourceRecord_domain

private theorem P_cosupp_subset : P.cosupp ⊆ {p} := by
  intro x hx
  have hHol : ∀ x g, P.ideal.mem x g → HolomorphicAt 3 g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem P_dom.isWellFormed.isCoherent hg
  have hxZ : x ∈ P.ideal.zeroLocus := by
    have he : P.cosupp = P.N ∩ P.ideal.zeroLocus := cosupport_one hHol
    exact (he ▸ hx).2
  let i : X → ComplexModel 3 := Subtype.val
  have hi : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) ∞ i := contMDiff_subtype_val
  have hz (j : Bool ⊕ Unit) : paddedGenerator j x.val = 0 := by
    apply hxZ (paddedGenerator j ∘ i)
    rw [proper_source_generators]
    refine GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨paddedGenerator j, ?_, rfl⟩ ?_)
    · exact isInSpanAt_self ⟨j, rfl⟩ (Eventually.of_forall fun z => paddedGenerator_hol j z)
    · exact Eventually.of_forall fun z => ((paddedGenerator_hol j).comp (hi.mdifferentiable (by simp))) z
  have h0 : x.val (0 : Fin 3) = 0 := hz (.inl true)
  have h1 : x.val (1 : Fin 3) = 0 := eq_zero_of_pow_eq_zero (show x.val (1 : Fin 3) ^ 2 = 0 from hz (.inl false))
  have h2 : x.val (2 : Fin 3) = 0 := hz (.inr ())
  apply mem_singleton_iff.mpr
  apply Subtype.ext
  have hp0 : p.val = 0 := map_zero (tangentInclusion 2 1)
  rw [hp0]
  ext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

private theorem S_cosupp_subset : S.cosupp ⊆ {p} :=
  (((properNormalMarked_locWPEquiv_section sourceRecord sourceRecord_domain).wEquiv.2 T).2 trivial) ▸ P_cosupp_subset

private theorem p_mem_H : p ∈ H := by
  change tangentProjection 2 1 (tangentInclusion 2 1 0) ∈ firstCoordinateDivisor
  rw [tangentProjection_tangentInclusion]
  simp [firstCoordinateDivisor]

private theorem lower_eq :
    L = MarkedIdeal.pullback (Subtype.val : O → X) (⟨H, [], P.ideal, 1⟩ : MarkedIdeal 3 X) := by
  have h := positive_mark_one_single_member_lower_eq (X := X) P rfl
    P_dom.isWellFormed.isCoherent H rfl p p_mem_H
  have hN : P.N = univ := preimage_univ
  rw [hN, univ_inter] at h
  exact h

private theorem lower_regular (x : O) (hx : x ∈ L.N) :
    RegularAtDim (n := 3) L.N x 2 := by
  rw [lower_eq] at hx ⊢
  have he : P.E = [H] := rfl
  have hH : H ∈ P.E := he.symm ▸ List.mem_singleton_self H
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hH
  change RegularAtDim (n := 3) ((Subtype.val : O → X) ⁻¹' H) x 2
  apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
  exact hi ▸ SNCGlobalPrimeComponents.regularAtDim_member P_dom.isWellFormed.isSNCDivisor i
    (hi.symm ▸ hx)

private theorem order_threshold_eq {n : ℕ} {A : CMfd.{0} n} (J : MarkedIdeal n A)
    (hI : J.ideal.IsCoherent) (hd : J.d = 1) (hE : J.E = []) (r : ℕ) :
    ordGe J r = cosupport n J.N J.ideal r := by
  have he : J = ordinaryTraceMarked J.N J.ideal :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl hE rfl hd
  rw [← ordGe_ordinaryTraceMarked_eq_cosupport (X := A) J.N J.ideal hI, ← he]

private theorem curve_domain {n : ℕ} {A : CMfd.{0} n} (J : MarkedIdeal n A)
    (hNI : IsClosedSubmanifold n J.N) (hI : J.ideal.IsCoherent) (hd : J.d = 1) (hE : J.E = [])
    (hR : ∀ x ∈ J.N, RegularAtDim (n := n) J.N x 1)
    (p : A) (hCos : J.cosupp ⊆ {p}) (hOrd : nmOrd J p = 2) :
    IsInvDomain 1 J := by
  refine ⟨⟨hNI, hI, hE.symm ▸ isSNCDivisor_nil, hE.symm ▸ isTransverse_nil_of_isClosedSubmanifold hNI⟩,
    fun x hx => ⟨1, le_rfl, hR x hx⟩, hd.symm ▸ le_rfl, ?_⟩
  intro x hx
  by_contra hNone
  have hAll (r : ℕ) : x ∈ cosupport n J.N J.ideal r := by
    refine ⟨hx, fun g hg => ⟨fun _ => 0, GiraudAlong.zero_mem_idealPow _ _ _, ?_⟩⟩
    have hh : ¬ ∃ᶠ y in 𝓝 x, y ∈ J.N ∧ g y ≠ 0 := fun hf => hNone ⟨g, hg, hf⟩
    exact (not_frequently.mp hh).mono fun _ hy hyN => by
      by_contra hc
      exact hy ⟨hyN, hc⟩
  have hxCos : x ∈ J.cosupp := by
    change x ∈ cosupport n J.N J.ideal J.d
    rw [hd]
    exact hAll 1
  have hxp : x = p := hCos hxCos
  subst x
  have hEmpty : {r : ℕ | p ∉ ordGe J (r + 1)} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro r hr
    exact hr (order_threshold_eq J hI hd hE (r + 1) ▸ hAll (r + 1))
  unfold nmOrd at hOrd
  rw [hEmpty, Nat.sInf_empty] at hOrd
  omega

private theorem contact_at_origin (pO : O) (hp : pO.val = p) :
    (invFamily (by decide : 0 < 3) 1).inv C (BlowupTower.refl (X := Y)) ⟨pO, mem_univ _⟩ =
      orderTwoSpecialValue := by
  let q : Y := ⟨pO, mem_univ _⟩
  let A : MarkedIdeal 3 M := withN L (L.N ∩ {y | t y = 0})
  have hLI : L.ideal.IsCoherent := by
    rw [lower_eq]
    exact isCoherent_pullback contMDiff_subtype_val P_dom.isWellFormed.isCoherent
  have hLd : L.d = 1 := by rw [lower_eq]; rfl
  have hLE : L.E = [] := by rw [lower_eq]; rfl
  have he : C = MarkedIdeal.pullback (Subtype.val : W → M) A := by
    change MarkedIdeal.pullback (Subtype.val : W → M)
      (withN (coeffMarkedAlong (geoTransformAlong (barMarked (X := M) L) e))
        (strictAlong e (L.N ∩ {y | t y = 0}))) = _
    have hC := coeffMarkedAlong_eq_of_mark_one L hLd hLI
    rw [geoTransformAlong_refl, strictAlong_refl]
    change MarkedIdeal.pullback (Subtype.val : W → M)
      (withN (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong L))) (L.N ∩ {y | t y = 0})) = _
    rw [homMarkedAlong_eq_of_mark_one L hLd hLI, hC, hC]
  have hCD : C.d = 1 := by rw [he]; exact hLd
  have hCE : C.E = [] := by rw [he]; change L.E.map _ = []; rw [hLE]; rfl
  have hCI : C.ideal.IsCoherent := by rw [he]; exact isCoherent_pullback contMDiff_subtype_val hLI
  have hLN : IsClosedSubmanifold 3 L.N := by
    refine ⟨?_, fun x hx => ⟨2, lower_regular x hx⟩⟩
    rw [lower_eq]
    have hH := P_dom.isWellFormed.isSNCDivisor.1 H (by change H ∈ [H]; simp)
    exact hH.preimage continuous_subtype_val
  have hAR (x : M) (hx : x ∈ A.N) : RegularAtDim (n := 3) A.N x 1 := by
    have hTan := padded_selected_normal_tangent
    obtain ⟨k, hk, hR⟩ := hTan.regularAtDim_contact
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hLI hg) hLN
      (show x ∈ L.N ∩ {y | t y = 0} ∩ univ from ⟨hx, mem_univ _⟩)
    have hk2 := RegularPointDimension.eq_of_regularAtDim hk (lower_regular x hx.1)
    rw [hk2, inter_univ] at hR
    exact hR
  have hCR (x : Y) (hx : x ∈ C.N) : RegularAtDim (n := 3) C.N x 1 := by
    rw [he] at hx ⊢
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hAR x.val hx)
  have hCN : IsClosedSubmanifold 3 C.N := by
    refine ⟨?_, fun x hx => ⟨1, hCR x hx⟩⟩
    rw [he]
    have ht : Continuous t := (HironakaActualWeightedNormalPadding.normalCoordinate_mdifferentiable U).continuous.comp
      continuous_subtype_val
    exact (hLN.1.inter (isClosed_eq ht continuous_const)).preimage continuous_subtype_val
  have hOrd : nmOrd C q = 2 := by
    have h := padded_selected_normal_contact_fst pO hp
    exact (canonicalInvariant_fst (X := Y) C .refl q).symm.trans h
  have hCosSub : C.cosupp ⊆ {q} := by
    change cosupport 3 C.N C.ideal C.d ⊆ _
    rw [hCD, padded_selected_normal_contact_cosupport]
    intro x hx
    have hxS : x.val.val ∈ S.cosupp :=
      ⟨hx.1.1, fun g hg => by
        have hHol := GermIdeal.IsCoherent.holomorphicAt_mem S_dom.isWellFormed.isCoherent hg
        exact (vanishesToOrderOn_one_iff hx.1.1 hHol).mpr
          ((vanishesToOrderOn_one_iff hx.1 hHol).mp (hx.2 g hg))⟩
    have hxp : x.val.val = p := S_cosupp_subset hxS
    exact mem_singleton_iff.mpr (Subtype.ext (Subtype.ext (hxp.trans hp.symm)))
  have hqC : q ∈ C.cosupp := by
    have h := mem_ordGe_of_succ_le (𝔪 := C) (q := 0) (by rw [hOrd]; decide : 1 ≤ nmOrd C q)
    rw [order_threshold_eq (A := Y) C hCI hCD hCE] at h
    change q ∈ cosupport 3 C.N C.ideal C.d
    rw [hCD]
    exact h
  have hCos : C.cosupp = {q} := Subset.antisymm hCosSub (singleton_subset_iff.mpr hqC)
  exact initial_orderTwoSpecial_value (X := Y) (by decide) C
    (curve_domain C hCN hCI hCD hCE hCR q hCosSub hOrd) hCD hCE q hCos
    (hCR q (C.cosupp_subset_N hqC)) hOrd

private abbrev Z := nativeManifold (Y := X) (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U)
private abbrev B : MarkedIdeal 2 Z :=
  nativePullback (Y := X) (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U) S
private abbrev N : BlowupTower Z Z := .refl

private theorem native_at_origin (z : Z) (hz : z.val = p) (hLevel : level B N z = 1)
    (zO : lowerMask B 1 N z) (hzO : zO.val = z)
    (hFirst : fstEntry ((canonicalInvariant 2).inv (lowerMarkedM B 1 N z)
      (BlowupTower.refl (X := CMfd.of (n := 2) (lowerMask B 1 N z))) zO) = 2) :
    (invFamily (by decide : 0 < 2) 1).inv (lowerMarkedM B 1 N z)
      (BlowupTower.refl (X := CMfd.of (n := 2) (lowerMask B 1 N z))) zO =
    orderTwoSpecialValue := by
  let V := lowerMask B 1 N z
  let Q := CMfd.of (n := 2) V
  let J : MarkedIdeal 2 Q := lowerMarkedM B 1 N z
  let H' : Set Z := (Subtype.val : zeroPlane U → X) ⁻¹' H
  have hSsub : S.N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hTr : IsTransverse 3 (zeroPlane U) S.E :=
    isTransverse_liftedCarrier sourceRecord.N sourceRecord.E sourceRecord_domain.isWellFormed.isTransverse
  have hB : IsInvDomain 2 B := isInvDomain_nativePullback (X := X) (by decide : 0 < 3)
    (Nat.le_succ 2) (zeroPlane_regular U) S S_dom hSsub hTr
  have hBN : B.N = univ := by
    ext y
    exact ⟨fun _ => mem_univ _, fun _ => y.property⟩
  have hBE : B.E = [H'] := rfl
  have hzH : z ∈ H' := by change z.val ∈ H; rw [hz]; exact p_mem_H
  have hEq : J = MarkedIdeal.pullback (Subtype.val : V → Z)
      (⟨H', [], B.ideal, 1⟩ : MarkedIdeal 2 Z) := by
    have h := positive_mark_one_single_member_lower_eq (X := Z) B rfl hB.isWellFormed.isCoherent
      H' hBE z hzH
    rw [hBN, univ_inter] at h
    exact h
  have hJ : IsInvDomain 1 J :=
    isInvDomain_lowerMarked_succ (X := Z) B hB.isWellFormed hB.one_le_d (by decide)
      N trivial hB.dimLE hLevel
  have hJE : J.E = [] := by rw [hEq]; rfl
  have hJD : J.d = 1 := by rw [hEq]; rfl
  have hOrd : nmOrd J zO = 2 := (canonicalInvariant_fst (X := Q) J .refl zO).symm.trans hFirst
  have hqp : zO ∈ J.cosupp := by
    have h := mem_ordGe_of_succ_le (𝔪 := J) (q := 0) (by rw [hOrd]; decide : 1 ≤ nmOrd J zO)
    rw [order_threshold_eq (A := Q) J hJ.isWellFormed.isCoherent hJD hJE] at h
    change zO ∈ cosupport 2 J.N J.ideal J.d
    rw [hJD]
    exact h
  have hBC : B.cosupp ⊆ {z} := by
    rw [cosupp_nativePullback (Y := X) (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U)
      S hSsub (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem S_dom.isWellFormed.isCoherent hg)]
    intro y hy
    exact mem_singleton_iff.mpr (Subtype.ext ((mem_singleton_iff.mp (S_cosupp_subset hy)).trans hz.symm))
  have hJSub : J.cosupp ⊆ {zO} := by
    have hHol : ∀ x g, B.ideal.mem x g → HolomorphicAt 2 g x :=
      fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg
    let K : MarkedIdeal 2 Z := ⟨H', [], B.ideal, 1⟩
    rw [hEq, cosupp_pullback_val K hHol V]
    intro y hy
    have hyB : y.val ∈ B.cosupp := by
      change y.val ∈ K.cosupp at hy
      have hC : K.cosupp = H' ∩ B.ideal.zeroLocus := cosupport_one hHol
      have hBCos : B.cosupp = B.N ∩ B.ideal.zeroLocus := cosupport_one hHol
      rw [hC] at hy
      rw [hBCos, hBN]
      exact ⟨mem_univ _, hy.2⟩
    exact mem_singleton_iff.mpr (Subtype.ext ((mem_singleton_iff.mp (hBC hyB)).trans hzO.symm))
  have hJReg : RegularAtDim (n := 2) J.N zO 1 := by
    have hH' : H' ∈ B.E := hBE.symm ▸ List.mem_singleton_self H'
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hH'
    rw [hEq]
    apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
    exact hi ▸ SNCGlobalPrimeComponents.regularAtDim_member hB.isWellFormed.isSNCDivisor i
      (hi.symm ▸ (hzO.symm ▸ hzH))
  exact initial_orderTwoSpecial_value (X := Q) (by decide) J hJ hJD hJE zO
    (Subset.antisymm hJSub (singleton_subset_iff.mpr hqp)) hJReg hOrd

set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency false in
/-- The literal native selected value on the common empty lift agrees with
the actual padded normal contact value under the one-coordinate dimension shift. -/
theorem joint_native_selected_matches_normal_contact :
    ∃ (z : Z) (hZero : IsClosed (zeroPlane U)) (pO : O) (zO : lowerMask B 1 N z),
      Lift (Nat.le_succ 2) (zeroPlane U) hZero (zeroPlane_regular U) S.E T
        (zeroPlane U) hZero (zeroPlane_regular U) N ∧
      pO.val = p ∧ z.val = p ∧ zO.val = z ∧
      let v := (invFamily (by decide : 0 < 2) 1).inv (lowerMarkedM B 1 N z)
        (BlowupTower.refl (X := CMfd.of (n := 2) (lowerMask B 1 N z))) zO
      let w := (invFamily (by decide : 0 < 3) 1).inv C
        (BlowupTower.refl (X := Y)) ⟨pO, mem_univ _⟩
      v = orderTwoSpecialValue ∧ w = sameIndexMap 1 1 v ∧
      (invFamily (by decide : 0 < 3) 2).inv L e pO =
        initialEmbedding 1 (sameIndexMap 1 1 v) := by
  obtain ⟨z, hZero, pO, zO, hLift, hz, hp, hzO, _, _, _, hLevel, _, _, _, _, hFirst⟩ :=
    joint_positive_nonspecial_first_entries
  have hNative := native_at_origin z hz hLevel zO hzO hFirst
  have hContact := contact_at_origin pO hp
  have hShift := hContact.trans ((congrArg (sameIndexMap 1 1) hNative).trans
    (show sameIndexMap 1 1 orderTwoSpecialValue = orderTwoSpecialValue from rfl)).symm
  obtain ⟨pO', w, hp', hGen, hNormal, _⟩ := canonical_normal_selected_general_value
  have hP' : pO' = pO := Subtype.ext (hp'.trans hp.symm)
  subst pO'
  refine ⟨z, hZero, pO, zO, hLift, hp, hz, hzO, hNative, hShift, ?_⟩
  exact hGen.trans (congrArg (initialEmbedding 1) (hNormal.trans hShift))

end
end Hironaka.HironakaG1CanonicalNormalJointNativeExample
