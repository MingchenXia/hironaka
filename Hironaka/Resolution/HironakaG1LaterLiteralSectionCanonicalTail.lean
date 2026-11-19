import Hironaka.Resolution.HironakaG1LaterSectionPairOrder
import Hironaka.Resolution.HironakaG1LaterContactRecursiveDomain
import Hironaka.Invariant.MaxLocusLocal

/-! The literal finite section upper read along its actual canonical suffix. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterLiteralSectionCanonicalTail
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSpec
  ResolutionInvariantSeq InvDomainTowerAlong BlowupTowerIsomorphism MaxLocusLocal
  CanonicalCentres StepOneValue StepOneValueMasked StepOneLowerDomain StepOneRegime BlowupTowerSplit
  HironakaG1LaterSectionPairOrder HironakaG1LaterContactRecursiveDomain
  HironakaG1RecursiveMemberValueTransport HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaActualSectionBoundaryGeometry
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HironakaG8LocalHistory HironakaG8HomStable HironakaG8MemberLoci InvDomainMemberRestriction
  HironakaCoherentTransformExtension HomogenizedIdealAlong CoefficientIdealRestriction
  RelativePrincipalizationSpan ResolutionDriver
  HironakaG1OriginalUnequalMarkCanonical HironakaG11InvBMClass

private theorem restrict_actual_section_tail {n k : ℕ} {X Y : CMfd.{0} n}
    (I : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k (ValTy k))
    (A : MarkedIdeal n X) (hA : A.ideal.IsCoherent) {U W : Opens X} (hWU : W ≤ U)
    (T : BlowupTower X Y) (y : Y) (hy : T.proj y ∈ W) :
    let B := MarkedIdeal.pullback (Subtype.val : U → X) A
    let D := MarkedIdeal.pullback (Subtype.val : W → X) A
    let yU : openPreimage T U := ⟨y, hWU hy⟩
    let yW : openPreimage T W := ⟨y, hy⟩
    IsInvDomain k B → IsCanonical B (I.inv B) (restrict U T) →
    yU ∈ (geoTransformAlong B (restrict U T)).cosupp →
    IsCanonical D (I.inv D) (restrict W T) ∧
    yW ∈ (geoTransformAlong D (restrict W T)).cosupp ∧
    I.inv D (restrict W T) yW = I.inv B (restrict U T) yU := by
  intro B D yU yW hB hCan hyU
  let E := nestedOpens U W
  let Φ := (nestedOpensDiffeo (n := n) hWU).symm
  let χ := (nestedDiffeo (n := n) (openPreimage T U) (openPreimage (restrict U T) E)
      (openPreimage T W) (mem_openPreimage_restrict_nestedOpens U W T)
      (openPreimage_mono T hWU)).symm
  let q := MarkedIdeal.pullback (Subtype.val : E → U) B
  have hq := isInvDomain_pullback_val E hB
  have hqCan := Seq.ResolutionInvariantExt.isCanonical_restrict I hB E (restrict U T) hCan
  have hIso := (isTowerIso_restrict_nestedOpens (X := X) hWU T).symm
  have heq : MarkedIdeal.pullback Φ q = D := pullback_symm_nestedOpensDiffeo hA hWU
  have hCanD := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso I hq Φ hIso hqCan
  rw [heq] at hCanD
  have hTest := I.isInvValue.isGeoTestTower_of_isCanonical hB _ hCan
  have hqTest := I.isInvValue.isGeoTestTower_of_isCanonical hq _ hqCan
  have hyχ : (χ yW).val = yU := rfl
  have hqCos : χ yW ∈ (geoTransformAlong q (restrict E (restrict U T))).cosupp := by
    change χ yW ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : E → U) B)
      (restrict E (restrict U T))).cosupp
    rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hB.isWellFormed.isClosedSubmanifold_N
      hB.isWellFormed.isCoherent E (restrict U T) hTest]
    change (χ yW).val ∈ (geoTransformAlong B (restrict U T)).cosupp
    rw [hyχ]
    exact hyU
  have hCosD := IsTowerIso.cosupp_geoTransformAlong Φ hq.isWellFormed.isClosedSubmanifold_N
    hq.isWellFormed.isCoherent hIso hqTest
  rw [heq] at hCosD
  have hyD : yW ∈ (geoTransformAlong D (restrict W T)).cosupp := by
    rw [hCosD]
    exact hqCos
  have hVal := I.isInvValue.towerIso Φ q hq (restrict W T) (restrict E (restrict U T))
    χ hIso hqCan yW hqCos
  rw [heq] at hVal
  have hy' : (χ yW).val ∈ (geoTransformAlong B (restrict U T)).cosupp := by rw [hyχ]; exact hyU
  have hRestr := I.isInvValue.restrictOpen B hB E (restrict U T) hCan (χ yW) hy'
  exact ⟨hCanD, hyD, hVal.trans (hRestr.trans (congrArg (I.inv B (restrict U T)) hyχ))⟩

private theorem positive_upper_read {n k s : ℕ} {X Y : CMfd.{0} n}
    (hn : 0 < n) (A : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y)
    (hLevel : level A T y = s+1) (hNS : ¬ IsSpecial A T y) :
    let I := invFamily hn k
    let j := regimeRun (stepRegime A (s+1)) T y
    let H := head T j
    let F := tail T j
    let p := F.proj y
    ∀ hp : p ∈ maskA A H p,
      let M := maskA A H p
      let L := lowerMarkedM A (s+1) H p
      Seq.StepOneValueMasked.stepOneInvM I A T y =
        toLex (s+1, (I.inv L (restrict M F) (⟨y, hp⟩ : openPreimage F M) : WithTop (ValTy k))) := by
  intro I j H F p hp M L
  have hStep := Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial (X := X) I A
    (lowerMarkedM A) T (y := y) hNS
  rw [hLevel] at hStep
  have hLow := Seq.StepOneValueMasked.lowerValueL_eq_of_mem (X := X) I A (lowerMarkedM A)
    (s := s+1) (T₀ := H) (T₁ := F) (y := y) hp
  exact hStep.trans (congrArg (fun v : WithTop (ValTy k) => toLex (s+1, v)) hLow)

set_option maxHeartbeats 1600000 in
/-- An actual canonical original section history yields its finite upper read
on the inherited mask at the true run head. Its literal suffix, restricted
to a prescribed-contact window, is canonical for both actual lower records. -/
theorem later_literal_section_finite_read {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q)
    {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (y : Y) (hy : y ∈ (geoTransformAlong (sectionMarked Q) T).cosupp)
    (hLevel : level (sectionMarked Q) T y = s+1)
    (hNS : ¬ IsSpecial (sectionMarked Q) T y)
    (hMax : IsMaximalOrderAlong (sectionMarked Q).N (sectionMarked Q).ideal (sectionMarked Q).d)
    (hCan : IsCanonical (sectionMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q)) T) :
    let I := invFamily (Nat.succ_pos n) k
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let j := regimeRun (stepRegime Sec (s+1)) T y
    let H := head T j
    let F := tail T j
    let p := F.proj y
    ∃ (W : Opens (split T j).1) (u : (split T j).1 → ℂ) (hpW : p ∈ W),
      let L := positiveMemberOn P H p W
      let S := positiveMemberOn Sec H p W
      let C := withN (coeffMarkedAlong L) (L.N ∩ {x : W | u x.val = 0})
      let z : openPreimage F W := ⟨y, hpW⟩
      W ≤ maskA Sec H p ∧
      LaterSectionComparison (X := CMfd.of (n := n+1) W) Q.d k C S ∧
      IsCanonical C (I.inv C) (restrict W F) ∧
      IsCanonical S (I.inv S) (restrict W F) ∧
      z ∈ (geoTransformAlong C (restrict W F)).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM I Sec T y =
        toLex (s+1, (I.inv S (restrict W F) z : WithTop (ValTy k))) := by
  intro I P Sec j H F p
  let X₀ := CMfd.of (n := n+1) (productOpen U)
  let X := (split T j).1
  let M := maskA Sec H p
  have hSec : IsInvDomain (k+1) Sec := section_projected_domain k.succ Q.N Q.E Q.ideal Q.d hQ
  obtain ⟨hBarTest, hTest, hCos⟩ := Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (X := X₀) (k := k+1) I Sec hSec hMax (Nat.succ_pos n) T hCan
  have hData := Seq.StepOneAdmissible.hasLowerDataL_stepOneInvM_of_isCanonical (X := X₀)
    (k := k+1) Sec I hSec.isWellFormed hSec.one_le_d (Nat.succ_pos n) hMax hSec.dimLE T
    ((Seq.StepOneBridge.isCanonical_iff I Sec hSec hMax (Nat.succ_pos n) T).mp hCan)
    y (hCos.symm ▸ hy) hNS
  obtain ⟨hHreg, hpBar⟩ := stepRegime_and_mem_cosupp_head Sec hSec.isWellFormed T hBarTest
    (hCos.symm ▸ hy) hNS
  rw [hLevel] at hData hHreg hpBar
  obtain ⟨hpM, hDomM, hCanM, hyM⟩ := hData
  obtain ⟨hLevH, hNSH⟩ := hHreg
  have hSecH := ((isGeoTestTower_iff_head_tail Sec T j).mp hTest).1
  have hBarH := ((isGeoTestTower_iff_head_tail (barMarked Sec) T j).mp hBarTest).1
  have hPS := properNormalMarked_locWPEquiv_section Q hQ
  have hPH := (hPS.wEquiv.2 H).1.mpr hSecH
  have hB := bar_local_any_boundary (X := X₀) Sec hSec
  have hpSec := ((hB.wEquiv.2 H).2 hSecH).symm ▸ hpBar
  have hpP := ((hPS.wEquiv.2 H).2 hPH).symm ▸ hpSec
  have hLevP := (level_eq_of_E_eq (A := P) (B := Sec) rfl H p).trans hLevH
  obtain ⟨W, u, hpW, _, hWM, _, hL, hC, _, hu, hTrace⟩ :=
    exists_later_contact_recursive_domain_of_section_nonspecial Q hQ H hPH p hpP hLevP hNSH
  let XW := CMfd.of (n := n+1) W
  let L := positiveMemberOn P H p W
  let S := positiveMemberOn Sec H p W
  let C := withN (coeffMarkedAlong L) (L.N ∩ {x : W | u x.val = 0})
  let z : openPreimage F W := ⟨y, hpW⟩
  have hCmp : LaterSectionComparison (X := XW) Q.d k C S :=
    later_section_comparison Q hQ H hPH p W u hL hu hTrace
      (by simpa only [Nat.add_sub_cancel] using hC)
  let B := geoTransformAlong (barMarked (X := X₀) Sec) H
  let S₀ := memberRestrict B (membersThrough B.E (origMembers Sec H) p)
  have hBdom : IsInvDomain (k+1) B :=
    isInvDomain_geoTransformAlong (isInvDomain_barMarked (X := X₀) Sec hSec) H hBarH
  have hS₀ : S₀.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hBdom.isWellFormed _
  obtain ⟨hCanS, hyS, hVal⟩ := restrict_actual_section_tail (X := X) I S₀ hS₀.isCoherent
    (U := M) (W := W) hWM F y hpW hDomM hCanM hyM
  have hCanC := (invFamily_isCanonical_iff_of_local (Nat.succ_pos n) C S
    hCmp.contactDomain hCmp.sectionDomain hCmp.localClass (SameCarrierDim.of_N_eq hCmp.carrier)
    hCmp.exponents (restrict W F)).mpr hCanS
  have hTestC := I.isInvValue.isGeoTestTower_of_isCanonical hCmp.contactDomain _ hCanC
  have hyC := ((hCmp.localClass.wEquiv.2 (restrict W F)).2 hTestC).symm ▸ hyS
  have hRead := positive_upper_read (X := X₀) (k := k) (Nat.succ_pos n) Sec T y hLevel hNS hpM
  refine ⟨W, u, hpW, hWM, hCmp, hCanC, hCanS, hyC, ?_⟩
  exact hRead.trans (congrArg (fun v : ValTy k => toLex (s+1, (v : WithTop (ValTy k)))) hVal.symm)

set_option maxHeartbeats 1500000 in
/-- Same-level finite section strata compare by the prescribed contacts
on the actual canonical suffix of each anchor, including ties. -/
theorem later_literal_section_finite_stratum {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q)
    {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hMax : IsMaximalOrderAlong (sectionMarked Q).N (sectionMarked Q).ideal (sectionMarked Q).d)
    (hCan : IsCanonical (sectionMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q)) T)
    {A : Type*} (i : A → Y)
    (hAnchors : ∀ a : A, i a ∈ (geoTransformAlong (sectionMarked Q) T).cosupp ∧
      level (sectionMarked Q) T (i a) = s+1 ∧ ¬ IsSpecial (sectionMarked Q) T (i a)) :
    let I := invFamily (Nat.succ_pos n) k
    let Sec := sectionMarked Q
    let f := Seq.StepOneValueMasked.stepOneInvM I Sec T
    ∃ g : A → ValTy k,
      (∀ a : A,
        let y := i a
        let j := regimeRun (stepRegime Sec (s+1)) T y
        let H := head T j
        let F := tail T j
        let p := F.proj y
        ∃ (W : Opens (split T j).1) (u : (split T j).1 → ℂ) (hpW : p ∈ W),
          let L := positiveMemberOn (properNormalMarked Q) H p W
          let S := positiveMemberOn Sec H p W
          let C := withN (coeffMarkedAlong L) (L.N ∩ {x : W | u x.val = 0})
          let z : openPreimage F W := ⟨y, hpW⟩
          LaterSectionComparison (X := CMfd.of (n := n+1) W) Q.d k C S ∧
          IsCanonical C (I.inv C) (restrict W F) ∧
          z ∈ (geoTransformAlong C (restrict W F)).cosupp ∧
          g a = I.inv C (restrict W F) z) ∧
      (∀ a b : A, g a < g b ↔ f (i a) < f (i b)) ∧
      i '' maxLocus g univ = maxLocus f (range i) := by
  intro I Sec f
  let j (a : A) := regimeRun (stepRegime Sec (s+1)) T (i a)
  let H (a : A) := head T (j a)
  let F (a : A) := tail T (j a)
  let p (a : A) := (F a).proj (i a)
  have hEach (a : A) := later_literal_section_finite_read Q hQ T (i a)
    (hAnchors a).1 (hAnchors a).2.1 (hAnchors a).2.2 hMax hCan
  choose W u hpW hWM hPair hCanC hCanS hCos hRead using hEach
  let L (a : A) := positiveMemberOn (properNormalMarked Q) (H a) (p a) (W a)
  let C (a : A) : MarkedIdeal (n+1) (CMfd.of (n := n+1) (W a)) :=
    withN (coeffMarkedAlong (L a)) ((L a).N ∩ {x : W a | u a x.val = 0})
  let z (a : A) : openPreimage (F a) (W a) := ⟨i a, hpW a⟩
  let g (a : A) := I.inv (C a) (restrict (W a) (F a)) (z a)
  have hEmb : StrictMono (fun v : ValTy k =>
      (toLex (s+1, (v : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k))) := by
    intro x y h
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, WithTop.coe_lt_coe.mpr h⟩)
  have hLt (a b : A) : g a < g b ↔ f (i a) < f (i b) := by
    change g a < g b ↔
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q) T (i a) <
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q) T (i b)
    rw [hRead a, hRead b, hEmb.lt_iff_lt]
    exact LaterSectionComparison.lt_iff (hPair a) (hPair b)
      (restrict (W a) (F a)) (restrict (W b) (F b)) (hCanC a) (hCanC b)
      (z a) (hCos a) (z b) (hCos b)
  have hLe (a b : A) : g a ≤ g b ↔ f (i a) ≤ f (i b) := by
    simpa only [not_lt] using not_congr (hLt b a)
  have hPre : i ⁻¹' maxLocus f (range i) = maxLocus g univ := by
    ext a
    constructor
    · intro ha
      have hm : i a ∈ maxLocus f (range i) := ha
      exact ⟨mem_univ a, fun b _ => (hLe b a).mpr (hm.2 (i b) (mem_range_self b))⟩
    · intro ha
      refine ⟨mem_range_self a, ?_⟩
      rintro _ ⟨b, rfl⟩
      exact (hLe b a).mp (ha.2 b (mem_univ b))
  refine ⟨g, fun a => ⟨W a, u a, hpW a, hPair a, hCanC a, hCos a, rfl⟩, hLt, ?_⟩
  rw [← hPre, image_preimage_eq_inter_range]
  exact inter_eq_left.mpr (fun _ h => h.1)

end
end Hironaka.HironakaG1LaterLiteralSectionCanonicalTail
