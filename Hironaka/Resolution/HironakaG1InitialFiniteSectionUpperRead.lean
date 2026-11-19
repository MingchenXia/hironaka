import Hironaka.Resolution.HironakaG1InitialPositiveAllStratumCentres
import Hironaka.Resolution.HironakaActualFullBoundaryCurveEndpointHistories

/-! The original finite section read through the literal nested masks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialFiniteSectionUpperRead
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec InvDomainTowerAlong ContactRepresentative
  MarkedIdealOperationsAlong.MarkedIdeal ResolutionInvariantSeq
  HironakaActualFullBoundaryCurveEndpointHistories MaxLocusLocal
  RelativePrincipalizationSpan CanonicalCentres StepOneValue StepOneValueMasked StepOneLowerDomain
  GeneralValue NonmonomialOrderTail CompanionRebase ContactStageKept
  InvDomainMemberRestriction HironakaG1InitialCompanionSectionPairOrder
  HironakaG1ProperNormalOriginalTest HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaActualOpenZeroSectionDifferentials
  HironakaActualRelativeNormalGeometry HironakaG1InitialCompanionSectionComparison
  HironakaG8MemberLoci HironakaG8LocalHistory HironakaCoherentTransformExtension
  BlowupTowerSplit StepOneRegime BlowupTowerIsomorphism HironakaActualSectionBoundaryGeometry
  HironakaG1InitialCompanionSpecial HironakaG1InitialPositiveFiniteCentres
  HironakaG1PositiveNormalRepairCentres HironakaG1InitialSelectedOrderPhase
  RestrictedIdealExtension ResolutionDriver

private theorem flatten_refl_value {n k : ℕ} {X : CMfd.{0} n}
    (I : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k (ValTy k)) (A : MarkedIdeal n X)
    (hA : A.ideal.IsCoherent) (U : Opens X) (W : Opens (CMfd.of (n := n) U)) :
    let V := ambientOpen U W
    let XW := CMfd.of (n := n) W
    let XV := CMfd.of (n := n) V
    let Φ := flattenOpenEquiv U W
    let P := MarkedIdeal.pullback (Subtype.val : W → U)
      (MarkedIdeal.pullback (Subtype.val : U → X) A)
    let Q := MarkedIdeal.pullback (Subtype.val : V → X) A
    ∀ (_hP : IsInvDomain k P) (w : W), w ∈ P.cosupp →
      IsInvDomain k Q ∧ Φ w ∈ Q.cosupp ∧
      I.inv P (.refl (X := XW)) w = I.inv Q (.refl (X := XV)) (Φ w) := by
  intro V XW XV Φ P Q hP w hw
  have hEq : MarkedIdeal.pullback Φ.symm P = Q := by
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
    · change ((A.E.map ((Subtype.val : U → X) ⁻¹' ·)).map
          ((Subtype.val : W → U) ⁻¹' ·)).map (Φ.symm ⁻¹' ·) = _
      rw [List.map_map, List.map_map]
      rfl
    · change GermIdeal.pullback (m := n) Φ.symm
          (GermIdeal.pullback (m := n) (Subtype.val : W → U)
            (GermIdeal.pullback (m := n) (Subtype.val : U → X) A.ideal)) = _
      rw [← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val contMDiff_subtype_val hA,
        ← GermIdealTotalTransform.pullback_comp (contMDiff_subtype_val.comp contMDiff_subtype_val)
          Φ.symm.contMDiff hA]
      rfl
  have hQ : IsInvDomain k Q := hEq ▸ isInvDomain_pullback Φ.symm hP
  have hCos := MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback
    Φ.symm.contMDiff Φ.contMDiff Φ.symm_apply_apply Φ.apply_symm_apply P
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hg)
  rw [hEq] at hCos
  have hy : Φ w ∈ Q.cosupp := by
    rw [hCos]
    simpa only [mem_preimage, Φ.symm_apply_apply] using hw
  have hVal := I.isInvValue.towerIso Φ.symm P hP (.refl (X := XV)) (.refl (X := XW))
    Φ.symm IsTowerIso.refl trivial (Φ w) (by
      change Φ.symm (Φ w) ∈ P.cosupp
      rw [Φ.symm_apply_apply]
      exact hw)
  rw [hEq, Φ.symm_apply_apply] at hVal
  exact ⟨hQ, hy, hVal.symm⟩

private theorem refl_value_on_common_restrictions {n k : ℕ} {X : CMfd.{0} n}
    (I : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k (ValTy k)) (A B : MarkedIdeal n X)
    (hA : A.ideal.IsCoherent) (hB : B.ideal.IsCoherent) (hEq : RestrictEquiv A B)
    (U V : Opens X) :
    let P := MarkedIdeal.pullback (Subtype.val : U → X) A
    let Q := MarkedIdeal.pullback (Subtype.val : V → X) B
    ∀ (_hP : IsInvDomain k P) (_hQ : IsInvDomain k Q) (x : X) (hxU : x ∈ U) (hxV : x ∈ V),
      (⟨x, hxU⟩ : U) ∈ P.cosupp →
      I.inv P (.refl (X := CMfd.of (n := n) U)) (⟨x, hxU⟩ : U) =
        I.inv Q (.refl (X := CMfd.of (n := n) V)) (⟨x, hxV⟩ : V) := by
  intro P Q hP hQ x hxU hxV hx
  let W := U ⊓ V
  let Y := CMfd.of (n := n) W
  let p : W := ⟨x, hxU, hxV⟩
  let A' := MarkedIdeal.pullback (Subtype.val : W → X) A
  let B' := MarkedIdeal.pullback (Subtype.val : W → X) B
  have hCos : p ∈ A'.cosupp := by
    have hp := hx
    rw [show P = MarkedIdeal.pullback (Subtype.val : U → X) A from rfl,
      cosupp_pullback_val A (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hA hg) U] at hp
    rw [show A' = MarkedIdeal.pullback (Subtype.val : W → X) A from rfl,
      cosupp_pullback_val A (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hA hg) W]
    exact hp
  have hAt {A : MarkedIdeal n X} (hA : A.ideal.IsCoherent)
      (D : Opens X) (hWD : W ≤ D)
      (hD : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : D → X) A))
      (hxD : (⟨x, hWD p.property⟩ : D) ∈ (MarkedIdeal.pullback (Subtype.val : D → X) A).cosupp) :
      IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → X) A) ∧
        I.inv (MarkedIdeal.pullback (Subtype.val : W → X) A) (.refl (X := Y)) p =
        I.inv (MarkedIdeal.pullback (Subtype.val : D → X) A) (.refl (X := CMfd.of (n := n) D))
          (⟨x, hWD p.property⟩ : D) := by
    let E := nestedOpens D W
    let z : E := ⟨⟨x, hWD p.property⟩, p.property⟩
    let A₀ := MarkedIdeal.pullback (Subtype.val : D → X) A
    let A₁ := MarkedIdeal.pullback (Subtype.val : E → D) A₀
    let Ψ := nestedOpensDiffeo (n := n) hWD
    have hD' : IsInvDomain k A₁ := isInvDomain_pullback_val E hD
    have hEq' : MarkedIdeal.pullback Ψ.symm A₁ = MarkedIdeal.pullback (Subtype.val : W → X) A :=
      pullback_symm_nestedOpensDiffeo hA hWD
    have hz : z ∈ A₁.cosupp := by
      change z ∈ (MarkedIdeal.pullback (Subtype.val : E → D) A₀).cosupp
      rw [cosupp_pullback_val A₀
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hD.isWellFormed.isCoherent hg) E]
      exact hxD
    have hIso := I.isInvValue.towerIso Ψ.symm A₁ hD' (.refl (X := Y))
      (.refl (X := CMfd.of (n := n) E)) Ψ.symm IsTowerIso.refl trivial p hz
    rw [hEq'] at hIso
    exact ⟨hEq' ▸ isInvDomain_pullback Ψ.symm hD', hIso.trans
      (I.isInvValue.restrictOpen (X := CMfd.of (n := n) D) A₀ hD E
        (.refl (X := CMfd.of (n := n) D)) trivial z hxD)⟩
  obtain ⟨hA', hAv⟩ := hAt hA U inf_le_left hP hx
  have hRE : RestrictEquiv A' B' := restrictEquiv_pullback_val W hEq hA hB
  have hBW : B'.IsWellFormed := by
    have hEqB := pullback_symm_nestedOpensDiffeo hB (show W ≤ V from inf_le_right)
    have hDomB := isInvDomain_pullback (nestedOpensDiffeo (n := n) (show W ≤ V from inf_le_right)).symm
      (isInvDomain_pullback_val (nestedOpens V W) hQ)
    exact (hEqB ▸ hDomB).isWellFormed
  have hBCos : p ∈ B'.cosupp := by
    have hW := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv (X := Y) hRE
      hA'.isWellFormed.isClosedSubmanifold_N.1 hA'.isWellFormed.isCoherent hBW.isCoherent
    exact hW.cosupp_eq ▸ hCos
  have hxB : (⟨x, hxV⟩ : V) ∈ Q.cosupp := by
    rw [show B' = MarkedIdeal.pullback (Subtype.val : W → X) B from rfl,
      cosupp_pullback_val B (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB hg) W] at hBCos
    rw [show Q = MarkedIdeal.pullback (Subtype.val : V → X) B from rfl,
      cosupp_pullback_val B (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB hg) V]
    exact hBCos
  obtain ⟨hB', hBv⟩ := hAt hB V inf_le_right hQ hxB
  have hVal := I.isInvValue.representative (X := Y) A' B' hA' hB' hRE
    (.refl (X := Y)) trivial p hCos
  exact hAv.symm.trans (hVal.trans hBv)

private theorem positive_step_refl_read {n k s : ℕ} {X : CMfd.{0} n} (hn : 0 < n)
    (A : MarkedIdeal n X) (p : X)
    (hLevel : level A (.refl (X := X)) p = s+1)
    (hNS : ¬ IsSpecial A (.refl (X := X)) p)
    (hp : p ∈ maskA A (.refl (X := X)) p) :
    let V := invFamily hn k
    let O := maskA A (.refl (X := X)) p
    let L := lowerMarkedM A (s+1) (.refl (X := X)) p
    Seq.StepOneValueMasked.stepOneInvM V A (.refl (X := X)) p =
      toLex (s+1, (V.inv L (.refl (X := CMfd.of (n := n) O)) (⟨p, hp⟩ : O) :
        WithTop (ValTy k))) := by
  intro V O L
  have hStep := Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial V A
    (lowerMarkedM A) (.refl (X := X)) hNS
  rw [hLevel] at hStep
  have hLower := Seq.StepOneValueMasked.lowerValueL_eq_of_mem V A (lowerMarkedM A)
    (s := s+1) (T₀ := .refl (X := X)) (T₁ := .refl (X := X)) (y := p) hp
  exact hStep.trans (congrArg (fun v : WithTop (ValTy k) => toLex (s+1, v)) hLower)

set_option maxHeartbeats 1500000 in
/-- The actual finite supported cut on the triple companion window has
exactly the recursive value in the literal original section upper read. -/
theorem initial_finite_section_upper_read {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p = s + 1)
    (hpO : p ∈ maskA (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p) :
    let X₀ := CMfd.of (n := n+1) (productOpen U)
    let H := BlowupTower.refl (X := X₀)
    let P := properNormalMarked Q
    let O := lowerMask P (s+1) H p
    let X := CMfd.of (n := n+1) O
    let L : MarkedIdeal (n+1) X := lowerMarkedM (X := X₀) P (s+1) H p
    let C : Opens X := ordMask (M := X) (geoTransformAlong L (.refl (X := X))) L.d
    let Y := CMfd.of (n := n+1) C
    let J : MarkedIdeal (n+1) Y := compAt (X := X) L L.d (.refl (X := X))
    let u : C → ℂ := fun x => relativeNormalCoordinate U (x.val : O).val
    let B := barMarked (X := X₀) (supportedNormalMarked Q)
    let S := memberRestrict B (membersThrough B.E B.E p)
    let R₁ := MarkedIdeal.pullback (Subtype.val : O → X₀) S
    let R₂ := MarkedIdeal.pullback (Subtype.val : C → X) R₁
    ∀ (y : O) (hyC : y ∈ C),
      let z : C := ⟨y, hyC⟩
      let W := maskB J (.refl (X := Y)) z
      let K := contactMarkedKept J u (.refl (X := Y)) W
      let R := MarkedIdeal.pullback (Subtype.val : W → Y) R₂
      y.val = p → y ∈ L.cosupp → p ∈ P.cosupp →
      ¬ IsSpecial (sectionMarked Q) H p →
      ∃ hz : z ∈ W,
        let r : W := ⟨z, hz⟩
        let V := invFamily (Nat.succ_pos n) k
        FiniteSectionPair (X := CMfd.of (n := n+1) W) Q k K R r ∧
        Seq.StepOneValueMasked.stepOneInvM V (sectionMarked Q) H p =
          toLex (s+1, (V.inv R (.refl (X := CMfd.of (n := n+1) W)) r : WithTop (ValTy k))) ∧
        Seq.StepOneValueMasked.stepOneInvM V J (.refl (X := Y)) z =
          toLex (0, (V.inv K (.refl (X := CMfd.of (n := n+1) W)) r : WithTop (ValTy k))) := by
  intro X₀ H P O X L C Y J u B S R₁ R₂ y hyC z W K R hyp hy hpP hSec
  have hNS : ¬ IsSpecial J (.refl (X := Y)) z := by
    intro hs
    have hCmp := (initial_positive_companion_special_iff Q hQ p hpP hLevel z hyp).2
    exact hSec (hCmp.mp hs)
  obtain ⟨hz, hPair, hValue⟩ := initial_finite_section_records Q hQ p hLevel hpO y hyC hy hNS
  let r : W := ⟨z, hz⟩
  let Z := CMfd.of (n := n+1) W
  let I := invFamily (Nat.succ_pos n) k
  let A := sectionMarked Q
  let Abar := barMarked (X := X₀) A
  let Aselected := memberRestrict Abar (membersThrough Abar.E Abar.E p)
  have hA : IsInvDomain (k+1) A := section_projected_domain _ Q.N Q.E Q.ideal Q.d hQ
  obtain ⟨hSupEq, hSupp, _⟩ := supported_normal_data Q hQ
  have hB := isInvDomain_barMarked (X := X₀) (supportedNormalMarked Q) hSupp
  have hAbar := isInvDomain_barMarked (X := X₀) A hA
  have hBarEq : RestrictEquiv B Abar :=
    restrictEquiv_barMarked hSupEq hSupp.isWellFormed.isClosedSubmanifold_N
      hSupp.isWellFormed.isCoherent hA.isWellFormed.isCoherent
  have hES : Abar.E = B.E := hBarEq.E_eq.symm
  have hCuts : RestrictEquiv S Aselected := by
    have hc := StepOneEmptyPrefix.restrictEquiv_memberRestrict_membersThrough hBarEq
      hB.isWellFormed.isCoherent hAbar.isWellFormed.isCoherent B.E p
    have hRhs := congrArg (fun E => memberRestrict Abar (membersThrough Abar.E E p)) hES
    rw [← hRhs] at hc
    exact hc
  have hSCoh := (isWellFormed_memberRestrict (Nat.succ_pos n) hB.isWellFormed
    (membersThrough B.E B.E p)).isCoherent
  have hTCo := (isWellFormed_memberRestrict (Nat.succ_pos n) hAbar.isWellFormed
    (membersThrough Abar.E Abar.E p)).isCoherent
  let D₁ := ambientOpen C W
  let D₂ := ambientOpen O D₁
  obtain ⟨hD₁, hx₁, hv₁⟩ := flatten_refl_value (X := X) I R₁
    ((MarkedIdealRestrictOpen.IsWellFormed.pullback_val
      (isWellFormed_memberRestrict (Nat.succ_pos n) hB.isWellFormed (membersThrough B.E B.E p)) O).isCoherent)
    C W hPair.sectionDomain (⟨z, hz⟩ : W) (hPair.locallyEquivalent.cosupp_eq_base ▸ hPair.survives)
  obtain ⟨hD₂, hx₂, hv₂⟩ := flatten_refl_value (X := X₀) I S hSCoh
    O D₁ hD₁ (flattenOpenEquiv C W r) hx₁
  let r₂ := flattenOpenEquiv O D₁ (flattenOpenEquiv C W r)
  have hp' : r₂.val = p := hyp
  have hLvl : level A H p = s+1 :=
    (level_eq_of_E_eq (A := P) (B := A) rfl H p).symm.trans hLevel
  have hpA := mem_maskA A hA.isWellFormed hA.one_le_d (Nat.succ_pos n) H trivial
    (y₀ := p) (by omega) hSec
  let UA := maskA A H p
  let Lsec := lowerMarkedM A (s+1) H p
  have hDom : IsInvDomain k Lsec := by
    have h := isInvDomain_lowerMarked_succ A hA.isWellFormed hA.one_le_d (Nat.succ_pos n)
      H trivial hA.dimLE hLvl
    simpa only [Nat.add_sub_cancel, Lsec, lowerMarkedM] using h
  have hActual : Lsec = MarkedIdeal.pullback (Subtype.val : UA → X₀) Aselected := by
    change MarkedIdeal.pullback (Subtype.val : UA → X₀)
      (memberRestrict Abar (membersThrough Abar.E (Abar.E.take A.E.length) p)) = _
    rw [show A.E = Abar.E from rfl, List.take_length]
  have hvOverlap :=
    refl_value_on_common_restrictions (X := X₀) I S Aselected hSCoh hTCo hCuts D₂ UA
      hD₂ (hActual ▸ hDom) r₂.val r₂.property (hp'.symm ▸ hpA) hx₂
  have hV := hv₁.trans (hv₂.trans hvOverlap)
  rw [← hActual] at hV
  have hRead := positive_step_refl_read (X := X₀) (k := k) (Nat.succ_pos n) A p hLvl hSec hpA
  refine ⟨hz, hPair, ?_, hValue⟩
  exact hRead.trans (congrArg (fun v : ValTy k => toLex (s+1, (v : WithTop (ValTy k))))
    (by simpa only [hp'] using hV.symm))


section Stratum

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  (hQ : IsInvDomain (k+1) Q) {A : Type*} (i : A → productOpen U)

local notation "X₀" => CMfd.of (n := n+1) (productOpen U)
local notation "T₀" => BlowupTower.refl (X := X₀)
local notation "P" => properNormalMarked Q
local notation "SEC" => sectionMarked Q
local notation "V" => invFamily (Nat.succ_pos n) k
local notation "f" => Seq.StepOneValueMasked.stepOneInvM
  (invFamily (Nat.succ_pos n) (k+1)) (properNormalMarked Q) T₀
local notation "fM" => Seq.StepOneValueMasked.stepOneInvM
  (invFamily (Nat.succ_pos n) k) (sectionMarked Q) T₀

include hQ in
private theorem selected_survives_of_initial_finite_read {p : productOpen U}
    (F : InitialFiniteRead Q T₀ p k s) :
    (⟨p, F.head_mem⟩ : initialMask Q T₀ p) ∈ (initialSelected Q T₀ p s).cosupp := by
  let O := initialMask Q T₀ p
  let X := CMfd.of (n := n+1) O
  let L := initialSelected Q T₀ p s
  let C := initialCompanionMask Q T₀ p s
  let J := initialCompanion Q T₀ p s
  let B := companionOf (n+1) (M := X) L L.d
  let z : C := F.point
  have hL : IsInvDomain (k+1) L := padded_lower_isInvDomain Q hQ T₀ trivial p F.initial_level
  have hB := (original_initial_positive_lower_companion_recursion Q hQ p F.initial_level).1
  have hEq : MarkedIdeal.pullback (Subtype.val : C → X) B = J :=
    pullback_val_companionOf (Nat.succ_pos n) hL.isWellFormed hL.isNonzeroAlongAt C L.d
  have hLB : RestrictEquiv L B := by
    rw [show B = ⟨L.N, L.E, restrictOn (n+1) L.N L.ideal, L.d⟩ from
      (original_initial_positive_lower_companion_eq Q hQ p F.initial_level).2]
    exact ⟨rfl, rfl, rfl, restrictLe_self_restrictOn hL.isWellFormed.isCoherent, restrictLe_restrictOn⟩
  have hCos := (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hLB hL.isWellFormed.isClosedSubmanifold_N.1
    hL.isWellFormed.isCoherent hB.isWellFormed.isCoherent).cosupp_eq
  have hz : z ∈ J.cosupp := F.cosupp
  rw [← hEq, cosupp_pullback_val B
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg) C] at hz
  exact hCos.symm ▸ hz


private theorem section_top_read {p : productOpen U} (hLevel : level P T₀ p = s+1)
    (hs : IsSpecial SEC T₀ p) :
    fM p = toLex (s+1, (⊤ : WithTop (ValTy k))) := by
  have hLev : level SEC T₀ p = s+1 :=
    (level_eq_of_E_eq (A := P) (B := SEC) rfl T₀ p).symm.trans hLevel
  have hRead : fM p = toLex (level SEC T₀ p, (⊤ : WithTop (ValTy k))) :=
    Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (X := X₀)
      V SEC (lowerMarkedM (X := X₀) SEC) T₀ (y := p) hs
  exact hRead.trans (congrArg (fun t => toLex (t, (⊤ : WithTop (ValTy k)))) hLev)

include hQ in
set_option maxHeartbeats 1800000 in
/-- The literal original upper section read has the same order and maximum
locus as the padded upper read on a same-level initial positive stratum
of padded-nonspecial cosupport points. Both section branches are covered. -/
theorem initial_positive_literal_section_stratum
    (hAnchor : ∀ a : A, i a ∈ (P).cosupp ∧ level P T₀ (i a) = s+1 ∧
      ¬ IsSpecial P T₀ (i a)) :
    (∀ a b : A, f (i a) < f (i b) ↔ fM (i a) < fM (i b)) ∧
      maxLocus f (range i) = maxLocus fM (range i) := by
  classical
  let F (a : A) : InitialFiniteRead Q T₀ (i a) k s :=
    Classical.choice (exists_initialFiniteRead Q T₀ (i a) hQ trivial
      (hAnchor a).1 (hAnchor a).2.1 (hAnchor a).2.2 rfl)
  let e (z : WithTop (ValTy k)) : ℕ ×ₗ WithTop (ValTy k) := toLex (0, z)
  let eM (z : WithTop (ValTy k)) : ℕ ×ₗ WithTop (ValTy k) := toLex (s+1, z)
  have hMono (l : ℕ) : StrictMono (fun z : WithTop (ValTy k) =>
      (toLex (l, z) : ℕ ×ₗ WithTop (ValTy k))) := by
    intro u v huv
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, huv⟩)
  have he : StrictMono e := hMono 0
  have heM : StrictMono eM := hMono (s+1)
  have hTop (a : A) (ha : IsSpecial SEC T₀ (i a)) :
      (F a).value = e ⊤ ∧ fM (i a) = eM ⊤ := by
    exact ⟨initial_positive_companion_special_value Q hQ (i a) (hAnchor a).1
      (hAnchor a).2.1 ha (F a).point rfl, section_top_read (k := k) Q (hAnchor a).2.1 ha⟩
  have hFinite (a : A) (ha : ¬ IsSpecial SEC T₀ (i a)) :
      ∃ (Z : CMfd.{0} (n+1)) (K R : MarkedIdeal (n+1) Z) (r : Z),
        FiniteSectionPair (X := Z) Q k K R r ∧
        (F a).value = e (((V).inv K (.refl (X := Z)) r : ValTy k) : WithTop (ValTy k)) ∧
        fM (i a) = eM (((V).inv R (.refl (X := Z)) r : ValTy k) : WithTop (ValTy k)) := by
    obtain ⟨hz, hPair, hM, hK⟩ := initial_finite_section_upper_read Q hQ (i a)
      (F a).initial_level (F a).head_mem ⟨i a, (F a).head_mem⟩ (F a).companion_mem
      rfl (selected_survives_of_initial_finite_read Q hQ (F a)) (hAnchor a).1 ha
    exact ⟨_, _, _, _, hPair, hK, hM⟩
  have hLt (a b : A) : f (i a) < f (i b) ↔ fM (i a) < fM (i b) := by
    rw [InitialFiniteRead.upper_lt_iff (F a) (F b)]
    by_cases ha : IsSpecial SEC T₀ (i a) <;> by_cases hb : IsSpecial SEC T₀ (i b)
    · rw [(hTop a ha).1, (hTop b hb).1, (hTop a ha).2, (hTop b hb).2,
        he.lt_iff_lt, heM.lt_iff_lt]
    · obtain ⟨Z, K, R, r, hPair, hK, hR⟩ := hFinite b hb
      rw [(hTop a ha).1, hK, (hTop a ha).2, hR, he.lt_iff_lt, heM.lt_iff_lt]
      simp
    · obtain ⟨Z, K, R, r, hPair, hK, hR⟩ := hFinite a ha
      rw [(hTop b hb).1, hK, (hTop b hb).2, hR, he.lt_iff_lt, heM.lt_iff_lt]
      simp
    · obtain ⟨_, _, _, _, hPair₁, hK₁, hR₁⟩ := hFinite a ha
      obtain ⟨_, _, _, _, hPair₂, hK₂, hR₂⟩ := hFinite b hb
      rw [hK₁, hK₂, hR₁, hR₂, he.lt_iff_lt, heM.lt_iff_lt]
      simpa only [WithTop.coe_lt_coe] using hPair₁.lt_iff hPair₂
  refine ⟨hLt, ?_⟩
  ext p
  constructor <;> rintro ⟨hp, hMax⟩ <;> refine ⟨hp, ?_⟩ <;>
    rcases hp with ⟨a, rfl⟩ <;> rintro _ ⟨b, rfl⟩
  · exact (not_lt.mp ((not_congr (hLt a b)).mp (not_lt.mpr (hMax _ (mem_range_self b)))))
  · exact (not_lt.mp ((not_congr (hLt a b)).mpr (not_lt.mpr (hMax _ (mem_range_self b)))))

end Stratum

end
end Hironaka.HironakaG1InitialFiniteSectionUpperRead
