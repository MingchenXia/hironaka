import Hironaka.Resolution.HironakaG1LaterSectionPairOrder
import Hironaka.Resolution.HironakaG1LaterContactRecursiveDomain
import Hironaka.Invariant.MaxLocusLocal

/-! The literal section upper read when the current positive run has just started. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterLiteralSectionUpperRead
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

private theorem inv_refl_on_subwindow {n k : ℕ} {X : CMfd.{0} n}
    (I : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k (ValTy k))
    (A : MarkedIdeal n X) (hA : A.ideal.IsCoherent) {U W : Opens X} (hWU : W ≤ U)
    (hU : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : U → X) A))
    (p : W) (hp : (p : X) ∈ A.cosupp) :
    I.inv (MarkedIdeal.pullback (Subtype.val : W → X) A) (.refl (X := CMfd.of (n := n) W)) p =
    I.inv (MarkedIdeal.pullback (Subtype.val : U → X) A) (.refl (X := CMfd.of (n := n) U))
      (⟨p, hWU p.property⟩ : U) := by
  let E := nestedOpens U W
  let A₀ := MarkedIdeal.pullback (Subtype.val : U → X) A
  let A₁ := MarkedIdeal.pullback (Subtype.val : E → U) A₀
  let Ψ := nestedOpensDiffeo (n := n) hWU
  let z : E := Ψ.symm p
  have hD : IsInvDomain k A₁ := isInvDomain_pullback_val E hU
  have hEq : MarkedIdeal.pullback Ψ.symm A₁ = MarkedIdeal.pullback (Subtype.val : W → X) A :=
    pullback_symm_nestedOpensDiffeo hA hWU
  have hx : (z.val : U) ∈ A₀.cosupp := by
    change z.val ∈ (MarkedIdeal.pullback (Subtype.val : U → X) A).cosupp
    rw [cosupp_pullback_val A (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hA hg) U]
    exact hp
  have hz : z ∈ A₁.cosupp := by
    change z ∈ (MarkedIdeal.pullback (Subtype.val : E → U) A₀).cosupp
    rw [cosupp_pullback_val A₀
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hU.isWellFormed.isCoherent hg) E]
    exact hx
  have hIso := I.isInvValue.towerIso Ψ.symm A₁ hD (.refl (X := CMfd.of (n := n) W))
    (.refl (X := CMfd.of (n := n) E)) Ψ.symm IsTowerIso.refl trivial p hz
  rw [hEq] at hIso
  exact hIso.trans (I.isInvValue.restrictOpen (X := CMfd.of (n := n) U)
    A₀ hU E (.refl (X := CMfd.of (n := n) U)) trivial z hx)

private theorem positive_restart_read {n k s : ℕ} {X Y : CMfd.{0} n}
    (hn : 0 < n) (A : MarkedIdeal n X) (H : BlowupTower X Y) (p : Y)
    (hLev : level A H p = s+1) (hNS : ¬ IsSpecial A H p)
    (hRun : regimeRun (stepRegime A (s+1)) H p = 0)
    (hp : p ∈ maskA A H p) :
    let I := invFamily hn k
    let M := maskA A H p
    let L := lowerMarkedM A (s+1) H p
    Seq.StepOneValueMasked.stepOneInvM I A H p =
      toLex (s+1, (I.inv L (.refl (X := CMfd.of (n := n) M)) (⟨p, hp⟩ : M) :
        WithTop (ValTy k))) := by
  intro I M L
  have hRaw := Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial (X := X) I A
    (lowerMarkedM A) H (y := p) hNS
  rw [hLev, hRun] at hRaw
  have hCut :
      Seq.StepOneValueMasked.lowerValueL I A (lowerMarkedM A) (s+1) (head H 0) (tail H 0) p =
      Seq.StepOneValueMasked.lowerValueL I A (lowerMarkedM A) (s+1) H (.refl (X := Y)) p := by
    cases H <;> rfl
  rw [hCut] at hRaw
  have hLow := Seq.StepOneValueMasked.lowerValueL_eq_of_mem (X := X) I A (lowerMarkedM A)
    (s := s+1) (T₀ := H) (T₁ := .refl (X := Y)) (y := p) hp
  exact hRaw.trans (congrArg (fun v : WithTop (ValTy k) => toLex (s+1, v)) hLow)

set_option maxHeartbeats 1300000 in
/-- At the start of a positive section run, the upper section's exact
finite recursive value is the cut paired with the prescribed contact.
The actual test history may already have born exceptional members. -/
theorem later_literal_section_restart_read {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q)
    {Y : CMfd.{0} (n+1)}
    (H : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hp : p ∈ (geoTransformAlong (properNormalMarked Q) H).cosupp)
    (hLevel : level (properNormalMarked Q) H p = s+1)
    (hNS : ¬ IsSpecial (sectionMarked Q) H p)
    (hRun : regimeRun (stepRegime (sectionMarked Q) (s+1)) H p = 0) :
    let I := invFamily (Nat.succ_pos n) k
    ∃ (W : Opens Y) (u : Y → ℂ) (hpW : p ∈ W),
      let XW := CMfd.of (n := n+1) W
      let L := positiveMemberOn (properNormalMarked Q) H p W
      let S := positiveMemberOn (sectionMarked Q) H p W
      let C := withN (coeffMarkedAlong L) (L.N ∩ {x : W | u x.val = 0})
      let z : W := ⟨p, hpW⟩
      W ≤ maskA (sectionMarked Q) H p ∧
      LaterSectionComparison (X := XW) Q.d k C S ∧ z ∈ C.cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM I (sectionMarked Q) H p =
        toLex (s+1, (I.inv S (.refl (X := XW)) z : WithTop (ValTy k))) := by
  intro I
  let X₀ := CMfd.of (n := n+1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let M := maskA Sec H p
  obtain ⟨W, u, hpW, _, hWM, _, hL, hC, hS, hu, hTrace⟩ :=
    exists_later_contact_recursive_domain_of_section_nonspecial Q hQ H hH p hp hLevel hNS
  let XW := CMfd.of (n := n+1) W
  let L := positiveMemberOn P H p W
  let S := positiveMemberOn Sec H p W
  let C := withN (coeffMarkedAlong L) (L.N ∩ {x : W | u x.val = 0})
  let z : W := ⟨p, hpW⟩
  have hComp : LaterSectionComparison (X := XW) Q.d k C S :=
    later_section_comparison Q hQ H hH p W u hL hu hTrace
      (by simpa only [Nat.add_sub_cancel] using hC)
  have hSec : IsInvDomain (k+1) Sec := section_projected_domain _ Q.N Q.E Q.ideal Q.d hQ
  have hScl := properNormalMarked_locWPEquiv_section Q hQ
  have hHT := (hScl.wEquiv.2 H).1.mp hH
  have hpSec := (hScl.wEquiv.2 H).2 hH ▸ hp
  have hBar := bar_local_any_boundary (X := X₀) Sec hSec
  have hBT := (hBar.wEquiv.2 H).1.mp hHT
  have hpBar := (hBar.wEquiv.2 H).2 hHT ▸ hpSec
  let B := geoTransformAlong (barMarked (X := X₀) Sec) H
  let S₀ := memberRestrict B (membersThrough B.E (origMembers Sec H) p)
  have hB : IsInvDomain (k+1) B :=
    isInvDomain_geoTransformAlong (isInvDomain_barMarked (X := X₀) Sec hSec) H hBT
  have hS₀ := isWellFormed_memberRestrict (Nat.succ_pos n) hB.isWellFormed
    (membersThrough B.E (origMembers Sec H) p)
  have hpS : p ∈ S₀.cosupp := by
    change p ∈ (memberRestrict B _).cosupp
    rw [cosupp_memberRestrict hB.isWellFormed hB.one_le_d]
    refine ⟨hpBar, ?_⟩
    have hOld : ∀ D ∈ origMembers Sec H, D ∈ B.E := fun _ h => List.mem_of_mem_take h
    rw [memberInter_membersThrough hOld]
    exact fun _ _ h => h
  have hzS : z ∈ S.cosupp := by
    change z ∈ (MarkedIdeal.pullback (Subtype.val : W → Y) S₀).cosupp
    rw [cosupp_pullback_val S₀ (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hS₀.isCoherent hg) W]
    exact hpS
  have hzC : z ∈ C.cosupp := hComp.localClass.cosupp_eq_base.symm ▸ hzS
  have hLev : level Sec H p = s+1 :=
    (level_eq_of_E_eq (A := P) (B := Sec) rfl H p).symm.trans hLevel
  have hFull : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : M → Y) S₀) := by
    have hDomain := isInvDomain_lowerMarked_succ Sec hSec.isWellFormed hSec.one_le_d
      (Nat.succ_pos n) H hBT hSec.dimLE hLev
    change IsInvDomain k (lowerMarked Sec (s+1) H p)
    simpa only [Nat.add_sub_cancel] using hDomain
  have hWindow := inv_refl_on_subwindow I S₀ hS₀.isCoherent (U := M) (W := W) hWM hFull z hpS
  have hMem : p ∈ M := hWM hpW
  have hRead := positive_restart_read (X := X₀) (k := k) (Nat.succ_pos n) Sec H p hLev hNS hRun hMem
  refine ⟨W, u, hpW, hWM, hComp, hzC, hRead.trans ?_⟩
  exact congrArg (fun v : ValTy k => toLex (s+1, (v : WithTop (ValTy k)))) hWindow.symm

set_option maxHeartbeats 1200000 in
/-- On a same-level section stratum whose positive runs start at the
current stage, the actual prescribed contacts give the exact strict cuts
and maximum locus of the original section upper evaluator. -/
theorem later_literal_section_restart_stratum {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q)
    {Y : CMfd.{0} (n+1)}
    (H : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H)
    {A : Type*} (i : A → Y)
    (hAnchors : ∀ a : A, i a ∈ (geoTransformAlong (properNormalMarked Q) H).cosupp ∧
      level (properNormalMarked Q) H (i a) = s+1 ∧
      ¬ IsSpecial (sectionMarked Q) H (i a) ∧
      regimeRun (stepRegime (sectionMarked Q) (s+1)) H (i a) = 0) :
    let I := invFamily (Nat.succ_pos n) k
    let f := Seq.StepOneValueMasked.stepOneInvM I (sectionMarked Q) H
    ∃ g : A → ValTy k,
      (∀ a : A, ∃ (W : Opens Y) (u : Y → ℂ) (hpW : i a ∈ W),
        let XW := CMfd.of (n := n+1) W
        let L := positiveMemberOn (properNormalMarked Q) H (i a) W
        let S := positiveMemberOn (sectionMarked Q) H (i a) W
        let C := withN (coeffMarkedAlong L) (L.N ∩ {x : W | u x.val = 0})
        let z : W := ⟨i a, hpW⟩
        LaterSectionComparison (X := XW) Q.d k C S ∧ z ∈ C.cosupp ∧
          g a = I.inv C (.refl (X := XW)) z) ∧
      (∀ a b : A, g a < g b ↔ f (i a) < f (i b)) ∧
      i '' maxLocus g univ = maxLocus f (range i) := by
  intro I f
  have hEach (a : A) := later_literal_section_restart_read Q hQ H hH (i a)
    (hAnchors a).1 (hAnchors a).2.1 (hAnchors a).2.2.1 (hAnchors a).2.2.2
  choose W u hpW hWM hPair hCos hRead using hEach
  let XW (a : A) := CMfd.of (n := n+1) (W a)
  let L (a : A) := positiveMemberOn (properNormalMarked Q) H (i a) (W a)
  let C (a : A) : MarkedIdeal (n+1) (XW a) :=
    withN (coeffMarkedAlong (L a)) ((L a).N ∩ {x : W a | u a x.val = 0})
  let z (a : A) : W a := ⟨i a, hpW a⟩
  let g (a : A) := I.inv (C a) (.refl (X := XW a)) (z a)
  have hEmb : StrictMono (fun v : ValTy k =>
      (toLex (s+1, (v : WithTop (ValTy k))) : ℕ ×ₗ WithTop (ValTy k))) := by
    intro x y h
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, WithTop.coe_lt_coe.mpr h⟩)
  have hLt (a b : A) : g a < g b ↔ f (i a) < f (i b) := by
    change g a < g b ↔
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q) H (i a) <
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q) H (i b)
    rw [hRead a, hRead b, hEmb.lt_iff_lt]
    exact LaterSectionComparison.lt_iff (hPair a) (hPair b)
      (.refl (X := XW a)) (.refl (X := XW b)) trivial trivial
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
  refine ⟨g, fun a => ⟨W a, u a, hpW a, hPair a, hCos a, rfl⟩, hLt, ?_⟩
  rw [← hPre, image_preimage_eq_inter_range]
  exact inter_eq_left.mpr (fun _ h => h.1)

end
end Hironaka.HironakaG1LaterLiteralSectionUpperRead
