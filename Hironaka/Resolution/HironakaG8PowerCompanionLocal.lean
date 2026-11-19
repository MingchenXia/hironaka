import Hironaka.Resolution.HironakaG8PowerCompanionEquiv
import Hironaka.Resolution.HironakaG8E4cCompanion
import Hironaka.Resolution.HironakaG8LocalPower
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PowerCompanionLocal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSpec
  NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase HironakaG8PowerNonmonomialOrder HironakaActualOriginalPowerTransform CompanionReductionAlong
  HironakaActualPowerBoundaryExponents HironakaG8LocalHistory HironakaG8LocalStable
  HironakaG8LocalPower HironakaG8CompanionEquiv HironakaG8PowerCompanionEquiv
  HironakaG8E4cCompanion HironakaG8E4cMonomialStep HironakaG8E4cProduct
  HironakaActualProjectionTestRecord HironakaG8MixedEquiv MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal

structure PowerCompData (o e : ℕ) {m : ℕ} {Y : CMfd.{0} m} (A B : MarkedIdeal m Y) : Prop where
  power : powerRel A B
  deq : B.d = A.d * e
  pos : 0 < m
  ho : 1 ≤ o
  he : 1 ≤ e
  ba : ∀ x ∈ A.cosupp, x ∉ ordGe A (o+1)
  bb : ∀ x ∈ B.cosupp, x ∉ ordGe B (e*o+1)

def PowerCompRel (o e : ℕ) {m : ℕ} {Y : CMfd.{0} m} (P Q : MarkedIdeal m Y) : Prop :=
  ∃ A B : MarkedIdeal m Y, PowerCompData o e A B ∧
    RestrictEquiv P (companionOf m A o) ∧ RestrictEquiv Q (companionOf m B (e*o)) ∧
    P.ideal.IsCoherent ∧ Q.ideal.IsCoherent

variable {m : ℕ} {Y : CMfd.{0} m} {o e : ℕ} {A B : MarkedIdeal m Y}

theorem PowerCompData.eqPower (hD : PowerCompData o e A B) :
    ∃ k k', IsInvDomain k A ∧ IsInvDomain k' B ∧ RestrictEquiv B (powerMarked A e) := by
  obtain ⟨k,k',j,hj,hA,hB,hr⟩ := hD.power
  have h : A.d * j = A.d * e := hr.d_eq.symm.trans hD.deq
  have hj' : j=e := Nat.eq_of_mul_eq_mul_left hA.one_le_d h
  subst j
  exact ⟨k,k',hA,hB,hr⟩

theorem PowerCompData.companion_equiv (hD : PowerCompData o e A B) :
    WEquiv (companionOf m A o) (companionOf m B (e*o)) := by
  obtain ⟨k,k',hA,hB,hr⟩ := hD.eqPower
  have hc := companionOf_congr hr hB.isWellFormed.isClosedSubmanifold_N.1 (e*o)
  rw [hc]
  exact wEquiv_companionOf_powerMarked hD.pos A hA hD.he hD.ho hD.ba

theorem PowerCompData.geoTransform (hD : PowerCompData o e A B) {C : Set Y}
    {Z : CMfd.{0} m} {π : Z → Y} (hπ : IsBlowupAlong m C π)
    (hC : (companionOf m A o).IsAdmissibleCentre C) :
    (companionOf m B (e*o)).IsAdmissibleCentre C ∧
      PowerCompData o e (A.geoTransform C π) (B.geoTransform C π) := by
  obtain ⟨k,k',hA,hB,hr⟩ := hD.eqPower
  have heo : 1 ≤ e*o := Nat.mul_pos hD.he hD.ho
  have hCW := hD.companion_equiv
  have hCB : (companionOf m B (e*o)).IsAdmissibleCentre C :=
    (isAdmissibleCentre_congr hCW.1 hCW.cosupp_eq C).mp hC
  have hCA' := (companion_step_facts hD.pos hA.isWellFormed hA.isNonzeroAlongAt hD.ho hD.ba hπ hC).1
  have hCB' := (companion_step_facts hD.pos hB.isWellFormed hB.isNonzeroAlongAt heo hD.bb hπ hCB).1
  refine ⟨hCB, (isLocStable_powerRel Kinds.wp).controlled hD.power C π hπ hCA', ?_, hD.pos, hD.ho, hD.he,
    (restrictEquiv_nonmonomial_geoTransform hD.pos hA.isWellFormed hA.isNonzeroAlongAt hD.ho hD.ba hπ hC).2,
    (restrictEquiv_nonmonomial_geoTransform hD.pos hB.isWellFormed hB.isNonzeroAlongAt heo hD.bb hπ hCB).2⟩
  exact hD.deq

theorem PowerCompData.projectionTest (hD : PowerCompData o e A B) :
    PowerCompData o e (projectionTest A) (projectionTest B) := by
  obtain ⟨k,k',hA,hB,hr⟩ := hD.eqPower
  exact ⟨(isLocStable_powerRel Kinds.wp).projection rfl hD.power, hD.deq, Nat.succ_pos m, hD.ho, hD.he,
    bound_projectionTest hD.pos hA.isWellFormed hA.isNonzeroAlongAt hD.ba,
    bound_projectionTest hD.pos hB.isWellFormed hB.isNonzeroAlongAt hD.bb⟩

theorem PowerCompData.pullback_val (hD : PowerCompData o e A B) (U : Opens Y) :
    PowerCompData (Y := CMfd.of (n := m) U) o e
      (MarkedIdeal.pullback (Subtype.val : U → Y) A) (MarkedIdeal.pullback (Subtype.val : U → Y) B) := by
  obtain ⟨k,k',hA,hB,hr⟩ := hD.eqPower
  exact ⟨(isLocStable_powerRel Kinds.wp).restrict hD.power U, hD.deq, hD.pos, hD.ho, hD.he,
    CompanionOpen.bound_pullback_val hD.pos hA.isWellFormed hA.isNonzeroAlongAt U fun x hx _ => hD.ba x hx,
    CompanionOpen.bound_pullback_val hD.pos hB.isWellFormed hB.isNonzeroAlongAt U fun x hx _ => hD.bb x hx⟩

theorem isLocStable_powerCompRel (o e : ℕ) :
    IsLocStable.{0} Kinds.wp (fun {m} {Y} P Q => PowerCompRel o e (m := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P Q ⟨A,B,hD,hP,hQ,_,_⟩
    rw [hQ.E_eq,hP.E_eq]
    exact hD.companion_equiv.1.symm
  cosupp_eq := by
    rintro m Y P Q ⟨A,B,hD,hP,hQ,_,_⟩
    rw [hP.cosupp_eq,hQ.cosupp_eq]
    exact hD.companion_equiv.cosupp_eq
  controlled := by
    rintro m Y P Q ⟨A,B,hD,hP,hQ,hPc,hQc⟩ C Z π hπ hC
    obtain ⟨k,k',hA,hB,hr⟩ := hD.eqPower
    have hCA : (companionOf m A o).IsAdmissibleCentre C := hP.isAdmissibleCentre_iff.mp hC
    obtain ⟨hCB,hD'⟩ := hD.geoTransform hπ hCA
    obtain ⟨hP',hPc'⟩ := restrictEquiv_geoTransform_companion hA hD.pos hD.ho hD.ba hP hPc hπ hCA
    obtain ⟨hQ',hQc'⟩ := restrictEquiv_geoTransform_companion hB hD.pos
      (Nat.mul_pos hD.he hD.ho) hD.bb hQ hQc hπ hCB
    exact ⟨_,_,hD',hP',hQ',hPc',hQc'⟩
  projection := by
    rintro _ m Y P Q ⟨A,B,hD,hP,hQ,hPc,hQc⟩
    obtain ⟨k,k',hA,hB,hr⟩ := hD.eqPower
    obtain ⟨hP',hPc'⟩ := restrictEquiv_projectionTest_companion hA hD.pos hD.ho hP hPc
    obtain ⟨hQ',hQc'⟩ := restrictEquiv_projectionTest_companion hB hD.pos
      (Nat.mul_pos hD.he hD.ho) hQ hQc
    exact ⟨_,_,hD.projectionTest,hP',hQ',hPc',hQc'⟩
  restrict := by
    rintro m Y P Q ⟨A,B,hD,hP,hQ,hPc,hQc⟩ U
    obtain ⟨k,k',hA,hB,hr⟩ := hD.eqPower
    obtain ⟨hP',hPc'⟩ := restrictEquiv_pullback_val_companion hA hD.pos hD.ho hP hPc U
    obtain ⟨hQ',hQc'⟩ := restrictEquiv_pullback_val_companion hB hD.pos
      (Nat.mul_pos hD.he hD.ho) hQ hQc U
    exact ⟨_,_,hD.pullback_val U,hP',hQ',hPc',hQc'⟩

/-- A companion and its whole-power recoding agree for controlled blowups,
products with a line, and arbitrary open restrictions at each stage. -/
theorem locWPEquiv_companionOf_powerMarked {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o)
    (hb : ∀ x ∈ M.cosupp, x ∉ ordGe M (o+1)) :
    LocWPEquiv (companionOf n M o) (companionOf n (powerMarked M e) (e*o)) := by
  have hPower := powerMarked_isInvDomain M hM he
  have heo : 1 ≤ e*o := Nat.mul_pos he ho
  have hbP : ∀ x ∈ (powerMarked M e).cosupp, x ∉ ordGe (powerMarked M e) (e*o+1) := by
    intro x hx hp
    have hxM : x ∈ M.cosupp := (powerMarked_cosupp M hM he) ▸ hx
    have hxN := M.cosupp_subset_N hxM
    have hp' := (mem_ordGe_iff hPower.isWellFormed hPower.isNonzeroAlongAt hxN _).mp hp
    rw [nmOrd_powerMarked hn M hM he hxN] at hp'
    have hgt : o < nmOrd M x := Nat.lt_of_mul_lt_mul_left (by omega : e*o < e*nmOrd M x)
    exact hb x hxM ((mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt hxN _).mpr (by omega))
  have hData : PowerCompData o e M (powerMarked M e) :=
    ⟨⟨k,k,e,he,hM,hPower,RestrictEquiv.refl hPower.isWellFormed.isCoherent⟩,
      rfl,hn,ho,he,hb,hbP⟩
  have hWF := companion_wf hM hn ho
  have hWFP := companion_wf hPower hn heo
  exact LocEquiv.of_isLocStable (isLocStable_powerCompRel o e) rfl
    ⟨M,powerMarked M e,hData,RestrictEquiv.refl hWF.isCoherent,
      RestrictEquiv.refl hWFP.isCoherent,hWF.isCoherent,hWFP.isCoherent⟩

/-- On the genuine common companion mask at any original controlled stage,
the original companion and the recoded original companion have the same
controlled tests. The powered stage is the actual transformed source power. -/
theorem masked_companion_local_original_power_history {n : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) :
    let W := ordMask (geoTransformAlong M T) o
    LocWPEquiv
      (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)) o)
      (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
        (geoTransformAlong (powerMarked M e) T)) (e * o)) := by
  let A := geoTransformAlong M T
  let B := geoTransformAlong (powerMarked M e) T
  let W := ordMask A o
  have hA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  obtain ⟨hTP, hEq⟩ := original_power_transform M hM e he T hT
  have hB := InvDomainTowerAlong.isInvDomain_geoTransformAlong (powerMarked_isInvDomain M hM he) T hTP
  have hPA := InvDomainTowerAlong.isInvDomain_pullback_val W hA
  have hbound : ∀ x ∈ (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) A).cosupp,
      x ∉ ordGe (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) A) (o + 1) := by
    intro x _ hx
    exact notMem_ordGe_of_mem_ordMask x.2
      ((mem_ordGe_pullback_val_iff hn hA.isWellFormed hA.isNonzeroAlongAt W (o + 1) x).mp hx)
  have hBase := locWPEquiv_companionOf_powerMarked hn (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) A)
    hPA he ho hbound
  have hPow := powerMarked_isInvDomain A hA he
  have hRE := ContactRepresentative.restrictEquiv_pullback_val W hEq hB.isWellFormed.isCoherent
    hPow.isWellFormed.isCoherent
  have hPullPow := HironakaG11PresClassTransport.pullback_powerMarked
    (M := Y) (M' := CMfd.of (n := n) W) contMDiff_subtype_val A hA.isWellFormed.isCoherent e
  rw [hPullPow] at hRE
  have hClosed : IsClosed (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) B).N :=
    hB.isWellFormed.isClosedSubmanifold_N.1.preimage continuous_subtype_val
  have hComp := companionOf_congr hRE hClosed (e * o)
  change LocWPEquiv (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) A) o)
    (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) B) (e * o))
  rw [hComp]
  exact hBase

end
end Hironaka.HironakaG8PowerCompanionLocal
