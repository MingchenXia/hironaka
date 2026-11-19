import Hironaka.Resolution.HironakaG8ProjEquiv
import Hironaka.Resolution.HironakaG8SpecialLoci
import Hironaka.Resolution.HironakaG8P1ArcTower
import Hironaka.Resolution.HironakaG8LocalHistory
import Hironaka.Resolution.HironakaG8LocalCompanion

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Boundary exponents along towers for carriers of equal dimension (G8 lane, run 0080, round 5; (B') port P6)

Blueprint: `hironaka-g8-resume-born-exponents.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2 (P6:
"born exponents are history-determined ... with P1 for the orders along centres on carriers of equal dimension").

Along a common multiple test blow-up every member of the boundary that was not there initially is born at a step, with
exponent `divExpAlong(𝔞_T, C) − d` (`HironakaActualPolymorphicBornExponent.original_history_born_exponent`), and old
members keep their exponents on their strict transforms.  G8 r2/r3 proved that the exponents of `A_T` and `B_T` agree
for equivalent `A`, `B` with the SAME carrier (`HironakaG8ProjEquiv.expAgree_geoTransformAlong_of_ordAgree`).  Lane
G8B's port P1 (`HironakaG8P1ArcTower.normalized_order_eq_of_projected_wEquiv`, BM08 Theorem 6.1 for different
carriers of equal dimension) gives the orders on the cosupport for different carriers, so the same argument runs for
carriers of equal dimension:

* **`projEquiv_towerOrdAgree_of_sameCarrierDim`**: `A ≈ B` (`ProjEquiv`, native domain, same mark, carriers of the same
  dimension on the cosupport) have equal ordinary orders on the cosupport along every common test tower;
* `divExpAlong_centre_eq_of_ordAgree'`: exponents along an admissible centre (carriers may differ: the centre lies in
  the cosupport, hence in both carriers);
* **`expAgree_geoTransformAlong_of_ordAgree'`**, **`projEquiv_expAgree_geoTransformAlong_of_sameCarrierDim`**,
  **`locWPEquiv_expAgree_geoTransformAlong`**: if the initial exponents agree (e.g. `E = []`), the boundary exponents of
  `A_T` and `B_T` agree at every cosupport point along every common test tower (born members: history-determined);
* **`locWPEquiv_stage_restrict_of_sameCarrierDim`**: the class data restrict to every open subset of every common test
  stage (the different-carrier form of `HironakaG8LocalCompanion.locWPEquiv_stage_restrict`).

Sorry-free.  Universe `0` (the old-member exponent transport and `ProjEquiv`'s entries are stated there).  Import
discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8BornExponents

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal GermIdealOrder RelativePrincipalizationSpan DivisorExponentAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.BlowupStrictSubmanifold (geoStrictTransform geoStrictTransform_subset_preimage)
open Hironaka.HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder
  ordinaryTraceOrder_cosupport_iff)
open Hironaka.HironakaActualMixedTestPowerNormalization
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.HironakaG8MixedEquiv
open Hironaka.HironakaG8MixedBoundaryExponents
open Hironaka.HironakaG8ProjEquiv
open Hironaka.HironakaG11InvBMClass (SameCarrierDim)

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n} {kA kB : ℕ} {A B : MarkedIdeal n X}

/-- **Equal orders along towers for carriers of equal dimension** (BM08 Theorem 6.1 at every stage, lane G8B's P1):
same-mark `s(i,ii)`-equivalent marked ideals of the native domain whose carriers have the same dimension on the
cosupport have equal ordinary orders on the cosupport along every common test tower. -/
theorem projEquiv_towerOrdAgree_of_sameCarrierDim (h : ProjEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hdim : SameCarrierDim A B) (hd : B.d = A.d) : TowerOrdAgree A B := by
  intro Y T hT y hy
  have hW := h.wEquiv
  have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hT
  have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (hW.2 T).2 hT
  have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT
  have hdB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T hTB
  -- the projection tests of the stages are Włodarczyk-equivalent
  have rA := record_towerHistory_refl A T
  have rB : record (withBoundary B A.E) (towerHistory (.refl : History X A.E X A.E) T) = geoTransformAlong B T :=
    (record_towerHistory_refl (withBoundary B A.E) T).trans
      (congrArg (fun M => geoTransformAlong M T) (withBoundary_eq h.E_eq))
  have hH : IsTest A (towerHistory (.refl : History X A.E X A.E) T) := (isTest_towerHistory_refl_iff A T).mpr hT
  have hPT := h.record (towerHistory .refl T) hH (noExc_towerHistory .refl noExc_refl T)
  rw [rA, rB] at hPT
  have hdimT := HironakaG8SpecialLoci.sameCarrierDim_geoTransformAlong hA.isWellFormed hB.isWellFormed hW hdim T hT
  have h1 := HironakaG8P1ArcTower.normalized_order_eq_of_projected_wEquiv (geoTransformAlong A T)
    (geoTransformAlong B T) hdA hdB y hy (hcos ▸ hy) hPT.projectionTest_wEquiv hdimT
  rw [d_geoTransformAlong, d_geoTransformAlong, hd] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.lt_of_lt_of_le Nat.zero_lt_one hA.one_le_d) h1

/-- **Exponents along an admissible centre, from equal orders** (carriers may differ). -/
theorem divExpAlong_centre_eq_of_ordAgree' (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    {C : Set Y} (hC : (geoTransformAlong A T).IsAdmissibleCentre C) (x : Y) :
    divExpAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal C x =
      divExpAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal C x := by
  have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hT
  have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (hW.2 T).2 hT
  have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT
  have hdB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T hTB
  have iffA := fun {z : Y} (hz : z ∈ (geoTransformAlong A T).N) (e : ℕ) =>
    ordinaryTraceOrder_cosupport_iff hdA.isWellFormed.isClosedSubmanifold_N hdA.isWellFormed.isCoherent
      hdA.isNonzeroAlongAt hz e
  have iffB := fun {z : Y} (hz : z ∈ (geoTransformAlong B T).N) (e : ℕ) =>
    ordinaryTraceOrder_cosupport_iff hdB.isWellFormed.isClosedSubmanifold_N hdB.isWellFormed.isCoherent
      hdB.isNonzeroAlongAt hz e
  have hCA : ∀ {z : Y}, z ∈ C → z ∈ (geoTransformAlong A T).N := fun hz =>
    (geoTransformAlong A T).cosupp_subset_N (hC.2.1 hz)
  have hCB : ∀ {z : Y}, z ∈ C → z ∈ (geoTransformAlong B T).N := fun hz =>
    (geoTransformAlong B T).cosupp_subset_N (hcos ▸ hC.2.1 hz)
  refine divExpAlong_congr fun e => ?_
  unfold IsDivNearAlong
  refine eventually_congr (Eventually.of_forall fun z => ?_)
  constructor
  · intro hz hzB hzC
    have hzA : z ∈ (geoTransformAlong A T).N := hCA hzC
    have ho := hOrd T hT z (hC.2.1 hzC)
    exact (iffB hzB e).mpr (ho ▸ (iffA hzA e).mp (hz hzA hzC))
  · intro hz hzA hzC
    have hzB : z ∈ (geoTransformAlong B T).N := hCB hzC
    have ho := hOrd T hT z (hC.2.1 hzC)
    exact (iffA hzA e).mpr (ho.symm ▸ (iffB hzB e).mp (hz hzB hzC))

/-- **Boundary exponents along common test towers, from equal orders** (carriers may differ; initial exponents
agreeing): born members by the born-exponent formula and `divExpAlong_centre_eq_of_ordAgree'`, old members by the
exponent transport on strict transforms. -/
theorem expAgree_geoTransformAlong_of_ordAgree' (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hd : B.d = A.d) (h0 : ExpAgree A B) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower A T →
      ExpAgree (geoTransformAlong A T) (geoTransformAlong B T)
  | _, .refl, _ => h0
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff A T C π hπ).mp hT
    have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hTT
    have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (hW.2 T).2 hTT
    have hcos' : (geoTransformAlong A (.step T C π hπ)).cosupp = (geoTransformAlong B (.step T C π hπ)).cosupp :=
      (hW.2 (.step T C π hπ)).2 hT
    have hET : (geoTransformAlong B T).E = (geoTransformAlong A T).E :=
      MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hW.1.symm T
    have hCB : (geoTransformAlong B T).IsAdmissibleCentre C :=
      (isAdmissibleCentre_congr hET.symm hcos C).mp hC
    have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hTT
    have ih := expAgree_geoTransformAlong_of_ordAgree' hW hOrd hA hB hd h0 T hTT
    intro H hH z hz hzH
    have hzN : z ∈ ((geoTransformAlong A T).geoTransform C π).N :=
      ((geoTransformAlong A T).geoTransform C π).cosupp_subset_N hz
    have hzNB : z ∈ ((geoTransformAlong B T).geoTransform C π).N :=
      ((geoTransformAlong B T).geoTransform C π).cosupp_subset_N (hcos' ▸ hz)
    have hpz : π z ∈ (geoTransformAlong A T).cosupp :=
      CompanionReductionAlong.mem_cosupp_of_mem_cosupp_geoTransform_along hdA.isWellFormed.isClosedSubmanifold_N.1
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hdA.isWellFormed.isCoherent hg) hC hπ hz
    change H ∈ (geoTransformAlong A T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C] at hH
    rcases List.mem_append.mp hH with hold | hborn
    · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hold
      obtain ⟨i, hi⟩ := List.get_of_mem hH₀
      obtain ⟨j, hj⟩ := List.get_of_mem (hET.symm ▸ hH₀ : H₀ ∈ (geoTransformAlong B T).E)
      have hzi : z ∈ geoStrictTransform π C ((geoTransformAlong A T).E.get i) := by rw [hi]; exact hzH
      have hzj : z ∈ geoStrictTransform π C ((geoTransformAlong B T).E.get j) := by rw [hj]; exact hzH
      have eA := HironakaActualOldDivisorExponentTransport.original_history_old_exponent A hA T hTT hC hπ i hzN hzi
      have eB := HironakaActualOldDivisorExponentTransport.original_history_old_exponent B hB T hTB hCB hπ j hzNB hzj
      rw [hi] at eA
      rw [hj] at eB
      have hH₀c : IsClosed H₀ := hdA.isWellFormed.isSNCDivisor.1 H₀ hH₀
      have hpzH : π z ∈ H₀ := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hH₀c hzH
      show divExpAlong n ((geoTransformAlong A T).geoTransform C π).N ((geoTransformAlong A T).geoTransform C π).ideal
          (geoStrictTransform π C H₀) z =
        divExpAlong n ((geoTransformAlong B T).geoTransform C π).N ((geoTransformAlong B T).geoTransform C π).ideal
          (geoStrictTransform π C H₀) z
      rw [eA, eB]
      exact ih H₀ hH₀ (π z) hpz hpzH
    · rw [List.mem_singleton] at hborn
      subst hborn
      have bA := (HironakaActualPolymorphicBornExponent.original_history_born_exponent A hA T hTT hC hπ hzN hzH).2
      have bB := (HironakaActualPolymorphicBornExponent.original_history_born_exponent B hB T hTB hCB hπ hzNB hzH).2
      show divExpAlong n ((geoTransformAlong A T).geoTransform C π).N ((geoTransformAlong A T).geoTransform C π).ideal
          (π ⁻¹' C) z =
        divExpAlong n ((geoTransformAlong B T).geoTransform C π).N ((geoTransformAlong B T).geoTransform C π).ideal
          (π ⁻¹' C) z
      rw [bA, bB, divExpAlong_centre_eq_of_ordAgree' hW hOrd hA hB T hTT hC (π z), hd]

/-- **P6: boundary exponents are history-determined for carriers of equal dimension**: for `A ≈ B` (`ProjEquiv`) in
the native domain with the same mark, carriers of the same dimension on the cosupport and agreeing initial exponents
(e.g. `E = []`), the boundary exponents of `A_T` and `B_T` agree at every cosupport point along every common test
tower. -/
theorem projEquiv_expAgree_geoTransformAlong_of_sameCarrierDim (h : ProjEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) :
    ExpAgree (geoTransformAlong A T) (geoTransformAlong B T) :=
  expAgree_geoTransformAlong_of_ordAgree' h.wEquiv (projEquiv_towerOrdAgree_of_sameCarrierDim h hA hB hdim hd) hA hB
    hd h0 T hT

/-- **The `LocWPEquiv` form** (the relation of G11B's class functoriality). -/
theorem locWPEquiv_expAgree_geoTransformAlong (h : HironakaG8LocalHistory.LocWPEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) :
    ExpAgree (geoTransformAlong A T) (geoTransformAlong B T) :=
  projEquiv_expAgree_geoTransformAlong_of_sameCarrierDim h.projEquiv hA hB hdim hd h0 T hT

/-- **The class data restrict to every open subset of every common test stage** (carriers of equal dimension; the
different-carrier form of `HironakaG8LocalCompanion.locWPEquiv_stage_restrict`): `P = (A_{T₀})|_W` and
`Q = (B_{T₀})|_W` are `LocWPEquiv`, in the native domain, with carriers of the same dimension on the cosupport, the same
mark and agreeing boundary exponents. -/
theorem locWPEquiv_stage_restrict_of_sameCarrierDim (h : HironakaG8LocalHistory.LocWPEquiv A B)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B)
    {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower A T₀) (W : TopologicalSpace.Opens Y₀) :
    HironakaG8LocalHistory.LocWPEquiv (X := CMfd.of (n := n) W)
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀))
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) ∧
      IsInvDomain kA (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)) ∧
      IsInvDomain kB (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) ∧
      SameCarrierDim (X := CMfd.of (n := n) W)
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀))
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) ∧
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)).d =
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀)).d ∧
      ExpAgree (Y := CMfd.of (n := n) W)
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong A T₀))
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong B T₀)) := by
  have hP := h.projEquiv
  have hTB : IsGeoTestTower B T₀ := (hP.wEquiv.2 T₀).1.mp hT₀
  have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T₀ hT₀
  have hdB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T₀ hTB
  have hexp := projEquiv_expAgree_geoTransformAlong_of_sameCarrierDim hP hA hB hdim hd h0 T₀ hT₀
  have hdimT := HironakaG8SpecialLoci.sameCarrierDim_geoTransformAlong hA.isWellFormed hB.isWellFormed hP.wEquiv hdim
    T₀ hT₀
  have hholA : ∀ x g, (geoTransformAlong A T₀).ideal.mem x g → HolomorphicAt n g x :=
    fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hdA.isWellFormed.isCoherent hg
  refine ⟨(h.geoTransformAlong T₀ hT₀).restrict W, InvDomainTowerAlong.isInvDomain_pullback_val W hdA,
    InvDomainTowerAlong.isInvDomain_pullback_val W hdB,
    HironakaG8SpecialLoci.sameCarrierDim_pullback_val hholA hdimT W, ?_, ?_⟩
  · show (geoTransformAlong B T₀).d = (geoTransformAlong A T₀).d
    rw [d_geoTransformAlong, d_geoTransformAlong, hd]
  · exact HironakaG8LocalCompanion.expAgree_pullback_val hholA
      (fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hdB.isWellFormed.isCoherent hg) hexp W

end

end Hironaka.HironakaG8BornExponents
