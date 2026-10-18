/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteFullCutSmoothHistory
import Hironaka.Invariant.GeneralRepresentative
import Hironaka.Invariant.ContactEmptyPrefix
/-! Actual relative ideal equivalence transports genuine original full-cut
histories; real empty-prefix contact geometry supplies that equivalence internally. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFullCutEmptyPrefixContact
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CanonicalCentres GeneralRepresentative GeneralValue InvDomainRebase MarkedIdealRestrictOpen
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction
  ContactStageKept ContactEmptyPrefix TangentDirectionAlong
  HironakaOriginalFiniteFullCutSmoothHistory HironakaOriginalFiniteOrderCutCompanionTests
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)
variable {n : ℕ} {X A B Y : CMfd.{u} n}

/-- Original relative equivalence gives literal ALL-depth values on EVERY
actual history, without canonicality, TEST or point membership. -/
theorem full_values_of_restrictEquiv (hn : 0<n) (M N : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hN : N.ideal.IsCoherent) (hEq : RestrictEquiv M N)
    (q : ℕ) (T : BlowupTower X Y) (y : Y) :
    (invFamily hn q).inv M T y=(invFamily hn q).inv N T y := by
  cases q with
  | zero => rfl
  | succ q =>
    exact genInv_congr
      (fun {V} J {Z} S z => Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) (X := V) J (Y := Z) S z)
      hEq hM.isClosedSubmanifold_N.1 hM.isCoherent hN T y

private theorem actual_source_full_cut (hn : 0<n) (d : ℕ) (M N : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hN : N.ideal.IsCoherent) (hEq : RestrictEquiv M N)
    (T : BlowupTower X Y) (hT : IsFullCutTower hn d M T) :
    IsFullCutTower hn d N T := by
  have hW := RestrictEquiv.wEquiv hEq hM.isClosedSubmanifold_N.1 hM.isCoherent hN
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    have hTest := orderCutTower_geoTest M (.step T C π hπ)
      (fullCutTower_orderCut hn d M _ hT)
    have hSource := ((hW.2 (.step T C π hπ)).1).mp hTest
    refine ⟨ih hT.1,hSource.2,?_⟩
    intro y hy c hc
    have hCos := (hW.2 T).2 hTest.1
    rw [←hCos] at hy
    rw [←full_values_of_restrictEquiv hn M N hM hN hEq (d+2) T y,
      ←full_values_of_restrictEquiv hn M N hM hN hEq (d+2) T c]
    exact hT.2.2 y hy c hc

/-- True source DOMAIN and entire original cut history are constructed,
not assumed, before the whole TEST/cosupport and all-values dictionary. -/
theorem full_cut_reference_transport (hn : 0<n) (b d : ℕ) (M N : MarkedIdeal n X)
    (hM : IsInvDomain b M) (hN : N.ideal.IsCoherent) (hEq : RestrictEquiv M N)
    (T : BlowupTower X Y) (hT : IsFullCutTower hn d M T) :
    IsInvDomain b N ∧ IsFullCutTower hn d N T ∧ IsGeoTestTower N T ∧
      (geoTransformAlong M T).cosupp=(geoTransformAlong N T).cosupp ∧
      ∀ (q : ℕ) (y : Y),(invFamily hn q).inv M T y=(invFamily hn q).inv N T y := by
  have hTest := orderCutTower_geoTest M T (fullCutTower_orderCut hn d M T hT)
  have hW := RestrictEquiv.wEquiv hEq hM.isWellFormed.isClosedSubmanifold_N.1
    hM.isWellFormed.isCoherent hN
  exact ⟨isInvDomain_of_restrictEquiv hM hEq hN,
    actual_source_full_cut hn d M N hM.isWellFormed hN hEq T hT,
    ((hW.2 T).1).mp hTest,(hW.2 T).2 hTest,
    fun q y => full_values_of_restrictEquiv hn M N hM.isWellFormed hN hEq q T y⟩

/-- Actual original empty-prefix contact geometry internally supplies the
changed reference before EVERY future genuine full-cut comparison. -/
theorem contact_empty_prefix_head_transport (hn : 0<n) (b : ℕ)
    (J : MarkedIdeal n X) (hJ : J.IsWellFormed) (hd : 1≤J.d)
    (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong J.N J.ideal J.d U u)
    (P : BlowupTower X A) (hP : IsEmptyTower P) (H : BlowupTower A B)
    (hHead : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong J)) (P.append H))
    (W : Opens B) (hWU : (W : Set B)⊆openPreimage (P.append H) U)
    (hDom : IsInvDomain b (contactMarkedKept J u (P.append H) W)) :
    let M := contactMarkedKept J u (P.append H) W
    let N := contactMarkedKept (geoTransformAlong J P) (u ∘ P.proj) H W
    IsInvDomain b N ∧ ∀ {Z : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) W) Z) (d : ℕ),
      IsFullCutTower hn d M T → IsFullCutTower hn d N T ∧ IsGeoTestTower N T ∧
        (geoTransformAlong M T).cosupp=(geoTransformAlong N T).cosupp ∧
        ∀ (q : ℕ) (z : Z),(invFamily hn q).inv M T z=(invFamily hn q).inv N T z := by
  have hEq := restrictEquiv_symm (restrictEquiv_contactMarkedKept_emptyPrefix J
    hJ.isClosedSubmanifold_N hJ.isCoherent hd U hu P hP H hHead W hWU)
  have hPt : IsGeoTestTower J P := isGeoTestTower_of_isEmptyTower J P hP
  obtain ⟨hNP,hcP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    hJ.isClosedSubmanifold_N hJ.isCoherent P hPt
  have hHead' : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong (geoTransformAlong J P))) H :=
    (isGeoTestTower_barMarked_geoTransformAlong_iff J hJ.isClosedSubmanifold_N
      hJ.isCoherent hd P hP H).mpr hHead
  have hCoherent : (contactMarkedKept (geoTransformAlong J P) (u ∘ P.proj) H W).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff (geoTransformAlong J P) hcP hNP (u ∘ P.proj) H hHead')
  refine ⟨isInvDomain_of_restrictEquiv hDom hEq hCoherent,?_⟩
  intro Z T d hT
  exact (full_cut_reference_transport hn b d _ _ hDom hCoherent hEq T hT).2

end
end Hironaka.HironakaOriginalFullCutEmptyPrefixContact
