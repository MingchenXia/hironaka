/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaGeneralTwoCompanionCurveLoci
import Hironaka.Analytic.ClosureDifferenceAnalytic

/-!
# Whole analytic superlevels of the actual constructed dimension-two invariant

The actual finite history, genuine entire coherent companions and locally finite
actual global components internally produce the component dictionary and its
zero-dimensional analytic exception. The final theorem concerns every literal
threshold of `invFamily hn 2` on the entire current cosupport along an actual
canonical tower. Higher dimensions and the noncompact global sequence remain open.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaGeneralTwoAnalyticSuperlevels

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GlobalComponents HironakaCurveAnalyticPredicates HironakaDimensionTwoStepOneAnalyticSuperlevels
  HironakaOneDimensionalCanonicalSuperlevels HironakaGeneralTwoCompanionCurveLoci
  ClosureDifferenceAnalytic AnalyticDimensionBasics

open Hironaka
noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem closure_diff_eq_globalComponent_of_not_subset {A B Z : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hB : B ∈ globalComponents (n := n) A)
    (hZ : IsComplexAnalyticSubset (n := n) Z) (hnot : ¬ B ⊆ Z) : closure (B \ Z) = B := by
  have hBi := isComplexAnalyticallyIrreducible_of_mem_globalComponents hA hB
  have hC := isComplexAnalyticSubset_closure_diff hBi.1 hZ
  have hCB : closure (B \ Z) ⊆ B := closure_minimal sdiff_subset hBi.1.isClosed
  have heq : B = (B ∩ Z) ∪ closure (B \ Z) := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxZ : x ∈ Z
      · exact Or.inl ⟨hx, hxZ⟩
      · exact Or.inr (subset_closure ⟨hx, hxZ⟩)
    · exact union_subset inter_subset_left hCB
  rcases hBi.eq_left_or_eq_right (hBi.1.inter hZ) hC inter_subset_left hCB heq with h | h
  · exact False.elim (hnot (fun x hx => (h ▸ hx : x ∈ B ∩ Z).2))
  · exact h.symm

theorem eq_selected_globalComponents_union_exception {A L Z : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hL : IsClosed L) (hLA : L ⊆ A)
    (hZ : IsComplexAnalyticSubset (n := n) Z)
    (hcomp : ∀ B ∈ globalComponents (n := n) A, ∀ x ∈ B \ Z, ∀ y ∈ B \ Z,
      x ∈ L ↔ y ∈ L) :
    L = (⋃₀ {B | B ∈ globalComponents (n := n) A ∧ B ⊆ L}) ∪ (L ∩ Z) := by
  apply Subset.antisymm
  · intro x hx
    by_cases hxZ : x ∈ Z
    · exact Or.inr ⟨hx, hxZ⟩
    · have hxU : x ∈ ⋃₀ globalComponents (n := n) A := by
        rw [sUnion_globalComponents hA]
        exact hLA hx
      obtain ⟨B, hB, hxB⟩ := hxU
      have hsub : B \ Z ⊆ L := fun y hy => (hcomp B hB x ⟨hxB, hxZ⟩ y hy).mp hx
      have hnot : ¬ B ⊆ Z := fun hb => hxZ (hb hxB)
      have hBL : B ⊆ L := by
        rw [← closure_diff_eq_globalComponent_of_not_subset hA hB hZ hnot]
        exact closure_minimal hsub hL
      exact Or.inl ⟨B, ⟨hB, hBL⟩, hxB⟩
  · rintro x (⟨B, ⟨_, hBL⟩, hxB⟩ | ⟨hxL, _⟩)
    · exact hBL hxB
    · exact hxL

theorem isComplexAnalyticSubset_of_component_dictionary {A L Z : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hL : IsClosed L) (hLA : L ⊆ A)
    (hZ : IsComplexAnalyticSubset (n := n) Z) (hdZ : DimLE (n := n) Z 0)
    (hcomp : ∀ B ∈ globalComponents (n := n) A, ∀ x ∈ B \ Z, ∀ y ∈ B \ Z,
      x ∈ L ↔ y ∈ L) : IsComplexAnalyticSubset (n := n) L := by
  classical
  let S := {B : Set M // B ∈ globalComponents (n := n) A ∧ B ⊆ L}
  let f : S → globalComponents (n := n) A := fun B => ⟨B.1, B.2.1⟩
  have hf : Function.Injective f := by
    intro B C h
    exact Subtype.ext (congrArg (fun D : globalComponents (n := n) A => D.1) h)
  have hlf := (locallyFinite_globalComponents hA).comp_injective hf
  have hsel := isComplexAnalyticSubset_iUnion_of_locallyFinite (fun B : S => B.1) hlf
    (fun B => (isComplexAnalyticallyIrreducible_of_mem_globalComponents hA B.2.1).1)
  have heq : (⋃ B : S, B.1) = ⋃₀ {B | B ∈ globalComponents (n := n) A ∧ B ⊆ L} := by
    ext x
    constructor
    · intro hx
      obtain ⟨B, hxB⟩ := mem_iUnion.mp hx
      exact ⟨B.1, B.2, hxB⟩
    · rintro ⟨B, hB, hxB⟩
      exact mem_iUnion.mpr ⟨⟨B, hB⟩, hxB⟩
  rw [heq] at hsel
  have hrem : IsComplexAnalyticSubset (n := n) (L ∩ Z) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (isClosedSubmanifold_subset_of_analytic_dimLE_zero hZ hdZ inter_subset_right)
  rw [eq_selected_globalComponents_union_exception hA hL hLA hZ hcomp]
  exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union hsel hrem

section ActualGeneral

universe u
open BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  CodimOneSupportAlong HomogenizedIdealAlong NonmonomialOrderLocal NonmonomialOrderRegime
  CanonicalCentres StepOneValue CompanionRebase GeneralValue HironakaOrderTupleAnalyticSuperlevels
  BoundaryCount NormalCrossings MemberInterLocusAlong StepOneRegime DivisorExponentAlong

variable {X Y : CMfd.{u} n}

theorem exists_analytic_dimzero_positive_history_exception (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (q : ℕ) (hq : 1 ≤ q) :
    ∃ Z : Set Y, IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 0 ∧
      (∀ B ∈ globalComponents (n := n) (geoTransformAlong m T).cosupp,
        ∀ x ∈ B \ Z, ∀ y ∈ B \ Z, ∀ b : Fin 2,
          (q + b ≤ nmOrd (geoTransformAlong m T) x ↔ q + b ≤ nmOrd (geoTransformAlong m T) y)) ∧
      (∀ B ∈ globalComponents (n := n) (geoTransformAlong m T).cosupp,
        ∀ x ∈ B \ Z, ∀ y ∈ B \ Z,
          regimeRun (OrdRegime m q) T x = regimeRun (OrdRegime m q) T y) ∧
      (∀ B ∈ globalComponents (n := n) (geoTransformAlong m T).cosupp,
        ∀ x ∈ B \ Z, ∀ y ∈ B \ Z, ∀ W ∈ (geoTransformAlong m T).E,
          (x ∈ W ↔ y ∈ W)) ∧
      ∀ r : Fin (T.length + 1),
        ∀ p : openPreimage (tail T r) (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q),
          p ∈ (geoTransformAlong (barMarked (compAt m q (head T r)))
            (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) (tail T r))).cosupp →
          ¬ IsSpecial (compAt m q (head T r))
            (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) (tail T r)) p →
          (p : Y) ∈ Z := by
  classical
  let J := geoTransformAlong m T
  have hJ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hA : IsComplexAnalyticSubset (n := n) J.cosupp := isComplexAnalyticSubset_cosupport_along
    hJ.isWellFormed.isCoherent hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d
  have hdim : DimLE (n := n) J.cosupp 1 := dimLE_cosupport_of_isInvDomain hJ
  let P : Fin 2 → Set Y := fun b => {y | y ∈ J.cosupp ∧ q + b ≤ nmOrd J y}
  have hP : ∀ b, IsComplexAnalyticSubset (n := n) (P b) := by
    intro b
    have hord := isComplexAnalyticSubset_canonical_first_superlevel hn m h T hT (q + b)
    have heq : P b = J.cosupp ∩ {y | y ∈ J.N ∧ q + b ≤ nmOrd J y} := by
      ext y
      exact ⟨fun hy => ⟨hy.1, J.cosupp_subset_N hy.1, hy.2⟩, fun hy => ⟨hy.1, hy.2.2⟩⟩
    rw [heq]
    exact hA.inter hord
  obtain ⟨Zo, hZo, hdZo, _, horder⟩ := exists_analytic_dimzero_predicate_exception hA hdim P hP
  have hE : ∀ i : Fin J.E.length, IsComplexAnalyticSubset (n := n) (J.E.get i) := by
    intro i
    have hH := isClosedSubmanifold_memberInter hn hJ.isWellFormed.isSNCDivisor {i}
    rw [memberInter_singleton] at hH
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hH
  obtain ⟨Zb, hZb, hdZb, _, hboundary⟩ := exists_analytic_dimzero_predicate_exception hA hdim J.E.get hE
  obtain ⟨Zh, hZh, hdZh, _, _, hrun⟩ := exists_analytic_dimzero_history_regime_exception hn m h T hT q
  have hc : ∀ r : Fin (T.length + 1), ∃ Zr : Set Y,
      IsComplexAnalyticSubset (n := n) Zr ∧ DimLE (n := n) Zr 0 ∧
      Zr ⊆ (geoTransformAlong (barMarked (companionOf n (geoTransformAlong m (head T r)) q)) (tail T r)).cosupp ∧
      ∀ p : openPreimage (tail T r) (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q),
        p ∈ (geoTransformAlong (barMarked (compAt m q (head T r)))
          (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) (tail T r))).cosupp →
        ¬ IsSpecial (compAt m q (head T r))
          (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) (tail T r)) p → (p : Y) ∈ Zr := by
    intro r
    obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail m T r).mp hT
    exact exists_analytic_dimzero_literal_companion_exception hn m h q hq (head T r) hhead (tail T r) htail
  choose Zr hZr hdZr _ hspecial using hc
  let Zc := ⋃ r ∈ (Finset.univ : Finset (Fin (T.length + 1))), Zr r
  obtain ⟨hZc, hdZc⟩ := analytic_dimzero_finset_union Finset.univ Zr
    (fun r _ => hZr r) (fun r _ => hdZr r)
  obtain ⟨hZob, hdZob⟩ := analytic_dimzero_union hZo hdZo hZb hdZb
  obtain ⟨hZobh, hdZobh⟩ := analytic_dimzero_union hZob hdZob hZh hdZh
  obtain ⟨hZ, hdZ⟩ := analytic_dimzero_union hZobh hdZobh hZc hdZc
  let Z := ((Zo ∪ Zb) ∪ Zh) ∪ Zc
  have hnotO : ∀ x ∉ Z, x ∉ Zo := fun _ hx hz => hx (Or.inl (Or.inl (Or.inl hz)))
  have hnotB : ∀ x ∉ Z, x ∉ Zb := fun _ hx hz => hx (Or.inl (Or.inl (Or.inr hz)))
  have hnotH : ∀ x ∉ Z, x ∉ Zh := fun _ hx hz => hx (Or.inl (Or.inr hz))
  refine ⟨Z, hZ, hdZ, ?_, ?_, ?_, ?_⟩
  · intro B hB x hx y hy b
    have hxA := subset_of_mem_globalComponents hA hB hx.1
    have hyA := subset_of_mem_globalComponents hA hB hy.1
    have hdict := (horder B hB x ⟨hx.1, hnotO x hx.2⟩ b).trans
      (horder B hB y ⟨hy.1, hnotO y hy.2⟩ b).symm
    exact (and_iff_right hxA).symm.trans (hdict.trans (and_iff_right hyA))
  · intro B hB x hx y hy
    exact hrun B hB x ⟨hx.1, hnotH x hx.2⟩ y ⟨hy.1, hnotH y hy.2⟩
  · intro B hB x hx y hy W hW
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hW
    exact (hboundary B hB x ⟨hx.1, hnotB x hx.2⟩ i).trans
      (hboundary B hB y ⟨hy.1, hnotB y hy.2⟩ i).symm
  · intro r p hp hnot
    exact Or.inr (mem_iUnion₂.mpr ⟨r, Finset.mem_univ r, hspecial r p hp hnot⟩)

private theorem level_literal_companion_eq_current_prefix (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (q : ℕ) (hq : 1 ≤ q) (r : ℕ)
    (p : openPreimage (tail T r) (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q)) :
    level (compAt m q (head T r))
      (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) (tail T r)) p =
      boundaryCount ((geoTransformAlong m T).E.take (geoTransformAlong m (head T r)).E.length) (p : Y) := by
  let W := NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q
  let K := companionOf n (geoTransformAlong m (head T r)) q
  let V := openPreimage (tail T r) W
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail m T r).mp hT
  have hd₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (head T r) hhead
  have hinit : compAt m q (head T r) = MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : W → (split T r).1) K :=
    (pullback_val_companionOf hn hd₀.isWellFormed hd₀.isNonzeroAlongAt _ q).symm
  have hKE : K.E = (geoTransformAlong m (head T r)).E := by
    simp only [K, companionOf, CompanionReductionAlong.companionAlong_E]
  have hlen : (compAt m q (head T r)).E.length = (geoTransformAlong m (head T r)).E.length := by
    rw [hinit]
    change (K.E.map _).length = _
    rw [List.length_map, hKE]
  have hbarE : (barMarked K).E = (geoTransformAlong m (head T r)).E :=
    hKE
  have hTE : (geoTransformAlong (barMarked K) (tail T r)).E = (geoTransformAlong m T).E := by
    rw [HironakaCoherentTransformExtension.geoTransformAlong_E_eq_of_E_eq hbarE]
    rw [← geoTransformAlong_head_tail m T r]
  have hid := (HironakaCoherentTransformExtension.coherent_coefficient_transform_and_mask_identity
    hn m h q hq (head T r) hhead (tail T r) htail).2
  have hF : origMembers (compAt m q (head T r)) (restrict W (tail T r)) =
      ((geoTransformAlong m T).E.take (geoTransformAlong m (head T r)).E.length).map
        ((Subtype.val : V → Y) ⁻¹' ·) := by
    unfold origMembers
    rw [hid, hlen]
    change ((geoTransformAlong (barMarked K) (tail T r)).E.map _).take _ = _
    rw [hTE, ← List.map_take]
  unfold level
  rw [hF]
  exact CodimOnePartCanonical.boundaryCount_map_preimage _ _ p

private theorem maskedStepOne_literal_companion_of_special (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (q : ℕ) (hq : 1 ≤ q) (r : ℕ)
    (p : openPreimage (tail T r) (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q))
    (hsp : IsSpecial (compAt m q (head T r))
      (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) (tail T r)) p) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) (compAt m q (head T r))
      (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) (tail T r)) p =
        toLex (boundaryCount ((geoTransformAlong m T).E.take (geoTransformAlong m (head T r)).E.length) (p : Y),
          (⊤ : WithTop (ValTy 1))) := by
  exact (Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (invFamily hn 1) _ _ _ hsp).trans
    (congrArg (fun a : ℕ => toLex (a, (⊤ : WithTop (ValTy 1))))
      (level_literal_companion_eq_current_prefix hn m h T hT q hq r p))

private theorem value_eq_generic_positive_of_avoids_exception (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T)
    (hcan : ResolutionInvariantSpec.IsCanonical m ((invFamily hn 2).inv m) T)
    (q : ℕ) (hq : 1 ≤ q) (Z : Set Y)
    (hspecial : ∀ r : Fin (T.length + 1),
        ∀ p : openPreimage (tail T r) (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q),
          p ∈ (geoTransformAlong (barMarked (compAt m q (head T r)))
            (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) (tail T r))).cosupp →
          ¬ IsSpecial (compAt m q (head T r))
            (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) (tail T r)) p → (p : Y) ∈ Z)
    (z : Y) (hzA : z ∈ (geoTransformAlong m T).cosupp) (hzZ : z ∉ Z)
    (hzq : nmOrd (geoTransformAlong m T) z = q) :
        (invFamily hn 2).inv m T z =
          toLex (q, toLex (Sum.inr ((toLex
            (boundaryCount ((geoTransformAlong m T).E.take
              (geoTransformAlong m (head T (regimeRun (OrdRegime m q) T z))).E.length) z,
              (⊤ : WithTop (ValTy 1))) : ℕ ×ₗ WithTop (ValTy 1)) :
              WithTop (ℕ ×ₗ WithTop (ValTy 1))))) := by
  let R := invFamily hn 1
  let lower := fun {X : CMfd.{u} n} (J : MarkedIdeal n X) {Y : CMfd.{u} n}
    (S : BlowupTower X Y) (z : Y) => Seq.StepOneValueMasked.stepOneInvM R J S z
  have hM := StepOneSeq.isMaxOrderValue_stepOneInvM (k := 2) R hn
  have hcanG : ResolutionInvariantSpec.IsCanonical m (genInv lower m) T := hcan
  have hD := GeneralCanonicalTail.hasGenLowerData_of_isCanonical lower hM hn h T hT hcanG
  let r := regimeRun (OrdRegime m q) T z
  let rf : Fin (T.length + 1) := ⟨r, Nat.lt_succ_of_le (regimeRun_le_length _ T z)⟩
  obtain ⟨hmask, hK, hmax, hcanK, hcosK⟩ := hD z hzA q hzq hq
  let p : openPreimage (tail T r)
    (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) := ⟨z, hmask⟩
  have hpbar : p ∈ (geoTransformAlong (barMarked (compAt m q (head T r)))
      (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) (tail T r))).cosupp := by
    rw [(Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 2) R (compAt m q (head T r))
      hK hmax hn _ hcanK).2.2]
    exact hcosK
  have hsp : IsSpecial (compAt m q (head T r))
      (restrict (NonmonomialOrderTail.ordMask (geoTransformAlong m (head T r)) q) (tail T r)) p := by
    by_contra hnot
    exact hzZ (hspecial rf p hpbar hnot)
  have hlower := maskedStepOne_literal_companion_of_special hn m h T hT q hq r p hsp
  change genInv lower m T z = _
  rw [genInv_of_nmOrd_ne_zero lower m T hzq (by omega), genLowerValue_eq_of_mem lower m hmask]
  let embed : (ℕ ×ₗ WithTop (ValTy 1)) → ValTy 2 := fun v =>
    toLex (q, toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy 1)))))
  exact congrArg embed hlower

theorem exists_analytic_dimzero_positive_threshold_dictionary (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T)
    (hcan : ResolutionInvariantSpec.IsCanonical m ((invFamily hn 2).inv m) T)
    (q : ℕ) (hq : 1 ≤ q)
    (β : WithBot MonomialInvariant.Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy 1))) :
    ∃ Z : Set Y, IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 0 ∧
      ∀ B ∈ globalComponents (n := n) (geoTransformAlong m T).cosupp,
        ∀ x ∈ B \ Z, ∀ y ∈ B \ Z,
          (toLex (q, β) ≤ (invFamily hn 2).inv m T x ↔
            toLex (q, β) ≤ (invFamily hn 2).inv m T y) := by
  classical
  obtain ⟨Z, hZ, hdZ, horder, hrun, hboundary, hspecial⟩ :=
    exists_analytic_dimzero_positive_history_exception hn m h T hT q hq
  refine ⟨Z, hZ, hdZ, ?_⟩
  let R := invFamily hn 1
  let lower := fun {X : CMfd.{u} n} (J : MarkedIdeal n X) {Y : CMfd.{u} n}
    (S : BlowupTower X Y) (z : Y) => Seq.StepOneValueMasked.stepOneInvM R J S z
  have hJ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hA : IsComplexAnalyticSubset (n := n) (geoTransformAlong m T).cosupp :=
    isComplexAnalyticSubset_cosupport_along hJ.isWellFormed.isCoherent
      hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d
  have hv : ∀ B ∈ globalComponents (n := n) (geoTransformAlong m T).cosupp,
      ∀ z ∈ B \ Z, nmOrd (geoTransformAlong m T) z = q →
        (invFamily hn 2).inv m T z =
          toLex (q, toLex (Sum.inr ((toLex
            (boundaryCount ((geoTransformAlong m T).E.take
              (geoTransformAlong m (head T (regimeRun (OrdRegime m q) T z))).E.length) z,
              (⊤ : WithTop (ValTy 1))) : ℕ ×ₗ WithTop (ValTy 1)) :
              WithTop (ℕ ×ₗ WithTop (ValTy 1))))) := by
    intro B hB z hz hzq
    exact value_eq_generic_positive_of_avoids_exception hn m h T hT hcan q hq Z hspecial
      z (subset_of_mem_globalComponents hA hB hz.1) hz.2 hzq
  intro B hB x hx y hy
  have ho0 : q ≤ nmOrd (geoTransformAlong m T) x ↔ q ≤ nmOrd (geoTransformAlong m T) y := by
    simpa using horder B hB x hx y hy 0
  have ho1 : q + 1 ≤ nmOrd (geoTransformAlong m T) x ↔ q + 1 ≤ nmOrd (geoTransformAlong m T) y := by
    simpa using horder B hB x hx y hy 1
  by_cases hxlo : nmOrd (geoTransformAlong m T) x < q
  · have hylo : nmOrd (geoTransformAlong m T) y < q :=
      Nat.lt_of_not_ge (fun h => (not_le.mpr hxlo) (ho0.mpr h))
    have hxl : (invFamily hn 2).inv m T x < toLex (q, β) := by
      change genInv lower m T x < _
      rw [genInv, Prod.Lex.toLex_lt_toLex]
      exact Or.inl hxlo
    have hyl : (invFamily hn 2).inv m T y < toLex (q, β) := by
      change genInv lower m T y < _
      rw [genInv, Prod.Lex.toLex_lt_toLex]
      exact Or.inl hylo
    exact iff_of_false (not_le.mpr hxl) (not_le.mpr hyl)
  by_cases hxhi : q < nmOrd (geoTransformAlong m T) x
  · have hyhi : q < nmOrd (geoTransformAlong m T) y :=
      ho1.mp (Nat.succ_le_of_lt hxhi)
    have hxl : toLex (q, β) ≤ (invFamily hn 2).inv m T x := by
      change _ ≤ genInv lower m T x
      rw [genInv, Prod.Lex.toLex_le_toLex]
      exact Or.inl hxhi
    have hyl : toLex (q, β) ≤ (invFamily hn 2).inv m T y := by
      change _ ≤ genInv lower m T y
      rw [genInv, Prod.Lex.toLex_le_toLex]
      exact Or.inl hyhi
    exact iff_of_true hxl hyl
  have hxq : nmOrd (geoTransformAlong m T) x = q := by omega
  have hyq : nmOrd (geoTransformAlong m T) y = q := by
    have hyle : ¬ q + 1 ≤ nmOrd (geoTransformAlong m T) y := by
      intro h1
      have := ho1.mpr h1
      omega
    have := ho0.mp (by omega : q ≤ nmOrd (geoTransformAlong m T) x)
    omega
  have hr := hrun B hB x hx y hy
  have hc : boundaryCount ((geoTransformAlong m T).E.take
        (geoTransformAlong m (head T (regimeRun (OrdRegime m q) T x))).E.length) x =
      boundaryCount ((geoTransformAlong m T).E.take
        (geoTransformAlong m (head T (regimeRun (OrdRegime m q) T x))).E.length) y :=
    boundaryCount_eq_of_forall_iff (fun W hW => hboundary B hB x hx y hy W (List.mem_of_mem_take hW))
  rw [hv B hB x hx hxq, hv B hB y hy hyq, ← hr, hc]

theorem exists_positive_superlevel_component_decomposition (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T)
    (hcan : ResolutionInvariantSpec.IsCanonical m ((invFamily hn 2).inv m) T)
    (q : ℕ) (hq : 1 ≤ q)
    (β : WithBot MonomialInvariant.Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy 1))) :
    ∃ Z : Set Y, IsComplexAnalyticSubset (n := n) Z ∧ DimLE (n := n) Z 0 ∧
      {y | y ∈ (geoTransformAlong m T).cosupp ∧ toLex (q, β) ≤ (invFamily hn 2).inv m T y} =
        (⋃₀ {B | B ∈ globalComponents (n := n) (geoTransformAlong m T).cosupp ∧
          B ⊆ {y | y ∈ (geoTransformAlong m T).cosupp ∧ toLex (q, β) ≤ (invFamily hn 2).inv m T y}}) ∪
        ({y | y ∈ (geoTransformAlong m T).cosupp ∧ toLex (q, β) ≤ (invFamily hn 2).inv m T y} ∩ Z) := by
  obtain ⟨Z, hZ, hdZ, hdict⟩ :=
    exists_analytic_dimzero_positive_threshold_dictionary hn m h T hT hcan q hq β
  have hJ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hA := isComplexAnalyticSubset_cosupport_along hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d
  have hL := ResolutionInvariantOrder.IsInvUSCOn.isClosed_superlevel
    ((invFamily hn 2).isInvValue.usc m h T hcan) hA.isClosed (toLex (q, β))
  refine ⟨Z, hZ, hdZ, eq_selected_globalComponents_union_exception hA hL
    (fun _ hy => hy.1) hZ ?_⟩
  intro B hB x hx y hy
  exact and_congr (iff_of_true (subset_of_mem_globalComponents hA hB hx.1)
    (subset_of_mem_globalComponents hA hB hy.1)) (hdict B hB x hx y hy)

theorem isComplexAnalyticSubset_positive_general_two_superlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T)
    (hcan : ResolutionInvariantSpec.IsCanonical m ((invFamily hn 2).inv m) T)
    (q : ℕ) (hq : 1 ≤ q)
    (β : WithBot MonomialInvariant.Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy 1))) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong m T).cosupp ∧ toLex (q, β) ≤ (invFamily hn 2).inv m T y} := by
  obtain ⟨Z, hZ, hdZ, hdict⟩ :=
    exists_analytic_dimzero_positive_threshold_dictionary hn m h T hT hcan q hq β
  have hJ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hA := isComplexAnalyticSubset_cosupport_along hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d
  have hL := ResolutionInvariantOrder.IsInvUSCOn.isClosed_superlevel
    ((invFamily hn 2).isInvValue.usc m h T hcan) hA.isClosed (toLex (q, β))
  apply isComplexAnalyticSubset_of_component_dictionary hA hL (fun _ hy => hy.1) hZ hdZ
  intro B hB x hx y hy
  exact and_congr (iff_of_true (subset_of_mem_globalComponents hA hB hx.1)
    (subset_of_mem_globalComponents hA hB hy.1)) (hdict B hB x hx y hy)

theorem isComplexAnalyticSubset_zero_general_two_superlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T)
    (β : WithBot MonomialInvariant.Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy 1))) :
    IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong m T).cosupp ∧ toLex (0, β) ≤ (invFamily hn 2).inv m T y} := by
  have hJ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hA := isComplexAnalyticSubset_cosupport_along hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d
  refine Lex.rec (fun b => ?_) β
  rcases b with v | a
  ·
    have hmon := HironakaMonomialAnalyticSuperlevels.isComplexAnalyticSubset_canonical_monomial_superlevel
      hn m h T hT v
    have heq : {y | y ∈ (geoTransformAlong m T).cosupp ∧
        toLex (0, toLex (Sum.inl v)) ≤ (invFamily hn 2).inv m T y} =
        (geoTransformAlong m T).cosupp ∩ {y | y ∈ (geoTransformAlong m T).N ∧
          toLex (0, toLex (Sum.inl v)) ≤ (invFamily hn 2).inv m T y} := by
      ext y
      exact ⟨fun hy => ⟨hy.1, (geoTransformAlong m T).cosupp_subset_N hy.1, hy.2⟩,
        fun hy => ⟨hy.1, hy.2.2⟩⟩
    rw [heq]
    exact hA.inter hmon
  ·
    have hord := isComplexAnalyticSubset_canonical_first_superlevel hn m h T hT 1
    have heq : {y | y ∈ (geoTransformAlong m T).cosupp ∧
        toLex (0, toLex (Sum.inr a)) ≤ (invFamily hn 2).inv m T y} =
        (geoTransformAlong m T).cosupp ∩ {y | y ∈ (geoTransformAlong m T).N ∧
          1 ≤ (ofLex ((invFamily hn 2).inv m T y)).1} := by
      ext y
      let lower := fun {X : CMfd.{u} n} (J : MarkedIdeal n X) {Y : CMfd.{u} n}
        (S : BlowupTower X Y) (z : Y) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn 1) J S z
      have he : (invFamily hn 2).inv m T y = genInv lower m T y := rfl
      simp only [mem_ofPred_eq, mem_inter_iff, he]
      by_cases ho : nmOrd (geoTransformAlong m T) y = 0
      · rw [genInv_of_nmOrd_eq_zero lower m T ho]
        simp [Prod.Lex.toLex_le_toLex]
      · have hp : 0 < nmOrd (geoTransformAlong m T) y := Nat.pos_of_ne_zero ho
        have hfirst : 1 ≤ (ofLex (genInv lower m T y)).1 := hp
        have hv : toLex (0, toLex (Sum.inr a)) ≤ genInv lower m T y := by
          rw [genInv, Prod.Lex.toLex_le_toLex]
          exact Or.inl hp
        exact ⟨fun hy => ⟨hy.1, (geoTransformAlong m T).cosupp_subset_N hy.1, hfirst⟩,
          fun hy => ⟨hy.1, hv⟩⟩
    rw [heq]
    exact hA.inter hord

theorem isComplexAnalyticSubset_canonical_general_two_superlevel (hn : 0 < n)
    (m : MarkedIdeal n X) (h : ResolutionInvariantSpec.IsInvDomain 2 m)
    (T : BlowupTower X Y)
    (hcan : ResolutionInvariantSpec.IsCanonical m ((invFamily hn 2).inv m) T)
    (l : ValTy 2) : IsComplexAnalyticSubset (n := n)
      {y | y ∈ (geoTransformAlong m T).cosupp ∧ l ≤ (invFamily hn 2).inv m T y} := by
  have hT := (invFamily hn 2).isInvValue.isGeoTestTower_of_isCanonical h T hcan
  obtain ⟨q, β⟩ := l
  by_cases hq : q = 0
  · subst q
    exact isComplexAnalyticSubset_zero_general_two_superlevel hn m h T hT β
  · exact isComplexAnalyticSubset_positive_general_two_superlevel hn m h T hT hcan q
      (Nat.one_le_iff_ne_zero.mpr hq) β

end ActualGeneral
end
end Hironaka.HironakaGeneralTwoAnalyticSuperlevels
