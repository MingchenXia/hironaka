/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStepOneMemberTailExtension

/-!
# Actual member lower-order predicates and finite curve history

Actual whole-tail domains produce analytic nonmonomial-order predicates at
all literal prefixes. An actually attained natural minimum on every genuine
global curve component produces its proper analytic excess; their locally
finite union is a true zero-dimensional exception. Original constructed
General3 canonical data internally produce the history curve and chosen
entire lower cosupport point. No finite order range, global maximum, caller
curve, or entire-candidate canonical hypothesis is supplied. Deeper lower
history, level-zero contact, whole General3 and global G3 termination stay open.
-/


set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaStepOneMemberLowerOrderPredicates
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  HironakaStepOneMemberLowerExtension HironakaStepOneMemberTailExtension
  InvDomainMemberRestriction NonmonomialOrderLocal MonomialPartAlong
  AnalyticDimensionBasics GlobalComponents RegularLocusComponent
  HironakaCurveAnalyticPredicates HironakaDimensionThreeStepOneCurveEnvelope
  NormalCrossings GermIdealOrder HomogenizedIdealAlong StepOneValue StepOneLowerDomain
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka
noncomputable section
variable {n : ℕ} {X Y : CMfd.{u} n}

def memberPrefixOrderPredicate (m : MarkedIdeal n X) (S : Finset (Fin m.E.length))
    (T : BlowupTower X Y) (i q : ℕ) : Set Y :=
  (tail T i).proj ⁻¹' ordGe (geoTransformAlong (memberRemainderMarked m S) (head T i)) q

theorem isComplexAnalyticSubset_ordGe_of_domain (hn : 0 < n) {k : ℕ}
    (m : MarkedIdeal n Y) (h : IsInvDomain k m) (q : ℕ) :
    IsComplexAnalyticSubset (n := n) (ordGe m q) := by
  have hcoh := isCoherent_nonmonomialPartAlong hn h.isWellFormed.isClosedSubmanifold_N
    h.isWellFormed.isSNCDivisor h.isWellFormed.isTransverse h.isWellFormed.isCoherent h.isNonzeroAlongAt
  by_cases hz : q = 0
  · rw [hz, ordGe, cosupport_zero (fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg)]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold h.isWellFormed.isClosedSubmanifold_N
  · exact CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along hcoh
      h.isWellFormed.isClosedSubmanifold_N (Nat.pos_of_ne_zero hz)

private theorem exists_attained_minimum {B : Set Y} (hB : B.Nonempty) (f : Y → ℕ) :
    ∃ q : ℕ, (∃ x ∈ B, f x = q) ∧ ∀ x ∈ B, q ≤ f x := by
  classical
  obtain ⟨x, hx⟩ := hB
  have hex : ∃ q : ℕ, ∃ x ∈ B, f x = q := ⟨f x, x, hx, rfl⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun x hx => Nat.find_min' hex ⟨x, hx, rfl⟩⟩

private theorem exists_analytic_dimzero_nat_order_exception {Z : Set Y}
    (hZ : IsComplexAnalyticSubset (n := n) Z) (hdim : DimLE (n := n) Z 1)
    (f : Y → ℕ) (P : ℕ → Set Y) (hP : ∀ q, IsComplexAnalyticSubset (n := n) (P q))
    (hdict : ∀ x ∈ Z, ∀ q, x ∈ P q ↔ q ≤ f x) :
    ∃ Q : Set Y, IsComplexAnalyticSubset (n := n) Q ∧ DimLE (n := n) Q 0 ∧ Q ⊆ Z ∧
      ∀ B ∈ globalComponents (n := n) Z, ∃ q : ℕ,
        (∃ x ∈ B, f x = q) ∧ (∀ x ∈ B, q ≤ f x) ∧
        (∀ x ∈ B \ Q, f x = q) ∧
        ∀ x ∈ B \ Q, ∀ r, x ∈ P r ↔ B ⊆ P r := by
  classical
  let C := globalComponents (n := n) Z
  have hm : ∀ B : C, ∃ q : ℕ, (∃ x ∈ (B : Set Y), f x = q) ∧ ∀ x ∈ (B : Set Y), q ≤ f x := by
    intro B
    apply exists_attained_minimum
    obtain ⟨c, ⟨k, hc⟩, heq⟩ := B.2
    rw [heq]
    exact ⟨c, subset_closure (mem_component_self hc)⟩
  choose qB hmin using hm
  let E : C → Set Y := fun B => (B : Set Y) ∩ P (qB B + 1)
  have hnot : ∀ B : C, ¬ (B : Set Y) ⊆ P (qB B + 1) := by
    intro B hsub
    obtain ⟨x, hxB, hfx⟩ := (hmin B).1
    have hxZ := subset_of_mem_globalComponents hZ B.2 hxB
    have hgt := (hdict x hxZ (qB B+1)).mp (hsub hxB)
    omega
  have hE : ∀ B : C, IsComplexAnalyticSubset (n := n) (E B) ∧ DimLE (n := n) (E B) 0 :=
    fun B => analytic_dimzero_inter_globalComponent_of_not_subset hZ hdim B.2 (hP _) (hnot B)
  have hlf : LocallyFinite E := (locallyFinite_globalComponents hZ).subset (fun B => inter_subset_left)
  let Q := ⋃ B : C, E B
  obtain ⟨hQ, hdQ⟩ := analytic_dimzero_iUnion_of_locallyFinite E hlf (fun B => (hE B).1) (fun B => (hE B).2)
  have hQZ : Q ⊆ Z := by
    intro x hx
    obtain ⟨B, hxB⟩ := mem_iUnion.mp hx
    exact subset_of_mem_globalComponents hZ B.2 hxB.1
  have hconst : ∀ B : C, ∀ x ∈ (B : Set Y) \ Q, f x = qB B := by
    intro B x hx
    have hlow := (hmin B).2 x hx.1
    have hxZ := subset_of_mem_globalComponents hZ B.2 hx.1
    have hnotex : x ∉ P (qB B+1) := fun hxP => hx.2 (mem_iUnion.mpr ⟨B, ⟨hx.1, hxP⟩⟩)
    have hhigh : ¬ qB B+1 ≤ f x := fun h => hnotex ((hdict x hxZ _).mpr h)
    omega
  refine ⟨Q, hQ, hdQ, hQZ, ?_⟩
  intro B hB
  let b : C := ⟨B,hB⟩
  refine ⟨qB b, (hmin b).1, (hmin b).2, hconst b, ?_⟩
  intro x hx r
  have hxZ := subset_of_mem_globalComponents hZ hB hx.1
  refine ⟨fun hxr z hzB => ?_, fun hBP => hBP hx.1⟩
  have hle := (hdict x hxZ r).mp hxr
  rw [hconst b x hx] at hle
  exact (hdict z (subset_of_mem_globalComponents hZ hB hzB) r).mpr (hle.trans ((hmin b).2 z hzB))

theorem exists_analytic_dimzero_pulled_nmOrd_exception (hn : 0 < n) {k : ℕ}
    (m : MarkedIdeal n X) (h : IsInvDomain k m) (g : Y → X)
    (hg : ContMDiff (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ComplexModel n)) ∞ g)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdim : DimLE (n := n) Z 1)
    (hsub : Z ⊆ g ⁻¹' m.N) :
    ∃ Q : Set Y, IsComplexAnalyticSubset (n := n) Q ∧ DimLE (n := n) Q 0 ∧ Q ⊆ Z ∧
      ∀ B ∈ globalComponents (n := n) Z, ∃ q : ℕ,
        (∃ x ∈ B, nmOrd m (g x) = q) ∧ (∀ x ∈ B, q ≤ nmOrd m (g x)) ∧
        (∀ x ∈ B \ Q, nmOrd m (g x) = q) ∧
        ∀ x ∈ B \ Q, ∀ r, g x ∈ ordGe m r ↔ B ⊆ g ⁻¹' ordGe m r := by
  apply exists_analytic_dimzero_nat_order_exception hZ hdim (fun x => nmOrd m (g x))
    (fun r => g ⁻¹' ordGe m r)
  · intro r
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg (isComplexAnalyticSubset_ordGe_of_domain hn m h r)
  · intro x hx r
    exact mem_ordGe_iff h.isWellFormed h.isNonzeroAlongAt (hsub hx) r

theorem isComplexAnalyticSubset_memberPrefixOrderPredicate (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (i q : ℕ) :
    IsComplexAnalyticSubset (n := n) (memberPrefixOrderPredicate m S T i q) := by
  have hhead := (isGeoTestTower_iff_head_tail m T i).mp hT
  have hd := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS
    (head T i) hhead.1
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (tail T i).contMDiff_proj
    (isComplexAnalyticSubset_ordGe_of_domain hn _ hd q)

private theorem proj_mem_member_prefix_carrier (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T) (i : ℕ) {z : Y}
    (hz : z ∈ (geoTransformAlong (memberRemainderMarked m S) T).N) :
    (tail T i).proj z ∈ (geoTransformAlong (memberRemainderMarked m S) (head T i)).N := by
  have hhead := (isGeoTestTower_iff_head_tail m T i).mp hT
  have hd := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS
    (head T i) hhead.1
  apply MemberInterTowerAlong.strictAlong_subset_preimage (tail T i) hd.isWellFormed.isClosedSubmanifold_N.1
  rw [← HomogenizedGlueingTower.N_geoTransformAlong, ← geoTransformAlong_head_tail]
  exact hz

theorem member_lower_first_entry_eq_entire_nmOrd (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) {Y₀ : CMfd.{u} n}
    (H : BlowupTower X Y₀) (hH : IsGeoTestTower (barMarked m) H)
    (y₀ : Y₀) {s : ℕ} (hl : level m H y₀ = s+1)
    (T : BlowupTower Y₀ Y) (hT : IsGeoTestTower (geoTransformAlong (barMarked m) H) T)
    (z : openPreimage T (maskA m H y₀)) :
    (ofLex ((CanonicalCentres.invFamily hn 2).inv (lowerMarked m (s+1) H y₀)
      (restrict (maskA m H y₀) T) z)).1 =
      nmOrd (geoTransformAlong (memberLowerExtension m H y₀) T) (z : Y) := by
  obtain ⟨hd, heq⟩ := memberLowerExtension_tail_domain_and_mask_identity hn m h H hH y₀ hl T hT
  change nmOrd (geoTransformAlong (lowerMarked m (s+1) H y₀) (restrict (maskA m H y₀) T)) z = _
  rw [heq]
  exact nmOrd_pullback_val hn hd.isWellFormed hd.isNonzeroAlongAt _ z

theorem member_lower_first_threshold_eq_entire_trace (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) {Y₀ : CMfd.{u} n}
    (H : BlowupTower X Y₀) (hH : IsGeoTestTower (barMarked m) H)
    (y₀ : Y₀) {s : ℕ} (hl : level m H y₀ = s+1)
    (T : BlowupTower Y₀ Y) (hT : IsGeoTestTower (geoTransformAlong (barMarked m) H) T) (q : ℕ) :
    {z : openPreimage T (maskA m H y₀) |
      z ∈ (geoTransformAlong (lowerMarked m (s+1) H y₀) (restrict (maskA m H y₀) T)).N ∧
      q ≤ (ofLex ((CanonicalCentres.invFamily hn 2).inv (lowerMarked m (s+1) H y₀)
        (restrict (maskA m H y₀) T) z)).1} =
      (Subtype.val : openPreimage T (maskA m H y₀) → Y) ⁻¹'
        ordGe (geoTransformAlong (memberLowerExtension m H y₀) T) q := by
  obtain ⟨hd, heq⟩ := memberLowerExtension_tail_domain_and_mask_identity hn m h H hH y₀ hl T hT
  ext z
  have hcar : z ∈ (geoTransformAlong (lowerMarked m (s+1) H y₀) (restrict (maskA m H y₀) T)).N ↔
      (z : Y) ∈ (geoTransformAlong (memberLowerExtension m H y₀) T).N := by rw [heq]; rfl
  change (_ ∧ _) ↔ _
  rw [hcar, member_lower_first_entry_eq_entire_nmOrd hn m h H hH y₀ hl T hT z]
  constructor
  · rintro ⟨hzN, hzq⟩
    exact (mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt hzN q).mpr hzq
  · intro hz
    have hzN := ordGe_subset_N _ q hz
    exact ⟨hzN, (mem_ordGe_iff hd.isWellFormed hd.isNonzeroAlongAt hzN q).mp hz⟩

theorem exists_analytic_dimzero_member_order_history_exception (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (S : Finset (Fin m.E.length)) (hS : S.Nonempty)
    (T : BlowupTower X Y) (hT : IsGeoTestTower m T)
    {Z : Set Y} (hZ : IsComplexAnalyticSubset (n := n) Z) (hdim : DimLE (n := n) Z 1)
    (hsub : Z ⊆ (geoTransformAlong (memberRemainderMarked m S) T).N) :
    ∃ Q : Set Y, IsComplexAnalyticSubset (n := n) Q ∧ DimLE (n := n) Q 0 ∧ Q ⊆ Z ∧
      ∀ B ∈ globalComponents (n := n) Z, ∀ x ∈ B \ Q, ∀ y ∈ B \ Q,
        ∀ i : Fin (T.length+1),
          nmOrd (geoTransformAlong (memberRemainderMarked m S) (head T i)) ((tail T i).proj x) =
            nmOrd (geoTransformAlong (memberRemainderMarked m S) (head T i)) ((tail T i).proj y) ∧
          ∀ q, x ∈ memberPrefixOrderPredicate m S T i q ↔ B ⊆ memberPrefixOrderPredicate m S T i q := by
  have hex : ∀ i : Fin (T.length+1), ∃ Q : Set Y,
      IsComplexAnalyticSubset (n := n) Q ∧ DimLE (n := n) Q 0 ∧ Q ⊆ Z ∧
      ∀ B ∈ globalComponents (n := n) Z, ∃ q : ℕ,
        (∃ x ∈ B, nmOrd (geoTransformAlong (memberRemainderMarked m S) (head T i)) ((tail T i).proj x) = q) ∧
        (∀ x ∈ B, q ≤ nmOrd (geoTransformAlong (memberRemainderMarked m S) (head T i)) ((tail T i).proj x)) ∧
        (∀ x ∈ B \ Q, nmOrd (geoTransformAlong (memberRemainderMarked m S) (head T i)) ((tail T i).proj x) = q) ∧
        ∀ x ∈ B \ Q, ∀ r, x ∈ memberPrefixOrderPredicate m S T i r ↔ B ⊆ memberPrefixOrderPredicate m S T i r := by
    intro i
    have ht := (isGeoTestTower_iff_head_tail m T i).mp hT
    have hd := isInvDomain_geoTransformAlong_memberRemainder hn m h.isWellFormed h.one_le_d h.dimLE S hS (head T i) ht.1
    exact exists_analytic_dimzero_pulled_nmOrd_exception hn _ hd (tail T i).proj (tail T i).contMDiff_proj hZ hdim
      (fun z hz => proj_mem_member_prefix_carrier hn m h S hS T hT i (hsub hz))
  choose Q hQ hdQ hQZ hdictionary using hex
  let E := ⋃ i : Fin (T.length+1), Q i
  obtain ⟨hE, hdE⟩ := analytic_dimzero_iUnion_of_locallyFinite Q (locallyFinite_of_finite Q) hQ hdQ
  refine ⟨E, hE, hdE, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
    exact hQZ i hzi
  · intro B hB x hx y hy i
    have hxQi : x ∈ B \ Q i := ⟨hx.1, fun h => hx.2 (mem_iUnion.mpr ⟨i,h⟩)⟩
    have hyQi : y ∈ B \ Q i := ⟨hy.1, fun h => hy.2 (mem_iUnion.mpr ⟨i,h⟩)⟩
    obtain ⟨q, _, _, hconst, hpred⟩ := hdictionary i B hB
    exact ⟨(hconst x hxQi).trans (hconst y hyQi).symm, hpred x hxQi⟩
open StepOneRegime HironakaGeneralThreeNonspecialAnalyticLoci
open Hironaka.ResolutionInvariantSpec (IsCanonical)

private theorem regime_at_run_start (P : Regime X) (T : BlowupTower X Y)
    (y : Y) (hy : P T y) :
    P (head T (regimeRun P T y)) ((tail T (regimeRun P T y)).proj y) := by
  by_cases hr : regimeRun P T y = 0
  · rw [hr]
    cases T <;> exact hy
  · exact regime_head_of_le_regimeRun P T y _ (by omega) le_rfl

theorem mem_cosupp_entire_member_tail_of_canonical (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m)
    (hmax : IsMaximalOrderAlong m.N m.ideal m.d) (T : BlowupTower X Y)
    (hcan : IsCanonical m (Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily hn 2) m) T)
    (y : Y) (hy : y ∈ (geoTransformAlong m T).cosupp) (hsp : ¬ IsSpecial m T y)
    {s : ℕ} (hs : level m T y = s+1) :
    let r := regimeRun (stepRegime m (level m T y)) T y
    let H := head T r
    let Q := tail T r
    y ∈ (geoTransformAlong (memberLowerExtension m H (Q.proj y)) Q).cosupp := by
  dsimp only
  let r := regimeRun (stepRegime m (level m T y)) T y
  let H := head T r
  let Q := tail T r
  let y₀ := Q.proj y
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (CanonicalCentres.invFamily hn 2)
    m h hmax hn T hcan
  have hbarcan := (Seq.StepOneBridge.isCanonical_iff (k := 3) (CanonicalCentres.invFamily hn 2)
    m h hmax hn T).mp hcan
  have hybar : y ∈ (geoTransformAlong (barMarked m) T).cosupp := by rw [hb.2.2]; exact hy
  have hD := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (k := 3) m (CanonicalCentres.invFamily hn 2)
    h.isWellFormed h.one_le_d hn hmax h.dimLE T hb.1 hbarcan
  have hLy : Seq.StepOneValueMasked.LowerDataL (CanonicalCentres.invFamily hn 2) m
      (StepOneValueMasked.lowerMarkedM m) (level m T y) H Q y := hD y hybar hsp
  rw [hs] at hLy
  obtain ⟨hymask, _, _, hycs⟩ := hLy
  change (⟨y, hymask⟩ : openPreimage Q (maskA m H y₀)) ∈
    (geoTransformAlong (lowerMarked m (s+1) H y₀) (restrict (maskA m H y₀) Q)).cosupp at hycs
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail (barMarked m) T r).mp hb.1
  have hreg : stepRegime m (level m T y) H y₀ := regime_at_run_start _ T y ⟨rfl, hsp⟩
  have hl : level m H y₀ = s+1 := hreg.1.trans hs
  obtain ⟨hd, heq⟩ := memberLowerExtension_tail_domain_and_mask_identity hn m h H hhead y₀ hl Q htail
  rw [heq] at hycs
  rw [MarkedIdealRestrictOpen.cosupp_pullback_val _
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hd.isWellFormed.isCoherent hg)] at hycs
  exact hycs

theorem exists_actual_companion_member_history_curve (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((CanonicalCentres.invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hnsp : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (hpos : 1 ≤ level (companionAt m T x) (companionTailAt m T x) p) :
    let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
    let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
      (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    ∃ s : ℕ, level K R p = s+1 ∧ p₀ ∈ maskA K H p₀ ∧
      p ∈ (geoTransformAlong (memberLowerExtension K H p₀) Q).cosupp ∧
      ∃ A : Set (patchAt m T x), IsComplexAnalyticSubset (n := n) A ∧
        DimLE (n := n) A 1 ∧ A ⊆ (geoTransformAlong (memberLowerExtension K H p₀) Q).N ∧ p ∈ A := by
  dsimp only
  let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
  let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
    (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  obtain ⟨s, hs, hmask, hd, _, _⟩ := exists_actual_companion_member_tail_extension hn m h T hcan x hx hq p hp hnsp hpos
  have hpentire := mem_cosupp_entire_member_tail_of_canonical hn K hK hmax R hcanK p hp hnsp hs
  obtain ⟨Z, hZ, hdZ, _, hpZ⟩ := exists_actual_companion_dimone_nonspecial_envelope hn m h T hcan x hx hq
  let A : Set (patchAt m T x) := Z ∩ (geoTransformAlong (memberLowerExtension K H p₀) Q).N
  have hN := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hd.isWellFormed.isClosedSubmanifold_N
  exact ⟨s, hs, hmask, hpentire, A, hZ.inter hN,
    DimensionMonotone.DimLE.anti hZ inter_subset_left hdZ, inter_subset_right, ⟨hpZ p hp hnsp, hpentire.1⟩⟩

theorem exists_actual_companion_member_order_history (hn : 0 < n)
    (m : MarkedIdeal n X) (h : IsInvDomain 3 m) (T : BlowupTower X Y)
    (hcan : IsCanonical m ((CanonicalCentres.invFamily hn 3).inv m) T)
    (x : Y) (hx : x ∈ (geoTransformAlong m T).cosupp) (hq : 1 ≤ orderAt m T x)
    (p : patchAt m T x)
    (hp : p ∈ (geoTransformAlong (companionAt m T x) (companionTailAt m T x)).cosupp)
    (hnsp : ¬ IsSpecial (companionAt m T x) (companionTailAt m T x) p)
    (hpos : 1 ≤ level (companionAt m T x) (companionTailAt m T x) p) :
    let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
    let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
      (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
    let r := regimeRun (stepRegime K (level K R p)) R p
    let H := head R r
    let Q := tail R r
    let p₀ := Q.proj p
    let J₀ := geoTransformAlong (barMarked K) H
    let S := membersThrough J₀.E (origMembers K H) p₀
    ∃ s : ℕ, level K R p = s+1 ∧ p₀ ∈ maskA K H p₀ ∧
      ∃ A E : Set (patchAt m T x),
        IsComplexAnalyticSubset (n := n) A ∧ DimLE (n := n) A 1 ∧
        A ⊆ (geoTransformAlong (memberLowerExtension K H p₀) Q).N ∧ p ∈ A ∧
        IsComplexAnalyticSubset (n := n) E ∧ DimLE (n := n) E 0 ∧ E ⊆ A ∧
        (∀ B ∈ globalComponents (n := n) A, ∀ z ∈ B \ E, ∀ w ∈ B \ E,
          ∀ i : Fin (Q.length+1),
            nmOrd (geoTransformAlong (memberLowerExtension K H p₀) (head Q i)) ((tail Q i).proj z) =
              nmOrd (geoTransformAlong (memberLowerExtension K H p₀) (head Q i)) ((tail Q i).proj w) ∧
            ∀ q, z ∈ memberPrefixOrderPredicate J₀ S Q i q ↔ B ⊆ memberPrefixOrderPredicate J₀ S Q i q) ∧
        ∀ i : ℕ, ∀ z : openPreimage (head Q i) (maskA K H p₀),
          (ofLex ((CanonicalCentres.invFamily hn 2).inv (lowerMarked K (s+1) H p₀)
            (restrict (maskA K H p₀) (head Q i)) z)).1 =
              nmOrd (geoTransformAlong (memberLowerExtension K H p₀) (head Q i)) z := by
  dsimp only
  let K : MarkedIdeal n (CMfd.of (n := n) (maskAt m T x)) := companionAt m T x
  let R : BlowupTower (CMfd.of (n := n) (maskAt m T x))
    (CMfd.of (n := n) (patchAt m T x)) := companionTailAt m T x
  let r := regimeRun (stepRegime K (level K R p)) R p
  let H := head R r
  let Q := tail R r
  let p₀ := Q.proj p
  let J₀ := geoTransformAlong (barMarked K) H
  let S := membersThrough J₀.E (origMembers K H) p₀
  obtain ⟨_, hK, hmax, hcanK, _⟩ := actual_companion_domain_and_cosupport_dictionary hn m h T hcan x hx hq
  have hb := Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := 3) (CanonicalCentres.invFamily hn 2) K hK hmax hn R hcanK
  obtain ⟨hhead, htail⟩ := (isGeoTestTower_iff_head_tail (barMarked K) R r).mp hb.1
  obtain ⟨s, hs, hmask, _, A, hA, hdA, hsubA, hpA⟩ := exists_actual_companion_member_history_curve hn m h T hcan x hx hq p hp hnsp hpos
  have hreg : stepRegime K (level K R p) H p₀ := regime_at_run_start _ R p ⟨rfl, hnsp⟩
  have hl : level K H p₀ = s+1 := hreg.1.trans hs
  have hdJ₀ : IsInvDomain 3 J₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (HironakaCoherentTransformExtension.isInvDomain_barMarked K hK) H hhead
  have hE₀ : ∀ B ∈ origMembers K H, B ∈ J₀.E := fun B hB => List.mem_of_mem_take hB
  have hS : S.Nonempty := membersThrough_nonempty hE₀ (by change 1 ≤ level K H p₀; rw [hl]; omega)
  obtain ⟨E, hE, hdE, hEA, hhist⟩ := exists_analytic_dimzero_member_order_history_exception hn J₀ hdJ₀ S hS Q htail hA hdA hsubA
  refine ⟨s, hs, hmask, A, E, hA, hdA, hsubA, hpA, hE, hdE, hEA, hhist, ?_⟩
  intro i z
  have hprefix := (isGeoTestTower_iff_head_tail J₀ Q i).mp htail
  exact member_lower_first_entry_eq_entire_nmOrd hn K hK H hhead p₀ hl (head Q i) hprefix.1 z

end
end Hironaka.HironakaStepOneMemberLowerOrderPredicates
