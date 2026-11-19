import Hironaka.Resolution.HironakaG8P1NormalizedOrder
import Hironaka.Resolution.HironakaG8DomainExponents
import Hironaka.Resolution.HironakaG8ClassStepCut
import Hironaka.Invariant.MemberInterAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Two records along one arc tower; Lemma M (i): order = mark is an invariant without transversality
(G8B lane, run 0080, round 5; route R1 of lane G11B's `FALLBACK-DECISION-ANALYSIS.md` §2, step 2)

Blueprint: `hironaka-g8-p1-arc-pair.tex`.  Notes: `work/hironaka-resume-20261111/G8B/REPORT-r5.md`.

Source: Bierstone–Milman 2008, §6, proof of Theorem 6.1 (product with a line, point blowups at the arc points, the count
of the exponent along the last exceptional divisor), run for marked ideals whose simple normal crossings boundary is NOT
assumed transverse to the carriers.  Point centres are admissible for every boundary, so the arc tower of the record
WITHOUT boundary (which is in the native domain after restricting to the open set where the ideal is nonzero along the
carrier) is a common test tower of both records WITH boundary.

* `PointTower` (every centre a point), `pointTower_append`, `pointTower_arcFamily`;
* `SameNID` (same carrier, ideal and mark; boundaries may differ), `sameNID_geoTransformAlong`, `cosupp_eq_of_sameNID`,
  **`isGeoTestTower_of_sameNID`** (a point tower that is a test tower of one record is one of every record with the same
  carrier, ideal and mark and a simple normal crossings boundary);
* `locWPEquiv_projectionTest`; `sameCarrierDim_along` (equal carrier dimensions along a common point tower);
* **`isDivNearAlong_mark_of_stage`** (the stage argument of Lemma M: if near the arc point the trace of the last divisor
  on one carrier lies in the common cosupport, so does the trace on the other — filling of submanifolds of equal
  dimension);
* **`exists_arcPairStage`** (the common arc stage `r` of two records with equal cosupports along point towers, with the
  exact counts `(r+1)(ord - d)` of both at the common arc point);
* **`cosupport_succ_iff`** (Lemma M (i)): for `LocWPEquiv` marked ideals with a simple normal crossings boundary (not
  necessarily transverse to the carriers), closed submanifold carriers of the same dimension, coherent ideals and the same
  mark `d ≥ 1`, at a cosupport point where both ideals are nonzero along their carriers, the order exceeds the mark for one
  iff for the other.

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ArcPair

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal NormalCrossings DivisorExponentAlong GermIdealOrder MarkedIdealRestrictOpen
  HironakaActualSharedCartierTraceTests HironakaActualProjectionTestRecord HironakaG8P1ArcTower
  BlowupStrictSubmanifold BlowupConstruction RestrictedIdealQuotient IdealWeightPowers MarkedIdealBiholomorphism
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv LocEquiv)
open Hironaka.HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)
open scoped Hironaka.ProductComplexManifold

noncomputable section

/-! ### Point towers -/

section PointTowers

variable {m : ℕ} {X : CMfd.{u} m}

/-- **A point tower**: every centre is a point. -/
def PointTower : {Y : CMfd.{u} m} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => PointTower T ∧ ∃ y, C = {y}

theorem pointTower_append {Y : CMfd.{u} m} (T : BlowupTower X Y) (hT : PointTower T) :
    ∀ {Z : CMfd.{u} m} (S : BlowupTower Y Z), PointTower S → PointTower (T.append S)
  | _, .refl, _ => hT
  | _, .step S _ _ _, hS => ⟨pointTower_append T hT S hS.1, hS.2⟩

end PointTowers

/-! ### Records with the same carrier, ideal and mark -/

section SameNID

variable {m : ℕ} {X : CMfd.{u} m}

/-- **Same carrier, ideal and mark** (the boundaries may differ). -/
def SameNID (M M' : MarkedIdeal m X) : Prop := M'.N = M.N ∧ M'.ideal = M.ideal ∧ M'.d = M.d

theorem cosupp_eq_of_sameNID {M M' : MarkedIdeal m X} (h : SameNID M M') : M'.cosupp = M.cosupp := by
  obtain ⟨hN, hI, hd⟩ := h
  show cosupport m M'.N M'.ideal M'.d = cosupport m M.N M.ideal M.d
  rw [hN, hI, hd]

theorem sameNID_geoTransform {M M' : MarkedIdeal m X} (h : SameNID M M') {Y : CMfd.{u} m} (C : Set X) (π : Y → X) :
    SameNID (M.geoTransform C π) (M'.geoTransform C π) := by
  obtain ⟨hN, hI, hd⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show geoStrictTransform π C M'.N = geoStrictTransform π C M.N
    rw [hN]
  · show colonAlong m (geoStrictTransform π C M'.N) (GermIdeal.pullback π M'.ideal)
        (idealPow (GermIdeal.pullback π (vanishingIdeal (n := m) C)) M'.d) =
      colonAlong m (geoStrictTransform π C M.N) (GermIdeal.pullback π M.ideal)
        (idealPow (GermIdeal.pullback π (vanishingIdeal (n := m) C)) M.d)
    rw [hN, hI, hd]
  · exact hd

theorem sameNID_geoTransformAlong {M M' : MarkedIdeal m X} (h : SameNID M M') :
    ∀ {Y : CMfd.{u} m} (T : BlowupTower X Y), SameNID (geoTransformAlong M T) (geoTransformAlong M' T)
  | _, .refl => h
  | _, .step T C π _ => sameNID_geoTransform (sameNID_geoTransformAlong h T) C π

/-- **Along test towers the boundary stays simple normal crossings.** -/
theorem isSNCDivisor_geoTransformAlong {P : MarkedIdeal m X} (hP : IsSNCDivisor m P.E) :
    ∀ {Y : CMfd.{u} m} (T : BlowupTower X Y), IsGeoTestTower P T → IsSNCDivisor m (geoTransformAlong P T).E
  | _, .refl, _ => hP
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff P T C π hπ).mp hT
    exact SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ
      (isSNCDivisor_geoTransformAlong hP T hTT) hC.2.2

/-- **Point towers are tests for every boundary**: a point tower that is a test tower of `M` is a test tower of every
`M'` with the same carrier, ideal and mark and a simple normal crossings boundary. -/
theorem isGeoTestTower_of_sameNID {M M' : MarkedIdeal m X} (h : SameNID M M') (hE : IsSNCDivisor m M'.E) :
    ∀ {Y : CMfd.{u} m} (T : BlowupTower X Y), PointTower T → IsGeoTestTower M T → IsGeoTestTower M' T
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hpt, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff M T C π hπ).mp hT
    have ih := isGeoTestTower_of_sameNID h hE T hpt.1 hTT
    refine (isGeoTestTower_step_iff M' T C π hπ).mpr ⟨ih, hC.1, ?_, ?_⟩
    · rw [cosupp_eq_of_sameNID (sameNID_geoTransformAlong h T)]
      exact hC.2.1
    · obtain ⟨y, rfl⟩ := hpt.2
      exact HironakaOneDimensionalCanonicalSuperlevels.hasNormalCrossings_singleton y
        (isSNCDivisor_geoTransformAlong hE T ih)

/-- **Equal carrier dimensions along a common point tower**: `M₀`, `M₁` well formed with equal carrier dimensions on the
cosupport; `M₀'`, `M₁'` with the same carriers, ideals and marks are `WEquiv` with a simple normal crossings boundary.
Along every point tower that is a test tower of `M₀` and `M₁`, the carrier dimensions stay equal on the cosupport. -/
theorem sameCarrierDim_along {M₀ M₁ M₀' M₁' : MarkedIdeal m X} (hwf₀ : M₀.IsWellFormed) (hwf₁ : M₁.IsWellFormed)
    (h₀ : SameNID M₀ M₀') (h₁ : SameNID M₁ M₁') (hW : WEquiv M₀' M₁') (hE : IsSNCDivisor m M₀'.E)
    (hdim : SameCarrierDim M₀ M₁) :
    ∀ {Y : CMfd.{u} m} (T : BlowupTower X Y), PointTower T → IsGeoTestTower M₀ T → IsGeoTestTower M₁ T →
      SameCarrierDim (geoTransformAlong M₀ T) (geoTransformAlong M₁ T)
  | _, .refl, _, _, _ => hdim
  | _, .step T C π hπ, hpt, hT₀, hT₁ => by
    obtain ⟨hTT₀, hC₀⟩ := (isGeoTestTower_step_iff M₀ T C π hπ).mp hT₀
    obtain ⟨hTT₁, hC₁⟩ := (isGeoTestTower_step_iff M₁ T C π hπ).mp hT₁
    have ih := sameCarrierDim_along hwf₀ hwf₁ h₀ h₁ hW hE hdim T hpt.1 hTT₀ hTT₁
    have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwf₀ T hTT₀
    have hwB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwf₁ T hTT₁
    have hT' : IsGeoTestTower M₀' (.step T C π hπ) := isGeoTestTower_of_sameNID h₀ hE _ hpt hT₀
    have hcos : (geoTransformAlong M₀ (.step T C π hπ)).cosupp = (geoTransformAlong M₁ (.step T C π hπ)).cosupp := by
      rw [← cosupp_eq_of_sameNID (sameNID_geoTransformAlong h₀ (.step T C π hπ)), (hW.2 _).2 hT',
        cosupp_eq_of_sameNID (sameNID_geoTransformAlong h₁ (.step T C π hπ))]
    exact HironakaG8SpecialLoci.sameCarrierDim_geoTransform hwA.isClosedSubmanifold_N hwB.isClosedSubmanifold_N
      (fun x g hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwA.isCoherent hg) ih hC₀
      hC₁.subset_N hπ hcos

end SameNID

/-! ### Products with a line -/

section Products

variable {n : ℕ} {X : CMfd.{u} n}

theorem locWPEquiv_projectionTest {M M' : MarkedIdeal n X} (h : LocWPEquiv M M') :
    LocWPEquiv (projectionTest M) (projectionTest M') := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  have hE : E' = E := h.1
  subst hE
  exact h.record (.projection .refl) ⟨rfl, trivial⟩ trivial

theorem sameNID_projectionTest {M M' : MarkedIdeal n X} (h : SameNID M M') :
    SameNID (projectionTest M) (projectionTest M') := by
  obtain ⟨hN, hI, hd⟩ := h
  refine ⟨?_, ?_, hd⟩
  · show (Prod.fst : projectionAmbient X → X) ⁻¹' M'.N = Prod.fst ⁻¹' M.N
    rw [hN]
  · show GermIdeal.pullback (m := n + 1) Prod.fst M'.ideal = GermIdeal.pullback (m := n + 1) Prod.fst M.ideal
    rw [hI]

end Products

/-! ### Arc families are point towers -/

section Arc

variable {n : ℕ} {X : CMfd.{u} n}

theorem pointTower_arcFamily {x : X} {hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
    (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X)))} {S : ℕ → ArcStage n (arcY1 x)}
    (hS : IsArcFamily x hπ1 S) : ∀ r, PointTower ((arcA1 x hπ1).append (S r).R) := by
  have hbase : PointTower (arcA1 x hπ1) := ⟨trivial, (x, 0), rfl⟩
  have key : ∀ r, PointTower (S r).R := by
    intro r
    induction r with
    | zero =>
      have hZ := hS.zero_Z
      have hR := hS.zero_R
      generalize S 0 = s at hZ hR ⊢
      obtain ⟨Zs, Rs, es, zs⟩ := s
      dsimp only at hZ hR ⊢
      subst hZ
      obtain rfl := eq_of_heq hR
      trivial
    | succ r ih =>
      obtain ⟨hπ, hZt, hRt⟩ := hS.succ r
      generalize S (r + 1) = t at hZt hRt ⊢
      generalize S r = s at ih hπ hZt hRt
      obtain ⟨Zs, Rs, es, zs⟩ := s
      obtain ⟨Zt, Rt, et, zt⟩ := t
      dsimp only at ih hπ hZt hRt ⊢
      subst hZt
      obtain rfl := eq_of_heq hRt
      exact ⟨ih, zs, rfl⟩
  exact fun r => pointTower_append _ hbase _ (key r)

end Arc

/-! ### The stage argument of Lemma M -/

section Stage

variable {m : ℕ} {Y : CMfd.{u} m}

/-- **The stage argument of Lemma M** (filling): two records in the native domain with the same cosupport, a common
member `D`, a point `z` of both carriers on `D` at which the carriers have the same dimension.  If near `z` the trace of `D`
on the second carrier lies in the cosupport, so does the trace on the first. -/
theorem isDivNearAlong_mark_of_stage (hm : 0 < m) {kA kB : ℕ} {SA SB : MarkedIdeal m Y} (hA : IsInvDomain kA SA)
    (hB : IsInvDomain kB SB) (hcos : SA.cosupp = SB.cosupp) {D : Set Y} (hDA : D ∈ SA.E) (hDB : D ∈ SB.E) {z : Y}
    (hzA : z ∈ SA.N) (hzB : z ∈ SB.N) (hzD : z ∈ D)
    (hdim : ∀ j, RegularAtDim (n := m) SA.N z j ↔ RegularAtDim (n := m) SB.N z j)
    (hB' : IsDivNearAlong m SB.N SB.ideal D SB.d z) : IsDivNearAlong m SA.N SA.ideal D SA.d z := by
  obtain ⟨j, hjA⟩ := hA.isWellFormed.isClosedSubmanifold_N.2 z hzA
  have hjB := (hdim j).mp hjA
  have hA1 := HironakaG8P1ForeignCount.regularAtDim_inter_of_mem hA.isWellFormed.isTransverse hDA hzA hzD hjA
  have hB1 := HironakaG8P1ForeignCount.regularAtDim_inter_of_mem hB.isWellFormed.isTransverse hDB hzB hzD hjB
  obtain ⟨i, hi⟩ := List.get_of_mem hDB
  have hSB : IsClosedSubmanifold m (SB.N ∩ D) := by
    have h := MemberInterAlong.isClosedSubmanifold_inter_memberInter hm hB.isWellFormed.isClosedSubmanifold_N.1
      hB.isWellFormed.isSNCDivisor hB.isWellFormed.isTransverse {i}
    rw [DivisorExponentAlong.memberInter_singleton, hi] at h
    exact h
  have hsub : ∀ᶠ y in 𝓝 z, y ∈ SB.N ∩ D → y ∈ SA.N ∩ D := by
    filter_upwards [hB'] with y hy hyND
    have hyc : y ∈ SB.cosupp := hy hyND.1 hyND.2
    rw [← hcos] at hyc
    exact ⟨SA.cosupp_subset_N hyc, hyND.2⟩
  have heq := HironakaG8P1ForeignCount.eventually_mem_iff_of_subset hSB hB1.2 hA1.2 hsub
  filter_upwards [hB', heq] with y hy hiff hyN hyD
  have hyc : y ∈ SB.cosupp := hy (hiff.mpr ⟨hyN, hyD⟩).1 hyD
  rw [← hcos] at hyc
  exact hyc

end Stage

/-! ### The common arc stage -/

section Common

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The common arc stage `r`** of two records `A`, `B` in the native domain at a common cosupport point `x`, whose
products with a line have records `A'`, `B'` (same carriers, ideals, marks; another boundary, simple normal crossings) with
equal cosupports along their common test towers: the arc tower `T` of `A` at `x` is the arc tower of `B`; it is a point
tower and a test tower of both products and of `A'`; the transforms have equal cosupports and equal carrier dimensions on
the cosupport; the arc point `z` lies on the last member, and the exponents along it at `z` are exactly
`(r + 1)(ord_x - d)` for both. -/
theorem exists_arcPairStage {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
    (A' B' : MarkedIdeal (n+1) (projectionAmbient X)) (hsA : SameNID (projectionTest A) A')
    (hsB : SameNID (projectionTest B) B') (hW : WEquiv A' B') (hE' : IsSNCDivisor (n+1) A'.E) (r : ℕ) :
    ∃ (Z : CMfd.{u} (n+1)) (T : BlowupTower (projectionAmbient X) Z) (z : Z),
      PointTower T ∧ IsGeoTestTower (projectionTest A) T ∧ IsGeoTestTower (projectionTest B) T ∧
      IsGeoTestTower A' T ∧
      (geoTransformAlong (projectionTest A) T).cosupp = (geoTransformAlong (projectionTest B) T).cosupp ∧
      SameCarrierDim (geoTransformAlong (projectionTest A) T) (geoTransformAlong (projectionTest B) T) ∧
      z ∈ (geoTransformAlong (projectionTest A) T).cosupp ∧
      ∃ D : Set Z, D ∈ (geoTransformAlong (projectionTest A) T).E ∧ D ∈ (geoTransformAlong (projectionTest B) T).E ∧
        z ∈ D ∧
        (∀ e, IsDivNearAlong (n+1) (geoTransformAlong (projectionTest A) T).N
          (geoTransformAlong (projectionTest A) T).ideal D e z ↔ e ≤ (r + 1) * (ordinaryTraceOrder A.N A.ideal x - A.d)) ∧
        (∀ e, IsDivNearAlong (n+1) (geoTransformAlong (projectionTest B) T).N
          (geoTransformAlong (projectionTest B) T).ideal D e z ↔ e ≤ (r + 1) * (ordinaryTraceOrder B.N B.ideal x - B.d)) := by
  have hxB : x ∈ B.cosupp := by
    have h1 : A'.cosupp = B'.cosupp := (hW.2 .refl).2 trivial
    have h2 := cosupp_eq_of_sameNID hsA
    have h3 := cosupp_eq_of_sameNID hsB
    have hA0 := (projection_test_dictionary A hA).2.2.2.2.2.2.2
    have hB0 := (projection_test_dictionary B hB).2.2.2.2.2.2.2
    have hp : ((x, 0) : projectionAmbient X) ∈ (projectionTest B).cosupp := by
      rw [← h3, ← h1, h2, hA0]
      exact hx
    rw [hB0] at hp
    exact hp
  have hπ1 : IsBlowupAlong (n+1) ({(x, 0)} : Set (projectionAmbient X))
      (blowupProj (n+1) ({(x, 0)} : Set (projectionAmbient X))) :=
    isBlowupAlong_blowupProj (n := n+1) (C := ({(x, 0)} : Set (projectionAmbient X)))
      (HironakaActualProjectionVerticalBlowupChart.projection_point_centre A hA x hx).2
  obtain ⟨S, hS, hcA⟩ := exists_arcFamily (k := kA) A hA x hx hπ1
  obtain ⟨S', hS', hcB⟩ := exists_arcFamily (k := kB) B hB x hxB hπ1
  obtain ⟨hZ, hR, hz, -⟩ := arcFamily_identify hS hS' r
  have hpt := pointTower_arcFamily hS r
  have hca := arcCounts_of_raw (hcA r)
  have hcb := arcCounts_of_raw (hcB r)
  generalize S r = s at hZ hR hz hca hpt
  generalize S' r = s' at hZ hR hz hcb
  obtain ⟨Zs, Rs, es, zs⟩ := s
  obtain ⟨Zs', Rs', es', zs'⟩ := s'
  dsimp only at hZ hR hz hpt
  subst hZ
  obtain rfl := eq_of_heq hR
  obtain rfl := eq_of_heq hz
  obtain ⟨hlen, hTA, hCosA, GA, hNA, hEA, hiA, hzGA, hCA⟩ := hca
  obtain ⟨-, hTB, -, GB, hNB, hEB', hiB, hzGB, hCB⟩ := hcb
  set T := (arcA1 x hπ1).append Rs with hTdef
  set QA := (projectionTest A).geoTransformAlong T with hQA
  set QB := (projectionTest B).geoTransformAlong T with hQB
  have hTA' : IsGeoTestTower A' T := isGeoTestTower_of_sameNID hsA hE' T hpt hTA
  have hcos : QA.cosupp = QB.cosupp := by
    rw [hQA, hQB, ← cosupp_eq_of_sameNID (sameNID_geoTransformAlong hsA T), (hW.2 T).2 hTA',
      cosupp_eq_of_sameNID (sameNID_geoTransformAlong hsB T)]
  have hdimQ : SameCarrierDim QA QB :=
    sameCarrierDim_along (projection_test_isInvDomain A hA).isWellFormed
      (projection_test_isInvDomain B hB).isWellFormed hsA hsB hW hE'
      (HironakaG8P1Assembly.sameCarrierDim_projectionTest hA hB hdim) T hpt hTA hTB
  have hEAB : QA.E = QB.E := by
    refine MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq ?_ T
    show A.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X] =
      B.E.map ((Prod.fst : projectionAmbient X → X) ⁻¹' ·) ++ [horizontal X]
    rw [hEB]
  obtain ⟨hneA, -, hzDA, hExpA⟩ := HironakaG8P1Assembly.count_zero_exponent GA QA _ zs hCA hNA hEA hiA hzGA
  obtain ⟨hneB, -, -, hExpB⟩ := HironakaG8P1Assembly.count_zero_exponent GB QB _ zs hCB hNB hEB' hiB hzGB
  have hlastEq : ∀ (l₁ l₂ : List (Set Zs)) (h : l₁ = l₂) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []),
      l₁.getLast h₁ = l₂.getLast h₂ := by
    rintro _ _ rfl _ _
    rfl
  have hDD : QB.E.getLast hneB = QA.E.getLast hneA := hlastEq _ _ hEAB.symm _ _
  refine ⟨Zs, T, zs, hpt, hTA, hTB, hTA', hcos, hdimQ, hCosA, QA.E.getLast hneA, List.getLast_mem hneA,
    hEAB ▸ List.getLast_mem hneA, hzDA, ?_, ?_⟩
  · intro e

    exact hExpA e
  · intro e
    rw [← hDD]

    exact hExpB e

end Common

/-! ### Lemma M (i) -/

section LemmaMi

variable {n : ℕ} {X : CMfd.{u} n}

/-- The arithmetic of Lemma M (i) with `r + 1 = d`. -/
theorem le_mul_sub_iff (d ρ : ℕ) (hd : 1 ≤ d) : d ≤ (d - 1 + 1) * (ρ - d) ↔ d + 1 ≤ ρ := by
  rw [Nat.sub_add_cancel hd]
  constructor
  · intro h
    by_contra hc
    have h0 : ρ - d = 0 := by omega
    rw [h0, Nat.mul_zero] at h
    omega
  · intro h
    have h1 : 1 ≤ ρ - d := by omega
    calc d = d * 1 := (Nat.mul_one d).symm
      _ ≤ d * (ρ - d) := Nat.mul_le_mul_left d h1

/-- **Lemma M (i): "order = mark" is an invariant without transversality** (route R1, G11B's
`FALLBACK-DECISION-ANALYSIS.md` §2).  `P ≈ Q` (`LocWPEquiv`) with a simple normal crossings boundary that need NOT be
transverse to the carriers, closed submanifold carriers of the same dimension on the cosupport, coherent ideals, the same
mark `d ≥ 1`; at a cosupport point `x` where both ideals are nonzero along their carriers, `ord_x(P) > d` iff
`ord_x(Q) > d`.  Proof: restrict to the open set where both ideals are nonzero along their carriers, drop the boundary
(native domain), run the arc test (BM08 §6) at `x` for both (one common tower, `exists_arcPairStage`); its point centres
are tests of the records WITH boundary, so the cosupports agree at stage `r = d - 1`; the exact counts `d(ord - d)` along
the last divisor and the filling argument `isDivNearAlong_mark_of_stage` give `d ≤ d(ord_P - d) ↔ d ≤ d(ord_Q - d)`. -/
theorem cosupport_succ_iff (P Q : MarkedIdeal n X) (h : LocWPEquiv P Q) (hNP : IsClosedSubmanifold n P.N)
    (hNQ : IsClosedSubmanifold n Q.N) (hIP : P.ideal.IsCoherent) (hIQ : Q.ideal.IsCoherent) (hE : IsSNCDivisor n P.E)
    (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q) {x : X} (hx : x ∈ P.cosupp)
    (hxP : IsNonzeroAlongAt P.N P.ideal x) (hxQ : IsNonzeroAlongAt Q.N Q.ideal x) :
    x ∈ cosupport n P.N P.ideal (P.d + 1) ↔ x ∈ cosupport n Q.N Q.ideal (P.d + 1) := by
  set P0 : MarkedIdeal n X := ⟨P.N, [], P.ideal, P.d⟩ with hP0
  set Q0 : MarkedIdeal n X := ⟨Q.N, [], Q.ideal, Q.d⟩ with hQ0
  have hwfP0 : P0.IsWellFormed := ⟨hNP, hIP, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hNP⟩
  have hwfQ0 : Q0.IsWellFormed := ⟨hNQ, hIQ, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold hNQ⟩
  have hdQ1 : 1 ≤ Q.d := hd ▸ hd1
  have hxQc : x ∈ Q.cosupp := h.cosupp_eq_base ▸ hx
  let G : Opens X := HironakaG8DomainExponents.domOpen P0 hNP ⊓ HironakaG8DomainExponents.domOpen Q0 hNQ
  have hxG : x ∈ G := ⟨(HironakaG8DomainExponents.mem_domOpen_iff (P := P0) hNP hIP hd1 (P.cosupp_subset_N hx)).mpr hxP,
    (HironakaG8DomainExponents.mem_domOpen_iff (P := Q0) hNQ hIQ hdQ1 (Q.cosupp_subset_N hxQc)).mpr hxQ⟩
  have hholP : ∀ y g, P.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIP hg
  have hholQ : ∀ y g, Q.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIQ hg
  set A0 := MarkedIdeal.pullback (Subtype.val : G → X) P0 with hA0def
  set B0 := MarkedIdeal.pullback (Subtype.val : G → X) Q0 with hB0def
  have hA0 : IsInvDomain n A0 :=
    HironakaG8DomainExponents.isInvDomain_pullback_val_of_le_domOpen hwfP0 hd1 (G := G) inf_le_left
  have hB0 : IsInvDomain n B0 :=
    HironakaG8DomainExponents.isInvDomain_pullback_val_of_le_domOpen hwfQ0 hdQ1 (G := G) inf_le_right
  set x' : G := ⟨x, hxG⟩ with hx'def
  have hcosP : ∀ e, cosupport n ((Subtype.val : G → X) ⁻¹' P.N) (GermIdeal.pullback (m := n) (Subtype.val : G → X) P.ideal) e =
      (Subtype.val : G → X) ⁻¹' cosupport n P.N P.ideal e :=
    fun e => cosupp_pullback_val (⟨P.N, [], P.ideal, e⟩ : MarkedIdeal n X) hholP G
  have hcosQ : ∀ e, cosupport n ((Subtype.val : G → X) ⁻¹' Q.N) (GermIdeal.pullback (m := n) (Subtype.val : G → X) Q.ideal) e =
      (Subtype.val : G → X) ⁻¹' cosupport n Q.N Q.ideal e :=
    fun e => cosupp_pullback_val (⟨Q.N, [], Q.ideal, e⟩ : MarkedIdeal n X) hholQ G
  have hx'A : x' ∈ A0.cosupp := by
    show x' ∈ cosupport n ((Subtype.val : G → X) ⁻¹' P.N) (GermIdeal.pullback (m := n) (Subtype.val : G → X) P.ideal) P.d
    rw [hcosP]
    exact hx
  -- the records with boundary
  have hL : LocWPEquiv (X := CMfd.of (n := n) G) (MarkedIdeal.pullback (Subtype.val : G → X) P)
      (MarkedIdeal.pullback (Subtype.val : G → X) Q) := LocEquiv.restrict h G
  have hLp := locWPEquiv_projectionTest hL
  have hsA :=
    sameNID_projectionTest (X := CMfd.of (n := n) G) (M := A0) (M' := MarkedIdeal.pullback (Subtype.val : G → X) P) ⟨rfl, rfl, rfl⟩
  have hsB :=
    sameNID_projectionTest (X := CMfd.of (n := n) G) (M := B0) (M' := MarkedIdeal.pullback (Subtype.val : G → X) Q) ⟨rfl, rfl, rfl⟩
  have hEG : IsSNCDivisor n (MarkedIdeal.pullback (Subtype.val : G → X) P).E :=
    NormalCrossingsInvariance.isSNCDivisor_map_preimage (NormalCrossingsInvariance.pullsBackCoordinates_val G)
      continuous_subtype_val hE
  have hE' := HironakaG8ClassStepCut.isSNCDivisor_projectionTest (Y := CMfd.of (n := n) G)
    (A := MarkedIdeal.pullback (Subtype.val : G → X) P) hEG
  have hdim0 : SameCarrierDim (X := CMfd.of (n := n) G) A0 B0 :=
    HironakaG8SpecialLoci.sameCarrierDim_pullback_val (A := P0) (B := Q0) hholP hdim G
  obtain ⟨Z, T, z, -, hTA, hTB, -, hcos, hdimQ, hzc, D, hDA, hDB, hzD, hexA, hexB⟩ :=
    exists_arcPairStage A0 B0 hA0 hB0 rfl hdim0 hx'A _ _ hsA hsB hLp.wEquiv hE' (P.d - 1)
  have hQA := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (projection_test_isInvDomain (X := CMfd.of (n := n) G) A0 hA0) T hTA
  have hQB := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (projection_test_isInvDomain (X := CMfd.of (n := n) G) B0 hB0) T hTB
  have hzA : z ∈ ((projectionTest A0).geoTransformAlong T).N := MarkedIdeal.cosupp_subset_N _ hzc
  have hzB : z ∈ ((projectionTest B0).geoTransformAlong T).N := MarkedIdeal.cosupp_subset_N _ (hcos ▸ hzc)
  have hdA : ((projectionTest A0).geoTransformAlong T).d = P.d := d_geoTransformAlong _ T
  have hdB : ((projectionTest B0).geoTransformAlong T).d = P.d := (d_geoTransformAlong _ T).trans hd
  have hm : 0 < n + 1 := Nat.succ_pos n
  have key : P.d ≤ (P.d - 1 + 1) * (ordinaryTraceOrder (X := CMfd.of (n := n) G) A0.N A0.ideal x' - A0.d) ↔
      P.d ≤ (P.d - 1 + 1) * (ordinaryTraceOrder (X := CMfd.of (n := n) G) B0.N B0.ideal x' - B0.d) := by
    constructor
    · intro ha
      have h1 := (hexA P.d).mpr ha
      rw [← hdA] at h1
      have h2 := isDivNearAlong_mark_of_stage hm hQB hQA hcos.symm hDB hDA hzB hzA hzD
        (fun j => (hdimQ z hzc j).symm) h1
      rw [hdB] at h2
      exact (hexB P.d).mp h2
    · intro hb
      have h1 := (hexB P.d).mpr hb
      rw [← hdB] at h1
      have h2 := isDivNearAlong_mark_of_stage hm hQA hQB hcos hDA hDB hzA hzB hzD (hdimQ z hzc) h1
      rw [hdA] at h2
      exact (hexA P.d).mp h2
  have hcA := fun e => HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder_cosupport_iff (X := CMfd.of (n := n) G)
    hA0.isWellFormed.isClosedSubmanifold_N hA0.isWellFormed.isCoherent hA0.isNonzeroAlongAt
    (A0.cosupp_subset_N hx'A) e
  have hx'B : x' ∈ B0.cosupp := by
    show x' ∈ cosupport n ((Subtype.val : G → X) ⁻¹' Q.N) (GermIdeal.pullback (m := n) (Subtype.val : G → X) Q.ideal) Q.d
    rw [hcosQ]
    exact hxQc
  have hcB := fun e => HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder_cosupport_iff (X := CMfd.of (n := n) G)
    hB0.isWellFormed.isClosedSubmanifold_N hB0.isWellFormed.isCoherent hB0.isNonzeroAlongAt
    (B0.cosupp_subset_N hx'B) e
  have hA0d : A0.d = P.d := rfl
  have hB0d : B0.d = P.d := hd
  rw [hA0d, hB0d, le_mul_sub_iff _ _ hd1, le_mul_sub_iff _ _ hd1, ← hcA, ← hcB] at key
  have e1 : x' ∈ cosupport n A0.N A0.ideal (P.d + 1) ↔ x ∈ cosupport n P.N P.ideal (P.d + 1) := by
    show x' ∈ cosupport n ((Subtype.val : G → X) ⁻¹' P.N) (GermIdeal.pullback (m := n) (Subtype.val : G → X) P.ideal)
      (P.d + 1) ↔ _
    rw [hcosP]
    rfl
  have e2 : x' ∈ cosupport n B0.N B0.ideal (P.d + 1) ↔ x ∈ cosupport n Q.N Q.ideal (P.d + 1) := by
    show x' ∈ cosupport n ((Subtype.val : G → X) ⁻¹' Q.N) (GermIdeal.pullback (m := n) (Subtype.val : G → X) Q.ideal)
      (P.d + 1) ↔ _
    rw [hcosQ]
    rfl
  exact e1.symm.trans (key.trans e2)

end LemmaMi

end

end Hironaka.HironakaG8P1ArcPair
