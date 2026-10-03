/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.NonmonomialOrderCanonical
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionOpen
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.CompanionReductionAlong
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.NonmonomialTransformAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.Invariant.StepOneRegime
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The companion phase of the general step after the start of a run

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2a of Proposition `pr:resol` ("By Step 1 we can resolve the
marked ideal of maximal order `O(𝓘, μ)`"); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Step II.B.

At a point `y` of order `o = ν(y) ≥ 1` along a canonical segment `T` of the general step's value `f`, the value is read off
the companion ideal `𝓞(𝔪_{T₀}|_W, o)` formed at the start `T₀` of the run of `y` in the regime `OrdRegime 𝔪 o`, on an open
set `W` where `ν ≤ o`, along the restricted tail `T₁|_W` (`T = T₀ T₁`).  This module proves, for every value function whose
order dominates `ν` (`NonmonomialOrderCanonical.OrdMonotone`), that this restricted tail is a multiple test blow-up of the
companion ideal -- the test-tower half of the general step's canonical-tail theorem, and the hypothesis of the mask theorem
`NonmonomialOrderRegime.ordRegime_and_le_regimeRun` -- and its consequence that nearby points of the same order started no
later:

* `E_geoTransformAlong_congr`; **`cosupp_companionOf_geoTransformAlong`**: along a multiple test blow-up of the companion
  ideal, `cosupp 𝓞_T = {ν ≥ o} ∩ cosupp 𝔪_T` (the inclusion `⊆` is `NonmonomialOrderLocal.companionOf_tower_facts`);
* **`isGeoTestTower_companion_of_canonical`**: if `T₀ T₁` is a multiple test blow-up of `𝔪` and a canonical segment of `f`,
  `W` an open set of the last stage of `T₀` with `ν ≤ o` on the cosupport over it (`o ≥ 1`), and some point has run
  `≥ length T₁` in the regime `o`, then `T₁|_W` is a multiple test blow-up of `𝓞(𝔪_{T₀}|_W, o)` (every centre of `T₁` is
  empty or the maximum locus of `f`, which lies in `{ν ≥ o}` while some image of that point has order `o`);
* `ordMask 𝔪 o`: the open set `{ν ≤ o}` (complement of the closure of `{ν ≥ o + 1}`, which is closed on the domain,
  `mem_ordMask_iff`); **`ordRegime_start`**: the image of a point at the start of its run is in the regime and in
  the mask there
* **`isGeoTestTower_companion_tail_of_canonical`**: with `T₀ = head T r`, `T₁ = tail T r` (`r` the run of `y`) and
  `W = ordMask 𝔪_{T₀} o`, the restricted tail is a multiple test blow-up of the companion ideal;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.NonmonomialOrderTail

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.CompanionRebase Hironaka.GermIdealOrder Hironaka.BlowupTowers Hironaka.DivisorExponentAlong Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealRestrictOpen Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderCanonical
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### The cosupport of the companion ideal along its multiple test blow-ups -/

section Companion

/-- **The divisor of a transform only depends on the divisor**: marked ideals with the same `E` have transforms with the
same `E` along every tower. Duplicate of `MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq` (the same
statement, proved earlier), kept per the no-delete rule. -/
theorem E_geoTransformAlong_congr {X : CMfd.{u} n} {𝔪 𝔫 : MarkedIdeal n X} (hE : 𝔪.E = 𝔫.E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), (geoTransformAlong 𝔪 T).E = (geoTransformAlong 𝔫 T).E
  | _, .refl => hE
  | _, .step T C π _ => by
      show ((geoTransformAlong 𝔪 T).geoTransform C π).E = ((geoTransformAlong 𝔫 T).geoTransform C π).E
      rw [geoTransform_E, geoTransform_E, E_geoTransformAlong_congr hE T]

/-- **The cosupport of the companion ideal along its multiple test blow-ups** (`𝔫` in the domain, `n > 0`, `o ≥ 1`,
`ν ≤ o` on `cosupp 𝔫`): `cosupp 𝓞(𝔫, o)_T = {ν_{𝔫_T} ≥ o} ∩ cosupp 𝔫_T`.  The inclusion `⊆` is
`NonmonomialOrderLocal.companionOf_tower_facts`; for `⊇`, `cosupp 𝓞_T = cosupp(𝓝_T|_{N_T}, o) ∩ cosupp 𝔫_T`
(`CompanionOpen.companionOf_reduction`) and the transform `𝓝_T` of `(N, E, 𝓝, o)` lies in the nonmonomial part of `𝔫_T`
(`NonmonomialTransformAlong.nonmonomialPart_geoTransformAlong_along`). -/
theorem cosupp_companionOf_geoTransformAlong (hn : 0 < n) {Z : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Z}
    (h : IsInvDomain k 𝔫) {o : ℕ} (ho : 1 ≤ o) (hbound : ∀ x ∈ 𝔫.cosupp, x ∉ ordGe 𝔫 (o + 1)) {Y : CMfd.{u} n}
    (T : BlowupTower Z Y) (hT : IsGeoTestTower (companionOf n 𝔫 o) T) :
    (geoTransformAlong (companionOf n 𝔫 o) T).cosupp = ordGe (geoTransformAlong 𝔫 T) o ∩ (geoTransformAlong 𝔫 T).cosupp := by
  obtain ⟨-, -, hNeq, -, hL, -, -, -⟩ :=
    NonmonomialTransformAlong.nonmonomialPart_geoTransformAlong_along hn 𝔫 h.isWellFormed h.isNonzeroAlongAt ho
      hbound T hT
  obtain ⟨-, -, -, hcos⟩ := CompanionOpen.companionOf_reduction hn h.isWellFormed h.isNonzeroAlongAt ho hbound T hT
  refine Set.Subset.antisymm (companionOf_tower_facts hn h ho hbound T hT).2.2 ?_
  rintro z ⟨hz1, hz2⟩
  rw [hcos]
  refine ⟨?_, hz2⟩
  show z ∈ cosupport n _ _ _
  rw [hNeq, d_geoTransformAlong]
  exact ⟨hz1.1, fun g hg => hz1.2 g (hL z g hg)⟩

end Companion

/-! ### The restricted tail is a multiple test blow-up of the companion ideal -/

section Tail

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
  {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The restricted tail is a multiple test blow-up of the companion ideal** (`𝔪` in the domain, `n > 0`, `o ≥ 1`): let
`T₀ T₁` be a multiple test blow-up of `𝔪` and a canonical segment of `f` (whose order dominates `ν`), `W` an open set of
the last stage of `T₀` with `ν ≤ o` at the points of the cosupport over `W`, and `y` a point whose run in the regime
`OrdRegime 𝔪 o` is at least the length of `T₁`.  Then `T₁|_W` is a multiple test blow-up of `𝓞(𝔪_{T₀}|_W, o)`.  Induction
along `T₁`: the image of `y` before the last step is in the regime, so the last centre (empty or the maximum locus of `f`)
lies in `{ν ≥ o}` (`NonmonomialOrderCanonical.subset_ordGe_of_canonical`); its trace over `W` is admissible for the transform
of `𝔪_{T₀}|_W` and lies in `{ν ≥ o}`, i.e. in the cosupport of the companion's transform
(`cosupp_companionOf_geoTransformAlong`), whose divisor is the same. -/
theorem isGeoTestTower_companion_of_canonical (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f)
    {o : ℕ} (ho : 1 ≤ o) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (W : Opens Y₀)
    (hbound : ∀ x ∈ (geoTransformAlong 𝔪 T₀).cosupp, x ∈ W → x ∉ ordGe (geoTransformAlong 𝔪 T₀) (o + 1)) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y), IsGeoTestTower 𝔪 (T₀.append T₁) → IsCanonical 𝔪 f (T₀.append T₁) →
      ∀ y : Y, T₁.length ≤ regimeRun (OrdRegime 𝔪 o) (T₀.append T₁) y →
        IsGeoTestTower (companionOf n (M := CMfd.of (n := n) W)
          (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong 𝔪 T₀)) o) (restrict W T₁)
  | _, .refl, _, _, _, _ => trivial
  | _, .step S C π hπ, hT, hcan, y, hrun => by
      have hT' : IsGeoTestTower 𝔪 (.step (T₀.append S) C π hπ) := hT
      have hcan' : IsCanonical 𝔪 f (T₀.append S) ∧
          (C = ∅ ∨ C = maxLocus (f (T₀.append S)) (geoTransformAlong 𝔪 (T₀.append S)).cosupp) := hcan
      have hrun' : S.length + 1 ≤ regimeRun (OrdRegime 𝔪 o) (.step (T₀.append S) C π hπ) y := by
        rw [BlowupTower.length_step] at hrun
        exact hrun
      -- the image of `y` before the last step is in the regime, with run at least `length S`
      have hP : OrdRegime 𝔪 o (T₀.append S) (π y) := by
        by_contra hP
        rw [regimeRun_step_of_not (OrdRegime 𝔪 o) _ C π hπ hP] at hrun'
        omega
      rw [regimeRun_step_of (OrdRegime 𝔪 o) _ C π hπ hP] at hrun'
      have ih := isGeoTestTower_companion_of_canonical hn h hf ho T₀ W hbound S hT'.1 hcan'.1 (π y) (by omega)
      refine ⟨ih, ?_⟩
      -- the trace of `C` is admissible for the transform of the companion ideal
      obtain ⟨hT₀, hTS⟩ := (isGeoTestTower_append_iff 𝔪 T₀ (.step S C π hπ)).mp hT
      have hS₀ : IsGeoTestTower (geoTransformAlong 𝔪 T₀) S := hTS.1
      have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
      have hdomS := InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom₀ S hS₀
      obtain ⟨-, hadm⟩ := isGeoTestTower_restrict W hdom₀.isWellFormed.isClosedSubmanifold_N
        hdom₀.isWellFormed.isCoherent _ hTS
      have hW := InvDomainTowerAlong.isInvDomain_pullback_val W hdom₀
      have hboundW : ∀ x ∈ (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong 𝔪 T₀)).cosupp,
          x ∉ ordGe (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong 𝔪 T₀))
            (o + 1) := by
        intro x hx hx'
        rw [cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
          hdom₀.isWellFormed.isCoherent hg)] at hx
        exact hbound x hx x.2
          ((mem_ordGe_pullback_val_iff hn hdom₀.isWellFormed hdom₀.isNonzeroAlongAt W (o + 1) x).mp hx')
      have hcos := cosupp_companionOf_geoTransformAlong (Z := CMfd.of (n := n) W) hn hW ho hboundW (restrict W S) ih
      have hsub := subset_ordGe_of_canonical h hf hT'.1 hcan'.2 hP.1 hP.2.ge
      rw [geoTransformAlong_append] at hsub
      refine ⟨hadm.1, fun x hx => ?_, ?_⟩
      · rw [hcos]
        refine ⟨?_, hadm.2.1 hx⟩
        rw [geoTransformAlong_restrict W hdom₀.isWellFormed.isClosedSubmanifold_N hdom₀.isWellFormed.isCoherent S hS₀]
        exact (mem_ordGe_pullback_val_iff hn hdomS.isWellFormed hdomS.isNonzeroAlongAt _ o x).mpr (hsub hx)
      · rw [E_geoTransformAlong_congr (companionAlong_E _ _ _ _ _ _) (restrict W S)]
        exact hadm.2.2

end Tail

/-! ### The mask `{ν ≤ o}` and the start of the run -/

section Start

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
  {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The mask of the order `o`**: the open set of the points of order `≤ o`, written as the complement of the closure of
`{ν ≥ o + 1}` so that it needs no hypothesis (on the domain that set is closed, `mem_ordMask_iff`). -/
def ordMask {M : CMfd.{u} n} (𝔪 : MarkedIdeal n M) (o : ℕ) : Opens M :=
  ⟨(closure (ordGe 𝔪 (o + 1)))ᶜ, isClosed_closure.isOpen_compl⟩

theorem mem_ordMask_iff (hn : 0 < n) {M : CMfd.{u} n} {𝔫 : MarkedIdeal n M} (h𝔫 : 𝔫.IsWellFormed)
    (hne : ∀ y ∈ 𝔫.N, IsNonzeroAlongAt 𝔫.N 𝔫.ideal y) (o : ℕ) (x : M) :
    x ∈ ordMask 𝔫 o ↔ x ∉ ordGe 𝔫 (o + 1) := by
  show x ∈ (closure (ordGe 𝔫 (o + 1)))ᶜ ↔ _
  rw [(isClosed_ordGe hn h𝔫 hne (o + 1)).closure_eq]
  rfl

/-- **The bound holds on the mask.** -/
theorem notMem_ordGe_of_mem_ordMask {M : CMfd.{u} n} {𝔫 : MarkedIdeal n M} {o : ℕ} {x : M} (hx : x ∈ ordMask 𝔫 o) :
    x ∉ ordGe 𝔫 (o + 1) :=
  fun h => hx (subset_closure h)

/-- **The restricted tail of a point is a multiple test blow-up of its companion ideal** (`𝔪` in the domain, `n > 0`):
along a multiple test blow-up `T` of `𝔪` which is a canonical segment of `f`, let `y` be a point of the cosupport of order
`o ≥ 1` and `r` its run in the regime `o`; split `T = T₀ T₁` at `r` (`T₀ = head T r`, `T₁ = tail T r`).  Then
`T₁|_W` is a multiple test blow-up of `𝓞(𝔪_{T₀}|_W, o)` for `W = ordMask 𝔪_{T₀} o`. -/
theorem isGeoTestTower_companion_tail_of_canonical (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f)
    {o : ℕ} (ho : 1 ≤ o) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 f T)
    (y : Y) :
    IsGeoTestTower (companionOf n
        (M := CMfd.of (n := n) (ordMask (geoTransformAlong 𝔪 (BlowupTowerSplit.head T (regimeRun (OrdRegime 𝔪 o) T y))) o))
        (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong 𝔪
          (BlowupTowerSplit.head T (regimeRun (OrdRegime 𝔪 o) T y))) o → _)
          (geoTransformAlong 𝔪 (BlowupTowerSplit.head T (regimeRun (OrdRegime 𝔪 o) T y)))) o)
      (restrict (ordMask (geoTransformAlong 𝔪 (BlowupTowerSplit.head T (regimeRun (OrdRegime 𝔪 o) T y))) o)
        (BlowupTowerSplit.tail T (regimeRun (OrdRegime 𝔪 o) T y))) := by
  set j := regimeRun (OrdRegime 𝔪 o) T y with hj
  have hT' : IsGeoTestTower 𝔪 ((BlowupTowerSplit.head T j).append (BlowupTowerSplit.tail T j)) := by
    rw [BlowupTowerSplit.head_append_tail]
    exact hT
  have hcan' : IsCanonical 𝔪 f ((BlowupTowerSplit.head T j).append (BlowupTowerSplit.tail T j)) := by
    rw [BlowupTowerSplit.head_append_tail]
    exact hcan
  have hrun : (BlowupTowerSplit.tail T j).length ≤
      regimeRun (OrdRegime 𝔪 o) ((BlowupTowerSplit.head T j).append (BlowupTowerSplit.tail T j)) y := by
    rw [BlowupTowerSplit.length_tail, BlowupTowerSplit.head_append_tail, ← hj]
    exact min_le_left _ _
  exact isGeoTestTower_companion_of_canonical hn h hf ho (BlowupTowerSplit.head T j)
    (ordMask (geoTransformAlong 𝔪 (BlowupTowerSplit.head T j)) o) (fun _ _ hx => notMem_ordGe_of_mem_ordMask hx)
    (BlowupTowerSplit.tail T j) hT' hcan' y hrun

end Start

end

end Hironaka.NonmonomialOrderTail
