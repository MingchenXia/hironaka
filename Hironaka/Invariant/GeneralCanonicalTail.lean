/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.GeneralCompare
import Hironaka.Invariant.NonmonomialOrderMonomialCanonical
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.GeneralValue
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.MaxOrderValue
import Hironaka.Invariant.MonomialCaseAlong
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.MonomialStepAlong
import Hironaka.Invariant.NonmonomialOrderCanonical
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.StepOneCanonicalTail
import Hironaka.Invariant.StepOneNearby
import Hironaka.Invariant.StepOneRegime
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The canonical-tail theorem of the general step: lower data along canonical segments; the drop property

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 2a: at a point of order `o ≥ 1`
the value is that of the maximal-order invariant of the companion ideal formed where the point reached the order
`o`, along the rest of the resolution, "which is a canonical segment of it" -- near the point, the centres of a
canonical segment of the general value are empty or the maximum loci of the companion's invariant.

Let `𝔪` lie in the domain (`0 < n`), `M` a value function for the marked ideals of maximal order
(`MaxOrderValue.IsMaxOrderValue`) and `genInv M 𝔪` the general value (`GeneralValue`).  **Main theorem**
(`hasGenLowerData_of_isCanonical`): along every multiple test blow-up `T` of `𝔪` which is a canonical segment of `genInv M 𝔪`,
every point of the cosupport of positive order has lower data at the split of `T` at the start of its run
(`GeneralValue.GenLowerData`).

Proof: induction on the tower. After a further blowup `σ` along `C`, a point `y` whose image `σ y` is in the regime
of its order `o` has the split of `σ y` with the tail extended by `σ`; the trace of `C` on the restricted tail is
empty or the maximum locus of the companion's value (`MaxLocusLocal.preimage_maxLocus_eq_or` with the strictly
monotone `λ ↦ (o, λ)`): over the mask `W = {ν ≤ o}` the points of the companion's cosupport are the points of order
`o` (`mem_cosupp_compAt_iff`), their value is `(o, value of the companion formed at the start of σ y)` by the
comparison (`genInv_eq_of_mem_cosupp_compAt`: their own runs started no earlier -- `ordRegime_and_le_regimeRun` --,
the steps between the two starts miss their mask -- `exists_middle_ord`, from `centresAvoid_of_canonical` --, and
`GeneralCompare.genLowerValue_eq_rebase`), and the other points over the mask have smaller order. A point leaving
its regime starts a new run with lower data along the empty tail (`genLowerData_refl`).

Consequence (`genInv_drop`): along a canonical segment of `genInv M 𝔪` which is a multiple test blow-up, after one
more step every point of the new cosupport lies over the cosupport, with a smaller value over the centre and the
same value off it -- properties (3) and (4) of `hir:centre-function` for the general value -- at positive order from
the lower data and the order bookkeeping of `NonmonomialOrderCanonical`, at order `0` by
`NonmonomialOrderMonomialCanonical`.

## Main results

* `mem_cosupp_compAt_iff`, `genLowerData_refl`, `exists_middle_ord`, `genLowerValue_eq_rebase_of_eq`,
  `genInv_eq_of_mem_cosupp_compAt`: tools;
* `HasGenLowerData`, `genLowerData_step`, **`hasGenLowerData_of_isCanonical`**: the canonical-tail theorem;
* `ordZeroValue_genInv`, **`genInv_drop`**: the drop property of the general value along canonical test segments.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralCanonicalTail

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.CompanionRebase Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism Hironaka.RestrictEmptyTower Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderCanonical Hironaka.NonmonomialOrderTail Hironaka.HomogenizedIdealAlong Hironaka.MaxOrderValue Hironaka.GeneralValue Hironaka.GeneralCompare Hironaka.InvDomainCompanion Hironaka.StepOneWellFounded
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### Tools -/

section Tools

variable {X : CMfd.{u} n} {k : ℕ} {𝔪 : MarkedIdeal n X}

/-- **The cosupport of the companion ideal along a restricted tail**: if `T₀` and `T₁` are multiple test blow-ups of `𝔪` and of
`𝔪_{T₀}` (in the domain, `0 < n`, `o ≥ 1`) and `T₁|_W` is one of the companion ideal formed at `T₀` on its mask `W`, a point over
`W` lies in the cosupport of the companion's transform iff it lies in the cosupport of `𝔪_{T₀ T₁}` and has order `o`. -/
theorem mem_cosupp_compAt_iff (hn : 0 < n) (h : IsInvDomain k 𝔪) {o : ℕ} (ho : 1 ≤ o) {Y₀ Y : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (hT₀ : IsGeoTestTower 𝔪 T₀)
    (hT₁ : IsGeoTestTower (geoTransformAlong 𝔪 T₀) T₁)
    (hTW : IsGeoTestTower (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁))
    (p : openPreimage T₁ (ordMask (geoTransformAlong 𝔪 T₀) o)) :
    p ∈ (geoTransformAlong (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁)).cosupp ↔
      (p : Y) ∈ (geoTransformAlong (geoTransformAlong 𝔪 T₀) T₁).cosupp ∧
        nmOrd (geoTransformAlong (geoTransformAlong 𝔪 T₀) T₁) p = o := by
  have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  have hdom₁ := InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom₀ T₁ hT₁
  have hdomW := InvDomainTowerAlong.isInvDomain_pullback_val (ordMask (geoTransformAlong 𝔪 T₀) o) hdom₀
  have hhol : ∀ x g, (geoTransformAlong 𝔪 T₀).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom₀.isWellFormed.isCoherent hg
  have hbound : ∀ x ∈ (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong 𝔪 T₀) o → Y₀)
      (geoTransformAlong 𝔪 T₀)).cosupp, x ∉ ordGe (M := CMfd.of (n := n) (ordMask (geoTransformAlong 𝔪 T₀) o))
        (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong 𝔪 T₀) o → Y₀) (geoTransformAlong 𝔪 T₀))
        (o + 1) := by
    intro x _ hx
    rw [mem_ordGe_pullback_val_iff hn hdom₀.isWellFormed hdom₀.isNonzeroAlongAt] at hx
    exact (mem_ordMask_iff hn hdom₀.isWellFormed hdom₀.isNonzeroAlongAt o x).mp x.2 hx
  have hcos := cosupp_companionOf_geoTransformAlong hn hdomW ho hbound _ hTW
  have hrest := geoTransformAlong_restrict (U := ordMask (geoTransformAlong 𝔪 T₀) o)
    hdom₀.isWellFormed.isClosedSubmanifold_N hdom₀.isWellFormed.isCoherent T₁ hT₁
  have hhol₁ : ∀ x g, (geoTransformAlong (geoTransformAlong 𝔪 T₀) T₁).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom₁.isWellFormed.isCoherent hg
  -- the bound persists over the mask
  have hle : (p : Y) ∈ (geoTransformAlong (geoTransformAlong 𝔪 T₀) T₁).cosupp →
      nmOrd (geoTransformAlong (geoTransformAlong 𝔪 T₀) T₁) p ≤ o := fun hp =>
    nmOrd_le_of_notMem (notMem_ordGe_of_mask hn hdom₀ ho _ (fun x _ hx => (mem_ordMask_iff hn hdom₀.isWellFormed
      hdom₀.isNonzeroAlongAt o x).mp hx) T₁ hT₁ hTW (p : Y) hp p.2)
  show p ∈ (geoTransformAlong (companionOf n (M := CMfd.of (n := n) (ordMask (geoTransformAlong 𝔪 T₀) o))
    (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong 𝔪 T₀) o → Y₀) (geoTransformAlong 𝔪 T₀)) o)
    (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁)).cosupp ↔ _
  rw [hcos, hrest, mem_inter_iff, mem_ordGe_pullback_val_iff hn hdom₁.isWellFormed hdom₁.isNonzeroAlongAt,
    cosupp_pullback_val _ hhol₁, mem_preimage]
  constructor
  · rintro ⟨hge, hp⟩
    refine ⟨hp, le_antisymm (hle hp) ?_⟩
    exact (mem_ordGe_iff hdom₁.isWellFormed hdom₁.isNonzeroAlongAt
      ((geoTransformAlong (geoTransformAlong 𝔪 T₀) T₁).cosupp_subset_N hp) o).mp hge
  · rintro ⟨hp, hpo⟩
    refine ⟨?_, hp⟩
    exact (mem_ordGe_iff hdom₁.isWellFormed hdom₁.isNonzeroAlongAt
      ((geoTransformAlong (geoTransformAlong 𝔪 T₀) T₁).cosupp_subset_N hp) o).mpr hpo.ge

variable {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

variable (M) in
/-- **Lower data along the empty tail**: at a point of the cosupport of order `o ≥ 1` along a multiple test blow-up `T`, the
companion ideal formed at the last stage gives lower data along the empty tail. -/
theorem genLowerData_refl (hn : 0 < n) (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) {y : Y} (hy : y ∈ (geoTransformAlong 𝔪 T).cosupp) {o : ℕ}
    (hyo : nmOrd (geoTransformAlong 𝔪 T) y = o) (ho : 1 ≤ o) : GenLowerData M k 𝔪 o T .refl y := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hyW : y ∈ ordMask (geoTransformAlong 𝔪 T) o :=
    (mem_ordMask_iff hn hdomT.isWellFormed hdomT.isNonzeroAlongAt o y).mpr fun hy1 => by
      have := (mem_ordGe_iff hdomT.isWellFormed hdomT.isNonzeroAlongAt
        ((geoTransformAlong 𝔪 T).cosupp_subset_N hy) (o + 1)).mp hy1
      omega
  refine ⟨hyW, isInvDomain_compAt hn ho T hdomT, isMaximalOrderAlong_compAt hn o T hdomT, trivial, ?_⟩
  exact (mem_cosupp_compAt_iff hn h ho T .refl hT trivial trivial ⟨y, hyW⟩).mpr ⟨hy, hyo⟩

variable {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The middle part between two start stages misses the earlier mask** (the analogue of
`StepOneCanonicalTail.exists_middle` for the order of the nonmonomial part): along a canonical segment `T` of a value function
whose order dominates `ν`, which is a multiple test blow-up, let `z` have order `o` and run `rz ≤ rq ≤ length T`.  The tower
from the stage `rq` steps before the end to the start of `z` misses the mask `{ν ≤ o}` of the former. -/
theorem exists_middle_ord (hn : 0 < n) (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 f T) {z : Y}
    (hz : z ∈ (geoTransformAlong 𝔪 T).cosupp) {o : ℕ} (hzo : nmOrd (geoTransformAlong 𝔪 T) z = o) {rz rq : ℕ}
    (hrz : regimeRun (OrdRegime 𝔪 o) T z = rz) (hle : rz ≤ rq) (hrq : rq ≤ T.length) :
    ∃ Mt : BlowupTower (split T rq).1 (split T rz).1, (head T rq).append Mt = head T rz ∧
      Mt.append (tail T rz) = tail T rq ∧ CentresAvoid (ordMask (geoTransformAlong 𝔪 (head T rq)) o) Mt := by
  rcases hle.lt_or_eq with hlt | heq
  · have hrzlt : rz < T.length := lt_of_lt_of_le hlt hrq
    -- the last step before the start of `z`
    obtain ⟨τ, hτ₁, hτ₂⟩ := StepOneNearby.exists_split_le T (a := rz) (b := rz + 1) (Nat.le_succ rz)
    have hτlen : τ.length = 1 := by
      have h := congrArg BlowupTower.length hτ₁
      rw [BlowupTower.length_append, length_head, length_head] at h
      omega
    obtain ⟨Cm, πm, hπm, rfl⟩ := StepOneCanonicalTail.exists_eq_step_refl τ hτlen
    obtain ⟨M₂, hM₁, hM₂⟩ := StepOneNearby.exists_split_le T (a := rz + 1) (b := rq) (by omega)
    refine ⟨M₂.append (.step .refl Cm πm hπm), ?_, ?_, ?_⟩
    · rw [← BlowupTower.append_assoc, hM₁, hτ₁]
    · rw [BlowupTower.append_assoc, hτ₂, hM₂]
    · show CentresAvoid _ (.step M₂ Cm πm hπm)
      -- the image of `z` one stage before its start: in the cosupport, of order at least `o + 1`
      obtain ⟨hw, hwo⟩ := mem_cosupp_and_succ_le_before_start hn h hf T hT hcan hz hzo (j := rz + 1)
        (by rw [hrz]) (by rw [hrz]; exact hrzlt)
      rw [← hM₁] at hw hwo
      have heq : (head T rq).append (.step M₂ Cm πm hπm) = head T rz := by
        rw [← hτ₁, ← hM₁]
        rfl
      have hTh : IsGeoTestTower 𝔪 ((head T rq).append (.step M₂ Cm πm hπm)) := by
        rw [heq]; exact ((isGeoTestTower_iff_head_tail 𝔪 T rz).mp hT).1
      have hcanh : IsCanonical 𝔪 f ((head T rq).append (.step M₂ Cm πm hπm)) := by
        rw [heq]; exact isCanonical_head _ _ T rz hcan
      have hTq : IsGeoTestTower 𝔪 (head T rq) := ((isGeoTestTower_iff_head_tail 𝔪 T rq).mp hT).1
      have hdomq := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (head T rq) hTq
      exact (centresAvoid_of_canonical hn h hf (head T rq) (ordMask (geoTransformAlong 𝔪 (head T rq)) o)
        (fun x _ hx => (mem_ordMask_iff hn hdomq.isWellFormed hdomq.isNonzeroAlongAt o x).mp hx) M₂ Cm πm hπm hTh
        hcanh hw hwo).1
  · subst heq
    obtain ⟨Mt, h₁, h₂⟩ := StepOneNearby.exists_split_le T (le_refl rz)
    refine ⟨Mt, h₁, h₂, StepOneCanonicalTail.centresAvoid_of_length_eq_zero _ Mt ?_⟩
    have h := congrArg BlowupTower.length h₁
    rw [BlowupTower.length_append] at h
    omega

/-- **The comparison of `GeneralCompare.genLowerValue_eq_rebase`, with the stages given by equations.** -/
theorem genLowerValue_eq_rebase_of_eq (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) {o : ℕ}
    (ho : 1 ≤ o) {Y₁ Y₀ Y : CMfd.{u} n} (T₀' : BlowupTower X Y₁) (Mt : BlowupTower Y₁ Y₀) (T₁ : BlowupTower Y₀ Y)
    {T₀ : BlowupTower X Y₀} (h₀ : T₀'.append Mt = T₀) {T₁' : BlowupTower Y₁ Y} (h₁ : Mt.append T₁ = T₁')
    (hT : IsGeoTestTower 𝔪 T₀) (hMt : CentresAvoid (ordMask (geoTransformAlong 𝔪 T₀') o) Mt) {p : Y}
    (hd : GenLowerData M k 𝔪 o T₀' T₁' p) (hpW : T₁.proj p ∈ ordMask (geoTransformAlong 𝔪 T₀) o)
    (hcan₀ : IsCanonical (compAt 𝔪 o T₀) (M (compAt 𝔪 o T₀)) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁)) :
    genLowerValue M 𝔪 o T₀' T₁' p =
        ((M (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁) ⟨p, hpW⟩ : Λ) : WithTop Λ) ∧
      (⟨p, hpW⟩ : openPreimage T₁ (ordMask (geoTransformAlong 𝔪 T₀) o)) ∈
        (geoTransformAlong (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁)).cosupp := by
  subst h₀ h₁
  exact genLowerValue_eq_rebase hM hn h ho T₀' Mt T₁ hT hMt hd hpW hcan₀

end Tools

/-! ### The canonical-tail theorem -/

section Tail

variable {X : CMfd.{u} n} {k : ℕ} {𝔪 : MarkedIdeal n X} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Every point of the cosupport of positive order has lower data** at the split of the tower at the start of its run. -/
def HasGenLowerData (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) (k : ℕ)
    (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) : Prop :=
  ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, ∀ o : ℕ, nmOrd (geoTransformAlong 𝔪 T) y = o → 1 ≤ o →
    GenLowerData M k 𝔪 o (head T (regimeRun (OrdRegime 𝔪 o) T y)) (tail T (regimeRun (OrdRegime 𝔪 o) T y)) y

/-- **The value at a point of the companion's cosupport, through the reference point's companion ideal**: along a canonical
segment `T` of the general value which is a multiple test blow-up, with lower data at every point of positive order, let `y₀`
have order `o ≥ 1` and run `r`, with `T_r|_W` a canonical segment of the companion ideal formed at the start of `y₀`.  At every
point `q` of the cosupport of that companion ideal along the restricted tail, the general value is `(o, M(q))`. -/
theorem genInv_eq_of_mem_cosupp_compAt (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 (genInv M 𝔪) T)
    (hD : HasGenLowerData M k 𝔪 T) {y₀ : Y} (hy₀ : y₀ ∈ (geoTransformAlong 𝔪 T).cosupp) {o : ℕ}
    (hy₀o : nmOrd (geoTransformAlong 𝔪 T) y₀ = o) (ho : 1 ≤ o) {r : ℕ} (hr : regimeRun (OrdRegime 𝔪 o) T y₀ = r)
    (hcan₀ : IsCanonical (compAt 𝔪 o (head T r)) (M (compAt 𝔪 o (head T r)))
      (restrict (ordMask (geoTransformAlong 𝔪 (head T r)) o) (tail T r)))
    (q : openPreimage (tail T r) (ordMask (geoTransformAlong 𝔪 (head T r)) o))
    (hq : q ∈ (geoTransformAlong (compAt 𝔪 o (head T r))
      (restrict (ordMask (geoTransformAlong 𝔪 (head T r)) o) (tail T r))).cosupp) :
    genInv M 𝔪 T q = toLex (o, (toLex (Sum.inr ((M (compAt 𝔪 o (head T r))
      (restrict (ordMask (geoTransformAlong 𝔪 (head T r)) o) (tail T r)) q : Λ) : WithTop Λ)) :
        WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ)) := by
  have hf : OrdMonotone 𝔪 (genInv M 𝔪) := ordMonotone_genInv M 𝔪
  have hTW := isGeoTestTower_companion_tail_of_canonical hn h hf ho T hT hcan y₀
  rw [hr] at hTW
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_iff_head_tail 𝔪 T r).mp hT
  have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h (head T r) hT₀
  have hq' := (mem_cosupp_compAt_iff hn h ho (head T r) (tail T r) hT₀ hT₁ hTW q).mp hq
  rw [← geoTransformAlong_head_tail 𝔪 T r] at hq'
  obtain ⟨hqcos, hqo⟩ := hq'
  -- the run of `q` is at least `r`
  have hTa : IsGeoTestTower 𝔪 ((head T r).append (tail T r)) := by rw [head_append_tail]; exact hT
  have hrun := ordRegime_and_le_regimeRun hn h ho (head T r) (ordMask (geoTransformAlong 𝔪 (head T r)) o)
    (fun x _ hx => (mem_ordMask_iff hn hdom₀.isWellFormed hdom₀.isNonzeroAlongAt o x).mp hx) (tail T r) hTa hTW
    (q : Y) (by rw [head_append_tail]; exact hqcos) q.2 (le_of_eq (by rw [head_append_tail, hqo]))
  rw [head_append_tail] at hrun
  have hrT : r ≤ T.length := hr ▸ regimeRun_le_length _ T y₀
  have hrle : r ≤ regimeRun (OrdRegime 𝔪 o) T (q : Y) := by
    have h2 := hrun.2
    rw [length_tail, min_eq_left hrT] at h2
    exact h2
  obtain ⟨Mt, h₀, h₁, hMt⟩ := exists_middle_ord hn h hf T hT hcan hy₀ hy₀o hr hrle (regimeRun_le_length _ T _)
  have hdq := hD q hqcos o hqo ho
  obtain ⟨hval, -⟩ := genLowerValue_eq_rebase_of_eq hM hn h ho _ Mt (tail T r) h₀ h₁ hT₀ hMt hdq q.2 hcan₀
  rw [genInv_of_nmOrd_ne_zero M 𝔪 T hqo (by omega), hval]

/-- **The lower data of a point whose image keeps its regime**: after a further blowup along `C`, a point `y` of order
`o ≥ 1` whose image is in the regime of order `o` has lower data at the split of its image followed by the blowup. -/
theorem genLowerData_step (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) {Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower 𝔪 (.step T C π hπ)) (hcan : IsCanonical 𝔪 (genInv M 𝔪) (.step T C π hπ))
    (hD : HasGenLowerData M k 𝔪 T) {y : Z} (hy : y ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp) {o : ℕ}
    (hyo : nmOrd (geoTransformAlong 𝔪 (.step T C π hπ)) y = o) (ho : 1 ≤ o) (hreg : OrdRegime 𝔪 o T (π y)) :
    GenLowerData M k 𝔪 o (head T (regimeRun (OrdRegime 𝔪 o) T (π y)))
      (.step (tail T (regimeRun (OrdRegime 𝔪 o) T (π y))) C π hπ) y := by
  have hf : OrdMonotone 𝔪 (genInv M 𝔪) := ordMonotone_genInv M 𝔪
  obtain ⟨hTT, -⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
  have hcanT : IsCanonical 𝔪 (genInv M 𝔪) T := hcan.1
  have hC : C = ∅ ∨ C = maxLocus (genInv M 𝔪 T) (geoTransformAlong 𝔪 T).cosupp := hcan.2
  obtain ⟨hW, hdom, hmax, hcan₀, hcos₀⟩ := hD (π y) hreg.1 o hreg.2 ho
  have hTW' := isGeoTestTower_companion_tail_of_canonical hn h hf ho (.step T C π hπ) hT hcan y
  rw [regimeRun_step_of _ T C π hπ hreg] at hTW'
  have hTW : IsGeoTestTower (compAt 𝔪 o (head T (regimeRun (OrdRegime 𝔪 o) T (π y))))
      (restrict (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T (π y)))) o)
        (.step (tail T (regimeRun (OrdRegime 𝔪 o) T (π y))) C π hπ)) := hTW'
  have hTW₀ := ((isGeoTestTower_step_iff _ _ _ _ _).mp hTW).1
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_iff_head_tail 𝔪 T (regimeRun (OrdRegime 𝔪 o) T (π y))).mp hTT
  have hT₁' : IsGeoTestTower (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T (π y))))
      (.step (tail T (regimeRun (OrdRegime 𝔪 o) T (π y))) C π hπ) := by
    have h2 := ((isGeoTestTower_iff_head_tail 𝔪 (.step T C π hπ) (regimeRun (OrdRegime 𝔪 o) T (π y) + 1)).mp hT).2
    exact h2
  refine ⟨hW, hdom, hmax, ?_, ?_⟩
  · show IsCanonical (compAt 𝔪 o (head T (regimeRun (OrdRegime 𝔪 o) T (π y))))
        (M (compAt 𝔪 o (head T (regimeRun (OrdRegime 𝔪 o) T (π y)))))
        (restrict (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T (π y)))) o)
          (tail T (regimeRun (OrdRegime 𝔪 o) T (π y)))) ∧
      (((Subtype.val : openPreimage (tail T (regimeRun (OrdRegime 𝔪 o) T (π y)))
          (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T (π y)))) o) → Y) ⁻¹' C) = ∅ ∨
        ((Subtype.val : openPreimage (tail T (regimeRun (OrdRegime 𝔪 o) T (π y)))
          (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T (π y)))) o) → Y) ⁻¹' C) =
          maxLocus (M (compAt 𝔪 o (head T (regimeRun (OrdRegime 𝔪 o) T (π y))))
            (restrict (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T (π y)))) o)
              (tail T (regimeRun (OrdRegime 𝔪 o) T (π y)))))
            (geoTransformAlong (compAt 𝔪 o (head T (regimeRun (OrdRegime 𝔪 o) T (π y))))
              (restrict (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T (π y)))) o)
                (tail T (regimeRun (OrdRegime 𝔪 o) T (π y))))).cosupp)
    refine ⟨hcan₀, ?_⟩
    rcases hC with hC | hC
    · left
      rw [hC]
      exact preimage_empty
    · rw [hC]
      have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h _ hT₀
      refine MaxLocusLocal.preimage_maxLocus_eq_or Subtype.val
        (φ := fun l : Λ => (toLex (o, (toLex (Sum.inr (l : WithTop Λ)) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ)) :
          ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))) ?_ ?_ ?_ ?_
      · intro a b hab
        rw [Prod.Lex.toLex_lt_toLex]
        exact Or.inr ⟨rfl, Sum.Lex.inr_lt_inr_iff.mpr (WithTop.coe_lt_coe.mpr hab)⟩
      · intro q hq
        have hq' := ((mem_cosupp_compAt_iff hn h ho _ _ hT₀ hT₁ hTW₀ q).mp hq).1
        rw [← geoTransformAlong_head_tail 𝔪 T] at hq'
        exact hq'
      · intro q hq
        exact genInv_eq_of_mem_cosupp_compAt hM hn h T hTT hcanT hD hreg.1 hreg.2 ho rfl hcan₀ q hq
      · intro p hp hps'
        refine ⟨⟨π y, hW⟩, hcos₀, genInv_lt_of_nmOrd_lt M 𝔪 ?_⟩
        rw [hreg.2]
        have hp' : (p : Y) ∈ (geoTransformAlong (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T (π y))))
            (tail T (regimeRun (OrdRegime 𝔪 o) T (π y)))).cosupp := by
          rw [← geoTransformAlong_head_tail 𝔪 T]; exact hp
        have hle : nmOrd (geoTransformAlong (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T (π y))))
            (tail T (regimeRun (OrdRegime 𝔪 o) T (π y)))) p ≤ o :=
          nmOrd_le_of_notMem (notMem_ordGe_of_mask hn hdom₀ ho _ (fun x _ hx => (mem_ordMask_iff hn
            hdom₀.isWellFormed hdom₀.isNonzeroAlongAt o x).mp hx) _ hT₁ hTW₀ (p : Y) hp' p.2)
        have hne : nmOrd (geoTransformAlong (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T (π y))))
            (tail T (regimeRun (OrdRegime 𝔪 o) T (π y)))) p ≠ o := fun heq =>
          hps' ((mem_cosupp_compAt_iff hn h ho _ _ hT₀ hT₁ hTW₀ p).mpr ⟨hp', heq⟩)
        rw [geoTransformAlong_head_tail 𝔪 T (regimeRun (OrdRegime 𝔪 o) T (π y))]
        omega
  · refine (mem_cosupp_compAt_iff hn h ho _ _ hT₀ hT₁' hTW ⟨y, hW⟩).mpr ⟨?_, ?_⟩
    · have e := geoTransformAlong_head_tail 𝔪 (.step T C π hπ) (regimeRun (OrdRegime 𝔪 o) T (π y) + 1)
      have e' : geoTransformAlong 𝔪 (.step T C π hπ) = geoTransformAlong (geoTransformAlong 𝔪
          (head T (regimeRun (OrdRegime 𝔪 o) T (π y)))) (.step (tail T (regimeRun (OrdRegime 𝔪 o) T (π y))) C π hπ) := e
      rw [← e']
      exact hy
    · have e := geoTransformAlong_head_tail 𝔪 (.step T C π hπ) (regimeRun (OrdRegime 𝔪 o) T (π y) + 1)
      have e' : geoTransformAlong 𝔪 (.step T C π hπ) = geoTransformAlong (geoTransformAlong 𝔪
          (head T (regimeRun (OrdRegime 𝔪 o) T (π y)))) (.step (tail T (regimeRun (OrdRegime 𝔪 o) T (π y))) C π hπ) := e
      rw [← e']
      exact hyo

variable (M) in
/-- **The canonical-tail theorem of the general step**: along every multiple test blow-up of `𝔪` which is a canonical segment
of the general value, every point of the cosupport of positive order has lower data at the split at the start of its run. -/
theorem hasGenLowerData_of_isCanonical (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → IsCanonical 𝔪 (genInv M 𝔪) T →
      HasGenLowerData M k 𝔪 T
  | _, .refl, hT, _ => by
      intro y hy o hyo ho
      exact genLowerData_refl M hn h .refl hT hy hyo ho
  | _, .step T C π hπ, hT, hcan => by
      have ih := hasGenLowerData_of_isCanonical hM hn h T ((isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT).1 hcan.1
      intro y hy o hyo ho
      by_cases hreg : OrdRegime 𝔪 o T (π y)
      · rw [regimeRun_step_of _ T C π hπ hreg]
        exact genLowerData_step hM hn h T C π hπ hT hcan ih hy hyo ho hreg
      · rw [regimeRun_step_of_not _ T C π hπ hreg]
        exact genLowerData_refl M hn h (.step T C π hπ) hT hy hyo ho

end Tail

/-! ### The drop property of the general value -/

section Drop

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) (𝔪 : MarkedIdeal n X)

/-- At the points of order `0` the general value is `(0, γ)` (the hypothesis `OrdZeroValue` of
`NonmonomialOrderMonomialCanonical`). -/
theorem ordZeroValue_genInv :
    NonmonomialOrderMonomialCanonical.OrdZeroValue 𝔪 (genInv M 𝔪)
      (fun w => toLex ((0 : ℕ), (toLex (Sum.inl w) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))) :=
  NonmonomialOrderMonomialCanonical.ordZeroValue_toLex 𝔪 (genSecond M 𝔪) fun T _ y _ h0 => by
    rw [genSecond, if_pos h0]
    rfl

variable {M 𝔪}

/-- **Properties (3) and (4) of the general value**: along a canonical segment of the general value which is a multiple test
blow-up, after one more step every point of the new cosupport lies over the cosupport, its value is smaller than that of its
image over the centre and equal to it off the centre. -/
theorem genInv_drop (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) {Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower 𝔪 (.step T C π hπ)) (hcan : IsCanonical 𝔪 (genInv M 𝔪) (.step T C π hπ)) :
    ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
      π z ∈ (geoTransformAlong 𝔪 T).cosupp ∧
        (π z ∈ C → genInv M 𝔪 (.step T C π hπ) z < genInv M 𝔪 T (π z)) ∧
        (π z ∉ C → genInv M 𝔪 (.step T C π hπ) z = genInv M 𝔪 T (π z)) := by
  intro z hz
  have hf : OrdMonotone 𝔪 (genInv M 𝔪) := ordMonotone_genInv M 𝔪
  obtain ⟨hTT, hCadm⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
  have hcanT : IsCanonical 𝔪 (genInv M 𝔪) T := hcan.1
  obtain ⟨hpz, hle⟩ := nmOrd_step_le_of_canonical hn h hf T C π hπ hT hcan.2 hz
  rcases Nat.eq_zero_or_pos (nmOrd (geoTransformAlong 𝔪 T) (π z)) with h0 | hpos
  · exact NonmonomialOrderMonomialCanonical.value_step_of_nmOrd_eq_zero hn h hf
      NonmonomialOrderMonomialCanonical.strictMono_toLex_zero_inl (ordZeroValue_genInv M 𝔪) T C π hπ hT hcan hz h0
  · have hD := hasGenLowerData_of_isCanonical M hM hn h T hTT hcanT
    have hreg : OrdRegime 𝔪 (nmOrd (geoTransformAlong 𝔪 T) (π z)) T (π z) := ⟨hpz, rfl⟩
    refine ⟨hpz, fun hzC => ?_, fun hzC => ?_⟩
    · rcases hle.lt_or_eq with hlt | heq
      · exact genInv_lt_of_nmOrd_lt M 𝔪 hlt
      · have hdz := genLowerData_step hM hn h T C π hπ hT hcan hD hz heq hpos hreg
        exact genInv_step_lt_of_mem 𝔪 hM T C π hπ hzC (by omega) heq hreg hdz
    · have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hTT
      have hzo : nmOrd (geoTransformAlong 𝔪 (.step T C π hπ)) z = nmOrd (geoTransformAlong 𝔪 T) (π z) :=
        nmOrd_geoTransform_of_notMem hn hdomT hCadm hπ hzC
      have hdz := genLowerData_step hM hn h T C π hπ hT hcan hD hz hzo hpos hreg
      exact genInv_step_of_notMem 𝔪 hM hn h T C π hπ hT hz hzC (by omega) rfl hdz

end Drop

end

end Hironaka.GeneralCanonicalTail
