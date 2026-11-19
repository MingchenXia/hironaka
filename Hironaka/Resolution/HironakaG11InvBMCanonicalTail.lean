import Hironaka.Resolution.HironakaG11InvBMRebase
import Hironaka.Invariant.StepOneCanonicalTail

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The canonical-tail theorem for Bierstone--Milman's lower family, modulo the anchor change (repair (B'), plan module 7)

Blueprint: `hironaka-g11-inv-bm-lower.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6b.  Source:
Bierstone--Milman 2008, §5 Step I and §7.2 (the values at a point equal those of its year), Włodarczyk 2005 Step 1 ("along
`T₁|_W`, which is a canonical segment of it").  The skeleton is W's `StepOneCanonicalTail` for the masked family; the
family-specific inputs are Bierstone--Milman's: the domain (`HironakaG11InvBMLowerDomainSucc`), the cosupports along
restricted tails (`HironakaG11InvBMLowerTailSucc.mem_cosupp_lowerBM_iff`), the re-basing (`HironakaG11InvBMRebase`), the
middle parts (`HironakaG11InvBMMaskStep.centresAvoid_maskG`), and

* **`AnchorChangeBM 𝔍 R`** (a property of the lower-dimensional invariant `R`, plan module 6): at one stage `T₀`, the values of
  `R` on the lower ideals of two anchors `a`, `b` of the same level with the same original members, restricted to opens inside
  their tangent open sets, agree along canonical restricted tails at the points of the cosupport of `b`.  The two lower
  ideals use the tangent directions chosen at the (possibly different) base points of `a` and `b`; Bierstone--Milman's
  coefficient ideals on two hypersurfaces of maximal contact are equivalent on the overlap (BM08 §5 Step I.A, Cor 4.2), so
  `AnchorChangeBM` holds for class-functorial `R` (to be proved in module 6 from lane G8's port P4 in `LocWPEquiv` form).
  When the base points coincide the lower ideals are equal and it follows from property (5).

Main results: `maskBM_subset_tangent`, `throughMembers_eq_of_mem_maskBM`, `lowerDataG_refl`, `lowerValueG_eq_of_eq` (the
comparison of a nearby point: restricted concatenation, re-basing, anchor change), `exists_middle`, `level_le_of_mem_maskBM`,
`stepOneInvBM_eq_lower`, `lowerDataG_step`, **`hasLowerDataG_of_isCanonical`** (given `AnchorChangeBM 𝔍 R`: along every
multiple test blow-up of `J̄` which is a canonical segment of `stepOneInvBM R 𝔍`, every non-special point of the cosupport has
lower data at its split).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMCanonicalTail

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneLowerDomain
  Hironaka.StepOneMaskTower Hironaka.StepOneNearby
  Hironaka.StepOneValueMasked Hironaka.StepOneCanonicalTail
  Hironaka.BoundaryCount Hironaka.MarkedIdealBiholomorphism
  Hironaka.RestrictEmptyTower Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMMaskStep Hironaka.HironakaG11InvBMLower
open Hironaka.HomogenizedGlueingTower (strictAlong)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Masks and members -/

section Masks

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- Bierstone--Milman's masks lie over the tangent open set of their anchor. -/
theorem maskBM_subset_tangent (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    ((maskBM 𝔍 s T₀ y₀ : Opens Y₀) : Set Y₀) ⊆ T₀.proj ⁻¹' (tangentChoice 𝔍 (T₀.proj y₀)).1 := fun z hz => by
  match s, hz with
  | 0, hz => exact (interior_subset hz).1
  | _ + 1, hz => exact (interior_subset (s := T₀.proj ⁻¹' (tangentChoice 𝔍 (T₀.proj y₀)).1) hz.2 : _)

open Classical in
/-- Over the mask of `y₀`, a point of the level of `y₀` has the original members of `y₀` through it. -/
theorem throughMembers_eq_of_mem_maskBM {s : ℕ} {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) {y₀ w : Y₀}
    (hw : w ∈ maskBM 𝔍 s T₀ y₀) (hl : level 𝔍 T₀ w = level 𝔍 T₀ y₀) (hl₀ : level 𝔍 T₀ y₀ = s) :
    throughMembers 𝔍 T₀ w = throughMembers 𝔍 T₀ y₀ := by
  have hiff : ∀ H ∈ origMembers 𝔍 T₀, w ∈ H ↔ y₀ ∈ H := by
    match s, hw, hl₀ with
    | 0, hw, hl₀ =>
      intro H hH
      refine ⟨fun hwH => absurd hwH ((interior_subset hw).2.1 H hH), fun hyH => ?_⟩
      exfalso
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
      have hpos : 0 < boundaryCount (origMembers 𝔍 T₀) y₀ :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyH⟩⟩
      have : boundaryCount (origMembers 𝔍 T₀) y₀ = 0 := hl₀
      omega
    | _ + 1, hw, _ => exact mem_origMembers_iff_of_mem_maskA 𝔍 T₀ hw.1 hl
  unfold throughMembers
  exact List.filter_congr fun H hH => by rw [hiff H hH]

end Masks

/-! ### The anchor change -/

section Anchor

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **The anchor change at one stage** (plan module 6): along a multiple test blow-up `T₀ T₁` of `J̄`, for anchors `a`, `b` of
the cosupport at `T₀` of the same level `s` with the same original members through them, and opens `Oa`, `Ob` over the tangent
open sets chosen at their base points, if the restricted lower ideals lie in the domain of `R` with `T₁|_{Oa}`, `T₁|_{Ob}`
canonical segments of them, then at every common point `p` of the cosupport of the second their values agree. -/
def AnchorChangeBM : Prop :=
  ∀ {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y), IsGeoTestTower (barMarked 𝔍) (T₀.append T₁) →
    ∀ (s : ℕ) (a b : Y₀) (Oa Ob : Opens Y₀),
      a ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp → b ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp →
      level 𝔍 T₀ a = s → level 𝔍 T₀ b = s → throughMembers 𝔍 T₀ a = throughMembers 𝔍 T₀ b →
      (Oa : Set Y₀) ⊆ T₀.proj ⁻¹' (tangentChoice 𝔍 (T₀.proj a)).1 →
      (Ob : Set Y₀) ⊆ T₀.proj ⁻¹' (tangentChoice 𝔍 (T₀.proj b)).1 →
      IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : Oa → Y₀) (lowerIdealBM 𝔍 s T₀ a)) →
      IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : Ob → Y₀) (lowerIdealBM 𝔍 s T₀ b)) →
      IsCanonical (MarkedIdeal.pullback (Subtype.val : Oa → Y₀) (lowerIdealBM 𝔍 s T₀ a))
        (R.inv (MarkedIdeal.pullback (Subtype.val : Oa → Y₀) (lowerIdealBM 𝔍 s T₀ a))) (restrict Oa T₁) →
      IsCanonical (MarkedIdeal.pullback (Subtype.val : Ob → Y₀) (lowerIdealBM 𝔍 s T₀ b))
        (R.inv (MarkedIdeal.pullback (Subtype.val : Ob → Y₀) (lowerIdealBM 𝔍 s T₀ b))) (restrict Ob T₁) →
      ∀ (p : Y) (hpa : T₁.proj p ∈ Oa) (hpb : T₁.proj p ∈ Ob),
        (⟨p, hpb⟩ : openPreimage T₁ Ob) ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : Ob → Y₀)
          (lowerIdealBM 𝔍 s T₀ b)) (restrict Ob T₁)).cosupp →
        R.inv (MarkedIdeal.pullback (Subtype.val : Oa → Y₀) (lowerIdealBM 𝔍 s T₀ a)) (restrict Oa T₁) ⟨p, hpa⟩ =
          R.inv (MarkedIdeal.pullback (Subtype.val : Ob → Y₀) (lowerIdealBM 𝔍 s T₀ b)) (restrict Ob T₁) ⟨p, hpb⟩

/-- **Lower data along the empty tail** (`StepOneCanonicalTail.lowerDataL_refl` for Bierstone--Milman's family). -/
theorem lowerDataG_refl (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀} (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp)
    {s : ℕ} (hreg : stepRegime 𝔍 s T₀ y₀) : LowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s T₀ .refl y₀ := by
  obtain ⟨hW, hdom⟩ := HironakaG11InvBMLowerDomainSucc.mem_maskBM_and_isInvDomain_lowerBM 𝔍 h𝔍 hd hn hmax hk T₀ hT₀
    hy₀ hreg
  refine ⟨hW, hdom, trivial, ?_⟩
  exact (HironakaG11InvBMLowerTailSucc.mem_cosupp_lowerBM_iff 𝔍 h𝔍 hd hn hmax T₀ .refl hT₀ hy₀ hreg.1 trivial
    ⟨y₀, hW⟩).mpr ⟨hy₀, hreg.1⟩

/-- **The lower value of a nearby point** (the comparison of `StepOneCompare` for Bierstone--Milman's family): let
`T₀' M T₁` be a multiple test blow-up of `J̄`, `y₀` a point of the cosupport at `T₀ = T₀' M` of level `s` whose restricted lower
ideal lies in the domain with `T₁|_W` a canonical segment of it, and `p` a point over its mask, of the level of `y₀` at `T₀`, in
its cosupport along `T₁|_W`.  If `p` has lower data at the split `T₀' (M T₁)`, with its image at `T₀'` in the cosupport of level
`s`, and the centres of `M` miss its mask, its lower value is the value of `R` for the lower ideal of `y₀` along `T₁|_W` at `p`
(restricted concatenation, re-basing along `M`, anchor change at `T₀`). -/
theorem lowerValueG_eq_of_eq (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₁ Y₀ Y : CMfd.{u} n}
    (T₀' : BlowupTower X Y₁) (M : BlowupTower Y₁ Y₀) (T₀ : BlowupTower X Y₀) (e : T₀'.append M = T₀)
    (T₁ : BlowupTower Y₀ Y) (T₁' : BlowupTower Y₁ Y) (e' : M.append T₁ = T₁')
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) (hl₀ : level 𝔍 T₀ y₀ = s)
    (hdom₀ : IsInvDomain (k - 1) (lowerBM 𝔍 s T₀ y₀))
    (hcan₀ : IsCanonical (lowerBM 𝔍 s T₀ y₀) (R.inv (lowerBM 𝔍 s T₀ y₀)) (restrict (maskBM 𝔍 s T₀ y₀) T₁))
    {p : Y} (hpW : T₁.proj p ∈ maskBM 𝔍 s T₀ y₀) (hlp : level 𝔍 T₀ (T₁.proj p) = level 𝔍 T₀ y₀)
    (hpc : p ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp)
    (hcos₀ : (⟨p, hpW⟩ : openPreimage T₁ (maskBM 𝔍 s T₀ y₀)) ∈
      (geoTransformAlong (lowerBM 𝔍 s T₀ y₀) (restrict (maskBM 𝔍 s T₀ y₀) T₁)).cosupp)
    (ha : T₁'.proj p ∈ (geoTransformAlong (barMarked 𝔍) T₀').cosupp) (hla : level 𝔍 T₀' (T₁'.proj p) = s)
    (hd₁ : LowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s T₀' T₁' p)
    (hM : CentresAvoid (maskBM 𝔍 s T₀' (T₁'.proj p)) M) :
    lowerValueG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s T₀' T₁' p =
      ((R.inv (lowerBM 𝔍 s T₀ y₀) (restrict (maskBM 𝔍 s T₀ y₀) T₁) ⟨p, hpW⟩ : Λ) : WithTop Λ) := by
  subst e e'
  obtain ⟨h₁, hdom₁, hcan₁, hcos₁⟩ := hd₁
  rw [lowerValueG_eq_of_mem R 𝔍 _ _ h₁]
  congr 1
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ (T₀'.append M) T₁).mp hT
  -- (i) the restricted concatenation
  obtain ⟨hcanb, hval⟩ := StepOneCompare.inv_restrict_append R (maskBM 𝔍 s T₀' ((M.append T₁).proj p)) hdom₁ M T₁
    hcan₁
  have hp₁ : (M.append T₁).proj p = M.proj (T₁.proj p) := by rw [BlowupTower.proj_append]; rfl
  have hq : p ∈ openPreimage T₁ (openPreimage M (maskBM 𝔍 s T₀' ((M.append T₁).proj p))) :=
    show M.proj (T₁.proj p) ∈ maskBM 𝔍 s T₀' ((M.append T₁).proj p) from hp₁ ▸ h₁
  obtain ⟨hcosb, hvalb⟩ := hval p h₁ hq hcos₁
  rw [← hvalb]
  -- (ii) re-basing along `M`, whose centres miss the mask
  obtain ⟨hdomS, hcanS, hvalS⟩ := HironakaG11InvBMRebase.inv_rebase_lowerBM 𝔍 R h𝔍 hd hn hmax T₀' M hT₀ ha hla hM
    ⟨T₁.proj p, hq⟩ hp₁.symm hdom₁ (restrict (openPreimage M (maskBM 𝔍 s T₀' ((M.append T₁).proj p))) T₁) hcanb
  rw [hvalS ⟨p, hq⟩ hcosb]
  -- (iii) the anchor change at the stage `T₀' M`
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨hNh, hch⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
    _ hT₀
  have hpc' : p ∈ (geoTransformAlong (geoTransformAlong (barMarked 𝔍) (T₀'.append M)) T₁).cosupp := by
    rw [← geoTransformAlong_append]; exact hpc
  have hqc : T₁.proj p ∈ (geoTransformAlong (barMarked 𝔍) (T₀'.append M)).cosupp :=
    proj_mem_cosupp_of_mem_cosupp hNh hch T₁ hT₁ hpc'
  have hbase : (T₀'.append M).proj (T₁.proj p) = T₀'.proj ((M.append T₁).proj p) := by
    rw [BlowupTower.proj_append, hp₁]; rfl
  refine hAC (T₀'.append M) T₁ hT s (T₁.proj p) y₀ _ _ hqc hy₀ (hlp.trans hl₀) hl₀
    (throughMembers_eq_of_mem_maskBM 𝔍 _ hpW hlp hl₀) ?_ (maskBM_subset_tangent 𝔍 s _ y₀) hdomS hdom₀ hcanS hcan₀ p
    hq hpW hcos₀
  intro z hz
  have h := maskBM_subset_tangent 𝔍 s T₀' ((M.append T₁).proj p) (show M.proj z ∈ _ from hz)
  rw [mem_preimage, hbase, BlowupTower.proj_append T₀' M]
  exact h

end Anchor

/-! ### The middle part between two start stages -/

section Middle

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **The middle part between two start stages, empty over the earlier mask**: along a multiple test blow-up `T'` of `J̄` which
is a canonical segment of `stepOneInvBM R 𝔍`, with lower data along every tower at most as long, let `z` be a point of the
cosupport of level `s` whose run in the regime of level `s` is `rz`, and `q` a point whose run `rq` is at least `rz`, with
image of level `s` at the start of its run.  Then the head at `rq` followed by a tower `M` is the head at `rz`, `M` followed by
the tail at `rz` is the tail at `rq`, and the centres of `M` miss the mask of the image of `q` (if `rq > rz`, the image of `z`
one stage before its start is out of the regime: `StepOneValueMasked.centresAvoid_lowerMaskL`). -/
theorem exists_middle (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y' : CMfd.{u} n} (T' : BlowupTower X Y')
    (hT : IsGeoTestTower (barMarked 𝔍) T') (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T')
    (hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T'.length → IsGeoTestTower (barMarked 𝔍) T'' →
      IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T'' → HasLowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T'')
    {z q : Y'} (hz : z ∈ (geoTransformAlong (barMarked 𝔍) T').cosupp) {s : ℕ} (hzs : level 𝔍 T' z = s)
    {rz rq : ℕ} (hrz : regimeRun (stepRegime 𝔍 s) T' z = rz) (hrq : regimeRun (stepRegime 𝔍 s) T' q = rq)
    (hle : rz ≤ rq) (hp₁ : level 𝔍 (head T' rq) ((tail T' rq).proj q) = s) :
    ∃ M : BlowupTower (split T' rq).1 (split T' rz).1, (head T' rq).append M = head T' rz ∧
      M.append (tail T' rz) = tail T' rq ∧ CentresAvoid (maskBM 𝔍 s (head T' rq) ((tail T' rq).proj q)) M := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  rcases hle.lt_or_eq with hlt | heq
  · have hrqle : rq ≤ T'.length := hrq ▸ regimeRun_le_length _ T' q
    have hrzlt : rz < T'.length := lt_of_lt_of_le hlt hrqle
    -- the last step before the start of `z`
    obtain ⟨τ, hτ₁, hτ₂⟩ := exists_split_le T' (a := rz) (b := rz + 1) (Nat.le_succ rz)
    have hτlen : τ.length = 1 := by
      have h := congrArg BlowupTower.length hτ₁
      rw [BlowupTower.length_append, length_head, length_head] at h
      omega
    obtain ⟨Cm, πm, hπm, rfl⟩ := exists_eq_step_refl τ hτlen
    obtain ⟨M₂, hM₁, hM₂⟩ := exists_split_le T' (a := rz + 1) (b := rq) (by omega)
    refine ⟨M₂.append (.step .refl Cm πm hπm), ?_, ?_, ?_⟩
    · rw [← BlowupTower.append_assoc, hM₁, hτ₁]
    · rw [BlowupTower.append_assoc, hτ₂, hM₂]
    · show CentresAvoid _ (.step M₂ Cm πm hπm)
      -- the image of `z` one stage before its start: out of the regime, of level at least `s`, in the cosupport
      have hnw := not_regime_head_regimeRun (stepRegime 𝔍 s) T' z (by rw [hrz]; exact hrzlt)
      rw [hrz] at hnw
      have hw := mem_cosupp_head 𝔍 h𝔍 T' hT hz (rz + 1)
      have hlw := level_le_head 𝔍 hE T' z (rz + 1)
      rw [hzs] at hlw
      rw [← hM₁] at hnw hw hlw
      -- the head at `rz` is a prefix of `T'`: multiple test blow-up and canonical segment
      have heq : (head T' rq).append (.step M₂ Cm πm hπm) = head T' rz := by
        rw [← hτ₁, ← hM₁]
        rfl
      have hTh : IsGeoTestTower (barMarked 𝔍) ((head T' rq).append (.step M₂ Cm πm hπm)) := by
        rw [heq]; exact ((isGeoTestTower_iff_head_tail (barMarked 𝔍) T' rz).mp hT).1
      have hcanh : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) ((head T' rq).append (.step M₂ Cm πm hπm)) := by
        rw [heq]; exact isCanonical_head _ _ T' rz hcan
      have hlenM₂ : (head T' rq).length + M₂.length + 1 ≤ T'.length := by
        have h := congrArg BlowupTower.length hM₁
        rw [BlowupTower.length_append, length_head, length_head] at h
        rw [length_head]
        omega
      refine HironakaG11InvBMMaskStep.centresAvoid_maskG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍)
        (fun s _ T₀ y₀ => maskBM_le_lowerMask 𝔍 s T₀ y₀) h𝔍 hd hn hmax hk (head T' rq) hp₁ M₂ Cm πm hπm hTh hcanh
        (fun M' hM' hT'' hcan'' => hD _ ?_ hT'' hcan'') hw hlw hnw
      rw [BlowupTower.length_append]
      omega
  · subst heq
    obtain ⟨M, h₁, h₂⟩ := exists_split_le T' (le_refl rz)
    refine ⟨M, h₁, h₂, centresAvoid_of_length_eq_zero _ M ?_⟩
    have h := congrArg BlowupTower.length h₁
    rw [BlowupTower.length_append] at h
    omega

end Middle

/-! ### The canonical-tail theorem -/

section Tail

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- Over the mask at level `s` the level is at most `s`. -/
theorem level_le_of_mem_maskBM (hE : ∀ H ∈ 𝔍.E, IsClosed H) {s : ℕ} {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) {y₀ : Y₀} (hl₀ : level 𝔍 T₀ y₀ = s) {q : Y} (hq : T₁.proj q ∈ maskBM 𝔍 s T₀ y₀) :
    level 𝔍 (T₀.append T₁) q ≤ s := by
  match s, hl₀, hq with
  | 0, _, hq => exact (level_eq_zero_of_mem_maskB 𝔍 hE T₀ T₁ hq).le
  | _ + 1, hl₀, hq => exact (level_le_of_mem_maskA 𝔍 hE T₀ T₁ hq.1).trans hl₀.le

/-- **The value at a point of the cosupport of the lower marked ideal** (`hir:step-one-canonical-tail`): along a multiple test
blow-up `T'` of `J̄` which is a canonical segment of `stepOneInvBM R 𝔍`, with lower data along every tower at most as long, let
`z` be a point of the cosupport in the regime of level `s`, with run `r`, and `q` a point of the cosupport of its lower marked
ideal along the restricted tail.  Then the value at `q` is `(s, R(q))`, `R` of that lower marked ideal at `q`: `q` has level
`s`, it entered the regime no later than `z` (`StepOneMaskTower`), the steps between the two starts miss its mask
(`exists_middle`), and `StepOneCompare` moves its value to the lower marked ideal of `z`. -/
theorem stepOneInvBM_eq_lower (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y' : CMfd.{u} n} (T' : BlowupTower X Y')
    (hT : IsGeoTestTower (barMarked 𝔍) T') (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T')
    (hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T'.length → IsGeoTestTower (barMarked 𝔍) T'' →
      IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T'' → HasLowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T'')
    {z : Y'} (hz : z ∈ (geoTransformAlong (barMarked 𝔍) T').cosupp) {s r : ℕ} (hreg : stepRegime 𝔍 s T' z)
    (hr : regimeRun (stepRegime 𝔍 s) T' z = r)
    (q : openPreimage (tail T' r) (maskBM 𝔍 s (head T' r) ((tail T' r).proj z)))
    (hq : q ∈ (geoTransformAlong (lowerBM 𝔍 s (head T' r) ((tail T' r).proj z))
      (restrict (maskBM 𝔍 s (head T' r) ((tail T' r).proj z)) (tail T' r))).cosupp) :
    stepOneInvBM R 𝔍 T' q = toLex (s, ((R.inv (lowerBM 𝔍 s (head T' r) ((tail T' r).proj z))
      (restrict (maskBM 𝔍 s (head T' r) ((tail T' r).proj z)) (tail T' r)) q : Λ) : WithTop Λ)) := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  have hsplit : (head T' r).append (tail T' r) = T' := head_append_tail T' r
  have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T' r).append (tail T' r)) := by rw [hsplit]; exact hT
  -- the lower data of `z`
  have hzD := hD T' le_rfl hT hcan z hz hreg.2
  rw [hreg.1, hr] at hzD
  obtain ⟨hy₀W, hdom₀, hcan₀, -⟩ := hzD
  obtain ⟨hreg₀, hy₀⟩ := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T' hT hz hreg.2
  rw [hreg.1, hr] at hreg₀ hy₀
  have hTW := isGeoTestTower_of_isCanonical R hdom₀ _ hcan₀
  -- `q`: cosupport, level, regime and run
  obtain ⟨hqc₀, hql₀⟩ := (HironakaG11InvBMLowerTailSucc.mem_cosupp_lowerBM_iff 𝔍 h𝔍 hd hn hmax (head T' r) (tail T' r) hT₀₁ hy₀ hreg₀.1
    hTW q).mp hq
  obtain ⟨hqreg, hqrun⟩ := stepRegime_and_le_regimeRun_of_mem_lowerMask 𝔍 h𝔍 hd hmax (head T' r) (tail T' r) hT₀₁
    hreg₀.1 (maskBM_le_lowerMask 𝔍 _ _ _ q.2) hql₀
  have hqc : (q : Y') ∈ (geoTransformAlong (barMarked 𝔍) T').cosupp :=
    (congrArg (fun T : BlowupTower X Y' => (q : Y') ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) hsplit).mp hqc₀
  have hql : level 𝔍 T' q = s :=
    (congrArg (fun T : BlowupTower X Y' => level 𝔍 T (q : Y') = s) hsplit).mp hql₀
  have hqreg' : stepRegime 𝔍 s T' q :=
    (congrArg (fun T : BlowupTower X Y' => stepRegime 𝔍 s T (q : Y')) hsplit).mp hqreg
  have hqrun' : (tail T' r).length ≤ regimeRun (stepRegime 𝔍 s) T' q :=
    (congrArg (fun T : BlowupTower X Y' => (tail T' r).length ≤ regimeRun (stepRegime 𝔍 s) T (q : Y')) hsplit).mp hqrun
  clear hqreg hqrun
  have hlenT₁ : (tail T' r).length = r := by
    rw [length_tail]
    have := regimeRun_le_length (stepRegime 𝔍 s) T' z
    omega
  have hle : r ≤ regimeRun (stepRegime 𝔍 s) T' q := hlenT₁.symm.trans_le hqrun'
  have hqreg := hqreg'
  -- the lower data of `q` and the level of its image at the start of its run
  have hqD := hD T' le_rfl hT hcan q hqc hqreg.2
  rw [hql] at hqD
  obtain ⟨hqreg₀, hqc₁⟩ := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T' hT hqc hqreg.2
  rw [hql] at hqreg₀ hqc₁
  -- the middle part between the two starts
  obtain ⟨M, e₁, e₂, hM⟩ := exists_middle 𝔍 R h𝔍 hd hn hmax hk T' hT hcan hD hz hreg.1 hr rfl hle hqreg₀.1
  -- the value of `q`
  show stepOneInvG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T' q = _
  rw [stepOneInvG_of_not_isSpecial R 𝔍 _ _ T' hqreg.2, hql]
  congr 2
  -- the level of the image of `q` at the start of `z`
  have hlp : level 𝔍 (head T' r) ((tail T' r).proj q) = level 𝔍 (head T' r) ((tail T' r).proj z) := by
    rw [hreg₀.1]
    refine le_antisymm ?_ ?_
    · have h := level_le_of_mem_maskBM 𝔍 hE (head T' r) (.refl) hreg₀.1 (q := (tail T' r).proj q) q.2
      exact h
    · have h := level_le_head 𝔍 hE T' q r
      rw [hql] at h
      exact h
  exact lowerValueG_eq_of_eq 𝔍 R hAC h𝔍 hd hn hmax (head T' (regimeRun (stepRegime 𝔍 s) T' q)) M (head T' r) e₁
    (tail T' r) (tail T' (regimeRun (stepRegime 𝔍 s) T' q)) e₂ hT₀₁ hy₀ hreg₀.1 hdom₀ hcan₀ q.2 hlp hqc₀ hq hqc₁
    hqreg₀.1 hqD hM

/-- **The induction step of the canonical-tail theorem**: along a multiple test blow-up `T' σ` of `J̄` which is a canonical
segment of `stepOneInvBM R 𝔍` (`σ` the blowup along `C`), with lower data along every tower at most as long as `T'`, a point
`y` of the cosupport whose image `σ y` is in the regime of the level `s` of `y`, with run `r`, has lower data at the split of
`T'` at `r` followed by `σ`: the trace of `C` on the restricted tail is empty or the maximum locus of the lower-dimensional
invariant (TN3's `MaxLocusLocal.preimage_maxLocus_eq_or`, with `stepOneInvM_eq_lower` and the smaller levels elsewhere over the
mask), and `y` lies in the cosupport of the lower marked ideal. -/
theorem lowerDataG_step (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y' Z : CMfd.{u} n} (T' : BlowupTower X Y')
    (C : Set Y') (π : Z → Y') (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (barMarked 𝔍) (.step T' C π hπ))
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) (.step T' C π hπ))
    (hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T'.length → IsGeoTestTower (barMarked 𝔍) T'' →
      IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T'' → HasLowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T'')
    {y : Z} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) (.step T' C π hπ)).cosupp) {s r : ℕ}
    (hs : level 𝔍 (.step T' C π hπ) y = s) (hreg : stepRegime 𝔍 s T' (π y))
    (hr : regimeRun (stepRegime 𝔍 s) T' (π y) = r) :
    LowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s (head T' r) (.step (tail T' r) C π hπ) y := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  obtain ⟨hT', hCadm⟩ := (isGeoTestTower_step_iff _ T' C π hπ).mp hT
  obtain ⟨hcan', hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T' ∧
      (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 T') (geoTransformAlong (barMarked 𝔍) T').cosupp) := hcan
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T'
    hT'
  have hz : π y ∈ (geoTransformAlong (barMarked 𝔍) T').cosupp :=
    proj_mem_cosupp_of_mem_cosupp (𝔪 := geoTransformAlong (barMarked 𝔍) T') hNT hcT (.step .refl C π hπ) ⟨trivial, hCadm⟩ hy
  have hsplit : (head T' r).append (tail T' r) = T' := head_append_tail T' r
  -- the lower data of `σ y`
  have hzD := hD T' le_rfl hT' hcan' (π y) hz hreg.2
  rw [hreg.1, hr] at hzD
  obtain ⟨hy₀W, hdom₀, hcan₀, hcos₀⟩ := hzD
  obtain ⟨hreg₀, hy₀⟩ := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T' hT' hz hreg.2
  rw [hreg.1, hr] at hreg₀ hy₀
  have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T' r).append (tail T' r)) := by rw [hsplit]; exact hT'
  have hTW := isGeoTestTower_of_isCanonical R hdom₀ _ hcan₀
  -- the canonical clause
  have hcanS : IsCanonical (lowerBM 𝔍 s (head T' r) ((tail T' r).proj (π y)))
      (R.inv (lowerBM 𝔍 s (head T' r) ((tail T' r).proj (π y))))
      (restrict (maskBM 𝔍 s (head T' r) ((tail T' r).proj (π y))) (.step (tail T' r) C π hπ)) := by
    refine ⟨hcan₀, ?_⟩
    rcases hC with hC | hC
    · left
      rw [hC]
      exact preimage_empty
    · rw [hC]
      refine MaxLocusLocal.preimage_maxLocus_eq_or Subtype.val (MaxLocusLocal.strictMono_toLex_coe s) ?_ ?_ ?_
      · intro q hq
        have h := ((HironakaG11InvBMLowerTailSucc.mem_cosupp_lowerBM_iff 𝔍 h𝔍 hd hn hmax (head T' r) (tail T' r) hT₀₁ hy₀ hreg₀.1 hTW
          q).mp hq).1
        exact (congrArg (fun T : BlowupTower X Y' => (q : Y') ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) hsplit).mp h
      · intro q hq
        exact stepOneInvBM_eq_lower 𝔍 R hAC h𝔍 hd hn hmax hk T' hT' hcan' hD hz hreg hr q hq
      · intro q hq hqn
        refine ⟨⟨π y, hy₀W⟩, hcos₀, ?_⟩
        have hql₀ := level_le_of_mem_maskBM 𝔍 hE (head T' r) (tail T' r) hreg₀.1 q.2
        have hql₁ : level 𝔍 T' q ≤ s :=
          (congrArg (fun T : BlowupTower X Y' => level 𝔍 T (q : Y') ≤ s) hsplit).mp hql₀
        rcases hql₁.lt_or_eq with hlt | heq
        · exact stepOneInvG_lt_of_level_lt R 𝔍 _ _ (hlt.trans_eq hreg.1.symm)
        · exfalso
          apply hqn
          refine (HironakaG11InvBMLowerTailSucc.mem_cosupp_lowerBM_iff 𝔍 h𝔍 hd hn hmax (head T' r) (tail T' r) hT₀₁ hy₀ hreg₀.1 hTW
            q).mpr ⟨?_, ?_⟩
          · exact (congrArg (fun T : BlowupTower X Y' => (q : Y') ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp)
              hsplit).mpr hq
          · exact (congrArg (fun T : BlowupTower X Y' => level 𝔍 T (q : Y') = s) hsplit).mpr heq
  refine ⟨hy₀W, hdom₀, hcanS, ?_⟩
  -- the cosupport clause
  have heq : (head T' r).append (.step (tail T' r) C π hπ) = .step T' C π hπ := by
    rw [BlowupTower.append_step, hsplit]
  have hTs : IsGeoTestTower (barMarked 𝔍) ((head T' r).append (.step (tail T' r) C π hπ)) := by rw [heq]; exact hT
  refine (HironakaG11InvBMLowerTailSucc.mem_cosupp_lowerBM_iff 𝔍 h𝔍 hd hn hmax (head T' r) (.step (tail T' r) C π hπ) hTs hy₀ hreg₀.1
    (isGeoTestTower_of_isCanonical R hdom₀ _ hcanS) ⟨y, hy₀W⟩).mpr ⟨?_, ?_⟩
  · rw [heq]; exact hy
  · rw [heq]; exact hs

/-- **The canonical-tail theorem** (`hir:step-one-canonical-tail`): for `𝔍` well formed with `d ≥ 1`, of maximal order along
`N` with `dim N ≤ k` (`0 < n`) and `R` a resolution invariant in dimension `≤ k - 1`, along every multiple test blow-up of
`J̄ = 𝓒_N(𝓗_N(𝔍))` which is a canonical segment of the masked Step 1 value function `stepOneInvBM R 𝔍`, every non-special point
of the cosupport has lower data at its split: its lower value is the value of `R` along one of its own canonical segments. -/
theorem hasLowerDataG_of_isCanonical (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) :
    HasLowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T := by
  suffices h : ∀ (m : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y), T.length ≤ m → IsGeoTestTower (barMarked 𝔍) T →
      IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T → HasLowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T from
    h T.length T le_rfl hT hcan
  intro m
  induction m with
  | zero =>
    intro Y T hlen hT hcan y hy hsp
    cases T with
    | refl => exact lowerDataG_refl 𝔍 R h𝔍 hd hn hmax hk .refl trivial hy ⟨rfl, hsp⟩
    | step T' C π hπ => simp at hlen
  | succ m ih =>
    intro Y T hlen hT hcan y hy hsp
    cases T with
    | refl => exact lowerDataG_refl 𝔍 R h𝔍 hd hn hmax hk .refl trivial hy ⟨rfl, hsp⟩
    | step T' C π hπ =>
      have hlen' : T'.length ≤ m := by
        rw [BlowupTower.length_step] at hlen
        omega
      have hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T'.length →
          IsGeoTestTower (barMarked 𝔍) T'' → IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T'' →
          HasLowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T'' := fun T'' h => ih T'' (h.trans hlen')
      by_cases hreg : stepRegime 𝔍 (level 𝔍 (.step T' C π hπ) y) T' (π y)
      · rw [regimeRun_step_of _ T' C π hπ hreg]
        exact lowerDataG_step 𝔍 R hAC h𝔍 hd hn hmax hk T' C π hπ hT hcan hD hy rfl hreg rfl
      · rw [regimeRun_step_of_not _ T' C π hπ hreg]
        exact lowerDataG_refl 𝔍 R h𝔍 hd hn hmax hk _ hT hy ⟨rfl, hsp⟩

/-- **Properties (3) "equal off the centre" and (4) of `stepOneInvBM` along canonical segments** (given the anchor change):
along a multiple test blow-up `T σ` of `J̄` which is a canonical segment of `stepOneInvBM R 𝔍`, at a point `z` of the cosupport
with `σ z` off the centre, the value at `z` is the value at `σ z`. -/
theorem stepOneInvBM_step_of_notMem_of_isCanonical (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower (barMarked 𝔍) (.step T C π hπ))
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) (.step T C π hπ)) {z : Z}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp) (hzC : π z ∉ C) :
    stepOneInvBM R 𝔍 (.step T C π hπ) z = stepOneInvBM R 𝔍 T (π z) := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  have hT' : IsGeoTestTower (barMarked 𝔍) T := hT.1
  refine stepOneInvG_step_of_notMem R 𝔍 _ _ h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hE T hT' C π hπ hzC fun hsp => ?_
  have hs := isSpecial_step_iff_of_notMem 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hE T hT' C π hπ hzC
  have hl := level_step_of_notMem 𝔍 hE T C π hπ hzC
  have hzD := hasLowerDataG_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk _ hT hcan z hz fun h => hsp (hs.mp h)
  have hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z) := ⟨hl.symm, hsp⟩
  rw [regimeRun_step_of _ T C π hπ hreg, hl] at hzD
  exact hzD

/-- **Property (3), drop over the centre, of `stepOneInvBM` at non-special points keeping their level, along canonical
segments** (given the anchor change). -/
theorem stepOneInvBM_step_lt_of_mem_of_isCanonical (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower (barMarked 𝔍) (.step T C π hπ))
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) (.step T C π hπ)) {z : Z}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp) (hzC : π z ∈ C)
    (hzs : ¬ IsSpecial 𝔍 (.step T C π hπ) z) (hzT : ¬ IsSpecial 𝔍 T (π z))
    (hl : level 𝔍 (.step T C π hπ) z = level 𝔍 T (π z)) :
    stepOneInvBM R 𝔍 (.step T C π hπ) z < stepOneInvBM R 𝔍 T (π z) := by
  refine stepOneInvG_step_lt_of_mem R 𝔍 _ _ T C π hπ hzC hzs hzT hl ?_
  have hzD := hasLowerDataG_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk _ hT hcan z hz hzs
  have hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z) := ⟨hl.symm, hzT⟩
  rw [regimeRun_step_of _ T C π hπ hreg, hl] at hzD
  exact hzD

end Tail


end

end Hironaka.HironakaG11InvBMCanonicalTail
