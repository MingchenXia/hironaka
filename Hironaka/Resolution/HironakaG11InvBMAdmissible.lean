import Hironaka.Resolution.HironakaG11InvBMUSC
import Hironaka.Invariant.StepOneAdmissible

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's Step 1 value: admissibility of the level sets (repair (B'), plan module 8, part 2)

Blueprint: `hironaka-g11-inv-bm-max-order.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §1 module 8.
Sources: Bierstone--Milman 2008, §5 Step I.B ("any sequence of test transformations of `𝒥` is a sequence of test transformations
of `ℐ|_U` (and the centre `C` of each admissible blowing-up lies inside the intersection of the components of `E` that pass
through a point of `C`) ... blowings-up which are admissible for `𝒥` are also admissible for `ℐ|_U`"); the skeleton is W's
`StepOneAdmissible` for the masked family.

* `hasNormalCrossings_append_of_dichotomy` (general): normal crossings with `E₂` extend to `E₁ ++ E₂` (simple normal crossings)
  when every member of `E₁` contains the centre or misses it;
* `E_geoTransformAlong_lowerBM`: the divisor of the transform of Bierstone--Milman's lower marked ideal along a restricted tail is
  the restriction of the born part of the divisor of `J̄_{T₀T₁}`;
* **`isAdmissibleCentre_of_lowerBM`** (the transfer, both levels): an admissible centre of (an open restriction of) the transform
  of the lower marked ideal is one of `J̄_{T₀T₁}`: the original members through the anchor contain it (level), the others miss
  the mask;
* `exists_opens_preimage_eq_empty`, `exists_opens_isAdmissibleCentre_of_eq`, **`stepOneInvBM_admissible`** (property (1) at
  every value, given the anchor change), `isAdmissibleCentre_maxLocus_stepOneInvBM`, **`isGeoTestTower_of_isCanonical_stepOneInvBM`**
  (canonical segments of `stepOneInvBM R 𝔍` are multiple test blow-ups of `J̄`);
* `maxLocus_stepOneInvBM_eq_of_isSpecial`, **`stepOneInvBM_decrease`**, **`stepOneInvBM_emptyStep`** (properties (3), (4)) and the
  forms along canonical segments without the test-tower hypothesis.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMAdmissible

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneLowerDomain
  Hironaka.StepOneMaskTower Hironaka.StepOneValueMasked
  Hironaka.BoundaryCount Hironaka.MarkedIdealBiholomorphism
  Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong
  Hironaka.ResolutionInvariantOrder Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMCanonicalTail
  Hironaka.HironakaG11InvBMUSC Hironaka.MaxLocusLocal
  Hironaka.NormalCrossings
open Hironaka.HomogenizedGlueingTower (strictAlong)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Normal crossings with members containing or missing the centre -/

section NC

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Normal crossings extend to members containing or missing the centre**: if `E₁ ++ E₂` is a simple normal crossings divisor,
`C` has only normal crossings with `E₂`, and every member of `E₁` contains `C` or is disjoint from it, then `C` has only normal
crossings with `E₁ ++ E₂`. -/
theorem hasNormalCrossings_append_of_dichotomy {C : Set M} {E₁ E₂ : List (Set M)} (hE : IsSNCDivisor n (E₁ ++ E₂))
    (h₂ : HasNormalCrossings n C E₂) (hdich : ∀ H ∈ E₁, C ⊆ H ∨ Disjoint C H) :
    HasNormalCrossings n C (E₁ ++ E₂) := by
  classical
  have hsub : (E₁.filter (fun H => decide (C ⊆ H)) ++ E₂).Sublist (E₁ ++ E₂) :=
    (List.filter_sublist).append (List.Sublist.refl _)
  have hmid : HasNormalCrossings n C (E₁.filter (fun H => decide (C ⊆ H)) ++ E₂) :=
    NormalCrossingsComparison.hasNormalCrossings_of_forall_notMem
      (NormalCrossingsComparison.isSNCDivisor_of_sublist hE hsub) h₂ fun H hH hH₂ => by
        rcases List.mem_append.mp hH with h | h
        · exact of_decide_eq_true (List.mem_filter.mp h).2
        · exact absurd h hH₂
  refine DropMembers.hasNormalCrossings_of_forall_disjoint hmid fun H hH hHn => ?_
  rcases List.mem_append.mp hH with h | h
  · rcases hdich H h with hC | hC
    · exact absurd (List.mem_append_left _ (List.mem_filter.mpr ⟨h, decide_eq_true hC⟩)) hHn
    · exact hC
  · exact absurd (List.mem_append_right _ h) hHn

end NC

/-! ### The transfer of admissible centres -/

section Transfer

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **The divisor of the transform of the lower marked ideal along a restricted tail** is the restriction of the born part of
the divisor of `J̄_{T₀ T₁}` (the lower marked ideal starts at `T₀` with the members born along `T₀`, and divisors of transforms
depend only on the initial divisor). -/
theorem E_geoTransformAlong_lowerBM (h𝔍 : 𝔍.IsWellFormed) (s : ℕ) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) (y₀ : Y₀) :
    (geoTransformAlong (lowerBM 𝔍 s T₀ y₀) (restrict (maskBM 𝔍 s T₀ y₀) T₁)).E =
      ((geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).E.drop 𝔍.E.length).map
        ((Subtype.val : openPreimage T₁ (maskBM 𝔍 s T₀ y₀) → Y) ⁻¹' ·) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hTe := HironakaG11InvBMStage.isGeoTestTower_emptyBoundary (barMarked 𝔍) _ hT
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hTe
  have hwe := HironakaG11InvBMStage.isWellFormed_emptyBoundary hJ
  obtain ⟨hN₀, hc₀⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwe.isClosedSubmanifold_N hwe.isCoherent
    T₀ hT₀
  -- the initial divisors agree
  have hE₀ : (lowerBM 𝔍 s T₀ y₀).E = (MarkedIdeal.pullback (Subtype.val : maskBM 𝔍 s T₀ y₀ → Y₀)
      (geoTransformAlong (emptyBoundary (barMarked 𝔍)) T₀)).E := by
    rw [lowerBM_E]
    show _ = (geoTransformAlong (emptyBoundary (barMarked 𝔍)) T₀).E.map _
    rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := coeffEmptyBM 𝔍)
      (𝔫 := emptyBoundary (barMarked 𝔍)) rfl T₀]
  rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE₀,
    geoTransformAlong_restrict (maskBM 𝔍 s T₀ y₀) hN₀ hc₀ T₁ hT₁, ← geoTransformAlong_append,
    HironakaG11InvBMStage.geoTransformAlong_emptyBoundary]
  rfl

/-- **A member missing the anchor misses the mask**, along every tail. -/
theorem notMem_strictAlong_of_mem_maskBM (hE : ∀ H ∈ 𝔍.E, IsClosed H) {s : ℕ} {Y₀ Y : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) {y₀ : Y₀} {q : Y} (hq : T₁.proj q ∈ maskBM 𝔍 s T₀ y₀)
    {H₀ : Set Y₀} (hH₀ : H₀ ∈ origMembers 𝔍 T₀) (hyH : y₀ ∉ H₀) : q ∉ strictAlong T₁ H₀ := by
  intro hqH
  have hpre := MemberInterTowerAlong.strictAlong_subset_preimage T₁ (isClosed_of_mem_origMembers 𝔍 hE T₀ H₀ hH₀) hqH
  match s, hq with
  | 0, hq => exact (interior_subset hq).2.1 H₀ hH₀ hpre
  | _ + 1, hq => exact hyH ((interior_subset hq.1).1 H₀ hH₀ hpre)

/-- **A member through the anchor contains the points over the mask of the anchor's level.** -/
theorem mem_strictAlong_of_mem_maskBM (hE : ∀ H ∈ 𝔍.E, IsClosed H) {s : ℕ} {Y₀ Y : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) {y₀ : Y₀} (hl₀ : level 𝔍 T₀ y₀ = s) {q : Y}
    (hq : T₁.proj q ∈ maskBM 𝔍 s T₀ y₀) (hlq : level 𝔍 (T₀.append T₁) q = s) {H₀ : Set Y₀}
    (hH₀ : H₀ ∈ origMembers 𝔍 T₀) (hyH : y₀ ∈ H₀) : q ∈ strictAlong T₁ H₀ := by
  match s, hl₀, hq, hlq with
  | 0, hl₀, _, _ => exact absurd hl₀ (Nat.one_le_iff_ne_zero.mp
      (StepOneAdmissibleTop.one_le_boundaryCount_of_mem hH₀ hyH))
  | _ + 1, hl₀, hq, hlq =>
    exact (StepOneCompare.level_eq_iff_of_mem_maskA 𝔍 hE T₀ T₁ hq.1).mp (hlq.trans hl₀.symm) H₀ hH₀ hyH

/-- **The transfer of admissible centres** (Bierstone--Milman 2008 §5 Step I.B, both levels): along a multiple test blow-up
`T₀ T₁` of `J̄`, for `y₀` in the cosupport at `T₀` of level `s` whose lower marked ideal lies in the domain with `T₁|_W` a
multiple test blow-up of it (`W` its mask), on every open `W''` of `T₁⁻¹W` an admissible centre of the restriction of the
transform of the lower marked ideal is an admissible centre of the restriction of `J̄_{T₀ T₁}`: the cosupports agree at the level
`s`; the born members are those of the lower marked ideal; the original members through `y₀` contain the centre (its points have
the level of `y₀`, over `maskA`), the others miss the mask. -/
theorem isAdmissibleCentre_of_lowerBM {k : ℕ} (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) (hl₀ : level 𝔍 T₀ y₀ = s)
    (hdom : IsInvDomain k (lowerBM 𝔍 s T₀ y₀))
    (hTW : IsGeoTestTower (lowerBM 𝔍 s T₀ y₀) (restrict (maskBM 𝔍 s T₀ y₀) T₁))
    (W'' : Opens (openPreimage T₁ (maskBM 𝔍 s T₀ y₀))) (C : Set W'')
    (h : (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ (maskBM 𝔍 s T₀ y₀))
      (geoTransformAlong (lowerBM 𝔍 s T₀ y₀) (restrict (maskBM 𝔍 s T₀ y₀) T₁))).IsAdmissibleCentre C) :
    (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ (maskBM 𝔍 s T₀ y₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ (maskBM 𝔍 s T₀ y₀) → Y)
        (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)))).IsAdmissibleCentre C := by
  have hE𝔍 : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwfT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ _ hT
  have hwfP := IsWellFormed.pullback_val hwfT (openPreimage T₁ (maskBM 𝔍 s T₀ y₀))
  have hwf'' := IsWellFormed.pullback_val hwfP W''
  obtain ⟨-, hcL⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent _ hTW
  obtain ⟨hcl, hsub, hnc⟩ := h
  -- the points of the centre: in the cosupport of `J̄_{T₀ T₁}`, of level `s`
  have hlev : ∀ c ∈ C, ((c : openPreimage T₁ (maskBM 𝔍 s T₀ y₀)) : Y) ∈
      (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp ∧
      level 𝔍 (T₀.append T₁) ((c : openPreimage T₁ (maskBM 𝔍 s T₀ y₀)) : Y) = s := by
    intro c hc
    have h1 := hsub hc
    rw [cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcL hg)]
      at h1
    exact (HironakaG11InvBMLowerTailSucc.mem_cosupp_lowerBM_iff 𝔍 h𝔍 hd hn hmax T₀ T₁ hT hy₀ hl₀ hTW _).mp h1
  refine ⟨hcl, ?_, ?_⟩
  · -- the cosupport
    intro c hc
    rw [cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hwfP.isCoherent hg), mem_preimage, cosupp_pullback_val _
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwfT.isCoherent hg)]
    exact (hlev c hc).1
  · -- the divisor: the born members, and original members containing or missing the centre
    have hEL : (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ (maskBM 𝔍 s T₀ y₀))
        (geoTransformAlong (lowerBM 𝔍 s T₀ y₀) (restrict (maskBM 𝔍 s T₀ y₀) T₁))).E =
        ((((geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).E.drop 𝔍.E.length).map
          ((Subtype.val : openPreimage T₁ (maskBM 𝔍 s T₀ y₀) → Y) ⁻¹' ·)).map
            ((Subtype.val : W'' → openPreimage T₁ (maskBM 𝔍 s T₀ y₀)) ⁻¹' ·)) := by
      show (geoTransformAlong (lowerBM 𝔍 s T₀ y₀) (restrict (maskBM 𝔍 s T₀ y₀) T₁)).E.map _ = _
      rw [E_geoTransformAlong_lowerBM 𝔍 h𝔍 s T₀ T₁ hT y₀]
    have hEJ : (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ (maskBM 𝔍 s T₀ y₀))
        (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ (maskBM 𝔍 s T₀ y₀) → Y)
          (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)))).E =
        (((origMembers 𝔍 (T₀.append T₁)).map ((Subtype.val : openPreimage T₁ (maskBM 𝔍 s T₀ y₀) → Y) ⁻¹' ·)).map
          ((Subtype.val : W'' → openPreimage T₁ (maskBM 𝔍 s T₀ y₀)) ⁻¹' ·)) ++
        ((((geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).E.drop 𝔍.E.length).map
          ((Subtype.val : openPreimage T₁ (maskBM 𝔍 s T₀ y₀) → Y) ⁻¹' ·)).map
            ((Subtype.val : W'' → openPreimage T₁ (maskBM 𝔍 s T₀ y₀)) ⁻¹' ·)) := by
      show ((geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).E.map _).map _ = _
      rw [← List.map_append, ← List.map_append]
      unfold origMembers
      rw [List.take_append_drop]
    rw [hEL] at hnc
    have hsnc := hwf''.isSNCDivisor
    rw [hEJ] at hsnc
    show HasNormalCrossings n C (MarkedIdeal.pullback (Subtype.val : W'' → openPreimage T₁ (maskBM 𝔍 s T₀ y₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₁ (maskBM 𝔍 s T₀ y₀) → Y)
        (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)))).E
    rw [hEJ]
    refine hasNormalCrossings_append_of_dichotomy hsnc hnc fun H hH => ?_
    obtain ⟨H₁, hH₁, rfl⟩ := List.mem_map.mp hH
    obtain ⟨H', hH', rfl⟩ := List.mem_map.mp hH₁
    rw [StepOneMaskTower.origMembers_append] at hH'
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH'
    by_cases hyH : y₀ ∈ H₀
    · left
      intro c hc
      exact mem_strictAlong_of_mem_maskBM 𝔍 hE𝔍 T₀ T₁ hl₀ (c : openPreimage T₁ (maskBM 𝔍 s T₀ y₀)).2
        (hlev c hc).2 hH₀ hyH
    · right
      exact Set.disjoint_left.mpr fun c _ hcH =>
        notMem_strictAlong_of_mem_maskBM 𝔍 hE𝔍 T₀ T₁ (c : openPreimage T₁ (maskBM 𝔍 s T₀ y₀)).2 hH₀ hyH hcH

end Transfer

/-! ### The level sets near a point -/

section Local

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **A point off the level set has a neighbourhood missing it** (given the anchor change, for upper semicontinuity). -/
theorem exists_opens_preimage_eq_empty (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) (W : Opens Y) (l : ℕ ×ₗ WithTop Λ)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W → stepOneInvBM R 𝔍 T y ≤ l) {x : Y}
    (hxW : x ∈ W) (hx : ¬ (x ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvBM R 𝔍 T x = l)) :
    ∃ V : Opens Y, x ∈ V ∧ V ≤ W ∧
      (Subtype.val : V → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvBM R 𝔍 T y = l} =
        ∅ := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T hT
  obtain ⟨t, hto, hxt, hdisj⟩ : ∃ t : Set Y, IsOpen t ∧ x ∈ t ∧ ∀ y ∈ t,
      ¬ (y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvBM R 𝔍 T y = l) := by
    by_cases hxc : x ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp
    · have hxl : stepOneInvBM R 𝔍 T x < l := lt_of_le_of_ne (hle x hxc hxW) fun h => hx ⟨hxc, h⟩
      obtain ⟨t, hts, hto, hxt⟩ := mem_nhds_iff.mp
        (stepOneInvBM_usc 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan x hxc)
      exact ⟨t, hto, hxt, fun y hy hyl => absurd hyl.2 (((hts hy) hyl.1).trans_lt hxl).ne⟩
    · have hcl : IsClosed (geoTransformAlong (barMarked 𝔍) T).cosupp :=
        GiraudAlong.isClosed_cosupport_along hwf.isCoherent hwf.isClosedSubmanifold_N _
      exact ⟨_, hcl.isOpen_compl, hxc, fun y hy hyl => hy hyl.1⟩
  refine ⟨W ⊓ ⟨t, hto⟩, ⟨hxW, hxt⟩, inf_le_left, ?_⟩
  exact eq_empty_iff_forall_notMem.mpr fun v hv => hdisj v v.2.2 hv

/-- **Near a point of the level set of a non-special value** `(s, λ)`, `s` the level of the point, the level set is an
admissible centre (given the anchor change): on `V = W ∩ T₁⁻¹ W_x` it is the level set `{R = λ}` of the lower invariant on the
cosupport of the lower marked ideal of `x`, admissible for the restriction of its transform by the field `admissible` of `R`,
hence admissible for the restriction of `J̄_T` by the transfer `isAdmissibleCentre_of_lowerBM`. -/
theorem exists_opens_isAdmissibleCentre_of_eq (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) (W : Opens Y) {x : Y} (l : Λ)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W →
      stepOneInvBM R 𝔍 T y ≤ toLex (level 𝔍 T x, (l : WithTop Λ)))
    (hxW : x ∈ W) (hx : x ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (hsp : ¬ IsSpecial 𝔍 T x) :
    ∃ V : Opens Y, x ∈ V ∧ V ≤ W ∧
      (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
        ((Subtype.val : V → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
          stepOneInvBM R 𝔍 T y = toLex (level 𝔍 T x, (l : WithTop Λ))}) := by
  set s := level 𝔍 T x with hs
  set r := regimeRun (stepRegime 𝔍 s) T x with hr
  have hreg : stepRegime 𝔍 s T x := ⟨rfl, hsp⟩
  have hsplit : (head T r).append (tail T r) = T := head_append_tail T r
  have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T r).append (tail T r)) := by rw [hsplit]; exact hT
  have hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T.length → IsGeoTestTower (barMarked 𝔍) T'' →
      IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T'' → HasLowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T'' :=
    fun T'' _ hT'' hcan'' => hasLowerDataG_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk T'' hT'' hcan''
  -- the lower data of `x`
  obtain ⟨hxM, hdom₀, hcan₀, -⟩ := hD T le_rfl hT hcan x hx hsp
  obtain ⟨hreg₀, hy₀⟩ := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T hT hx hsp
  have hTW := isGeoTestTower_of_isCanonical R hdom₀ _ hcan₀
  -- the neighbourhood
  set P : Opens Y := openPreimage (tail T r) (maskBM 𝔍 s (head T r) ((tail T r).proj x)) with hP
  have hVP : W ⊓ P ≤ P := inf_le_right
  refine ⟨W ⊓ P, ⟨hxW, hxM⟩, inf_le_left, ?_⟩
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hT
  have hVc : (MarkedIdeal.pullback (Subtype.val : (W ⊓ P : Opens Y) → Y)
      (geoTransformAlong (barMarked 𝔍) T)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcT
  have hcos : ∀ q : P, q ∈ (geoTransformAlong (lowerBM 𝔍 s (head T r) ((tail T r).proj x))
      (restrict (maskBM 𝔍 s (head T r) ((tail T r).proj x)) (tail T r))).cosupp ↔
        (q : Y) ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ level 𝔍 T q = s := by
    intro q
    rw [HironakaG11InvBMLowerTailSucc.mem_cosupp_lowerBM_iff 𝔍 h𝔍 hd hn hmax (head T r) (tail T r) hT₀₁ hy₀ hreg₀.1
      hTW q, hsplit]
  have hle'' : ∀ q ∈ (geoTransformAlong (lowerBM 𝔍 s (head T r) ((tail T r).proj x))
      (restrict (maskBM 𝔍 s (head T r) ((tail T r).proj x)) (tail T r))).cosupp,
        q ∈ nestedOpens P (W ⊓ P) →
        R.inv (lowerBM 𝔍 s (head T r) ((tail T r).proj x))
          (restrict (maskBM 𝔍 s (head T r) ((tail T r).proj x)) (tail T r)) q ≤ l := by
    intro q hq hqV
    have hv := stepOneInvBM_eq_lower 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan hD hx hreg rfl q hq
    have h := hle q ((hcos q).mp hq).1 hqV.1
    rw [hv, Prod.Lex.toLex_le_toLex] at h
    rcases h with h | ⟨-, h⟩
    · exact absurd h (lt_irrefl _)
    · exact WithTop.coe_le_coe.mp h
  -- the field `admissible` of `R` on `W ∩ P`, then the transfer
  have hadm := R.admissible _ hdom₀ _ hcan₀ (nestedOpens P (W ⊓ P)) l hle''
  have htr' := isAdmissibleCentre_of_lowerBM 𝔍 h𝔍 hd hn hmax (head T r) (tail T r) hT₀₁ hy₀ hreg₀.1 hdom₀ hTW
    (nestedOpens P (W ⊓ P)) _ hadm
  rw [show (head T r).append (tail T r) = T from hsplit, pullback_val_pullback_val hcT hVP] at htr'
  have hset : (Subtype.val : nestedOpens P (W ⊓ P) → P) ⁻¹'
      {q | q ∈ (geoTransformAlong (lowerBM 𝔍 s (head T r) ((tail T r).proj x))
          (restrict (maskBM 𝔍 s (head T r) ((tail T r).proj x)) (tail T r))).cosupp ∧
        R.inv (lowerBM 𝔍 s (head T r) ((tail T r).proj x))
          (restrict (maskBM 𝔍 s (head T r) ((tail T r).proj x)) (tail T r)) q = l} =
      (nestedOpensDiffeo (n := n) hVP) ⁻¹' ((Subtype.val : (W ⊓ P : Opens Y) → Y) ⁻¹'
        {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
          stepOneInvBM R 𝔍 T y = toLex (s, (l : WithTop Λ))}) := by
    ext w
    simp only [mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨hq, hql⟩
      refine ⟨((hcos _).mp hq).1, ?_⟩
      have hv := stepOneInvBM_eq_lower 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan hD hx hreg rfl _ hq
      rw [hql] at hv
      exact hv
    · rintro ⟨hc, hv⟩
      replace hc : ((w : P) : Y) ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp := hc
      replace hv : stepOneInvBM R 𝔍 T ((w : P) : Y) = toLex (s, (l : WithTop Λ)) := hv
      have hlev : level 𝔍 T ((w : P) : Y) = s := by
        have h := congrArg (fun p => (ofLex p).1) hv
        simp only [ofLex_toLex] at h
        rw [← h]
        exact (stepOneInvG_fst R 𝔍 _ _ T _).symm
      have hq := (hcos (w : P)).mpr ⟨hc, hlev⟩
      refine ⟨hq, ?_⟩
      rw [stepOneInvBM_eq_lower 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan hD hx hreg rfl _ hq] at hv
      have h := congrArg (fun p => (ofLex p).2) hv
      simp only [ofLex_toLex] at h
      exact WithTop.coe_injective h
  rw [hset] at htr'
  exact (MarkedIdealTowerTransport.isAdmissibleCentre_pullback_iff (Φ := nestedOpensDiffeo (n := n) hVP) hVc).mp htr'

end Local

/-! ### Property (1) -/

section Admissible

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **Property (1) at the values `(s, λ)`** (given the anchor change). -/
theorem stepOneInvBM_admissible_coe (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) (W : Opens Y)
    (s : ℕ) (l : Λ)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W →
      stepOneInvBM R 𝔍 T y ≤ toLex (s, (l : WithTop Λ))) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        stepOneInvBM R 𝔍 T y = toLex (s, (l : WithTop Λ))}) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hT
  refine isAdmissibleCentre_pullback_val_of_forall_exists_opens hcT W fun x hxW => ?_
  by_cases hx : x ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
      stepOneInvBM R 𝔍 T x = toLex (s, (l : WithTop Λ))
  · obtain ⟨hxc, hxv⟩ := hx
    have hsp : ¬ IsSpecial 𝔍 T x := fun h => by
      have hxv' : stepOneInvG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T x = toLex (s, (l : WithTop Λ)) := hxv
      rw [stepOneInvG_of_isSpecial R 𝔍 _ _ T h] at hxv'
      have := congrArg (fun p => (ofLex p).2) hxv'
      simp only [ofLex_toLex] at this
      exact WithTop.top_ne_coe this
    have hlev : level 𝔍 T x = s := by
      have h := congrArg (fun p => (ofLex p).1) hxv
      simp only [ofLex_toLex] at h
      rw [← h]
      exact (stepOneInvG_fst R 𝔍 _ _ T x).symm
    subst hlev
    exact exists_opens_isAdmissibleCentre_of_eq 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan W l hle hxW hxc hsp
  · obtain ⟨V, hxV, hVW, hV⟩ := exists_opens_preimage_eq_empty 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan W _ hle hxW hx
    refine ⟨V, hxV, hVW, ?_⟩
    rw [hV]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Property (1) of Bierstone--Milman's Step 1 value at every value** (given the anchor change): the values `(s, ∞)` by
`HironakaG11InvBMUSC.stepOneInvBM_admissible_top`, the values `(s, λ)` by `stepOneInvBM_admissible_coe`. -/
theorem stepOneInvBM_admissible (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) (W : Opens Y)
    (l : ℕ ×ₗ WithTop Λ)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W → stepOneInvBM R 𝔍 T y ≤ l) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvBM R 𝔍 T y = l}) := by
  obtain ⟨⟨s, t⟩, rfl⟩ : ∃ p : ℕ × WithTop Λ, toLex p = l := ⟨ofLex l, toLex_ofLex l⟩
  induction t using WithTop.recTopCoe with
  | top => exact stepOneInvBM_admissible_top R 𝔍 h𝔍 hd hn hmax T hT W s hle
  | coe l => exact stepOneInvBM_admissible_coe 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan W s l hle

/-- **The maximum locus is an admissible centre** of `J̄_T` (given the anchor change). -/
theorem isAdmissibleCentre_maxLocus_stepOneInvBM (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) :
    (geoTransformAlong (barMarked 𝔍) T).IsAdmissibleCentre
      (maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) := by
  by_cases hne : (maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hadm := stepOneInvBM_admissible 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan ⊤ (stepOneInvBM R 𝔍 T y₀)
      (fun y hy _ => hy₀.2 y hy)
    rw [← ResolutionInvariantDriver.maxLocus_eq_level hy₀] at hadm
    have hJ := isWellFormed_barMarked 𝔍 h𝔍
    obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T
      hT
    exact ResolutionInvariantDriver.isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) hadm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Canonical segments of Bierstone--Milman's Step 1 value are multiple test blow-ups of `J̄`** (given the anchor change). -/
theorem isGeoTestTower_of_isCanonical_stepOneInvBM (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T →
      IsGeoTestTower (barMarked 𝔍) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hcanT, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) := hcan
      have hTt := isGeoTestTower_of_isCanonical_stepOneInvBM hAC h𝔍 hd hn hmax hk T hcanT
      refine (isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hTt, ?_⟩
      rcases hC with rfl | rfl
      · exact MarkedIdeal.isAdmissibleCentre_empty _
      · exact isAdmissibleCentre_maxLocus_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk T hTt hcanT

end Admissible


/-! ### Properties (3) and (4) -/

section Decrease

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **A maximum at a special point**: if the maximum of Bierstone--Milman's Step 1 value on `cosupp J̄_T` is attained at a special
point, the maximum locus is that of W's value (both are the special points of its level). -/
theorem maxLocus_stepOneInvBM_eq_of_isSpecial (R : ResolutionInvariant.{u, v} n k Λ) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) {x : Y}
    (hx : x ∈ maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) (hsp : IsSpecial 𝔍 T x) :
    maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp =
      maxLocus (stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T) (geoTransformAlong (barMarked 𝔍) T).cosupp := by
  have hGx : stepOneInvBM R 𝔍 T x = toLex (level 𝔍 T x, (⊤ : WithTop Λ)) :=
    stepOneInvG_of_isSpecial R 𝔍 _ _ T hsp
  have hLx : stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T x = toLex (level 𝔍 T x, (⊤ : WithTop Λ)) :=
    stepOneInvL_of_isSpecial R 𝔍 _ T hsp
  have hxL : x ∈ maxLocus (stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T) (geoTransformAlong (barMarked 𝔍) T).cosupp := by
    refine ⟨hx.1, fun y hy => ?_⟩
    have hl := level_le_of_stepOneInvG_le R 𝔍 _ _ T ((hx.2 y hy).trans_eq hGx)
    rw [hLx, Prod.Lex.le_iff, stepOneInvL_fst]
    simp only [ofLex_toLex]
    rcases hl.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, le_top⟩
  rw [ResolutionInvariantDriver.maxLocus_eq_level hx, ResolutionInvariantDriver.maxLocus_eq_level hxL, hGx, hLx]
  ext y
  refine and_congr_right fun hy => ?_
  rw [stepOneInvBM_eq_top_iff R 𝔍 h𝔍 hd hn hmax T hT hy,
    StepOneAdmissibleTop.stepOneInvL_eq_top_iff R 𝔍 _ h𝔍 hd hn hmax T hT hy]

variable (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **Property (3) of Bierstone--Milman's Step 1 value** (given the anchor change; along a canonical segment `T` whose
continuation by the blowup of the maximum locus is a multiple test blow-up of `J̄`): the value drops over the centre and is
unchanged off it.  (Special points: W's `StepOneSpecialDrop`, the maximum locus being the same; non-special points: a smaller
level, or the same level and the canonical-tail theorem.) -/
theorem stepOneInvBM_decrease (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower (barMarked 𝔍) (.step T C π hπ))
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T)
    (hC : C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) :
    ∀ z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp,
      (π z ∈ C → stepOneInvBM R 𝔍 (.step T C π hπ) z < stepOneInvBM R 𝔍 T (π z)) ∧
      (π z ∉ C → stepOneInvBM R 𝔍 (.step T C π hπ) z = stepOneInvBM R 𝔍 T (π z)) := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  have hcanS : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) (.step T C π hπ) := ⟨hcan, Or.inr hC⟩
  obtain ⟨hTT, hCadm⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
  intro z hz
  refine ⟨fun hzC => ?_, fun hzC =>
    stepOneInvBM_step_of_notMem_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk T C π hπ hT hcanS hz hzC⟩
  by_cases hsp : IsSpecial 𝔍 T (π z)
  · have hxmax : π z ∈ maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp := hC ▸ hzC
    have hC' : C = maxLocus (stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T) (geoTransformAlong (barMarked 𝔍) T).cosupp := by
      rw [hC]
      exact maxLocus_stepOneInvBM_eq_of_isSpecial 𝔍 R h𝔍 hd hn hmax T hTT hxmax hsp
    rcases Nat.eq_zero_or_pos (level 𝔍 T (π z)) with h0 | hpos
    · exact absurd hz (StepOneSpecialDrop.notMem_cosupp_step_of_isSpecial_zero R 𝔍 (lowerMarkedM 𝔍) h𝔍 hd hmax T C π
        hπ hT hC' hzC h0 hsp)
    · exact stepOneInvG_lt_of_level_lt R 𝔍 _ _
        (StepOneSpecialDrop.level_step_lt_of_isSpecial R 𝔍 (lowerMarkedM 𝔍) h𝔍 T C π hπ hT hC' hz hzC hpos hsp)
  · rcases (level_step_le 𝔍 hE T C π hπ z).lt_or_eq with hlt | heq
    · exact stepOneInvG_lt_of_level_lt R 𝔍 _ _ hlt
    · have hJ := isWellFormed_barMarked 𝔍 h𝔍
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N
        hJ.isCoherent T hTT
      have hzc : π z ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp :=
        proj_mem_cosupp_of_mem_cosupp (𝔪 := geoTransformAlong (barMarked 𝔍) T) hNT hcT (.step .refl C π hπ)
          ⟨trivial, hCadm⟩ hz
      have hreg : stepRegime 𝔍 (level 𝔍 T (π z)) T (π z) := ⟨rfl, hsp⟩
      have hmask := mem_lowerMask_of_stepRegime 𝔍 h𝔍 hd hn hmax T hTT hzc hreg
      have hzs : ¬ IsSpecial 𝔍 (.step T C π hπ) z :=
        (stepRegime_and_le_regimeRun_of_mem_lowerMask 𝔍 h𝔍 hd hmax T (.step .refl C π hπ) hT rfl hmask heq).1.2
      exact stepOneInvBM_step_lt_of_mem_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk T C π hπ hT hcanS hz hzC hzs hsp heq

/-- **Property (4) of Bierstone--Milman's Step 1 value** (given the anchor change): a blowup along the empty centre does not
change the values. -/
theorem stepOneInvBM_emptyStep (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) (hC : C = ∅)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) :
    ∀ z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp,
      stepOneInvBM R 𝔍 (.step T C π hπ) z = stepOneInvBM R 𝔍 T (π z) := by
  subst hC
  have hTS : IsGeoTestTower (barMarked 𝔍) (.step T ∅ π hπ) :=
    (isGeoTestTower_step_iff _ T ∅ π hπ).mpr ⟨hT, MarkedIdeal.isAdmissibleCentre_empty _⟩
  intro z hz
  exact stepOneInvBM_step_of_notMem_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk T ∅ π hπ hTS ⟨hcan, Or.inl rfl⟩ hz
    (Set.notMem_empty _)

end Decrease

/-! ### Along canonical segments: the test-tower hypothesis removed -/

section Canonical

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **The canonical-tail theorem along canonical segments** (given the anchor change). -/
theorem hasLowerDataG_stepOneInvBM_of_isCanonical (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) :
    HasLowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T :=
  hasLowerDataG_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk T
    (isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk T hcan) hcan

/-- **Property (1) along canonical segments.** -/
theorem stepOneInvBM_admissible_of_isCanonical (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) (W : Opens Y)
    (l : ℕ ×ₗ WithTop Λ)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W → stepOneInvBM R 𝔍 T y ≤ l) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ stepOneInvBM R 𝔍 T y = l}) :=
  stepOneInvBM_admissible 𝔍 R hAC h𝔍 hd hn hmax hk T
    (isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk T hcan) hcan W l hle

/-- **Property (2) along canonical segments.** -/
theorem stepOneInvBM_usc_of_isCanonical (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) :
    IsInvUSCOn (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp :=
  stepOneInvBM_usc 𝔍 R hAC h𝔍 hd hn hmax hk T
    (isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk T hcan) hcan

/-- **Property (3) along canonical segments** (`C ≠ ∅` is not needed). -/
theorem stepOneInvBM_decrease_of_isCanonical (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T)
    (hC : C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp) :
    ∀ z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp,
      (π z ∈ C → stepOneInvBM R 𝔍 (.step T C π hπ) z < stepOneInvBM R 𝔍 T (π z)) ∧
      (π z ∉ C → stepOneInvBM R 𝔍 (.step T C π hπ) z = stepOneInvBM R 𝔍 T (π z)) :=
  stepOneInvBM_decrease 𝔍 R hAC h𝔍 hd hn hmax hk T C π hπ
    (isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk (.step T C π hπ)
      (⟨hcan, Or.inr hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T ∧
        (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp)))
    hcan hC

/-- **Property (4) along canonical segments.** -/
theorem stepOneInvBM_emptyStep_of_isCanonical (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) (hC : C = ∅)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) :
    ∀ z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp,
      stepOneInvBM R 𝔍 (.step T C π hπ) z = stepOneInvBM R 𝔍 T (π z) :=
  stepOneInvBM_emptyStep 𝔍 R hAC h𝔍 hd hn hmax hk T C π hπ hC
    (isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk T hcan) hcan

end Canonical

end

end Hironaka.HironakaG11InvBMAdmissible
