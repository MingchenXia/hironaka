import Hironaka.Resolution.HironakaG11InvBMCanonicalTail
import Hironaka.Invariant.StepOneUSC
import Hironaka.Invariant.StepOneAdmissibleTop

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's Step 1 value: upper semicontinuity and the top level sets (repair (B'), plan module 8, part 1)

Blueprint: `hironaka-g11-inv-bm-lower.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §1 module 8, §6b.
Sources: Bierstone--Milman 2008, §5 Step I (the invariant at a point of `cosupp` is `(s(x), inv_{k-1}(x))`, `s` the number of
original divisor members through `x`, `inv_{k-1}` the invariant of the lower marked ideal), Włodarczyk 2005 Step 1 (the
special points); the skeleton is W's `StepOneUSC` and `StepOneAdmissibleTop` for the masked family.

Properties (2) and (1) at the top values of `stepOneInvBM R 𝔍` (the generic Step 1 value with Bierstone--Milman's lower family
`HironakaG11InvBMLower.lowerBM` on the masks `HironakaG11InvBMMask.maskBM`), along multiple test blow-ups of `J̄` which are
canonical segments, for a lower invariant `R` with the anchor change `AnchorChangeBM 𝔍 R` (a property of `R`, plan module 6):

* **`stepOneInvBM_usc`**: upper semicontinuity on the cosupport of `J̄_T` (special points: the level is upper semicontinuous;
  non-special points: over the mask of the point the values of its level are `(s, R(·))` of one lower marked ideal,
  `HironakaG11InvBMCanonicalTail.stepOneInvBM_eq_lower`, and `R` is upper semicontinuous);
* `stepOneInvBM_eq_top_iff`: the value `(s, ⊤)` is taken exactly at the special points of level `s`;
* **`stepOneInvBM_admissible_top`** (no hypothesis on `R`): on an open set where the value is `≤ (s, ⊤)` on the cosupport, the
  points of value `(s, ⊤)` form an admissible centre (they are the special points of level `s`, the same set as for W's value,
  `StepOneAdmissibleTop.stepOneInvL_admissible_top`).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMUSC

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
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Upper semicontinuity -/

section USC

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **Upper semicontinuity at a non-special point** (given the anchor change): along a multiple test blow-up `T` of `J̄` which
is a canonical segment of `stepOneInvBM R 𝔍`, near a non-special point `x` of the cosupport every point of the cosupport has
value at most that of `x`. -/
theorem stepOneInvBM_eventually_le_of_not_isSpecial (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hn : 0 < n) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) {x : Y}
    (hx : x ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (hsp : ¬ IsSpecial 𝔍 T x) :
    ∀ᶠ y in 𝓝 x, y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp → stepOneInvBM R 𝔍 T y ≤ stepOneInvBM R 𝔍 T x := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  set s := level 𝔍 T x with hs
  set r := regimeRun (stepRegime 𝔍 s) T x with hr
  have hreg : stepRegime 𝔍 s T x := ⟨rfl, hsp⟩
  have hsplit : (head T r).append (tail T r) = T := head_append_tail T r
  have hT₀₁ : IsGeoTestTower (barMarked 𝔍) ((head T r).append (tail T r)) := by rw [hsplit]; exact hT
  have hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T.length → IsGeoTestTower (barMarked 𝔍) T'' →
      IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T'' → HasLowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T'' :=
    fun T'' _ hT'' hcan'' => hasLowerDataG_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk T'' hT'' hcan''
  -- the lower data of `x`
  obtain ⟨hxW, hdom₀, hcan₀, hcos₀⟩ := hD T le_rfl hT hcan x hx hsp
  obtain ⟨hreg₀, hy₀⟩ := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T hT hx hsp
  have hTW := isGeoTestTower_of_isCanonical R hdom₀ _ hcan₀
  -- the open preimage of the mask
  set P : Opens Y := openPreimage (tail T r) (maskBM 𝔍 s (head T r) ((tail T r).proj x)) with hP
  -- `R` is upper semicontinuous at `x` on the lower marked ideal
  have husc := R.usc _ hdom₀ _ hcan₀ ⟨x, hxW⟩ hcos₀
  have hev := StepOneUSC.eventually_forall_mem_of_eventually P hxW husc
  -- the value at `x`
  have hvx := stepOneInvBM_eq_lower 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan hD hx hreg rfl ⟨x, hxW⟩ hcos₀
  filter_upwards [hev, P.isOpen.mem_nhds hxW] with y hy hyP hyc
  have hyl : level 𝔍 T y ≤ s := by
    have h := level_le_of_mem_maskBM 𝔍 hE (head T r) (tail T r) hreg₀.1 (q := y) hyP
    rwa [hsplit] at h
  rcases hyl.lt_or_eq with hlt | heq
  · exact (stepOneInvG_lt_of_level_lt R 𝔍 _ _ hlt).le
  · have hyc' : (⟨y, hyP⟩ : P) ∈ (geoTransformAlong (lowerBM 𝔍 s (head T r) ((tail T r).proj x))
        (restrict (maskBM 𝔍 s (head T r) ((tail T r).proj x)) (tail T r))).cosupp := by
      refine (HironakaG11InvBMLowerTailSucc.mem_cosupp_lowerBM_iff 𝔍 h𝔍 hd hn hmax (head T r) (tail T r) hT₀₁ hy₀
        hreg₀.1 hTW ⟨y, hyP⟩).mpr ⟨?_, ?_⟩
      · rw [hsplit]; exact hyc
      · rw [hsplit]; exact heq
    have hvy := stepOneInvBM_eq_lower 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan hD hx hreg rfl ⟨y, hyP⟩ hyc'
    rw [hvx, hvy, Prod.Lex.toLex_le_toLex]
    exact Or.inr ⟨rfl, WithTop.coe_le_coe.mpr (hy hyP hyc')⟩

/-- **Property (2) of Bierstone--Milman's Step 1 value** (given the anchor change): along every multiple test blow-up `T` of
`J̄` which is a canonical segment of `stepOneInvBM R 𝔍`, the value is upper semicontinuous on the cosupport of `J̄_T`. -/
theorem stepOneInvBM_usc (hAC : AnchorChangeBM 𝔍 R) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) T) :
    IsInvUSCOn (stepOneInvBM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  intro x hx
  by_cases hsp : IsSpecial 𝔍 T x
  · filter_upwards [StepOneUSC.eventually_level_le 𝔍 hE T x] with y hy _
    exact stepOneInvG_le_of_isSpecial R 𝔍 _ _ hsp hy
  · exact stepOneInvBM_eventually_le_of_not_isSpecial 𝔍 R hAC h𝔍 hd hn hmax hk T hT hcan hx hsp

end USC

/-! ### The top level sets -/

section Top

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X)

/-- **A value `≤ (s, ∞)` has level `≤ s`** (every mask family and lower family). -/
theorem level_le_of_stepOneInvG_le (Mk : MaskFamily 𝔍) (L : LowerFamilyG 𝔍 Mk) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) {y : Y} {s : ℕ} (h : stepOneInvG R 𝔍 Mk L T y ≤ toLex (s, (⊤ : WithTop Λ))) :
    level 𝔍 T y ≤ s := by
  rw [Prod.Lex.le_iff, stepOneInvG_fst] at h
  simp only [ofLex_toLex] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- **The top values of Bierstone--Milman's Step 1 value are the special points**: along a multiple test blow-up of `J̄`, a
point of the cosupport has the value `(s, ∞)` iff it is special of level `s`. -/
theorem stepOneInvBM_eq_top_iff (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (s : ℕ) :
    stepOneInvBM R 𝔍 T y = toLex (s, (⊤ : WithTop Λ)) ↔ IsSpecial 𝔍 T y ∧ level 𝔍 T y = s := by
  show stepOneInvG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T y = _ ↔ _
  by_cases hsp : IsSpecial 𝔍 T y
  · rw [stepOneInvG_of_isSpecial R 𝔍 _ _ T hsp]
    constructor
    · intro h
      exact ⟨hsp, congrArg (fun p => (ofLex p).1) h⟩
    · rintro ⟨-, h⟩
      rw [h]
  · rw [stepOneInvG_of_not_isSpecial R 𝔍 _ _ T hsp]
    refine ⟨fun h => ?_, fun h => absurd h.1 hsp⟩
    exact absurd (congrArg (fun p => (ofLex p).2) h)
      (lowerValueG_maskBM_ne_top R 𝔍 h𝔍 hd hn hmax (lowerBM 𝔍) T hT hy hsp)

/-- **Property (1) of Bierstone--Milman's Step 1 value at the top values** (no hypothesis on `R`): let `𝔍` be well formed with
`d ≥ 1`, of maximal order along `N`, `0 < n`, `T` a multiple test blow-up of `J̄` and `W` an open of its last stage on which
the value is `≤ (s, ∞)` on the cosupport.  Then the points of `W` in the cosupport with value `(s, ∞)` form an admissible
centre of the restriction to `W` of the transform: they are the special points of level `s`, the same set as for W's value
(`StepOneAdmissibleTop.stepOneInvL_admissible_top`). -/
theorem stepOneInvBM_admissible_top (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (W : Opens Y) (s : ℕ)
    (hle : ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, y ∈ W →
      stepOneInvBM R 𝔍 T y ≤ toLex (s, (⊤ : WithTop Λ))) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (barMarked 𝔍) T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        stepOneInvBM R 𝔍 T y = toLex (s, (⊤ : WithTop Λ))}) := by
  have hset : {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        stepOneInvBM R 𝔍 T y = toLex (s, (⊤ : WithTop Λ))} =
      {y | y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧
        stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T y = toLex (s, (⊤ : WithTop Λ))} := by
    ext y
    refine and_congr_right fun hy => ?_
    rw [stepOneInvBM_eq_top_iff R 𝔍 h𝔍 hd hn hmax T hT hy s,
      StepOneAdmissibleTop.stepOneInvL_eq_top_iff R 𝔍 (lowerMarkedM 𝔍) h𝔍 hd hn hmax T hT hy s]
  rw [hset]
  refine StepOneAdmissibleTop.stepOneInvL_admissible_top R 𝔍 (lowerMarkedM 𝔍) h𝔍 hd hn hmax T hT W s
    fun y hy hyW => ?_
  have hl := level_le_of_stepOneInvG_le R 𝔍 _ _ T (hle y hy hyW)
  rcases hl.lt_or_eq with hlt | heq
  · rw [Prod.Lex.le_iff, stepOneInvL_fst]
    exact Or.inl hlt
  · rw [Prod.Lex.le_iff, stepOneInvL_fst]
    exact Or.inr ⟨heq, le_top⟩

end Top

end

end Hironaka.HironakaG11InvBMUSC
