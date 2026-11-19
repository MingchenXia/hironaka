import Hironaka.Resolution.HironakaG11InvBMMask

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The mask-generic Step 1 value under one blowup and between two start stages (repair (B'), plan module 2, part 2)

Blueprint: `hironaka-g11-inv-bm-mask.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` (module 2).

The copies, for the value `HironakaG11InvBMMask.stepOneInvG` with an arbitrary mask family `Mk` and lower family `L`, of the
family-generic lemmas of `StepOneValueMasked` (sections `Step` and `Avoid`); the proofs are those of `StepOneValueMasked`,
the mask entering only through `LowerDataG` / `HasLowerDataG`:

* under one blowup: `stepOneInvG_step_eq_of_regime`, **`stepOneInvG_step_of_notMem`** ((3) "equal off the centre" and (4),
  given lower data), `stepOneInvG_step_lt_of_level_lt`, `stepOneInvG_step_lt_of_mem` ((3) "drop over the centre");
* between two start stages: `stepOneInvG_lt_top_of_hasLowerData`, `toLex_top_le_stepOneInvG`,
  `stepOneInvG_lt_of_mem_lowerMask`, `disjoint_lowerMask_of_isCanonicalG`, **`centresAvoid_lowerMaskG`** (the centres between
  two start stages miss the earlier mask `lowerMask`, hence every smaller mask: `centresAvoid_mono`,
  **`centresAvoid_maskG`** for `Mk ≤ lowerMask`, e.g. Bierstone--Milman's masks `maskBM`).

The comparison of a point with the earlier masks needs no hypothesis on `Mk`: a non-special cosupport point with lower data has a
finite lower value whatever the mask, and the level bound comes from `lowerMask`.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMMaskStep

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneValueMasked
  Hironaka.StepOneLowerDomain Hironaka.StepOneMaskTower
  Hironaka.RestrictEmptyTower Hironaka.HironakaG11InvBMMask
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)

noncomputable section

variable {n : ℕ}

/-! ### The value under one blowup -/

section Step

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X) (Mk : MaskFamily 𝔍) (L : LowerFamilyG 𝔍 Mk)

/-- **The value after a blowup at a point whose image keeps its regime** is computed from the same stage, along the tail
extended by the blowup. -/
theorem stepOneInvG_step_eq_of_regime {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) {z : Z} (hz : ¬ IsSpecial 𝔍 (.step T C π hπ) z)
    (hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z)) :
    stepOneInvG R 𝔍 Mk L (.step T C π hπ) z = toLex (level 𝔍 (.step T C π hπ) z,
      lowerValueG R 𝔍 Mk L (level 𝔍 (.step T C π hπ) z)
        (head T (regimeRun (stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z)) T (π z)))
        (.step (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z)) T (π z))) C π hπ) z) := by
  rw [stepOneInvG_of_not_isSpecial R 𝔍 Mk L _ hz, regimeRun_step_of _ T C π hπ hreg]
  rfl

/-- **Properties (3) "equal off the centre" and (4) of the mask-generic Step 1 value**: along a multiple test blow-up `T` of
`J̄` followed by a blowup `π` along `C`, at `z` with `π z ∉ C` the value at `z` is that at `π z`, provided, if `π z` is not
special, `z` has lower data at the split of `T` at the start of the run of `π z` followed by `π`. -/
theorem stepOneInvG_step_of_notMem (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent)
    (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) {z : Z} (hzC : π z ∉ C)
    (hd : ¬ IsSpecial 𝔍 T (π z) → LowerDataG R 𝔍 Mk L (level 𝔍 T (π z))
      (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z)))
      (.step (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z))) C π hπ) z) :
    stepOneInvG R 𝔍 Mk L (.step T C π hπ) z = stepOneInvG R 𝔍 Mk L T (π z) := by
  have hl := level_step_of_notMem 𝔍 hE T C π hπ hzC
  have hs := isSpecial_step_iff_of_notMem 𝔍 hN h𝔞 hE T hT C π hπ hzC
  by_cases hsp : IsSpecial 𝔍 T (π z)
  · rw [stepOneInvG_of_isSpecial R 𝔍 Mk L _ (hs.mpr hsp), stepOneInvG_of_isSpecial R 𝔍 Mk L _ hsp, hl]
  · have hz : ¬ IsSpecial 𝔍 (.step T C π hπ) z := fun h => hsp (hs.mp h)
    have hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z) := ⟨hl.symm, hsp⟩
    rw [stepOneInvG_step_eq_of_regime R 𝔍 Mk L T C π hπ hz hreg, stepOneInvG_of_not_isSpecial R 𝔍 Mk L _ hsp, hl,
      lowerValueG_step_of_notMem R 𝔍 Mk L (hd hsp) hzC]

/-- **Property (3), drop over the centre, when the level drops.** -/
theorem stepOneInvG_step_lt_of_level_lt {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) {z : Z} (h : level 𝔍 (.step T C π hπ) z < level 𝔍 T (π z)) :
    stepOneInvG R 𝔍 Mk L (.step T C π hπ) z < stepOneInvG R 𝔍 Mk L T (π z) :=
  stepOneInvG_lt_of_level_lt R 𝔍 Mk L h

/-- **Property (3), drop over the centre, at a point keeping its regime** (given lower data). -/
theorem stepOneInvG_step_lt_of_mem {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) {z : Z} (hzC : π z ∈ C) (hz : ¬ IsSpecial 𝔍 (.step T C π hπ) z)
    (hzT : ¬ IsSpecial 𝔍 T (π z)) (hl : level 𝔍 (.step T C π hπ) z = level 𝔍 T (π z))
    (hd : LowerDataG R 𝔍 Mk L (level 𝔍 T (π z))
      (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z)))
      (.step (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z))) C π hπ) z) :
    stepOneInvG R 𝔍 Mk L (.step T C π hπ) z < stepOneInvG R 𝔍 Mk L T (π z) := by
  have hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z) := ⟨hl.symm, hzT⟩
  rw [stepOneInvG_step_eq_of_regime R 𝔍 Mk L T C π hπ hz hreg, stepOneInvG_of_not_isSpecial R 𝔍 Mk L _ hzT, hl,
    Prod.Lex.toLex_lt_toLex]
  right
  exact ⟨rfl, lowerValueG_step_lt_of_mem R 𝔍 Mk L hd hzC⟩

end Step

/-! ### The steps between two start stages -/

section Avoid

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X) (Mk : MaskFamily 𝔍) (L : LowerFamilyG 𝔍 Mk)

/-- Under lower data the value at a non-special point is below `(s(y), ∞)`. -/
theorem stepOneInvG_lt_top_of_hasLowerData {Y : CMfd.{u} n} {T : BlowupTower X Y} (hD : HasLowerDataG R 𝔍 Mk L T)
    {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (hsp : ¬ IsSpecial 𝔍 T y) :
    stepOneInvG R 𝔍 Mk L T y < toLex (level 𝔍 T y, (⊤ : WithTop Λ)) := by
  obtain ⟨h, -⟩ := hD y hy hsp
  rw [stepOneInvG_of_not_isSpecial R 𝔍 Mk L T hsp, lowerValueG_eq_of_mem R 𝔍 Mk L h, Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, WithTop.coe_lt_top _⟩

/-- Out of the regime of level `s`, at level at least `s`, the value is at least `(s, ∞)`. -/
theorem toLex_top_le_stepOneInvG {Y : CMfd.{u} n} (T : BlowupTower X Y) {s : ℕ} {w : Y} (hl : s ≤ level 𝔍 T w)
    (hn : ¬ stepRegime 𝔍 s T w) : toLex (s, (⊤ : WithTop Λ)) ≤ stepOneInvG R 𝔍 Mk L T w := by
  by_cases hsp : IsSpecial 𝔍 T w
  · rw [stepOneInvG_of_isSpecial R 𝔍 Mk L T hsp, Prod.Lex.toLex_le_toLex]
    rcases hl.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, le_rfl⟩
  · have hlt : s < level 𝔍 T w := hl.lt_of_ne fun heq => hn ⟨heq.symm, hsp⟩
    rw [stepOneInvG_of_not_isSpecial R 𝔍 Mk L T hsp, Prod.Lex.toLex_le_toLex]
    exact Or.inl hlt

/-- **Over an earlier mask the values stay below a point out of the regime** (for every mask family and lower family; the
earlier mask is `lowerMask`, which contains every mask `Mk ≤ lowerMask`). -/
theorem stepOneInvG_lt_of_mem_lowerMask (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₁ Y₂ : CMfd.{u} n} (T₀ : BlowupTower X Y₁)
    (M : BlowupTower Y₁ Y₂) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append M)) {p₁ : Y₁}
    (hp₁ : level 𝔍 T₀ p₁ = s) (hD : HasLowerDataG R 𝔍 Mk L (T₀.append M)) {q : Y₂}
    (hq : q ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp) (hqW : M.proj q ∈ lowerMask 𝔍 s T₀ p₁)
    {w : Y₂} (hw : s ≤ level 𝔍 (T₀.append M) w) (hnw : ¬ stepRegime 𝔍 s (T₀.append M) w) :
    stepOneInvG R 𝔍 Mk L (T₀.append M) q < stepOneInvG R 𝔍 Mk L (T₀.append M) w := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  have hle : level 𝔍 (T₀.append M) q ≤ s := by
    match s, hp₁, hqW with
    | 0, _, hqW => exact (level_eq_zero_of_mem_maskB 𝔍 hE T₀ M hqW).le
    | _ + 1, hp₁, hqW => exact (level_le_of_mem_maskA 𝔍 hE T₀ M hqW).trans hp₁.le
  rcases hle.lt_or_eq with hlt | heq
  · exact stepOneInvG_lt_of_level_lt R 𝔍 Mk L (hlt.trans_le hw)
  · have hreg := (stepRegime_and_le_regimeRun_of_mem_lowerMask 𝔍 h𝔍 hd hmax T₀ M hT hp₁ hqW heq).1
    have h1 := stepOneInvG_lt_top_of_hasLowerData R 𝔍 Mk L hD hq hreg.2
    rw [heq] at h1
    exact h1.trans_le (toLex_top_le_stepOneInvG R 𝔍 Mk L _ hw hnw)

/-- **The last centre misses the earlier mask** (for every mask family and lower family). -/
theorem disjoint_lowerMask_of_isCanonicalG (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₁ Y₂ Z : CMfd.{u} n} (T₀ : BlowupTower X Y₁)
    {p₁ : Y₁} (hp₁ : level 𝔍 T₀ p₁ = s) (M : BlowupTower Y₁ Y₂) (C : Set Y₂) (π : Z → Y₂)
    (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append M))
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvG R 𝔍 Mk L) (T₀.append (.step M C π hπ)))
    (hD : HasLowerDataG R 𝔍 Mk L (T₀.append M)) {w : Y₂}
    (hw : w ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp) (hlw : s ≤ level 𝔍 (T₀.append M) w)
    (hnw : ¬ stepRegime 𝔍 s (T₀.append M) w) :
    Disjoint C (M.proj ⁻¹' (lowerMask 𝔍 s T₀ p₁ : Set Y₁)) := by
  obtain ⟨-, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvG R 𝔍 Mk L) (T₀.append M) ∧
      (C = ∅ ∨ C = maxLocus (stepOneInvG R 𝔍 Mk L (T₀.append M))
        (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp) := hcan
  rcases hC with hC | hC
  · rw [hC]
    exact Set.empty_disjoint _
  · rw [Set.disjoint_left]
    intro q hqC hqW
    rw [hC] at hqC
    have hlt := stepOneInvG_lt_of_mem_lowerMask R 𝔍 Mk L h𝔍 hd hmax T₀ M hT hp₁ hD hqC.1 hqW hlw hnw
    exact absurd (hqC.2 w hw) (not_le.mpr hlt)

/-- **The centres between two start stages miss the earlier mask** (for every mask family and lower family;
`StepOneValueMasked.centresAvoid_lowerMaskL` for `Mk = lowerMask`): along a multiple test blow-up `T₀ M σ` of `J̄` which is a
canonical segment of `stepOneInvG R 𝔍 Mk L`, with lower data along the prefixes `T₀ M'`, for `p₁` of level `s` at `T₀` and `w`
of level at least `s` at `T₀ M`, in the cosupport and out of the regime of level `s`, the centres of `M σ` miss the mask
`lowerMask 𝔍 s T₀ p₁`. -/
theorem centresAvoid_lowerMaskG (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k' : ℕ} (hk : DimLE n 𝔍.N k') {s : ℕ} {Y₁ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₁) {p₁ : Y₁} (hp₁ : level 𝔍 T₀ p₁ = s) :
    ∀ {Y₂ Z : CMfd.{u} n} (M : BlowupTower Y₁ Y₂) (C : Set Y₂) (π : Z → Y₂) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower (barMarked 𝔍) (T₀.append (.step M C π hπ)) →
      IsCanonical (barMarked 𝔍) (stepOneInvG R 𝔍 Mk L) (T₀.append (.step M C π hπ)) →
      (∀ {Y₃ : CMfd.{u} n} (M' : BlowupTower Y₁ Y₃), M'.length ≤ M.length →
        IsGeoTestTower (barMarked 𝔍) (T₀.append M') →
        IsCanonical (barMarked 𝔍) (stepOneInvG R 𝔍 Mk L) (T₀.append M') →
        HasLowerDataG R 𝔍 Mk L (T₀.append M')) →
      ∀ w ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp, s ≤ level 𝔍 (T₀.append M) w →
        ¬ stepRegime 𝔍 s (T₀.append M) w → CentresAvoid (lowerMask 𝔍 s T₀ p₁) (.step M C π hπ)
  | _, _, .refl, C, π, hπ, hT, hcan, hD, w, hw, hlw, hnw => by
      have hT' : IsGeoTestTower (barMarked 𝔍) (T₀.append .refl) := hT.1
      have hcan' : IsCanonical (barMarked 𝔍) (stepOneInvG R 𝔍 Mk L) (T₀.append .refl) := hcan.1
      exact ⟨trivial, disjoint_lowerMask_of_isCanonicalG R 𝔍 Mk L h𝔍 hd hmax T₀ hp₁ .refl C π hπ hT' hcan
        (hD .refl le_rfl hT' hcan') hw hlw hnw⟩
  | _, _, .step M₂ C₂ π₂ hπ₂, C, π, hπ, hT, hcan, hD, w, hw, hlw, hnw => by
      have hT' : IsGeoTestTower (barMarked 𝔍) (T₀.append (.step M₂ C₂ π₂ hπ₂)) := hT.1
      have hcan' : IsCanonical (barMarked 𝔍) (stepOneInvG R 𝔍 Mk L) (T₀.append (.step M₂ C₂ π₂ hπ₂)) := hcan.1
      obtain ⟨hw₂, hl₂, hn₂⟩ := StepOneNearby.not_stepRegime_proj 𝔍 h𝔍 hd hn hmax hk (T₀.append M₂) C₂ π₂ hπ₂ hT' hw
        hlw hnw
      refine ⟨centresAvoid_lowerMaskG h𝔍 hd hn hmax hk T₀ hp₁ M₂ C₂ π₂ hπ₂ hT' hcan'
        (fun M' hM' => hD M' (hM'.trans (by rw [BlowupTower.length_step]; omega))) (π₂ w) hw₂ hl₂ hn₂, ?_⟩
      exact disjoint_lowerMask_of_isCanonicalG R 𝔍 Mk L h𝔍 hd hmax T₀ hp₁ (.step M₂ C₂ π₂ hπ₂) C π hπ hT' hcan
        (hD _ le_rfl hT' hcan') hw hlw hnw

/-- **Avoiding a larger open set avoids a smaller one.** -/
theorem centresAvoid_mono {X : CMfd.{u} n} {U V : Opens X} (hUV : U ≤ V) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresAvoid V T → CentresAvoid U T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, h => by
      obtain ⟨hT, hC⟩ := (centresAvoid_step_iff V T C π hπ).mp h
      exact (centresAvoid_step_iff U T C π hπ).mpr
        ⟨centresAvoid_mono hUV T hT, hC.mono_right (preimage_mono (fun x hx => hUV hx))⟩

/-- **The centres between two start stages miss the earlier mask of `Mk`**, for every mask family below `lowerMask` (e.g.
`maskBM`, `maskBM_le_lowerMask`). -/
theorem centresAvoid_maskG (hMk : ∀ (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀),
      Mk s T₀ y₀ ≤ lowerMask 𝔍 s T₀ y₀)
    (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k' : ℕ} (hk : DimLE n 𝔍.N k') {s : ℕ} {Y₁ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₁) {p₁ : Y₁} (hp₁ : level 𝔍 T₀ p₁ = s) {Y₂ Z : CMfd.{u} n} (M : BlowupTower Y₁ Y₂)
    (C : Set Y₂) (π : Z → Y₂) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append (.step M C π hπ)))
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvG R 𝔍 Mk L) (T₀.append (.step M C π hπ)))
    (hD : ∀ {Y₃ : CMfd.{u} n} (M' : BlowupTower Y₁ Y₃), M'.length ≤ M.length →
      IsGeoTestTower (barMarked 𝔍) (T₀.append M') →
      IsCanonical (barMarked 𝔍) (stepOneInvG R 𝔍 Mk L) (T₀.append M') →
      HasLowerDataG R 𝔍 Mk L (T₀.append M'))
    {w : Y₂} (hw : w ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp)
    (hlw : s ≤ level 𝔍 (T₀.append M) w) (hnw : ¬ stepRegime 𝔍 s (T₀.append M) w) :
    CentresAvoid (Mk s T₀ p₁) (.step M C π hπ) :=
  centresAvoid_mono (hMk s T₀ p₁) _
    (centresAvoid_lowerMaskG R 𝔍 Mk L h𝔍 hd hn hmax hk T₀ hp₁ M C π hπ hT hcan hD w hw hlw hnw)

end Avoid

end

end Hironaka.HironakaG11InvBMMaskStep
