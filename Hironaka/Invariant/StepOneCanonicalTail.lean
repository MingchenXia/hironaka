/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneCompare
import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneMaskTower
import Hironaka.Invariant.StepOneNearby
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.StepOneValueMasked
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The canonical-tail theorem of Step 1: lower data along canonical segments

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1: the lower-dimensional
invariant of a point is that of the restricted marked ideal formed at the stage where the point entered its regime,
"along `T₁|_W`, which is a canonical segment of it" -- near the point, the centres of the canonical segment of the
Step 1 invariant are empty or the maximum loci of the lower-dimensional invariant.

Let `𝔍` be well formed with `d ≥ 1`, of maximal order along `N` with `dim N ≤ k` (`0 < n`), `R` a resolution invariant in
dimension `≤ k - 1` and `stepOneInvM R 𝔍` the Step 1 value function with the original members masked
(`StepOneValueMasked`).  **Main theorem** (`hasLowerDataL_of_isCanonical`): along every multiple test blow-up `T` of `J̄` which
is a canonical segment of `stepOneInvM R 𝔍`, every point of the cosupport which is not special has lower data at its split
(`StepOneValueMasked.LowerDataL`): the image lies in its mask, the lower marked ideal lies in the domain, the restricted tail is a
canonical segment of it, and the point lies in its cosupport.

Proof: induction on the length. After a further blowup `σ` along `C` (the maximum locus or empty), a point `y` whose
image `z = σ y` keeps its regime has the split of `z` with the tail extended by `σ`; the new centre traced on the
restricted tail is empty or the maximum locus of the lower-dimensional invariant
(`MaxLocusLocal.preimage_maxLocus_eq_or` with the strictly monotone `λ ↦ (s, λ)`), because at every point `q` of the
cosupport of the lower marked ideal the value is `(s, R(q))`: `stepOneInvM_eq_lower` -- `q` has the level `s`, lower
data at its own (possibly earlier) split by induction, the steps between the two starts miss its mask
(`StepOneValueMasked.centresAvoid_lowerMaskL`, with `exists_middle`), and `StepOneCompare` moves its value to the
reference point's lower marked ideal (Step 1bb with `StepOneTangentChange`); and the other points over the mask have
a smaller level. A point leaving its regime starts a new run with lower data from `StepOneValueMasked` and
`StepOneCompare` (`lowerDataL_refl`).

## Main results

* `centresAvoid_of_length_eq_zero`, `exists_eq_step_refl`, `mem_cosupp_head`, `level_le_head`: small tools;
* `mem_cosupp_lowerMarkedM_iff`: a point over the mask lies in the cosupport of the lower marked ideal along the restricted
  tail iff it lies in `cosupp J̄_T` and has the level of the mask;
* `lowerDataL_refl`: lower data along the empty tail;
* `lowerValueL_eq_succ_of_eq`, `lowerValueL_eq_zero_of_eq`: the comparison of `StepOneCompare` with the stages given
  by equations, Step 1bb finished by `inv_restrictedCoeffHom_eq_of_opens_disjoint`;
* `exists_middle`: the middle part between two start stages, with its centres missing the earlier mask;
* `stepOneInvM_eq_lower`: the value at a point of the cosupport of the lower marked ideal;
* `lowerDataL_step`, **`hasLowerDataL_of_isCanonical`**: the canonical-tail theorem;
* `stepOneInvM_step_of_notMem_of_isCanonical`, `stepOneInvM_step_lt_of_mem_of_isCanonical`: properties (3) "equal off the
  centre", (4), and (3) "drop over the centre" at non-special points keeping their level, now unconditional along canonical
  segments which are multiple test blow-ups.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneCanonicalTail

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneMaskTower Hironaka.StepOneNearby Hironaka.StepOneValueMasked Hironaka.StepOneCompare Hironaka.BoundaryCount Hironaka.InvDomainMemberRestriction Hironaka.MarkedIdealBiholomorphism Hironaka.RestrictEmptyTower Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong Hironaka.TangentDirectionAlong Hironaka.CoefficientIdealRestriction
open Hironaka.HomogenizedGlueingTower (strictAlong)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Small tools -/

section Tools

/-- A tower of length `0` has no centre, so it avoids every open set. -/
theorem centresAvoid_of_length_eq_zero {Y₁ Y₂ : CMfd.{u} n} (W : Opens Y₁) (M : BlowupTower Y₁ Y₂)
    (h : M.length = 0) : CentresAvoid W M := by
  cases M with
  | refl => trivial
  | step M C π hπ => simp [BlowupTower.length_step] at h

/-- A tower of length `1` is a single blowup. -/
theorem exists_eq_step_refl {Y₁ Y₂ : CMfd.{u} n} (τ : BlowupTower Y₁ Y₂) (h : τ.length = 1) :
    ∃ (C : Set Y₁) (π : Y₂ → Y₁) (hπ : IsBlowupAlong n C π), τ = .step .refl C π hπ := by
  cases τ with
  | refl => simp at h
  | step τ C π hπ =>
    cases τ with
    | refl => exact ⟨C, π, hπ, rfl⟩
    | step τ' C' π' hπ' => simp [BlowupTower.length_step] at h

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- The images of the points of the cosupport at the stages of a multiple test blow-up of `J̄` lie in the cosupport. -/
theorem mem_cosupp_head (h𝔍 : 𝔍.IsWellFormed) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (j : ℕ) :
    (tail T j).proj y ∈ (geoTransformAlong (barMarked 𝔍) (head T j)).cosupp := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hsplit := (isGeoTestTower_iff_head_tail (barMarked 𝔍) T j).mp hT
  obtain ⟨hNh, hch⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
    (head T j) hsplit.1
  rw [geoTransformAlong_head_tail (barMarked 𝔍) T j] at hy
  exact proj_mem_cosupp_of_mem_cosupp hNh hch (tail T j) hsplit.2 hy

/-- The level of the images at the earlier stages is at least the level (closed members). -/
theorem level_le_head (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) (j : ℕ) :
    level 𝔍 T y ≤ level 𝔍 (head T j) ((tail T j).proj y) := by
  have h := level_append_le 𝔍 hE (head T j) (tail T j) y
  rwa [head_append_tail] at h

end Tools

/-! ### The cosupport of the masked lower marked ideals; the empty tail -/

section Cosupp

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **The cosupport of the masked lower marked ideal along a restricted tail which is a multiple test blow-up of it**: a point
over the mask lies in it iff it lies in `cosupp J̄_{T₀ T₁}` and has the level `s` of the mask (`StepOneCompare`). -/
theorem mem_cosupp_lowerMarkedM_iff (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) (hl₀ : level 𝔍 T₀ y₀ = s)
    (hy₀W : y₀ ∈ lowerMask 𝔍 s T₀ y₀)
    (hTW : IsGeoTestTower (lowerMarkedM 𝔍 s T₀ y₀) (restrict (lowerMask 𝔍 s T₀ y₀) T₁))
    (q : openPreimage T₁ (lowerMask 𝔍 s T₀ y₀)) :
    q ∈ (geoTransformAlong (lowerMarkedM 𝔍 s T₀ y₀) (restrict (lowerMask 𝔍 s T₀ y₀) T₁)).cosupp ↔
      (q : Y) ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp ∧ level 𝔍 (T₀.append T₁) q = s := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  match s, hl₀, hy₀W, hTW, q with
  | 0, hl₀, hy₀W, hTW, q =>
    have h := (isGeoTestTower_cosupp_lowerMarkedB 𝔍 h𝔍 hd hmax T₀ T₁ hT hy₀).2
    have hl := level_eq_zero_of_mem_maskB 𝔍 hE T₀ T₁ q.2
    show q ∈ (geoTransformAlong (lowerMarkedB 𝔍 T₀ y₀) (restrict (maskB 𝔍 T₀ y₀) T₁)).cosupp ↔ _
    rw [h]
    exact ⟨fun hq => ⟨hq, hl⟩, fun hq => hq.1⟩
  | s' + 1, hl₀, hy₀W, hTW, q =>
    have h := mem_cosupp_lowerMarked_succ_iff 𝔍 h𝔍 hn T₀ T₁ hT hy₀W hTW q
    have hlev := level_eq_iff_of_mem_maskA 𝔍 hE T₀ T₁ (y₀ := y₀) (q := (q : Y)) q.2
    rw [hl₀] at hlev
    exact h.trans (and_congr_right fun _ => hlev.symm)

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **Lower data along the empty tail**: at a point of the cosupport in the regime of its level, along a multiple test
blow-up of `J̄`, the point has lower data for the empty tail (`StepOneValueMasked.mem_lowerMask_and_isInvDomain_M` and the
cosupport). -/
theorem lowerDataL_refl (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀} (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp)
    {s : ℕ} (hreg : stepRegime 𝔍 s T₀ y₀) : LowerDataL R 𝔍 (lowerMarkedM 𝔍) s T₀ .refl y₀ := by
  obtain ⟨hW, hdom⟩ := mem_lowerMask_and_isInvDomain_M 𝔍 h𝔍 hd hn hmax hk T₀ hT₀ hy₀ hreg
  refine ⟨hW, hdom, trivial, ?_⟩
  exact (mem_cosupp_lowerMarkedM_iff 𝔍 h𝔍 hd hn hmax T₀ .refl hT₀ hy₀ hreg.1 hW trivial ⟨y₀, hW⟩).mpr
    ⟨hy₀, hreg.1⟩

end Cosupp

/-! ### The comparison with the stages given by equations -/

section Compare

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **Step 1ab comparison, stages given by equations** (`StepOneCompare.lowerValue_eq_succ` with `T₀ = T₀' M` and the tail of
`p` equal to `M T₁`). -/
theorem lowerValueL_eq_succ_of_eq (h𝔍 : 𝔍.IsWellFormed) (hn : 0 < n) {s : ℕ} {Y₁ Y₀ Y : CMfd.{u} n}
    (T₀' : BlowupTower X Y₁) (M : BlowupTower Y₁ Y₀) (T₀ : BlowupTower X Y₀) (e : T₀'.append M = T₀)
    (T₁ : BlowupTower Y₀ Y) (T₁' : BlowupTower Y₁ Y) (e' : M.append T₁ = T₁')
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀}
    (hdom₀ : IsInvDomain (k - 1) (lowerMarkedM 𝔍 (s + 1) T₀ y₀))
    (hcan₀ : IsCanonical (lowerMarkedM 𝔍 (s + 1) T₀ y₀) (R.inv (lowerMarkedM 𝔍 (s + 1) T₀ y₀))
      (restrict (lowerMask 𝔍 (s + 1) T₀ y₀) T₁))
    {p : Y} (hpW : T₁.proj p ∈ lowerMask 𝔍 (s + 1) T₀ y₀) (hlp : level 𝔍 T₀ (T₁.proj p) = level 𝔍 T₀ y₀)
    (hcos₀ : (⟨p, hpW⟩ : openPreimage T₁ (lowerMask 𝔍 (s + 1) T₀ y₀)) ∈
      (geoTransformAlong (lowerMarkedM 𝔍 (s + 1) T₀ y₀) (restrict (lowerMask 𝔍 (s + 1) T₀ y₀) T₁)).cosupp)
    (hd₁ : LowerDataL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀' T₁' p)
    (hM : CentresAvoid (lowerMask 𝔍 (s + 1) T₀' (T₁'.proj p)) M) :
    lowerValueL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀' T₁' p =
      ((R.inv (lowerMarkedM 𝔍 (s + 1) T₀ y₀) (restrict (lowerMask 𝔍 (s + 1) T₀ y₀) T₁) ⟨p, hpW⟩ : Λ) : WithTop Λ) := by
  subst e e'
  exact lowerValue_eq_succ R 𝔍 h𝔍 hn T₀' M T₁ hT hdom₀ hcan₀ hpW hlp hcos₀ hd₁ hM

/-- **Step 1bb comparison, stages given by equations**: re-basing (`StepOneCompare.lowerValue_eq_zero_rebase`) and the
change of tangent direction on the masks (`StepOneTangentChange.inv_restrictedCoeffHom_eq_of_opens_disjoint`,
divisor kept): the lower value of `p` is the value of `R` for the masked lower marked ideal of `y₀` along `T₁|_W` at
`p`. -/
theorem lowerValueL_eq_zero_of_eq (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₁ Y₀ Y : CMfd.{u} n}
    (T₀' : BlowupTower X Y₁) (M : BlowupTower Y₁ Y₀) (T₀ : BlowupTower X Y₀) (e : T₀'.append M = T₀)
    (T₁ : BlowupTower Y₀ Y) (T₁' : BlowupTower Y₁ Y) (e' : M.append T₁ = T₁')
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp)
    (hdom₀ : IsInvDomain (k - 1) (lowerMarkedM 𝔍 0 T₀ y₀))
    (hcan₀ : IsCanonical (lowerMarkedM 𝔍 0 T₀ y₀) (R.inv (lowerMarkedM 𝔍 0 T₀ y₀))
      (restrict (lowerMask 𝔍 0 T₀ y₀) T₁))
    {p : Y} (hpW : T₁.proj p ∈ lowerMask 𝔍 0 T₀ y₀)
    (hpc : p ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp)
    (hd₁ : LowerDataL R 𝔍 (lowerMarkedM 𝔍) 0 T₀' T₁' p)
    (hM : CentresAvoid (lowerMask 𝔍 0 T₀' (T₁'.proj p)) M) :
    lowerValueL R 𝔍 (lowerMarkedM 𝔍) 0 T₀' T₁' p =
      ((R.inv (lowerMarkedM 𝔍 0 T₀ y₀) (restrict (lowerMask 𝔍 0 T₀ y₀) T₁) ⟨p, hpW⟩ : Λ) : WithTop Λ) := by
  subst e e'
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  have hT₀' : IsGeoTestTower (barMarked 𝔍) (T₀'.append M) := ((isGeoTestTower_append_iff _ _ T₁).mp hT).1
  obtain ⟨hq, hdomS, hcanS, hval⟩ := lowerValue_eq_zero_rebase R 𝔍 h𝔍 hd T₀' M T₁ hT hd₁ hM
  rw [hval]
  congr 1
  -- the tangent direction chosen at the base point of `y₀`
  obtain ⟨-, hu⟩ := tangentChoice_spec 𝔍 (exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax (T₀'.append M) hT₀' hy₀)
  -- the tangent direction chosen at the base point of `p`
  obtain ⟨h₁, -⟩ := hd₁
  have hxv : T₀'.proj ((M.append T₁).proj p) ∈ (tangentChoice 𝔍 (T₀'.proj ((M.append T₁).proj p))).1 :=
    (interior_subset h₁).1
  have hv := tangentChoice_spec_of_mem 𝔍 hxv
  have hbase : (T₀'.append M).proj (T₁.proj p) = T₀'.proj ((M.append T₁).proj p) := by
    rw [BlowupTower.proj_append, BlowupTower.proj_append]; rfl
  have hxU₁ : (T₀'.append M).proj (T₁.proj p) ∈ (tangentChoice 𝔍 ((T₀'.append M).proj y₀)).1 := (interior_subset hpW).1
  have hxU₂ : (T₀'.append M).proj (T₁.proj p) ∈ (tangentChoice 𝔍 (T₀'.proj ((M.append T₁).proj p))).1 := hbase ▸ hxv
  -- the base point of `p` lies in the cosupport of `𝔍`
  have hx : (T₀'.append M).proj (T₁.proj p) ∈ 𝔍.cosupp := by
    have hJ := isWellFormed_barMarked 𝔍 h𝔍
    have h := proj_mem_cosupp_of_mem_cosupp hJ.isClosedSubmanifold_N hJ.isCoherent _ hT hpc
    rw [cosupp_barMarked 𝔍 h𝔍 hd, BlowupTower.proj_append] at h
    exact h
  obtain ⟨O, hxO, hO⟩ := StepOneTangentChange.inv_restrictedCoeffHom_eq_of_opens_disjoint R 𝔍 h𝔍.isCoherent
    h𝔍.isClosedSubmanifold_N hd hx hu hxU₁ hv hxU₂
  have hWU₁ : ((maskB 𝔍 (T₀'.append M) y₀ : Opens Y₀) : Set Y₀) ⊆
      (T₀'.append M).proj ⁻¹' (tangentChoice 𝔍 ((T₀'.append M).proj y₀)).1 := fun z hz => (interior_subset hz).1
  have hWU₂ : ((openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p)) : Opens Y₀) : Set Y₀) ⊆
      (T₀'.append M).proj ⁻¹' (tangentChoice 𝔍 (T₀'.proj ((M.append T₁).proj p))).1 := by
    intro z hz
    have h := (interior_subset (show M.proj z ∈ maskB 𝔍 T₀' ((M.append T₁).proj p) from hz)).1
    show (T₀'.append M).proj z ∈ (tangentChoice 𝔍 (T₀'.proj ((M.append T₁).proj p))).1
    rw [BlowupTower.proj_append T₀' M]
    exact h
  have hdisj : ∀ H ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀'.append M)).E.take 𝔍.E.length,
      Disjoint ((maskB 𝔍 (T₀'.append M) y₀ : Opens Y₀) : Set Y₀) H := fun H hH =>
    Set.disjoint_left.mpr fun z hz hzH => (interior_subset hz).2.1 H hH hzH
  have hdisj' : ∀ H ∈ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀'.append M)).E.take 𝔍.E.length,
      Disjoint ((openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p)) : Opens Y₀) : Set Y₀) H := by
    intro H hH
    have hH' : H ∈ origMembers 𝔍 (T₀'.append M) := hH
    rw [origMembers_append] at hH'
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH'
    refine Set.disjoint_left.mpr fun z hz hzH => ?_
    have hzH₀ := MemberInterTowerAlong.strictAlong_subset_preimage M (isClosed_of_mem_origMembers 𝔍 hE T₀' H₀ hH₀) hzH
    exact (interior_subset (show M.proj z ∈ maskB 𝔍 T₀' ((M.append T₁).proj p) from hz)).2.1 H₀ hH₀ hzH₀
  exact (hO (T₀'.append M) T₁ hT (maskB 𝔍 (T₀'.append M) y₀) (openPreimage M (maskB 𝔍 T₀' ((M.append T₁).proj p)))
    hWU₁ hWU₂ hdisj hdisj' hdom₀ hcan₀ hdomS hcanS ⟨p, hpW⟩ ⟨p, hq⟩ rfl hxO hpc).symm

end Compare

/-! ### The middle part between two start stages -/

section Middle

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **The middle part between two start stages, empty over the earlier mask**: along a multiple test blow-up `T'` of `J̄` which
is a canonical segment of `stepOneInvM R 𝔍`, with lower data along every tower at most as long, let `z` be a point of the
cosupport of level `s` whose run in the regime of level `s` is `rz`, and `q` a point whose run `rq` is at least `rz`, with
image of level `s` at the start of its run.  Then the head at `rq` followed by a tower `M` is the head at `rz`, `M` followed by
the tail at `rz` is the tail at `rq`, and the centres of `M` miss the mask of the image of `q` (if `rq > rz`, the image of `z`
one stage before its start is out of the regime: `StepOneValueMasked.centresAvoid_lowerMaskL`). -/
theorem exists_middle (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y' : CMfd.{u} n} (T' : BlowupTower X Y')
    (hT : IsGeoTestTower (barMarked 𝔍) T') (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T')
    (hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T'.length → IsGeoTestTower (barMarked 𝔍) T'' →
      IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T'' → HasLowerDataL R 𝔍 (lowerMarkedM 𝔍) T'')
    {z q : Y'} (hz : z ∈ (geoTransformAlong (barMarked 𝔍) T').cosupp) {s : ℕ} (hzs : level 𝔍 T' z = s)
    {rz rq : ℕ} (hrz : regimeRun (stepRegime 𝔍 s) T' z = rz) (hrq : regimeRun (stepRegime 𝔍 s) T' q = rq)
    (hle : rz ≤ rq) (hp₁ : level 𝔍 (head T' rq) ((tail T' rq).proj q) = s) :
    ∃ M : BlowupTower (split T' rq).1 (split T' rz).1, (head T' rq).append M = head T' rz ∧
      M.append (tail T' rz) = tail T' rq ∧ CentresAvoid (lowerMask 𝔍 s (head T' rq) ((tail T' rq).proj q)) M := by
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
      have hcanh : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) ((head T' rq).append (.step M₂ Cm πm hπm)) := by
        rw [heq]; exact isCanonical_head _ _ T' rz hcan
      have hlenM₂ : (head T' rq).length + M₂.length + 1 ≤ T'.length := by
        have h := congrArg BlowupTower.length hM₁
        rw [BlowupTower.length_append, length_head, length_head] at h
        rw [length_head]
        omega
      refine centresAvoid_lowerMaskL R 𝔍 (lowerMarkedM 𝔍) h𝔍 hd hn hmax hk (head T' rq) hp₁ M₂ Cm πm hπm hTh hcanh
        (fun M' hM' hT'' hcan'' => hD _ ?_ hT'' hcan'') _ hw hlw hnw
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
theorem level_le_of_mem_lowerMask (hE : ∀ H ∈ 𝔍.E, IsClosed H) {s : ℕ} {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) {y₀ : Y₀} (hl₀ : level 𝔍 T₀ y₀ = s) {q : Y} (hq : T₁.proj q ∈ lowerMask 𝔍 s T₀ y₀) :
    level 𝔍 (T₀.append T₁) q ≤ s := by
  match s, hl₀, hq with
  | 0, _, hq => exact (level_eq_zero_of_mem_maskB 𝔍 hE T₀ T₁ hq).le
  | _ + 1, hl₀, hq => exact (level_le_of_mem_maskA 𝔍 hE T₀ T₁ hq).trans hl₀.le

/-- **The value at a point of the cosupport of the lower marked ideal** (`hir:step-one-canonical-tail`): along a multiple test
blow-up `T'` of `J̄` which is a canonical segment of `stepOneInvM R 𝔍`, with lower data along every tower at most as long, let
`z` be a point of the cosupport in the regime of level `s`, with run `r`, and `q` a point of the cosupport of its lower marked
ideal along the restricted tail.  Then the value at `q` is `(s, R(q))`, `R` of that lower marked ideal at `q`: `q` has level
`s`, it entered the regime no later than `z` (`StepOneMaskTower`), the steps between the two starts miss its mask
(`exists_middle`), and `StepOneCompare` moves its value to the lower marked ideal of `z`. -/
theorem stepOneInvM_eq_lower (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y' : CMfd.{u} n} (T' : BlowupTower X Y')
    (hT : IsGeoTestTower (barMarked 𝔍) T') (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T')
    (hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T'.length → IsGeoTestTower (barMarked 𝔍) T'' →
      IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T'' → HasLowerDataL R 𝔍 (lowerMarkedM 𝔍) T'')
    {z : Y'} (hz : z ∈ (geoTransformAlong (barMarked 𝔍) T').cosupp) {s r : ℕ} (hreg : stepRegime 𝔍 s T' z)
    (hr : regimeRun (stepRegime 𝔍 s) T' z = r)
    (q : openPreimage (tail T' r) (lowerMask 𝔍 s (head T' r) ((tail T' r).proj z)))
    (hq : q ∈ (geoTransformAlong (lowerMarkedM 𝔍 s (head T' r) ((tail T' r).proj z))
      (restrict (lowerMask 𝔍 s (head T' r) ((tail T' r).proj z)) (tail T' r))).cosupp) :
    stepOneInvM R 𝔍 T' q = toLex (s, ((R.inv (lowerMarkedM 𝔍 s (head T' r) ((tail T' r).proj z))
      (restrict (lowerMask 𝔍 s (head T' r) ((tail T' r).proj z)) (tail T' r)) q : Λ) : WithTop Λ)) := by
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
  obtain ⟨hqc₀, hql₀⟩ := (mem_cosupp_lowerMarkedM_iff 𝔍 h𝔍 hd hn hmax (head T' r) (tail T' r) hT₀₁ hy₀ hreg₀.1 hy₀W
    hTW q).mp hq
  obtain ⟨hqreg, hqrun⟩ := stepRegime_and_le_regimeRun_of_mem_lowerMask 𝔍 h𝔍 hd hmax (head T' r) (tail T' r) hT₀₁
    hreg₀.1 q.2 hql₀
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
  obtain ⟨hqreg₀, -⟩ := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T' hT hqc hqreg.2
  rw [hql] at hqreg₀
  -- the middle part between the two starts
  obtain ⟨M, e₁, e₂, hM⟩ := exists_middle 𝔍 R h𝔍 hd hn hmax hk T' hT hcan hD hz hreg.1 hr rfl hle hqreg₀.1
  -- the value of `q`
  show stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T' q = _
  rw [stepOneInvL_of_not_isSpecial R 𝔍 _ T' hqreg.2, hql]
  congr 2
  -- the level of the image of `q` at the start of `z`
  have hlp : level 𝔍 (head T' r) ((tail T' r).proj q) = level 𝔍 (head T' r) ((tail T' r).proj z) := by
    rw [hreg₀.1]
    refine le_antisymm ?_ ?_
    · have h := level_le_of_mem_lowerMask 𝔍 hE (head T' r) (.refl) hreg₀.1 (q := (tail T' r).proj q) q.2
      exact h
    · have h := level_le_head 𝔍 hE T' q r
      rw [hql] at h
      exact h
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · exact lowerValueL_eq_zero_of_eq 𝔍 R h𝔍 hd hmax (head T' (regimeRun (stepRegime 𝔍 0) T' q)) M (head T' r) e₁
      (tail T' r) (tail T' (regimeRun (stepRegime 𝔍 0) T' q)) e₂ hT₀₁ hy₀ hdom₀ hcan₀ q.2 hqc₀ hqD hM
  · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    exact lowerValueL_eq_succ_of_eq 𝔍 R h𝔍 hn (head T' (regimeRun (stepRegime 𝔍 (s' + 1)) T' q)) M (head T' r) e₁
      (tail T' r) (tail T' (regimeRun (stepRegime 𝔍 (s' + 1)) T' q)) e₂ hT₀₁ hdom₀ hcan₀ q.2 hlp hq hqD hM

/-- **The induction step of the canonical-tail theorem**: along a multiple test blow-up `T' σ` of `J̄` which is a
canonical segment of `stepOneInvM R 𝔍` (`σ` the blowup along `C`), with lower data along every tower at most as long
as `T'`, a point `y` of the cosupport whose image `σ y` is in the regime of the level `s` of `y`, with run `r`, has
lower data at the split of `T'` at `r` followed by `σ`: the trace of `C` on the restricted tail is empty or the
maximum locus of the lower-dimensional invariant (`MaxLocusLocal.preimage_maxLocus_eq_or`, with
`stepOneInvM_eq_lower` and the smaller levels elsewhere over the mask), and `y` lies in the cosupport of the lower
marked ideal. -/
theorem lowerDataL_step (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y' Z : CMfd.{u} n} (T' : BlowupTower X Y')
    (C : Set Y') (π : Z → Y') (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (barMarked 𝔍) (.step T' C π hπ))
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) (.step T' C π hπ))
    (hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T'.length → IsGeoTestTower (barMarked 𝔍) T'' →
      IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T'' → HasLowerDataL R 𝔍 (lowerMarkedM 𝔍) T'')
    {y : Z} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) (.step T' C π hπ)).cosupp) {s r : ℕ}
    (hs : level 𝔍 (.step T' C π hπ) y = s) (hreg : stepRegime 𝔍 s T' (π y))
    (hr : regimeRun (stepRegime 𝔍 s) T' (π y) = r) :
    LowerDataL R 𝔍 (lowerMarkedM 𝔍) s (head T' r) (.step (tail T' r) C π hπ) y := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  obtain ⟨hT', hCadm⟩ := (isGeoTestTower_step_iff _ T' C π hπ).mp hT
  obtain ⟨hcan', hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T' ∧
      (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T') (geoTransformAlong (barMarked 𝔍) T').cosupp) := hcan
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
  have hcanS : IsCanonical (lowerMarkedM 𝔍 s (head T' r) ((tail T' r).proj (π y)))
      (R.inv (lowerMarkedM 𝔍 s (head T' r) ((tail T' r).proj (π y))))
      (restrict (lowerMask 𝔍 s (head T' r) ((tail T' r).proj (π y))) (.step (tail T' r) C π hπ)) := by
    refine ⟨hcan₀, ?_⟩
    rcases hC with hC | hC
    · left
      rw [hC]
      exact preimage_empty
    · rw [hC]
      refine MaxLocusLocal.preimage_maxLocus_eq_or Subtype.val (MaxLocusLocal.strictMono_toLex_coe s) ?_ ?_ ?_
      · intro q hq
        have h := ((mem_cosupp_lowerMarkedM_iff 𝔍 h𝔍 hd hn hmax (head T' r) (tail T' r) hT₀₁ hy₀ hreg₀.1 hy₀W hTW
          q).mp hq).1
        exact (congrArg (fun T : BlowupTower X Y' => (q : Y') ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) hsplit).mp h
      · intro q hq
        exact stepOneInvM_eq_lower 𝔍 R h𝔍 hd hn hmax hk T' hT' hcan' hD hz hreg hr q hq
      · intro q hq hqn
        refine ⟨⟨π y, hy₀W⟩, hcos₀, ?_⟩
        have hql₀ := level_le_of_mem_lowerMask 𝔍 hE (head T' r) (tail T' r) hreg₀.1 q.2
        have hql₁ : level 𝔍 T' q ≤ s :=
          (congrArg (fun T : BlowupTower X Y' => level 𝔍 T (q : Y') ≤ s) hsplit).mp hql₀
        rcases hql₁.lt_or_eq with hlt | heq
        · exact stepOneInvL_lt_of_level_lt R 𝔍 _ (hlt.trans_eq hreg.1.symm)
        · exfalso
          apply hqn
          refine (mem_cosupp_lowerMarkedM_iff 𝔍 h𝔍 hd hn hmax (head T' r) (tail T' r) hT₀₁ hy₀ hreg₀.1 hy₀W hTW
            q).mpr ⟨?_, ?_⟩
          · exact (congrArg (fun T : BlowupTower X Y' => (q : Y') ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp)
              hsplit).mpr hq
          · exact (congrArg (fun T : BlowupTower X Y' => level 𝔍 T (q : Y') = s) hsplit).mpr heq
  refine ⟨hy₀W, hdom₀, hcanS, ?_⟩
  -- the cosupport clause
  have heq : (head T' r).append (.step (tail T' r) C π hπ) = .step T' C π hπ := by
    rw [BlowupTower.append_step, hsplit]
  have hTs : IsGeoTestTower (barMarked 𝔍) ((head T' r).append (.step (tail T' r) C π hπ)) := by rw [heq]; exact hT
  refine (mem_cosupp_lowerMarkedM_iff 𝔍 h𝔍 hd hn hmax (head T' r) (.step (tail T' r) C π hπ) hTs hy₀ hreg₀.1 hy₀W
    (isGeoTestTower_of_isCanonical R hdom₀ _ hcanS) ⟨y, hy₀W⟩).mpr ⟨?_, ?_⟩
  · rw [heq]; exact hy
  · rw [heq]; exact hs

/-- **The canonical-tail theorem** (`hir:step-one-canonical-tail`): for `𝔍` well formed with `d ≥ 1`, of maximal order along
`N` with `dim N ≤ k` (`0 < n`) and `R` a resolution invariant in dimension `≤ k - 1`, along every multiple test blow-up of
`J̄ = 𝓒_N(𝓗_N(𝔍))` which is a canonical segment of the masked Step 1 value function `stepOneInvM R 𝔍`, every non-special point
of the cosupport has lower data at its split: its lower value is the value of `R` along one of its own canonical segments. -/
theorem hasLowerDataL_of_isCanonical (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T) :
    HasLowerDataL R 𝔍 (lowerMarkedM 𝔍) T := by
  suffices h : ∀ (m : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y), T.length ≤ m → IsGeoTestTower (barMarked 𝔍) T →
      IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T → HasLowerDataL R 𝔍 (lowerMarkedM 𝔍) T from
    h T.length T le_rfl hT hcan
  intro m
  induction m with
  | zero =>
    intro Y T hlen hT hcan y hy hsp
    cases T with
    | refl => exact lowerDataL_refl 𝔍 R h𝔍 hd hn hmax hk .refl trivial hy ⟨rfl, hsp⟩
    | step T' C π hπ => simp at hlen
  | succ m ih =>
    intro Y T hlen hT hcan y hy hsp
    cases T with
    | refl => exact lowerDataL_refl 𝔍 R h𝔍 hd hn hmax hk .refl trivial hy ⟨rfl, hsp⟩
    | step T' C π hπ =>
      have hlen' : T'.length ≤ m := by
        rw [BlowupTower.length_step] at hlen
        omega
      have hD : ∀ {Y₃ : CMfd.{u} n} (T'' : BlowupTower X Y₃), T''.length ≤ T'.length →
          IsGeoTestTower (barMarked 𝔍) T'' → IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T'' →
          HasLowerDataL R 𝔍 (lowerMarkedM 𝔍) T'' := fun T'' h => ih T'' (h.trans hlen')
      by_cases hreg : stepRegime 𝔍 (level 𝔍 (.step T' C π hπ) y) T' (π y)
      · rw [regimeRun_step_of _ T' C π hπ hreg]
        exact lowerDataL_step 𝔍 R h𝔍 hd hn hmax hk T' C π hπ hT hcan hD hy rfl hreg rfl
      · rw [regimeRun_step_of_not _ T' C π hπ hreg]
        exact lowerDataL_refl 𝔍 R h𝔍 hd hn hmax hk _ hT hy ⟨rfl, hsp⟩

/-- **Properties (3) "equal off the centre" and (4) of the masked Step 1 value function along canonical segments**: along a
multiple test blow-up `T σ` of `J̄` which is a canonical segment of `stepOneInvM R 𝔍`, at a point `z` of the cosupport with
`σ z` off the centre, the value at `z` is the value at `σ z` (no further hypothesis: the lower data come from the
canonical-tail theorem). -/
theorem stepOneInvM_step_of_notMem_of_isCanonical (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y Z : CMfd.{u} n} (T : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (barMarked 𝔍) (.step T C π hπ))
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) (.step T C π hπ)) {z : Z}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp) (hzC : π z ∉ C) :
    stepOneInvM R 𝔍 (.step T C π hπ) z = stepOneInvM R 𝔍 T (π z) := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  have hT' : IsGeoTestTower (barMarked 𝔍) T := hT.1
  refine stepOneInvL_step_of_notMem R 𝔍 _ h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hE T hT' C π hπ hzC fun hsp => ?_
  have hs := isSpecial_step_iff_of_notMem 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hE T hT' C π hπ hzC
  have hl := level_step_of_notMem 𝔍 hE T C π hπ hzC
  have hzD := hasLowerDataL_of_isCanonical 𝔍 R h𝔍 hd hn hmax hk _ hT hcan z hz fun h => hsp (hs.mp h)
  have hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z) := ⟨hl.symm, hsp⟩
  rw [regimeRun_step_of _ T C π hπ hreg, hl] at hzD
  exact hzD

/-- **Property (3), drop over the centre, at non-special points keeping their level, along canonical segments** (the lower
data from the canonical-tail theorem). -/
theorem stepOneInvM_step_lt_of_mem_of_isCanonical (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) {Y Z : CMfd.{u} n} (T : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (barMarked 𝔍) (.step T C π hπ))
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) (.step T C π hπ)) {z : Z}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp) (hzC : π z ∈ C)
    (hzs : ¬ IsSpecial 𝔍 (.step T C π hπ) z) (hzT : ¬ IsSpecial 𝔍 T (π z))
    (hl : level 𝔍 (.step T C π hπ) z = level 𝔍 T (π z)) :
    stepOneInvM R 𝔍 (.step T C π hπ) z < stepOneInvM R 𝔍 T (π z) := by
  refine stepOneInvL_step_lt_of_mem R 𝔍 _ T C π hπ hzC hzs hzT hl ?_
  have hzD := hasLowerDataL_of_isCanonical 𝔍 R h𝔍 hd hn hmax hk _ hT hcan z hz hzs
  have hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z) := ⟨hl.symm, hzT⟩
  rw [regimeRun_step_of _ T C π hπ hreg, hl] at hzD
  exact hzD

end Tail

end

end Hironaka.StepOneCanonicalTail
