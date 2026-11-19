import Hironaka.Resolution.HironakaG11PresM8EmptyCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's Step 1 value across an empty prefix: property (4') (repair (B'), plan module 8, part 2)

Blueprint: `hironaka-g11-pres-m8-empty-prefix.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c; property
(4') released by lane G11B to lane G11C (inbox I-1368, comment C-0002).  Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of
Proposition `pr:resol` (resolutions are compatible with extensions: isomorphisms inserted into the sequence, here blowups along
the empty set at the start); Bierstone--Milman 2008, §5 Step I.

Let `P` be a tower with only empty centres and `𝔍_P` the transform of `𝔍` along it.  The Step 1 value of `𝔍` with
Bierstone--Milman's lower family along `P T₁` is that of `𝔍_P` along `T₁` (property (4') of `hir:centre-function` for
`stepOneInvBM`), given the independence of the hypersurface of maximal contact for `𝔍` and `𝔍_P` (`TangentIndepBM`) and the
independence of empty members of the divisor (`HironakaG11InvBMEmptyMember.EmptyMemberIndep`), both properties of `R`.  The
skeleton is W's `StepOneEmptyPrefix` (levels, special points, regimes and runs are about `𝔍` and are reused unchanged); the
lower values are compared by `HironakaG11PresM8EmptyCore.lowerValueG_emptyPrefix_of`:

* `lowerValueG_emptyPrefix_inside`: the run stays inside `T₁` (split `(P H₀, T₁')` versus `(H₀, T₁')`);
* `lowerValueG_emptyPrefix_cover`: the run covers `T₁` and then all of `P` (split `(refl, P T₁)` versus `(refl, T₁)`):
  restricted concatenation, re-basing along `P` (`HironakaG11InvBMRebase.inv_rebase_lowerBM`), then the comparison with
  `H₀ = refl`;
* `stepOneInvBM_emptyPrefix_eq`, **`stepOneInvBM_emptyPrefix`**, **`emptyPrefix_field`** (the field `emptyPrefix` of
  `MaxOrderValue.IsMaxOrderValue` for `stepOneInvBM R`).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11PresM8EmptyPrefix

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneLowerDomain
  Hironaka.StepOneValueMasked Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong Hironaka.BlowupTowerIsomorphism
  Hironaka.BlowupTowerIsoTail Hironaka.MarkedIdealBiholomorphism
  Hironaka.HironakaG11InvBMMask Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG11InvBMCanonicalTail Hironaka.HironakaG11InvBMAdmissible
  Hironaka.HironakaG11InvBMTangentIndep Hironaka.HironakaG11InvBMNaturality
  Hironaka.HironakaG11InvBMEmptyMember Hironaka.HironakaG11PresM8EmptyCore
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open Hironaka.HomogenizedGlueingTower (strictAlong)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)
open Hironaka.RestrictEmptyTower (CentresAvoid isEmptyTower_restrict_iff)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant IsEmptyTower
  isGeoTestTower_of_isEmptyTower isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

section Lower

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **The lower values across an empty prefix, the run inside the tail** (both levels): at the split `(P H₀, T₁)` for `𝔍` and
`(H₀, T₁)` for `𝔍_P`, with lower data on both sides and the image at `P H₀` in the cosupport of level `s`, the lower values
agree. -/
theorem lowerValueG_emptyPrefix_inside (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n) {Y₁ Y₀ Z : CMfd.{u} n}
    (P : BlowupTower X Y₁) (hP : IsEmptyTower P) (hTIP : TangentIndepBM (geoTransformAlong 𝔍 P) R)
    (hEI : EmptyMemberIndep (k - 1) R.inv) (H₀ : BlowupTower Y₁ Y₀) (T₁ : BlowupTower Y₀ Z)
    (hT : IsGeoTestTower (barMarked 𝔍) ((P.append H₀).append T₁)) {s : ℕ} {z : Z}
    (ha : T₁.proj z ∈ (geoTransformAlong (barMarked 𝔍) (P.append H₀)).cosupp)
    (hl : level 𝔍 (P.append H₀) (T₁.proj z) = s)
    (hD : LowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s (P.append H₀) T₁ z)
    (hD' : LowerDataG R (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P)) (lowerBM (geoTransformAlong 𝔍 P)) s
      H₀ T₁ z) :
    lowerValueG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s (P.append H₀) T₁ z =
      lowerValueG R (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P)) (lowerBM (geoTransformAlong 𝔍 P)) s H₀ T₁
        z := by
  obtain ⟨h, hdom, hcan, hcos⟩ := hD
  rw [lowerValueG_eq_of_mem R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) h]
  have hw := isTangentDirectionAlong_tangentChoice_of_nonempty 𝔍
    ⟨_, maskBM_subset_tangent 𝔍 s (P.append H₀) _ h⟩
  have hLeq : lowerBM 𝔍 s (P.append H₀) (T₁.proj z) =
      MarkedIdeal.pullback (Subtype.val : maskBM 𝔍 s (P.append H₀) (T₁.proj z) → Y₀)
        (lowerIdealWBM 𝔍 s (tangentChoice 𝔍 ((P.append H₀).proj (T₁.proj z))).2 (P.append H₀)
          (throughMembers 𝔍 (P.append H₀) (T₁.proj z))) := by
    rw [lowerBM_eq, lowerIdealBM_eq_lowerIdealWBM]
  rw [hLeq] at hdom hcan hcos ⊢
  exact (lowerValueG_emptyPrefix_of 𝔍 R h𝔍 hd hn P hP hTIP hEI H₀ T₁ hT ha hl hD' ⟨_, hw.isOpen⟩ hw _
    (maskBM_subset_tangent 𝔍 s (P.append H₀) _) h hdom hcan hcos).symm

/-- **The lower values across an empty prefix, the run covering the tail and the prefix** (both levels): at the split
`(refl, P T₁)` for `𝔍` and `(refl, T₁)` for `𝔍_P`, with lower data on both sides, the base points in the regime of level `s`,
the lower values agree (restricted concatenation; re-basing along `P`, whose centres are empty; then
`lowerValueG_emptyPrefix_of` with `H₀ = refl`). -/
theorem lowerValueG_emptyPrefix_cover (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₁ Y : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P)
    (hTIP : TangentIndepBM (geoTransformAlong 𝔍 P) R) (hEI : EmptyMemberIndep (k - 1) R.inv) (T₁ : BlowupTower Y₁ Y)
    (hT : IsGeoTestTower (barMarked 𝔍) (P.append T₁)) {s : ℕ} {z : Y}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) (P.append T₁)).cosupp)
    (hreg₀ : stepRegime 𝔍 s .refl ((P.append T₁).proj z)) (hreg₁ : stepRegime 𝔍 s P (T₁.proj z))
    (hD : LowerDataG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s .refl (P.append T₁) z)
    (hD' : LowerDataG R (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P)) (lowerBM (geoTransformAlong 𝔍 P)) s
      .refl T₁ z) :
    lowerValueG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) s .refl (P.append T₁) z =
      lowerValueG R (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P)) (lowerBM (geoTransformAlong 𝔍 P)) s .refl
        T₁ z := by
  obtain ⟨h₁, hdom₁, hcan₁, hcos₁⟩ := hD
  rw [lowerValueG_eq_of_mem R 𝔍 _ _ h₁]
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨hPJ, hT₁J⟩ := (isGeoTestTower_append_iff _ P T₁).mp hT
  -- (i) the restricted concatenation
  obtain ⟨hcanb, hval⟩ := StepOneCompare.inv_restrict_append R (maskBM 𝔍 s .refl ((P.append T₁).proj z)) hdom₁ P T₁
    hcan₁
  have hp₁ : (P.append T₁).proj z = P.proj (T₁.proj z) := by rw [BlowupTower.proj_append]; rfl
  have hq : z ∈ openPreimage T₁ (openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z))) :=
    show P.proj (T₁.proj z) ∈ maskBM 𝔍 s .refl ((P.append T₁).proj z) from hp₁ ▸ h₁
  obtain ⟨hcosb, hvalb⟩ := hval z h₁ hq hcos₁
  rw [← hvalb]
  -- (ii) re-basing along `P`, whose centres are empty
  have hT' : IsGeoTestTower (barMarked 𝔍) ((BlowupTower.refl : BlowupTower X X).append P) := by
    rw [BlowupTower.refl_append]
    exact hPJ
  have hb₀ : (P.append T₁).proj z ∈ (geoTransformAlong (barMarked 𝔍) (BlowupTower.refl : BlowupTower X X)).cosupp :=
    proj_mem_cosupp_of_mem_cosupp hJ.isClosedSubmanifold_N hJ.isCoherent (P.append T₁) hT hz
  have hM : CentresAvoid (maskBM 𝔍 s .refl ((P.append T₁).proj z)) P :=
    ContactLowerValue.centresAvoid_of_isEmptyTower _ P hP
  obtain ⟨hdomS, hcanS, hvalS⟩ := HironakaG11InvBMRebase.inv_rebase_lowerBM 𝔍 R h𝔍 hd hn hmax .refl P hT' hb₀
    hreg₀.1 hM ⟨T₁.proj z, hq⟩ hp₁.symm hdom₁
    (restrict (openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z))) T₁) hcanb
  rw [hvalS ⟨z, hq⟩ hcosb]
  have hEqR := HironakaG11InvBMRebase.restrictEquiv_rebase_lowerBM 𝔍 h𝔍 hd hn hmax .refl P hT' hb₀ hreg₀.1 hM
    ⟨T₁.proj z, hq⟩ hp₁.symm
  have he : IsEmptyTower (restrict (maskBM 𝔍 s .refl ((P.append T₁).proj z)) P) :=
    (isEmptyTower_restrict_iff _ P).mpr hM
  have hdom₀ := InvDomainRebase.isInvDomain_geoTransformAlong_of_isEmptyTower hdom₁ _ he
  have hcosS := (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hEqR
    hdom₀.isWellFormed.isClosedSubmanifold_N.1 hdom₀.isWellFormed.isCoherent hdomS.isWellFormed.isCoherent
    (restrict (openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z))) T₁)).1
  have hcos₂ : (⟨z, hq⟩ : openPreimage T₁ (openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z)))) ∈
      (geoTransformAlong (MarkedIdeal.pullback
        (Subtype.val : openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z)) → Y₁)
        (lowerIdealBM 𝔍 s ((BlowupTower.refl : BlowupTower X X).append P) (T₁.proj z)))
        (restrict (openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z))) T₁)).cosupp := by
    rw [← hcosS, ← geoTransformAlong_append]
    exact hcosb
  rw [BlowupTower.refl_append] at hdomS hcanS hcos₂ ⊢
  rw [lowerIdealBM_eq_lowerIdealWBM] at hdomS hcanS hcos₂ ⊢
  -- (iii) the comparison with `H₀ = refl`, through the tangent direction chosen at the base point
  have hU : P.proj (T₁.proj z) ∈ (tangentChoice 𝔍 (P.proj (T₁.proj z))).1 := by
    have h := maskBM_subset_tangent 𝔍 s .refl _ h₁
    rw [hp₁] at h
    exact h
  have hw := isTangentDirectionAlong_tangentChoice_of_nonempty 𝔍 ⟨_, hU⟩
  have hO : ((openPreimage P (maskBM 𝔍 s .refl ((P.append T₁).proj z)) : Opens Y₁) : Set Y₁) ⊆
      (P.append (BlowupTower.refl : BlowupTower Y₁ Y₁)).proj ⁻¹' (tangentChoice 𝔍 (P.proj (T₁.proj z))).1 :=
    fun y hy => by
      have h := maskBM_subset_tangent 𝔍 s .refl ((P.append T₁).proj z) hy
      rw [hp₁] at h
      exact h
  have haP : T₁.proj z ∈ (geoTransformAlong (barMarked 𝔍) (P.append (BlowupTower.refl : BlowupTower Y₁ Y₁))).cosupp := by
    obtain ⟨hNP, hcP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
      P hPJ
    have hz' : z ∈ (geoTransformAlong (geoTransformAlong (barMarked 𝔍) P) T₁).cosupp := by
      rw [← geoTransformAlong_append]
      exact hz
    exact proj_mem_cosupp_of_mem_cosupp hNP hcP T₁ hT₁J hz'
  exact (lowerValueG_emptyPrefix_of 𝔍 R h𝔍 hd hn P hP hTIP hEI .refl T₁ hT haP hreg₁.1 hD' ⟨_, hw.isOpen⟩ hw _ hO
    hq hdomS hcanS hcos₂).symm

end Lower

/-! ### Property (4') -/

section EmptyPrefix

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **The values agree along `P T₁` and `T₁`** when both are canonical segments (`P` empty; given `TangentIndepBM` for `𝔍` and
`𝔍_P` and `EmptyMemberIndep` for `R`): equal levels and special points; at a non-special point the run either stays inside
`T₁` (`lowerValueG_emptyPrefix_inside`) or covers `T₁` and then all of `P` (`lowerValueG_emptyPrefix_cover`). -/
theorem stepOneInvBM_emptyPrefix_eq (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (hTI : TangentIndepBM 𝔍 R) {Y₁ : CMfd.{u} n}
    (P : BlowupTower X Y₁) (hP : IsEmptyTower P) (hTIP : TangentIndepBM (geoTransformAlong 𝔍 P) R)
    (hEI : EmptyMemberIndep (k - 1) R.inv) {Y : CMfd.{u} n} (T₁ : BlowupTower Y₁ Y)
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) (P.append T₁))
    (hcan' : IsCanonical (barMarked (geoTransformAlong 𝔍 P)) (stepOneInvBM R (geoTransformAlong 𝔍 P)) T₁) {z : Y}
    (hz : z ∈ (geoTransformAlong (barMarked 𝔍) (P.append T₁)).cosupp) :
    stepOneInvBM R 𝔍 (P.append T₁) z = stepOneInvBM R (geoTransformAlong 𝔍 P) T₁ z := by
  have hAC : AnchorChangeBM 𝔍 R := anchorChangeBM_of_tangentIndepBM 𝔍 R hTI
  have hACP : AnchorChangeBM (geoTransformAlong 𝔍 P) R := anchorChangeBM_of_tangentIndepBM _ R hTIP
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  obtain ⟨h𝔍', hd', hmax', hk'⟩ := StepOneEmptyPrefix.hypotheses_emptyPrefix 𝔍 h𝔍 hd hmax hk P hP
  have hT := isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk _ hcan
  have hT' := isGeoTestTower_of_isCanonical_stepOneInvBM _ R hACP h𝔍' hd' hn hmax' hk' _ hcan'
  have hPJ : IsGeoTestTower (barMarked 𝔍) P := ((isGeoTestTower_append_iff _ _ T₁).mp hT).1
  have hEqT := StepOneEmptyPrefix.restrictEquiv_barMarked_append 𝔍 h𝔍 hd P hP T₁ hT
  have hz' : z ∈ (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) T₁).cosupp := by
    rw [hEqT.cosupp_eq]
    exact hz
  have hD := hasLowerDataG_of_isCanonical 𝔍 R hAC h𝔍 hd hn hmax hk _ hT hcan z hz
  have hD' := hasLowerDataG_of_isCanonical _ R hACP h𝔍' hd' hn hmax' hk' _ hT' hcan' z hz'
  have hG : ∀ {Y₀ Z : CMfd.{u} n} (T : BlowupTower Y₁ Y₀) (C : Set Y₀) (π : Z → Y₀) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower (barMarked 𝔍) (P.append (.step T C π hπ)) → IsGeoTestTower (barMarked 𝔍) (P.append T) :=
    fun _ _ _ _ h => h.1
  have hQ : ∀ (s : ℕ) {Y₀ : CMfd.{u} n} (H₀ : BlowupTower Y₁ Y₀) (y : Y₀),
      IsGeoTestTower (barMarked 𝔍) (P.append H₀) →
        (stepRegime 𝔍 s (P.append H₀) y ↔ stepRegime (geoTransformAlong 𝔍 P) s H₀ y) :=
    fun s _ H₀ y hH => (StepOneEmptyPrefix.stepRegime_emptyPrefix_iff 𝔍 h𝔍 hd P hP H₀ hH s y).symm
  have hl := StepOneEmptyPrefix.level_emptyPrefix 𝔍 P hP T₁ z
  unfold stepOneInvBM
  by_cases hs : IsSpecial 𝔍 (P.append T₁) z
  · have hs' := (StepOneEmptyPrefix.isSpecial_emptyPrefix_iff 𝔍 h𝔍 hd P hP T₁ hT z).mpr hs
    rw [stepOneInvG_of_isSpecial R 𝔍 _ _ _ hs, stepOneInvG_of_isSpecial R _ _ _ _ hs', hl]
  · have hs' : ¬ IsSpecial (geoTransformAlong 𝔍 P) T₁ z :=
      fun h => hs ((StepOneEmptyPrefix.isSpecial_emptyPrefix_iff 𝔍 h𝔍 hd P hP T₁ hT z).mp h)
    have hregP := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 _ hT hz hs
    specialize hD hs
    specialize hD' hs'
    rw [stepOneInvG_of_not_isSpecial R 𝔍 _ _ _ hs, stepOneInvG_of_not_isSpecial R _ _ _ _ hs']
    rw [hl] at hD' ⊢
    obtain ⟨s, hsdef⟩ : ∃ s, level 𝔍 (P.append T₁) z = s := ⟨_, rfl⟩
    have hreg' : stepRegime (geoTransformAlong 𝔍 P) s T₁ z := ⟨hl.trans hsdef, hs'⟩
    rw [hsdef] at hD hD' hregP ⊢
    rcases (regimeRun_le_length (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z).lt_or_eq with hlt | heq
    · -- the run stays inside `T₁`
      have hr := StepOneEmptyPrefix.regimeRun_append_of_lt (stepRegime 𝔍 s) (stepRegime (geoTransformAlong 𝔍 P) s) P
        (fun H₀ => IsGeoTestTower (barMarked 𝔍) (P.append H₀)) hG (hQ s) T₁ z hT hlt
      rw [hr] at hD hregP ⊢
      simp only [head, tail] at hD hD' hregP ⊢
      rw [StepOneEmptyPrefix.split_append_of_le P T₁ _ hlt.le] at hD hregP ⊢
      dsimp only at hD hregP ⊢
      have hT₀₁ : IsGeoTestTower (barMarked 𝔍)
          ((P.append (head T₁ (regimeRun (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z))).append
            (tail T₁ (regimeRun (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z))) := by
        rw [BlowupTower.append_assoc, head_append_tail]
        exact hT
      congr 2
      exact lowerValueG_emptyPrefix_inside 𝔍 R h𝔍 hd hn P hP hTIP hEI _ _ hT₀₁ hregP.2 hregP.1.1 hD hD'
    · -- the run covers `T₁`, then all of `P`
      have hbase := StepOneEmptyPrefix.regime_base_of_regimeRun_eq (stepRegime (geoTransformAlong 𝔍 P) s) T₁ z
        hreg' heq
      have hbaseP : stepRegime 𝔍 s P (T₁.proj z) := (hQ s .refl (T₁.proj z) hPJ).mpr hbase
      have hstep : ∀ {Y' Z' : CMfd.{u} n} (T : BlowupTower X Y') (π : Z' → Y') (hπ : IsBlowupAlong n (∅ : Set Y') π),
          IsEmptyTower T → ∀ w : Z', stepRegime 𝔍 s (.step T ∅ π hπ) w → stepRegime 𝔍 s T (π w) := by
        intro Y' Z' T π hπ hTe w hw
        have hTt : IsGeoTestTower (barMarked 𝔍) T := isGeoTestTower_of_isEmptyTower _ T hTe
        have hl' := level_step_of_notMem 𝔍 hE T ∅ π hπ (notMem_empty (π w))
        have hs'' := isSpecial_step_iff_of_notMem 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hE T hTt ∅ π hπ
          (notMem_empty (π w))
        exact ⟨hl'.symm.trans hw.1, fun h => hw.2 (hs''.mpr h)⟩
      have hrP := StepOneEmptyPrefix.regimeRun_eq_length_of_isEmptyTower (stepRegime 𝔍 s) hstep P hP _ hbaseP
      have hr := StepOneEmptyPrefix.regimeRun_append_of_eq (stepRegime 𝔍 s) (stepRegime (geoTransformAlong 𝔍 P) s) P
        (fun H₀ => IsGeoTestTower (barMarked 𝔍) (P.append H₀)) hG (hQ s) T₁ z hT heq
      have hreg₀ : stepRegime 𝔍 s .refl ((P.append T₁).proj z) := by
        have hregT : stepRegime 𝔍 s (P.append T₁) z := ⟨hsdef, hs⟩
        have hrun : regimeRun (stepRegime 𝔍 s) (P.append T₁) z = (P.append T₁).length := by
          rw [hr, hrP, BlowupTower.length_append]
          omega
        exact StepOneEmptyPrefix.regime_base_of_regimeRun_eq (stepRegime 𝔍 s) (P.append T₁) z hregT hrun
      rw [hr, hrP] at hD ⊢
      rw [heq] at hD' ⊢
      simp only [head, tail] at hD hD' ⊢
      rw [StepOneEmptyPrefix.split_of_length_le (P.append T₁) _ (by rw [BlowupTower.length_append]; omega)] at hD ⊢
      rw [StepOneEmptyPrefix.split_of_length_le T₁ _ le_rfl] at hD' ⊢
      dsimp only at hD hD' ⊢
      congr 2
      exact lowerValueG_emptyPrefix_cover 𝔍 R h𝔍 hd hn hmax P hP hTIP hEI T₁ hT hz hreg₀ hbaseP hD hD'

/-- **Property (4') of Bierstone--Milman's Step 1 value** (given the independence of the hypersurface of maximal contact for
`𝔍` and `𝔍_P` and the independence of empty members of the divisor for `R`): for `𝔍` well formed with `d ≥ 1`, of maximal
order along `N` with `dim N ≤ k` (`0 < n`), `P` a tower with only empty centres and `P T₁` a canonical segment of
`stepOneInvBM R 𝔍`, the tower `T₁` is a canonical segment of `stepOneInvBM R 𝔍_P` and, at every point of the cosupport of
`J̄_{P T₁}`, the value of `𝔍` along `P T₁` is that of `𝔍_P` along `T₁` (induction on `T₁`: the maximum loci agree, the
cosupports being equal). -/
theorem stepOneInvBM_emptyPrefix (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hk : DimLE n 𝔍.N k) (hTI : TangentIndepBM 𝔍 R) {Y₁ : CMfd.{u} n}
    (P : BlowupTower X Y₁) (hP : IsEmptyTower P) (hTIP : TangentIndepBM (geoTransformAlong 𝔍 P) R)
    (hEI : EmptyMemberIndep (k - 1) R.inv) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₁ Y), IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) (P.append T₁) →
      IsCanonical (barMarked (geoTransformAlong 𝔍 P)) (stepOneInvBM R (geoTransformAlong 𝔍 P)) T₁ ∧
        ∀ z ∈ (geoTransformAlong (barMarked 𝔍) (P.append T₁)).cosupp,
          stepOneInvBM R 𝔍 (P.append T₁) z = stepOneInvBM R (geoTransformAlong 𝔍 P) T₁ z
  | _, .refl, hcan => ⟨trivial, fun _ hz =>
      stepOneInvBM_emptyPrefix_eq 𝔍 R h𝔍 hd hn hmax hk hTI P hP hTIP hEI .refl hcan trivial hz⟩
  | _, .step T C π hπ, hcan => by
      have hAC : AnchorChangeBM 𝔍 R := anchorChangeBM_of_tangentIndepBM 𝔍 R hTI
      have hcan₀ := hcan
      obtain ⟨hcanT, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvBM R 𝔍) (P.append T) ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvBM R 𝔍 (P.append T)) (geoTransformAlong (barMarked 𝔍) (P.append T)).cosupp) :=
        hcan
      obtain ⟨hcan'T, hval⟩ := stepOneInvBM_emptyPrefix h𝔍 hd hn hmax hk hTI P hP hTIP hEI T hcanT
      have hT := isGeoTestTower_of_isCanonical_stepOneInvBM 𝔍 R hAC h𝔍 hd hn hmax hk _ hcanT
      have hEqT := StepOneEmptyPrefix.restrictEquiv_barMarked_append 𝔍 h𝔍 hd P hP T hT
      have hcan'S : IsCanonical (barMarked (geoTransformAlong 𝔍 P)) (stepOneInvBM R (geoTransformAlong 𝔍 P))
          (.step T C π hπ) := by
        refine (⟨hcan'T, hC.imp id fun h => h.trans ?_⟩ :
          IsCanonical (barMarked (geoTransformAlong 𝔍 P)) (stepOneInvBM R (geoTransformAlong 𝔍 P)) T ∧
            (C = ∅ ∨ C = maxLocus (stepOneInvBM R (geoTransformAlong 𝔍 P) T)
              (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) T).cosupp))
        rw [hEqT.cosupp_eq]
        exact ResolutionInvariantExt.maxLocus_congr hval
      exact ⟨hcan'S, fun _ hz =>
        stepOneInvBM_emptyPrefix_eq 𝔍 R h𝔍 hd hn hmax hk hTI P hP hTIP hEI _ hcan₀ hcan'S hz⟩

/-- **Property (4'), the field `emptyPrefix`** of `MaxOrderValue.IsMaxOrderValue` for `stepOneInvBM R` (given the independence
of the hypersurface of maximal contact for `𝔍` and for `𝔍_{T₀}`, and the independence of empty members of the divisor for
`R`). -/
theorem emptyPrefix_field (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    (hTI : TangentIndepBM 𝔍 R) (hEI : EmptyMemberIndep (k - 1) R.inv) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) (h₀ : IsEmptyTower T₀) (hTIP : TangentIndepBM (geoTransformAlong 𝔍 T₀) R)
    (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) (T₀.append T₁)) :
    ∀ z ∈ (geoTransformAlong 𝔍 (T₀.append T₁)).cosupp,
      stepOneInvBM R 𝔍 (T₀.append T₁) z = stepOneInvBM R (geoTransformAlong 𝔍 T₀) T₁ z := by
  intro z hz
  have hAC : AnchorChangeBM 𝔍 R := anchorChangeBM_of_tangentIndepBM 𝔍 R hTI
  rw [← (HironakaG11InvBMBridge.isGeoTestTower_of_isCanonical R 𝔍 hAC h hmax hn _ hcan).2.2] at hz
  exact (stepOneInvBM_emptyPrefix 𝔍 R h.isWellFormed h.one_le_d hn hmax h.dimLE hTI T₀ h₀ hTIP hEI T₁
    ((HironakaG11InvBMBridge.isCanonical_iff R 𝔍 hAC h hmax hn _).mp hcan)).2 z hz

/-- **Property (4'), the field `emptyPrefix`, in lane G11B's announced shape** (I-1368 C-0002): the independence of the
hypersurface of maximal contact for every transform of `𝔍` along a tower with only empty centres. -/
theorem emptyPrefix_field_of_forall (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    (hTI : TangentIndepBM 𝔍 R)
    (hTIP : ∀ {Y₁ : CMfd.{u} n} (P : BlowupTower X Y₁), IsEmptyTower P → TangentIndepBM (geoTransformAlong 𝔍 P) R)
    (hEI : EmptyMemberIndep (k - 1) R.inv) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y)
    (h₀ : IsEmptyTower T₀) (hcan : IsCanonical 𝔍 (stepOneInvBM R 𝔍) (T₀.append T₁)) :
    ∀ z ∈ (geoTransformAlong 𝔍 (T₀.append T₁)).cosupp,
      stepOneInvBM R 𝔍 (T₀.append T₁) z = stepOneInvBM R (geoTransformAlong 𝔍 T₀) T₁ z :=
  emptyPrefix_field 𝔍 R h hmax hn hTI hEI T₀ T₁ h₀ (hTIP T₀ h₀) hcan

end EmptyPrefix


end

end Hironaka.HironakaG11PresM8EmptyPrefix
