/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.Coherence.VanishingIdealCoherent
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The transform of a marked ideal with centre-relative strict transforms

Sources: Bierstone--Milman 2008, Definitions 2.2 (the transform `(M', N', E', 𝓘', d)` of a marked ideal by an
admissible blowing-up: `N'` and the members of `E'` other than the last are STRICT transforms, i.e. blowups of `N`
and of the `H ∈ E` along their intersections with the centre), Włodarczyk 2005 §2.1 (conditions (3)--(5) of a
resolution) and §2.2 (controlled transforms).

## Why a second transform

When the algorithm blows up a codimension-one centre equal to an earlier exceptional member `H` (Włodarczyk's lemma
on codimension-one components of the cosupport), the old transform lists `H` twice in `E'` (not simple normal
crossings), and a component of `N` inside `C` survives in `N'` (not transverse to `E'`, and the generator of the
exceptional ideal vanishes on it). This module defines the corrected transform `geoTransform`, NEW, without touching
the existing one.

## Main declarations

* `geoTransform`, `geoTransformAlong`, `IsGeoTestTower`, `IsGeoResolution` and their bookkeeping
  (`geoTransformAlong_append`, `isGeoTestTower_append_iff`, `d_geoTransformAlong`, `length_E_geoTransformAlong`);
* well-formedness ingredients: `isClosedSubmanifold_geoTransform_N` (`N'` is a closed submanifold, from
  `BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold`),
  `isInvertibleAlong_geoStrictTransform` (the exceptional ideal is invertible ALONG `N'`, the property that fails
  for the old transform), `restrictLe_pullback`, `isCoherent_geoTransform_ideal` (the transformed ideal is
  coherent);
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MarkedIdeals.MarkedIdeal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.NormalCrossings
open Hironaka.BlowupTowers Hironaka.IdealWeightPowers
open Hironaka.RestrictedIdealQuotient Hironaka.RestrictedIdealWeight
open Hironaka.RestrictedIdealExtension Hironaka.BlowupStrictSubmanifold
open Hironaka.GermIdealTotalTransform Hironaka.GermIdealPullbackCalculus
open Hironaka.InvertibleIdealQuotient Hironaka.RelativePrincipalizationSpan
open Hironaka.BlowupExceptionalDivisor Hironaka.BlowupControlledTransform

noncomputable section

/-! ### The transform -/

section OneSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The transform with centre-relative strict transforms** of `(M, N, E, 𝓘, d)` by the blowup
`π : M' → M` along `C` (BM08 Definitions 2.2; Włodarczyk §2.1 (3)--(5)): `N' = closure (π⁻¹ (N \ C))`;
`E'` = the strict transforms `closure (π⁻¹ (H \ C))` of the members `H` of `E`, followed by `π⁻¹ C`;
`𝓘' = 𝓘_{π⁻¹C}^{-d} π^*𝓘` on `N'`, realised as the colon along `N'` of `π^*𝓘` by `(π^*𝓘_C)^d`;
`d' = d`. -/
def geoTransform (𝔪 : MarkedIdeal n M) {M' : Type u} [TopologicalSpace M']
    [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M'] (C : Set M) (π : M' → M) :
    MarkedIdeal n M' where
  N := geoStrictTransform π C 𝔪.N
  E := 𝔪.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  ideal := colonAlong n (geoStrictTransform π C 𝔪.N) (GermIdeal.pullback π 𝔪.ideal)
    (idealPow (GermIdeal.pullback π (vanishingIdeal (n := n) C)) 𝔪.d)
  d := 𝔪.d

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] (𝔪 : MarkedIdeal n M) (C : Set M) (π : M' → M)

@[simp] theorem geoTransform_N : (𝔪.geoTransform C π).N = geoStrictTransform π C 𝔪.N := rfl

@[simp] theorem geoTransform_E :
    (𝔪.geoTransform C π).E = 𝔪.E.map (geoStrictTransform π C) ++ [π ⁻¹' C] := rfl

@[simp] theorem geoTransform_d : (𝔪.geoTransform C π).d = 𝔪.d := rfl

theorem geoTransform_ideal : (𝔪.geoTransform C π).ideal =
    colonAlong n (geoStrictTransform π C 𝔪.N) (GermIdeal.pullback π 𝔪.ideal)
      (idealPow (GermIdeal.pullback π (vanishingIdeal (n := n) C)) 𝔪.d) := rfl

theorem length_E_geoTransform : (𝔪.geoTransform C π).E.length = 𝔪.E.length + 1 := by
  simp

variable {𝔪 C π}

/-! ### Well-formedness ingredients -/

/-- **`N'` is a closed submanifold** for a closed submanifold `N` and an admissible centre. -/
theorem isClosedSubmanifold_geoTransform_N (hN : IsClosedSubmanifold n 𝔪.N)
    (hC : 𝔪.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) :
    IsClosedSubmanifold n (𝔪.geoTransform C π).N :=
  BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hC.subset_N

/-- If `1` is a germ of `𝔩` at `y`, it is a germ of every power of `𝔩`. -/
theorem one_mem_idealPow {𝔩 : GermIdeal n M'} {y : M'} (h : 𝔩.mem y fun _ => (1 : ℂ)) :
    ∀ d : ℕ, (idealPow 𝔩 d).mem y fun _ => (1 : ℂ)
  | 0 => holomorphicAt_const 1
  | d + 1 => by
      have := mem_mul_of_mem_mem (one_mem_idealPow h d) h
        (by simpa using (holomorphicAt_const (n := n) (x := y) (1 : ℂ)))
      simpa using this

/-- Off `π⁻¹ C`, the constant `1` is a germ of `π^*𝓘_C`. -/
theorem one_mem_pullback_vanishingIdeal {y : M'} (hy : π y ∉ C) (hC : IsClosed C) :
    (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem y fun _ => (1 : ℂ) := by
  have h1 : (vanishingIdeal (n := n) C).mem (π y) fun _ => (1 : ℂ) := by
    refine ⟨holomorphicAt_const 1, ?_⟩
    filter_upwards [hC.isOpen_compl.mem_nhds hy] with x hx hxC
    exact absurd hxC hx
  exact isInSpanAt_self (S := fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π y) a ∧ s = a ∘ π)
    ⟨fun _ => (1 : ℂ), h1, rfl⟩ (holomorphicAt_const 1)

/-- **The exceptional ideal is invertible along `N'`**: its local generator vanishes identically on no nonempty
relatively open subset of `N' = closure (π⁻¹ (N \ C))`, because `π⁻¹ (N \ C)` is dense in `N'` and misses `π⁻¹ C`. -/
theorem isInvertibleAlong_geoStrictTransform (hπ : IsBlowupAlong n C π) (N : Set M) (d : ℕ) :
    IsInvertibleAlong n (geoStrictTransform π C N)
      (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) d) := by
  intro x _
  obtain ⟨U, hU, hxU, h, hhdiff, -, hgen⟩ := isInvertible_idealPow_exceptionalDivisor hπ d x
  refine ⟨U, hU, hxU, h, hhdiff, fun V hV hVU hVN => ?_, hgen⟩
  obtain ⟨z, hzV, hzN⟩ := hVN
  obtain ⟨y, hyV, hyD⟩ := mem_closure_iff.mp hzN V hV hzV
  refine ⟨y, ⟨hyV, subset_closure hyD⟩, fun hy0 => ?_⟩
  have h1 := one_mem_idealPow (n := n) (one_mem_pullback_vanishingIdeal (n := n) (π := π) hyD.2 hπ.1.1) d
  obtain ⟨-, K, s, a, hs, -, hsum⟩ := (hgen y (hVU hyV) _).mp h1
  have := hsum.self_of_nhds
  simp only [hs, hy0, mul_zero, Finset.sum_const_zero] at this
  exact one_ne_zero this

/-- **Restricted inclusions pull back**: `Res_W 𝔞 ⊆ Res_W 𝔟` gives
`Res_{f⁻¹W} f^*𝔞 ⊆ Res_{f⁻¹W} f^*𝔟`, for an ideal `𝔟` of holomorphic germs. -/
theorem restrictLe_pullback {f : M' → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {W : Set M}
    {𝔞 𝔟 : GermIdeal n M} (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x)
    (hle : RestrictLe W 𝔞 𝔟) :
    RestrictLe (f ⁻¹' W) (GermIdeal.pullback (m := n) f 𝔞) (GermIdeal.pullback (m := n) f 𝔟) := by
  intro y hy g hg
  have hfat : ∀ᶠ y' in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y' :=
    Eventually.of_forall fun _ => hf.contMDiffAt
  refine IsInSpanOnAt.trans ?_
    (IsInSpanAt.restrict (S := fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f) hg)
  rintro s ⟨a, ha, rfl⟩
  obtain ⟨K, t, b, ht, hb, hsum⟩ := hle (f y) hy a ha
  refine ⟨K, fun i => t i ∘ f, fun i => b i ∘ f, fun i => ?_, fun i => (hb i).comp_contMDiff hfat,
    ?_⟩
  · exact isInSpanAt_self (S := fun s => ∃ a, 𝔟.mem (f y) a ∧ s = a ∘ f) ⟨t i, ht i, rfl⟩
      ((h𝔟 _ _ (ht i)).comp_contMDiff hfat)
  · filter_upwards [(hf.continuous.tendsto y).eventually hsum] with z hz hzW
    exact hz hzW

/-- **The transformed ideal is coherent**, given the restricted inclusion
`Res_N 𝔞 ⊆ Res_N 𝓘_C^d` (for `N = M` this is the Hadamard bridge,
`HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre`). -/
theorem isCoherent_geoTransform_ideal (h𝔞 : 𝔪.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔪.N)
    (hπ : IsBlowupAlong n C π) (hCN : C ⊆ 𝔪.N)
    (hle : RestrictLe 𝔪.N 𝔪.ideal (idealPow (vanishingIdeal (n := n) C) 𝔪.d)) :
    (𝔪.geoTransform C π).ideal.IsCoherent := by
  have hIC := isCoherent_vanishingIdeal_centre hπ
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hpow : (idealPow (vanishingIdeal (n := n) C) 𝔪.d).IsCoherent := isCoherent_idealPow hIC _
  have hle' : RestrictLe (geoStrictTransform π C 𝔪.N) (GermIdeal.pullback (m := n) π 𝔪.ideal)
      (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔪.d) := by
    rw [← BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff hIC]
    intro y hy g hg
    have hsub := geoStrictTransform_subset_preimage (C := C) hπ.contMDiff.continuous hN.1
    obtain ⟨K, s, a, hs, ha, hsum⟩ := restrictLe_pullback hπ.contMDiff
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hpow hg) hle y (hsub hy) g hg
    exact ⟨K, s, a, hs, ha, hsum.mono fun z hz hzN => hz (hsub hzN)⟩
  exact isCoherent_colonAlong hN'.1 (isCoherent_pullback hπ.contMDiff h𝔞)
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hN')
    (isCoherent_idealPow (isCoherent_pullback hπ.contMDiff hIC) _)
    (isInvertibleAlong_geoStrictTransform hπ 𝔪.N 𝔪.d) hle'

/-! ### `N = M` -/

/-- **The strict transform of the whole space is the whole space** (`π⁻¹ C` is nowhere dense). -/
theorem geoStrictTransform_univ (hπ : IsBlowupAlong n C π) : geoStrictTransform π C univ = univ := by
  rw [geoStrictTransform, preimage_sdiff, preimage_univ, ← compl_eq_univ_sdiff, closure_compl,
    ExceptionalFibres.interior_preimage_eq_empty hπ, compl_empty]

theorem geoTransform_N_eq_univ (hN : 𝔪.N = univ) (hπ : IsBlowupAlong n C π) :
    (𝔪.geoTransform C π).N = univ := by
  rw [geoTransform_N, hN, geoStrictTransform_univ hπ]

/-- **For `N = M` the transform is the controlled transform** `σ^c(𝔞, d)`. -/
theorem geoTransform_ideal_eq_controlledTransform (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hπ : IsBlowupAlong n C π) :
    (𝔪.geoTransform C π).ideal = controlledTransform hπ 𝔪.ideal 𝔪.d := by
  rw [geoTransform_ideal, hN, geoStrictTransform_univ hπ]
  show colon (restrictOn n univ (GermIdeal.pullback (m := n) π 𝔪.ideal)) _ = _
  rw [BlowupTowerTransforms.restrictOn_univ (isCoherent_pullback hπ.contMDiff h𝔞)]
  rfl

end OneSpace

/-! ### Along a tower -/

section Tower

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- **The transform along a tower** (centre-relative strict transforms). -/
def geoTransformAlong (𝔪 : MarkedIdeal n X) : {Y : CMfd.{u} n} → BlowupTower X Y → MarkedIdeal n Y
  | _, .refl => 𝔪
  | _, .step T C π _ => (geoTransformAlong 𝔪 T).geoTransform C π

/-- **A multiple test blow-up** for the transform with centre-relative strict transforms. -/
def IsGeoTestTower (𝔪 : MarkedIdeal n X) : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => IsGeoTestTower 𝔪 T ∧ (geoTransformAlong 𝔪 T).IsAdmissibleCentre C

/-- **A resolution**: a multiple test blow-up after which the cosupport is empty. -/
def IsGeoResolution (𝔪 : MarkedIdeal n X) (T : BlowupTower X Y) : Prop :=
  IsGeoTestTower 𝔪 T ∧ (geoTransformAlong 𝔪 T).cosupp = ∅

variable (𝔪 : MarkedIdeal n X)

@[simp] theorem geoTransformAlong_refl :
    geoTransformAlong 𝔪 (BlowupTower.refl : BlowupTower X X) = 𝔪 := rfl

@[simp] theorem geoTransformAlong_step (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) :
    geoTransformAlong 𝔪 (.step T C π hπ) = (geoTransformAlong 𝔪 T).geoTransform C π := rfl

theorem N_geoTransformAlong_step (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) :
    (geoTransformAlong 𝔪 (.step T C π hπ)).N = geoStrictTransform π C (geoTransformAlong 𝔪 T).N :=
  rfl

@[simp] theorem isGeoTestTower_step_iff (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) :
    IsGeoTestTower 𝔪 (.step T C π hπ) ↔
      IsGeoTestTower 𝔪 T ∧ (geoTransformAlong 𝔪 T).IsAdmissibleCentre C :=
  Iff.rfl

/-- The mark never changes. -/
@[simp] theorem d_geoTransformAlong (T : BlowupTower X Y) : (geoTransformAlong 𝔪 T).d = 𝔪.d := by
  induction T with
  | refl => rfl
  | step T C π hπ ih => exact ih

/-- `E` grows by exactly one member per blowup. -/
theorem length_E_geoTransformAlong (T : BlowupTower X Y) :
    (geoTransformAlong 𝔪 T).E.length = 𝔪.E.length + T.length := by
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    rw [geoTransformAlong_step, length_E_geoTransform, ih, BlowupTower.length_step]
    omega

/-- Transforms compose along concatenated towers. -/
theorem geoTransformAlong_append (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    geoTransformAlong 𝔪 (T.append S) = geoTransformAlong (geoTransformAlong 𝔪 T) S := by
  induction S with
  | refl => rfl
  | step S C π hπ ih => simp [BlowupTower.append, geoTransformAlong, ih]

/-- A concatenation is a multiple test blow-up iff both pieces are (the second for the transform). -/
theorem isGeoTestTower_append_iff (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    IsGeoTestTower 𝔪 (T.append S) ↔
      IsGeoTestTower 𝔪 T ∧ IsGeoTestTower (geoTransformAlong 𝔪 T) S := by
  induction S with
  | refl => simp [BlowupTower.append, IsGeoTestTower]
  | step S C π hπ ih =>
    simp only [BlowupTower.append, IsGeoTestTower, ih, geoTransformAlong_append]
    tauto

/-- **Along a multiple test blow-up of `(X, X, E, 𝔞, d)`** with `𝔞` coherent, `N` stays the whole
space, the transform `𝔞_T` is coherent, and `T^*𝔞 = 𝒪(-d E_T) · 𝔞_T` (any mark `d`; the centre
inclusions `𝔞_T ⊆ 𝓘_C^d` come from the Hadamard bridge). -/
theorem pullback_eq_mul_geoTransformAlong (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).N = univ ∧ (geoTransformAlong 𝔪 T).ideal.IsCoherent ∧
      GermIdeal.pullback (m := n) T.proj 𝔪.ideal =
        (idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal 𝔪.d).mul
          (geoTransformAlong 𝔪 T).ideal
  | _, .refl, _ => by
      refine ⟨hN, h𝔞, ?_⟩
      rw [BlowupTowerTransforms.exceptionalDivisor_refl_ideal, BlowupTower.proj_refl,
        geoTransformAlong_refl, idealPow_unitIdeal, unitIdeal_mul h𝔞]
      exact pullback_id h𝔞
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hNT, hcohT, hpb⟩ := pullback_eq_mul_geoTransformAlong hN h𝔞 T hTT
      set 𝔫 := geoTransformAlong 𝔪 T with h𝔫
      have hd𝔫 : 𝔫.d = 𝔪.d := by rw [h𝔫, d_geoTransformAlong]
      have hle : 𝔫.ideal.Le (idealPow (vanishingIdeal (n := n) C) 𝔪.d) := by
        rw [← hd𝔫]
        exact HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hNT hcohT hC
      have htr : (𝔫.geoTransform C π).ideal = controlledTransform hπ 𝔫.ideal 𝔪.d := by
        rw [geoTransform_ideal_eq_controlledTransform hNT hcohT hπ, hd𝔫]
      have hD : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsCoherent :=
        isCoherent_pullback hπ.contMDiff (isCoherent_vanishingIdeal_centre hπ)
      have hE : (BlowupTowerTransforms.exceptionalDivisor T).ideal.IsCoherent := isCoherent_ideal _
      have hEd : (idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal 𝔪.d).IsCoherent :=
        isCoherent_idealPow hE _
      have hπE : (GermIdeal.pullback (m := n) π
          (idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal 𝔪.d)).IsCoherent :=
        isCoherent_pullback hπ.contMDiff hEd
      have hDd : (idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal 𝔪.d).IsCoherent :=
        isCoherent_idealPow (isCoherent_ideal _) _
      have hcon := isCoherent_controlledTransform hπ hcohT hle
      refine ⟨?_, ?_, ?_⟩
      · rw [geoTransformAlong_step]
        exact geoTransform_N_eq_univ hNT hπ
      · rw [geoTransformAlong_step, htr]
        exact hcon
      · rw [geoTransformAlong_step, htr, BlowupTower.proj_step,
          pullback_comp T.contMDiff_proj hπ.contMDiff h𝔞, hpb,
          pullback_mul hπ.contMDiff hEd hcohT,
          pullback_eq_mul_controlledTransform hπ hcohT hle,
          BlowupTowerTransforms.exceptionalDivisor_step_ideal,
          idealPow_mul (isCoherent_pullback hπ.contMDiff hE) hD,
          ← BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff hE,
          ← mul_assoc hπE hDd hcon]
        rfl

/-- **A resolution with the mark `1` principalizes** (Włodarczyk §2.3, (1) ⟹ (2)): if `T` resolves
`(X, X, E, 𝔞, 1)` with `𝔞` coherent, then `T^*𝔞 = 𝒪(-E_T)`.  (With a mark `d ≥ 2` a resolution only
gives `T^*𝔞 = 𝒪(-d E_T) · 𝔞_T` with `ord 𝔞_T < d` everywhere, `pullback_eq_mul_geoTransformAlong`.) -/
theorem pullback_eq_exceptionalDivisor_of_isGeoResolution (hN : 𝔪.N = univ)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 𝔪.d = 1) (T : BlowupTower X Y) (hT : IsGeoResolution 𝔪 T) :
    GermIdeal.pullback (m := n) T.proj 𝔪.ideal = (BlowupTowerTransforms.exceptionalDivisor T).ideal := by
  obtain ⟨hNT, hcohT, hpb⟩ := pullback_eq_mul_geoTransformAlong 𝔪 hN h𝔞 T hT.1
  have hz : (geoTransformAlong 𝔪 T).ideal.zeroLocus = ∅ := by
    have h2 := hT.2
    rw [MarkedIdeal.cosupp, d_geoTransformAlong, hd, hNT,
      cosupport_one fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcohT hg,
      univ_inter] at h2
    exact h2
  rw [hpb, BlowupTowerTransforms.eq_unitIdeal_of_zeroLocus_eq_empty hcohT hz, hd,
    RestrictLeCalculus.mul_unitIdeal (isCoherent_idealPow (isCoherent_ideal _) _), idealPow_succ,
    idealPow_zero, unitIdeal_mul (isCoherent_ideal _)]

end Tower

end

end Hironaka.MarkedIdeals.MarkedIdeal
