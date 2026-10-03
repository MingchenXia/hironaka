/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealTowerTransport
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.NormalCrossingsInvariance
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Marked ideals, transforms and multiple test blow-ups restricted to open subsets

Sources: Włodarczyk 2005 §2.1 (extensions "arise naturally when we pass to open subsets") and §2.4 (Proposition
`pr:funct`: multiple test blow-ups pull back along étale maps, here open embeddings), Bierstone--Milman 2008, the
paragraph after Theorem 1.3 (restriction to open sets, trivial blowings-up); the canonicity clause (2) of
`hir:canonical-resolution`.

The restriction of a marked ideal `𝔪 = (X, N, E, 𝔞, d)` to an open `U ⊆ X` is its pullback along the inclusion `ι: U
→ X` (`MarkedIdealBiholomorphism.MarkedIdeal.pullback`, no new definition): `𝔪|_U = (U, N ∩ U, E ∩ U, ι^*𝔞, d)`.
Towers are restricted with `BlowupTowerTransforms.restrict` (stages `openPreimage T U`, centres `C ∩ U_i`).

## Germ ideals on an open subset (`O : Opens Y`, `ι = Subtype.val`)

* `mem_pullback_val_iff`: for a coherent `𝔠`, a germ `f` on `O` lies in `ι^*𝔠` iff its extension by zero lies in `𝔠`
  (`extendOpens`);
* `restrictOn_pullback_val_iff`: the same for `Res_{W ∩ O} ι^*𝔟` and `Res_W 𝔟`;
* `colonAlong_pullback_val`: **the quotient along `W` commutes with restriction to `O`** (coherent ideals);
* `mem_idealPow_pointIdeal_extendOpens`: `h ∈ 𝔪_x^q` on `O` gives `ext h ∈ 𝔪_x^q` on `Y`.

## Marked ideals and transforms

* `cosupp_pullback_val`: `cosupp(𝔪|_U) = cosupp(𝔪) ∩ U` (any `N`, ideal of holomorphic germs);
* `IsAdmissibleCentre.pullback_val`, `IsWellFormed.pullback_val`: admissible centres and well-formedness restrict;
* `geoStrictTransform_restrict`: strict transforms commute with restriction;
* `geoTransform_pullback_val`: **the transform commutes with restriction**: transforming `𝔪|_U` along the
  restriction `π⁻¹U → U` of the blowup `π` (`BlowupRestrictOpen.isBlowupAlong_restrict`) with centre `C ∩ U` gives
  the restriction of the transform of `𝔪` to `π⁻¹U` (coherent ideals).

## Towers

* `isClosedSubmanifold_N_and_isCoherent_geoTransformAlong`: along a multiple test blow-up of `𝔪` with `N` a closed
  submanifold and `𝔞` coherent, every stage keeps both properties;
* `geoTransformAlong_restrict`: along such a tower, the transform of `𝔪|_U` along the restricted tower is the
  restriction of the transform of `𝔪` to the open preimage, stage by stage;
* `isGeoTestTower_restrict`: **the restriction of a multiple test blow-up (a resolution) of `𝔪` to `U` is one of
  `𝔪|_U`**, and well-formed stages restrict to well-formed stages.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MarkedIdealRestrictOpen

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.NormalCrossingsInvariance Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.GermIdealPullbackCalculus Hironaka.GermIdealOrder Hironaka.IdealWeightPowers Hironaka.RestrictedIdealExtension Hironaka.RestrictedIdealQuotient Hironaka.InvertibleIdealQuotient Hironaka.GermIdealTotalTransform Hironaka.BlowupStrictSubmanifold Hironaka.BlowupRestrictOpen Hironaka.BlowupTowerTransforms

noncomputable section

/-! ### Germ ideals on an open subset -/

section Ideals

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] (O : Opens Y)

/-- **Germs of a restricted coherent ideal**: `f ∈ ι^*𝔠` at `x ∈ O` iff the extension of `f` by zero lies in `𝔠`
at `x`. -/
theorem mem_pullback_val_iff {𝔠 : GermIdeal n Y} (h𝔠 : 𝔠.IsCoherent) {x : O} {f : O → ℂ} :
    (GermIdeal.pullback (m := n) (Subtype.val : O → Y) 𝔠).mem x f ↔ 𝔠.mem x.1 (extendOpens O f) := by
  have h1 : (GermIdeal.pullback (m := n) (Subtype.val : O → Y) 𝔠).mem x f ↔
      IsInSpanAt (n := n) (𝔠.mem x.1) x.1 (extendOpens O f) := isInSpanAt_comp_val_iff O
  rw [h1]
  exact ⟨fun h => mem_of_isInSpanAt_mem h𝔠 h, fun h => isInSpanAt_self h
    (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 h)⟩

/-- A germ of `𝔠` at a point of `O` restricts to a germ of `ι^*𝔠`. -/
theorem comp_val_mem_pullback_val {𝔠 : GermIdeal n Y} (h𝔠 : 𝔠.IsCoherent) {x : O} {g : Y → ℂ}
    (hg : 𝔠.mem x.1 g) : (GermIdeal.pullback (m := n) (Subtype.val : O → Y) 𝔠).mem x (g ∘ Subtype.val) :=
  RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
    (isInSpanAt_self (S := fun s => ∃ b, 𝔠.mem x.1 b ∧ s = b ∘ Subtype.val) ⟨g, hg, rfl⟩
      ((holomorphicAt_comp_val_iff O).mpr
        (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hg)))

/-- **Restricted germs on an open subset**: `F ∈ Res_{W ∩ O} ι^*𝔟` at `x ∈ O` iff the extension of `F` by zero
lies in `Res_W 𝔟` at `x` (coherent `𝔟`). -/
theorem restrictOn_pullback_val_iff {𝔟 : GermIdeal n Y} (h𝔟 : 𝔟.IsCoherent) {W : Set Y} {x : O}
    {F : O → ℂ} :
    (restrictOn n ((↑) ⁻¹' W : Set O) (GermIdeal.pullback (m := n) (Subtype.val : O → Y) 𝔟)).mem x F ↔
      (restrictOn n W 𝔟).mem x.1 (extendOpens O F) := by
  refine and_congr (holomorphicAt_iff_extendOpens O) ⟨?_, ?_⟩
  · rintro ⟨K, s, a, hs, ha, hsum⟩
    refine ⟨K, fun i => extendOpens O (s i), fun i => extendOpens O (a i),
      fun i => (mem_pullback_val_iff O h𝔟).mp (hs i), fun i => (holomorphicAt_iff_extendOpens O).mp (ha i), ?_⟩
    refine (eventually_nhds_val_iff O (P := fun y => y ∈ W →
      extendOpens O F y = ∑ i, extendOpens O (a i) y * extendOpens O (s i) y)).mpr ?_
    filter_upwards [hsum] with y hy hyW
    simp only [extendOpens_val]
    exact hy hyW
  · rintro ⟨K, s, a, hs, ha, hsum⟩
    refine ⟨K, fun i => s i ∘ Subtype.val, fun i => a i ∘ Subtype.val,
      fun i => comp_val_mem_pullback_val O h𝔟 (hs i), fun i => (holomorphicAt_comp_val_iff O).mpr (ha i), ?_⟩
    have h := (eventually_nhds_val_iff O (P := fun y => y ∈ W →
      extendOpens O F y = ∑ i, a i y * s i y)).mp hsum
    filter_upwards [h] with y hy hyW
    have h' := hy hyW
    simp only [extendOpens_val] at h'
    exact h'

/-- `ext ((g ∘ ι) · f) = g · ext f`. -/
theorem extendOpens_comp_val_mul (g : Y → ℂ) (f : O → ℂ) :
    extendOpens O (fun y => (g ∘ Subtype.val) y * f y) = fun y => g y * extendOpens O f y := by
  funext y
  by_cases hy : y ∈ O <;> simp [extendOpens, hy]

/-- `ext (h · f) = ext h · ext f`. -/
theorem extendOpens_mul (h f : O → ℂ) :
    extendOpens O (fun y => h y * f y) = fun y => extendOpens O h y * extendOpens O f y := by
  funext y
  by_cases hy : y ∈ O <;> simp [extendOpens, hy]

/-- **The quotient along `W` commutes with restriction to an open subset** (coherent ideals and quotient). -/
theorem colonAlong_pullback_val {𝔟 𝔩 : GermIdeal n Y} (h𝔟 : 𝔟.IsCoherent) (h𝔩 : 𝔩.IsCoherent) {W : Set Y}
    (hc : (colonAlong n W 𝔟 𝔩).IsCoherent) :
    colonAlong n ((↑) ⁻¹' W : Set O) (GermIdeal.pullback (m := n) (Subtype.val : O → Y) 𝔟)
        (GermIdeal.pullback (m := n) (Subtype.val : O → Y) 𝔩) =
      GermIdeal.pullback (m := n) (Subtype.val : O → Y) (colonAlong n W 𝔟 𝔩) := by
  refine GermIdeal.ext (funext fun x => funext fun f => propext ?_)
  rw [mem_pullback_val_iff O hc]
  refine and_congr (holomorphicAt_iff_extendOpens O) ⟨fun h g hg => ?_, fun h g hg => ?_⟩
  · have := (restrictOn_pullback_val_iff O h𝔟).mp (h _ (comp_val_mem_pullback_val O h𝔩 hg))
    rwa [extendOpens_comp_val_mul] at this
  · refine (restrictOn_pullback_val_iff O h𝔟).mpr ?_
    rw [extendOpens_mul]
    exact h _ ((mem_pullback_val_iff O h𝔩).mp hg)

/-- **Powers of the point ideal extend by zero**: `h ∈ 𝔪_x^q` on `O` gives `ext h ∈ 𝔪_x^q` on `Y`. -/
theorem mem_idealPow_pointIdeal_extendOpens {x : O} :
    ∀ (q : ℕ) {h : O → ℂ}, (idealPow (pointIdeal n x) q).mem x h →
      (idealPow (pointIdeal n x.1) q).mem x.1 (extendOpens O h)
  | 0, _, hh => (holomorphicAt_iff_extendOpens O).mp hh
  | q + 1, h, hh => by
      show IsInSpanAt (n := n) (fun s => ∃ a b, (idealPow (pointIdeal n x.1) q).mem x.1 a ∧
        (pointIdeal n x.1).mem x.1 b ∧ s = a * b) x.1 (extendOpens O h)
      rw [← isInSpanAt_comp_val_iff O]
      have hh' : IsInSpanAt (n := n) (fun s => ∃ a b, (idealPow (pointIdeal n x) q).mem x a ∧
          (pointIdeal n x).mem x b ∧ s = a * b) x h := hh
      refine IsInSpanAt.mono ?_ hh'
      rintro s ⟨a, b, ha, hb, rfl⟩
      have hpt : ((↑) ⁻¹' ({x.1} : Set Y) : Set O) = {x} := by
        ext z
        constructor
        · intro hz
          exact Subtype.ext hz
        · intro hz
          rw [Set.mem_singleton_iff.mp hz]
          exact Set.mem_singleton _
      have hb' : (pointIdeal n x.1).mem x.1 (extendOpens O b) := by
        have : (vanishingIdeal (n := n) ((↑) ⁻¹' ({x.1} : Set Y) : Set O)).mem x b := by
          rw [hpt]; exact hb
        exact (vanishingIdeal_opens_mem_iff O).mp this
      refine ⟨extendOpens O a * extendOpens O b,
        ⟨_, _, mem_idealPow_pointIdeal_extendOpens q ha, hb', rfl⟩, ?_⟩
      funext z
      simp

end Ideals

/-! ### Marked ideals and transforms -/

section Marked

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **The cosupport restricts**: `cosupp(𝔪|_U) = cosupp(𝔪) ∩ U` (any `N`). -/
theorem cosupp_pullback_val (𝔪 : MarkedIdeal n X) (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x)
    (U : Opens X) : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).cosupp = (↑) ⁻¹' 𝔪.cosupp := by
  ext p
  constructor
  · rintro ⟨hpN, hp⟩
    refine ⟨hpN, fun a ha => ?_⟩
    have haφ : (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔪.ideal).mem p (a ∘ Subtype.val) :=
      RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
        (isInSpanAt_self (S := fun s => ∃ b, 𝔪.ideal.mem p.1 b ∧ s = b ∘ Subtype.val) ⟨a, ha, rfl⟩
          ((holomorphicAt_comp_val_iff U).mpr (h𝔞 _ _ ha)))
    obtain ⟨h, hh, hah⟩ := hp _ haφ
    refine ⟨extendOpens U h, mem_idealPow_pointIdeal_extendOpens U _ hh, ?_⟩
    refine (eventually_nhds_val_iff U (P := fun y => y ∈ 𝔪.N → a y = extendOpens U h y)).mpr ?_
    filter_upwards [hah] with y hy hyN
    rw [extendOpens_val]
    exact hy hyN
  · rintro ⟨hpN, hp⟩
    refine ⟨hpN, fun g hg => ?_⟩
    refine IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn
      (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg) ?_
    rintro s ⟨a, ha, rfl⟩
    obtain ⟨h, hh, hah⟩ := hp a ha
    have hval : ∀ q : U, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
        (Subtype.val : U → X) q :=
      fun q => (contMDiff_subtype_val (n := ∞) q).mdifferentiableAt (by simp)
    refine ⟨h ∘ Subtype.val,
      HadamardBridge.comp_mem_idealPow_pointIdeal (Eventually.of_forall hval) _ hh, ?_⟩
    filter_upwards [(continuous_subtype_val.tendsto p).eventually hah] with y hy hyN
    exact hy hyN

/-- **Admissible centres restrict.** -/
theorem IsAdmissibleCentre.pullback_val {𝔪 : MarkedIdeal n X}
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) {C : Set X} (hC : 𝔪.IsAdmissibleCentre C)
    (U : Opens X) :
    (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).IsAdmissibleCentre ((↑) ⁻¹' C : Set U) := by
  refine ⟨isClosedSubmanifold_preimage_val hC.1 U, ?_, ?_⟩
  · rw [cosupp_pullback_val 𝔪 h𝔞 U]
    exact preimage_mono hC.2.1
  · exact hasNormalCrossings_preimage (pullsBackCoordinates_val U) hC.2.2

/-- **Well-formedness restricts.** -/
theorem IsWellFormed.pullback_val {𝔪 : MarkedIdeal n X} (h : 𝔪.IsWellFormed) (U : Opens X) :
    (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).IsWellFormed where
  isClosedSubmanifold_N := isClosedSubmanifold_preimage_val h.isClosedSubmanifold_N U
  isCoherent := isCoherent_pullback contMDiff_subtype_val h.isCoherent
  isSNCDivisor := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val h.isSNCDivisor
  isTransverse := isTransverse_preimage (pullsBackCoordinates_val U) h.isTransverse

variable {C : Set X} {π : Y → X}

/-- **Strict transforms commute with restriction**: for the restriction `π⁻¹U → U` of `π`,
`(A ∩ U)' = A' ∩ π⁻¹U`. -/
theorem geoStrictTransform_restrict (U : Opens X) (hV : IsOpen (π ⁻¹' (U : Set X))) (A : Set X) :
    geoStrictTransform (fun p : (⟨π ⁻¹' (U : Set X), hV⟩ : Opens Y) => (⟨π p.1, p.2⟩ : U))
        ((↑) ⁻¹' C : Set U) ((↑) ⁻¹' A) =
      (↑) ⁻¹' geoStrictTransform π C A := by
  set V : Opens Y := ⟨π ⁻¹' (U : Set X), hV⟩
  have key := (V.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
    continuous_subtype_val (π ⁻¹' (A \ C))
  exact key.symm

/-- **The transform commutes with restriction to an open subset**: transforming `𝔪|_U` along the restriction
`π⁻¹U → U` of the blowup `π` with centre `C ∩ U` gives the restriction to `π⁻¹U` of the transform of `𝔪`
(coherent ideal and coherent transformed ideal). -/
theorem geoTransform_pullback_val {𝔪 : MarkedIdeal n X} (h𝔞 : 𝔪.ideal.IsCoherent) (hπ : IsBlowupAlong n C π)
    (hc : (𝔪.geoTransform C π).ideal.IsCoherent) (U : Opens X) (hV : IsOpen (π ⁻¹' (U : Set X))) :
    (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).geoTransform ((↑) ⁻¹' C : Set U)
        (fun p : (⟨π ⁻¹' (U : Set X), hV⟩ : Opens Y) => (⟨π p.1, p.2⟩ : U)) =
      MarkedIdeal.pullback (Subtype.val : (⟨π ⁻¹' (U : Set X), hV⟩ : Opens Y) → Y)
        (𝔪.geoTransform C π) := by
  set V : Opens Y := ⟨π ⁻¹' (U : Set X), hV⟩ with hVdef
  set r : V → U := fun p => ⟨π p.1, p.2⟩ with hrdef
  have hr : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ r :=
    contMDiff_opens_mk (hπ.contMDiff.comp contMDiff_subtype_val) fun p => p.2
  have hvr : (Subtype.val ∘ r : V → X) = π ∘ Subtype.val := rfl
  have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have hpbA : GermIdeal.pullback (m := n) r (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔪.ideal) =
      GermIdeal.pullback (m := n) (Subtype.val : V → Y) (GermIdeal.pullback (m := n) π 𝔪.ideal) := by
    rw [← pullback_comp contMDiff_subtype_val hr h𝔞, hvr,
      pullback_comp hπ.contMDiff contMDiff_subtype_val h𝔞]
  have hpbC : GermIdeal.pullback (m := n) r (vanishingIdeal (n := n) ((↑) ⁻¹' C : Set U)) =
      GermIdeal.pullback (m := n) (Subtype.val : V → Y)
        (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) := by
    rw [pullback_vanishingIdeal_opens U r C, hvr, pullback_comp hπ.contMDiff contMDiff_subtype_val hIC]
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of (geoStrictTransform_restrict U hV 𝔪.N) ?_ ?_ rfl
  · simp only [geoTransform_E, MarkedIdeal.pullback, List.map_append, List.map_map, List.map_cons,
      List.map_nil]
    congr 1
    exact List.map_congr_left fun A _ => geoStrictTransform_restrict U hV A
  · change colonAlong n (geoStrictTransform r ((↑) ⁻¹' C : Set U) ((↑) ⁻¹' 𝔪.N))
        (GermIdeal.pullback (m := n) r (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔪.ideal))
        (idealPow (GermIdeal.pullback (m := n) r (vanishingIdeal (n := n) ((↑) ⁻¹' C : Set U))) 𝔪.d) =
      GermIdeal.pullback (m := n) (Subtype.val : V → Y)
        (colonAlong n (geoStrictTransform π C 𝔪.N) (GermIdeal.pullback (m := n) π 𝔪.ideal)
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔪.d))
    rw [geoStrictTransform_restrict U hV 𝔪.N, hpbA, hpbC,
      ← BlowupExceptionalDivisor.pullback_idealPow contMDiff_subtype_val
        (isCoherent_pullback hπ.contMDiff hIC)]
    exact colonAlong_pullback_val V (isCoherent_pullback hπ.contMDiff h𝔞)
      (isCoherent_idealPow (isCoherent_pullback hπ.contMDiff hIC) _) hc

end Marked

/-! ### Towers -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n} (U : Opens X) {𝔪 : MarkedIdeal n X}

/-- **Along a multiple test blow-up, `N` stays a closed submanifold and the ideal stays coherent.** -/
theorem isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      IsClosedSubmanifold n (geoTransformAlong 𝔪 T).N ∧ (geoTransformAlong 𝔪 T).ideal.IsCoherent
  | _, .refl, _ => ⟨hN, h𝔞⟩
  | _, .step T _ _ hπ, hT => by
      obtain ⟨hTT, hC⟩ := hT
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hTT
      exact ⟨isClosedSubmanifold_geoTransform_N hNT hC hπ,
        HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT hcT hC hπ⟩

/-- **Transforms commute with restriction along multiple test blow-ups**: the transform of `𝔪|_U` along the
restricted tower is the restriction of the transform of `𝔪` to the open preimage of `U`. -/
theorem geoTransformAlong_restrict (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) =
        MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong 𝔪 T)
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, hC⟩ := hT
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hTT
      have ih := geoTransformAlong_restrict hN h𝔞 T hTT
      change (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).geoTransform
        ((↑) ⁻¹' C : Set (openPreimage T U)) _ = _
      rw [ih]
      exact geoTransform_pullback_val hcT hπ
        (HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT hcT hC hπ)
        (openPreimage T U) _

/-- **Multiple test blow-ups restrict**: the restriction to `U` of a multiple test blow-up of `𝔪` is a multiple
test blow-up of `𝔪|_U`. -/
theorem isGeoTestTower_restrict (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, hC⟩ := hT
      obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hTT
      refine ⟨isGeoTestTower_restrict hN h𝔞 T hTT, ?_⟩
      rw [geoTransformAlong_restrict U hN h𝔞 T hTT]
      exact IsAdmissibleCentre.pullback_val
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) hC
        (openPreimage T U)

end Tower

end

end Hironaka.MarkedIdealRestrictOpen
