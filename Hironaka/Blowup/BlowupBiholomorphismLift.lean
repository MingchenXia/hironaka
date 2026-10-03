/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.Blowup.BlowupUniqueness
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedIdeal
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Lifting biholomorphisms of open sets along a blowup; naturality of transforms on the blown-up side

Source: Włodarczyk 2005, proof of `le:homo` (4) ("both morphisms `φ_u` and `φ_v` lift ... by the universal property
of a blow-up") and Proposition `pr:funct`.

* `mem_pullback_diffeo_iff`, `mem_restrictOn_pullback_diffeo_iff`, `colonAlong_pullback_diffeo`: along a biholomorphism
  `χ`, membership in a pulled-back coherent ideal is read through `χ⁻¹`, and the quotient along a set commutes with
  pullback;
* `geoStrictTransform_comp_diffeo`, `geoTransform_comp_diffeo`: **the transform along `π ∘ χ` is the `χ`-pullback of
  the transform along `π`** (naturality on the blown-up side; the base-side version is
  `MarkedIdealBiholomorphism.MarkedIdeal.geoTransform_pullback`);
* `preOpen hπ A = π⁻¹(A)` and `exists_lift`: **a biholomorphism `Φ : A ≅ B` of open sets of the base with
  `Φ⁻¹(C ∩ B) = C ∩ A` lifts to a biholomorphism `Φ₁ : π⁻¹A ≅ π⁻¹B` with `π ∘ Φ₁ = Φ ∘ π`** (universal property,
  `BlowupUniqueness.exists_biholomorphism_over`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupBiholomorphismLift

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder IdealWeightPowers BlowupStrictSubmanifold BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism RestrictedIdealExtension RestrictedIdealQuotient InvertibleIdealQuotient BlowupRestrictOpen

noncomputable section

/-! ### Ideals along a biholomorphism -/

section Diffeo

variable {n : ℕ} {Y₁ : Type*} [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  {Y₂ : Type*} [TopologicalSpace Y₂] [ChartedSpace (ComplexModel n) Y₂] [IsComplexManifold n Y₂]
  (χ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂)

theorem holomorphicAt_comp_diffeo {f : Y₂ → ℂ} {p : Y₁} (hf : HolomorphicAt n f (χ p)) :
    HolomorphicAt n (f ∘ χ) p :=
  hf.comp_contMDiff (Eventually.of_forall fun q => χ.contMDiff q)

theorem holomorphicAt_comp_diffeo_symm {f : Y₁ → ℂ} {p : Y₁} (hf : HolomorphicAt n f p) :
    HolomorphicAt n (f ∘ χ.symm) (χ p) := by
  have h : HolomorphicAt n f (χ.symm (χ p)) := by rw [χ.symm_apply_apply]; exact hf
  exact h.comp_contMDiff (Eventually.of_forall fun q => χ.symm.contMDiff q)

/-- **Germs of a pulled-back coherent ideal along a biholomorphism**: `f ∈ (χ^*𝔠)_p` iff `f ∘ χ⁻¹ ∈ 𝔠_{χ p}`. -/
theorem mem_pullback_diffeo_iff {𝔠 : GermIdeal n Y₂} (h𝔠 : 𝔠.IsCoherent) {p : Y₁} {f : Y₁ → ℂ} :
    (GermIdeal.pullback (m := n) χ 𝔠).mem p f ↔ 𝔠.mem (χ p) (f ∘ χ.symm) := by
  constructor
  · intro hf
    have h1 := RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf
    have h1' : IsInSpanAt (n := n) (fun s => ∃ b, 𝔠.mem (χ p) b ∧ s = b ∘ χ) (χ.symm (χ p)) f := by
      rw [χ.symm_apply_apply]; exact h1
    have h2 := GermIdealPullbackCalculus.isInSpanAt_comp χ.symm.contMDiff h1'
    refine HomogenizedIdeal.mem_of_isInSpanAt h𝔠 (IsInSpanAt.mono ?_ h2)
    rintro s ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    have : (b ∘ χ) ∘ χ.symm = b := funext fun y => by simp
    rw [this]
    exact hb
  · intro hf
    refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (InvertibleIdealQuotient.isInSpanAt_self ⟨f ∘ χ.symm, hf, funext fun y => by simp⟩ ?_)
    have h := holomorphicAt_comp_diffeo χ
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hf)
    have : (f ∘ χ.symm) ∘ χ = f := funext fun y => by simp
    rwa [this] at h

/-- `g ∘ χ ∈ (χ^*𝔠)_p` for `g ∈ 𝔠_{χ p}`. -/
theorem comp_mem_pullback_diffeo {𝔠 : GermIdeal n Y₂} (h𝔠 : 𝔠.IsCoherent) {p : Y₁} {g : Y₂ → ℂ}
    (hg : 𝔠.mem (χ p) g) : (GermIdeal.pullback (m := n) χ 𝔠).mem p (g ∘ χ) :=
  (mem_pullback_diffeo_iff χ h𝔠).mpr (by
    have : (g ∘ χ) ∘ χ.symm = g := funext fun y => by simp
    rwa [this])

/-- **Restricted germs along a biholomorphism.** -/
theorem mem_restrictOn_pullback_diffeo_iff {𝔟 : GermIdeal n Y₂} (h𝔟 : 𝔟.IsCoherent) {W : Set Y₂} {p : Y₁}
    {F : Y₁ → ℂ} :
    (restrictOn n (χ ⁻¹' W) (GermIdeal.pullback (m := n) χ 𝔟)).mem p F ↔
      (restrictOn n W 𝔟).mem (χ p) (F ∘ χ.symm) := by
  constructor
  · rintro ⟨hF, K, s, a, hs, ha, hsum⟩
    refine ⟨holomorphicAt_comp_diffeo_symm χ hF, K, fun i => s i ∘ χ.symm, fun i => a i ∘ χ.symm,
      fun i => (mem_pullback_diffeo_iff χ h𝔟).mp (hs i), fun i => holomorphicAt_comp_diffeo_symm χ (ha i), ?_⟩
    have hc : Tendsto χ.symm (𝓝 (χ p)) (𝓝 p) := by
      have := χ.symm.continuous.tendsto (χ p)
      rwa [χ.symm_apply_apply] at this
    filter_upwards [hc.eventually hsum] with y hy hyW
    have := hy (by simpa using hyW)
    simpa using this
  · rintro ⟨hF, K, s, a, hs, ha, hsum⟩
    have hF' : HolomorphicAt n F p := by
      have h := holomorphicAt_comp_diffeo χ hF
      have : (F ∘ χ.symm) ∘ χ = F := funext fun y => by simp
      rwa [this] at h
    refine ⟨hF', K, fun i => s i ∘ χ, fun i => a i ∘ χ, fun i => comp_mem_pullback_diffeo χ h𝔟 (hs i),
      fun i => holomorphicAt_comp_diffeo χ (ha i), ?_⟩
    filter_upwards [(χ.continuous.tendsto p).eventually hsum] with y hy hyW
    have := hy hyW
    simpa using this

/-- **The quotient along a set commutes with pullback along a biholomorphism** (coherent ideals and quotient). -/
theorem colonAlong_pullback_diffeo {𝔟 𝔩 : GermIdeal n Y₂} (h𝔟 : 𝔟.IsCoherent) (h𝔩 : 𝔩.IsCoherent) {W : Set Y₂}
    (hc : (colonAlong n W 𝔟 𝔩).IsCoherent) :
    colonAlong n (χ ⁻¹' W) (GermIdeal.pullback (m := n) χ 𝔟) (GermIdeal.pullback (m := n) χ 𝔩) =
      GermIdeal.pullback (m := n) χ (colonAlong n W 𝔟 𝔩) := by
  refine GermIdeal.ext (funext fun p => funext fun f => propext ?_)
  rw [mem_pullback_diffeo_iff χ hc]
  constructor
  · rintro ⟨hf, hcol⟩
    refine ⟨holomorphicAt_comp_diffeo_symm χ hf, fun g' hg' => ?_⟩
    have h1 := hcol (g' ∘ χ) (comp_mem_pullback_diffeo χ h𝔩 hg')
    have h2 := (mem_restrictOn_pullback_diffeo_iff χ h𝔟).mp h1
    have : (fun y => (g' ∘ χ) y * f y) ∘ χ.symm = fun y => g' y * (f ∘ χ.symm) y :=
      funext fun y => by simp
    rwa [this] at h2
  · rintro ⟨hf, hcol⟩
    have hf' : HolomorphicAt n f p := by
      have h := holomorphicAt_comp_diffeo χ hf
      have : (f ∘ χ.symm) ∘ χ = f := funext fun y => by simp
      rwa [this] at h
    refine ⟨hf', fun g hg => ?_⟩
    have h1 := hcol (g ∘ χ.symm) ((mem_pullback_diffeo_iff χ h𝔩).mp hg)
    refine (mem_restrictOn_pullback_diffeo_iff χ h𝔟).mpr ?_
    have : (fun y => g y * f y) ∘ χ.symm = fun y => (g ∘ χ.symm) y * (f ∘ χ.symm) y :=
      funext fun y => by simp
    rwa [this]

end Diffeo

/-! ### Naturality of the transform on the blown-up side -/

section Naturality

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y₁ : Type u} [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  {Y₂ : Type u} [TopologicalSpace Y₂] [ChartedSpace (ComplexModel n) Y₂] [IsComplexManifold n Y₂]
  (χ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂)

/-- **Strict transforms along `π ∘ χ`** are the `χ`-preimages of those along `π`. -/
theorem geoStrictTransform_comp_diffeo (π : Y₂ → X) (C A : Set X) :
    geoStrictTransform (π ∘ χ) C A = χ ⁻¹' geoStrictTransform π C A := by
  unfold geoStrictTransform
  rw [preimage_comp]
  exact (χ.toHomeomorph.preimage_closure _).symm

/-- **Naturality of the transform on the blown-up side**: for a biholomorphism `χ : Y₁ ≅ Y₂` and a map `π : Y₂ → X`,
the transform of `𝔪` along `π ∘ χ` is the `χ`-pullback of its transform along `π` (coherent ideal, coherent ideal
of the centre, coherent transform). -/
theorem geoTransform_comp_diffeo (𝔪 : MarkedIdeal n X) (h𝔞 : 𝔪.ideal.IsCoherent) (C : Set X)
    (hIC : (vanishingIdeal (n := n) C).IsCoherent) {π : Y₂ → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (hc : (𝔪.geoTransform C π).ideal.IsCoherent) :
    𝔪.geoTransform C (π ∘ χ) = MarkedIdeal.pullback χ (𝔪.geoTransform C π) := by
  have hpa := GermIdealTotalTransform.pullback_comp hπ χ.contMDiff h𝔞
  have hpC := GermIdealTotalTransform.pullback_comp hπ χ.contMDiff hIC
  have hpCc := GermIdealPullbackCalculus.isCoherent_pullback hπ hIC
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of (geoStrictTransform_comp_diffeo χ π C 𝔪.N) ?_ ?_ rfl
  · simp only [geoTransform_E, MarkedIdeal.pullback, List.map_append, List.map_map, List.map_cons,
      List.map_nil]
    congr 1
    exact List.map_congr_left fun A _ => geoStrictTransform_comp_diffeo χ π C A
  · change colonAlong n (geoStrictTransform (π ∘ χ) C 𝔪.N) (GermIdeal.pullback (m := n) (π ∘ χ) 𝔪.ideal)
        (idealPow (GermIdeal.pullback (m := n) (π ∘ χ) (vanishingIdeal (n := n) C)) 𝔪.d) =
      GermIdeal.pullback (m := n) χ (colonAlong n (geoStrictTransform π C 𝔪.N)
        (GermIdeal.pullback (m := n) π 𝔪.ideal)
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) 𝔪.d))
    rw [geoStrictTransform_comp_diffeo χ π C 𝔪.N, hpa, hpC,
      ← BlowupExceptionalDivisor.pullback_idealPow χ.contMDiff hpCc]
    exact colonAlong_pullback_diffeo χ (GermIdealPullbackCalculus.isCoherent_pullback hπ h𝔞)
      (GermIdealPullbackCalculus.isCoherent_idealPow hpCc _) hc

end Naturality

/-! ### Lifting a biholomorphism of open sets along a blowup -/

section Lift

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Y' : Type u} [TopologicalSpace Y'] [ChartedSpace (ComplexModel n) Y'] [IsComplexManifold n Y']
  {C : Set Y} {π : Y' → Y} (hπ : IsBlowupAlong n C π)

/-- The open preimage `π⁻¹(A)`. -/
def preOpen (A : Opens Y) : Opens Y' :=
  ⟨π ⁻¹' (A : Set Y), A.isOpen.preimage hπ.contMDiff.continuous⟩

/-- The restriction `π⁻¹(A) → A` of the blowup. -/
def restrictMap (A : Opens Y) : preOpen hπ A → A := fun p => ⟨π p.1, p.2⟩

theorem isBlowupAlong_restrictMap (A : Opens Y) :
    IsBlowupAlong n ((↑) ⁻¹' C : Set A) (restrictMap hπ A) :=
  isBlowupAlong_restrict hπ A (preOpen hπ A).isOpen

/-- **Lifting a biholomorphism of open sets along a blowup** (Włodarczyk, proof of `le:homo` (4): "by the universal
property of a blow-up"): if `Φ : A ≅ B` maps `C ∩ A` onto `C ∩ B` (`Φ⁻¹(C ∩ B) = C ∩ A`), there is a biholomorphism
`Φ₁ : π⁻¹A ≅ π⁻¹B` with `π ∘ Φ₁ = Φ ∘ π`. -/
theorem exists_lift {A B : Opens Y}
    (Φ : CMfd.of (n := n) A ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) B)
    (hC : Φ ⁻¹' ((↑) ⁻¹' C : Set B) = ((↑) ⁻¹' C : Set A)) :
    ∃ Φ₁ : CMfd.of (n := n) (preOpen hπ A) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (preOpen hπ B),
      ∀ p : preOpen hπ A, π (Φ₁ p : Y') = (Φ (restrictMap hπ A p) : Y) := by
  have hA := isBlowupAlong_restrictMap hπ A
  have hB := isBlowupAlong_restrictMap hπ B
  have hB' := isBlowupAlong_comp_inverse Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply hB
  rw [hC] at hB'
  obtain ⟨e, f, he, hf, hπe, hπf, hfe, hef⟩ := BlowupUniqueness.exists_biholomorphism_over hA hB'
  refine ⟨⟨⟨e, f, congrFun hfe, congrFun hef⟩, he, hf⟩, fun p => ?_⟩
  have h1 : Φ.symm (restrictMap hπ B (e p)) = restrictMap hπ A p := congrFun hπe p
  have h2 : restrictMap hπ B (e p) = Φ (restrictMap hπ A p) := by
    rw [← h1, Φ.apply_symm_apply]
  exact congrArg Subtype.val h2

end Lift

end

end Hironaka.BlowupBiholomorphismLift
