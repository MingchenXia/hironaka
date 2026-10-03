/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Blowup.BlowupExistenceCodimOne
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Marked ideals, blowups and transforms under biholomorphisms of the base

Source: Włodarczyk 2005 §2.4 (functoriality of the resolution for étale maps, here biholomorphisms; the canonicity
clause (3) of `hir:canonical-resolution`), Bierstone--Milman 2008 Theorem 1.3 (functoriality).

Let `φ : M' → M` be a biholomorphism with inverse `ψ` (holomorphic, `φ ∘ ψ = id`, `ψ ∘ φ = id`).
* `notMem_exceptionalLocus_of_inverse`: a biholomorphism has no exceptional points;
* `pullback_vanishingIdeal_preimage`: `g^*𝓘_{φ⁻¹A} = (φ ∘ g)^*𝓘_A` for every continuous `g` (any dimension of
  the source), in particular `φ^*𝓘_A = 𝓘_{φ⁻¹A}`;
* `isBlowupAlong_comp_inverse`: if `π: Y → M` is a blowup along `C`, then `ψ ∘ π: Y → M'` is a blowup along `φ⁻¹C`
  (the same space `Y`); with `π = id`, `C = ∅`: every biholomorphism is a blowup along `∅`;
* `MarkedIdeal.pullback φ 𝔪 = (φ⁻¹N, φ⁻¹E, φ^*𝔞, d)` and `cosupp_pullback`: `cosupp(φ^*𝔪) = φ⁻¹ cosupp 𝔪` (any `N`);
* `geoTransform_pullback` (**naturality of the transform**): `(φ^*𝔪)` transformed along `ψ ∘ π` with centre
  `φ⁻¹C` is `𝔪` transformed along `π` with centre `C` (coherent ideal).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MarkedIdealBiholomorphism

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers Hironaka.GermIdealTotalTransform Hironaka.GermIdealPullbackCalculus Hironaka.HadamardBridge Hironaka.MarkedIdeals Hironaka.BlowupStrictSubmanifold Hironaka.IdealOrderArithmetic

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {φ : M' → M} {ψ : M → M'}

/-! ### Biholomorphisms -/

section Biholomorphism

variable (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
  (hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ)
  (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ p, ψ (φ p) = p)
include hφ hψ hφψ hψφ

/-- **A biholomorphism has no exceptional points.** -/
theorem notMem_exceptionalLocus_of_inverse (p : M') : p ∉ exceptionalLocus n φ := by
  intro hp
  apply hp
  have hφd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ q :=
    fun q => (hφ q).mdifferentiableAt (by simp)
  have hψd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ q :=
    fun q => (hψ q).mdifferentiableAt (by simp)
  have h1 : (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ (φ p)).comp
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ p) = ContinuousLinearMap.id ℂ _ := by
    rw [← mfderiv_comp p (hψd _) (hφd p), show ψ ∘ φ = id from funext hψφ]
    exact mfderiv_id
  have h2 : (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ (ψ (φ p))).comp
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ (φ p)) = ContinuousLinearMap.id ℂ _ := by
    rw [← mfderiv_comp (φ p) (hφd _) (hψd (φ p)), show φ ∘ ψ = id from funext hφψ]
    exact mfderiv_id
  rw [hψφ] at h2
  exact ⟨Function.LeftInverse.injective (g := mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ (φ p))
      fun v => DFunLike.congr_fun h1 v,
    Function.RightInverse.surjective (g := mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ (φ p))
      fun v => DFunLike.congr_fun h2 v⟩

/-- **Preimages of closed submanifolds under a biholomorphism are closed submanifolds.** -/
theorem isClosedSubmanifold_preimage {C : Set M} (hC : IsClosedSubmanifold n C) :
    IsClosedSubmanifold n (φ ⁻¹' C) := by
  refine ⟨hC.1.preimage hφ.continuous, fun p hp => ?_⟩
  obtain ⟨k, hk⟩ := hC.2 _ hp
  exact ⟨k, RegularAtDimTransport.regularAtDim_of_preimage hφ
    (notMem_exceptionalLocus_of_inverse hφ hψ hφψ hψφ p) isOpen_univ (mem_univ p)
    (fun _ _ => Iff.rfl) hk⟩

/-- `ψ⁻¹(φ⁻¹ A) = A`. -/
theorem preimage_preimage_eq (A : Set M) : ψ ⁻¹' (φ ⁻¹' A) = A := by
  ext x
  simp [hφψ x]

/-- **Vanishing ideals under a biholomorphism**: `g^*𝓘_{φ⁻¹A} = (φ ∘ g)^*𝓘_A` for every holomorphic `g`
(any source dimension). -/
theorem pullback_vanishingIdeal_preimage {m : ℕ} {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z] {g : Z → M'}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g) (A : Set M) :
    GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) (φ ⁻¹' A)) =
      GermIdeal.pullback (m := m) (φ ∘ g) (vanishingIdeal (n := n) A) := by
  have hφd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ q :=
    fun q => (hφ q).mdifferentiableAt (by simp)
  have hψd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ q :=
    fun q => (hψ q).mdifferentiableAt (by simp)
  have hgd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) g q :=
    fun q => (hg q).mdifferentiableAt (by simp)
  have hφgd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) (φ ∘ g) q :=
    fun q => (hφd (g q)).comp q (hgd q)
  refine GermIdeal.ext (funext fun z => funext fun f => propext ⟨fun hf => ?_, fun hf => ?_⟩)
  · refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (RelativePrincipalizationSpan.IsInSpanAt.trans ?_
        (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf))
    rintro s ⟨t, ht, rfl⟩
    have htψ : (vanishingIdeal (n := n) A).mem ((φ ∘ g) z) (t ∘ ψ) := by
      refine ⟨?_, ?_⟩
      · have h1 : HolomorphicAt n t (ψ ((φ ∘ g) z)) := by
          simpa only [Function.comp_apply, hψφ] using ht.1
        exact holomorphicAt_comp_map (Eventually.of_forall hψd) h1
      · have hT : Tendsto ψ (𝓝 ((φ ∘ g) z)) (𝓝 (g z)) := by
          have := (hψ.continuous.tendsto ((φ ∘ g) z))
          simpa only [Function.comp_apply, hψφ] using this
        filter_upwards [hT.eventually ht.2] with a ha haA
        exact ha (by simp only [mem_preimage, hφψ]; exact haA)
    have heq : t ∘ g = (t ∘ ψ) ∘ (φ ∘ g) := funext fun q => by simp [hψφ]
    rw [heq]
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨t ∘ ψ, htψ, rfl⟩
      (holomorphicAt_comp_map (Eventually.of_forall hφgd) htψ.1)
  · refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (RelativePrincipalizationSpan.IsInSpanAt.trans ?_
        (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf))
    rintro s ⟨t, ht, rfl⟩
    have htφ : (vanishingIdeal (n := n) (φ ⁻¹' A)).mem (g z) (t ∘ φ) := by
      refine ⟨holomorphicAt_comp_map (Eventually.of_forall hφd) ht.1, ?_⟩
      filter_upwards [(hφ.continuous.tendsto (g z)).eventually ht.2] with a ha haA
      exact ha haA
    exact InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a,
        (vanishingIdeal (n := n) (φ ⁻¹' A)).mem (g z) a ∧ s = a ∘ g) ⟨t ∘ φ, htφ, rfl⟩
      (show HolomorphicAt m ((t ∘ φ) ∘ g) z from holomorphicAt_comp_map (Eventually.of_forall hgd) htφ.1)

/-- **A blowup composed with a biholomorphism of the base**: if `π : Y → M` is a blowup along `C`, then
`ψ ∘ π : Y → M'` is a blowup along `φ⁻¹C`. -/
theorem isBlowupAlong_comp_inverse {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {C : Set M} {π : Y → M} (hπ : IsBlowupAlong n C π) :
    IsBlowupAlong n (φ ⁻¹' C) (ψ ∘ π) := by
  let h : M' ≃ₜ M := ⟨⟨φ, ψ, hψφ, hφψ⟩, hφ.continuous, hψ.continuous⟩
  have hint : interior (φ ⁻¹' C) = ∅ := by
    have := h.preimage_interior C
    simp only [hπ.2.1, preimage_empty] at this
    exact this.symm
  have hinv : GermIdeal.pullback (m := n) (ψ ∘ π) (vanishingIdeal (n := n) (φ ⁻¹' C)) =
      GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) := by
    rw [← pullback_vanishingIdeal_preimage hψ hφ hψφ hφψ hπ.contMDiff (φ ⁻¹' C),
      preimage_preimage_eq hφ hψ hφψ hψφ]
  refine ⟨isClosedSubmanifold_preimage hφ hψ hφψ hψφ hπ.1, hint, hψ.comp hπ.contMDiff, ?_, ?_⟩
  · rw [hinv]
    exact hπ.2.2.2.1
  · intro m Z _ _ _ g hg hginv
    rw [pullback_vanishingIdeal_preimage hφ hψ hφψ hψφ hg C] at hginv
    obtain ⟨k, ⟨hk, hπk⟩, huniq⟩ := hπ.2.2.2.2 m Z (φ ∘ g) (hφ.comp hg) hginv
    refine ⟨k, ⟨hk, ?_⟩, fun k' ⟨hk', hπk'⟩ => huniq k' ⟨hk', ?_⟩⟩
    · funext z
      have := congrFun hπk z
      simp only [Function.comp_apply] at this ⊢
      rw [this, hψφ]
    · funext z
      have := congrArg φ (congrFun hπk' z)
      simp only [Function.comp_apply, hφψ] at this ⊢
      exact this

end Biholomorphism

/-! ### Marked ideals -/

namespace MarkedIdeal

/-- **The pullback of a marked ideal** by `φ : M' → M`: `(φ⁻¹N, φ⁻¹E, φ^*𝔞, d)`. -/
def pullback (φ : M' → M) (𝔪 : MarkedIdeal n M) : MarkedIdeal n M' where
  N := φ ⁻¹' 𝔪.N
  E := 𝔪.E.map (φ ⁻¹' ·)
  ideal := GermIdeal.pullback (m := n) φ 𝔪.ideal
  d := 𝔪.d

variable (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
  (hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ)
  (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ p, ψ (φ p) = p)
include hφ hψ hφψ hψφ

/-- **The cosupport of a pulled-back marked ideal** (any `N`): `cosupp(φ^*𝔪) = φ⁻¹ cosupp(𝔪)`. -/
theorem cosupp_pullback (𝔪 : MarkedIdeal n M) (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) :
    (pullback φ 𝔪).cosupp = φ ⁻¹' 𝔪.cosupp := by
  have hφd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ q :=
    fun q => (hφ q).mdifferentiableAt (by simp)
  have hψd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ q :=
    fun q => (hψ q).mdifferentiableAt (by simp)
  -- orders along `N` pull back along holomorphic maps
  have hcomp : ∀ {Θ : M' → M} {p : M'} {N : Set M} {q : ℕ} {g : M → ℂ},
      (∀ r, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Θ r) → Continuous Θ →
      VanishesToOrderOn n N (Θ p) q g → VanishesToOrderOn n (Θ ⁻¹' N) p q (g ∘ Θ) := by
    intro Θ p N q g hΘ hΘc ⟨h, hh, hgh⟩
    exact ⟨h ∘ Θ, comp_mem_idealPow_pointIdeal (Eventually.of_forall hΘ) q hh,
      by filter_upwards [(hΘc.tendsto p).eventually hgh] with r hr hrN; exact hr hrN⟩
  have hcomp' : ∀ {Θ : M → M'} {p : M} {N : Set M'} {q : ℕ} {g : M' → ℂ},
      (∀ r, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Θ r) → Continuous Θ →
      VanishesToOrderOn n N (Θ p) q g → VanishesToOrderOn n (Θ ⁻¹' N) p q (g ∘ Θ) := by
    intro Θ p N q g hΘ hΘc ⟨h, hh, hgh⟩
    exact ⟨h ∘ Θ, comp_mem_idealPow_pointIdeal (Eventually.of_forall hΘ) q hh,
      by filter_upwards [(hΘc.tendsto p).eventually hgh] with r hr hrN; exact hr hrN⟩
  ext p
  constructor
  · rintro ⟨hpN, hp⟩
    refine ⟨hpN, fun a ha => ?_⟩
    have haφ : (GermIdeal.pullback (m := n) φ 𝔪.ideal).mem p (a ∘ φ) :=
      RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
        (InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ b, 𝔪.ideal.mem (φ p) b ∧ s = b ∘ φ)
          ⟨a, ha, rfl⟩ (holomorphicAt_comp_map (Eventually.of_forall hφd) (h𝔞 _ _ ha)))
    have h1 := hp _ haφ
    have h1' : VanishesToOrderOn n (φ ⁻¹' 𝔪.N) (ψ (φ p)) 𝔪.d (a ∘ φ) := by rwa [hψφ]
    have h2 := hcomp' hψd hψ.continuous h1'
    rwa [show (a ∘ φ) ∘ ψ = a from funext fun x => by simp [hφψ x],
      preimage_preimage_eq hφ hψ hφψ hψφ] at h2
  · rintro ⟨hpN, hp⟩
    refine ⟨hpN, fun g hg => ?_⟩
    refine IsInSpanAt.vanishesToOrderOn (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg) ?_
    rintro s ⟨a, ha, rfl⟩
    exact hcomp hφd hφ.continuous (hp a ha)

/-- **Naturality of the transform under biholomorphisms of the base**: transforming `φ^*𝔪` along the blowup
`ψ ∘ π` with centre `φ⁻¹C` gives the transform of `𝔪` along `π` with centre `C` (on the same space `Y`). -/
theorem geoTransform_pullback (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent) {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] (C : Set M) {π : Y → M}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) :
    (pullback φ 𝔪).geoTransform (φ ⁻¹' C) (ψ ∘ π) = 𝔪.geoTransform C π := by
  have hpre := preimage_preimage_eq hφ hψ hφψ hψφ
  have hgeo : ∀ A : Set M, geoStrictTransform (ψ ∘ π) (φ ⁻¹' C) (φ ⁻¹' A) = geoStrictTransform π C A := by
    intro A
    simp only [geoStrictTransform, ← preimage_sdiff, preimage_comp, hpre]
  have hN : ((pullback φ 𝔪).geoTransform (φ ⁻¹' C) (ψ ∘ π)).N = (𝔪.geoTransform C π).N := hgeo 𝔪.N
  have hpb : GermIdeal.pullback (m := n) (ψ ∘ π) (GermIdeal.pullback (m := n) φ 𝔪.ideal) =
      GermIdeal.pullback (m := n) π 𝔪.ideal := by
    rw [pullback_comp hψ hπ (isCoherent_pullback hφ h𝔞), ← pullback_comp hφ hψ h𝔞,
      show φ ∘ ψ = id from funext hφψ, BlowupControlledTransform.pullback_id h𝔞]
  have hI : GermIdeal.pullback (m := n) (ψ ∘ π) (vanishingIdeal (n := n) (φ ⁻¹' C)) =
      GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) := by
    rw [← pullback_vanishingIdeal_preimage hψ hφ hψφ hφψ hπ (φ ⁻¹' C), hpre]
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN ?_ ?_ rfl
  · simp only [MarkedIdeals.MarkedIdeal.geoTransform_E, pullback, List.map_map]
    congr 1
    · exact List.map_congr_left fun A _ => hgeo A
    · simp only [preimage_comp, hpre]
  · rw [MarkedIdeals.MarkedIdeal.geoTransform_ideal, MarkedIdeals.MarkedIdeal.geoTransform_ideal]
    show RestrictedIdealQuotient.colonAlong n (geoStrictTransform (ψ ∘ π) (φ ⁻¹' C) (φ ⁻¹' 𝔪.N))
      (GermIdeal.pullback (m := n) (ψ ∘ π) (GermIdeal.pullback (m := n) φ 𝔪.ideal))
      (idealPow (GermIdeal.pullback (m := n) (ψ ∘ π) (vanishingIdeal (n := n) (φ ⁻¹' C))) 𝔪.d) = _
    rw [hgeo, hpb, hI]

end MarkedIdeal

end

end Hironaka.MarkedIdealBiholomorphism
