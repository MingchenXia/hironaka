/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Pullback calculus for germ ideals

Step 1 starts from the inclusion `𝔅_M ⊆ 𝔅_m^{M/m}` on `V` and transports it to `Y_fix`:

    `𝔅_M 𝒪_{Y_fix} ⊆ (𝔅_m 𝒪_{Y_fix})^{M/m} = 𝒪_{Y_fix}(-(M/m) G̃_m)`,

This module supplies them:

* `isInSpanAt_comp` — a span relation at `f y` composes with `f` to a span
  relation at `y` in the pulled-back family.  The workhorse; everything else is
  an application.
* `pullback_le_pullback` — `𝔞 ⊆ 𝔟` implies `𝔞 𝒪_Y ⊆ 𝔟 𝒪_Y`.
* `isCoherent_pullback` — **the pullback of a coherent ideal along a holomorphic
  map is coherent**, with the pulled-back generators as generators.  Without it
  `InvertibleIdealQuotient` cannot even be applied to `𝔅_M 𝒪_{Y_fix}`.

No Hironaka input, no compactness, no Kähler hypothesis.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.GermIdealPullbackCalculus

open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan IdealWeightPowers

noncomputable section

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
  {f : Y → M}

/-! ## Composition of span relations -/

/-- A span relation at `f y` composes with a holomorphic `f` to a span relation
at `y`, with the composed family as generators. -/
theorem isInSpanAt_comp
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {S : (M → ℂ) → Prop} {y : Y} {c : M → ℂ} (hc : IsInSpanAt (n := n) S (f y) c) :
    IsInSpanAt (n := m) (fun s => ∃ a, S a ∧ s = a ∘ f) y (c ∘ f) := by
  obtain ⟨hchol, N, s, a, hs, ha, hsum⟩ := hc
  have hfat : ∀ᶠ z in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f z :=
    Eventually.of_forall fun z => hf.contMDiffAt
  refine ⟨hchol.comp_contMDiff hfat, N, fun i => s i ∘ f, fun i => a i ∘ f,
    fun i => ⟨s i, hs i, rfl⟩, fun i => (ha i).comp_contMDiff hfat, ?_⟩
  exact Filter.Tendsto.eventually hf.continuous.continuousAt hsum

/-! ## Monotonicity and coherence of the pullback -/

/-- The pullback ideal is monotone in the source ideal. -/
theorem pullback_le_pullback {𝔞 𝔟 : GermIdeal n M} (h : 𝔞.Le 𝔟) :
    (GermIdeal.pullback (m := m) f 𝔞).Le (GermIdeal.pullback (m := m) f 𝔟) := by
  intro y g hg
  refine GermIdeal.mem_pullback_iff.mpr
    (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg))
  rintro s ⟨a, ham, rfl⟩
  exact ⟨a, h _ _ ham, rfl⟩

/-- **The pullback of a coherent ideal along a holomorphic map is coherent**, and
the pulled-back generators generate it. -/
theorem isCoherent_pullback
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    (GermIdeal.pullback (m := m) f 𝔞).IsCoherent := by
  intro y
  obtain ⟨U, hU, hxU, N, s, hs, hgen⟩ := h𝔞 (f y)
  have hfat : ∀ {z : Y}, ∀ᶠ z' in 𝓝 z,
      ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f z' :=
    fun {_} => Eventually.of_forall fun z => hf.contMDiffAt
  have hshol : ∀ (i : Fin N), ∀ x ∈ U, HolomorphicAt n (s i) x := fun i x hx =>
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hs i) hx
  refine ⟨f ⁻¹' U, hU.preimage hf.continuous, hxU, N, fun i => s i ∘ f, ?_, ?_⟩
  · intro i z hz
    exact ((hshol i (f z) hz).comp_contMDiff hfat).mdifferentiableAt.mdifferentiableWithinAt
  intro z hz g
  constructor
  · -- Every pulled-back germ is a combination of the pulled-back generators.
    intro hg
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro t ⟨a, ham, rfl⟩
    refine IsInSpanAt.mono ?_ (isInSpanAt_comp hf ((hgen (f z) hz a).mp ham))
    rintro s' ⟨σ, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · -- Conversely each pulled-back generator lies in the pullback ideal.
    intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hg)
    rintro s' ⟨i, rfl⟩
    exact ⟨s i, (hgen (f z) hz (s i)).mpr (InvertibleIdealQuotient.isInSpanAt_self
      ⟨i, rfl⟩ (hshol i (f z) hz)), rfl⟩

/-! ## Products -/

/-- The pullback of a product is contained in the product of the pullbacks.  The
left factor's members must be holomorphic; see the corollaries. -/
theorem pullback_mul_le
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {𝔞 𝔟 : GermIdeal n M}
    (h𝔞hol : ∀ {x : M} {g : M → ℂ}, 𝔞.mem x g → HolomorphicAt n g x)
    (h𝔟hol : ∀ {x : M} {g : M → ℂ}, 𝔟.mem x g → HolomorphicAt n g x) :
    (GermIdeal.pullback (m := m) f (𝔞.mul 𝔟)).Le
      ((GermIdeal.pullback (m := m) f 𝔞).mul (GermIdeal.pullback (m := m) f 𝔟)) := by
  intro y g hg
  have hfat : ∀ᶠ z in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f z :=
    Eventually.of_forall fun z => hf.contMDiffAt
  refine InvertibleIdealQuotient.mem_mul_iff.mpr
    (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg))
  rintro t ⟨c, hcmem, rfl⟩
  refine IsInSpanAt.mono ?_
    (isInSpanAt_comp hf (InvertibleIdealQuotient.mem_mul_iff.mp hcmem))
  rintro s' ⟨σ, ⟨a, b, ham, hbm, rfl⟩, rfl⟩
  refine ⟨a ∘ f, b ∘ f, ?_, ?_, funext fun z => rfl⟩
  · exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨a, ham, rfl⟩
      ((h𝔞hol ham).comp_contMDiff hfat)
      (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))
  · exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨b, hbm, rfl⟩
      ((h𝔟hol hbm).comp_contMDiff hfat)
      (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))

/-- Coherence is stable under powers. -/
theorem isCoherent_idealPow {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    ∀ p : ℕ, (idealPow 𝔞 p).IsCoherent
  | 0 => isCoherent_unitIdeal
  | p + 1 => isCoherent_mul (isCoherent_idealPow h𝔞 p) h𝔞

/-! ## Absorption -/

/-- `𝔞 · 𝔟 ⊆ 𝔞`, the mirror statement. -/
theorem mul_le_left {𝔞 𝔟 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    (h𝔟hol : ∀ {x : M} {g : M → ℂ}, 𝔟.mem x g → HolomorphicAt n g x) :
    (𝔞.mul 𝔟).Le 𝔞 := by
  intro x g hg
  obtain ⟨U, hU, hxU, N, s, hs, hgen⟩ := h𝔞 x
  refine (hgen x hxU g).mpr
    (IsInSpanAt.trans ?_ (InvertibleIdealQuotient.mem_mul_iff.mp hg))
  rintro t ⟨p, q, hp, hq, rfl⟩
  refine InvertibleIdealQuotient.IsInSpanAt.congr'
    (IsInSpanAt.mul_left (h𝔟hol hq) ((hgen x hxU p).mp hp)) ?_
  exact Eventually.of_forall fun z => mul_comm _ _

end

end Hironaka.GermIdealPullbackCalculus
