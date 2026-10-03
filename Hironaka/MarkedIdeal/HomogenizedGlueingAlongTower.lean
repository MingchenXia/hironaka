/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedGlueingAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The glueing lemma along a submanifold, on open sets and along multiple test blow-ups (pullback form)

Source: Włodarczyk 2005, Lemma `le:homo` (1)--(3) restated on open sets and the part of (4) that follows from the
functoriality of multiple test blow-ups under étale maps (Proposition `pr:funct`), for the marked ideal `(𝓗_N(𝔞),
μ)` on the submanifold `N`, in the ambient encoding: the marked ideal is `homogenizedMarkedAlong N 𝔞 μ = (M, N, ∅,
𝓗_N(𝔞), μ)`, and the glueing biholomorphism preserves `N`.

* `GlueingDataAlong N 𝔞 μ u v`: a local inverse pair `(φ, ψ)` on an open `W` with the conclusions of the glueing
  lemma along `N` on `W` (including `φ⁻¹N = N`).
* `GlueingDataAlong.pullback_restrict`: **`Φ^*((𝓗_N(𝔞), μ)|_{U'}) = (𝓗_N(𝔞), μ)|_U` as marked ideals** (the
  submanifold `N ∩ U'` pulls back to `N ∩ U`); `preimage_zeroSet`: `Φ⁻¹(V(u) ∩ U') = V(v) ∩ U`; `preimage_inter_eq`:
  `Φ` fixes `cosupp(𝔞|_N, μ) ∩ U` and `Φ⁻¹(C ∩ U') = C ∩ U` for `C ⊆ cosupp(𝔞|_N, μ)`.

Not here: the stage-by-stage lifts of `Φ` along a tower (the along-`N` form of `mc:glueing-lift`), which use the inclusions
of derivative ideals along `N` under blowups (item (2) of `hir:along-calculus`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedGlueingAlongTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport MarkedIdealRestrictOpen BlowupTowerTransforms BlowupRestrictOpen MarkedIdealOpenBiholomorphism HomogenizedIdealAlong HomogenizedGlueingAlong TangentDirectionAlong
open HomogenizedGlueingTower (LocalInversePair strictAlong strictAlong_restrict)

noncomputable section

/-! ### The glueing biholomorphism along `N` -/

section Glueing

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The homogenized marked ideal along `N`** `(M, N, ∅, 𝓗_N(𝔞), μ)`. -/
def homogenizedMarkedAlong (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) : MarkedIdeal n M where
  N := N
  E := []
  ideal := homogenizedIdealAlong N 𝔞 μ
  d := μ

/-- **The glueing data along `N` of two tangent directions** `u`, `v` of `(𝔞|_N, μ)`: a local inverse pair `(φ, ψ)` on an
open set `W` on which `φ^*𝓗_N(𝔞) = 𝓗_N(𝔞)`, `u ∘ φ = v`, `φ` fixes `cosupp(𝔞|_N, μ)` pointwise, and `φ⁻¹N = N`. -/
structure GlueingDataAlong (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) (u v : M → ℂ) where
  /-- The coordinate change replacing `u` by `v`. -/
  φ : M → M
  /-- Its inverse. -/
  ψ : M → M
  /-- The open set on which everything holds. -/
  W : Set M
  pair : LocalInversePair (n := n) φ ψ W
  pullback_iff : ∀ y ∈ W, ∀ g, (GermIdeal.pullback (m := n) φ (homogenizedIdealAlong N 𝔞 μ)).mem y g ↔
    (homogenizedIdealAlong N 𝔞 μ).mem y g
  comp_eq : ∀ p ∈ W, u (φ p) = v p
  apply_eq_self : ∀ y ∈ W, y ∈ cosupport n N 𝔞 μ → φ y = y
  mem_N_iff : ∀ p ∈ W, (φ p ∈ N ↔ p ∈ N)

namespace GlueingDataAlong

variable {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} {u v : M → ℂ} (G : GlueingDataAlong N 𝔞 μ u v)

/-- The open neighbourhood `U = W ∩ φ⁻¹W`. -/
abbrev dom : Opens M := G.pair.dom

/-- Its image `U' = φ(U)`. -/
abbrev cod : Opens M := G.pair.cod

/-- **The glueing biholomorphism** `Φ : U ≅ U'`, `p ↦ φ p`. -/
abbrev equiv : CMfd.of (n := n) G.dom ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) G.cod :=
  G.pair.toDiffeomorph

/-- A point of the cosupport in `W` lies in both `U` and `U'`. -/
theorem mem_dom_and_mem_cod {x : M} (hxW : x ∈ G.W) (hx : x ∈ cosupport n N 𝔞 μ) :
    x ∈ G.dom ∧ x ∈ G.cod := by
  have hφx : G.φ x = x := G.apply_eq_self x hxW hx
  have hdom : x ∈ G.dom := ⟨hxW, by rw [mem_preimage, hφx]; exact hxW⟩
  refine ⟨hdom, hxW, ?_⟩
  have hψx : G.ψ x = x := by
    have h := G.pair.left_inv x hxW
    rwa [hφx] at h
  show G.ψ x ∈ G.dom
  rw [hψx]
  exact hdom

/-- **`Φ` maps `V(v)` onto `V(u)`** (`le:homo` (2)): `Φ⁻¹(V(u) ∩ U') = V(v) ∩ U`. -/
theorem preimage_zeroSet :
    G.equiv ⁻¹' ((↑) ⁻¹' {y | u y = 0} : Set G.cod) = ((↑) ⁻¹' {y | v y = 0} : Set G.dom) := by
  ext p
  change u (G.φ p.1) = 0 ↔ v p.1 = 0
  rw [G.comp_eq p.1 p.2.1]

/-- **`Φ` preserves `N`**: `Φ⁻¹(N ∩ U') = N ∩ U`. -/
theorem preimage_N : G.equiv ⁻¹' ((↑) ⁻¹' N : Set G.cod) = ((↑) ⁻¹' N : Set G.dom) := by
  ext p
  exact G.mem_N_iff p.1 p.2.1

/-- `(φ|_U)^* 𝓗_N(𝔞) = 𝓗_N(𝔞)|_U`. -/
theorem pullback_comp_val (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) :
    GermIdeal.pullback (m := n) (fun p : G.dom => G.φ p) (homogenizedIdealAlong N 𝔞 μ) =
      GermIdeal.pullback (m := n) (Subtype.val : G.dom → M) (homogenizedIdealAlong N 𝔞 μ) := by
  have hH := isCoherent_homogenizedIdealAlong h𝔞 hN μ
  refine GermIdeal.ext (funext fun p => funext fun f => propext ⟨fun hf => ?_, fun hf => ?_⟩)
  · refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf))
    rintro s ⟨b, hb, rfl⟩
    have hφp : ∀ᶠ q in 𝓝 (p : M),
        MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) G.φ q :=
      eventually_of_mem (G.pair.isOpen.mem_nhds p.2.1) G.pair.mdifferentiableAt_left
    have hbφ : (homogenizedIdealAlong N 𝔞 μ).mem p (b ∘ G.φ) :=
      (G.pullback_iff p.1 p.2.1 _).mp (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
        (InvertibleIdealQuotient.isInSpanAt_self ⟨b, hb, rfl⟩
          (HadamardBridge.holomorphicAt_comp_map hφp (HomogenizedGlueing.holomorphicAt_of_mem hH hb))))
    exact ⟨b ∘ G.φ, hbφ, rfl⟩
  · refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (RelativePrincipalizationSpan.IsInSpanAt.trans ?_
        (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf))
    rintro s ⟨g, hg, rfl⟩
    have h1 := RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp
      ((G.pullback_iff p.1 p.2.1 g).mpr hg)
    refine IsInSpanAt.mono ?_ (GermIdealPullbackCalculus.isInSpanAt_comp
      (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) (U := G.dom)) (y := p) h1)
    rintro s ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, rfl⟩

/-- **The glueing biholomorphism preserves the homogenized marked ideal along `N`** (`le:homo` (1) on `U`, with `N`):
`Φ^*((𝓗_N(𝔞), μ)|_{U'}) = (𝓗_N(𝔞), μ)|_U`. -/
theorem pullback_restrict (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) :
    MarkedIdeal.pullback G.equiv
        (MarkedIdeal.pullback (Subtype.val : G.cod → M) (homogenizedMarkedAlong N 𝔞 μ)) =
      MarkedIdeal.pullback (Subtype.val : G.dom → M) (homogenizedMarkedAlong N 𝔞 μ) := by
  have hH := isCoherent_homogenizedIdealAlong h𝔞 hN μ
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of G.preimage_N rfl ?_ rfl
  change GermIdeal.pullback (m := n) G.equiv
      (GermIdeal.pullback (m := n) (Subtype.val : G.cod → M) (homogenizedIdealAlong N 𝔞 μ)) =
    GermIdeal.pullback (m := n) (Subtype.val : G.dom → M) (homogenizedIdealAlong N 𝔞 μ)
  rw [← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val G.equiv.contMDiff hH]
  exact G.pullback_comp_val h𝔞 hN

end GlueingDataAlong

end Glueing

end

end Hironaka.HomogenizedGlueingAlongTower
