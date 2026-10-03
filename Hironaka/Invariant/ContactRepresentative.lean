/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ContactStageRebase
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.Invariant.ContactEquivalenceAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1 does not depend on the representative of the marked ideal

A marked ideal is only determined by the restriction of its ideal to `N`
(`MarkedIdealOperationsAlong.RestrictEquiv`); Step 1 forms `J̄ = 𝓒_N(𝓗_N(𝔍))`, chooses a tangent direction of
`(𝔍.ideal|_N, d)` and restricts the coefficient ideal of the transform to the strict transform of the hypersurface
of maximal contact. All three steps respect restricted equivalence. Source: Włodarczyk 2005 (arXiv `hiron.tex`),
Proposition `pr:resol` (4) and the definition of marked ideals (`(M, N, E, 𝓘, μ)` with `𝓘` an ideal of `𝒪_N`).

## Main results

* `restrictLe_homogenizedIdealAlong`, `restrictEquiv_homMarkedAlong`, `restrictEquiv_barMarked`: `𝓗_N` and
  `𝓒_N(𝓗_N(·))` respect restricted inclusions / equivalence on `N`;
* `restrictEquiv_pullback_val`: restricted equivalence passes to open sets;
* `exists_isTangentDirectionAlong_of_restrictLe`: a tangent direction `u` of `(𝔞|_N, μ)` on `U` gives, near every point of
  `N ∩ U`, a tangent direction `w` of `(𝔟|_N, μ)` with `w = u` on `N` whenever `𝔞|_N ⊆ 𝔟|_N` (so the hypersurface of maximal
  contact inside `N` is the same);
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ContactRepresentative

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealBiholomorphism DerivativeIdealAlong MarkedIdealRestrictOpen MarkedIdealOperationsAlong.MarkedIdeal ResolutionInvariantExt RestrictedIdealWeight
open HomogenizedGlueingTower (strictAlong)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### The homogenized and coefficient ideals respect restricted equivalence -/

section Hom

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The homogenized ideal along `N` respects restricted inclusions on `N`**: `𝔞|_N ⊆ 𝔟|_N` gives
`𝓗_N(𝔞, μ)|_N ⊆ 𝓗_N(𝔟, μ)|_N` (the derivative ideals along `N` do, and so do products, powers and finite sums). -/
theorem restrictLe_homogenizedIdealAlong {N : Set M} {𝔞 𝔟 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x)
    (h : RestrictLe N 𝔞 𝔟) (μ : ℕ) :
    RestrictLe N (homogenizedIdealAlong N 𝔞 μ) (homogenizedIdealAlong N 𝔟 μ) :=
  HomogenizedIdealAlongTower.restrictLe_homSum
    (fun i _ => GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔟 i)
    (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔟 (μ - 1))
    (fun i _ => ContactCanonicalAlong.restrictLe_iterDerivIdealAlong h𝔞 h𝔟 h i)
    (ContactCanonicalAlong.restrictLe_iterDerivIdealAlong h𝔞 h𝔟 h (μ - 1))

/-- **Restricted-equivalent marked ideals have restricted-equivalent homogenized marked ideals along `N`.** -/
theorem restrictEquiv_homMarkedAlong {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫)
    (h𝔪 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (h𝔫 : ∀ x g, 𝔫.ideal.mem x g → HolomorphicAt n g x) :
    RestrictEquiv (homMarkedAlong 𝔪) (homMarkedAlong 𝔫) where
  N_eq := h.N_eq
  E_eq := h.E_eq
  d_eq := h.d_eq
  le := by
    show RestrictLe 𝔪.N (homogenizedIdealAlong 𝔪.N 𝔪.ideal 𝔪.d) (homogenizedIdealAlong 𝔫.N 𝔫.ideal 𝔫.d)
    rw [← h.N_eq, ← h.d_eq]
    exact restrictLe_homogenizedIdealAlong h𝔪 h𝔫 h.le 𝔪.d
  ge := by
    show RestrictLe 𝔪.N (homogenizedIdealAlong 𝔫.N 𝔫.ideal 𝔫.d) (homogenizedIdealAlong 𝔪.N 𝔪.ideal 𝔪.d)
    rw [← h.N_eq, ← h.d_eq]
    exact restrictLe_homogenizedIdealAlong h𝔫 h𝔪 h.ge 𝔪.d

/-- **The marked ideal of Step 1 respects restricted equivalence**: `𝔍 ≃ 𝔍'` gives `𝓒_N(𝓗_N(𝔍)) ≃ 𝓒_N(𝓗_N(𝔍'))` (`N` a
closed submanifold, coherent ideals). -/
theorem restrictEquiv_barMarked {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    RestrictEquiv (coeffMarkedAlong (homMarkedAlong 𝔪)) (coeffMarkedAlong (homMarkedAlong 𝔫)) :=
  ContactCanonicalAlong.restrictEquiv_coeffMarkedAlong
    (restrictEquiv_homMarkedAlong h (hol_of_isCoherent h𝔪) (hol_of_isCoherent h𝔫))
    (hol_of_isCoherent (isCoherent_homMarkedAlong h𝔪 hN))
    (hol_of_isCoherent (isCoherent_homMarkedAlong h𝔫 (h.N_eq ▸ hN)))

/-- **Restricted equivalence passes to open sets** (the second ideal coherent). -/
theorem restrictEquiv_pullback_val (U : Opens M) {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    RestrictEquiv (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪) (MarkedIdeal.pullback (Subtype.val : U → M) 𝔫) where
  N_eq := by
    show (Subtype.val : U → M) ⁻¹' 𝔪.N = (Subtype.val : U → M) ⁻¹' 𝔫.N
    rw [h.N_eq]
  E_eq := by
    show 𝔪.E.map ((Subtype.val : U → M) ⁻¹' ·) = 𝔫.E.map ((Subtype.val : U → M) ⁻¹' ·)
    rw [h.E_eq]
  d_eq := h.d_eq
  le := RestrictLeCalculus.restrictLe_pullback contMDiff_subtype_val (fun _ hy => hy) h𝔫 h.le
  ge := RestrictLeCalculus.restrictLe_pullback contMDiff_subtype_val (fun _ hy => hy) h𝔪 h.ge

end Hom

/-! ### Tangent directions of restricted-equivalent marked ideals -/

section Tangent

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Tangent directions transfer along restricted inclusions**: if `𝔞|_N ⊆ 𝔟|_N` (`N` a closed submanifold, `𝔟` coherent)
and `u` is a tangent direction of `(𝔞|_N, μ)` along `N` on `U`, then every `x ∈ N ∩ U` has an open neighbourhood `O ⊆ U`
carrying a tangent direction `w` of `(𝔟|_N, μ)` along `N` with `w = u` on `N ∩ O`: on `N`, the germs of `𝓓_N^{μ-1}(𝔞)` are
combinations of germs of `𝓓_N^{μ-1}(𝔟)` (`ContactEquivalenceAlong.exists_isTangentDirectionAlong_of_isInSpanOnAt`). -/
theorem exists_isTangentDirectionAlong_of_restrictLe {N : Set M} {𝔞 𝔟 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (h𝔟 : 𝔟.IsCoherent) (hN : IsClosedSubmanifold n N)
    (h : RestrictLe N 𝔞 𝔟) {μ : ℕ} {U : Set M} {u : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) {x : M}
    (hxU : x ∈ U) (hxN : x ∈ N) :
    ∃ O : Opens M, x ∈ O ∧ (O : Set M) ⊆ U ∧ ∃ w : M → ℂ, IsTangentDirectionAlong N 𝔟 μ O w ∧
      ∀ y ∈ O, y ∈ N → w y = u y :=
  ContactEquivalenceAlong.exists_isTangentDirectionAlong_of_isInSpanOnAt h𝔟 hN hu.isOpen
    (fun y hy => GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (μ - 1) y u (hu.mem y hy))
    (fun y hy hyN => ContactCanonicalAlong.restrictLe_iterDerivIdealAlong h𝔞 (hol_of_isCoherent h𝔟) h (μ - 1) y hyN u
      (hu.mem y hy))
    (fun y hy _ h0 => hu.multiplicity_one y hy h0) hxU hxN

end Tangent

end

end Hironaka.ContactRepresentative
