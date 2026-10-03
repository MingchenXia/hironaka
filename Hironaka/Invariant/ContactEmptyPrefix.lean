/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ContactStageKept
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.Invariant.ContactEquivalenceStage
import Hironaka.Invariant.ContactRepresentative
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
import Hironaka.MarkedIdeal.DerivativeIdealAlongTransform
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainRebase
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1b re-based across an empty prefix of the base

Source: Włodarczyk 2005 (arXiv `hiron.tex`), the definition of extensions (isomorphisms inserted anywhere in a
resolution) and the commutativity of the resolution procedure in Step 1 with étale morphisms.

## Main results

* `restrictEquiv_trans` (generic);
* `restrictEquiv_homMarkedAlong_geoTransform_empty`, `restrictEquiv_barMarked_geoTransform_empty`: across one blowup
  along `∅`, `𝓗_{N'}(𝔍') ≃ 𝓗_N(𝔍)'` and `𝓒(𝓗(𝔍')) ≃ 𝓒(𝓗(𝔍))'` (the twins of (K3) for `𝓒`);
* **`restrictEquiv_barMarked_geoTransformAlong_of_isEmptyTower`**: along a tower `P` with only empty centres,
  `𝓒(𝓗(𝔍_P)) ≃ 𝓒(𝓗(𝔍))_P`; `isGeoTestTower_barMarked_geoTransformAlong_iff`: `T₀'` is a multiple test blow-up of `𝓒(𝓗(𝔍_P))`
  iff `P T₀'` is one of `𝓒(𝓗(𝔍))`;
* `isTangentDirectionAlong_geoTransformAlong_of_isEmptyTower`: `u ∘ p_P` is a tangent direction of `(𝔍_P.ideal|_{N_P}, d)` on
  `p_P⁻¹U`, with `N_P ∩ V(u ∘ p_P) = p_P⁻¹(N ∩ V(u))`; `strictAlong_of_isEmptyTower` (closed sets),
  `strictAlong_inter_zero_of_isEmptyTower` (the strict transform of `N ∩ V(u)` over `p_P⁻¹U`);
* **`restrictEquiv_contactMarkedKept_emptyPrefix`**, **`contactMarkedKept_emptyPrefix`**: for `W` over `U`,
  `contactMarkedKept 𝔍_P (u ∘ p_P) T₀' W ≃ contactMarkedKept 𝔍 u (P T₀') W`, with the same domain, canonical segments and values.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ContactEmptyPrefix

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantExt MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal ContactStageKept RestrictedIdealWeight
open HomogenizedGlueingTower (strictAlong strictAlong_step N_geoTransformAlong)
open ContactIndependenceAlong (one_le_coeffMarkedAlong_d)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Restricted equivalence is transitive -/

section Trans

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Restricted equivalence is transitive. -/
theorem restrictEquiv_trans {𝔪 𝔫 𝔬 : MarkedIdeal n M} (h₁ : RestrictEquiv 𝔪 𝔫) (h₂ : RestrictEquiv 𝔫 𝔬) :
    RestrictEquiv 𝔪 𝔬 where
  N_eq := h₁.N_eq.trans h₂.N_eq
  E_eq := h₁.E_eq.trans h₂.E_eq
  d_eq := h₁.d_eq.trans h₂.d_eq
  le := DerivativeIdealAlongTransform.restrictLe_trans h₁.le (by rw [h₁.N_eq]; exact h₂.le)
  ge := DerivativeIdealAlongTransform.restrictLe_trans (by rw [h₁.N_eq]; exact h₂.ge) h₁.ge

end Trans

/-! ### One blowup along the empty set -/

section OneStep

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {π : Z → Y}

/-- **The homogenized marked ideal along `N` across a step with empty centre**: for the blowup `π` along `∅`,
`𝓗_{N'}(𝔪') ≃ 𝓗_N(𝔪)'` (`N` a closed submanifold, coherent ideal, `d ≥ 1`): both are restricted-equivalent on `N' = π⁻¹N`
to `π^*𝓗_N(𝔪) = 𝓗_{π⁻¹N}(π^*𝔪)`. -/
theorem restrictEquiv_homMarkedAlong_geoTransform_empty (𝔪 : MarkedIdeal n Y) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (hπ : IsBlowupAlong n (∅ : Set Y) π) :
    RestrictEquiv (homMarkedAlong (𝔪.geoTransform ∅ π)) ((homMarkedAlong 𝔪).geoTransform ∅ π) := by
  have hloc := ContactCanonicalAlong.exists_isLocalInverseAt_of_isBlowupAlong_empty hπ
  have hW : (𝔪.geoTransform ∅ π).N = (MarkedIdeal.pullback π 𝔪).N :=
    ContactCanonicalAlong.geoStrictTransform_empty hπ.contMDiff.continuous hN.1
  have hpb : (homMarkedAlong (MarkedIdeal.pullback π 𝔪)).ideal =
      GermIdeal.pullback (m := n) π (homMarkedAlong 𝔪).ideal :=
    (congrArg MarkedIdeal.ideal (pullback_homMarkedAlong hπ.contMDiff hloc 𝔪 h𝔞 hN hd)).symm
  have hhol𝔭 : ∀ x g, (MarkedIdeal.pullback π 𝔪).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg).1
  have hhol' : ∀ x g, (𝔪.geoTransform ∅ π).ideal.mem x g → HolomorphicAt n g x :=
    hol_of_isCoherent (HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h𝔞
      (isAdmissibleCentre_empty 𝔪) hπ)
  have a1 : RestrictLe (𝔪.geoTransform ∅ π).N (homMarkedAlong (𝔪.geoTransform ∅ π)).ideal
      (homMarkedAlong (MarkedIdeal.pullback π 𝔪)).ideal := by
    have h := ContactRepresentative.restrictLe_homogenizedIdealAlong hhol' hhol𝔭
      (ContactCanonicalAlong.restrictLe_geoTransform_empty_le_pullback hπ 𝔪) 𝔪.d
    show RestrictLe (𝔪.geoTransform ∅ π).N
      (homogenizedIdealAlong (𝔪.geoTransform ∅ π).N (𝔪.geoTransform ∅ π).ideal 𝔪.d)
      (homogenizedIdealAlong (MarkedIdeal.pullback π 𝔪).N (GermIdeal.pullback (m := n) π 𝔪.ideal) 𝔪.d)
    rw [← hW]
    exact h
  have a2 : RestrictLe (𝔪.geoTransform ∅ π).N (homMarkedAlong (MarkedIdeal.pullback π 𝔪)).ideal
      (homMarkedAlong (𝔪.geoTransform ∅ π)).ideal := by
    have h0 : RestrictLe (𝔪.geoTransform ∅ π).N (GermIdeal.pullback (m := n) π 𝔪.ideal) (𝔪.geoTransform ∅ π).ideal :=
      ContactCanonicalAlong.restrictLe_pullback_le_geoTransform (π := π) ∅ 𝔪
    have h := ContactRepresentative.restrictLe_homogenizedIdealAlong hhol𝔭 hhol' h0 𝔪.d
    show RestrictLe (𝔪.geoTransform ∅ π).N
      (homogenizedIdealAlong (MarkedIdeal.pullback π 𝔪).N (GermIdeal.pullback (m := n) π 𝔪.ideal) 𝔪.d)
      (homogenizedIdealAlong (𝔪.geoTransform ∅ π).N (𝔪.geoTransform ∅ π).ideal 𝔪.d)
    rw [← hW]
    exact h
  have b1 := ContactCanonicalAlong.restrictLe_geoTransform_empty_le_pullback hπ (homMarkedAlong 𝔪)
  have b2 := ContactCanonicalAlong.restrictLe_pullback_le_geoTransform (π := π) ∅ (homMarkedAlong 𝔪)
  rw [← hpb] at b1 b2
  exact ⟨rfl, rfl, rfl, DerivativeIdealAlongTransform.restrictLe_trans a1 b2,
    DerivativeIdealAlongTransform.restrictLe_trans b1 a2⟩

/-- **The marked ideal of Step 1 across a step with empty centre**: `𝓒(𝓗(𝔪')) ≃ 𝓒(𝓗(𝔪))'` for the blowup `π` along `∅`. -/
theorem restrictEquiv_barMarked_geoTransform_empty (𝔪 : MarkedIdeal n Y) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (hπ : IsBlowupAlong n (∅ : Set Y) π) :
    RestrictEquiv (coeffMarkedAlong (homMarkedAlong (𝔪.geoTransform ∅ π)))
      ((coeffMarkedAlong (homMarkedAlong 𝔪)).geoTransform ∅ π) := by
  have hc' : (𝔪.geoTransform ∅ π).ideal.IsCoherent :=
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h𝔞 (isAdmissibleCentre_empty 𝔪) hπ
  have hN' : IsClosedSubmanifold n (𝔪.geoTransform ∅ π).N :=
    isClosedSubmanifold_geoTransform_N hN (isAdmissibleCentre_empty 𝔪) hπ
  have hH := restrictEquiv_homMarkedAlong_geoTransform_empty 𝔪 hN h𝔞 hd hπ
  have hHc : (homMarkedAlong 𝔪).ideal.IsCoherent := isCoherent_homMarkedAlong h𝔞 hN
  have hHc' : (homMarkedAlong (𝔪.geoTransform ∅ π)).ideal.IsCoherent := isCoherent_homMarkedAlong hc' hN'
  have hHtc : ((homMarkedAlong 𝔪).geoTransform ∅ π).ideal.IsCoherent :=
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN hHc
      (isAdmissibleCentre_empty (homMarkedAlong 𝔪)) hπ
  have h1 := ContactCanonicalAlong.restrictEquiv_coeffMarkedAlong hH (hol_of_isCoherent hHc') (hol_of_isCoherent hHtc)
  have h2 := ContactCanonicalAlong.restrictEquiv_coeffMarkedAlong_geoTransform_empty (homMarkedAlong 𝔪) hN hHc hd hπ
  exact restrictEquiv_trans h1 h2

end OneStep

/-! ### Along a tower with only empty centres -/

section Tower

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **The strict transform of a closed set along a tower with only empty centres is its preimage.** -/
theorem strictAlong_of_isEmptyTower {A : Set X} (hA : IsClosed A) :
    ∀ {Y : CMfd.{u} n} (P : BlowupTower X Y), IsEmptyTower P → strictAlong P A = P.proj ⁻¹' A
  | _, .refl, _ => rfl
  | _, .step P C π hπ, hP => by
      obtain ⟨hP, hC⟩ : IsEmptyTower P ∧ C = ∅ := hP
      subst hC
      rw [strictAlong_step, strictAlong_of_isEmptyTower hA P hP, BlowupTower.proj_step, preimage_comp]
      exact ContactCanonicalAlong.geoStrictTransform_empty hπ.contMDiff.continuous
        (hA.preimage P.contMDiff_proj.continuous)

include 𝔍 in
/-- **The marked ideal of Step 1 along a tower with only empty centres**: `𝓒(𝓗(𝔍_P)) ≃ 𝓒(𝓗(𝔍))_P` (`N` a closed submanifold,
coherent ideal, `d ≥ 1`). -/
theorem restrictEquiv_barMarked_geoTransformAlong_of_isEmptyTower (hN : IsClosedSubmanifold n 𝔍.N)
    (h𝔞 : 𝔍.ideal.IsCoherent) (hd : 1 ≤ 𝔍.d) :
    ∀ {Y : CMfd.{u} n} (P : BlowupTower X Y), IsEmptyTower P →
      RestrictEquiv (coeffMarkedAlong (homMarkedAlong (geoTransformAlong 𝔍 P)))
        (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) P)
  | _, .refl, _ => RestrictEquiv.refl (isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN)
  | _, .step P C π hπ, hP => by
      obtain ⟨hP, hC⟩ : IsEmptyTower P ∧ C = ∅ := hP
      subst hC
      have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
      obtain ⟨hNP, hcP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 P hPt
      have hdP : 1 ≤ (geoTransformAlong 𝔍 P).d := by rw [d_geoTransformAlong]; exact hd
      have h1 := restrictEquiv_barMarked_geoTransform_empty (geoTransformAlong 𝔍 P) hNP hcP hdP hπ
      have ih := restrictEquiv_barMarked_geoTransformAlong_of_isEmptyTower hN h𝔞 hd P hP
      have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
      have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
        isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
      have hJP : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) P :=
        isGeoTestTower_of_isEmptyTower _ P hP
      obtain ⟨-, hcJP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc P hJP
      have hcbP : (coeffMarkedAlong (homMarkedAlong (geoTransformAlong 𝔍 P))).ideal.IsCoherent :=
        isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong hcP hNP) hNP
      have heq := ih.geoTransform_eq hNP.1 hcbP hcJP (C := ∅) hπ.contMDiff
      show RestrictEquiv (coeffMarkedAlong (homMarkedAlong ((geoTransformAlong 𝔍 P).geoTransform ∅ π)))
        ((geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) P).geoTransform ∅ π)
      rw [← heq]
      exact h1

/-- **Multiple test blow-ups after an empty prefix**: for a tower `P` with only empty centres, `T₀'` is a multiple test blow-up
of `𝓒(𝓗(𝔍_P))` iff `P T₀'` is one of `𝓒(𝓗(𝔍))`. -/
theorem isGeoTestTower_barMarked_geoTransformAlong_iff (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent)
    (hd : 1 ≤ 𝔍.d) {Y Y' : CMfd.{u} n} (P : BlowupTower X Y) (hP : IsEmptyTower P) (T₀' : BlowupTower Y Y') :
    IsGeoTestTower (coeffMarkedAlong (homMarkedAlong (geoTransformAlong 𝔍 P))) T₀' ↔
      IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (P.append T₀') := by
  have hJ := restrictEquiv_barMarked_geoTransformAlong_of_isEmptyTower 𝔍 hN h𝔞 hd P hP
  have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
  obtain ⟨hNP, hcP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 P hPt
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  have hJP : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) P := isGeoTestTower_of_isEmptyTower _ P hP
  obtain ⟨-, hcJP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc P hJP
  have hcbP : (coeffMarkedAlong (homMarkedAlong (geoTransformAlong 𝔍 P))).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong hcP hNP) hNP
  rw [isGeoTestTower_append_iff, ((MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hJ hNP.1 hcbP hcJP).2 T₀').1]
  exact ⟨fun h => ⟨hJP, h⟩, fun h => h.2⟩

/-- **The tangent direction across a tower with only empty centres**: if `u` is a tangent direction of `(𝔍.ideal|_N, μ)` on `U`,
then `u ∘ p_P` is one of `(𝔍_P.ideal|_{N_P}, μ)` on `p_P⁻¹U`, and `N_P ∩ V(u ∘ p_P) = p_P⁻¹(N ∩ V(u))`. -/
theorem isTangentDirectionAlong_geoTransformAlong_of_isEmptyTower (hN : IsClosedSubmanifold n 𝔍.N)
    (h𝔞 : 𝔍.ideal.IsCoherent) {μ : ℕ} {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal μ U u) :
    ∀ {Y : CMfd.{u} n} (P : BlowupTower X Y), IsEmptyTower P →
      IsTangentDirectionAlong (geoTransformAlong 𝔍 P).N (geoTransformAlong 𝔍 P).ideal μ (P.proj ⁻¹' U) (u ∘ P.proj) ∧
        (geoTransformAlong 𝔍 P).N ∩ {y | (u ∘ P.proj) y = 0} = P.proj ⁻¹' (𝔍.N ∩ {x | u x = 0})
  | _, .refl, _ => ⟨hu, rfl⟩
  | _, .step P C π hπ, hP => by
      obtain ⟨hP, hC⟩ : IsEmptyTower P ∧ C = ∅ := hP
      subst hC
      have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
      obtain ⟨hNP, hcP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 P hPt
      obtain ⟨ihu, ihN⟩ := isTangentDirectionAlong_geoTransformAlong_of_isEmptyTower hN h𝔞 hu P hP
      obtain ⟨h1, h2⟩ := ContactCanonicalAlong.isTangentDirectionAlong_geoTransform_empty (geoTransformAlong 𝔍 P) hNP.1
        (hol_of_isCoherent hcP) hπ ihu
      refine ⟨h1, ?_⟩
      show ((geoTransformAlong 𝔍 P).geoTransform ∅ π).N ∩ {z | ((u ∘ P.proj) ∘ π) z = 0} =
        π ⁻¹' (P.proj ⁻¹' (𝔍.N ∩ {x | u x = 0}))
      rw [h2, ihN]

/-- **The strict transform of `N ∩ V(u)` across a tower with only empty centres, over `U`**: for a tangent direction `u` on the
open `U`, `strictAlong P (N ∩ V(u)) ∩ p_P⁻¹U = p_P⁻¹(N ∩ V(u)) ∩ p_P⁻¹U` (`N ∩ V(u)` is closed in `U`). -/
theorem strictAlong_inter_zero_of_isEmptyTower (hN : IsClosed 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent) {μ : ℕ} {U : Opens X}
    {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal μ U u) {Y : CMfd.{u} n} (P : BlowupTower X Y)
    (hP : IsEmptyTower P) :
    strictAlong P (𝔍.N ∩ {x | u x = 0}) ∩ P.proj ⁻¹' (U : Set X) =
      P.proj ⁻¹' (𝔍.N ∩ {x | u x = 0}) ∩ P.proj ⁻¹' (U : Set X) := by
  set B : Set X := 𝔍.N ∩ closure ({x | u x = 0} ∩ (U : Set X)) with hBdef
  have hBc : IsClosed B := hN.inter isClosed_closure
  have hcont : ∀ x ∈ (U : Set X), ContinuousAt u x := fun x hx =>
    HolomorphicAt.continuousAt (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong (hol_of_isCoherent h𝔞) (μ - 1) x u
      (hu.mem x hx))
  have hAB : (𝔍.N ∩ {x | u x = 0}) ∩ (U : Set X) = B ∩ (U : Set X) := by
    ext x
    constructor
    · rintro ⟨⟨hxN, hx0⟩, hxU⟩
      exact ⟨⟨hxN, subset_closure ⟨hx0, hxU⟩⟩, hxU⟩
    · rintro ⟨⟨hxN, hxc⟩, hxU⟩
      refine ⟨⟨hxN, ?_⟩, hxU⟩
      by_contra hne
      have hev : ∀ᶠ y in 𝓝 x, u y ≠ 0 := (hcont x hxU).eventually_ne hne
      obtain ⟨y, hy, hy'⟩ := mem_closure_iff_nhds.mp hxc _ hev
      exact hy hy'.1
  have hloc := ContactEquivalenceStage.strictAlong_inter_preimage_eq U.isOpen hAB P
  rw [hloc, strictAlong_of_isEmptyTower hBc P hP, ← preimage_inter, ← preimage_inter, hAB]

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Step 1b's restricted marked ideal (divisor kept) re-based across an empty prefix of the base**: for a tower `P` with only
empty centres, a tangent direction `u` of `(𝔍.ideal|_N, d)` on `U`, a tower `T₀'` over the last stage of `P` such that `P T₀'` is a
multiple test blow-up of `J̄ = 𝓒(𝓗(𝔍))`, and an open `W` of the last stage over `U`: the marked ideal formed from `𝔍_P` with
`u ∘ p_P` along `T₀'` is restricted-equivalent to the one formed from `𝔍` with `u` along `P T₀'`. -/
theorem restrictEquiv_contactMarkedKept_emptyPrefix (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent)
    (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y Y' : CMfd.{u} n}
    (P : BlowupTower X Y) (hP : IsEmptyTower P) (T₀' : BlowupTower Y Y')
    (hT : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (P.append T₀')) (W : Opens Y')
    (hWU : (W : Set Y') ⊆ openPreimage (P.append T₀') U) :
    RestrictEquiv (contactMarkedKept (geoTransformAlong 𝔍 P) (u ∘ P.proj) T₀' W)
      (contactMarkedKept 𝔍 u (P.append T₀') W) := by
  have hJ := restrictEquiv_barMarked_geoTransformAlong_of_isEmptyTower 𝔍 hN h𝔞 hd P hP
  have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
  obtain ⟨hNP, hcP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 P hPt
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  have hJP : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) P := isGeoTestTower_of_isEmptyTower _ P hP
  obtain ⟨hNJP, hcJP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc P hJP
  have hcbP : (coeffMarkedAlong (homMarkedAlong (geoTransformAlong 𝔍 P))).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong hcP hNP) hNP
  have hT₀' : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong (geoTransformAlong 𝔍 P))) T₀' :=
    (isGeoTestTower_barMarked_geoTransformAlong_iff 𝔍 hN h𝔞 hd P hP T₀').mpr hT
  have hT₀'J : IsGeoTestTower (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) P) T₀' :=
    ((isGeoTestTower_append_iff _ P T₀').mp hT).2
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (𝔪 := coeffMarkedAlong (homMarkedAlong (geoTransformAlong 𝔍 P))) hNP hcbP T₀' hT₀'
  obtain ⟨hNT', hcT'⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hNJP hcJP T₀' hT₀'J
  -- the sets `N_P ∩ V(u ∘ p_P)` and `strictAlong P (N ∩ V(u))` agree over `p_P⁻¹U`
  set A : Set Y := (geoTransformAlong 𝔍 P).N ∩ {y | (u ∘ P.proj) y = 0} with hAdef
  have hAN : A ⊆ (coeffMarkedAlong (homMarkedAlong (geoTransformAlong 𝔍 P))).N := fun y hy => hy.1
  have hK := ContactCanonicalAlong.restrictEquiv_restrictedCoeff_geoTransformAlong hJ hNP.1 hcbP hcJP hAN T₀'
  have hP' := ContactRepresentative.restrictEquiv_pullback_val W hK (isCoherent_coeffMarkedAlong hcT hNT)
    (isCoherent_coeffMarkedAlong hcT' hNT')
  have hAO : A ∩ P.proj ⁻¹' (U : Set X) = strictAlong P (𝔍.N ∩ {x | u x = 0}) ∩ P.proj ⁻¹' (U : Set X) := by
    rw [hAdef, (isTangentDirectionAlong_geoTransformAlong_of_isEmptyTower 𝔍 hN h𝔞 hu P hP).2,
      strictAlong_inter_zero_of_isEmptyTower 𝔍 hN.1 h𝔞 hu P hP]
  have hloc := ContactEquivalenceStage.strictAlong_inter_preimage_eq
    ((U.isOpen).preimage P.contMDiff_proj.continuous) hAO T₀'
  have hset : (Subtype.val : W → Y') ⁻¹' strictAlong T₀' A =
      (Subtype.val : W → Y') ⁻¹' strictAlong T₀' (strictAlong P (𝔍.N ∩ {x | u x = 0})) := by
    ext p
    have hp : (p : Y') ∈ T₀'.proj ⁻¹' (P.proj ⁻¹' (U : Set X)) := by
      have h := hWU p.2
      rw [← BlowupTowerIsoTail.openPreimage_append] at h
      exact h
    constructor
    · intro h
      have h1 : (p : Y') ∈ strictAlong T₀' A ∩ T₀'.proj ⁻¹' (P.proj ⁻¹' (U : Set X)) := ⟨h, hp⟩
      rw [hloc] at h1
      exact h1.1
    · intro h
      have h1 : (p : Y') ∈ strictAlong T₀' (strictAlong P (𝔍.N ∩ {x | u x = 0})) ∩
          T₀'.proj ⁻¹' (P.proj ⁻¹' (U : Set X)) := ⟨h, hp⟩
      rw [← hloc] at h1
      exact h1.1
  show RestrictEquiv (MarkedIdeal.pullback (Subtype.val : W → Y')
      (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong (geoTransformAlong 𝔍 P))) T₀'))
        (strictAlong T₀' A)))
    (MarkedIdeal.pullback (Subtype.val : W → Y')
      (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) (P.append T₀')))
        (strictAlong (P.append T₀') (𝔍.N ∩ {x | u x = 0}))))
  rw [geoTransformAlong_append, MemberInterLocusAlong.strictAlong_append, ContactCanonicalAlong.pullback_withN,
    ContactCanonicalAlong.pullback_withN (Subtype.val : W → Y')
      (coeffMarkedAlong (geoTransformAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) P) T₀')),
    ← hset, ← ContactCanonicalAlong.pullback_withN, ← ContactCanonicalAlong.pullback_withN]
  exact hP'

/-- **Step 1b's values (divisor kept) re-based across an empty prefix of the base** (the Step 1bb input of property (4')): in
the situation of `restrictEquiv_contactMarkedKept_emptyPrefix`, if `contactMarkedKept 𝔍 u (P T₀') W` lies in the domain of a
resolution invariant `R`, so does `contactMarkedKept 𝔍_P (u ∘ p_P) T₀' W`, the two have the same canonical segments, and along
them `R` takes the same values on the cosupport. -/
theorem contactMarkedKept_emptyPrefix (R : ResolutionInvariant.{u, v} n k Λ) (hN : IsClosedSubmanifold n 𝔍.N)
    (h𝔞 : 𝔍.ideal.IsCoherent) (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y Y' : CMfd.{u} n} (P : BlowupTower X Y) (hP : IsEmptyTower P)
    (T₀' : BlowupTower Y Y') (hT : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (P.append T₀')) (W : Opens Y')
    (hWU : (W : Set Y') ⊆ openPreimage (P.append T₀') U)
    (hdom : IsInvDomain k (contactMarkedKept 𝔍 u (P.append T₀') W)) :
    IsInvDomain k (contactMarkedKept (geoTransformAlong 𝔍 P) (u ∘ P.proj) T₀' W) ∧
      ∀ {Z : CMfd.{u} n} (T₁ : BlowupTower (CMfd.of (n := n) W) Z),
        IsCanonical (contactMarkedKept 𝔍 u (P.append T₀') W) (R.inv (contactMarkedKept 𝔍 u (P.append T₀') W)) T₁ →
        IsCanonical (contactMarkedKept (geoTransformAlong 𝔍 P) (u ∘ P.proj) T₀' W)
          (R.inv (contactMarkedKept (geoTransformAlong 𝔍 P) (u ∘ P.proj) T₀' W)) T₁ ∧
        ∀ z ∈ (geoTransformAlong (contactMarkedKept 𝔍 u (P.append T₀') W) T₁).cosupp,
          R.inv (contactMarkedKept 𝔍 u (P.append T₀') W) T₁ z =
            R.inv (contactMarkedKept (geoTransformAlong 𝔍 P) (u ∘ P.proj) T₀' W) T₁ z := by
  have hE := InvDomainRebase.restrictEquiv_symm
    (restrictEquiv_contactMarkedKept_emptyPrefix 𝔍 hN h𝔞 hd U hu P hP T₀' hT W hWU)
  have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
  obtain ⟨hNP, hcP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 P hPt
  have hT₀' : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong (geoTransformAlong 𝔍 P))) T₀' :=
    (isGeoTestTower_barMarked_geoTransformAlong_iff 𝔍 hN h𝔞 hd P hP T₀').mpr hT
  have hc' : (contactMarkedKept (geoTransformAlong 𝔍 P) (u ∘ P.proj) T₀' W).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff (geoTransformAlong 𝔍 P) hcP hNP (u ∘ P.proj) T₀' hT₀')
  have hdom' := InvDomainRebase.isInvDomain_of_restrictEquiv hdom hE hc'
  refine ⟨hdom', fun T₁ hcan => ⟨InvDomainRebase.isCanonical_of_restrictEquiv R hdom hdom' hE T₁ hcan, fun z hz => ?_⟩⟩
  exact R.representative _ _ hdom hdom' hE T₁ hcan z hz

end Tower

end

end Hironaka.ContactEmptyPrefix
