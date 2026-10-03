/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ContactEquivalenceAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.MarkedIdeal.TransformOffCentre
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestrictionFull
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
import Hironaka.MarkedIdeal.DerivativeIdealAlongTransform
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictLe
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Canonicity of the coefficient ideals along `N` and of their restrictions, along multiple test blow-ups

Source: Włodarczyk 2005 (arXiv `hiron.tex`), the unlabelled lemma "Commutativity of the resolution procedure in Step
1 with étale morphisms" in the proof of Proposition `pr: resol`: its items (2)--(3), `φ^*(J̄_{i|H^s_α}) =
J̄'_{j|(H')^s_α}` and `J̄'_{|V(u)} = φ^*(J̄_{|V(u)})`, and its item (1), along which blow-ups whose centres miss the
image pull back to isomorphisms; with Proposition `pr: funct` (multiple test blow-ups pull back along smooth
morphisms) and `pr: resol` (4). Here étale maps are open embeddings and biholomorphisms, and the induced
isomorphisms are steps with empty centre.

Notation: `𝔪_T = geoTransformAlong 𝔪 T`; `A_T = strictAlong T A`; `S_A(𝔪_T) = withN (coeffMarkedAlong 𝔪_T) A_T`, the
coefficient ideal along `N_T` restricted to the strict transform of `A ⊆ N` (`A = N ∩ H_S` in Step 1a,
`A = N ∩ V(u)` in Step 1b).  Standing hypotheses on `𝔪`: `N` a closed submanifold, coherent ideal, `d ≥ 1`, `T` a multiple
test blow-up.

## (K4) Representatives

* `restrictLe_iterDerivIdealAlong`, `restrictLe_coeffMarkedAlong`: `𝔞|_N ⊆ 𝔟|_N` gives `𝓓_N^i(𝔞)|_N ⊆ 𝓓_N^i(𝔟)|_N`
  and `𝓒_N(𝔞)|_N ⊆ 𝓒_N(𝔟)|_N`; `restrictEquiv_coeffMarkedAlong`, `restrictEquiv_withN`: `𝔪 ≃ 𝔫` (`RestrictEquiv`)
  gives `𝓒_N(𝔪) ≃ 𝓒_N(𝔫)` and `S_A(𝔪) ≃ S_A(𝔫)` for `A ⊆ N`.
* `restrictEquiv_coeffMarkedAlong_geoTransformAlong`, `restrictEquiv_restrictedCoeff_geoTransformAlong`: the same at every
  stage of every tower (from the first blowup on the transforms are equal).

## Restriction, dropping members and pullbacks

* `pullback_withN`, `pullback_id`: `φ^*(𝔟|_S) = (φ^*𝔟)|_{φ⁻¹S}`, dropping members commutes with pullback, `id^*𝔪 =
  𝔪`.

## (K1) Transported towers (property (6))

## (K2) Restricted towers (property (5))

* `coeffMarkedAlong_geoTransformAlong_restrict`, **`restrictedCoeff_geoTransformAlong_restrict`**: `S_{A ∩
  U}((𝔪|_U)_{T|_U}) = S_A(𝔪_T)|_{T⁻¹U}`.

## (K3) Steps with empty centre (property (4))

* `exists_isLocalInverseAt_of_isBlowupAlong_empty`: a blowup along `∅` is a local biholomorphism at every point;
  `geoStrictTransform_empty`: the strict transform of a closed set is its preimage;
  `restrictLe_geoTransform_empty_le_pullback`, `restrictLe_pullback_le_geoTransform`: along `∅` the transform is the
  pullback on `N'` up to restricted equivalence.
* `restrictEquiv_coeffMarkedAlong_geoTransform_empty`: `𝓒_{N'}(𝔪') ≃ 𝓒_N(𝔪)'`;
  **`restrictEquiv_restrictedCoeff_geoTransform_empty`**: `𝓒_{N'}(𝔪')|_{A'} ≃ (𝓒_N(𝔪)|_A)'` (restricting at the new
  stage or transforming the old restriction); `restrictEquiv_restrictedCoeff_geoTransformAlong_empty`: the form
  along a tower, `S_A(𝔪_{T·π}) ≃ S_A(𝔪_T)'`.

## (K5) Tangent directions
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ContactCanonicalAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder IdealWeightPowers RestrictedIdealWeight DerivativeIdealAlong DerivativeIdealAlongEtale DerivativeIdealAlongTransform HomogenizedGlueing HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdeal CoefficientIdealRestriction MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms MarkedIdealBiholomorphism MarkedIdealTowerTransport MarkedIdealRestrictOpen BlowupStrictSubmanifold TangentDirectionAlong
open HomogenizedGlueingTower (strictAlong strictAlong_step strictAlong_restrict N_geoTransformAlong)

noncomputable section

variable {n : ℕ}

/-! ### (K4) Representatives -/

section Representatives

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Derivatives along `W` respect restricted inclusions on `W`**, iterated: `𝔞|_W ⊆ 𝔟|_W` gives
`𝓓_W^i(𝔞)|_W ⊆ 𝓓_W^i(𝔟)|_W`. -/
theorem restrictLe_iterDerivIdealAlong {W : Set M} {𝔞 𝔟 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x)
    (h : RestrictLe W 𝔞 𝔟) : ∀ i, RestrictLe W (iterDerivIdealAlong W 𝔞 i) (iterDerivIdealAlong W 𝔟 i)
  | 0 => h
  | i + 1 => restrictLe_derivIdealAlong (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 i)
      (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔟 i) (restrictLe_iterDerivIdealAlong h𝔞 h𝔟 h i)

/-- **The coefficient ideal along `N` respects restricted inclusions on `N`**: for two marked ideals with the same `N` and
the same mark, `𝔞|_N ⊆ 𝔟|_N` gives `𝓒_N(𝔞)|_N ⊆ 𝓒_N(𝔟)|_N`. -/
theorem restrictLe_coeffMarkedAlong {𝔪 𝔫 : MarkedIdeal n M} (hN : 𝔪.N = 𝔫.N) (hd : 𝔪.d = 𝔫.d)
    (h𝔪 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (h𝔫 : ∀ x g, 𝔫.ideal.mem x g → HolomorphicAt n g x)
    (h : RestrictLe 𝔪.N 𝔪.ideal 𝔫.ideal) :
    RestrictLe 𝔪.N (coeffMarkedAlong 𝔪).ideal (coeffMarkedAlong 𝔫).ideal := by
  show RestrictLe 𝔪.N (finSumIdeal (fun i => idealPow (iterDerivIdealAlong 𝔪.N 𝔪.ideal i)
      (sumExp (fun j => 𝔪.d - j) 𝔪.d i)) 𝔪.d)
    (finSumIdeal (fun i => idealPow (iterDerivIdealAlong 𝔫.N 𝔫.ideal i) (sumExp (fun j => 𝔫.d - j) 𝔫.d i)) 𝔫.d)
  rw [← hN, ← hd]
  refine restrictLe_finSumIdeal (fun i _ _ _ hg => holomorphicAt_of_mem_idealPow hg) fun i _ => ?_
  exact restrictLe_idealPow (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong h𝔫 i)
    (restrictLe_iterDerivIdealAlong h𝔪 h𝔫 h i) _

/-- **Restricted-equivalent marked ideals have restricted-equivalent coefficient ideals along `N`**. -/
theorem restrictEquiv_coeffMarkedAlong {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫)
    (h𝔪 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (h𝔫 : ∀ x g, 𝔫.ideal.mem x g → HolomorphicAt n g x) :
    RestrictEquiv (coeffMarkedAlong 𝔪) (coeffMarkedAlong 𝔫) where
  N_eq := h.N_eq
  E_eq := h.E_eq
  d_eq := by
    show ((Finset.range 𝔪.d).prod fun j => 𝔪.d - j) = (Finset.range 𝔫.d).prod fun j => 𝔫.d - j
    rw [h.d_eq]
  le := restrictLe_coeffMarkedAlong h.N_eq h.d_eq h𝔪 h𝔫 h.le
  ge := by
    have := restrictLe_coeffMarkedAlong h.N_eq.symm h.d_eq.symm h𝔫 h𝔪 (h.N_eq ▸ h.ge)
    exact h.N_eq ▸ this

/-- **Restricted equivalence restricts to subsets of `N`**: `𝔪 ≃ 𝔫` gives `𝔪|_A ≃ 𝔫|_A` for `A ⊆ N`. -/
theorem restrictEquiv_withN {𝔪 𝔫 : MarkedIdeal n M} (h : RestrictEquiv 𝔪 𝔫) {A : Set M} (hA : A ⊆ 𝔪.N) :
    RestrictEquiv (withN 𝔪 A) (withN 𝔫 A) :=
  ⟨rfl, h.E_eq, h.d_eq, restrictLe_mono hA h.le, restrictLe_mono hA h.ge⟩

end Representatives

section RepresentativesTower

variable {X : CMfd.{u} n} {𝔪 𝔫 : MarkedIdeal n X}

/-- A marked ideal whose germs are holomorphic is restricted-equivalent to itself. -/
theorem restrictEquiv_self (𝔟 : MarkedIdeal n X) (h𝔟 : ∀ x g, 𝔟.ideal.mem x g → HolomorphicAt n g x) :
    RestrictEquiv 𝔟 𝔟 :=
  ⟨rfl, rfl, rfl, restrictLe_refl h𝔟, restrictLe_refl h𝔟⟩

/-- **(K4) along every tower**: restricted-equivalent marked ideals (closed `N`, coherent ideals) have, at every stage of
every tower, restricted-equivalent coefficient ideals along `N_T` (from the first blowup on the transforms are equal). -/
theorem restrictEquiv_coeffMarkedAlong_geoTransformAlong (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      RestrictEquiv (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (coeffMarkedAlong (geoTransformAlong 𝔫 T))
  | _, .refl => restrictEquiv_coeffMarkedAlong h (hol_of_isCoherent h𝔪) (hol_of_isCoherent h𝔫)
  | _, .step T C π hπ => by
      rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq h hN h𝔪 h𝔫 T C π hπ]
      exact restrictEquiv_self _ fun _ _ hg => hg.1

/-- **(K4) for the restricted coefficient ideals along every tower**: for `A ⊆ N`, at every stage `T`,
`𝓒_{N_T}(𝔪_T)|_{A_T} ≃ 𝓒_{N_T}(𝔫_T)|_{A_T}` (`A_T` the strict transform of `A`). -/
theorem restrictEquiv_restrictedCoeff_geoTransformAlong (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) {A : Set X} (hA : A ⊆ 𝔪.N) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) :
    RestrictEquiv (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A))
      (withN (coeffMarkedAlong (geoTransformAlong 𝔫 T)) (strictAlong T A)) := by
  refine restrictEquiv_withN (restrictEquiv_coeffMarkedAlong_geoTransformAlong h hN h𝔪 h𝔫 T) ?_
  show strictAlong T A ⊆ (geoTransformAlong 𝔪 T).N
  rw [N_geoTransformAlong]
  exact MemberInterTowerAlong.strictAlong_mono T hA

end RepresentativesTower

/-! ### Restrictions to sets and pullbacks -/

section Pullback

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **Restriction to a set commutes with pullback**: `φ^*(𝔟|_S) = (φ^*𝔟)|_{φ⁻¹S}`. -/
theorem pullback_withN (φ : M' → M) (𝔟 : MarkedIdeal n M) (S : Set M) :
    MarkedIdeal.pullback φ (withN 𝔟 S) = withN (MarkedIdeal.pullback φ 𝔟) (φ ⁻¹' S) :=
  rfl

/-- The pullback along the identity of a marked ideal with coherent ideal is the marked ideal. -/
theorem pullback_id (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent) : MarkedIdeal.pullback (id : M → M) 𝔪 = 𝔪 :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl
    (show List.map (fun s => (id : M → M) ⁻¹' s) 𝔪.E = 𝔪.E by simp) (BlowupControlledTransform.pullback_id h𝔞) rfl

end Pullback

/-! ### (K2) Restricted towers -/

section Restrict

variable {X : CMfd.{u} n} (U : Opens X) {𝔪 : MarkedIdeal n X}

/-- **(K2) The coefficient ideal along `N_T` along restricted towers**:
`𝓒((𝔪|_U)_{T|_U}) = 𝓒(𝔪_T)|_{T⁻¹U}`. -/
theorem coeffMarkedAlong_geoTransformAlong_restrict (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    coeffMarkedAlong (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (coeffMarkedAlong (geoTransformAlong 𝔪 T)) := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  rw [geoTransformAlong_restrict U hN h𝔞 T hT,
    pullback_val_coeffMarkedAlong (openPreimage T U) _ hcT hNT (by rwa [d_geoTransformAlong])]

/-- **(K2) The restricted coefficient ideals along restricted towers** (property (5) for Steps 1a/1b inside `N`):
`S_{A ∩ U}((𝔪|_U)_{T|_U}) = S_A(𝔪_T)|_{T⁻¹U}`. -/
theorem restrictedCoeff_geoTransformAlong_restrict (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (A : Set X) :
    withN (coeffMarkedAlong (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)))
        (strictAlong (restrict U T) ((↑) ⁻¹' A : Set U)) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A)) := by
  rw [coeffMarkedAlong_geoTransformAlong_restrict U hN h𝔞 hd T hT, strictAlong_restrict U T A]
  rfl

end Restrict

/-! ### (K3) Steps with empty centre -/

section EmptyStep

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {π : Z → Y}

/-- **A blowup along `∅` is a local biholomorphism at every point**: its holomorphic section over the complement of the
centre (`BlowupIsomorphismOff.exists_section_compl`) is a global inverse. -/
theorem exists_isLocalInverseAt_of_isBlowupAlong_empty (hπ : IsBlowupAlong n (∅ : Set Y) π) (z : Z) :
    ∃ ψ : Y → Z, IsLocalInverseAt n π ψ z := by
  obtain ⟨s, hs, hsπ, hsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hmem : ∀ y : Y, y ∈ (⟨(∅ : Set Y)ᶜ, hπ.1.1.isOpen_compl⟩ : Opens Y) := fun y => notMem_empty y
  set y₀ : (⟨(∅ : Set Y)ᶜ, hπ.1.1.isOpen_compl⟩ : Opens Y) := ⟨π z, hmem _⟩ with hy₀
  have hinv := isLocalInverseAt_val (n := n) (⟨(∅ : Set Y)ᶜ, hπ.1.1.isOpen_compl⟩ : Opens Y) y₀
  have hopen : ∀ q : Y, openInv (⟨(∅ : Set Y)ᶜ, hπ.1.1.isOpen_compl⟩ : Opens Y) y₀ q = ⟨q, hmem q⟩ := fun q => by
    simp [openInv]
  refine ⟨s ∘ openInv (⟨(∅ : Set Y)ᶜ, hπ.1.1.isOpen_compl⟩ : Opens Y) y₀,
    ⟨Eventually.of_forall fun p => (hπ.contMDiff p).mdifferentiableAt (by simp), ?_, ?_, ?_⟩⟩
  · have h := hinv.mdiff_inv
    filter_upwards [h] with q hq
    exact ((hs _).mdifferentiableAt (by simp)).comp q hq
  · exact Eventually.of_forall fun p => by
      simp only [Function.comp_apply, hopen]
      exact hsec p (hmem _)
  · exact Eventually.of_forall fun q => by
      simp only [Function.comp_apply, hopen]
      exact congrFun hsπ ⟨q, hmem q⟩

/-- **The strict transform of a closed set along an empty centre is its preimage.** -/
theorem geoStrictTransform_empty (hπc : Continuous π) {A : Set Y} (hA : IsClosed A) :
    geoStrictTransform π (∅ : Set Y) A = π ⁻¹' A := by
  rw [geoStrictTransform, sdiff_empty, (hA.preimage hπc).closure_eq]

/-- **Along an empty centre the transform lies in the pullback on `N'`**: `Res_{N'} 𝔞' ⊆ Res_{N'} π^*𝔞`. -/
theorem restrictLe_geoTransform_empty_le_pullback (hπ : IsBlowupAlong n (∅ : Set Y) π) (𝔫 : MarkedIdeal n Y) :
    RestrictLe (𝔫.geoTransform ∅ π).N (𝔫.geoTransform ∅ π).ideal (GermIdeal.pullback (m := n) π 𝔫.ideal) :=
  fun _ _ _ hf =>
    CoefficientIdealAlongRestrictionFull.isInSpanOnAt_pullback_of_mem_geoTransform_of_notMem hπ 𝔫 (notMem_empty _) hf

/-- **The pullback lies in the transform**, restricted form: `Res_{N'} π^*𝔞 ⊆ Res_{N'} 𝔞'` (any centre). -/
theorem restrictLe_pullback_le_geoTransform (C : Set Y) (𝔫 : MarkedIdeal n Y) :
    RestrictLe (𝔫.geoTransform C π).N (GermIdeal.pullback (m := n) π 𝔫.ideal) (𝔫.geoTransform C π).ideal :=
  fun _ _ _ hG => RelativePrincipalizationSpan.IsInSpanAt.restrict
    (InvertibleIdealQuotient.isInSpanAt_self
      (CoefficientIdealAlongRestrictionFull.mem_geoTransform_of_mem_pullback 𝔫 hG) (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hG).1)

/-- **(K3) The coefficient ideal along `N` is unchanged by a step with empty centre**: for the blowup `π` along `∅`,
`𝓒_{N'}(𝔪') ≃ 𝓒_N(𝔪)'` (`N` a closed submanifold, coherent ideal, `d ≥ 1`).  Both are restricted-equivalent on
`N' = π⁻¹N` to `π^*𝓒_N(𝔪) = 𝓒_{π⁻¹N}(π^*𝔪)` (`π` is a biholomorphism). -/
theorem restrictEquiv_coeffMarkedAlong_geoTransform_empty (𝔪 : MarkedIdeal n Y) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (hπ : IsBlowupAlong n (∅ : Set Y) π) :
    RestrictEquiv (coeffMarkedAlong (𝔪.geoTransform ∅ π)) ((coeffMarkedAlong 𝔪).geoTransform ∅ π) := by
  have hloc := exists_isLocalInverseAt_of_isBlowupAlong_empty hπ
  have hW : (𝔪.geoTransform ∅ π).N = (MarkedIdeal.pullback π 𝔪).N :=
    geoStrictTransform_empty hπ.contMDiff.continuous hN.1
  have hpb : (coeffMarkedAlong (MarkedIdeal.pullback π 𝔪)).ideal =
      GermIdeal.pullback (m := n) π (coeffMarkedAlong 𝔪).ideal :=
    (congrArg MarkedIdeal.ideal (pullback_coeffMarkedAlong hπ.contMDiff hloc 𝔪 h𝔞 hN hd)).symm
  have hhol𝔭 : ∀ x g, (MarkedIdeal.pullback π 𝔪).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg).1
  have hhol' : ∀ x g, (𝔪.geoTransform ∅ π).ideal.mem x g → HolomorphicAt n g x :=
    hol_of_isCoherent (HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h𝔞
      (isAdmissibleCentre_empty 𝔪) hπ)
  have a1 : RestrictLe (𝔪.geoTransform ∅ π).N (coeffMarkedAlong (𝔪.geoTransform ∅ π)).ideal
      (coeffMarkedAlong (MarkedIdeal.pullback π 𝔪)).ideal :=
    restrictLe_coeffMarkedAlong hW rfl hhol' hhol𝔭 (restrictLe_geoTransform_empty_le_pullback hπ 𝔪)
  have a2 : RestrictLe (𝔪.geoTransform ∅ π).N (coeffMarkedAlong (MarkedIdeal.pullback π 𝔪)).ideal
      (coeffMarkedAlong (𝔪.geoTransform ∅ π)).ideal := by
    have h0 : RestrictLe (MarkedIdeal.pullback π 𝔪).N (MarkedIdeal.pullback π 𝔪).ideal (𝔪.geoTransform ∅ π).ideal := by
      rw [← hW]
      exact restrictLe_pullback_le_geoTransform (π := π) ∅ 𝔪
    have := restrictLe_coeffMarkedAlong hW.symm rfl hhol𝔭 hhol' h0
    rwa [← hW] at this
  have b1 := restrictLe_geoTransform_empty_le_pullback hπ (coeffMarkedAlong 𝔪)
  have b2 := restrictLe_pullback_le_geoTransform (π := π) ∅ (coeffMarkedAlong 𝔪)
  rw [← hpb] at b1 b2
  exact ⟨rfl, rfl, rfl, restrictLe_trans a1 b2, restrictLe_trans b1 a2⟩

/-- **(K3) The restricted coefficient ideal is unchanged by a step with empty centre**: for `A ⊆ N` and the blowup `π`
along `∅`, `𝓒_{N'}(𝔪')|_{A'} ≃ (𝓒_N(𝔪)|_A)'` (`A'` the strict transform of `A`); restricting at the new stage or
transforming the old restriction gives restricted-equivalent marked ideals. -/
theorem restrictEquiv_restrictedCoeff_geoTransform_empty (𝔪 : MarkedIdeal n Y) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (hπ : IsBlowupAlong n (∅ : Set Y) π) {A : Set Y} (hA : A ⊆ 𝔪.N) :
    RestrictEquiv (withN (coeffMarkedAlong (𝔪.geoTransform ∅ π)) (geoStrictTransform π ∅ A))
      ((withN (coeffMarkedAlong 𝔪) A).geoTransform ∅ π) := by
  have hK := restrictEquiv_coeffMarkedAlong_geoTransform_empty 𝔪 hN h𝔞 hd hπ
  have hA' : geoStrictTransform π ∅ A ⊆ (𝔪.geoTransform ∅ π).N :=
    closure_mono (preimage_mono (sdiff_subset_sdiff_left hA))
  have b1 := restrictLe_geoTransform_empty_le_pullback hπ (coeffMarkedAlong 𝔪)
  have b2 := restrictLe_pullback_le_geoTransform (π := π) ∅ (coeffMarkedAlong 𝔪)
  have c1 := restrictLe_geoTransform_empty_le_pullback hπ (withN (coeffMarkedAlong 𝔪) A)
  have c2 := restrictLe_pullback_le_geoTransform (π := π) ∅ (withN (coeffMarkedAlong 𝔪) A)
  exact ⟨rfl, rfl, rfl, restrictLe_trans (restrictLe_mono hA' (restrictLe_trans hK.le b1)) c2,
    restrictLe_trans c1 (restrictLe_mono hA' (restrictLe_trans b2 hK.ge))⟩

end EmptyStep

section EmptyStepTower

variable {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}

/-- **(K3) along a tower**: for a multiple test blow-up `T` of `𝔪` followed by a blowup `π` along `∅` and `A ⊆ N`,
`S_A(𝔪_{T·π}) ≃ S_A(𝔪_T)'`, `S_A(𝔪_T) = 𝓒_{N_T}(𝔪_T)|_{A_T}`. -/
theorem restrictEquiv_restrictedCoeff_geoTransformAlong_empty (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    (π : Z → Y) (hπ : IsBlowupAlong n (∅ : Set Y) π) {A : Set X} (hA : A ⊆ 𝔪.N) :
    RestrictEquiv (withN (coeffMarkedAlong (geoTransformAlong 𝔪 (.step T ∅ π hπ))) (strictAlong (.step T ∅ π hπ) A))
      ((withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A)).geoTransform ∅ π) := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  have hAT : strictAlong T A ⊆ (geoTransformAlong 𝔪 T).N := by
    rw [N_geoTransformAlong]
    exact MemberInterTowerAlong.strictAlong_mono T hA
  exact restrictEquiv_restrictedCoeff_geoTransform_empty _ hNT hcT (by rwa [d_geoTransformAlong]) hπ hAT

end EmptyStepTower

/-! ### (K5) Tangent directions along towers -/

section Tangent

/-- Iterated derivative ideals along `N` are monotone in the ideal. -/
theorem iterDerivIdealAlong_le {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {N : Set M} {𝔞 𝔟 : GermIdeal n M} (h : 𝔞.Le 𝔟) :
    ∀ j, (iterDerivIdealAlong N 𝔞 j).Le (iterDerivIdealAlong N 𝔟 j)
  | 0 => h
  | j + 1 => derivIdealAlong_mono (iterDerivIdealAlong_le h j)

end Tangent

section TangentEmpty

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {π : Z → Y}

/-- **(K5) Tangent directions across a step with empty centre**: for the blowup `π` along `∅`, if `u` is a tangent
direction of `(𝔪|_N, d')` on `V` (any mark `d'`), then `u ∘ π` is one of `(𝔪'|_{N'}, d')` on `π⁻¹V` (`N` closed, ideal of
holomorphic germs); and `N' ∩ V(u ∘ π) = π⁻¹(N ∩ V(u))`. -/
theorem isTangentDirectionAlong_geoTransform_empty (𝔪 : MarkedIdeal n Y) (hN : IsClosed 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hπ : IsBlowupAlong n (∅ : Set Y) π) {μ : ℕ} {V : Set Y}
    {u : Y → ℂ} (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal μ V u) :
    IsTangentDirectionAlong (𝔪.geoTransform ∅ π).N (𝔪.geoTransform ∅ π).ideal μ (π ⁻¹' V) (u ∘ π) ∧
      (𝔪.geoTransform ∅ π).N ∩ {z | (u ∘ π) z = 0} = π ⁻¹' (𝔪.N ∩ {y | u y = 0}) := by
  have hP := ContactEquivalenceAlong.isTangentDirectionAlong_pullback
    (exists_isLocalInverseAt_of_isBlowupAlong_empty hπ) h𝔞 hu
  have hW : (𝔪.geoTransform ∅ π).N = π ⁻¹' 𝔪.N := geoStrictTransform_empty hπ.contMDiff.continuous hN
  have hle : (GermIdeal.pullback (m := n) π 𝔪.ideal).Le (𝔪.geoTransform ∅ π).ideal := fun _ _ hG =>
    CoefficientIdealAlongRestrictionFull.mem_geoTransform_of_mem_pullback 𝔪 hG
  rw [hW]
  exact ⟨⟨hP.isOpen, fun x hx => iterDerivIdealAlong_le hle (μ - 1) x _ (hP.mem x hx), hP.multiplicity_one⟩, rfl⟩

end TangentEmpty

end

end Hironaka.ContactCanonicalAlong
