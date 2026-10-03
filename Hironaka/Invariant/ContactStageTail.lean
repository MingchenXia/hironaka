/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ContactStageInvDomain
import Hironaka.Invariant.MaximalOrderStepOneB
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestrictionFull
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.MarkedIdeal.MaximalContactAlongTower
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The tails of Step 1b on open sets smaller than `T₀⁻¹U`

"the lower-dimensional invariant is that of the marked ideal formed at the last stage of `T₀` (`𝓢_w`), restricted to
a neighbourhood `W` of the image of `x` meeting no other original member, along `T₁|_W`". Source: Włodarczyk 2005
(arXiv `hiron.tex`), Step 1bb ("By Lemma `le:codim2`, `(V(u)_i)_{0 ≤ i ≤ p}` is a multiple test blow-up of `(V(u),
J̄|_{V(u)}, ∅, μ̄)`"), with Lemma `le:S`.

An equivalence of marked ideals (`MarkedIdealEquivalence.WEquiv`) quantifies over the towers of its own base, so it does not
pass from `T₀⁻¹U` to a smaller open `W` (a tower over `W` need not extend).  The results here are therefore proved for the
given segment only, from Giraud's lemma along the **global** towers `T₀ T` over the base (`cosupp_tail_subset_strictAlong`)
and Lemma `le:S` on `W`.

## Main results

* `isGeoTestTower_restrict_withN_coeff_of_cosupp_subset` (generic): for a marked ideal `𝔫` on `Y`, an open `W ⊆ Y` and
  `A ⊆ N` with `A ∩ W` a closed submanifold of `W`, if along every multiple test blow-up `T` of `𝔫` the cosupport over `W`
  lies in the strict transform of `A`, then for every multiple test blow-up `T₁` of `𝔫` the restriction `T₁|_W` is one of
  `(𝓒_N(𝔫)|_A)|_W`, and along it the cosupport is the trace of `cosupp 𝔫_{T₁}`.
* `cosupp_tail_subset_strictAlong` (**Giraud at the stage `T₀` along the tails**): for `J̄ = 𝓒_N(𝓗_N(𝔍))` (any divisor),
  a tangent direction `u` of `(𝔍.ideal|_N, d)` along `N` on `U` and a multiple test blow-up `T₀ T` of `J̄`, the cosupport of
  `J̄_{T₀ T}` over `T₀⁻¹U` lies in the strict transform along `T` of `S_{T₀} = (N ∩ V(u))_{T₀}`.
* `isGeoTestTower_tail_coeffHomAlong_of_le` (**the tails on `W`**, any divisor): for `T₀ T₁` a multiple test blow-up of `J̄`
  and an open `W ⊆ T₀⁻¹U`, `T₁|_W` is a multiple test blow-up of `𝓢_{u,T₀}|_W = (𝓒_{N_{T₀}}(J̄_{T₀})|_{S_{T₀}})|_W`, with
  cosupport the trace of `cosupp J̄_{T₀ T₁}`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ContactStageTail

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower MarkedIdealBiholomorphism MarkedIdealRestrictOpen MemberInterTowerAlong MaximalContactAlongTower CoefficientIdealAlongRestrictionFull
open HomogenizedGlueingTower (strictAlong strictAlong_restrict)
open MemberInterLocusAlong (strictAlong_append)
open ContactIndependenceAlong (one_le_coeffMarkedAlong_d)

noncomputable section

variable {n : ℕ}

/-! ### The generic form -/

section Generic

variable {Y : CMfd.{u} n} (𝔫 : MarkedIdeal n Y) (hN : IsClosedSubmanifold n 𝔫.N) (h𝔞 : 𝔫.ideal.IsCoherent)
  (hd : 1 ≤ 𝔫.d) (W : Opens Y) {A : Set Y}

include hN h𝔞 hd in
/-- **Tails of a restricted coefficient ideal on an open set** (Włodarczyk `le:S` on `W`, for one given tower): let `𝔫` have
`N` a closed submanifold, coherent ideal and mark `≥ 1`, `W ⊆ Y` open and `A ⊆ N` with `A ∩ W` a closed submanifold of `W`.
If along every multiple test blow-up `T` of `𝔫` the cosupport of `𝔫_T` over `W` lies in the strict transform of `A`, then for
every multiple test blow-up `T₁` of `𝔫` the restricted tower `T₁|_W` is a multiple test blow-up of `(𝓒_N(𝔫)|_A)|_W`, and the
cosupport of its transform along `T₁|_W` is the trace of `cosupp 𝔫_{T₁}`. -/
theorem isGeoTestTower_restrict_withN_coeff_of_cosupp_subset
    (hA : IsClosedSubmanifold n ((Subtype.val : W → Y) ⁻¹' A)) (hAN : A ⊆ 𝔫.N)
    (hG : ∀ {Z : CMfd.{u} n} (T : BlowupTower Y Z), IsGeoTestTower 𝔫 T →
      (geoTransformAlong 𝔫 T).cosupp ∩ T.proj ⁻¹' (W : Set Y) ⊆ strictAlong T A)
    {Z : CMfd.{u} n} (T₁ : BlowupTower Y Z) (hT₁ : IsGeoTestTower 𝔫 T₁) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → Y) (withN (coeffMarkedAlong 𝔫) A)) (restrict W T₁) ∧
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y) (withN (coeffMarkedAlong 𝔫) A))
        (restrict W T₁)).cosupp = (Subtype.val : openPreimage T₁ W → Z) ⁻¹' (geoTransformAlong 𝔫 T₁).cosupp := by
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → Y) := contMDiff_subtype_val
  have hNW : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN W
  have hcW : (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval h𝔞
  have hdW : 1 ≤ (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).d := hd
  have hAW : (Subtype.val : W → Y) ⁻¹' A ⊆ (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).N := preimage_mono hAN
  have heq : MarkedIdeal.pullback (Subtype.val : W → Y) (withN (coeffMarkedAlong 𝔫) A) =
      withN (coeffMarkedAlong (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫)) ((Subtype.val : W → Y) ⁻¹' A) := by
    rw [ContactCanonicalAlong.pullback_withN, pullback_val_coeffMarkedAlong W 𝔫 h𝔞 hN hd]
  have hR := isGeoTestTower_restrict W hN h𝔞 T₁ hT₁
  have hC : CentresIn ((Subtype.val : W → Y) ⁻¹' A) (restrict W T₁) :=
    centresIn_restrict_of_forall 𝔫 W (fun T C hT hCa z hz => hG T hT ⟨hCa.2.1 hz.1, hz.2⟩) T₁ hT₁
  obtain ⟨hiff, hcos⟩ := coeffAlong_restrict_tower_iff (X := CMfd.of (n := n) W)
    (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫) hNW hcW hdW hA hAW (restrict W T₁)
  have hTest := hiff.mpr ⟨hR, hC⟩
  obtain ⟨-, hcT₁⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T₁ hT₁
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcT₁
  rw [heq]
  refine ⟨hTest, ?_⟩
  rw [hcos hTest, geoTransformAlong_restrict W hN h𝔞 T₁ hT₁, cosupp_pullback_val _ hhol, strictAlong_restrict W T₁ A]
  ext p
  simp only [mem_inter_iff, mem_preimage]
  exact ⟨fun h => h.1, fun h => ⟨h, hG T₁ hT₁ ⟨h, p.2⟩⟩⟩

end Generic

/-! ### Step 1b: `J̄ = 𝓒_N(𝓗_N(𝔍))`, any divisor -/

section CoeffHomAlong

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent)
  (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u)

include hN h𝔞 hd hu in
/-- **Giraud at the stage `T₀` along the tails** (READING `(𝔞, μ)`, any divisor): for `J̄ = 𝓒_N(𝓗_N(𝔍))`, a tangent
direction `u` of `(𝔍.ideal|_N, d)` along `N` on `U` and a multiple test blow-up `T₀ T` of `J̄`, the cosupport of
`J̄_{T₀ T}` over `T₀⁻¹U` lies in the strict transform along `T` of `S_{T₀} = (N ∩ V(u))_{T₀}`.
(`MaximalContactAlongTower.cosupp_subset_strictAlong_along` for `𝔍` along `T₀ T`, transferred by `J̄ ≃ 𝔍`.) -/
theorem cosupp_tail_subset_strictAlong {Y : CMfd.{u} n} (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) {Z : CMfd.{u} n} (T : BlowupTower Y Z)
    (hT : IsGeoTestTower (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) T) :
    (geoTransformAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) T).cosupp ∩
        T.proj ⁻¹' (openPreimage T₀ U : Set Y) ⊆
      strictAlong T (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})) := by
  have hW := coeff_homAlong_wEquiv 𝔍 hN h𝔞 hd
  have hTT : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T) :=
    (isGeoTestTower_append_iff _ T₀ T).mpr ⟨hT₀, hT⟩
  have hTa : IsGeoTestTower 𝔍 (T₀.append T) := (hW.2 _).1.mp hTT
  rintro z ⟨hz, hzU⟩
  rw [← geoTransformAlong_append, (hW.2 _).2 hTT] at hz
  have hzU' : z ∈ (T₀.append T).proj ⁻¹' (U : Set X) := by
    rw [BlowupTower.proj_append]
    exact hzU
  have h1 := cosupp_subset_strictAlong_along 𝔍 hN h𝔞 hd hu (T₀.append T) hTa ⟨hz, hzU'⟩
  rw [← strictAlong_append]
  exact strictAlong_mono (T₀.append T) inter_subset_left h1

include hN h𝔞 hd hu in
/-- **The tails of Step 1b on an open `W ⊆ T₀⁻¹U`** (READING `(𝔞, μ)`, any divisor): for `J̄ = 𝓒_N(𝓗_N(𝔍))`, a tangent
direction `u` of `(𝔍.ideal|_N, d)` along `N` on `U`, a multiple test blow-up `T₀ T₁` of `J̄` and an open `W` of the last stage
of `T₀` inside `T₀⁻¹U`: `T₁|_W` is a multiple test blow-up of `𝓢_{u,T₀}|_W = (𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(u))_{T₀}})|_W`,
and its cosupport along `T₁|_W` is the trace of `cosupp J̄_{T₀ T₁}`. -/
theorem isGeoTestTower_tail_coeffHomAlong_of_le {Y Z : CMfd.{u} n} (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z)
    (hT : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T₁)) (W : Opens Y)
    (hWU : (W : Set Y) ⊆ openPreimage T₀ U) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) (restrict W T₁) ∧
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) (restrict W T₁)).cosupp =
        (Subtype.val : openPreimage T₁ W → Z) ⁻¹'
          (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T₁)).cosupp := by
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  have hT₀a : IsGeoTestTower 𝔍 T₀ := ((coeff_homAlong_wEquiv 𝔍 hN h𝔞 hd).2 T₀).1.mp hT₀
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  have hdT : 1 ≤ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).d := by
    rw [d_geoTransformAlong]; exact one_le_coeffMarkedAlong_d _
  have hSN : strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ⊆ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).N :=
    strictAlong_subset_N (coeffMarkedAlong (homMarkedAlong 𝔍)) (fun x hx => hx.1) T₀
  have h := isGeoTestTower_restrict_withN_coeff_of_cosupp_subset _ hNT hcT hdT W
    (ContactStageInvDomain.isClosedSubmanifold_strictAlong_stage_of_le 𝔍 hN h𝔞 hd U hu T₀ hT₀a W hWU) hSN
    (fun T hT z hz => cosupp_tail_subset_strictAlong 𝔍 hN h𝔞 hd U hu T₀ hT₀ T hT ⟨hz.1, hWU hz.2⟩) T₁ hT₁
  rw [geoTransformAlong_append]
  exact h

end CoeffHomAlong

end

end Hironaka.ContactStageTail
