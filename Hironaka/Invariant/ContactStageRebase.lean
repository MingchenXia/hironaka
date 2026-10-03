/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ContactStageTail
import Hironaka.Invariant.InvDomainRebase
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.ContactCanonicalAlong
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.Invariant.ContactStageInvDomain
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.MarkedIdeal.MaximalContactAlongTower
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Re-basing Step 1b's restricted marked ideal across steps that are empty near the point

Source: Włodarczyk 2005 (arXiv `hiron.tex`), the lemma on the commutativity of the resolution procedure in Step 1
with étale morphisms (`J̄'_{|V(u)} = φ^*(J̄_{|V(u)})`; blow-ups whose centres miss the image pull back to
isomorphisms).

In Step 1b the value at a point involves the invariant of `𝓢_{u,T₀}|_W = (𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(u))_{T₀}})|_W`
(`MaximalOrderStepOneB.contactMarked N 𝔞 μ u T₀ W`), formed at a stage `T₀` that depends on the point and restricted to a
neighbourhood `W ⊆ T₀⁻¹U` of it, along the rest of the segment.  For a nearby point whose stage is later, `T₀ T`, the steps of
`T` are empty over `W` (`RestrictEmptyTower.CentresAvoid W T`), and re-basing (property (4') of
`ResolutionInvariantExt.ResolutionInvariant`) compares the two values once the marked ideal formed at the earlier stage,
transformed along `T|_W`, is known to be the one formed at the later stage.  This module proves that, up to restricted
equivalence, and the resulting identity of values.

## Main results

* `restrictEquiv_restrictedCoeff_geoTransformAlong_of_isEmptyTower` (generic): along a tower with only empty
  centres, `𝓒_{N_T}(𝔪_T)|_{A_T} ≃ (𝓒_N(𝔪)|_A)_T` ((K3)
  `ContactCanonicalAlong.restrictEquiv_restrictedCoeff_geoTransformAlong_empty` step by step);
* `restrictEquiv_restrictedCoeffHomAlong_rebase` (any divisor): for `J̄ = 𝓒_N(𝓗_N(𝔍))`, a multiple test blow-up `T₀ T` of `J̄`,
  `W ⊆ T₀⁻¹U` open with the centres of `T` missing `W`: `𝓢_{u,T₀T}|_{T⁻¹W} ≃ (𝓢_{u,T₀}|_W)_{T|_W}`;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ContactStageRebase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower MarkedIdealBiholomorphism MarkedIdealRestrictOpen MemberInterTowerAlong MaximalContactAlongTower MarkedIdealOperationsAlong.MarkedIdeal ResolutionInvariantExt RestrictEmptyTower
open HomogenizedGlueingTower (strictAlong strictAlong_restrict)
open MemberInterLocusAlong (strictAlong_append)
open ContactIndependenceAlong (one_le_coeffMarkedAlong_d)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Restricted coefficient ideals along towers with only empty centres -/

section Generic

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
  (hd : 1 ≤ 𝔪.d) {A : Set X} (hA : IsClosedSubmanifold n A) (hAN : A ⊆ 𝔪.N)

include hN h𝔞 hd hA hAN in
/-- **The restricted coefficient ideal along a tower with only empty centres** ((K3) along the tower): for `𝔪` with `N` a
closed submanifold, coherent ideal and mark `≥ 1`, a closed submanifold `A ⊆ N` and a tower `T` all of whose centres are
empty, `𝓒_{N_T}(𝔪_T)|_{A_T} ≃ (𝓒_N(𝔪)|_A)_T`: restricting at the last stage or transforming the restriction formed at the
first stage gives restricted-equivalent marked ideals. -/
theorem restrictEquiv_restrictedCoeff_geoTransformAlong_of_isEmptyTower :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T →
      RestrictEquiv (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T)) (strictAlong T A))
        (geoTransformAlong (withN (coeffMarkedAlong 𝔪) A) T)
  | _, .refl, _ => RestrictEquiv.refl (isCoherent_coeffMarkedAlong h𝔞 hN)
  | _, .step T C π hπ, hT => by
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := hT
      subst hC
      have hTt : IsGeoTestTower 𝔪 T := isGeoTestTower_of_isEmptyTower 𝔪 T hT
      obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hTt
      have hK := ContactCanonicalAlong.restrictEquiv_restrictedCoeff_geoTransformAlong_empty hN h𝔞 hd T hTt π hπ hAN
      have ih := restrictEquiv_restrictedCoeff_geoTransformAlong_of_isEmptyTower T hT
      have hcS : (geoTransformAlong (withN (coeffMarkedAlong 𝔪) A) T).ideal.IsCoherent :=
        (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (𝔪 := withN (coeffMarkedAlong 𝔪) A) hA
          (isCoherent_coeffMarkedAlong h𝔞 hN) T (isGeoTestTower_of_isEmptyTower _ T hT)).2
      have heq := ih.geoTransform_eq (isClosed_strictAlong T hA.1) (isCoherent_coeffMarkedAlong hcT hNT) hcS
        (C := ∅) hπ.contMDiff
      show RestrictEquiv _ ((geoTransformAlong (withN (coeffMarkedAlong 𝔪) A) T).geoTransform ∅ π)
      rw [← heq]
      exact hK

end Generic

/-! ### Step 1b: `J̄ = 𝓒_N(𝓗_N(𝔍))`, any divisor -/

section CoeffHomAlong

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent)
  (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u)

include hN h𝔞 hd hu in
/-- **Step 1b's restricted marked ideal re-based across steps empty over `W`** (any divisor; READING `(𝔞, μ)`): for
`J̄ = 𝓒_N(𝓗_N(𝔍))`, a tangent direction `u` of `(𝔍.ideal|_N, d)` along `N` on `U`, a multiple test blow-up `T₀ T` of `J̄` and
an open `W ⊆ T₀⁻¹U` of the last stage of `T₀` missed by the centres of `T`: the restricted coefficient ideal formed at the
later stage, `𝓢_{u,T₀T}|_{T⁻¹W}`, is restricted-equivalent to the transform along `T|_W` of the one formed at `T₀`,
`(𝓢_{u,T₀}|_W)_{T|_W}`. -/
theorem restrictEquiv_restrictedCoeffHomAlong_rebase {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T : BlowupTower Y₀ Y) (hT : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T)) (W : Opens Y₀)
    (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U) (hW : CentresAvoid W T) :
    RestrictEquiv
      (MarkedIdeal.pullback (Subtype.val : openPreimage T W → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T)))
          (strictAlong (T₀.append T) (𝔍.N ∩ {x | u x = 0}))))
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) (restrict W T)) := by
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T).mp hT
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  have hT₀a : IsGeoTestTower 𝔍 T₀ := ((coeff_homAlong_wEquiv 𝔍 hN h𝔞 hd).2 T₀).1.mp hT₀
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  have hdT : 1 ≤ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).d := by
    rw [d_geoTransformAlong]; exact one_le_coeffMarkedAlong_d _
  have hSN : strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ⊆ (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀).N :=
    strictAlong_subset_N (coeffMarkedAlong (homMarkedAlong 𝔍)) (fun x hx => hx.1) T₀
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → Y₀) := contMDiff_subtype_val
  have he : IsEmptyTower (restrict W T) := (isEmptyTower_restrict_iff W T).mpr hW
  have hK := restrictEquiv_restrictedCoeff_geoTransformAlong_of_isEmptyTower (X := CMfd.of (n := n) W)
    (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
    (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNT W) (GermIdealPullbackCalculus.isCoherent_pullback hval hcT)
    hdT (ContactStageInvDomain.isClosedSubmanifold_strictAlong_stage_of_le 𝔍 hN h𝔞 hd U hu T₀ hT₀a W hWU)
    (preimage_mono hSN) (restrict W T) he
  rw [ContactCanonicalAlong.restrictedCoeff_geoTransformAlong_restrict W hNT hcT hdT T hT₁,
    ← pullback_val_coeffMarkedAlong W _ hcT hNT hdT] at hK
  rw [geoTransformAlong_append, strictAlong_append]
  exact hK

end CoeffHomAlong

end

end Hironaka.ContactStageRebase
