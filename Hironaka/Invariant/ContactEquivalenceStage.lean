/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ContactEquivalenceAlong
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.MarkedIdeal.MaximalContactAlongTower
import Hironaka.MarkedIdeal.MaximalContactTower
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The reduction to a hypersurface of maximal contact at a later stage of a tower

Step 1b of `hir:maximal-order-step` forms the restricted marked ideal `𝓢_{u,T₀} = 𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩
V(u))_{T₀}}` at the stage `T₀` where it starts, for a tangent direction `u` chosen at the start of Step 1 on an open
`U`, and evaluates the inductive invariant of `𝓢_{u,T₀}` along the rest `T₁` of the segment. This module proves that
over `V = T₀⁻¹U` the transform `J̄_{T₀}` and `𝓢_{u,T₀}` are equivalent marked ideals
(`MarkedIdealEquivalence.WEquiv`), so that the tails `T₁|_V` are multiple test blow-ups of `𝓢_{u,T₀}|_V` with
cosupports `cosupp J̄_{T₀ T₁}`. Source: Włodarczyk 2005 (arXiv `hiron.tex`), Step 1bb ("By Lemma `le:codim2`,
`(V(u)_i)_{0 ≤ i ≤ p}` is a multiple test blow-up of `(V(u), J̄|_{V(u)}, ∅, μ̄)`. In particular the induced marked
ideal for `i = p` is `J̄_{p|V(u)_p}`").

## Main results

* `strictAlong_inter_preimage_eq` (**strict transforms are local over open sets of the base**): if `A ∩ O = B ∩ O` for an
  open `O`, then `strictAlong T A ∩ T⁻¹O = strictAlong T B ∩ T⁻¹O`.
* `exists_isTangentDirectionAlong_stage` (**the tangent directions at the stage `T₀`**): every point of `N_{T₀}`
  over `U` has an open neighbourhood `W` and a tangent direction `w` of `𝔪_{T₀}` on `W` with `N_{T₀} ∩ V(w) ∩ W =
  S_{T₀} ∩ W`, `S_{T₀} = strictAlong T₀ (N ∩ V(u))`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ContactEquivalenceStage

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdealAlong TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal CoefficientIdealAlongRestrictionFull MarkedIdealBiholomorphism MarkedIdealRestrictOpen MemberInterTowerAlong ContactEquivalenceAlong MaximalContactAlongTower
open HomogenizedGlueingTower (strictAlong strictAlong_step strictAlong_restrict N_geoTransformAlong)

noncomputable section

variable {n : ℕ}

/-! ### Locality of strict transforms -/

section Local

variable {X : CMfd.{u} n}

/-- **Strict transforms along a tower are local over open sets of the base**: if `A` and `B` agree on the open set `O`,
their strict transforms agree over `O`. -/
theorem strictAlong_inter_preimage_eq {O : Set X} (hO : IsOpen O) {A B : Set X} (hAB : A ∩ O = B ∩ O) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → strictAlong T A ∩ T.proj ⁻¹' O = strictAlong T B ∩ T.proj ⁻¹' O
  | _, .refl => hAB
  | _, .step T C π hπ => by
      rw [strictAlong_step, strictAlong_step, BlowupTower.proj_step, preimage_comp]
      exact MaximalContactTower.geoStrictTransform_inter_preimage hπ.contMDiff.continuous
        (hO.preimage T.contMDiff_proj.continuous) (strictAlong_inter_preimage_eq hO hAB T)

end Local

/-! ### The tangent directions at a later stage -/

section Stage

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
  (hd : 1 ≤ 𝔪.d) (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d U u)
  {Y : CMfd.{u} n} (T₀ : BlowupTower X Y) (hT₀ : IsGeoTestTower 𝔪 T₀)

include hN h𝔞 hd hu hT₀ in
/-- **The tangent directions at the stage `T₀`**: every point `z ∈ N_{T₀}` over `U` has an open neighbourhood `W` over
`U` carrying a tangent direction `w` of `(𝔞_{T₀}|_{N_{T₀}}, d)` along `N_{T₀}` with `N_{T₀} ∩ V(w) ∩ W = (N ∩
V(u))_{T₀} ∩ W` (`MaximalContactAlongTower.exists_contact_along`, made a genuine tangent direction by
`ContactEquivalenceAlong.exists_isTangentDirectionAlong_of_isInSpanOnAt`, and the locality of strict transforms). -/
theorem exists_isTangentDirectionAlong_stage {z : Y} (hzN : z ∈ (geoTransformAlong 𝔪 T₀).N) (hzU : T₀.proj z ∈ U) :
    ∃ W : Opens Y, z ∈ W ∧ (W : Set Y) ⊆ T₀.proj ⁻¹' U ∧ ∃ w : Y → ℂ,
      IsTangentDirectionAlong (geoTransformAlong 𝔪 T₀).N (geoTransformAlong 𝔪 T₀).ideal
        (geoTransformAlong 𝔪 T₀).d W w ∧
      (geoTransformAlong 𝔪 T₀).N ∩ {x | w x = 0} ∩ W = strictAlong T₀ (𝔪.N ∩ {x | u x = 0}) ∩ W := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T₀ hT₀
  have hdT : (geoTransformAlong 𝔪 T₀).d = 𝔪.d := d_geoTransformAlong 𝔪 T₀
  obtain ⟨O, w₀, hzO, hOo, hOU, hw₀, hw₀D, hw₀1, hw₀A⟩ := exists_contact_along 𝔪 hN h𝔞 hd hu T₀ hT₀ z hzN hzU
  rw [← hdT] at hw₀D
  obtain ⟨W, hzW, hWO, w, hw, hagree⟩ :=
    exists_isTangentDirectionAlong_of_isInSpanOnAt hcT hNT hOo hw₀ hw₀D hw₀1 hzO hzN
  refine ⟨W, hzW, hWO.trans hOU, w, hw, ?_⟩
  -- locality of the strict transform over `U`
  have hloc : strictAlong T₀ (𝔪.N ∩ {x | u x = 0} ∩ U) ∩ T₀.proj ⁻¹' U =
      strictAlong T₀ (𝔪.N ∩ {x | u x = 0}) ∩ T₀.proj ⁻¹' U :=
    strictAlong_inter_preimage_eq U.isOpen (by rw [inter_assoc, inter_self]) T₀
  ext y
  constructor
  · rintro ⟨⟨hyN, hy0⟩, hyW⟩
    have hyO := hWO hyW
    have hyA : y ∈ strictAlong T₀ (𝔪.N ∩ {x | u x = 0} ∩ U) := by
      refine (hw₀A y hyO hyN).mp ?_
      rw [← hagree y hyW hyN]
      exact hy0
    have h1 : y ∈ strictAlong T₀ (𝔪.N ∩ {x | u x = 0} ∩ U) ∩ T₀.proj ⁻¹' U := ⟨hyA, hOU hyO⟩
    rw [hloc] at h1
    exact ⟨h1.1, hyW⟩
  · rintro ⟨hyS, hyW⟩
    have hyO := hWO hyW
    have hyN : y ∈ (geoTransformAlong 𝔪 T₀).N :=
      strictAlong_subset_N 𝔪 (fun x hx => hx.1) T₀ hyS
    have h1 : y ∈ strictAlong T₀ (𝔪.N ∩ {x | u x = 0}) ∩ T₀.proj ⁻¹' U := ⟨hyS, hOU hyO⟩
    rw [← hloc] at h1
    have hyA := h1.1
    refine ⟨⟨hyN, ?_⟩, hyW⟩
    show w y = 0
    rw [hagree y hyW hyN]
    exact (hw₀A y hyO hyN).mpr hyA

end Stage

end

end Hironaka.ContactEquivalenceStage
