/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Restriction of a marked ideal and of the coefficient ideal to a submanifold

Sources: Włodarczyk 2005, §2.11, Lemmas `le:cf` and `le:S`; in the analytic paper (GGT 2008,
`wlodarczyk09-analytic-resolution`) Lemma 5.6.2, Lemma 5.6.3 and Proposition 5.6.4.

For a marked ideal `𝔟 = (M, M, E, 𝔞, d)` and a set `S ⊆ M`, `withN 𝔟 S = (M, S, E, 𝔞, d)` is the restriction
`(𝔞, d)|_S` of Włodarczyk (the ideal `𝔞|_S` of `𝒪_S`, represented by `𝔞`).

* `cosupp_inter_subset_cosupp_withN` (GGT Lemma 5.6.3, first half of `le:cf`): the order does not drop under
  restriction, `cosupp(𝔟) ∩ S ⊆ cosupp(𝔟|_S)`.
* `geoTransform_withN_restrictEquiv` (`le:cf`, one blowup): for a closed submanifold `S` and an admissible centre
  `C ⊆ S`, the transform of `𝔟|_S` is restricted-equivalent to the restriction of the transform of `𝔟` to the strict
  transform `S'` of `S`: `σ^c((𝔞, d)|_S) = (σ^c(𝔞, d))|_{S'}`.  Proof: along `S'` both are the quotient of
  `Res_{S'} σ^*𝔞` by the exceptional ideal `(σ^*𝓘_C)^d`, which is invertible along `S'` and can be cancelled
  (`restrictLe_of_restrictLe_mul_mul`); no coordinates are needed.
* `restrict_tower` (`le:cf` along towers): every multiple test blow-up of `𝔟` whose centres lie in the strict
  transforms `S_i` of `S` (`CentresIn S T`) is one of `𝔟|_S`, and along it `[𝔟|_S]_i ≃ (𝔟_i)|_{S_i}`
  (restricted equivalence).

NOT done here: the reverse inclusion `supp[𝓒(𝔪)|_S]_T ⊆ supp(𝔪_T)` for `T` nonempty (`le:S` (2) in full and (3)).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CoefficientIdealRestriction

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal IdealWeightPowers BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal DerivativeIdealTower CoefficientIdeal HomogenizedGlueing HomogenizedGlueingTower MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal RestrictedIdealWeight BlowupStrictSubmanifold

noncomputable section

/-! ### Restriction of a marked ideal to a set -/

section OneSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **The restriction `(𝔞, d)|_S`** of a marked ideal to a set `S`: the same `E`, ideal and mark, with `N = S`
(the ideal `𝔞|_S` of `𝒪_S` is represented by the ambient ideal). -/
def withN (𝔟 : MarkedIdeal n M) (S : Set M) : MarkedIdeal n M where
  N := S
  E := 𝔟.E
  ideal := 𝔟.ideal
  d := 𝔟.d

@[simp] theorem withN_N (𝔟 : MarkedIdeal n M) (S : Set M) : (withN 𝔟 S).N = S := rfl
@[simp] theorem withN_E (𝔟 : MarkedIdeal n M) (S : Set M) : (withN 𝔟 S).E = 𝔟.E := rfl
@[simp] theorem withN_ideal (𝔟 : MarkedIdeal n M) (S : Set M) : (withN 𝔟 S).ideal = 𝔟.ideal := rfl
@[simp] theorem withN_d (𝔟 : MarkedIdeal n M) (S : Set M) : (withN 𝔟 S).d = 𝔟.d := rfl

theorem cosupp_withN (𝔟 : MarkedIdeal n M) (S : Set M) :
    (withN 𝔟 S).cosupp = cosupport n S 𝔟.ideal 𝔟.d := rfl

/-- **The order does not drop under restriction** (GGT Lemma 5.6.3): `cosupp(𝔞, d) ∩ S ⊆ cosupp(𝔞|_S, d)`. -/
theorem cosupport_univ_inter_subset (𝔞 : GermIdeal n M) (d : ℕ) (S : Set M) :
    cosupport n univ 𝔞 d ∩ S ⊆ cosupport n S 𝔞 d :=
  fun _ hx => ⟨hx.2, fun g hg => (hx.1.2 g hg).mono_set (subset_univ S)⟩

/-- **`supp(𝔟) ∩ S ⊆ supp(𝔟|_S)`** for `N = M` (GGT Lemma 5.6.3; Włodarczyk 2005 `le:cf`, first statement). -/
theorem cosupp_inter_subset_cosupp_withN {𝔟 : MarkedIdeal n M} (hN : 𝔟.N = univ) (S : Set M) :
    𝔟.cosupp ∩ S ⊆ (withN 𝔟 S).cosupp := by
  rw [cosupp_withN, MarkedIdeal.cosupp, hN]
  exact cosupport_univ_inter_subset _ _ S

variable [IsComplexManifold n M] {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M']

/-- **Włodarczyk `le:cf`, one blowup** (GGT Lemma 5.6.3 and the first display of the proof of Proposition 5.6.4):
for `𝔟 = (M, M, E, 𝔞, d)` with `𝔞` coherent, a closed submanifold `S`, and a centre `C` admissible for `𝔟` and for
`𝔟|_S` (so `C ⊆ S`), the transform of `𝔟|_S` is restricted-equivalent to the restriction of the transform of `𝔟`
to the strict transform `S'` of `S`: `σ^c((𝔞, d)|_S) = (σ^c(𝔞, d))|_{S'}`. -/
theorem geoTransform_withN_restrictEquiv {𝔟 : MarkedIdeal n M} (hN : 𝔟.N = univ) (h𝔟 : 𝔟.ideal.IsCoherent)
    {S : Set M} (hS : IsClosedSubmanifold n S) {C : Set M} {π : M' → M} (hπ : IsBlowupAlong n C π)
    (hC : 𝔟.IsAdmissibleCentre C) (hCS : (withN 𝔟 S).IsAdmissibleCentre C) :
    RestrictEquiv ((withN 𝔟 S).geoTransform C π)
      (withN (𝔟.geoTransform C π) (geoStrictTransform π C S)) := by
  have hNuniv : IsClosedSubmanifold n 𝔟.N := hN ▸ isClosedSubmanifold_univ
  have hs' : ((withN 𝔟 S).geoTransform C π).ideal.IsCoherent :=
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (𝔪 := withN 𝔟 S) hS h𝔟 hCS hπ
  have hc' : (𝔟.geoTransform C π).ideal.IsCoherent :=
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNuniv h𝔟 hC hπ
  obtain ⟨s1, s2⟩ := restrictLe_pullback_geoTransform (𝔪 := withN 𝔟 S) hS h𝔟 hCS hπ
  obtain ⟨c1, c2⟩ := restrictLe_pullback_geoTransform hNuniv h𝔟 hC hπ
  have hsub : geoStrictTransform π C S ⊆ (𝔟.geoTransform C π).N := by
    rw [geoTransform_N, hN, geoStrictTransform_univ hπ]
    exact subset_univ _
  have c1' := restrictLe_mono hsub c1
  have c2' := restrictLe_mono hsub c2
  have hinv := isInvertibleAlong_geoStrictTransform hπ S 𝔟.d
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · refine RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul hs' hc' hinv ?_
    rw [RestrictLeCalculus.mul_comm' ((withN 𝔟 S).geoTransform C π).ideal,
      RestrictLeCalculus.mul_comm' (withN (𝔟.geoTransform C π) (geoStrictTransform π C S)).ideal]
    exact RestrictLeCalculus.RestrictLe.trans s2 c1'
  · refine RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul hc' hs' hinv ?_
    rw [RestrictLeCalculus.mul_comm' ((withN 𝔟 S).geoTransform C π).ideal,
      RestrictLeCalculus.mul_comm' (withN (𝔟.geoTransform C π) (geoStrictTransform π C S)).ideal]
    exact RestrictLeCalculus.RestrictLe.trans c2' s1

end OneSpace

/-! ### Along towers -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The centres of `T` lie in the strict transforms of `A`.** -/
def CentresIn (A : Set X) : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => CentresIn A T ∧ C ⊆ strictAlong T A

@[simp] theorem centresIn_refl (A : Set X) : CentresIn A (BlowupTower.refl : BlowupTower X X) := trivial

theorem centresIn_step_iff (A : Set X) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) : CentresIn A (.step T C π hπ) ↔ CentresIn A T ∧ C ⊆ strictAlong T A :=
  Iff.rfl

/-- The `N` of the transform of a restriction is the strict transform of the set. -/
theorem N_geoTransformAlong_withN (𝔟 : MarkedIdeal n X) (S : Set X) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (geoTransformAlong (withN 𝔟 S) T).N = strictAlong T S :=
  N_geoTransformAlong (withN 𝔟 S) T

/-- **Włodarczyk `le:cf` along towers** (GGT Lemma 5.6.3 / Proposition 5.6.4 (1)): let `𝔟 = (X, X, E, 𝔞, d)` with
`𝔞` coherent and `S` a closed submanifold.  Every multiple test blow-up `T` of `𝔟` whose centres lie in the strict
transforms of `S` is a multiple test blow-up of `𝔟|_S`, and along it `[𝔟|_S]_T ≃ (𝔟_T)|_{S_T}` (restricted
equivalence); moreover `𝔟_T` keeps `N` the whole space, both transformed ideals stay coherent and `S_T` is a closed
submanifold. -/
theorem restrict_tower (𝔟 : MarkedIdeal n X) (hN : 𝔟.N = univ) (h𝔟 : 𝔟.ideal.IsCoherent) {S : Set X}
    (hS : IsClosedSubmanifold n S) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔟 T → CentresIn S T →
      IsGeoTestTower (withN 𝔟 S) T ∧ (geoTransformAlong 𝔟 T).N = univ ∧
      (geoTransformAlong 𝔟 T).ideal.IsCoherent ∧ IsClosedSubmanifold n (strictAlong T S) ∧
      (geoTransformAlong (withN 𝔟 S) T).ideal.IsCoherent ∧
      RestrictEquiv (geoTransformAlong (withN 𝔟 S) T) (withN (geoTransformAlong 𝔟 T) (strictAlong T S))
  | _, .refl => fun _ _ => ⟨trivial, hN, h𝔟, hS, h𝔟, RestrictEquiv.refl (𝔪 := withN 𝔟 S) h𝔟⟩
  | _, .step T C π hπ => fun hT hTS => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff 𝔟 T C π hπ).mp hT
      obtain ⟨hTS0, hCS⟩ := hTS
      obtain ⟨hsT, hNT, hcohT, hST, hcohs, hRE⟩ := restrict_tower 𝔟 hN h𝔟 hS T hT0 hTS0
      have hCw : (withN (geoTransformAlong 𝔟 T) (strictAlong T S)).IsAdmissibleCentre C :=
        ⟨hC.1, fun x hx => cosupp_inter_subset_cosupp_withN hNT _ ⟨hC.2.1 hx, hCS hx⟩, hC.2.2⟩
      have hCs : (geoTransformAlong (withN 𝔟 S) T).IsAdmissibleCentre C := hRE.isAdmissibleCentre_iff.mpr hCw
      have hNs : (geoTransformAlong (withN 𝔟 S) T).N = strictAlong T S := N_geoTransformAlong_withN 𝔟 S T
      have heq : (geoTransformAlong (withN 𝔟 S) T).geoTransform C π =
          (withN (geoTransformAlong 𝔟 T) (strictAlong T S)).geoTransform C π :=
        hRE.geoTransform_eq (hNs ▸ hST.1) hcohs hcohT hπ.contMDiff
      have hNuniv : IsClosedSubmanifold n (geoTransformAlong 𝔟 T).N := hNT ▸ isClosedSubmanifold_univ
      refine ⟨(isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hsT, hCs⟩, geoTransform_N_eq_univ hNT hπ,
        HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNuniv hcohT hC hπ,
        BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hST hCS,
        HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (hNs ▸ hST) hcohs hCs hπ, ?_⟩
      show RestrictEquiv ((geoTransformAlong (withN 𝔟 S) T).geoTransform C π)
        (withN ((geoTransformAlong 𝔟 T).geoTransform C π) (geoStrictTransform π C (strictAlong T S)))
      rw [heq]
      exact geoTransform_withN_restrictEquiv hNT hcohT hST hπ hC hCw

end Tower

end

end Hironaka.CoefficientIdealRestriction
