/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestriction
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupStrictIdeal
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HadamardBridgeAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.MarkedIdeal.RestrictLe
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The coefficient ideal along a submanifold, restricted to a submanifold, along multiple test blow-ups

Sources: Włodarczyk 2005, Lemmas `le:cf` and `le:S` (1) and the inclusion `⊆` of (2); GGT 2008, Lemma 5.6.3 and
Proposition 5.6.4 (1)--(2), for a marked ideal `(M, N, E, 𝔞, d)` on a closed submanifold `N` and a closed
submanifold `S ⊆ N`. The along-`N` form of `CoefficientIdealRestriction.restrict_tower` / `coeff_restrict_tower` (`N
= M`).

* `geoTransform_withN_restrictEquiv_along` (`le:cf`, one blowup, along `N`): for `S ⊆ N` and an admissible centre
  `C ⊆ S`, the transform of `𝔟|_S` is restricted-equivalent to the restriction of the transform of `𝔟` to the strict
  transform `S'` of `S`, `S' ⊆ N'`.
* `restrict_tower_along` (`le:cf` along towers): every multiple test blow-up of `𝔟` whose centres lie in the strict
  transforms of `S` is one of `𝔟|_S`, and along it `[𝔟|_S]_T ≃ (𝔟_T)|_{S_T}`, `S_T ⊆ N_T`.
* **`coeffAlong_restrict_tower`** (`le:S` (1) and the inclusion `⊆` of (2) along `N`): along a multiple test blow-up `T` of
  `𝔪` with centres in the strict transforms of `S`, `T` is one of `𝓒_N(𝔪)|_S`, `[𝓒_N(𝔪)|_S]_T ≃ 𝓒_N(𝔪)_T|_{S_T}`, and
  `supp(𝔪_T) ∩ S_T ⊆ supp[𝓒_N(𝔪)|_S]_T`.

Not here: the reverse inclusion `supp[𝓒_N(𝔪)|_S]_T ⊆ supp(𝔪_T)` for `T` nonempty (`le:S` (2) in full and (3) along
`N`; at `T = refl` it is `CoefficientIdealAlongRestriction.cosupp_coeffMarkedAlong_withN`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CoefficientIdealAlongRestrictionTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder IdealWeightPowers RestrictedIdealWeight BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal BlowupStrictSubmanifold HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealRestriction
open HomogenizedGlueingTower (strictAlong)

noncomputable section

/-! ### One admissible blowup -/

section OneStep

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- Strict transforms relative to a centre are monotone. -/
theorem geoStrictTransform_mono' (π : M' → M) (C : Set M) {A B : Set M} (h : A ⊆ B) :
    geoStrictTransform π C A ⊆ geoStrictTransform π C B :=
  closure_mono (preimage_mono (sdiff_subset_sdiff_left h))

/-- **Włodarczyk `le:cf`, one blowup, along `N`** (GGT Lemma 5.6.3): for `𝔟 = (M, N, E, 𝔞, d)` with `N` a closed
submanifold and `𝔞` coherent, a closed submanifold `S ⊆ N` and a centre `C` admissible for `𝔟` and for `𝔟|_S`, the
transform of `𝔟|_S` is restricted-equivalent to the restriction of the transform of `𝔟` to the strict transform `S'` of
`S`: on `S' ⊆ N'` both satisfy the defining equation `Res_{S'} π^*𝔞 = Res_{S'} (π^*𝓘_C)^d 𝔞'`
(`HomogenizedIdealAlongTower.restrictEquiv_geoTransform_of_pullback`). -/
theorem geoTransform_withN_restrictEquiv_along {𝔟 : MarkedIdeal n M} (hN : IsClosedSubmanifold n 𝔟.N)
    (h𝔟 : 𝔟.ideal.IsCoherent) {S : Set M} (hS : IsClosedSubmanifold n S) (hSN : S ⊆ 𝔟.N) {C : Set M}
    {π : M' → M} (hπ : IsBlowupAlong n C π) (hC : 𝔟.IsAdmissibleCentre C) (hCS : (withN 𝔟 S).IsAdmissibleCentre C) :
    RestrictEquiv ((withN 𝔟 S).geoTransform C π) (withN (𝔟.geoTransform C π) (geoStrictTransform π C S)) := by
  obtain ⟨c1, c2⟩ := restrictLe_pullback_geoTransform hN h𝔟 hC hπ
  have hsub : geoStrictTransform π C S ⊆ (𝔟.geoTransform C π).N := geoStrictTransform_mono' π C hSN
  exact restrictEquiv_geoTransform_of_pullback (𝔫 := withN 𝔟 S) hS h𝔟 hCS hπ
    (HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN h𝔟 hC hπ)
    (restrictLe_mono hsub c1) (restrictLe_mono hsub c2)

end OneStep

/-! ### Along towers -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Włodarczyk `le:cf` along towers, along `N`** (GGT Lemma 5.6.3 / Proposition 5.6.4 (1)): let `𝔟 = (X, N, E, 𝔞, d)`
with `N` a closed submanifold, `𝔞` coherent, and `S ⊆ N` a closed submanifold.  Every multiple test blow-up `T` of `𝔟`
whose centres lie in the strict transforms of `S` is a multiple test blow-up of `𝔟|_S`, and along it
`[𝔟|_S]_T ≃ (𝔟_T)|_{S_T}` (restricted equivalence); moreover `N_T` and `S_T ⊆ N_T` are closed submanifolds and both
transformed ideals stay coherent. -/
theorem restrict_tower_along (𝔟 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔟.N) (h𝔟 : 𝔟.ideal.IsCoherent)
    {S : Set X} (hS : IsClosedSubmanifold n S) (hSN : S ⊆ 𝔟.N) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔟 T → CentresIn S T →
      IsGeoTestTower (withN 𝔟 S) T ∧ IsClosedSubmanifold n (geoTransformAlong 𝔟 T).N ∧
      (geoTransformAlong 𝔟 T).ideal.IsCoherent ∧ IsClosedSubmanifold n (strictAlong T S) ∧
      strictAlong T S ⊆ (geoTransformAlong 𝔟 T).N ∧
      (geoTransformAlong (withN 𝔟 S) T).ideal.IsCoherent ∧
      RestrictEquiv (geoTransformAlong (withN 𝔟 S) T) (withN (geoTransformAlong 𝔟 T) (strictAlong T S))
  | _, .refl => fun _ _ => ⟨trivial, hN, h𝔟, hS, hSN, h𝔟, RestrictEquiv.refl (𝔪 := withN 𝔟 S) h𝔟⟩
  | _, .step T C π hπ => fun hT hTS => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff 𝔟 T C π hπ).mp hT
      obtain ⟨hTS0, hCS⟩ := hTS
      obtain ⟨hsT, hNT, hcohT, hST, hSNT, hcohs, hRE⟩ := restrict_tower_along 𝔟 hN h𝔟 hS hSN T hT0 hTS0
      have hCw : (withN (geoTransformAlong 𝔟 T) (strictAlong T S)).IsAdmissibleCentre C :=
        ⟨hC.1, fun x hx => CoefficientIdealAlongRestriction.cosupport_inter_subset_of_subset hSNT _ _
          ⟨hC.2.1 hx, hCS hx⟩, hC.2.2⟩
      have hCs : (geoTransformAlong (withN 𝔟 S) T).IsAdmissibleCentre C := hRE.isAdmissibleCentre_iff.mpr hCw
      have hNs : (geoTransformAlong (withN 𝔟 S) T).N = strictAlong T S := N_geoTransformAlong_withN 𝔟 S T
      have heq : (geoTransformAlong (withN 𝔟 S) T).geoTransform C π =
          (withN (geoTransformAlong 𝔟 T) (strictAlong T S)).geoTransform C π :=
        hRE.geoTransform_eq (hNs ▸ hST.1) hcohs hcohT hπ.contMDiff
      refine ⟨(isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hsT, hCs⟩, isClosedSubmanifold_geoTransform_N hNT hC hπ,
        HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNT hcohT hC hπ,
        BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hST hCS,
        geoStrictTransform_mono' π C hSNT,
        HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (hNs ▸ hST) hcohs hCs hπ, ?_⟩
      show RestrictEquiv ((geoTransformAlong (withN 𝔟 S) T).geoTransform C π)
        (withN ((geoTransformAlong 𝔟 T).geoTransform C π) (geoStrictTransform π C (strictAlong T S)))
      rw [heq]
      exact geoTransform_withN_restrictEquiv_along hNT hcohT hST hSNT hπ hC hCw

/-- **Włodarczyk `le:S` (1) and the inclusion `⊆` of (2), along `N`** (GGT Proposition 5.6.4 (1)--(2)): let
`𝔪 = (X, N, E, 𝔞, d)` with `N` a closed submanifold, `𝔞` coherent and `d ≥ 1`, `S ⊆ N` a closed submanifold, and `T` a
multiple test blow-up of `𝔪` whose centres lie in the strict transforms of `S`.  Then `T` is a multiple test blow-up of
the restricted coefficient ideal along `N`, `𝓒_N(𝔪)|_S`, along it `[𝓒_N(𝔪)|_S]_T ≃ 𝓒_N(𝔪)_T|_{S_T}`, and
`supp(𝔪_T) ∩ S_T ⊆ supp[𝓒_N(𝔪)|_S]_T`. -/
theorem coeffAlong_restrict_tower (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) {S : Set X} (hS : IsClosedSubmanifold n S) (hSN : S ⊆ 𝔪.N)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hTS : CentresIn S T) :
    IsGeoTestTower (withN (coeffMarkedAlong 𝔪) S) T ∧
      RestrictEquiv (geoTransformAlong (withN (coeffMarkedAlong 𝔪) S) T)
        (withN (geoTransformAlong (coeffMarkedAlong 𝔪) T) (strictAlong T S)) ∧
      (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T S ⊆
        (geoTransformAlong (withN (coeffMarkedAlong 𝔪) S) T).cosupp := by
  obtain ⟨hiff, hcos⟩ := coeffAlong_tower 𝔪 hN h𝔞 hd T
  have hTc : IsGeoTestTower (coeffMarkedAlong 𝔪) T := hiff.mpr hT
  obtain ⟨hsT, -, -, -, hSNT, -, hRE⟩ := restrict_tower_along (coeffMarkedAlong 𝔪) hN
    (isCoherent_coeffMarkedAlong h𝔞 hN) hS hSN T hTc hTS
  refine ⟨hsT, hRE, ?_⟩
  rw [hRE.cosupp_eq, ← hcos hT]
  exact CoefficientIdealAlongRestriction.cosupport_inter_subset_of_subset hSNT _ _

end Tower

end

end Hironaka.CoefficientIdealAlongRestrictionTower
