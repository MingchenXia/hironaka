/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.CoefficientRestrictionDrop
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestrictionFull
import Hironaka.Blowup.BlowupSequences
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.DropMembers
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The restricted coefficient ideal along a submanifold with the members containing `S` deleted

Source: Włodarczyk 2005, Lemmas `le:cf`, `le:S`, `le:S2` and Step 1a (the marked ideal `(S, 𝓒(𝓙)|_S, E_S, μ_𝓒)` with
`E_S` the members of `E` not containing `S`), applied inside `N`.

* `coeffAlong_restrict_withE_iff`: for `𝔪 = (X, N, E, 𝔞, μ)` well formed with `μ ≥ 1`, a closed submanifold `S ⊆ N`, and a
  list `E'` of members of `E` such that every member of `E` missing from `E'` contains `S`: a tower is a multiple test
  blow-up of `(X, S, E', 𝓒_N(𝔞), μ_𝓒)` iff it is one of `𝔪` with centres in the strict transforms of `S`, and along it
  `cosupp = cosupp 𝔪_T ∩ S_T`.  From `CoefficientIdealAlongRestrictionFull.coeffAlong_restrict_tower_iff` (`le:S` in full
  along `N`, keeping `E`) and `DropMembers` (deleting members containing `S` changes nothing along towers with centres in
  the strict transforms of `S`, given simple normal crossings along the test towers of `𝔪`).
-/

open Set

universe u

namespace Hironaka.CoefficientIdealAlongRestrictionDrop

open Hironaka.BlowupSequences NormalCrossings BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction HomogenizedIdealAlong DropMembers CoefficientRestrictionDrop CoefficientIdealAlongRestrictionFull
open HomogenizedGlueingTower (strictAlong)

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The restricted coefficient ideal along `N` with `E_S`** (`hir:coefficient-restriction` inside `N`): for
`𝔪 = (X, N, E, 𝔞, μ)` well formed with `μ ≥ 1`, a closed submanifold `S ⊆ N` and a list `E'` of members of `E` such that
every member of `E` missing from `E'` contains `S`, a tower is a multiple test blow-up of `(X, S, E', 𝓒_N(𝔞), μ_𝓒)` if and
only if it is a multiple test blow-up of `𝔪` with centres in the strict transforms of `S`, and along it the cosupport is
`cosupp 𝔪_T ∩ S_T`. -/
theorem coeffAlong_restrict_withE_iff (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed) (hd : 1 ≤ 𝔪.d)
    {S : Set X} (hS : IsClosedSubmanifold n S) (hSN : S ⊆ 𝔪.N) {E' : List (Set X)} (hsub : ∀ H ∈ E', H ∈ 𝔪.E)
    (hA : ∀ H ∈ 𝔪.E, H ∉ E' → S ⊆ H) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (IsGeoTestTower ({ withN (coeffMarkedAlong 𝔪) S with E := E' } : MarkedIdeal n X) T ↔
        IsGeoTestTower 𝔪 T ∧ CentresIn S T) ∧
      (IsGeoTestTower ({ withN (coeffMarkedAlong 𝔪) S with E := E' } : MarkedIdeal n X) T →
        (geoTransformAlong ({ withN (coeffMarkedAlong 𝔪) S with E := E' } : MarkedIdeal n X) T).cosupp =
          (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T S) := by
  have hle : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (IsGeoTestTower (withN (coeffMarkedAlong 𝔪) S) T ↔ IsGeoTestTower 𝔪 T ∧ CentresIn S T) ∧
      (IsGeoTestTower (withN (coeffMarkedAlong 𝔪) S) T →
        (geoTransformAlong (withN (coeffMarkedAlong 𝔪) S) T).cosupp =
          (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T S) :=
    fun T => coeffAlong_restrict_tower_iff 𝔪 h𝔪.isClosedSubmanifold_N h𝔪.isCoherent hd hS hSN T
  -- simple normal crossings along the test towers of `𝓒_N(𝔪)|_S` (they are test towers of `𝔪`)
  have hSNC : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (withN (coeffMarkedAlong 𝔪) S) T →
      IsSNCDivisor n (geoTransformAlong (withN (coeffMarkedAlong 𝔪) S) T).E := fun T hT => by
    have h𝔪T := ((hle T).1.mp hT).1
    rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := withN (coeffMarkedAlong 𝔪) S) (𝔫 := 𝔪) rfl T]
    exact (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔪 T h𝔪T).isSNCDivisor
  have hdrop := fun (hTS : CentresIn S T) =>
    isGeoTestTower_withE_iff_of_centresIn_of_snc (withN (coeffMarkedAlong 𝔪) S) hSNC (S := S) hsub hA T hTS
  refine ⟨⟨fun hT => ?_, fun ⟨h𝔪T, hTS⟩ => ?_⟩, fun hT => ?_⟩
  · have hTS := centresIn_of_isGeoTestTower_withN_withE (coeffMarkedAlong 𝔪) S E' T hT
    exact (hle T).1.mp ((hdrop hTS).1.mp hT)
  · exact (hdrop hTS).1.mpr ((hle T).1.mpr ⟨h𝔪T, hTS⟩)
  · have hTS := centresIn_of_isGeoTestTower_withN_withE (coeffMarkedAlong 𝔪) S E' T hT
    have h𝔫T := (hdrop hTS).1.mp hT
    rw [cosupp_geoTransformAlong_withE]
    exact (hle T).2 h𝔫T

end Hironaka.CoefficientIdealAlongRestrictionDrop
