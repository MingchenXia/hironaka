import Hironaka.Invariant.DropMembers
import Hironaka.MarkedIdeal.CoefficientRestrictionTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The restricted coefficient ideal with the members containing `S` deleted

Blueprint `hir:coefficient-restriction` (`blueprint/src/hironaka.tex`, Hironaka phase H4, Step 1a of Proposition
`hir:maximal-order-step`).  Source: Włodarczyk 2005, Lemmas `le:cf`, `le:S`, `le:S2` and Step 1a (the marked ideal
`(S, 𝓒(𝓙)|_S, E_S, μ_𝓒)` with `E_S` the members of `E` not containing `S`).

TN23 proved Włodarczyk's `le:S` in full keeping the divisor `E` (`CoefficientRestrictionTower.coeff_restrict_tower_iff`).
Step 1a needs the divisor `E_S` (the members containing `S` deleted); deleting them changes nothing along towers with
centres in the strict transforms of `S` (`DropMembers`).  Combining the two:

* `coeff_restrict_withE_iff`: for `𝔪 = (X, X, E, 𝔞, μ)` well formed, `𝔞` coherent, `μ ≥ 1`, a closed submanifold `S`, and
  `E'` a list of members of `E` such that every member of `E` missing from `E'` contains `S`: a tower is a multiple test
  blow-up of `(X, S, E', 𝓒(𝔞), μ_𝓒)` iff it is one of `𝔪` with centres in the strict transforms of `S`, and along it
  `cosupp = cosupp 𝔪_T ∩ S_T`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set

universe u

namespace Hironaka.CoefficientRestrictionDrop

open Hironaka.BlowupSequences NormalCrossings BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction CoefficientIdeal HomogenizedGlueingTower CoefficientRestrictionTower DropMembers

variable {n : ℕ} {X : CMfd.{u} n}

/-- The centres of a multiple test blow-up of a marked ideal with submanifold `S` lie in the strict transforms of `S`,
whatever its divisor. -/
theorem centresIn_of_isGeoTestTower_withN_withE (𝔟 : MarkedIdeal n X) (S : Set X) (E' : List (Set X)) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      IsGeoTestTower ({ withN 𝔟 S with E := E' } : MarkedIdeal n X) T → CentresIn S T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
      refine ⟨centresIn_of_isGeoTestTower_withN_withE 𝔟 S E' T hT0, fun x hx => ?_⟩
      have h1 := hC.subset_N hx
      rw [(geoTransformAlong_withE (withN 𝔟 S) E' T).1, N_geoTransformAlong_withN 𝔟 S T] at h1
      exact h1

/-- **The restricted coefficient ideal with `E_S`** (`hir:coefficient-restriction`, `N = M`): for `𝔪 = (X, X, E, 𝔞, μ)`
well formed with `μ ≥ 1`, a closed submanifold `S` and a list `E'` of members of `E` such that every member of `E`
missing from `E'` contains `S`, a tower is a multiple test blow-up of `(X, S, E', 𝓒(𝔞), μ_𝓒)` if and only if it is a
multiple test blow-up of `𝔪` with centres in the strict transforms of `S`, and along it the cosupport is
`cosupp 𝔪_T ∩ S_T`. -/
theorem coeff_restrict_withE_iff (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed) (hN : 𝔪.N = univ) (hd : 1 ≤ 𝔪.d)
    {S : Set X} (hS : IsClosedSubmanifold n S) {E' : List (Set X)} (hsub : ∀ H ∈ E', H ∈ 𝔪.E)
    (hA : ∀ H ∈ 𝔪.E, H ∉ E' → S ⊆ H) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (IsGeoTestTower ({ withN (coeffMarked 𝔪) S with E := E' } : MarkedIdeal n X) T ↔
        IsGeoTestTower 𝔪 T ∧ CentresIn S T) ∧
      (IsGeoTestTower ({ withN (coeffMarked 𝔪) S with E := E' } : MarkedIdeal n X) T →
        (geoTransformAlong ({ withN (coeffMarked 𝔪) S with E := E' } : MarkedIdeal n X) T).cosupp =
          (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T S) := by
  have hle : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (IsGeoTestTower (withN (coeffMarked 𝔪) S) T ↔ IsGeoTestTower 𝔪 T ∧ CentresIn S T) ∧
      (IsGeoTestTower (withN (coeffMarked 𝔪) S) T →
        (geoTransformAlong (withN (coeffMarked 𝔪) S) T).cosupp =
          (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T S) :=
    fun T => coeff_restrict_tower_iff 𝔪 hN h𝔪.isCoherent hd hS T
  -- simple normal crossings along the test towers of `𝓒(𝔪)|_S` (they are test towers of `𝔪`)
  have hSNC : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower (withN (coeffMarked 𝔪) S) T →
      IsSNCDivisor n (geoTransformAlong (withN (coeffMarked 𝔪) S) T).E := fun T hT => by
    have h𝔪T := ((hle T).1.mp hT).1
    rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := withN (coeffMarked 𝔪) S) (𝔫 := 𝔪) rfl T]
    exact (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔪 T h𝔪T).isSNCDivisor
  have hdrop := fun (hTS : CentresIn S T) =>
    isGeoTestTower_withE_iff_of_centresIn_of_snc (withN (coeffMarked 𝔪) S) hSNC (S := S) hsub hA T hTS
  refine ⟨⟨fun hT => ?_, fun ⟨h𝔪T, hTS⟩ => ?_⟩, fun hT => ?_⟩
  · have hTS := centresIn_of_isGeoTestTower_withN_withE (coeffMarked 𝔪) S E' T hT
    exact (hle T).1.mp ((hdrop hTS).1.mp hT)
  · exact (hdrop hTS).1.mpr ((hle T).1.mpr ⟨h𝔪T, hTS⟩)
  · have hTS := centresIn_of_isGeoTestTower_withN_withE (coeffMarked 𝔪) S E' T hT
    have h𝔫T := (hdrop hTS).1.mp hT
    rw [cosupp_geoTransformAlong_withE]
    exact (hle T).2 h𝔫T

end Hironaka.CoefficientRestrictionDrop
