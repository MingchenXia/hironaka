/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.MarkedIdeal.TransformOffCentre
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Dropping members of `E` along multiple test blow-ups

Sources: Włodarczyk 2005, Step 1a (passing from `E` to `E_S`, the members not containing `S`) and Step 1b (the
members of the original `E` are dropped once they miss the cosupport); Bierstone--Milman 2008, §6.

Only the divisor of a transform depends on `E`; admissibility compares through normal-crossings comparison
(`NormalCrossingsComparison`).

* `geoTransformAlong_withE`: along any tower, `(M, N, E', 𝔞, d)` and `(M, N, E, 𝔞, d)` have transforms with the same
  submanifold, ideal and mark (hence cosupport).
* **Deleting the members that contain every centre**: if every member of `E` missing from `E'` contains `S`, then
  along towers with centres in the strict transforms of `S` the test towers of the two marked ideals coincide (`E`
  simple normal crossings, the marked ideal well formed), and the dropped members keep containing the strict
  transforms of `S`.
* **Deleting members away from the cosupport**: if every member of `E` missing from `E'` is disjoint from the
  cosupport, the test towers coincide.
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.DropMembers

open Hironaka.BlowupSequences NormalCrossings BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal BlowupStrictSubmanifold NormalCrossingsComparison CoefficientIdealRestriction HomogenizedGlueingTower

noncomputable section

/-! ### The transforms of `(M, N, E', 𝔞, d)` -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Only the divisor depends on `E`**: along every tower the transforms of `(M, N, E', 𝔞, d)` and of `𝔪` have the same
submanifold, ideal and mark. -/
theorem geoTransformAlong_withE (𝔪 : MarkedIdeal n X) (E' : List (Set X)) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).N = (geoTransformAlong 𝔪 T).N ∧
      (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).ideal = (geoTransformAlong 𝔪 T).ideal ∧
      (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).d = (geoTransformAlong 𝔪 T).d
  | _, .refl => ⟨rfl, rfl, rfl⟩
  | _, .step T C π hπ => by
    obtain ⟨hN, hI, hd⟩ := geoTransformAlong_withE 𝔪 E' T
    simp only [geoTransformAlong_step, geoTransform]
    exact ⟨by rw [hN], by rw [hN, hI, hd], hd⟩

/-- Along every tower the two transforms have the same cosupport. -/
theorem cosupp_geoTransformAlong_withE (𝔪 : MarkedIdeal n X) (E' : List (Set X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) :
    (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).cosupp = (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨hN, hI, hd⟩ := geoTransformAlong_withE 𝔪 E' T
  simp only [cosupp, hN, hI, hd]

/-- Admissibility for the transform of `(M, N, E', 𝔞, d)` is admissibility for the transform of `𝔪` with its divisor
replaced. -/
theorem isAdmissibleCentre_geoTransformAlong_withE_iff (𝔪 : MarkedIdeal n X) (E' : List (Set X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) :
    (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).IsAdmissibleCentre C ↔
      ({ geoTransformAlong 𝔪 T with E := (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E } :
        MarkedIdeal n Y).IsAdmissibleCentre C := by
  have hc := cosupp_geoTransformAlong_withE 𝔪 E' T
  unfold IsAdmissibleCentre
  rw [hc]
  rfl

theorem isGeoTestTower_withE_iff_of_centresIn_of_snc (𝔪 : MarkedIdeal n X)
    (hSNC : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
      IsSNCDivisor n (geoTransformAlong 𝔪 T).E) {E' : List (Set X)}
    {S : Set X} (hsub : ∀ H ∈ E', H ∈ 𝔪.E) (hA : ∀ H ∈ 𝔪.E, H ∉ E' → S ⊆ H) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → CentresIn S T →
      (IsGeoTestTower ({ 𝔪 with E := E' } : MarkedIdeal n X) T ↔ IsGeoTestTower 𝔪 T) ∧
      (∀ H ∈ (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E, H ∈ (geoTransformAlong 𝔪 T).E) ∧
      (∀ H ∈ (geoTransformAlong 𝔪 T).E,
        H ∉ (geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).E → strictAlong T S ⊆ H)
  | _, .refl, _ => ⟨Iff.rfl, hsub, hA⟩
  | _, .step T C π hπ, hT => by
    obtain ⟨hTS, hCS⟩ := (centresIn_step_iff S T C π hπ).mp hT
    obtain ⟨hiff, hsubT, hAT⟩ := isGeoTestTower_withE_iff_of_centresIn_of_snc 𝔪 hSNC hsub hA T hTS
    refine ⟨?_, forall_mem_transformE π C hsubT, ?_⟩
    · have hadm : IsGeoTestTower 𝔪 T →
          ((geoTransformAlong ({ 𝔪 with E := E' } : MarkedIdeal n X) T).IsAdmissibleCentre C ↔
            (geoTransformAlong 𝔪 T).IsAdmissibleCentre C) := fun h𝔪T => by
        rw [isAdmissibleCentre_geoTransformAlong_withE_iff]
        exact isAdmissibleCentre_withE_iff _ (hSNC T h𝔪T) hsubT fun H hH hH' => hCS.trans (hAT H hH hH')
      simp only [isGeoTestTower_step_iff]
      constructor
      · rintro ⟨h1, h2⟩
        have h𝔪T := hiff.mp h1
        exact ⟨h𝔪T, (hadm h𝔪T).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨hiff.mpr h1, (hadm h1).mpr h2⟩
    · rw [strictAlong_step]
      exact forall_notMem_transformE π C hAT

end Tower

end

end Hironaka.DropMembers
