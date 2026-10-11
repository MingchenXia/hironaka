/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneWellFounded
import Hironaka.Invariant.ResolutionCentreCounting

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.TowerPreimageCompact
open Hironaka
noncomputable section
open Hironaka HolomorphicIdealSheaves BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms ResolutionInvariantSpec
variable {n : ℕ} {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}

/-- **Along a multiple test blow-up `T S` the points of the cosupport lie over the cosupport at `T`** (closed submanifold `N`,
coherent ideal; one step at a time, `StepOneWellFounded.proj_mem_cosupp_step`). -/
theorem proj_mem_cosupp_append (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) {Y₀ : CMfd.{u} n}
    (T : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y), IsGeoTestTower 𝔪 (T.append S) →
      ∀ z ∈ (geoTransformAlong 𝔪 (T.append S)).cosupp, S.proj z ∈ (geoTransformAlong 𝔪 T).cosupp
  | _, .refl, _, z, hz => hz
  | _, .step S C π hπ, hT, z, hz => by
      have hT' : IsGeoTestTower 𝔪 (.step (T.append S) C π hπ) := hT
      have hπz := StepOneWellFounded.proj_mem_cosupp_step hN h𝔞 (T.append S) C π hπ hT' hz
      exact proj_mem_cosupp_append hN h𝔞 T S hT'.1 (π z) hπz

open Classical in
/-- **After the stage `T` the centres meeting `K` are counted against the compact part of the cosupport**: along a multiple
test blow-up `T S` (closed submanifold `N`, coherent ideal), a centre of `S` meets the preimage of `T⁻¹K` iff it meets the
preimage of `T⁻¹K ∩ cosupp 𝔪_T` (the centres are admissible, hence in the cosupport, which lies over the cosupport at `T`). -/
theorem countCentresMeeting_eq_inter_cosupp (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (K : Set X)
    {Y₀ : CMfd.{u} n} (T : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y), IsGeoTestTower 𝔪 (T.append S) →
      countCentresMeeting (T.proj ⁻¹' K) S = countCentresMeeting (T.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 T).cosupp) S
  | _, .refl, _ => rfl
  | _, .step S C π hπ, hT => by
      have hT' : IsGeoTestTower 𝔪 (.step (T.append S) C π hπ) := hT
      obtain ⟨hTS, hC⟩ := (isGeoTestTower_step_iff 𝔪 (T.append S) C π hπ).mp hT'
      have ih := countCentresMeeting_eq_inter_cosupp hN h𝔞 K T S hTS
      have hiff : (C ∩ S.proj ⁻¹' (T.proj ⁻¹' K)).Nonempty ↔
          (C ∩ S.proj ⁻¹' (T.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 T).cosupp)).Nonempty := by
        constructor
        · rintro ⟨c, hcC, hcK⟩
          exact ⟨c, hcC, hcK, proj_mem_cosupp_append hN h𝔞 T S hTS c (hC.2.1 hcC)⟩
        · rintro ⟨c, hcC, hcK, -⟩
          exact ⟨c, hcC, hcK⟩
      show countCentresMeeting (T.proj ⁻¹' K) S + (if (C ∩ S.proj ⁻¹' (T.proj ⁻¹' K)).Nonempty then 1 else 0) =
        countCentresMeeting (T.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 T).cosupp) S +
          (if (C ∩ S.proj ⁻¹' (T.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 T).cosupp)).Nonempty then 1 else 0)
      rw [ih]
      by_cases h1 : (C ∩ S.proj ⁻¹' (T.proj ⁻¹' K)).Nonempty
      · rw [if_pos h1, if_pos (hiff.mp h1)]
      · rw [if_neg h1, if_neg (fun h2 => h1 (hiff.mpr h2))]


end
end Hironaka.TowerPreimageCompact
