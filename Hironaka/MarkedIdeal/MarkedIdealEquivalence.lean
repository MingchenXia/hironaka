/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Włodarczyk's equivalence of marked ideals

Source: Włodarczyk 2005 §2.7 ("Equivalence relation for marked ideals": `(X, 𝓘, E, μ_𝓘) ≃ (X, 𝓙, E, μ_𝓙)` if `E` and
its order coincide, the supports coincide, and the two marked ideals have the same multiple test blow-ups, along
which the supports coincide) and the lemma after `le:operations` (sums are associative up to `≃`). The resolution
algorithm only sees a marked ideal through its class, so canonical resolutions are defined on classes.

* `MarkedIdeal.WEquiv 𝔪 𝔫`: same `E`; same multiple test blow-ups (`IsGeoTestTower`, for the corrected transform);
  equal cosupports along them. `.symm`, `.trans`, `.cosupp_eq`, `.isGeoResolution_iff` (the same resolutions),
  `.geoTransformAlong` (equivalence passes to the transforms along a multiple test blow-up);
* `RestrictEquiv.wEquiv`: restricted-equivalent marked ideals (`MarkedIdealOperationsAlong`, same restriction of the
  ideal to `N`) are equivalent -- from the first blowup on their transforms are EQUAL
  (`RestrictEquiv.geoTransformAlong_step_eq`);
-/

open Set

universe u

namespace Hironaka.MarkedIdealEquivalence

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal

noncomputable section

namespace MarkedIdeal

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Włodarczyk's equivalence of marked ideals** (§2.7): the same ordered `E`, the same multiple test blow-ups, and
equal cosupports along them (in particular, for the empty tower, equal cosupports). -/
def WEquiv (𝔪 𝔫 : MarkedIdeal n X) : Prop :=
  𝔪.E = 𝔫.E ∧ ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    (IsGeoTestTower 𝔪 T ↔ IsGeoTestTower 𝔫 T) ∧
      (IsGeoTestTower 𝔪 T → (geoTransformAlong 𝔪 T).cosupp = (geoTransformAlong 𝔫 T).cosupp)

variable {𝔪 𝔫 𝔬 : MarkedIdeal n X}

theorem WEquiv.trans (h₁ : WEquiv 𝔪 𝔫) (h₂ : WEquiv 𝔫 𝔬) : WEquiv 𝔪 𝔬 :=
  ⟨h₁.1.trans h₂.1, fun T => ⟨(h₁.2 T).1.trans (h₂.2 T).1, fun hT =>
    ((h₁.2 T).2 hT).trans ((h₂.2 T).2 ((h₁.2 T).1.mp hT))⟩⟩

/-- The `E` of the transform along a tower only depends on `E` and the tower. -/
theorem E_geoTransformAlong_eq (hE : 𝔪.E = 𝔫.E) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → (geoTransformAlong 𝔪 T).E = (geoTransformAlong 𝔫 T).E
  | _, .refl => hE
  | _, .step T _ _ _ => by
      rw [geoTransformAlong_step, geoTransformAlong_step, geoTransform_E, geoTransform_E,
        E_geoTransformAlong_eq hE T]

/-! ### Restricted equivalence implies equivalence -/

open MarkedIdealOperationsAlong.MarkedIdeal in
/-- **From the first blowup on, restricted-equivalent marked ideals have EQUAL transforms.** -/
theorem RestrictEquiv.geoTransformAlong_step_eq (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    {Y Z : CMfd.{u} n} → (T : BlowupTower X Y) → (C : Set Y) → (π : Z → Y) → (hπ : IsBlowupAlong n C π) →
      MarkedIdeals.MarkedIdeal.geoTransformAlong 𝔪 (.step T C π hπ) =
        MarkedIdeals.MarkedIdeal.geoTransformAlong 𝔫 (.step T C π hπ)
  | _, _, .refl, _, _, hπ => h.geoTransform_eq hN h𝔪 h𝔫 hπ.contMDiff
  | _, _, .step T C' π' hπ', C, π, hπ => by
      change (MarkedIdeals.MarkedIdeal.geoTransformAlong 𝔪 (.step T C' π' hπ')).geoTransform C π =
        (MarkedIdeals.MarkedIdeal.geoTransformAlong 𝔫 (.step T C' π' hπ')).geoTransform C π
      rw [RestrictEquiv.geoTransformAlong_step_eq h hN h𝔪 h𝔫 T C' π' hπ']

open MarkedIdealOperationsAlong.MarkedIdeal in
/-- Restricted-equivalent marked ideals have, at every stage, the same cosupport and the same admissible centres. -/
theorem RestrictEquiv.cosupp_admissible_geoTransformAlong (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
      (MarkedIdeals.MarkedIdeal.geoTransformAlong 𝔪 T).cosupp =
          (MarkedIdeals.MarkedIdeal.geoTransformAlong 𝔫 T).cosupp ∧
        ∀ C, (MarkedIdeals.MarkedIdeal.geoTransformAlong 𝔪 T).IsAdmissibleCentre C ↔
          (MarkedIdeals.MarkedIdeal.geoTransformAlong 𝔫 T).IsAdmissibleCentre C
  | _, .refl => ⟨h.cosupp_eq, fun _ => h.isAdmissibleCentre_iff⟩
  | _, .step T C π hπ => by
      rw [RestrictEquiv.geoTransformAlong_step_eq h hN h𝔪 h𝔫 T C π hπ]
      exact ⟨rfl, fun _ => Iff.rfl⟩

open MarkedIdealOperationsAlong.MarkedIdeal in
/-- **Restricted-equivalent marked ideals are equivalent** (closed `N`, coherent ideals). -/
theorem RestrictEquiv.wEquiv (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (h𝔪 : 𝔪.ideal.IsCoherent)
    (h𝔫 : 𝔫.ideal.IsCoherent) : WEquiv 𝔪 𝔫 := by
  have key : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), _ := fun T =>
    RestrictEquiv.cosupp_admissible_geoTransformAlong h hN h𝔪 h𝔫 T
  have htest : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T ↔ IsGeoTestTower 𝔫 T := by
    intro Y T
    induction T with
    | refl => exact Iff.rfl
    | step T C π hπ ih =>
      rw [isGeoTestTower_step_iff, isGeoTestTower_step_iff, ih, (key T).2 C]
  exact ⟨h.E_eq, fun T => ⟨htest T, fun _ => (key T).1⟩⟩

end MarkedIdeal

end

end Hironaka.MarkedIdealEquivalence
