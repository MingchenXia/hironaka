import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Włodarczyk's equivalence of marked ideals

Blueprint `hir:marked-equivalence`, `hir:marked-equivalence-basic`, `hir:marked-sum-associative`
(`blueprint/src/hironaka.tex`, Hironaka phase H1/H4).  Source: Włodarczyk 2005 §2.7 ("Equivalence relation for marked
ideals": `(X, 𝓘, E, μ_𝓘) ≃ (X, 𝓙, E, μ_𝓙)` if `E` and its order coincide, the supports coincide, and the two marked
ideals have the same multiple test blow-ups, along which the supports coincide) and the lemma after `le:operations`
(sums are associative up to `≃`).  The resolution algorithm only sees a marked ideal through its class, so canonical
resolutions are defined on classes (design note D10).

* `MarkedIdeal.WEquiv 𝔪 𝔫`: same `E`; same multiple test blow-ups (`IsGeoTestTower`, for the corrected transform);
  equal cosupports along them.  `WEquiv.refl`, `.symm`, `.trans`, `.cosupp_eq`, `.isGeoResolution_iff` (the same
  resolutions), `.geoTransformAlong` (equivalence passes to the transforms along a multiple test blow-up);
* `RestrictEquiv.wEquiv`: restricted-equivalent marked ideals (`MarkedIdealOperationsAlong`, same restriction of the
  ideal to `N`) are equivalent -- from the first blowup on their transforms are EQUAL
  (`RestrictEquiv.geoTransformAlong_step_eq`);
* `N = M`: `WEquiv.add_left` (equivalence is compatible with sums) and `add_assoc_wEquiv`
  (`(𝔪₁ + 𝔪₂) + 𝔪₃ ≃ 𝔪₁ + (𝔪₂ + 𝔪₃)`, Włodarczyk's associativity lemma; marks `≥ 1`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.

Sorry-free.
-/

open Set

universe u

namespace Hironaka.MarkedIdealEquivalence

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal

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

theorem WEquiv.refl (𝔪 : MarkedIdeal n X) : WEquiv 𝔪 𝔪 :=
  ⟨rfl, fun _ => ⟨Iff.rfl, fun _ => rfl⟩⟩

theorem WEquiv.symm (h : WEquiv 𝔪 𝔫) : WEquiv 𝔫 𝔪 :=
  ⟨h.1.symm, fun T => ⟨(h.2 T).1.symm, fun hT => ((h.2 T).2 ((h.2 T).1.mpr hT)).symm⟩⟩

theorem WEquiv.trans (h₁ : WEquiv 𝔪 𝔫) (h₂ : WEquiv 𝔫 𝔬) : WEquiv 𝔪 𝔬 :=
  ⟨h₁.1.trans h₂.1, fun T => ⟨(h₁.2 T).1.trans (h₂.2 T).1, fun hT =>
    ((h₁.2 T).2 hT).trans ((h₂.2 T).2 ((h₁.2 T).1.mp hT))⟩⟩

/-- Equivalent marked ideals have the same cosupport. -/
theorem WEquiv.cosupp_eq (h : WEquiv 𝔪 𝔫) : 𝔪.cosupp = 𝔫.cosupp :=
  (h.2 (BlowupTower.refl : BlowupTower X X)).2 trivial

/-- **Equivalent marked ideals have the same resolutions.** -/
theorem WEquiv.isGeoResolution_iff (h : WEquiv 𝔪 𝔫) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    IsGeoResolution 𝔪 T ↔ IsGeoResolution 𝔫 T := by
  refine ⟨fun hT => ⟨(h.2 T).1.mp hT.1, ?_⟩, fun hT => ⟨(h.2 T).1.mpr hT.1, ?_⟩⟩
  · rw [← (h.2 T).2 hT.1]; exact hT.2
  · rw [(h.2 T).2 ((h.2 T).1.mpr hT.1)]; exact hT.2

/-- The `E` of the transform along a tower only depends on `E` and the tower. -/
theorem E_geoTransformAlong_eq (hE : 𝔪.E = 𝔫.E) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → (geoTransformAlong 𝔪 T).E = (geoTransformAlong 𝔫 T).E
  | _, .refl => hE
  | _, .step T _ _ _ => by
      rw [geoTransformAlong_step, geoTransformAlong_step, geoTransform_E, geoTransform_E,
        E_geoTransformAlong_eq hE T]

/-- **Equivalence passes to the transforms along a multiple test blow-up.** -/
theorem WEquiv.geoTransformAlong (h : WEquiv 𝔪 𝔫) {Y : CMfd.{u} n} {T : BlowupTower X Y}
    (hT : IsGeoTestTower 𝔪 T) : WEquiv (MarkedIdeals.MarkedIdeal.geoTransformAlong 𝔪 T)
      (MarkedIdeals.MarkedIdeal.geoTransformAlong 𝔫 T) := by
  have hT' : IsGeoTestTower 𝔫 T := (h.2 T).1.mp hT
  refine ⟨E_geoTransformAlong_eq h.1 T, fun S => ⟨?_, fun hS => ?_⟩⟩
  · have h1 := isGeoTestTower_append_iff 𝔪 T S
    have h2 := isGeoTestTower_append_iff 𝔫 T S
    have h3 := (h.2 (T.append S)).1
    constructor
    · intro hS
      exact (h2.mp (h3.mp (h1.mpr ⟨hT, hS⟩))).2
    · intro hS
      exact (h1.mp (h3.mpr (h2.mpr ⟨hT', hS⟩))).2
  · have hTS : IsGeoTestTower 𝔪 (T.append S) := (isGeoTestTower_append_iff 𝔪 T S).mpr ⟨hT, hS⟩
    rw [← geoTransformAlong_append, ← geoTransformAlong_append]
    exact (h.2 (T.append S)).2 hTS

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

/-! ### Sums (`N = M`) -/

open MarkedIdealOperationsTransform.MarkedIdeal

/-- **Equivalence is compatible with sums** (`N = M`, same `E`, coherent ideals, marks `≥ 1`). -/
theorem WEquiv.add_left {𝔪₁ 𝔪₁' 𝔪₂ : MarkedIdeal n X} (h : WEquiv 𝔪₁ 𝔪₁') (hp : IsAmbientPair 𝔪₁ 𝔪₂)
    (hp' : IsAmbientPair 𝔪₁' 𝔪₂) (hd₁ : 1 ≤ 𝔪₁.d) (hd₁' : 1 ≤ 𝔪₁'.d) (hd₂ : 1 ≤ 𝔪₂.d) :
    WEquiv (add 𝔪₁ 𝔪₂) (add 𝔪₁' 𝔪₂) := by
  refine ⟨h.1, fun T => ?_⟩
  obtain ⟨hiff, heq⟩ := geoTransformAlong_add 𝔪₁ 𝔪₂ hp hd₁ hd₂ T
  obtain ⟨hiff', heq'⟩ := geoTransformAlong_add 𝔪₁' 𝔪₂ hp' hd₁' hd₂ T
  refine ⟨by rw [hiff, hiff', (h.2 T).1], fun hT => ?_⟩
  obtain ⟨hT₁, hT₂⟩ := hiff.mp hT
  obtain ⟨he, hpair⟩ := heq hT₁ hT₂
  obtain ⟨he', hpair'⟩ := heq' ((h.2 T).1.mp hT₁) hT₂
  rw [he, he', cosupp_add hpair.N₁ hpair.N₂ hpair.coh₁ hpair.coh₂
      (by rw [d_geoTransformAlong]; exact hd₁) (by rw [d_geoTransformAlong]; exact hd₂),
    cosupp_add hpair'.N₁ hpair'.N₂ hpair'.coh₁ hpair'.coh₂
      (by rw [d_geoTransformAlong]; exact hd₁') (by rw [d_geoTransformAlong]; exact hd₂),
    (h.2 T).2 hT₁]

/-- The sum of an ambient pair is coherent. -/
theorem isCoherent_add_of_isAmbientPair {𝔪₁ 𝔪₂ : MarkedIdeal n X} (h : IsAmbientPair 𝔪₁ 𝔪₂) :
    (add 𝔪₁ 𝔪₂).ideal.IsCoherent :=
  RestrictedIdealExtension.isCoherent_sumIdeal (GermIdealPullbackCalculus.isCoherent_idealPow h.coh₁ _)
    (GermIdealPullbackCalculus.isCoherent_idealPow h.coh₂ _)

/-- **Sums are associative up to equivalence** (Włodarczyk, the lemma after `le:operations`; `N = M`, same `E`,
coherent ideals, marks `≥ 1`): `(𝔪₁ + 𝔪₂) + 𝔪₃ ≃ 𝔪₁ + (𝔪₂ + 𝔪₃)`. -/
theorem add_assoc_wEquiv {𝔪₁ 𝔪₂ 𝔪₃ : MarkedIdeal n X} (h₁₂ : IsAmbientPair 𝔪₁ 𝔪₂)
    (h₂₃ : IsAmbientPair 𝔪₂ 𝔪₃) (hd₁ : 1 ≤ 𝔪₁.d) (hd₂ : 1 ≤ 𝔪₂.d) (hd₃ : 1 ≤ 𝔪₃.d) :
    WEquiv (add (add 𝔪₁ 𝔪₂) 𝔪₃) (add 𝔪₁ (add 𝔪₂ 𝔪₃)) := by
  have hA : IsAmbientPair (add 𝔪₁ 𝔪₂) 𝔪₃ :=
    ⟨h₁₂.N₁, h₂₃.N₂, h₁₂.E.trans h₂₃.E, isCoherent_add_of_isAmbientPair h₁₂, h₂₃.coh₂⟩
  have hB : IsAmbientPair 𝔪₁ (add 𝔪₂ 𝔪₃) := ⟨h₁₂.N₁, h₂₃.N₁, h₁₂.E, h₁₂.coh₁, isCoherent_add_of_isAmbientPair h₂₃⟩
  have hdA : 1 ≤ (add 𝔪₁ 𝔪₂).d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdB : 1 ≤ (add 𝔪₂ 𝔪₃).d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  refine ⟨rfl, fun T => ?_⟩
  obtain ⟨iA3, eA3⟩ := geoTransformAlong_add (add 𝔪₁ 𝔪₂) 𝔪₃ hA hdA hd₃ T
  obtain ⟨i12, e12⟩ := geoTransformAlong_add 𝔪₁ 𝔪₂ h₁₂ hd₁ hd₂ T
  obtain ⟨i1B, e1B⟩ := geoTransformAlong_add 𝔪₁ (add 𝔪₂ 𝔪₃) hB hd₁ hdB T
  obtain ⟨i23, e23⟩ := geoTransformAlong_add 𝔪₂ 𝔪₃ h₂₃ hd₂ hd₃ T
  refine ⟨by rw [iA3, i12, i1B, i23, and_assoc], fun hT => ?_⟩
  obtain ⟨hTA, hT₃⟩ := iA3.mp hT
  obtain ⟨hT₁, hT₂⟩ := i12.mp hTA
  have hTB : IsGeoTestTower (add 𝔪₂ 𝔪₃) T := i23.mpr ⟨hT₂, hT₃⟩
  obtain ⟨eqA3, pA3⟩ := eA3 hTA hT₃
  obtain ⟨eq12, p12⟩ := e12 hT₁ hT₂
  obtain ⟨eq1B, p1B⟩ := e1B hT₁ hTB
  obtain ⟨eq23, p23⟩ := e23 hT₂ hT₃
  have hdT : ∀ {𝔬 : MarkedIdeal n X}, 1 ≤ 𝔬.d → 1 ≤ (MarkedIdeals.MarkedIdeal.geoTransformAlong 𝔬 T).d :=
    fun h => by rw [d_geoTransformAlong]; exact h
  rw [eqA3, cosupp_add pA3.N₁ pA3.N₂ pA3.coh₁ pA3.coh₂ (hdT hdA) (hdT hd₃), eq12,
    cosupp_add p12.N₁ p12.N₂ p12.coh₁ p12.coh₂ (hdT hd₁) (hdT hd₂), eq1B,
    cosupp_add p1B.N₁ p1B.N₂ p1B.coh₁ p1B.coh₂ (hdT hd₁) (hdT hdB), eq23,
    cosupp_add p23.N₁ p23.N₂ p23.coh₁ p23.coh₂ (hdT hd₂) (hdT hd₃), inter_assoc]

end MarkedIdeal

end

end Hironaka.MarkedIdealEquivalence
