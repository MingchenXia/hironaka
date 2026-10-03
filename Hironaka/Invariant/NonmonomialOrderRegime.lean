/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.StepOneRegime
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.MarkedIdeal.TransformOffCentre
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The regime of the general step: the stage at which a point reached its order of the nonmonomial part

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2a of Proposition `pr:resol` and the lemma on étale
morphisms; Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Step II.B.

At a point `y` of the cosupport along a tower `T` where the order `o = ord_y(𝓝(𝔪_T))` of the nonmonomial part
(`NonmonomialOrderLocal.nmOrd`) is positive, the general step computes the value from the maximal-order invariant of the
companion ideal formed at the stage at which the images of `y` first had order `o`, restricted to a neighbourhood `W` of
the image of `y` there on which the order is at most `o` on the cosupport, along the rest of `T`.  That stage is the start
of the run of `y` in the regime `OrdRegime 𝔪 o` (`StepOneRegime.regimeRun`).  This module provides the regime and its
calculus:

* `OrdRegime 𝔪 o T y`: `y` lies in the cosupport of `𝔪_T` and `nmOrd 𝔪_T y = o`;
  `ordRegime_step_iff_of_notMem`: off the centre of a test blowup the regime of the image is the regime of the point;
* `regimeRun_restrict_of`, `regimeRun_isTowerIso_of`: the runs of `StepOneRegime` under restriction to opens and
  along isomorphisms of towers when the regimes correspond only along towers with a property inherited by prefixes
  (e.g. multiple test blow-ups) -- **`regimeRun_ordRegime_restrict`**, **`regimeRun_ordRegime_isTowerIso`**: for
  `OrdRegime` along multiple test blow-ups
* **`ordRegime_and_le_regimeRun`** (the mask theorem, analogue of `StepOneMaskTower`): if `T₀ T₁` is a multiple test
  blow-up of `𝔪`, `W` an open set of the last stage of `T₀` on which the order is `≤ o` on the cosupport (`o ≥ 1`), and
  `T₁|_W` a multiple test blow-up of the companion ideal `𝓞(𝔪_{T₀}|_W, o)`, then every point of the cosupport over `W` of
  order `≥ o` lies in the regime `OrdRegime 𝔪 o` and its run is at least the length of `T₁` -- it reached `o` at the last
  stage of `T₀` or before; in particular nearby points of the same order entered the regime no later;
* `CentresOrdGt 𝔪 o T`: every centre of `T` lies in `{ord ≥ o + 1}`; **`centresAvoid_of_centresOrdGt`** (the steps
  between two starts miss the mask): along a multiple test blow-up whose centres lie in `{ord ≥ o + 1}`, they miss
  an open set `W` on which the order is `≤ o` on the cosupport, and the bound persists over `W`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.NonmonomialOrderRegime

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.CompanionRebase Hironaka.GermIdealOrder Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealRestrictOpen Hironaka.RestrictEmptyTower Hironaka.BlowupTowerIsomorphism Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal
open Hironaka.ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {n : ℕ}

/-! ### Runs along towers with a property inherited by prefixes -/

section Run

variable {X : CMfd.{u} n}

/-- **The run along a restriction to an open set**, for regimes that correspond only along towers with a property `Q`
inherited by prefixes (e.g. multiple test blow-ups). -/
theorem regimeRun_restrict_of (U : Opens X) (P : Regime X) (P' : Regime (CMfd.of (n := n) U))
    (Q : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop)
    (hQ : ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      Q (.step T C π hπ) → Q T)
    (hP : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), Q T → ∀ p : openPreimage T U, P' (restrict U T) p ↔ P T p) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), Q T → ∀ p : openPreimage T U,
      regimeRun P' (restrict U T) p = regimeRun P T p
  | _, .refl, _, _ => rfl
  | _, .step T C π hπ, hT, p => by
      classical
      have hT' := hQ T C π hπ hT
      have hp : P' (restrict U T) ⟨π p.1, p.2⟩ ↔ P T (π p.1) := hP T hT' ⟨π p.1, p.2⟩
      have ih := regimeRun_restrict_of U P P' Q hQ hP T hT' ⟨π p.1, p.2⟩
      show (if P' (restrict U T) ⟨π p.1, p.2⟩ then regimeRun P' (restrict U T) ⟨π p.1, p.2⟩ + 1 else 0) =
        if P T (π p.1) then regimeRun P T (π p.1) + 1 else 0
      by_cases h : P T (π p.1)
      · rw [if_pos (hp.mpr h), if_pos h, ih]
      · rw [if_neg (fun h' => h (hp.mp h')), if_neg h]

/-- **The run along an isomorphism of towers**, for regimes that correspond along isomorphisms of towers with a property
`Q` (of the target tower) inherited by prefixes. -/
theorem regimeRun_isTowerIso_of {X' : CMfd.{u} n} {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    (P : Regime X) (P' : Regime X') (Q : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop)
    (hQ : ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      Q (.step T C π hπ) → Q T)
    (hP : ∀ {Y' Y : CMfd.{u} n} (S' : BlowupTower X' Y') (S : BlowupTower X Y)
      (ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y), IsTowerIso Φ S' S ψ → Q S →
        ∀ p, P' S' p ↔ P S (ψ p))
    {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (h : IsTowerIso Φ T' T χ) (hT : Q T) :
    ∀ p, regimeRun P' T' p = regimeRun P T (χ p) := by
  classical
  induction h with
  | refl => exact fun _ => rfl
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro p
    have hT' := hQ T C π hπ hT
    rw [regimeRun_step, regimeRun_step, hcomm]
    have hp := hP T' T χ h hT' (π' p)
    by_cases hq : P T (χ (π' p))
    · rw [if_pos (hp.mpr hq), if_pos hq, ih hT']
    · rw [if_neg (fun h' => hq (hp.mp h')), if_neg hq]

end Run

/-! ### The regime -/

section Regime

variable {X : CMfd.{u} n}

/-- **The regime "order `o`"** of the general step: the point lies in the cosupport of the transform and the order of
the nonmonomial part of the transform there is `o`. -/
def OrdRegime (𝔪 : MarkedIdeal n X) (o : ℕ) : Regime X :=
  fun {_} T y => y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ nmOrd (geoTransformAlong 𝔪 T) y = o

theorem ordRegime_iff (𝔪 : MarkedIdeal n X) (o : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    OrdRegime 𝔪 o T y ↔ y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ nmOrd (geoTransformAlong 𝔪 T) y = o :=
  Iff.rfl

/-- **Off the centre of a test blowup the regime does not change**: for `T` followed by a test blowup along `C`
(`𝔪` in the domain, `n > 0`) and `π z ∉ C`, `z` is in the regime iff `π z` is. -/
theorem ordRegime_step_iff_of_notMem (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    (o : ℕ) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower 𝔪 (.step T C π hπ)) {z : Z} (hz : π z ∉ C) :
    OrdRegime 𝔪 o (.step T C π hπ) z ↔ OrdRegime 𝔪 o T (π z) := by
  obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hTT
  show z ∈ ((geoTransformAlong 𝔪 T).geoTransform C π).cosupp ∧
      nmOrd ((geoTransformAlong 𝔪 T).geoTransform C π) z = o ↔ _
  rw [TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong 𝔪 T)
      hdomT.isWellFormed.isClosedSubmanifold_N.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomT.isWellFormed.isCoherent hg)
      hπ hz,
    nmOrd_geoTransform_of_notMem hn hdomT hC hπ hz]
  rfl

/-- **The regime under restriction to an open set** (`𝔪` in the domain, `n > 0`, `T` a multiple test blow-up). -/
theorem ordRegime_restrict_iff (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) (o : ℕ)
    (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (p : openPreimage T U) :
    OrdRegime (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) o (restrict U T) p ↔
      OrdRegime 𝔪 o T p := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  show p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)).cosupp ∧
      nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)) p = o ↔ _
  rw [geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T hT,
    cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hdomT.isWellFormed.isCoherent hg),
    nmOrd_pullback_val hn hdomT.isWellFormed hdomT.isNonzeroAlongAt (openPreimage T U) p]
  rfl

/-- **The run under restriction to an open set** (`𝔪` in the domain, `n > 0`, `T` a multiple test blow-up): the run of
`p` in `OrdRegime (𝔪|_U) o` along `T|_U` is its run in `OrdRegime 𝔪 o` along `T`. -/
theorem regimeRun_ordRegime_restrict (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) (o : ℕ)
    (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (p : openPreimage T U) :
    regimeRun (OrdRegime (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) o) (restrict U T) p =
      regimeRun (OrdRegime 𝔪 o) T p :=
  regimeRun_restrict_of U (OrdRegime 𝔪 o) _ (fun T => IsGeoTestTower 𝔪 T)
    (fun T C π hπ hT => ((isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT).1)
    (fun T hT p => ordRegime_restrict_iff hn h o U T hT p) T hT p

/-- **The regime along an isomorphism of towers** (`𝔪` in the domain, `n > 0`, `S` a multiple test blow-up). -/
theorem ordRegime_isTowerIso_iff (hn : 0 < n) {X' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    (o : ℕ) {Y' Y : CMfd.{u} n} {S' : BlowupTower X' Y'} {S : BlowupTower X Y}
    {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ S' S ψ)
    (hS : IsGeoTestTower 𝔪 S) (p : Y') :
    OrdRegime (MarkedIdeal.pullback Φ 𝔪) o S' p ↔ OrdRegime 𝔪 o S (ψ p) := by
  show p ∈ (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) S').cosupp ∧
      nmOrd (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) S') p = o ↔ _
  rw [IsTowerIso.cosupp_geoTransformAlong Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent hiso hS,
    nmOrd_geoTransformAlong_isTowerIso hn Φ h hiso hS p]
  rfl

/-- **The run along an isomorphism of towers** (`𝔪` in the domain, `n > 0`, `T` a multiple test blow-up): the run of
`p` in `OrdRegime (Φ^*𝔪) o` along `T'` is the run of `χ p` in `OrdRegime 𝔪 o` along `T`. -/
theorem regimeRun_ordRegime_isTowerIso (hn : 0 < n) {X' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    (o : ℕ) {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ T' T χ)
    (hT : IsGeoTestTower 𝔪 T) (p : Y') :
    regimeRun (OrdRegime (MarkedIdeal.pullback Φ 𝔪) o) T' p = regimeRun (OrdRegime 𝔪 o) T (χ p) :=
  regimeRun_isTowerIso_of (OrdRegime 𝔪 o) (OrdRegime (MarkedIdeal.pullback Φ 𝔪) o) (fun T => IsGeoTestTower 𝔪 T)
    (fun T C π hπ hT => ((isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT).1)
    (fun _ _ _ hiso hS p => ordRegime_isTowerIso_iff hn Φ h o hiso hS p) hiso hT p

end Regime

/-! ### The mask theorem -/

section Mask

variable {X : CMfd.{u} n}

/-- **Over the mask the order stays `≤ o`** (`𝔫` in the domain, `n > 0`, `o ≥ 1`): if the order is `≤ o` on
`cosupp 𝔫 ∩ W` and `S|_W` is a multiple test blow-up of the companion ideal `𝓞(𝔫|_W, o)`, then along the multiple test
blow-up `S` of `𝔫` the order is `≤ o` at the cosupport points over `W`. -/
theorem notMem_ordGe_of_mask (hn : 0 < n) {k : ℕ} {Y₀ : CMfd.{u} n} {𝔫 : MarkedIdeal n Y₀} (h : IsInvDomain k 𝔫)
    {o : ℕ} (ho : 1 ≤ o) (W : Opens Y₀) (hbound : ∀ x ∈ 𝔫.cosupp, x ∈ W → x ∉ ordGe 𝔫 (o + 1))
    {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y) (hS : IsGeoTestTower 𝔫 S)
    (hSW : IsGeoTestTower (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔫) o)
      (restrict W S)) :
    ∀ z ∈ (geoTransformAlong 𝔫 S).cosupp, S.proj z ∈ W → z ∉ ordGe (geoTransformAlong 𝔫 S) (o + 1) := by
  have hW := InvDomainTowerAlong.isInvDomain_pullback_val W h
  have hboundW : ∀ x ∈ (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔫).cosupp,
      x ∉ ordGe (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔫) (o + 1) := by
    intro x hx hx'
    rw [cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      h.isWellFormed.isCoherent hg)] at hx
    exact hbound x hx x.2 ((mem_ordGe_pullback_val_iff hn h.isWellFormed h.isNonzeroAlongAt W (o + 1) x).mp hx')
  obtain ⟨-, hb, -⟩ := companionOf_tower_facts (Z := CMfd.of (n := n) W) hn hW ho hboundW (restrict W S) hSW
  rw [geoTransformAlong_restrict W h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent S hS] at hb
  intro z hz hzW hzq
  have hdomS := InvDomainTowerAlong.isInvDomain_geoTransformAlong h S hS
  let z' : openPreimage S W := ⟨z, hzW⟩
  have hz' : z' ∈ (MarkedIdeal.pullback (Subtype.val : openPreimage S W → Y) (geoTransformAlong 𝔫 S)).cosupp := by
    rw [cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hdomS.isWellFormed.isCoherent hg)]
    exact hz
  exact hb z' hz' ((mem_ordGe_pullback_val_iff hn hdomS.isWellFormed hdomS.isNonzeroAlongAt _ (o + 1) z').mpr hzq)

/-- **Over the mask the centres lie in `{ord ≥ o}`**: under the hypotheses of `notMem_ordGe_of_mask`, if moreover the
restriction of the next blowup (along `C`) to the open preimage of `W` is a test blowup of the transform of the companion
ideal, the points of `C` over `W` have order `≥ o` (the cosupport of the companion's transform lies in `{ord ≥ o}`). -/
theorem mem_ordGe_of_mem_centre_of_mask (hn : 0 < n) {k : ℕ} {Y₀ : CMfd.{u} n} {𝔫 : MarkedIdeal n Y₀}
    (h : IsInvDomain k 𝔫) {o : ℕ} (ho : 1 ≤ o) (W : Opens Y₀) (hbound : ∀ x ∈ 𝔫.cosupp, x ∈ W → x ∉ ordGe 𝔫 (o + 1))
    {Y Z : CMfd.{u} n} (S : BlowupTower Y₀ Y) (hS : IsGeoTestTower 𝔫 S) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π)
    (hSW : IsGeoTestTower (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔫) o)
      (restrict W (.step S C π hπ))) :
    ∀ w ∈ C, S.proj w ∈ W → w ∈ ordGe (geoTransformAlong 𝔫 S) o := by
  have hW := InvDomainTowerAlong.isInvDomain_pullback_val W h
  have hboundW : ∀ x ∈ (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔫).cosupp,
      x ∉ ordGe (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → Y₀) 𝔫) (o + 1) := by
    intro x hx hx'
    rw [cosupp_pullback_val _ (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      h.isWellFormed.isCoherent hg)] at hx
    exact hbound x hx x.2 ((mem_ordGe_pullback_val_iff hn h.isWellFormed h.isNonzeroAlongAt W (o + 1) x).mp hx')
  obtain ⟨hSW', hadm⟩ := (isGeoTestTower_step_iff _ _ _ _ _).mp hSW
  obtain ⟨-, -, hcos⟩ := companionOf_tower_facts (Z := CMfd.of (n := n) W) hn hW ho hboundW (restrict W S) hSW'
  rw [geoTransformAlong_restrict W h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent S hS] at hcos
  have hdomS := InvDomainTowerAlong.isInvDomain_geoTransformAlong h S hS
  intro w hw hwW
  let w' : openPreimage S W := ⟨w, hwW⟩
  have hw' : w' ∈ ((↑) ⁻¹' C : Set (openPreimage S W)) := hw
  exact (mem_ordGe_pullback_val_iff hn hdomS.isWellFormed hdomS.isNonzeroAlongAt _ o w').mp
    (hcos (hadm.2.1 hw')).1

/-- **The mask theorem** (the general step's analogue of `StepOneMaskTower.stepRegime_and_le_regimeRun_of_mem_lowerMask`):
let `𝔪` be in the domain (`n > 0`), `o ≥ 1`, `T₀ T₁` a multiple test blow-up of `𝔪`, `W` an open set of the last stage of
`T₀` on which the order of the nonmonomial part of `𝔪_{T₀}` is `≤ o` at the points of the cosupport, and `T₁|_W` a multiple
test blow-up of the companion ideal `𝓞(𝔪_{T₀}|_W, o)`.  Then every point `z` of the cosupport of `𝔪_{T₀T₁}` over `W` of
order `≥ o` is in the regime `OrdRegime 𝔪 o`, and its run is at least the length of `T₁`: it reached the order `o` at
the last stage of `T₀` or before. -/
theorem ordRegime_and_le_regimeRun (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) {o : ℕ}
    (ho : 1 ≤ o) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (W : Opens Y₀)
    (hbound : ∀ x ∈ (geoTransformAlong 𝔪 T₀).cosupp, x ∈ W → x ∉ ordGe (geoTransformAlong 𝔪 T₀) (o + 1)) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y), IsGeoTestTower 𝔪 (T₀.append T₁) →
      IsGeoTestTower (companionOf n (M := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong 𝔪 T₀)) o) (restrict W T₁) →
      ∀ z, z ∈ (geoTransformAlong 𝔪 (T₀.append T₁)).cosupp → T₁.proj z ∈ W →
        o ≤ nmOrd (geoTransformAlong 𝔪 (T₀.append T₁)) z →
        OrdRegime 𝔪 o (T₀.append T₁) z ∧ T₁.length ≤ regimeRun (OrdRegime 𝔪 o) (T₀.append T₁) z := by
  -- the order at the last stage, over the mask
  have key : ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y), IsGeoTestTower 𝔪 (T₀.append S) →
      IsGeoTestTower (companionOf n (M := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → Y₀) (geoTransformAlong 𝔪 T₀)) o) (restrict W S) →
      ∀ z ∈ (geoTransformAlong 𝔪 (T₀.append S)).cosupp, S.proj z ∈ W →
        z ∉ ordGe (geoTransformAlong 𝔪 (T₀.append S)) (o + 1) := by
    intro Y S hS hSW
    obtain ⟨hT₀, hS'⟩ := (isGeoTestTower_append_iff 𝔪 T₀ S).mp hS
    have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
    rw [geoTransformAlong_append 𝔪 T₀ S]
    exact notMem_ordGe_of_mask hn hdom₀ ho W hbound S hS' hSW
  intro Y T₁
  induction T₁ with
  | refl =>
    intro hT hTW z hz hzW hzo
    exact ⟨⟨hz, le_antisymm (nmOrd_le_of_notMem (key .refl hT hTW z hz hzW)) hzo⟩, Nat.zero_le _⟩
  | @step Y Z S C π hπ ih =>
    intro hT hTW z hz hzW hzo
    have hregz : OrdRegime 𝔪 o (T₀.append (.step S C π hπ)) z :=
      ⟨hz, le_antisymm (nmOrd_le_of_notMem (key (.step S C π hπ) hT hTW z hz hzW)) hzo⟩
    have hT' : IsGeoTestTower 𝔪 (.step (T₀.append S) C π hπ) := hT
    obtain ⟨hTS, hC⟩ := (isGeoTestTower_step_iff 𝔪 _ C π hπ).mp hT'
    obtain ⟨hSW, -⟩ := (isGeoTestTower_step_iff _ _ _ _ _).mp hTW
    have hdomS := InvDomainTowerAlong.isInvDomain_geoTransformAlong h _ hTS
    have hwW : S.proj (π z) ∈ W := hzW
    have hz' : z ∈ ((geoTransformAlong 𝔪 (T₀.append S)).geoTransform C π).cosupp := hz
    have hzo' : o ≤ nmOrd ((geoTransformAlong 𝔪 (T₀.append S)).geoTransform C π) z := hzo
    -- the image of `z` is in the cosupport and has order `≥ o`
    have hwcos : π z ∈ (geoTransformAlong 𝔪 (T₀.append S)).cosupp := by
      by_cases hwC : π z ∈ C
      · exact hC.2.1 hwC
      · exact (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong 𝔪 (T₀.append S))
          hdomS.isWellFormed.isClosedSubmanifold_N.1
          (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
            hdomS.isWellFormed.isCoherent hg) hπ hwC).mp hz'
    have hwo : o ≤ nmOrd (geoTransformAlong 𝔪 (T₀.append S)) (π z) := by
      by_cases hwC : π z ∈ C
      · obtain ⟨hT₀, hS'⟩ := (isGeoTestTower_append_iff 𝔪 T₀ S).mp hTS
        have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
        have hmem := mem_ordGe_of_mem_centre_of_mask hn hdom₀ ho W hbound S hS' C π hπ hTW (π z) hwC hwW
        rw [← geoTransformAlong_append 𝔪 T₀ S] at hmem
        exact (mem_ordGe_iff hdomS.isWellFormed hdomS.isNonzeroAlongAt
          ((geoTransformAlong 𝔪 (T₀.append S)).cosupp_subset_N hwcos) o).mp hmem
      · rw [← nmOrd_geoTransform_of_notMem hn hdomS hC hπ hwC]
        exact hzo'
    obtain ⟨hregw, hrunw⟩ := ih hTS hSW (π z) hwcos hwW hwo
    refine ⟨hregz, ?_⟩
    rw [BlowupTower.length_step, BlowupTower.append_step, regimeRun_step_of (OrdRegime 𝔪 o) _ C π hπ hregw]
    exact Nat.succ_le_succ hrunw

end Mask

/-! ### The steps between two starts miss the mask -/

section Avoid

variable {X : CMfd.{u} n}

/-- **Every centre of `T` lies in `{ord ≥ o + 1}`** (the order of the nonmonomial part of the transform at that stage). -/
def CentresOrdGt (𝔪 : MarkedIdeal n X) (o : ℕ) : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => CentresOrdGt 𝔪 o T ∧ C ⊆ ordGe (geoTransformAlong 𝔪 T) (o + 1)

theorem centresOrdGt_step_iff (𝔪 : MarkedIdeal n X) (o : ℕ) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    CentresOrdGt 𝔪 o (.step T C π hπ) ↔ CentresOrdGt 𝔪 o T ∧ C ⊆ ordGe (geoTransformAlong 𝔪 T) (o + 1) :=
  Iff.rfl

/-- **The steps whose centres lie in `{ord ≥ o + 1}` miss an open set on which the order is `≤ o`** (`𝔪` in the domain,
`n > 0`): if the order is `≤ o` on `cosupp 𝔪 ∩ W` and every centre of the multiple test blow-up `T` lies in `{ord ≥
o + 1}`, the centres miss the preimages of `W` and the order stays `≤ o` at the cosupport points over `W` -- by
induction, a centre is in the cosupport, where over `W` the order is `≤ o`, and off the centres the order is that of
the image. -/
theorem centresAvoid_of_centresOrdGt (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) {o : ℕ}
    (W : Opens X) (hbound : ∀ x ∈ 𝔪.cosupp, x ∈ W → x ∉ ordGe 𝔪 (o + 1)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → CentresOrdGt 𝔪 o T →
      CentresAvoid W T ∧
        ∀ z ∈ (geoTransformAlong 𝔪 T).cosupp, T.proj z ∈ W → z ∉ ordGe (geoTransformAlong 𝔪 T) (o + 1)
  | _, .refl, _, _ => ⟨trivial, hbound⟩
  | _, .step T C π hπ, hT, hc => by
      obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hcT, hCo⟩ := (centresOrdGt_step_iff 𝔪 o T C π hπ).mp hc
      obtain ⟨hav, hb⟩ := centresAvoid_of_centresOrdGt hn h W hbound T hTT hcT
      have hdisj : Disjoint C (T.proj ⁻¹' (W : Set X)) :=
        Set.disjoint_left.mpr fun c hcC hcW => hb c (hC.2.1 hcC) hcW (hCo hcC)
      refine ⟨(centresAvoid_step_iff W T C π hπ).mpr ⟨hav, hdisj⟩, fun z hz hzW => ?_⟩
      have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hTT
      have hzW' : π z ∈ T.proj ⁻¹' (W : Set X) := hzW
      have hzC : π z ∉ C := fun hzC => Set.disjoint_left.mp hdisj hzC hzW'
      have hz' : π z ∈ (geoTransformAlong 𝔪 T).cosupp :=
        (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong 𝔪 T)
          hdomT.isWellFormed.isClosedSubmanifold_N.1
          (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
            hdomT.isWellFormed.isCoherent hg) hπ hzC).mp hz
      show z ∉ ordGe ((geoTransformAlong 𝔪 T).geoTransform C π) (o + 1)
      rw [mem_ordGe_geoTransform_of_notMem hn hdomT hC hπ (o + 1) hzC]
      exact hb (π z) hz' hzW

end Avoid

end

end Hironaka.NonmonomialOrderRegime
