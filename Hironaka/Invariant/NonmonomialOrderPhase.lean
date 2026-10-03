/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionOpen
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.CompanionReductionAlong
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Invariant.InvDomainCompanion
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The companion phase of the general step: admissible centres, and finitely many orders over a compact set

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2a of Proposition `pr:resol`; Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), Step II.B.

Two inputs of the general step's value on the side of the companion phase:

* property (8): over a compact set only finitely many orders occur, along the whole segment. This holds whichever
  form of (8) is chosen.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.NonmonomialOrderPhase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.CompanionReductionAlong Hironaka.CompanionRebase Hironaka.GermIdealOrder Hironaka.DivisorExponentAlong Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealRestrictOpen Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderCanonical Hironaka.NonmonomialOrderTail
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Admissible centres of the companion ideal along its multiple test blow-ups -/

section Admissible

variable {Z : CMfd.{u} n} {k : ℕ} {𝔫 : MarkedIdeal n Z}

/-- **Admissible centres of the companion's transform on an open set**: on every open `W''` of the last stage, `C ⊂
W''` is an admissible centre of the restriction of `𝓞(𝔫, o)_T` iff it is one of the restriction of `𝔫_T` lying over
`{ν_{𝔫_T} ≥ o}`. -/
theorem isAdmissibleCentre_pullback_val_companion_iff (hn : 0 < n) (h : IsInvDomain k 𝔫) {o : ℕ} (ho : 1 ≤ o)
    (hbound : ∀ x ∈ 𝔫.cosupp, x ∉ ordGe 𝔫 (o + 1)) {Y : CMfd.{u} n} (T : BlowupTower Z Y)
    (hT : IsGeoTestTower (companionOf n 𝔫 o) T) (W'' : Opens Y) (C : Set W'') :
    (MarkedIdeal.pullback (Subtype.val : W'' → Y) (geoTransformAlong (companionOf n 𝔫 o) T)).IsAdmissibleCentre C ↔
      (MarkedIdeal.pullback (Subtype.val : W'' → Y) (geoTransformAlong 𝔫 T)).IsAdmissibleCentre C ∧
        ∀ x ∈ C, (x : Y) ∈ ordGe (geoTransformAlong 𝔫 T) o := by
  have hcos := cosupp_companionOf_geoTransformAlong hn h ho hbound T hT
  have hE := E_geoTransformAlong_congr (companionAlong_E 𝔫.N 𝔫.E (MonomialPartAlong.nonmonomialPartAlong n 𝔫.N 𝔫.ideal 𝔫.E)
    (MonomialPartAlong.monomialPartAlong n 𝔫.N 𝔫.ideal 𝔫.E) o 𝔫.d) T
  have hT𝔫 := (CompanionOpen.companionOf_reduction hn h.isWellFormed h.isNonzeroAlongAt ho hbound T hT).1
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT𝔫
  have hdomO := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (InvDomainCompanion.isInvDomain_companionAlong hn h ho) T hT
  have hcosO := cosupp_pullback_val (geoTransformAlong (companionOf n 𝔫 o) T)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomO.isWellFormed.isCoherent hg)
    W''
  have hcos𝔫 := cosupp_pullback_val (geoTransformAlong 𝔫 T)
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdomT.isWellFormed.isCoherent hg)
    W''
  have hEp : (MarkedIdeal.pullback (Subtype.val : W'' → Y) (geoTransformAlong (companionOf n 𝔫 o) T)).E =
      (MarkedIdeal.pullback (Subtype.val : W'' → Y) (geoTransformAlong 𝔫 T)).E := by
    show List.map _ (geoTransformAlong (companionOf n 𝔫 o) T).E = List.map _ (geoTransformAlong 𝔫 T).E
    rw [hE]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hcosO, hcos] at h2
    rw [hEp] at h3
    refine ⟨⟨h1, fun x hx => ?_, h3⟩, fun x hx => (h2 hx).1⟩
    rw [hcos𝔫]
    exact (h2 hx).2
  · rintro ⟨⟨h1, h2, h3⟩, hC⟩
    refine ⟨h1, fun x hx => ?_, ?_⟩
    · rw [hcos𝔫] at h2
      rw [hcosO, hcos]
      exact ⟨hC x hx, h2 hx⟩
    · rw [hEp]
      exact h3

end Admissible

end

end Hironaka.NonmonomialOrderPhase
