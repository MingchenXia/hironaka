/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Invariant.SmoothCentreInvariant
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Invariant.InvDomainRebase
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.MonomialPartEtale
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneRegime
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The order of the nonmonomial part, its regime and its mask under the operations of the general step

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), §2.4 (commutativity with étale morphisms) and Step 2a of
Proposition `pr:resol`; Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Step II.B.

Properties (4'), (5), (6), (7) of the general step's value (`ResolutionInvariantExt.ResolutionInvariant`) compare values
computed for an empty prefix and the re-based marked ideal, for a marked ideal and its restriction to an open set, along an
isomorphism of towers, and for two restricted-equivalent representatives.  On the side of the first entry of the value
(the order `ν` of the nonmonomial part, `NonmonomialOrderLocal.nmOrd`) and of the data it determines -- the regime
`NonmonomialOrderRegime.OrdRegime 𝔪 o`, its run and the mask `NonmonomialOrderTail.ordMask` -- this module proves:

* (7) **`ordGe_geoTransformAlong_congr`**, `nmOrd_geoTransformAlong_congr`, **`ordRegime_congr`** (the regimes are equal, so
  the runs are), `ordMask_geoTransformAlong_congr`: restricted-equivalent marked ideals have the same `ν`, regime, run and
  mask along every tower (the companion ideal: `CompanionRebase.companionOf_congr`);
* (5) **`mem_ordMask_restrict_iff`**: the mask commutes with restriction to open sets along restricted multiple test
  blow-ups (`ν`, the regime and its run: `NonmonomialOrderRegime.ordRegime_restrict_iff`, `regimeRun_ordRegime_restrict`);
* (6) **`mem_ordMask_isTowerIso_iff`**: the mask along isomorphisms of towers (the regime and its run:
  `NonmonomialOrderRegime.ordRegime_isTowerIso_iff`, `regimeRun_ordRegime_isTowerIso`; the companion:
  `CompanionTowerIso`);
* (4') **`ordRegime_append_iff`**: the regime along `P S` is the regime of `𝔪_P` along `S` (for every `P`, the
  hypothesis of `StepOneEmptyPrefix.regimeRun_append_of_lt` / `_of_eq`); along a tower `P` with only empty centres,
  **`ordRegime_isEmptyTower_iff`** (the regime is that of the image at the base),
  **`regimeRun_ordRegime_isEmptyTower`** (the run is `length P` or `0`), **`ordMask_isEmptyTower`** (the mask is the
  preimage of the mask at the base; the companion:
  `CompanionRebase.restrictEquiv_companionOf_geoTransformAlong_of_isEmptyTower`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.NonmonomialOrderTransport

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.MonomialPartEtale Hironaka.GermIdealOrder Hironaka.DivisorExponentAlong Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderTail Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)

noncomputable section

variable {n : ℕ}

/-! ### (7) Restricted-equivalent representatives -/

section Representative

variable {X : CMfd.{u} n} {𝔪 𝔫 : MarkedIdeal n X}

/-- **Restricted-equivalent marked ideals have the same points of order `≥ q`** (`N` closed): the nonmonomial part only
depends on `Res_N 𝔞` (`MonomialPartEtale.nonmonomialPartAlong_congr`), and `N`, `E` agree. -/
theorem ordGe_congr (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (q : ℕ) : ordGe 𝔪 q = ordGe 𝔫 q := by
  have hNN := nonmonomialPartAlong_congr (E := 𝔪.E) hN hEq.le hEq.ge
  show cosupport n 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) q =
    cosupport n 𝔫.N (nonmonomialPartAlong n 𝔫.N 𝔫.ideal 𝔫.E) q
  rw [← hEq.N_eq, ← hEq.E_eq, hNN]

/-- **Along every tower** restricted-equivalent marked ideals (closed `N`, coherent ideals) have the same points of order
`≥ q`: at the base by `ordGe_congr`, after one blowup their transforms are equal
(`MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq`). -/
theorem ordGe_geoTransformAlong_congr (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (h𝔪 : 𝔪.ideal.IsCoherent)
    (h𝔫 : 𝔫.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (q : ℕ), ordGe (geoTransformAlong 𝔪 T) q = ordGe (geoTransformAlong 𝔫 T) q
  | _, .refl, q => ordGe_congr hEq hN q
  | _, .step T C π hπ, _ => by
      rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq hEq hN h𝔪 h𝔫 T C π hπ]

theorem nmOrd_geoTransformAlong_congr (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (h𝔪 : 𝔪.ideal.IsCoherent)
    (h𝔫 : 𝔫.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    nmOrd (geoTransformAlong 𝔪 T) y = nmOrd (geoTransformAlong 𝔫 T) y :=
  nmOrd_congr fun q => by rw [ordGe_geoTransformAlong_congr hEq hN h𝔪 h𝔫 T q]

/-- **Restricted-equivalent marked ideals have the same regimes** `OrdRegime · o` (closed `N`, coherent ideals): the
cosupports (`MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong`) and the orders agree
along every tower. -/
theorem ordRegime_congr (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (h𝔪 : 𝔪.ideal.IsCoherent)
    (h𝔫 : 𝔫.ideal.IsCoherent) (o : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    OrdRegime 𝔪 o T y ↔ OrdRegime 𝔫 o T y := by
  rw [ordRegime_iff, ordRegime_iff,
    (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hEq hN h𝔪 h𝔫 T).1,
    nmOrd_geoTransformAlong_congr hEq hN h𝔪 h𝔫 T y]

/-- **Hence the runs agree.** -/
theorem regimeRun_ordRegime_congr (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (h𝔪 : 𝔪.ideal.IsCoherent)
    (h𝔫 : 𝔫.ideal.IsCoherent) (o : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y), regimeRun (OrdRegime 𝔪 o) T y = regimeRun (OrdRegime 𝔫 o) T y
  | _, .refl, _ => rfl
  | _, .step T C π hπ, z => by
      by_cases hq : OrdRegime 𝔪 o T (π z)
      · rw [regimeRun_step_of (OrdRegime 𝔪 o) T C π hπ hq,
          regimeRun_step_of (OrdRegime 𝔫 o) T C π hπ ((ordRegime_congr hEq hN h𝔪 h𝔫 o T (π z)).mp hq),
          regimeRun_ordRegime_congr hEq hN h𝔪 h𝔫 o T (π z)]
      · rw [regimeRun_step_of_not (OrdRegime 𝔪 o) T C π hπ hq,
          regimeRun_step_of_not (OrdRegime 𝔫 o) T C π hπ
            (fun h' => hq ((ordRegime_congr hEq hN h𝔪 h𝔫 o T (π z)).mpr h'))]

/-- **Restricted-equivalent marked ideals have the same masks** along every tower. -/
theorem ordMask_geoTransformAlong_congr (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (h𝔪 : 𝔪.ideal.IsCoherent)
    (h𝔫 : 𝔫.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) (o : ℕ) :
    ordMask (geoTransformAlong 𝔪 T) o = ordMask (geoTransformAlong 𝔫 T) o := by
  ext x
  show x ∈ (closure (ordGe (geoTransformAlong 𝔪 T) (o + 1)))ᶜ ↔ x ∈ (closure (ordGe (geoTransformAlong 𝔫 T) (o + 1)))ᶜ
  rw [ordGe_geoTransformAlong_congr hEq hN h𝔪 h𝔫 T (o + 1)]

end Representative

/-! ### (5) Restriction to open sets and (6) isomorphisms of towers -/

section Local

variable {X : CMfd.{u} n} {k : ℕ} {𝔪 : MarkedIdeal n X}

/-- **The mask commutes with restriction to open sets** (`𝔪` in the domain, `n > 0`): along a multiple test blow-up `T` of
`𝔪` and an open `U ⊂ X`, a point of the open preimage of `U` is in the mask of the transform of `𝔪|_U` along `T|_U` iff it
is in the mask of `𝔪_T` -- the transform of `𝔪|_U` is the restriction of `𝔪_T`
(`MarkedIdealRestrictOpen.geoTransformAlong_restrict`), whose points of order `≥ o + 1` are the traces of those of `𝔪_T`
(`NonmonomialOrderLocal.mem_ordGe_pullback_val_iff`), and the closure commutes with the trace on an open set. -/
theorem mem_ordMask_restrict_iff (hn : 0 < n) (h : IsInvDomain k 𝔪) (U : Opens X) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (o : ℕ) (p : openPreimage T U) :
    p ∈ ordMask (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)) o ↔
      (p : Y) ∈ ordMask (geoTransformAlong 𝔪 T) o := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hset : ordGe (M := CMfd.of (n := n) (openPreimage T U))
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)) (o + 1) =
      (Subtype.val : openPreimage T U → Y) ⁻¹' ordGe (geoTransformAlong 𝔪 T) (o + 1) := by
    rw [geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T hT]
    ext q
    exact mem_ordGe_pullback_val_iff hn hdomT.isWellFormed hdomT.isNonzeroAlongAt (openPreimage T U) (o + 1) q
  show p ∈ (closure (ordGe (M := CMfd.of (n := n) (openPreimage T U))
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)) (o + 1)))ᶜ ↔
    (p : Y) ∈ (closure (ordGe (geoTransformAlong 𝔪 T) (o + 1)))ᶜ
  have hcl := (openPreimage T U).isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val (ordGe (geoTransformAlong 𝔪 T) (o + 1))
  rw [hset]
  exact not_congr (Set.ext_iff.mp hcl.symm p)

/-- **The mask along isomorphisms of towers** (`𝔪` in the domain, `n > 0`): for `χ : T' → T` over a biholomorphism `Φ` and
`T` a multiple test blow-up of `𝔪`, `p` is in the mask of `(Φ^*𝔪)_{T'}` iff `χ p` is in the mask of `𝔪_T`
(`NonmonomialOrderLocal.mem_ordGe_geoTransformAlong_isTowerIso`; `χ` is a homeomorphism). -/
theorem mem_ordMask_isTowerIso_iff (hn : 0 < n) {X' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (h : IsInvDomain k 𝔪) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower 𝔪 T) (o : ℕ) (p : Y') :
    p ∈ ordMask (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T') o ↔ χ p ∈ ordMask (geoTransformAlong 𝔪 T) o := by
  have hset : ordGe (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T') (o + 1) =
      χ.toHomeomorph ⁻¹' ordGe (geoTransformAlong 𝔪 T) (o + 1) := by
    ext q
    exact mem_ordGe_geoTransformAlong_isTowerIso hn Φ h hiso hT (o + 1) q
  show p ∈ (closure (ordGe (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T') (o + 1)))ᶜ ↔
    χ p ∈ (closure (ordGe (geoTransformAlong 𝔪 T) (o + 1)))ᶜ
  rw [hset, ← χ.toHomeomorph.preimage_closure]
  rfl

end Local

/-! ### (4') Empty prefixes -/

section Prefix

variable {X : CMfd.{u} n} {k : ℕ} {𝔪 : MarkedIdeal n X}

/-- **The regime along a concatenation** `P S` is the regime of the transform `𝔪_P` along `S`, for every `P`
(`geoTransformAlong_append`); the hypothesis `hQ` of `StepOneEmptyPrefix.regimeRun_append_of_lt` / `_of_eq`. -/
theorem ordRegime_append_iff (𝔪 : MarkedIdeal n X) (o : ℕ) {Y₁ Y : CMfd.{u} n} (P : BlowupTower X Y₁)
    (S : BlowupTower Y₁ Y) (z : Y) : OrdRegime 𝔪 o (P.append S) z ↔ OrdRegime (geoTransformAlong 𝔪 P) o S z := by
  rw [ordRegime_iff, ordRegime_iff, geoTransformAlong_append]

/-- **Along a tower with only empty centres** a point is in the regime `o` iff its image at the base is (`𝔪` in the
domain, `n > 0`): the cosupport (`SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower`) and the order
(`NonmonomialOrderLocal.mem_ordGe_geoTransformAlong_of_isEmptyTower`) are those of the image. -/
theorem ordRegime_isEmptyTower_iff (hn : 0 < n) (h : IsInvDomain k 𝔪) (o : ℕ) {Y : CMfd.{u} n} (P : BlowupTower X Y)
    (hP : IsEmptyTower P) (z : Y) : OrdRegime 𝔪 o P z ↔ OrdRegime 𝔪 o .refl (P.proj z) := by
  rw [ordRegime_iff, ordRegime_iff,
    SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower 𝔪 h.isWellFormed.isClosedSubmanifold_N
      h.isWellFormed.isCoherent P hP z,
    nmOrd_congr fun q => mem_ordGe_geoTransformAlong_of_isEmptyTower hn h q P hP z]
  rfl

open Classical in
/-- **The run along a tower with only empty centres** is the whole tower if the image at the base is in the regime, and
`0` otherwise (`𝔪` in the domain, `n > 0`). -/
theorem regimeRun_ordRegime_isEmptyTower (hn : 0 < n) (h : IsInvDomain k 𝔪) (o : ℕ) :
    ∀ {Y : CMfd.{u} n} (P : BlowupTower X Y), IsEmptyTower P → ∀ z : Y,
      regimeRun (OrdRegime 𝔪 o) P z = if OrdRegime 𝔪 o .refl (P.proj z) then P.length else 0
  | _, .refl, _, z => by
      rw [regimeRun_refl]
      split_ifs <;> rfl
  | _, .step P C π hπ, hP, z => by
      obtain ⟨hP', hC⟩ : IsEmptyTower P ∧ C = ∅ := hP
      have hiff := ordRegime_isEmptyTower_iff hn h o P hP' (π z)
      have hproj : (BlowupTower.step P C π hπ).proj z = P.proj (π z) := rfl
      rw [hproj, BlowupTower.length_step]
      by_cases hb : OrdRegime 𝔪 o .refl (P.proj (π z))
      · rw [regimeRun_step_of (OrdRegime 𝔪 o) P C π hπ (hiff.mpr hb),
          regimeRun_ordRegime_isEmptyTower hn h o P hP' (π z), if_pos hb, if_pos hb]
      · rw [regimeRun_step_of_not (OrdRegime 𝔪 o) P C π hπ (fun h' => hb (hiff.mp h')), if_neg hb]

/-- **The mask along a tower with only empty centres** is the preimage of the mask at the base (`𝔪` in the domain,
`n > 0`). -/
theorem ordMask_isEmptyTower (hn : 0 < n) (h : IsInvDomain k 𝔪) (o : ℕ) {Y : CMfd.{u} n} (P : BlowupTower X Y)
    (hP : IsEmptyTower P) : ordMask (geoTransformAlong 𝔪 P) o = openPreimage P (ordMask 𝔪 o) := by
  have hdomP := InvDomainRebase.isInvDomain_geoTransformAlong_of_isEmptyTower h P hP
  ext z
  show z ∈ ordMask (geoTransformAlong 𝔪 P) o ↔ P.proj z ∈ ordMask 𝔪 o
  rw [mem_ordMask_iff hn hdomP.isWellFormed hdomP.isNonzeroAlongAt]
  rw [mem_ordMask_iff hn h.isWellFormed h.isNonzeroAlongAt, mem_ordGe_geoTransformAlong_of_isEmptyTower hn h (o + 1) P hP z]

end Prefix

end

end Hironaka.NonmonomialOrderTransport
