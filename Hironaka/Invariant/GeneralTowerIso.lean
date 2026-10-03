/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.GeneralRepresentative
import Hironaka.Invariant.CompanionTowerIso
import Hironaka.Blowup.BlowupTowerSplitIso
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.CompanionReductionAlong
import Hironaka.Invariant.GeneralAdmissible
import Hironaka.Invariant.GeneralCanonicalTail
import Hironaka.Invariant.GeneralCompare
import Hironaka.Invariant.GeneralValue
import Hironaka.Invariant.GeneralValueOrderZero
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainCompanion
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxOrderValue
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.MonomialPartAlong
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Invariant.NonmonomialOrderTransport
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneTangentChange
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The general value along isomorphisms of towers: property (6)

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`: the resolution commutes with étale
morphisms, in particular with biholomorphisms; Bierstone--Milman 2008, Step II.

Let `χ: T' ≅ T` be an isomorphism of towers over a biholomorphism `Φ: X' ≅ X`, `𝔪` a marked ideal of the domain (`0
< n`) and `T` a canonical segment of the general value `genInv M 𝔪` (`M` a value function for the marked ideals of
maximal order). At a point `p` with `χ p` in the cosupport of positive order `o`, the general values of `Φ^*𝔪` along
`T'` at `p` and of `𝔪` along `T` at `χ p` agree: the orders and the runs agree
(`NonmonomialOrderLocal.nmOrd_geoTransformAlong_isTowerIso`,
`NonmonomialOrderRegime.regimeRun_ordRegime_isTowerIso`), the splits at the run correspond
(`IsTowerIso.exists_split`), the masks correspond (`NonmonomialOrderTransport.mem_ordMask_isTowerIso_iff`), the
companion ideal of `(Φ^*𝔪)_{T₀'}` on its mask is the pullback of that of `𝔪_{T₀}`
(`CompanionTowerIso.companionOf_isTowerIso`), and property (6) of `M` along the restricted tails -- a canonical
segment of the companion ideal by the canonical-tail theorem
(`GeneralCanonicalTail.hasGenLowerData_of_isCanonical`) -- gives the equality (`value_companionOf_isTowerIso`). At
order `0` this is `GeneralValueOrderZero.towerIso_field_of_nmOrd_eq_zero`.

## Main results

* `value_companionOf_isTowerIso`: the values of `M` for the companion ideals along an isomorphism of towers;
* **`genInv_isTowerIso_of_pos`**: property (6) of the general value at positive order;
* **`towerIso_field`**: property (6) in the shape of the field `towerIso` of `ResolutionInvariantExt.ResolutionInvariant`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralTowerIso

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.CompanionRebase Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism Hironaka.StepOneTangentChange Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderTail Hironaka.NonmonomialOrderTransport Hironaka.InvDomainCompanion Hironaka.MaxOrderValue Hironaka.GeneralValue Hironaka.GeneralCompare Hironaka.GeneralCanonicalTail Hironaka.CompanionTowerIso Hironaka.HomogenizedIdealAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### The companion values along an isomorphism of towers -/

section Companion

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {𝔪 : MarkedIdeal n X}
  {Y₀' Y₀ : CMfd.{u} n} {T₀' : BlowupTower X' Y₀'} {T₀ : BlowupTower X Y₀}
  {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀}
  {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The values of the companion ideal along an isomorphism of towers**: let `T₀' ≅ T₀` over `Φ` with last-stage map
`χ₀` and `T₁' ≅ T₁` over `χ₀`, `T₀` a multiple test blow-up of `𝔪` (in the domain, `0 < n`, `o ≥ 1`), and `W'`, `W`
opens with `q ∈ W' ↔ χ₀ q ∈ W`. If `𝓞₀ = 𝓞(𝔪_{T₀}, o)|_W` is of maximal order and `T₁|_W` is a canonical segment of
it for `M`, the values of `M` for `𝓞((Φ^*𝔪)_{T₀'}, o)|_{W'}` along `T₁'|_{W'}` and for `𝓞₀` along `T₁|_W` agree at
corresponding points of the cosupport. -/
theorem value_companionOf_isTowerIso (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) {o : ℕ}
    (ho : 1 ≤ o) (hiso : IsTowerIso Φ T₀' T₀ χ₀) (hT₀ : IsGeoTestTower 𝔪 T₀) {W' : Opens Y₀'} {W : Opens Y₀}
    (hW : ∀ q, q ∈ W' ↔ χ₀ q ∈ W)
    (hmax : IsMaximalOrderAlong
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o)).N
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o)).ideal
      (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o)).d)
    {Z' Z : CMfd.{u} n} {T₁' : BlowupTower Y₀' Z'} {T₁ : BlowupTower Y₀ Z}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z} (hχ : IsTowerIso χ₀ T₁' T₁ χ)
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o))
      (M (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o)))
      (restrict W T₁))
    (p : openPreimage T₁' W') (q : openPreimage T₁ W) (hpq : (χ p : Z) = q)
    (hq : q ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → Y₀)
      (companionOf n (geoTransformAlong 𝔪 T₀) o)) (restrict W T₁)).cosupp) :
    M (MarkedIdeal.pullback (Subtype.val : W' → Y₀')
        (companionOf n (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T₀') o)) (restrict W' T₁') p =
      M (MarkedIdeal.pullback (Subtype.val : W → Y₀) (companionOf n (geoTransformAlong 𝔪 T₀) o))
        (restrict W T₁) q := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  have hdomW := isInvDomain_pullback_val_companionAlong hn hdomT W ho
  have hξ := isTowerIso_restrictOpens hW hχ (isTowerIso_mem_openPreimage_iff hχ hW)
  rw [companionOf_isTowerIso Φ hn h ho hiso hT₀ W' W (diffeoOpens χ₀ W' W hW) fun _ => rfl]
  have hpq' : diffeoOpens χ (openPreimage T₁' W') (openPreimage T₁ W) (isTowerIso_mem_openPreimage_iff hχ hW) p = q :=
    Subtype.ext hpq
  have key := hM.towerIso _ _ hdomW hmax _ _ _ hξ hcan p (by rw [hpq']; exact hq)
  rw [key, hpq']

end Companion

/-! ### Property (6) of the general value -/

section TowerIso

variable {X X' : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Property (6) of the general value at positive order**: for `𝔪` in the domain (`0 < n`), an isomorphism of towers
`χ : T' ≅ T` over a biholomorphism `Φ : X' ≅ X` and `T` a canonical segment of the general value which is a multiple test
blow-up, at a point `p` with `χ p` in the cosupport of positive order, the general value of `Φ^*𝔪` along `T'` at `p` is that of
`𝔪` along `T` at `χ p`. -/
theorem genInv_isTowerIso_of_pos (hM : IsMaxOrderValue n k M) (hn : 0 < n) {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 (genInv M 𝔪) T) (p : Y')
    (hp : χ p ∈ (geoTransformAlong 𝔪 T).cosupp) (hpos : 0 < nmOrd (geoTransformAlong 𝔪 T) (χ p)) :
    genInv M (MarkedIdeal.pullback Φ 𝔪) T' p = genInv M 𝔪 T (χ p) := by
  obtain ⟨o, ho⟩ : ∃ o, nmOrd (geoTransformAlong 𝔪 T) (χ p) = o := ⟨_, rfl⟩
  have ho1 : 1 ≤ o := by omega
  have ho0 : o ≠ 0 := by omega
  have hν : nmOrd (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T') p = o :=
    (nmOrd_geoTransformAlong_isTowerIso hn Φ h hiso hT p).trans ho
  rw [genInv_of_nmOrd_ne_zero M _ T' hν ho0, genInv_of_nmOrd_ne_zero M 𝔪 T ho ho0,
    regimeRun_ordRegime_isTowerIso hn Φ h o hiso hT p]
  -- the lower data at `χ p`
  obtain ⟨hW, hdom, hmax, hcan₀, hcos₀⟩ := hasGenLowerData_of_isCanonical M hM hn h T hT hcan (χ p) hp o ho ho1
  -- the splits correspond
  obtain ⟨χ₀, h₀, h₁⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split hiso (regimeRun (OrdRegime 𝔪 o) T (χ p))
  obtain ⟨hT₀, -⟩ := (isGeoTestTower_iff_head_tail 𝔪 T (regimeRun (OrdRegime 𝔪 o) T (χ p))).mp hT
  have hdomT₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h _ hT₀
  have hT₀' : IsGeoTestTower (MarkedIdeal.pullback Φ 𝔪) (head T' (regimeRun (OrdRegime 𝔪 o) T (χ p))) :=
    (IsTowerIso.isGeoTestTower_iff Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent h₀).mpr hT₀
  have hdomT₀' := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (InvDomainTowerAlong.isInvDomain_pullback Φ h) _ hT₀'
  have hWiff := mem_ordMask_isTowerIso_iff hn Φ h h₀ hT₀ o
  have hp' : (tail T' (regimeRun (OrdRegime 𝔪 o) T (χ p))).proj p ∈
      ordMask (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) (head T' (regimeRun (OrdRegime 𝔪 o) T (χ p)))) o := by
    rw [hWiff, IsTowerIso.proj_comm h₁ p]
    exact hW
  rw [genLowerValue_eq_of_mem M _ hp', genLowerValue_eq_of_mem M 𝔪 hW]
  rw [compAt_eq_pullback hn o _ hdomT₀] at hmax hcan₀ hcos₀ ⊢
  rw [compAt_eq_pullback hn o _ hdomT₀']
  rw [value_companionOf_isTowerIso Φ hM hn h ho1 h₀ hT₀ hWiff hmax h₁ hcan₀ ⟨p, hp'⟩ ⟨χ p, hW⟩ rfl hcos₀]

/-- **Property (6) of the general value in the shape of the field `towerIso`** of
`ResolutionInvariantExt.ResolutionInvariant`: along canonical segments of the general value (`M` a value function
for the marked ideals of maximal order, `0 < n`), at every point (order `0`:
`GeneralValueOrderZero.towerIso_field_of_nmOrd_eq_zero`). -/
theorem towerIso_field (hM : IsMaxOrderValue n k M) (hn : 0 < n)
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (𝔪 : MarkedIdeal n X) (h : IsInvDomain k 𝔪)
    {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y) (hiso : IsTowerIso Φ T' T χ)
    (hcan : IsCanonical 𝔪 (genInv M 𝔪) T) (p : Y') (hp : χ p ∈ (geoTransformAlong 𝔪 T).cosupp) :
    genInv M (MarkedIdeal.pullback Φ 𝔪) T' p = genInv M 𝔪 T (χ p) := by
  rcases Nat.eq_zero_or_pos (nmOrd (geoTransformAlong 𝔪 T) (χ p)) with h0 | hpos
  · exact GeneralValueOrderZero.towerIso_field_of_nmOrd_eq_zero hM hn Φ 𝔪 h T' T χ hiso hcan p hp h0
  · exact genInv_isTowerIso_of_pos hM hn h Φ hiso
      (GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h T hcan) hcan p hp hpos

end TowerIso

end

end Hironaka.GeneralTowerIso
