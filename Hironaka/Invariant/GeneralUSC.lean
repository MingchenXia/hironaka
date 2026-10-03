/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.GeneralCanonicalTail
import Hironaka.Invariant.StepOneUSC
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.GeneralValue
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxOrderValue
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.NonmonomialOrderCanonical
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialOrderMonomialCanonical
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneRegime
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Property (2) of the general value: upper semicontinuity

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 2a: the invariant `(ν, inv_𝓞)` is
upper semicontinuous because `ν` is and, among the nearby points of the same order, the values are those of the
maximal-order invariant of one companion ideal, which is upper semicontinuous by Step 1.

Let `𝔪` lie in the domain (`0 < n`), `M` a value function for the marked ideals of maximal order
(`MaxOrderValue.IsMaxOrderValue`) and `T` a canonical segment of the general value `genInv M 𝔪` which is a multiple
test blow-up. At a point `y` of the cosupport of order `o ≥ 1`, the nearby points of the cosupport of order `o` lie
over the mask `W` of the start of `y` and in the cosupport of the companion ideal formed there along the restricted
tail (`GeneralCanonicalTail.mem_cosupp_compAt_iff`), where the general value is `(o, M)` of that companion ideal
(`GeneralCanonicalTail.genInv_eq_of_mem_cosupp_compAt`), and `M` is upper semicontinuous along the restricted tail,
a canonical segment of the companion ideal (property (2) of `M`, the canonical-tail theorem):
`genInv_eventually_le_of_pos`. At points of order `0` this is
`NonmonomialOrderMonomialCanonical.eventually_le_of_nmOrd_eq_zero`, and
`NonmonomialOrderCanonical.isInvUSCOn_of_ordMonotone` reduces upper semicontinuity to points of the same order:
**`genInv_usc`**.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralUSC

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdealRestrictOpen Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderCanonical Hironaka.NonmonomialOrderTail Hironaka.HomogenizedIdealAlong Hironaka.MaxOrderValue Hironaka.GeneralValue Hironaka.GeneralCanonicalTail Hironaka.ResolutionInvariantOrder
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n} {k : ℕ} {𝔪 : MarkedIdeal n X} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Upper semicontinuity among the points of the same positive order**: along a canonical segment `T` of the general value
which is a multiple test blow-up, near a point `y` of order `o ≥ 1` of the cosupport, the points of the cosupport of order `o`
have values `≤` that of `y`. -/
theorem genInv_eventually_le_of_pos (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 (genInv M 𝔪) T) {y : Y}
    (hy : y ∈ (geoTransformAlong 𝔪 T).cosupp) {o : ℕ} (hyo : nmOrd (geoTransformAlong 𝔪 T) y = o) (ho : 1 ≤ o) :
    ∀ᶠ y' in 𝓝 y, y' ∈ (geoTransformAlong 𝔪 T).cosupp → nmOrd (geoTransformAlong 𝔪 T) y' = o →
      genInv M 𝔪 T y' ≤ genInv M 𝔪 T y := by
  have hf : OrdMonotone 𝔪 (genInv M 𝔪) := ordMonotone_genInv M 𝔪
  have hD := hasGenLowerData_of_isCanonical M hM hn h T hT hcan
  obtain ⟨hW, hdom, hmax, hcan₀, hcos₀⟩ := hD y hy o hyo ho
  have hTW := isGeoTestTower_companion_tail_of_canonical hn h hf ho T hT hcan y
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_iff_head_tail 𝔪 T (regimeRun (OrdRegime 𝔪 o) T y)).mp hT
  -- upper semicontinuity of `M` along the restricted tail, pushed to the last stage
  have husc := hM.usc _ hdom hmax _ hcan₀ ⟨y, hW⟩ hcos₀
  have hev := StepOneUSC.eventually_forall_mem_of_eventually (openPreimage (tail T (regimeRun (OrdRegime 𝔪 o) T y))
    (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T y))) o)) (x := y) hW husc
  have hopen : ∀ᶠ y' in 𝓝 y, y' ∈ openPreimage (tail T (regimeRun (OrdRegime 𝔪 o) T y))
      (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T y))) o) :=
    (Opens.isOpen _).mem_nhds (show y ∈ openPreimage (tail T (regimeRun (OrdRegime 𝔪 o) T y))
      (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T y))) o) from hW)
  filter_upwards [hev, hopen] with y' hy' hy'W hy'cos hy'o
  have hq : (⟨y', hy'W⟩ : openPreimage (tail T (regimeRun (OrdRegime 𝔪 o) T y))
      (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T y))) o)) ∈
      (geoTransformAlong (compAt 𝔪 o (head T (regimeRun (OrdRegime 𝔪 o) T y)))
        (restrict (ordMask (geoTransformAlong 𝔪 (head T (regimeRun (OrdRegime 𝔪 o) T y))) o)
          (tail T (regimeRun (OrdRegime 𝔪 o) T y)))).cosupp := by
    refine (mem_cosupp_compAt_iff hn h ho _ _ hT₀ hT₁ hTW ⟨y', hy'W⟩).mpr ⟨?_, ?_⟩
    · rw [← geoTransformAlong_head_tail 𝔪 T]; exact hy'cos
    · rw [← geoTransformAlong_head_tail 𝔪 T]; exact hy'o
  rw [genInv_eq_of_mem_cosupp_compAt hM hn h T hT hcan hD hy hyo ho rfl hcan₀ _ hq,
    genInv_eq_of_mem_cosupp_compAt hM hn h T hT hcan hD hy hyo ho rfl hcan₀ _ hcos₀, Prod.Lex.toLex_le_toLex]
  refine Or.inr ⟨rfl, ?_⟩
  exact Sum.Lex.inr_le_inr_iff.mpr (WithTop.coe_le_coe.mpr (hy' hy'W hq))

/-- **Property (2) of the general value**: along a canonical segment of the general value which is a multiple test blow-up,
the value is upper semicontinuous on the cosupport. -/
theorem genInv_usc (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (hcan : IsCanonical 𝔪 (genInv M 𝔪) T) :
    IsInvUSCOn (genInv M 𝔪 T) (geoTransformAlong 𝔪 T).cosupp := by
  have hf : OrdMonotone 𝔪 (genInv M 𝔪) := ordMonotone_genInv M 𝔪
  refine isInvUSCOn_of_ordMonotone hn h hf T hT fun y hy => ?_
  rcases Nat.eq_zero_or_pos (nmOrd (geoTransformAlong 𝔪 T) y) with h0 | hpos
  · have hv : NonmonomialOrderMonomialCanonical.OrdZeroValue 𝔪 (genInv M 𝔪)
        (fun w => toLex ((0 : ℕ), (toLex (Sum.inl w) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))) :=
      ordZeroValue_genInv M 𝔪
    have hev := NonmonomialOrderMonomialCanonical.eventually_le_of_nmOrd_eq_zero (f := genInv M 𝔪)
      (ψ := fun w => toLex ((0 : ℕ), (toLex (Sum.inl w) : WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ))) hn h
      NonmonomialOrderMonomialCanonical.strictMono_toLex_zero_inl hv hT hy h0
    filter_upwards [hev] with y' hy' hy'cos hy'o
    exact hy' hy'cos (hy'o.trans h0)
  · exact genInv_eventually_le_of_pos hM hn h T hT hcan hy rfl hpos

end

end Hironaka.GeneralUSC
