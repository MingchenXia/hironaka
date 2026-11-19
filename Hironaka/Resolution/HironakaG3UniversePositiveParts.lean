import Hironaka.Resolution.HironakaG3UniversePullbackSum
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Invariant.GeneralValue
import Hironaka.Resolution.HironakaG3UniverseNonmonomialOrder
import Hironaka.Resolution.HironakaSmoothSubmersionRelativePartsCompanion
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeGeometry
import Hironaka.MarkedIdeal.RestrictedIdealExtension
import Hironaka.Resolution.HironakaG3UniverseOpenDiffeo
import Hironaka.Resolution.HironakaG3UniverseGeoTransformBase
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.Resolution.HironakaG3UniverseLiftedTower
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Resolution.HironakaG3UniverseLiftedTestHistory
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Resolution.HironakaG3UniverseMarkedDomain
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Resolution.HironakaG3UniverseRestrictedRecord
import Hironaka.Resolution.HironakaG3UniverseLiftedSplit
import Hironaka.Resolution.HironakaG3UniverseOrdRegime
import Hironaka.Resolution.HironakaG3UniverseOrderMask

set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseCompanion
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec IdealWeightPowers MonomialPartAlong
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniversePullbackPowers
  HironakaG3UniverseMonomialPart HironakaG3UniverseNonmonomialPart G3UniversePullbackSum
  GermIdealPullbackCalculus
noncomputable section

theorem markedPullback_companion_diffeo {n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} n}
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    (hMono : (monomialPartAlong n M.N M.ideal M.E).IsCoherent)
    (hNonmono : (nonmonomialPartAlong n M.N M.ideal M.E).IsCoherent)
    (hH : ∀ H ∈ M.E, (vanishingIdeal (n := n) H).IsCoherent)
    (hPre : ∀ H ∈ M.E, (vanishingIdeal (n := n) (e ⁻¹' H)).IsCoherent) (o : ℕ) :
    markedPullback (m := n) e (CompanionRebase.companionOf n M o) =
      CompanionRebase.companionOf n (markedPullback (m := n) e M) o := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change e ⁻¹' (CompanionRebase.companionOf n M o).N = _
    simp only [CompanionRebase.companionOf,CompanionReductionAlong.companionAlong_N,markedPullback]
  · change (CompanionRebase.companionOf n M o).E.map (e ⁻¹' ·) = _
    simp only [CompanionRebase.companionOf,CompanionReductionAlong.companionAlong_E,markedPullback]
  · change GermIdeal.pullback (m := n) e (CompanionRebase.companionOf n M o).ideal = _
    simp only [CompanionRebase.companionOf,CompanionRebase.companionAlong_ideal,markedPullback]
    split_ifs
    · rw [pullback_sumIdeal_dimensions e.contMDiff
        (isCoherent_idealPow hNonmono _) (isCoherent_idealPow hMono _),
        HironakaG3UniversePullbackPowers.pullback_idealPow e.contMDiff hNonmono,
        HironakaG3UniversePullbackPowers.pullback_idealPow e.contMDiff hMono,
        pullback_nonmonomialPartAlong_diffeo e M.N M.ideal M.E hI hMono hNonmono hH hPre,
        pullback_monomialPartAlong_diffeo e M.N M.ideal M.E hI hMono hH hPre]
    · exact pullback_nonmonomialPartAlong_diffeo e M.N M.ideal M.E hI hMono hNonmono hH hPre
  · change (CompanionRebase.companionOf n M o).d = _
    simp only [CompanionRebase.companionOf,CompanionRebase.companionAlong_d,markedPullback]

/-- A literal lift preserves the companion of any invariant-domain record. -/
theorem companion_lifted_record {n k : ℕ} (hn : 0 < n) (X : CMfd.{0} n)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (o : ℕ) :
    markedPullback (m := n) (HironakaG3UniverseLiftManifold.liftDiffeomorph.{u} X).symm
        (CompanionRebase.companionOf n M o) =
      CompanionRebase.companionOf n
        (markedPullback (m := n) (HironakaG3UniverseLiftManifold.liftDiffeomorph.{u} X).symm M) o := by
  have hm := isCoherent_monomialPartAlong hn hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isSNCDivisor hM.isWellFormed.isTransverse hM.isWellFormed.isCoherent hM.isNonzeroAlongAt
  have hnn := isCoherent_nonmonomialPartAlong hn hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isSNCDivisor hM.isWellFormed.isTransverse hM.isWellFormed.isCoherent hM.isNonzeroAlongAt
  have hH : ∀ H ∈ M.E, (vanishingIdeal (n := n) H).IsCoherent := by
    intro H hH
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn hM.isWellFormed.isSNCDivisor i)
  have hPre : ∀ H ∈ M.E, (vanishingIdeal (n := n) ((HironakaG3UniverseLiftManifold.liftDiffeomorph.{u} X).symm ⁻¹' H)).IsCoherent := by
    intro H hH
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal
      (HironakaG3UniverseCarrierGeometry.transported_closedSubmanifold
        (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) _
        (MonomialPart.isClosedSubmanifold_get hn hM.isWellFormed.isSNCDivisor i))
  exact markedPullback_companion_diffeo (HironakaG3UniverseLiftManifold.liftDiffeomorph.{u} X).symm M
    hM.isWellFormed.isCoherent hm hnn hH hPre o

/-- At a supplied actual test endpoint, the companion is the lift of the original companion. -/
theorem companion_lifted_test_endpoint {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (o : ℕ) :
    CompanionRebase.companionOf n
      (geoTransformAlong (markedPullback (m := n) (HironakaG3UniverseLiftManifold.liftDiffeomorph.{u} X).symm M)
        (G3UniverseLiftedTower.liftTower.{u} T)) o =
    markedPullback (m := n) (HironakaG3UniverseLiftManifold.liftDiffeomorph.{u} Y).symm
      (CompanionRebase.companionOf n (geoTransformAlong M T) o) := by
  rw [HironakaG3UniverseLiftedMarkedHistory.liftTower_geoTransformAlong M hM.isWellFormed T hT]
  exact (companion_lifted_record hn Y _ (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT) o).symm
end
end Hironaka.G3UniverseCompanion
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.G3UniverseRestrictedCompanion
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals ResolutionInvariantSpec IdealWeightPowers MonomialPartAlong
  HironakaSmoothSubmersionCoefficientIdeals G3UniverseOpenDiffeo G3UniverseCompanion
  G3UniverseRestrictedRecord
noncomputable section

/-- The companion of the actual restricted record commutes with the open diffeomorphism. -/
theorem companion_restrict_diffeo {n k : ℕ} (hn : 0 < n) {X : CMfd.{u} n} {Y : CMfd.{v} n}
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hPM : IsInvDomain k (markedPullback (m := n) e M)) (U : Opens X) (o : ℕ) :
    CompanionRebase.companionOf n
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : preimageOpens e U → Y)
        (markedPullback (m := n) e M)) o =
    markedPullback (m := n) (preimageDiffeo e U).symm
      (CompanionRebase.companionOf n
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M) o) := by
  let M₁ := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M
  let M₂ := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : preimageOpens e U → Y)
    (markedPullback (m := n) e M)
  let e' := (preimageDiffeo e U).symm
  have hd : M₂ = markedPullback (m := n) e' M₁ := markedPullback_restrict_diffeo e M hM.isWellFormed.isCoherent U
  have h₁ : IsInvDomain k M₁ := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have h₂ : IsInvDomain k M₂ := InvDomainTowerAlong.isInvDomain_pullback_val (preimageOpens e U) hPM
  have hm := isCoherent_monomialPartAlong hn h₁.isWellFormed.isClosedSubmanifold_N
    h₁.isWellFormed.isSNCDivisor h₁.isWellFormed.isTransverse h₁.isWellFormed.isCoherent h₁.isNonzeroAlongAt
  have hnn := isCoherent_nonmonomialPartAlong hn h₁.isWellFormed.isClosedSubmanifold_N
    h₁.isWellFormed.isSNCDivisor h₁.isWellFormed.isTransverse h₁.isWellFormed.isCoherent h₁.isNonzeroAlongAt
  have hH : ∀ H ∈ M₁.E, (vanishingIdeal (n := n) H).IsCoherent := by
    intro H hH
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn h₁.isWellFormed.isSNCDivisor i)
  have hPre : ∀ H ∈ M₁.E, (vanishingIdeal (n := n) (e' ⁻¹' H)).IsCoherent := by
    intro H hH
    have hmemb : e' ⁻¹' H ∈ M₂.E := by
      rw [hd]
      exact List.mem_map.mpr ⟨H,hH,rfl⟩
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hmemb
    rw [← hi]
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal
      (MonomialPart.isClosedSubmanifold_get hn h₂.isWellFormed.isSNCDivisor i)
  change CompanionRebase.companionOf n M₂ o = markedPullback (m := n) e' (CompanionRebase.companionOf n M₁ o)
  rw [hd]
  exact (markedPullback_companion_diffeo e' M₁ h₁.isWellFormed.isCoherent hm hnn hH hPre o).symm
end
end Hironaka.G3UniverseRestrictedCompanion
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
namespace Hironaka.G3UniverseMaskCompanion
open Set Function TopologicalSpace Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals ResolutionInvariantSpec HironakaSmoothSubmersionCoefficientIdeals
  HironakaG3UniverseLiftManifold HironakaG3UniverseMarkedDomain G3UniverseOpenDiffeo
  HironakaG3UniverseOrderMask G3UniverseRestrictedCompanion NonmonomialOrderTail
open scoped Topology Manifold ContDiff
noncomputable section

/-- The literal lifted order mask and its actual restricted companion record. -/
theorem companion_lifted_mask {n k : ℕ} (hn : 0 < n) (X : CMfd.{0} n)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (o : ℕ) :
    let e := (liftDiffeomorph.{u} X).symm
    let U := ordMask M o
    ordMask (markedPullback (m := n) e M) o = preimageOpens e U ∧
    CompanionRebase.companionOf n
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : preimageOpens e U → liftCMfd.{u} X)
        (markedPullback (m := n) e M)) o =
    markedPullback (m := n) (preimageDiffeo e U).symm
      (CompanionRebase.companionOf n
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M) o) := by
  have hL : IsInvDomain k (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) :=
    transported_markedPullback_domain X (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) M hM
  constructor
  · apply Opens.ext
    exact ordMask_lifted_record hn X M hM o
  · exact companion_restrict_diffeo hn (liftDiffeomorph.{u} X).symm M hM hL (ordMask M o) o
end
end Hironaka.G3UniverseMaskCompanion

namespace Hironaka.G3UniverseLowerValue
open Set Function TopologicalSpace Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec HironakaSmoothSubmersionCoefficientIdeals
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower HironakaG3UniverseOrderMask NonmonomialOrderTail GeneralValue
open scoped Topology Manifold ContDiff
noncomputable section

/-- Conditional comparison of the actual masked companion values at a literal lifted point. -/
theorem genLowerValue_lifted_of_masked_values {n k : ℕ} (hn : 0 < n) {X Y₀ Y : CMfd.{0} n}
    {Λ : Type} [LinearOrder Λ]
    (F₀ : ∀ {A : CMfd.{0} n}, MarkedIdeal n A → ∀ {B : CMfd.{0} n}, BlowupTower A B → B → Λ)
    (Fᵤ : ∀ {A : CMfd.{u} n}, MarkedIdeal n A → ∀ {B : CMfd.{u} n}, BlowupTower A B → B → Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower M T₀)
    (T₁ : BlowupTower Y₀ Y) (o : ℕ) (y : Y)
    (hval : ∀ (h₀ : T₁.proj y ∈ ordMask (geoTransformAlong M T₀) o)
      (hᵤ : (liftTower.{u} T₁).proj ((liftDiffeomorph.{u} Y) y) ∈
        ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) o),
      Fᵤ (compAt (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o (liftTower.{u} T₀))
        (restrict (ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) o) (liftTower.{u} T₁))
        ⟨(liftDiffeomorph.{u} Y) y, hᵤ⟩ =
      F₀ (compAt M o T₀) (restrict (ordMask (geoTransformAlong M T₀) o) T₁) ⟨y, h₀⟩) :
    genLowerValue Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o
      (liftTower.{u} T₀) (liftTower.{u} T₁) ((liftDiffeomorph.{u} Y) y) =
    genLowerValue F₀ M o T₀ T₁ y := by
  classical
  have hp : (liftTower.{u} T₁).proj ((liftDiffeomorph.{u} Y) y) ∈
      ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) o ↔
      T₁.proj y ∈ ordMask (geoTransformAlong M T₀) o := by
    change (liftTower.{u} T₁).proj ((liftDiffeomorph.{u} Y) y) ∈
      (ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) o : Set (liftCMfd.{u} Y₀)) ↔ _
    rw [ordMask_lifted_test_endpoint hn M hM T₀ hT₀ o]
    change (liftDiffeomorph.{u} Y₀).symm ((liftTower.{u} T₁).proj ((liftDiffeomorph.{u} Y) y)) ∈
      (ordMask (geoTransformAlong M T₀) o : Set Y₀) ↔ _
    rw [liftTower_proj]
    simp
  unfold genLowerValue
  by_cases ho : T₁.proj y ∈ ordMask (geoTransformAlong M T₀) o
  · have hu := hp.mpr ho
    simpa only [dif_pos hu, dif_pos ho] using congrArg WithTop.some (hval ho hu)
  · have hu : ¬ (liftTower.{u} T₁).proj ((liftDiffeomorph.{u} Y) y) ∈
      ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) o :=
        fun h => ho (hp.mp h)
    simp only [dif_neg hu, dif_neg ho]
end
end Hironaka.G3UniverseLowerValue

namespace Hironaka.G3UniversePositiveValue
open Set Function TopologicalSpace Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  HironakaG3UniverseLiftedSplit HironakaG3UniverseOrdRegime G3UniverseLowerValue HironakaG3UniverseLiftedNmOrd
  NonmonomialOrderTail NonmonomialOrderLocal NonmonomialOrderRegime GeneralValue
open scoped Topology Manifold ContDiff
noncomputable section

/-- Positive-order general-value agreement, assuming the actual masked recursive values agree. -/
theorem genInv_lifted_positive_of_masked_values {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {Λ : Type} [LinearOrder Λ]
    (F₀ : ∀ {A : CMfd.{0} n}, MarkedIdeal n A → ∀ {B : CMfd.{0} n}, BlowupTower A B → B → Λ)
    (Fᵤ : ∀ {A : CMfd.{u} n}, MarkedIdeal n A → ∀ {B : CMfd.{u} n}, BlowupTower A B → B → Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (y : Y)
    (hpos : nmOrd (geoTransformAlong M T) y ≠ 0)
    (hval : let o := nmOrd (geoTransformAlong M T) y
      let j := StepOneRegime.regimeRun (OrdRegime M o) T y
      ∀ (h₀ : (tail T j).proj y ∈ ordMask (geoTransformAlong M (head T j)) o)
        (hᵤ : (liftTower.{u} (tail T j)).proj ((liftDiffeomorph.{u} Y) y) ∈
          ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} (head T j))) o),
        Fᵤ (compAt (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o (liftTower.{u} (head T j)))
          (restrict (ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
            (liftTower.{u} (head T j))) o) (liftTower.{u} (tail T j))) ⟨(liftDiffeomorph.{u} Y) y,hᵤ⟩ =
        F₀ (compAt M o (head T j)) (restrict (ordMask (geoTransformAlong M (head T j)) o) (tail T j)) ⟨y,h₀⟩) :
    genInv Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) ((liftDiffeomorph.{u} Y) y) =
      genInv F₀ M T y := by
  classical
  let o := nmOrd (geoTransformAlong M T) y
  let j := StepOneRegime.regimeRun (OrdRegime M o) T y
  have hHead : IsGeoTestTower M (head T j) := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  have hLow := genLowerValue_lifted_of_masked_values hn F₀ Fᵤ M hM (head T j) hHead (tail T j) o y hval
  have hLow' : genLowerValue Fᵤ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o
      (head (liftTower.{u} T) j) (tail (liftTower.{u} T) j) ((liftDiffeomorph.{u} Y) y) =
      genLowerValue F₀ M o (head T j) (tail T j) y := by
    unfold head tail
    rw [liftTower_split]
    exact hLow
  have hord := nmOrd_lifted_test_endpoint hn M hM T hT ((liftDiffeomorph.{u} Y) y)
  simp only [Diffeomorph.symm_apply_apply] at hord
  have hrun := regimeRun_ordRegime_liftTower hn M hM o T hT ((liftDiffeomorph.{u} Y) y)
  simp only [Diffeomorph.symm_apply_apply] at hrun
  unfold genInv genSecond
  rw [hord, if_neg hpos, if_neg hpos]
  change _ = _
  rw [hrun]
  exact congrArg (fun x => toLex (o, toLex (Sum.inr x))) hLow'
end
end Hironaka.G3UniversePositiveValue

namespace Hironaka.G3UniversePositiveInvariant
open Set Function TopologicalSpace Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniversePositiveValue NonmonomialOrderTail NonmonomialOrderLocal NonmonomialOrderRegime GeneralValue
open scoped Topology Manifold ContDiff
noncomputable section

/-- The actual masked companion Step One evaluations agree at this point. -/
def LiftedMaskedStepValuesAgree {n : ℕ} (hn : 0 < n) (r : ℕ) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) : Prop :=
  let o := nmOrd (geoTransformAlong M T) y
      let j := StepOneRegime.regimeRun (OrdRegime M o) T y
      ∀ (h₀ : (tail T j).proj y ∈ ordMask (geoTransformAlong M (head T j)) o)
        (hᵤ : (liftTower.{u} (tail T j)).proj ((liftDiffeomorph.{u} Y) y) ∈
          ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} (head T j))) o),
        (fun {A} J {B} Q z => Seq.StepOneValueMasked.stepOneInvM (X := A) (CanonicalCentres.invFamily.{u} hn r) J (Y := B) Q z) (compAt (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o (liftTower.{u} (head T j)))
          (restrict (ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
            (liftTower.{u} (head T j))) o) (liftTower.{u} (tail T j))) ⟨(liftDiffeomorph.{u} Y) y,hᵤ⟩ =
        (fun {A} J {B} Q z => Seq.StepOneValueMasked.stepOneInvM (X := A) (CanonicalCentres.invFamily.{0} hn r) J (Y := B) Q z) (compAt M o (head T j)) (restrict (ordMask (geoTransformAlong M (head T j)) o) (tail T j)) ⟨y,h₀⟩

/-- Conditional positive-order value equality for the original recursive invariant family. -/
theorem invFamily_succ_lifted_positive_of_masked_values {n k r : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (y : Y)
    (hpos : nmOrd (geoTransformAlong M T) y ≠ 0) (hval : LiftedMaskedStepValuesAgree.{u} hn r M T y) :
    (invFamily.{u} hn (r+1)).inv (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (liftTower.{u} T) ((liftDiffeomorph.{u} Y) y) = (invFamily.{0} hn (r+1)).inv M T y := by
  simp only [invFamily_succ, generalStep_inv]
  exact genInv_lifted_positive_of_masked_values hn _ _ M hM T hT y hpos hval
end
end Hironaka.G3UniversePositiveInvariant
