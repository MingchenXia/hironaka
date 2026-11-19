import Hironaka.Resolution.HironakaG8NativeRelativeClearing
import Hironaka.Resolution.HironakaG8NativeCommonMarkRank
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.Resolution.HironakaG1OriginalInvariantClassFunctorial

/-! Simultaneous common-maximum native centres agree at a compared
literal ambient prefix, despite independently chosen common marks. -/

set_option autoImplicit false
set_option maxHeartbeats 3700000

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeSimultaneousComparison

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaHolomorphicJetChartInvariance NormalCrossings HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaActualPowerBoundaryExponents HironakaG8NativeNumericalOverlap
  HironakaG8NativeRelativeClearing HironakaG8NativeCommonMarkRank HironakaG8NativeSimultaneousCentre
  HironakaG1OriginalUnequalMarkCanonical HironakaActualOriginalPowerTransform
  HironakaG1OriginalInvariantClassFunctorial
  HironakaActualVanishingIntrinsicHSTransport IdealWeightPowers

variable {n : ℕ} {X Y : CMfd.{0} n} {I J : Type}

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)

private abbrev originalBM (n : ℕ) :
    BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n (ValTy n) :=
  ⟨canonicalInvariant n,classFunctorialFor_canonicalInvariant n⟩

/-- Whole-power recoding can be composed before comparing common marks. -/
theorem powerMarked_comp (P : MarkedIdeal n X) (hP : P.ideal.IsCoherent) (e f : ℕ) :
    powerMarked (powerMarked P e) f = powerMarked P (e * f) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ (Nat.mul_assoc _ _ _)
  change idealPow (idealPow P.ideal e) f = idealPow P.ideal (e*f)
  induction f with
  | zero => rw [Nat.mul_zero]; rfl
  | succ f ih =>
    rw [Nat.mul_succ, RestrictLeCalculus.idealPow_add hP]
    change (idealPow (idealPow P.ideal e) f).mul (idealPow P.ideal e) =
      (idealPow P.ideal (e*f)).mul (idealPow P.ideal e)
    rw [ih]

private theorem cosupp_whole_power_on_canonical {P : MarkedIdeal n X}
    (hP : IsInvDomain n P) (e : ℕ) (he : 1 ≤ e) (T : BlowupTower X Y)
    (hCan : IsCanonical P ((canonicalInvariant n).inv P) T) :
    (geoTransformAlong (powerMarked P e) T).cosupp = (geoTransformAlong P T).cosupp := by
  have hTest := (canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hP T hCan
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hP T hTest
  exact (original_power_transform P hP e he T hTest).2.cosupp_eq.trans
    (powerMarked_cosupp (geoTransformAlong P T) hCurrent he)

section MatchedWindows

variable {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
variable (A : NativeWindows X I W E H D) (B : NativeWindows X J W E H D)
variable (T : BlowupTower X Y)

local notation "inv" => ResolutionInvariantSeq.ResolutionInvariant.inv (canonicalInvariant n)

private theorem common_product_mark_point (hn : 0 < n)
    (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (hMarkA : 1 ≤ A.mark) (hMarkB : 1 ≤ B.mark)
    (hCanA : ∀ i, IsCanonical (A.powered i) (inv (A.powered i)) (restrict (A.openSet i) T))
    (hCanB : ∀ j, IsCanonical (B.powered j) (inv (B.powered j)) (restrict (B.openSet j) T))
    (i : I) (j : J) (y : Y)
    (hi : y ∈ openPreimage T (A.openSet i)) (hj : y ∈ openPreimage T (B.openSet j))
    (hy : (⟨y,hi⟩ : openPreimage T (A.openSet i)) ∈
      (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp) :
    (⟨y,hj⟩ : openPreimage T (B.openSet j)) ∈
      (geoTransformAlong (B.powered j) (restrict (B.openSet j) T)).cosupp ∧
    inv (powerMarked (A.powered i) B.mark) (restrict (A.openSet i) T) ⟨y,hi⟩ =
      inv (powerMarked (B.powered j) A.mark) (restrict (B.openSet j) T) ⟨y,hj⟩ := by
  have hRecA : powerMarked (A.powered i) B.mark =
      powerMarked (A.record i) (A.exponent i * B.mark) :=
    powerMarked_comp (A.record i) (A.domain i).isWellFormed.isCoherent _ _
  have hRecB : powerMarked (B.powered j) A.mark =
      powerMarked (B.record j) (B.exponent j * A.mark) :=
    powerMarked_comp (B.record j) (B.domain j).isWellFormed.isCoherent _ _
  have hNewA := (canonicalInvariant_isCanonical_power_iff (A.powered i) (A.powered_domain i)
    B.mark hMarkB (restrict (A.openSet i) T)).mp (hCanA i)
  have hNewB := (canonicalInvariant_isCanonical_power_iff (B.powered j) (B.powered_domain j)
    A.mark hMarkA (restrict (B.openSet j) T)).mp (hCanB j)
  have hCommon : (powerMarked (A.record i) (A.exponent i * B.mark)).d =
      (powerMarked (B.record j) (B.exponent j * A.mark)).d := by
    rw [← hRecA,← hRecB]
    change (A.powered i).d * B.mark = (B.powered j).d * A.mark
    rw [A.commonMark i,B.commonMark j,Nat.mul_comm]
  have hCosA := cosupp_whole_power_on_canonical (A.powered_domain i) B.mark hMarkB _ (hCanA i)
  have hCosB := cosupp_whole_power_on_canonical (B.powered_domain j) A.mark hMarkA _ (hCanB j)
  have hyNew : (⟨y,hi⟩ : openPreimage T (A.openSet i)) ∈
      (geoTransformAlong (powerMarked (A.record i) (A.exponent i * B.mark))
        (restrict (A.openSet i) T)).cosupp := by
    rw [← hRecA,hCosA]
    exact hy
  rw [hRecA] at hNewA
  rw [hRecB] at hNewB
  have hBaseNot : ∀ F ∈ E, ∀ x : A.openSet i, x ∈ (A.record i).cosupp → x.val ∈ F →
      ¬ ∀ᶠ z in 𝓝 x.val, z ∈ F → z ∈ W := by
    intro F hF x hx hxF
    apply hNot F hF x.val ?_ hxF
    rw [(A.native i).cosupp_eq] at hx
    refine (Set.ext_iff.mp hExact x.val).mpr ?_
    intro ℓ
    exact (hilbertSamuelAt_vanishing_actual_open_any (A.openSet i) W x ℓ).symm.trans (hx ℓ)
  have hNumeric := native_window_values_agree_along hn (originalBM n)
    (A.openSet i) (B.openSet j) (A.record i) (B.record j) (A.domain i) (B.domain j)
    W H (A.native i) (B.native j) E (A.boundary i) (B.boundary j)
    (A.exponent i * B.mark) (B.exponent j * A.mark)
    (Nat.mul_pos (A.positive i) hMarkB) (Nat.mul_pos (B.positive j) hMarkA)
    hCommon hBaseNot T hNewA hNewB hi hj hyNew
  change _ ∧ inv (powerMarked (A.record i) _) _ _ = inv (powerMarked (B.record j) _) _ _ at hNumeric
  rw [← hRecA,← hRecB] at hNumeric
  exact ⟨hCosB ▸ hNumeric.1,hNumeric.2⟩

/-- Independent choices of common positive mark yield the same strict
order on pairs of matched active points at one literal ambient prefix. -/
theorem native_windows_order_agrees_at_common_prefix (hn : 0 < n)
    (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (hMarkA : 1 ≤ A.mark) (hMarkB : 1 ≤ B.mark)
    (hCanA : ∀ i, IsCanonical (A.powered i) (inv (A.powered i)) (restrict (A.openSet i) T))
    (hCanB : ∀ j, IsCanonical (B.powered j) (inv (B.powered j)) (restrict (B.openSet j) T))
    (i₁ i₂ : I) (j₁ j₂ : J) (y₁ y₂ : Y)
    (hi₁ : y₁ ∈ openPreimage T (A.openSet i₁)) (hi₂ : y₂ ∈ openPreimage T (A.openSet i₂))
    (hj₁ : y₁ ∈ openPreimage T (B.openSet j₁)) (hj₂ : y₂ ∈ openPreimage T (B.openSet j₂))
    (hy₁ : (⟨y₁,hi₁⟩ : openPreimage T (A.openSet i₁)) ∈
      (geoTransformAlong (A.powered i₁) (restrict (A.openSet i₁) T)).cosupp)
    (hy₂ : (⟨y₂,hi₂⟩ : openPreimage T (A.openSet i₂)) ∈
      (geoTransformAlong (A.powered i₂) (restrict (A.openSet i₂) T)).cosupp) :
    (inv (A.powered i₁) (restrict (A.openSet i₁) T) ⟨y₁,hi₁⟩ <
      inv (A.powered i₂) (restrict (A.openSet i₂) T) ⟨y₂,hi₂⟩) ↔
    (inv (B.powered j₁) (restrict (B.openSet j₁) T) ⟨y₁,hj₁⟩ <
      inv (B.powered j₂) (restrict (B.openSet j₂) T) ⟨y₂,hj₂⟩) := by
  obtain ⟨hz₁,hEq₁⟩ := common_product_mark_point A B T hn hExact hNot hMarkA hMarkB
    hCanA hCanB i₁ j₁ y₁ hi₁ hj₁ hy₁
  obtain ⟨hz₂,hEq₂⟩ := common_product_mark_point A B T hn hExact hNot hMarkA hMarkB
    hCanA hCanB i₂ j₂ y₂ hi₂ hj₂ hy₂
  have hRecA := canonical_common_mark_power_lt_iff (A.powered i₁) (A.powered i₂)
    (A.powered_domain i₁) (A.powered_domain i₂) ((A.commonMark i₁).trans (A.commonMark i₂).symm)
    B.mark hMarkB _ _ (hCanA i₁) (hCanA i₂) hy₁ hy₂
  have hRecB := canonical_common_mark_power_lt_iff (B.powered j₁) (B.powered j₂)
    (B.powered_domain j₁) (B.powered_domain j₂) ((B.commonMark j₁).trans (B.commonMark j₂).symm)
    A.mark hMarkA _ _ (hCanB j₁) (hCanB j₂) hz₁ hz₂
  rw [hEq₁,hEq₂] at hRecA
  exact hRecA.trans hRecB.symm

private theorem simultaneous_centre_subset_at_common_prefix (hn : 0 < n)
    (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (hCanA : ∀ i, IsCanonical (A.powered i) (inv (A.powered i)) (restrict (A.openSet i) T))
    (hCanB : ∀ j, IsCanonical (B.powered j) (inv (B.powered j)) (restrict (B.openSet j) T))
    (hActiveA : ActiveWindows A T (canonicalInvariant n))
    (hActiveB : ActiveWindows B T (canonicalInvariant n))
    {C₁ C₂ : Set Y} {m₁ m₂ : ValTy n}
    (hA : NativeSimultaneousCentre (canonicalInvariant n) A.openSet A.powered T C₁ m₁)
    (hB : NativeSimultaneousCentre (canonicalInvariant n) B.openSet B.powered T C₂ m₂)
    (hC₂ : C₂.Nonempty) : C₁ ⊆ C₂ := by
  obtain ⟨q,hq⟩ := hC₂
  obtain ⟨j₂,hj₂⟩ := hB.covered q hq
  have hWitness := (Set.ext_iff.mp (hB.trace j₂) (⟨q,hj₂⟩ : openPreimage T (B.openSet j₂))).mp hq
  have hqF := (hActiveB.support j₂ ⟨q,hj₂⟩).mp hWitness.1
  obtain ⟨i₂,hi₂⟩ := A.covers (T.proj q) hqF.1
  have hqA := (hActiveA.support i₂ ⟨q,hi₂⟩).mpr hqF
  intro p hp
  obtain ⟨i₁,hi₁⟩ := hA.covered p hp
  have hMax := (Set.ext_iff.mp (hA.trace i₁) (⟨p,hi₁⟩ : openPreimage T (A.openSet i₁))).mp hp
  have hpF := (hActiveA.support i₁ ⟨p,hi₁⟩).mp hMax.1
  obtain ⟨j₁,hj₁⟩ := B.covers (T.proj p) hpF.1
  have hpB := (hActiveB.support j₁ ⟨p,hj₁⟩).mpr hpF
  have hMarkA : 1 ≤ A.mark := (A.commonMark i₁) ▸ (A.powered_domain i₁).one_le_d
  have hMarkB : 1 ≤ B.mark := (B.commonMark j₁) ▸ (B.powered_domain j₁).one_le_d
  apply (Set.ext_iff.mp (hB.trace j₁) (⟨p,hj₁⟩ : openPreimage T (B.openSet j₁))).mpr
  refine ⟨hpB,?_⟩
  by_contra hNe
  have hOrder := native_windows_order_agrees_at_common_prefix A B T hn hExact hNot hMarkA hMarkB
    hCanA hCanB i₁ i₂ j₁ j₂ p q hi₁ hi₂ hj₁ hj₂ hMax.1 hqA
  have hpLower := lt_of_le_of_ne (hB.upper j₁ ⟨p,hj₁⟩ hpB) hNe
  have hLt := hOrder.mpr (hWitness.2.symm ▸ hpLower)
  exact (not_lt_of_ge (hA.upper i₂ ⟨q,hi₂⟩ hqA)) (hMax.2 ▸ hLt)

/-- At one common actual ambient prefix, the simultaneous maximum
centre is independent of the native window cover and its chosen
positive common mark. The entire possibly disconnected centre agrees. -/
theorem simultaneous_centres_agree_at_common_prefix (hn : 0 < n)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (hT : IsGeoTestTower (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    (hCanA : ∀ i, IsCanonical (A.powered i) (inv (A.powered i)) (restrict (A.openSet i) T))
    (hCanB : ∀ j, IsCanonical (B.powered j) (inv (B.powered j)) (restrict (B.openSet j) T))
    {C₁ C₂ : Set Y} {m₁ m₂ : ValTy n}
    (hA : NativeSimultaneousCentre (canonicalInvariant n) A.openSet A.powered T C₁ m₁)
    (hB : NativeSimultaneousCentre (canonicalInvariant n) B.openSet B.powered T C₂ m₂)
    (hC₁ : C₁.Nonempty) (hC₂ : C₂.Nonempty) : C₁ = C₂ := by
  have hActiveA := nativeWindows_active_replay hn (originalBM n) hW hE hExact hNot A T hT hStage hCanA
  have hActiveB := nativeWindows_active_replay hn (originalBM n) hW hE hExact hNot B T hT hStage hCanB
  exact subset_antisymm
    (simultaneous_centre_subset_at_common_prefix A B T hn hExact hNot hCanA hCanB hActiveA hActiveB hA hB hC₂)
    (simultaneous_centre_subset_at_common_prefix B A T hn hExact hNot hCanB hCanA hActiveB hActiveA hB hA hC₁)

end MatchedWindows

end
end Hironaka.HironakaG8NativeSimultaneousComparison
