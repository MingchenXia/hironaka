import Hironaka.Resolution.HironakaG1LaterPositiveCANHistory

/-! # Initial maxima on the padded and literal native sources -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1InitialLiteralNativeSmallSupport

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres StepOneValue
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionInitialBar HironakaActualSectionBoundaryGeometry
  HironakaActualNativeSectionOrderHistory RelativePrincipalizationSpan
  HironakaG1LaterPositiveCANHistory
  NormalCrossings

variable {n k : ℕ} {U : Opens (ComplexModel n)} (hn : 0 < n) (Q : MarkedIdeal n U)
  (hQ : IsInvDomain (k + 1) Q) (hWc : IsClosed (zeroPlane U))

local notation "X₀" => CMfd.of (n := n + 1) (productOpen U)
local notation "A" => nativeManifold (Y := X₀) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)
local notation "P" => properNormalMarked Q
local notation "SEC" => sectionMarked Q
local notation "B" => nativePullback (Y := X₀) (Nat.le_succ n) (zeroPlane U)
  (zeroPlane_regular U) SEC
local notation "T₀" => BlowupTower.refl (X := X₀)
local notation "N₀" => BlowupTower.refl (X := A)
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P
local notation "g" => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) B

private theorem maxLocus_eq_of_subsingleton {Y Λ : Type*} [LinearOrder Λ]
    (v : Y → Λ) (D : Set Y) (hD : D.Subsingleton) : maxLocus v D = D := by
  ext x
  constructor
  · exact fun h => h.1
  · intro hx
    exact ⟨hx, fun y hy => (hD hy hx) ▸ le_rfl⟩

include hQ hWc in
set_option maxHeartbeats 900000 in
/-- Empty or singleton actual initial cosupport gives literal native
maximum readback at every initial level, in particular at level zero. -/
theorem initial_literal_native_subsingleton_max_image
    (hC : (P).cosupp.Subsingleton) :
    (Subtype.val : A → X₀) '' maxLocus (g N₀)
        (MarkedIdeal.cosupp (n := n) (M := A) (geoTransformAlong (Y := A) B N₀)) =
      maxLocus (f T₀) (geoTransformAlong P T₀).cosupp := by
  have hM : IsInvDomain (k + 1) SEC :=
    section_projected_domain _ Q.N Q.E Q.ideal Q.d hQ
  have hSupport : (SEC).N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hTrans : IsTransverse (n + 1) (zeroPlane U) (SEC).E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) (SEC).E
      T₀ (zeroPlane U) hWc (zeroPlane_regular U) N₀ := .refl
  let i : A → X₀ := Subtype.val
  let D := MarkedIdeal.cosupp (n := n) (M := A) (geoTransformAlong (Y := A) B N₀)
  have hCos : (P).cosupp = (SEC).cosupp :=
    (properNormalMarked_locWPEquiv_section Q hQ).cosupp_eq_base
  have hD : D = i ⁻¹' (P).cosupp := by
    rw [hCos]
    exact Lift.current_cosupport hLift (Nat.succ_pos n) hM.isWellFormed.isSNCDivisor hTrans SEC
      rfl hSupport (fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hf)
  have hRange : (P).cosupp ⊆ range i := by
    rw [hCos, Subtype.range_coe]
    exact (SEC).cosupp_subset_N.trans hSupport
  have hSub : D.Subsingleton := by
    rw [hD]
    intro x hx y hy
    exact Subtype.val_injective (hC hx hy)
  change i '' maxLocus (g N₀) D = maxLocus (f T₀) (P).cosupp
  rw [maxLocus_eq_of_subsingleton _ _ hSub, maxLocus_eq_of_subsingleton _ _ hC, hD,
    image_preimage_eq_inter_range, inter_eq_left.mpr hRange]

include hQ hWc in
/-- Exact initial history readback on an empty or singleton cosupport. -/
theorem initial_literal_native_subsingleton_prefix_read
    (hC : (P).cosupp.Subsingleton) :
    PrefixRead (k := k) hn Q T₀ N₀ :=
  PrefixRead.exactMax (initial_literal_native_subsingleton_max_image hn Q hQ hWc hC)

end
end Hironaka.HironakaG1InitialLiteralNativeSmallSupport
