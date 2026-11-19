import Hironaka.Resolution.HironakaG1MixedPrescribedSelectedTrace
import Hironaka.Resolution.HironakaG1ActualLaterCommonTangent
import Hironaka.Resolution.HironakaG1CompanionZeroBranchRecognition

/-! # Prescribed-zero compatibility at the actual initial order mask -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1ActualPrescribedCompanionTrace
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime HomogenizedIdealAlong HomogenizedGlueingTower
  TangentDirectionAlong NonmonomialOrderTail GeneralValue
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaG1ProperCarrierNormalContact HironakaG1ActualLaterCompanionTangent
  HironakaG1MixedPrescribedSelectedTrace HironakaG8LocalHistory
  HironakaG1CompanionZeroBranchRecognition CodimOneSupportAlong

/-- The strict prescribed normal zero-set at any real head is exactly
that head's section bar carrier. -/
theorem strict_prescribed_zero_eq_section_bar_carrier {n : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) {Y : CMfd.{0} (n+1)}
    (H : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y) :
    strictAlong H ((properNormalMarked Q).N ∩ {z | relativeNormalCoordinate U z = 0}) =
      (geoTransformAlong (barMarked (sectionMarked Q)) H).N := by
  rw [N_geoTransformAlong, normal_contact_carrier Q]
  rfl

private theorem zero_iff_on_carrier_of_trace {A B : Type*} (K Ω : Set A)
    (g : A → ℂ) (f : A → B) (D E : Set B)
    (hTrace : K ∩ {x | g x = 0} ∩ Ω = K ∩ f ⁻¹' D ∩ Ω) (hDE : D = E) :
    ∀ x ∈ K, x ∈ Ω → (g x = 0 ↔ f x ∈ E) := by
  subst E
  intro x hx hxΩ
  have he := Set.ext_iff.mp hTrace x
  exact ⟨fun h => (he.mp ⟨⟨hx, h⟩, hxΩ⟩).1.2,
    fun h => (he.mpr ⟨⟨hx, h⟩, hxΩ⟩).1.2⟩

set_option maxHeartbeats 1900000 in
/-- The actual tangent producer verifies prescribed-zero compatibility
on a genuine source neighborhood of the initial order companion. This
source identity is available on both section branches. -/
theorem exists_actual_initial_companion_prescribed_zero {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k+1) Q)
    {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k+1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s+1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n+1) (productOpen U)
    let P := properNormalMarked Q
    let r := regimeRun (stepRegime P (s+1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n+1) O
    let L : MarkedIdeal (n+1) A := lowerMarkedM (X := X) P (s+1) H p
    let C : Opens A := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let J : MarkedIdeal (n+1) (CMfd.of (n := n+1) C) := compAt (X := A) L L.d .refl
    ∃ hp : p ∈ O, ∃ hC : (⟨p, hp⟩ : O) ∈ C,
      ∃ (W : Opens (CMfd.of (n := n+1) C)) (u : C → ℂ),
        (⟨⟨p, hp⟩, hC⟩ : C) ∈ W ∧ IsInvDomain (k+1) J ∧
        IsTangentDirectionAlong J.N J.ideal J.d W u ∧
        ∀ x ∈ J.N, x ∈ W → (u x = 0 ↔
          x.val.val ∈ (geoTransformAlong (barMarked (sectionMarked Q)) H).N) := by
  intro X P r H S p O A L C J
  obtain ⟨hp, hC, Ω, u, hΩ, _, hJ, hTan, hTrace⟩ :=
    exists_actual_later_initial_order_companion_tangent Q hQ T hCan y hy hLevel hNS
  let W : Opens (CMfd.of (n := n+1) C) := ⟨Ω, hTan.isOpen⟩
  let v : C → ℂ := fun x => u x.val.val
  let f : C → (split T r).1 := fun x => x.val.val
  have hCarrier := strict_prescribed_zero_eq_section_bar_carrier Q H
  exact ⟨hp, hC, W, v, hΩ, hJ, hTan,
    zero_iff_on_carrier_of_trace J.N Ω v f _ _ hTrace hCarrier⟩

/-- Source-window equality suffices along a genuine strict transform,
at any endpoint whose actual projection lies in the window. -/
theorem strictAlong_eventually_eq_of_source_window {n : ℕ}
    {X Y : CMfd.{0} n} (T : BlowupTower X Y) (A B : Set X)
    (Ω : Opens X) (hEq : A ∩ Ω = B ∩ Ω) (y : Y) (hy : T.proj y ∈ Ω) :
    ∀ᶠ z in 𝓝 y, z ∈ strictAlong T A ↔ z ∈ strictAlong T B := by
  have hTrace := ContactEquivalenceStage.strictAlong_inter_preimage_eq Ω.isOpen hEq T
  have hOpen : IsOpen (T.proj ⁻¹' (Ω : Set X)) :=
    Ω.isOpen.preimage T.contMDiff_proj.continuous
  filter_upwards [hOpen.mem_nhds hy] with z hz
  have h := Set.ext_iff.mp hTrace z
  exact ⟨fun hzA => (h.mp ⟨hzA, hz⟩).1, fun hzB => (h.mpr ⟨hzB, hz⟩).1⟩

set_option maxHeartbeats 950000 in
/-- A verified prescribed-zero neighborhood at the actual companion
source transports to the selected section germ through both masks,
without requiring compatibility beyond the source neighborhood. -/
theorem local_prescribed_zero_transports_selected_trace
    {n : ℕ} {X Y Z : CMfd.{0} n} (P Sec : MarkedIdeal n X)
    (hSec : Sec.IsWellFormed) (hN : Sec.N ⊆ P.N) (hE : P.E = Sec.E)
    (H : BlowupTower X Y) (R : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked Sec) (H.append R))
    (z : Z) (hLevel : level Sec (H.append R) z = level Sec H (R.proj z))
    (W : Opens Y) (O : Opens (CMfd.of (n := n) W))
    (J : MarkedIdeal n (CMfd.of (n := n) O))
    (hCarrier : J.N = (fun x : O => (x.val.val : Y)) ⁻¹' selectedCarrier P H (R.proj z))
    (Ω : Opens (CMfd.of (n := n) O)) (u : O → ℂ)
    (hZero : ∀ x ∈ J.N, x ∈ Ω →
      (u x = 0 ↔ x.val.val ∈ (geoTransformAlong (barMarked Sec) H).N))
    (w : openPreimage (restrict W R) O) (hw : (restrict O (restrict W R)).proj w ∈ Ω) :
    let S := restrict O (restrict W R)
    let i : openPreimage (restrict W R) O → Z := fun x => x.val.val
    ∀ᶠ x in 𝓝 w, x ∈ strictAlong S (J.N ∩ {y | u y = 0}) ↔
      i x ∈ selectedCarrier Sec (H.append R) z := by
  intro S i
  let C := selectedCarrier Sec H (R.proj z)
  let j : O → Y := fun x => x.val.val
  have hOld := HironakaG8MemberLoci.origMembers_eq_of_E_eq hE H
  have hSub := bar_carrier_subset_of_source_subset P Sec hN H
  have hSrc : (J.N ∩ {x | u x = 0}) ∩ Ω = (j ⁻¹' C) ∩ Ω := by
    ext x
    constructor
    · rintro ⟨⟨hx, hxu⟩, hxΩ⟩
      have hp : x ∈ j ⁻¹' selectedCarrier P H (R.proj z) := hCarrier ▸ hx
      refine ⟨⟨(hZero x hx hxΩ).mp hxu, ?_⟩, hxΩ⟩
      intro D hD hpD
      exact hp.2 D (hOld.symm ▸ hD) hpD
    · rintro ⟨hx, hxΩ⟩
      have hP : x ∈ j ⁻¹' selectedCarrier P H (R.proj z) :=
        ⟨hSub hx.1, fun D hD hpD => hx.2 D (hOld ▸ hD) hpD⟩
      have hxJ : x ∈ J.N := hCarrier.symm ▸ hP
      exact ⟨⟨hxJ, (hZero x hxJ hxΩ).mpr hx.1⟩, hxΩ⟩
  have hNear := strictAlong_eventually_eq_of_source_window S _ _ Ω hSrc w hw
  have hStrict : strictAlong S (j ⁻¹' C) = i ⁻¹' selectedCarrier Sec (H.append R) z :=
    (strictAlong_twice_restrict_preimage R W O C).trans
      (congrArg (fun D => i ⁻¹' D) (selectedCarrier_strictAlong Sec hSec H R hT z hLevel))
  rw [hStrict] at hNear
  exact hNear

/-- A strict supported domain with the same tested threshold excludes
saturation at zero. This is the obstruction to treating the supported
finite construction as a producer on the saturated branch. -/
theorem no_strict_supported_domain_at_saturated_zero
    {n k l : ℕ} {X Y : CMfd.{0} n}
    (J : MarkedIdeal n X) (hJ : IsInvDomain k J)
    (u : X → ℂ) (hu : IsTangentDirectionAlong J.N J.ideal J.d univ u)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (y : Y)
    (hSat : y ∈ codimOnePartAlong (geoTransformAlong (barMarked J) T).N
      (geoTransformAlong (barMarked J) T).ideal (geoTransformAlong (barMarked J) T).d) :
    ¬ ∃ R : MarkedIdeal n X, IsInvDomain l R ∧ LocWPEquiv J R ∧
      J.N ∩ {x | u x = 0} = R.N := by
  rintro ⟨R, hR, hClass, hTrace⟩
  exact codim_one_absent_of_strict_supported_trace J R hJ hR hClass u hu hTrace T hT y hSat

end
end Hironaka.HironakaG1ActualPrescribedCompanionTrace
