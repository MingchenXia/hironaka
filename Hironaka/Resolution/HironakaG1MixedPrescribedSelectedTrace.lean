import Hironaka.Resolution.HironakaG1MixedSelectedThresholdTrace

/-! # The prescribed source trace gives the actual selected section carrier -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1MixedPrescribedSelectedTrace
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  StepOneValue StepOneValueMasked HomogenizedIdealAlong HomogenizedGlueingTower
  TangentDirectionAlong InvDomainMemberRestriction HironakaG8MemberLoci
  BoundaryCount GeneralValue NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  HironakaG8HomStable HironakaG8LocalHistory HironakaG1PositiveNormalRestartCarrier
  HironakaG1MixedSelectedThresholdTrace

/-- The selected carrier uses the actual old boundary members incident
to the indicated point, together with the current bar carrier. -/
def selectedCarrier {n : ℕ} {X Y : CMfd.{0} n}
    (Q : MarkedIdeal n X) (T : BlowupTower X Y) (p : Y) : Set Y :=
  (geoTransformAlong (barMarked Q) T).N ∩
    {x | ∀ D ∈ origMembers Q T, p ∈ D → x ∈ D}

/-- Since the old level is unchanged, the actual selected carrier at
the endpoint is exactly the strict transform of the selected source. -/
theorem selectedCarrier_strictAlong {n : ℕ} {X Y Z : CMfd.{0} n}
    (Q : MarkedIdeal n X) (hQ : Q.IsWellFormed) (H : BlowupTower X Y)
    (R : BlowupTower Y Z) (hT : IsGeoTestTower (barMarked Q) (H.append R))
    (z : Z) (hl : level Q (H.append R) z = level Q H (R.proj z)) :
    strictAlong R (selectedCarrier Q H (R.proj z)) = selectedCarrier Q (H.append R) z := by
  have hEq := (selected_carrier_strictAlong_of_level_eq Q hQ H R hT z hl).2
  change strictAlong R ((geoTransformAlong (barMarked Q) H).N ∩
    memberInter (geoTransformAlong (barMarked Q) H).E
      (membersThrough (geoTransformAlong (barMarked Q) H).E (origMembers Q H) (R.proj z))) =
    (geoTransformAlong (barMarked Q) (H.append R)).N ∩
      memberInter (geoTransformAlong (barMarked Q) (H.append R)).E
        (membersThrough (geoTransformAlong (barMarked Q) (H.append R)).E
          (origMembers Q (H.append R)) z) at hEq
  have h₀ : ∀ D ∈ origMembers Q H, D ∈ (geoTransformAlong (barMarked Q) H).E :=
    fun _ h => List.mem_of_mem_take h
  have h₁ : ∀ D ∈ origMembers Q (H.append R), D ∈ (geoTransformAlong (barMarked Q) (H.append R)).E :=
    fun _ h => List.mem_of_mem_take h
  rw [memberInter_membersThrough h₀, memberInter_membersThrough h₁] at hEq
  exact hEq

/-- Two real open restrictions preserve the whole selected trace. -/
theorem strictAlong_twice_restrict_preimage {n : ℕ} {Y Z : CMfd.{0} n}
    (R : BlowupTower Y Z) (W : Opens Y) (O : Opens (CMfd.of (n := n) W))
    (C : Set Y) :
    strictAlong (restrict O (restrict W R))
      ((fun x : O => (x.val.val : Y)) ⁻¹' C) =
      (fun x : openPreimage (restrict W R) O => x.val.val) ⁻¹' strictAlong R C := by
  change strictAlong (restrict O (restrict W R))
    ((Subtype.val : O → W) ⁻¹' ((Subtype.val : W → Y) ⁻¹' C)) =
      (Subtype.val : openPreimage (restrict W R) O → openPreimage R W) ⁻¹'
        ((Subtype.val : openPreimage R W → Z) ⁻¹' strictAlong R C)
  rw [strictAlong_restrict, strictAlong_restrict]

/-- The section bar carrier lies in the padded bar carrier. This follows
from the original carrier inclusion, independently of ideal marks. -/
theorem bar_carrier_subset_of_source_subset {n : ℕ} {X Y : CMfd.{0} n}
    (P Sec : MarkedIdeal n X) (hN : Sec.N ⊆ P.N) (H : BlowupTower X Y) :
    (geoTransformAlong (barMarked Sec) H).N ⊆ (geoTransformAlong (barMarked P) H).N := by
  rw [N_geoTransformAlong, N_geoTransformAlong]
  exact MemberInterTowerAlong.strictAlong_mono H hN

/-- The source identification can be checked as two geometric facts.
The companion carrier is the actual padded selected carrier in its
window. Within it the prescribed zero condition cuts out the section. -/
theorem source_zero_eq_selected_of_carrier_and_zero {n : ℕ} {X Y : CMfd.{0} n}
    (P Sec : MarkedIdeal n X) (hN : Sec.N ⊆ P.N) (hE : P.E = Sec.E)
    (H : BlowupTower X Y) (p : Y)
    (W : Opens Y) (O : Opens (CMfd.of (n := n) W))
    (B : MarkedIdeal n (CMfd.of (n := n) O)) (u : O → ℂ)
    (hCarrier : B.N = (fun x : O => (x.val.val : Y)) ⁻¹' selectedCarrier P H p)
    (hZero : ∀ x ∈ B.N, u x = 0 ↔ x.val.val ∈ (geoTransformAlong (barMarked Sec) H).N) :
    B.N ∩ {x | u x = 0} = (fun x : O => (x.val.val : Y)) ⁻¹' selectedCarrier Sec H p := by
  have hOld := origMembers_eq_of_E_eq hE H
  have hSub := bar_carrier_subset_of_source_subset P Sec hN H
  ext x
  constructor
  · rintro ⟨hx, hxU⟩
    have hSel : x.val.val ∈ selectedCarrier P H p := by
      change x ∈ B.N at hx
      rw [hCarrier] at hx
      exact hx
    exact ⟨(hZero x hx).mp hxU, fun D hD hpD => hSel.2 D (hOld.symm ▸ hD) hpD⟩
  · intro hx
    have hSec : x.val.val ∈ selectedCarrier Sec H p := hx
    have hxB : x ∈ B.N := hCarrier.symm ▸
      (show x ∈ (fun x : O => (x.val.val : Y)) ⁻¹' selectedCarrier P H p from
        ⟨hSub hSec.1, fun D hD hpD => hSec.2 D (hOld ▸ hD) hpD⟩)
    exact ⟨hxB, (hZero x hxB).mpr hSec.1⟩

set_option maxHeartbeats 950000 in
/-- For the actual initial order companion of the selected source tail,
its carrier is the twice-restricted padded selected carrier. -/
theorem initial_order_companion_carrier_selected {n s o : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (H : BlowupTower X Y) (p : Y) :
    let W := maskA P H p
    let A := CMfd.of (n := n) W
    let L : MarkedIdeal n A := lowerMarkedM (X := X) P (s+1) H p
    let O : Opens A := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) o
    let J : MarkedIdeal n (CMfd.of (n := n) O) := compAt (X := A) L o (.refl : BlowupTower A A)
    (barMarked (X := CMfd.of (n := n) O) J).N = (fun x : O => (x.val.val : Y)) ⁻¹' selectedCarrier P H p := by
  intro W A L O J
  have hComp : (barMarked (X := CMfd.of (n := n) O) J).N = (Subtype.val : O → W) ⁻¹' L.N := by
    change (compAt (X := A) L o (.refl : BlowupTower A A)).N = _
    unfold compAt companionOf
    rw [companionAlong_N]
    rfl
  rw [hComp]
  have hL : L.N = (Subtype.val : W → Y) ⁻¹' selectedCarrier P H p := by
    change (Subtype.val : W → Y) ⁻¹'
      ((geoTransformAlong (barMarked P) H).N ∩
        memberInter (geoTransformAlong (barMarked P) H).E
          (membersThrough (geoTransformAlong (barMarked P) H).E (origMembers P H) p)) = _
    have h₀ : ∀ D ∈ origMembers P H, D ∈ (geoTransformAlong (barMarked P) H).E :=
      fun _ h => List.mem_of_mem_take h
    rw [memberInter_membersThrough h₀]
    rfl
  rw [hL]
  rfl

set_option maxHeartbeats 1200000 in
/-- A zero companion of the actual initial order mask is section-special
under source prescribed-zero compatibility. The matching strict
selected-carrier germ at the endpoint is derived from the actual test. -/
theorem initial_order_zero_companion_special_iff_of_prescribed_source
    {n k s o : ℕ} {X Y Z : CMfd.{0} n} (hn : 0 < n) (P Sec : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hSec : IsInvDomain k Sec)
    (hClass : LocWPEquiv P Sec) (hE : P.E = Sec.E) (hN : Sec.N ⊆ P.N)
    (H : BlowupTower X Y) (R : BlowupTower Y Z) (hT : IsGeoTestTower P (H.append R))
    (z : Z) (hLevel : level P (H.append R) z = level P H (R.proj z))
    (hPos : 0 < level Sec (H.append R) z) (hp : R.proj z ∈ maskA P H (R.proj z)) :
    let W := maskA P H (R.proj z)
    let A := CMfd.of (n := n) W
    let L : MarkedIdeal n A := lowerMarkedM (X := X) P (s+1) H (R.proj z)
    let V := restrict W R
    let O : Opens A := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) o
    let J : MarkedIdeal n (CMfd.of (n := n) O) := compAt (X := A) L o (.refl : BlowupTower A A)
    let B := barMarked (X := CMfd.of (n := n) O) J
    let S := restrict O V
    let i : openPreimage V O → Z := fun x => x.val.val
    IsGeoTestTower L V →
    LocWPEquiv B (MarkedIdeal.pullback (Subtype.val : O → W) L) →
    B.IsWellFormed → 1 ≤ B.d →
    ∀ w : openPreimage V O, i w = z →
    w ∈ (geoTransformAlong B S).cosupp → level J S w = 0 →
    ∀ u : O → ℂ, IsTangentDirectionAlong B.N B.ideal B.d univ u →
    (∀ x ∈ B.N, u x = 0 ↔ x.val.val ∈ (geoTransformAlong (barMarked Sec) H).N) →
    (IsSpecial J S w ↔ IsSpecial Sec (H.append R) z) := by
  intro W A L V O J B S i hLV hPair hB hd w hwz hw hZero u hu hPrescribed
  have hFull := ((hClass.trans (bar_local_any_boundary Sec hSec)).wEquiv.2 (H.append R)).1.mp hT
  have hLevSec : level Sec (H.append R) z = level Sec H (R.proj z) :=
    (level_eq_of_E_eq hE (H.append R) z).symm.trans
      (hLevel.trans (level_eq_of_E_eq hE H (R.proj z)))
  have hC : B.N = (fun x : O => (x.val.val : Y)) ⁻¹' selectedCarrier P H (R.proj z) :=
    initial_order_companion_carrier_selected (s := s) (o := o) P H (R.proj z)
  have hSrc := source_zero_eq_selected_of_carrier_and_zero P Sec hN hE H (R.proj z)
    W O B u hC hPrescribed
  have hTr : strictAlong S (B.N ∩ {x | u x = 0}) =
      i ⁻¹' selectedCarrier Sec (H.append R) z := by
    rw [hSrc]
    exact (strictAlong_twice_restrict_preimage R W O _).trans
      (congrArg (fun D => i ⁻¹' D)
        (selectedCarrier_strictAlong Sec hSec.isWellFormed H R hFull z hLevSec))
  have hGerm : ∀ᶠ x in 𝓝 w, x ∈ strictAlong S (B.N ∩ {x | u x = 0}) ↔
      i x ∈ (geoTransformAlong (barMarked Sec) (H.append R)).N ∧
        ∀ D ∈ origMembers Sec (H.append R), z ∈ D → i x ∈ D := by
    exact Eventually.of_forall (fun x => by rw [hTr]; rfl)
  exact zero_companion_special_iff_of_selected_source_class (s := s) hn P Sec hP hSec hClass
    hE H R hT z hLevel hPos hp hLV O J hPair hB hd w hwz hw hZero u hu hGerm

end
end Hironaka.HironakaG1MixedPrescribedSelectedTrace
