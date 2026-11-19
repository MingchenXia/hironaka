import Hironaka.Resolution.HironakaG1InitialFiniteSectionUpperRead
import Hironaka.Resolution.HironakaG1LaterPositiveCANHistory
import Hironaka.Resolution.HironakaG1SupportedStepOne

/-! # Initial highest-level maxima on the padded and literal native sources -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1InitialLiteralNativeTopCentres

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres StepOneValue
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionInitialBar HironakaActualSectionBoundaryGeometry
  HironakaActualNativeSectionOrderHistory HironakaG1InitialFiniteSectionUpperRead
  HironakaG1LaterPositiveCANHistory HironakaG1SupportedStepOne
  HironakaG1NormalCentreComparison NormalCrossings HomogenizedIdealAlong HironakaG8MemberLoci
  HironakaG8HomStable HironakaActualCentreJointJets HironakaG1ProperCarrierNormalContact
  MemberInterLocusAlong HironakaRelativeNormalIdeal

set_option maxHeartbeats 900000 in
/-- The vertical fibre lies in every incident padded original member.
Nearby nonzero fibre points leave the actual padded cosupport, so positive
padded specialness cannot occur at the initial cut. -/
theorem initial_padded_positive_not_special {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hp : p ∈ (properNormalMarked Q).cosupp)
    (hLevel : 0 < level (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p) :
    ¬ IsSpecial (properNormalMarked Q)
      (BlowupTower.refl (X := CMfd.of (n := n+1) (productOpen U))) p := by
  let X := CMfd.of (n := n+1) (productOpen U)
  let P := properNormalMarked Q
  let T : BlowupTower X X := .refl
  have hBarCos : (barMarked (X := X) P).cosupp = P.cosupp :=
    (((bar_local_any_boundary (X := X) P (properNormalMarked_isInvDomain Q hQ)).wEquiv.2 T).2 trivial).symm
  have hImage : P.cosupp = zeroSection U '' Q.cosupp := properNormalMarked_cosupp Q hQ
  rw [hImage] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  let u (v : ComplexModel 1) : ComplexModel (n+1) :=
    tangentInclusion n 1 x.val + actualJointNormalInclusion n 1 v
  have hFirst (v : ComplexModel 1) : tangentProjection n 1 (u v) = x.val := by
    simp only [u, map_add, tangentProjection_tangentInclusion,
      tangentProjection_actualJointNormalInclusion, add_zero]
  have hLast (v : ComplexModel 1) : actualJointNormalProjection n 1 (u v) = v := by
    simp only [u, map_add, actualJointNormalProjection_tangent,
      actualJointNormalProjection_inclusion, zero_add]
  let c (v : ComplexModel 1) : productOpen U := ⟨u v, by
    change tangentProjection n 1 (u v) ∈ U
    rw [hFirst]
    exact x.property⟩
  have hProj (v : ComplexModel 1) : projection U (c v) = x := Subtype.ext (hFirst v)
  have hZero : c 0 = zeroSection U x := by
    apply Subtype.ext
    change u 0 = tangentInclusion n 1 x.val
    simp [u]
  have hContinuous : Continuous c :=
    (continuous_const.add (actualJointNormalInclusion n 1).continuous).subtype_mk _
  rintro (⟨h0, _⟩ | ⟨_, hMem⟩)
  · exact (Nat.ne_of_gt hLevel) h0
  have hOrig : origMembers P T = P.E := by rw [origMembers, geoTransformAlong_refl]; exact List.take_length
  rw [show origMembers (properNormalMarked Q) (.refl (X := X)) = P.E from hOrig, geoTransformAlong_refl] at hMem
  change zeroSection U x ∈ memberInterLocus (barMarked (X := X) P).N P.E
    (barMarked (X := X) P).cosupp at hMem
  rw [hBarCos, mem_memberInterLocus_iff] at hMem
  have ht : Tendsto c (𝓝 0) (𝓝 (zeroSection U x)) := hZero ▸ hContinuous.continuousAt
  have hNear := ht.eventually hMem.2
  have hN : x ∈ Q.N := Q.cosupp_subset_N hx
  have hEq : ∀ᶠ v : ComplexModel 1 in 𝓝 0, v = 0 := hNear.mono fun v hv => by
    have hCarrier : c v ∈ (barMarked (X := X) P).N := by
      change projection U (c v) ∈ Q.N
      rw [hProj]
      exact hN
    have hBoundary : ∀ H ∈ P.E, zeroSection U x ∈ H → c v ∈ H := by
      intro H hH hxH
      change H ∈ Q.E.map (projection U ⁻¹' ·) at hH
      obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hH
      change projection U (c v) ∈ D
      have hp0 : projection U (zeroSection U x) = x := hZero ▸ hProj 0
      rw [hProj]
      exact hp0 ▸ hxH
    have hvC := hv hCarrier hBoundary
    rw [hImage] at hvC
    obtain ⟨w, _, he⟩ := hvC
    have hh := congrArg (fun z : productOpen U => actualJointNormalProjection n 1 z.val) he
    change actualJointNormalProjection n 1 (tangentInclusion n 1 w.val) =
      actualJointNormalProjection n 1 (u v) at hh
    rwa [actualJointNormalProjection_tangent, hLast, eq_comm] at hh
  have hNE : ∀ᶠ v : ComplexModel 1 in 𝓝[≠] 0, v ∈ ({0} : Set (ComplexModel 1))ᶜ :=
    self_mem_nhdsWithin
  obtain ⟨_, hne, heq⟩ := (hNE.and (hEq.filter_mono nhdsWithin_le_nhds)).exists
  exact hne (mem_singleton_iff.mpr heq)

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (hn : 0 < n) (Q : MarkedIdeal n U)
  (hQ : IsInvDomain (k + 1) Q) (hWc : IsClosed (zeroPlane U))

local notation "X₀" => CMfd.of (n := n + 1) (productOpen U)
local notation "A₀" => nativeManifold (Y := X₀) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)
local notation "P" => properNormalMarked Q
local notation "SEC" => sectionMarked Q
local notation "B₀" => nativePullback (Y := X₀) (Nat.le_succ n) (zeroPlane U)
  (zeroPlane_regular U) SEC
local notation "T₀" => BlowupTower.refl (X := X₀)
local notation "N₀" => BlowupTower.refl (X := A₀)
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P
local notation "g" => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) B₀
local notation "fM" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) SEC


private theorem maxLocus_eq_of_strictly_below {Y Λ : Type*} [LinearOrder Λ]
    (v : Y → Λ) (C S : Set Y) (hSub : S ⊆ C) (hS : S.Nonempty)
    (hLt : ∀ x ∈ C, x ∉ S → ∀ y ∈ S, v x < v y) :
    maxLocus v C = maxLocus v S := by
  ext x
  constructor
  · rintro ⟨hx, hm⟩
    refine ⟨?_, fun y hy => hm y (hSub hy)⟩
    by_contra hNot
    obtain ⟨y, hy⟩ := hS
    exact (not_lt_of_ge (hm y (hSub hy))) (hLt x hx hNot y hy)
  · rintro ⟨hx, hm⟩
    refine ⟨hSub hx, fun y hy => ?_⟩
    by_cases h : y ∈ S
    · exact hm y h
    · exact (hLt y hy h x hx).le

private theorem step_lt_of_level_lt {d q : ℕ} {Y : CMfd.{0} d}
    (hd : 0 < d) (J : MarkedIdeal d Y) {x y : Y}
    (hlt : level J .refl x < level J .refl y) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hd q) J .refl x <
      Seq.StepOneValueMasked.stepOneInvM (invFamily hd q) J .refl y := by
  rw [Prod.Lex.lt_iff, Seq.StepOneValueMasked.stepOneInvL_fst,
    Seq.StepOneValueMasked.stepOneInvL_fst]
  exact Or.inl hlt

local notation "C₀" => (MarkedIdeal.cosupp (properNormalMarked Q))
local notation "TopSlice" => Set.ofPred (fun p : X₀ => p ∈ C₀ ∧ level P T₀ p = s + 1)

include hQ hWc in
set_option maxHeartbeats 900000 in
/-- At the genuine initial paired cut, the positive same-level comparison
against the section reader gives the exact whole native maximum image.
The padded positive anchors are automatically nonspecial. Their section
values may be finite or special, and lower-level points are unrestricted. -/
theorem initial_literal_native_top_max_image
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hBound : ∀ p ∈ C₀, level P T₀ p ≤ s + 1)
    (hTop : (TopSlice).Nonempty) :
    (Subtype.val : A₀ → X₀) '' maxLocus (g N₀)
        (MarkedIdeal.cosupp (n := n) (M := A₀) (geoTransformAlong (Y := A₀) B₀ N₀)) =
      maxLocus (f T₀) (geoTransformAlong P T₀).cosupp := by
  have hM : IsInvDomain (k + 1) SEC :=
    section_projected_domain _ Q.N Q.E Q.ideal Q.d hQ
  have hSupport : (SEC).N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hTrans : IsTransverse (n + 1) (zeroPlane U) (SEC).E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) (SEC).E
      T₀ (zeroPlane U) hWc (zeroPlane_regular U) N₀ := .refl
  have hCan : IsCanonical SEC fM T₀ := by trivial
  have hNative := (Lift.original_same_bound_step_one_max_loci (q := k) (X := X₀) (hk := Nat.le_succ n)
    (W := zeroPlane U) (hW := zeroPlane_regular U) (T := T₀)
    (V := zeroPlane U) (hV := zeroPlane_regular U) (Q := N₀)
    (Nat.succ_pos n) hn SEC hM hSupport hTrans hMax hLift hCan).2
  have hc : (P).cosupp = (SEC).cosupp :=
    (properNormalMarked_locWPEquiv_section Q hQ).cosupp_eq_base
  have hLevel : ∀ p : X₀, level P T₀ p = level SEC T₀ p :=
    level_eq_of_E_eq (A := P) (B := SEC) rfl T₀
  let i : TopSlice → X₀ := Subtype.val
  have hi : range i = TopSlice := Subtype.range_coe
  have hRead := (initial_positive_literal_section_stratum Q hQ (s := s) i
    (fun a => ⟨a.property.1, a.property.2, initial_padded_positive_not_special Q hQ a.val a.property.1
      (a.property.2.symm ▸ Nat.succ_pos s)⟩)).2
  rw [hi] at hRead
  have hDom (x : X₀) (hx : x ∈ C₀) (hxNot : x ∉ TopSlice)
      (y : X₀) (hy : y ∈ TopSlice) : level P T₀ x < level P T₀ y := by
    exact (lt_of_le_of_ne (hBound x hx) (fun h => hxNot ⟨hx, h⟩)).trans_eq hy.2.symm
  have hPMax : maxLocus (f T₀) C₀ = maxLocus (f T₀) TopSlice :=
    maxLocus_eq_of_strictly_below _ _ _ (fun _ h => h.1) hTop fun x hx hxn y hy =>
      step_lt_of_level_lt (q := k + 1) (Y := X₀) (Nat.succ_pos n) P (hDom x hx hxn y hy)
  have hSMax : maxLocus (fM T₀) C₀ = maxLocus (fM T₀) TopSlice :=
    maxLocus_eq_of_strictly_below _ _ _ (fun _ h => h.1) hTop fun x hx hxn y hy =>
      step_lt_of_level_lt (q := k) (Y := X₀) (Nat.succ_pos n) SEC
        ((hLevel x).symm.trans_lt ((hDom x hx hxn y hy).trans_eq (hLevel y)))
  change _ = maxLocus (f T₀) C₀
  rw [hNative]
  change maxLocus (fM T₀) (SEC).cosupp = _
  rw [← hc, hSMax, hPMax]
  exact hRead.symm

include hQ hWc in
/-- This actual initial paired prefix requires no supplied order comparison
or maximum image to provide a history readback. -/
theorem initial_literal_native_top_prefix_read
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hBound : ∀ p ∈ C₀, level P T₀ p ≤ s + 1)
    (hTop : (TopSlice).Nonempty) :
    PrefixRead (k := k) hn Q T₀ N₀ :=
  PrefixRead.exactMax (initial_literal_native_top_max_image hn Q hQ hWc hMax hBound hTop)

end
end Hironaka.HironakaG1InitialLiteralNativeTopCentres
