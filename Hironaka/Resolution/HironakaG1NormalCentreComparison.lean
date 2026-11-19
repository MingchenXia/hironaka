import Hironaka.Resolution.HironakaG1PositiveNormalChronology

/-!
# Centre comparison from finite and top branch order

A recoding of finite native lower values and an upper cut for the realized
native-top stratum suffice to compare the original padded and native orders.
Each level has its own recoding and its own top-stratum value.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1NormalCentreComparison

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver StepOneValue CanonicalCentres
  MarkedIdealBiholomorphism RelativePrincipalizationSpan
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG8HomStable
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionInitialBar
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionStepOneHistory
  HironakaActualSectionBoundaryGeometry HironakaActualNativeSectionOrderHistory

section Order

variable {A B Λ Γ : Type*} [LinearOrder Λ] [LinearOrder Γ]

/-- A finite-branch recoding at each level and the order conditions on the
realized native-top points. The common padded value at native-top points can
be finite. Separation is required only at levels with both branches. -/
structure LowerBranchComparison (f : A → ℕ ×ₗ WithTop Λ) (g : B → ℕ ×ₗ WithTop Γ)
    (i : B → A) (S : Set B) where
  finiteMap : ℕ → Γ → WithTop Λ
  topValue : ℕ → WithTop Λ
  strictMono_finiteMap : ∀ s, StrictMono (finiteMap s)
  finite_eq : ∀ x ∈ S, ∀ v : Γ, (ofLex (g x)).2 = (v : WithTop Γ) →
    (ofLex (f (i x))).2 = finiteMap (ofLex (g x)).1 v
  top_eq : ∀ x ∈ S, (ofLex (g x)).2 = ⊤ →
    (ofLex (f (i x))).2 = topValue (ofLex (g x)).1
  finite_lt_top : ∀ x ∈ S, ∀ y ∈ S, (ofLex (g x)).1 = (ofLex (g y)).1 →
    ∀ v : Γ, (ofLex (g x)).2 = (v : WithTop Γ) → (ofLex (g y)).2 = ⊤ →
      finiteMap (ofLex (g x)).1 v < topValue (ofLex (g y)).1

variable {f : A → ℕ ×ₗ WithTop Λ} {g : B → ℕ ×ₗ WithTop Γ}
  {i : B → A} {S : Set B}

/-- The lower branch conditions reflect and preserve the full lexicographic order. -/
theorem LowerBranchComparison.le_iff (h : LowerBranchComparison f g i S)
    (hLevels : ∀ x ∈ S, (ofLex (f (i x))).1 = (ofLex (g x)).1)
    {x y : B} (hx : x ∈ S) (hy : y ∈ S) :
    f (i x) ≤ f (i y) ↔ g x ≤ g y := by
  simp only [Prod.Lex.le_iff, hLevels x hx, hLevels y hy]
  refine or_congr Iff.rfl (and_congr_right fun hLevel => ?_)
  by_cases hxTop : (ofLex (g x)).2 = ⊤
  · by_cases hyTop : (ofLex (g y)).2 = ⊤
    · simp only [h.top_eq x hx hxTop, h.top_eq y hy hyTop, hLevel, hxTop, hyTop, le_refl]
    · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hyTop
      have hlt := h.finite_lt_top y hy x hx hLevel.symm v hv.symm hxTop
      rw [h.top_eq x hx hxTop, h.finite_eq y hy v hv.symm, hxTop, ← hv]
      exact iff_of_false (not_le_of_gt hlt) (not_le_of_gt (WithTop.coe_lt_top v))
  · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hxTop
    by_cases hyTop : (ofLex (g y)).2 = ⊤
    · have hlt := h.finite_lt_top x hx y hy hLevel v hv.symm hyTop
      rw [h.finite_eq x hx v hv.symm, h.top_eq y hy hyTop, ← hv, hyTop]
      exact iff_of_true hlt.le le_top
    · obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hyTop
      rw [h.finite_eq x hx v hv.symm, h.finite_eq y hy w hw.symm, hLevel, ← hv, ← hw,
        WithTop.coe_le_coe]
      exact (h.strictMono_finiteMap _).le_iff_le

/-- The maximum loci agree as image and preimage, without requiring an
attained maximum or nonempty cosupport. -/
theorem LowerBranchComparison.max_loci (h : LowerBranchComparison f g i S)
    (hLevels : ∀ x ∈ S, (ofLex (f (i x))).1 = (ofLex (g x)).1)
    (hi : Function.Injective i) {T : Set A} (hImage : i '' S = T) :
    i '' maxLocus g S = maxLocus f T ∧ i ⁻¹' maxLocus f T = maxLocus g S := by
  have hMax : i '' maxLocus g S = maxLocus f T := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hmax⟩, rfl⟩
      refine ⟨hImage ▸ mem_image_of_mem i hx, fun y hy => ?_⟩
      obtain ⟨z, hz, rfl⟩ := hImage.symm ▸ hy
      exact (h.le_iff hLevels hz hx).mpr (hmax z hz)
    · rintro ⟨hy, hmax⟩
      obtain ⟨x, hx, rfl⟩ := hImage.symm ▸ hy
      refine ⟨x, ⟨hx, fun z hz => ?_⟩, rfl⟩
      exact (h.le_iff hLevels hz hx).mp (hmax _ (hImage ▸ mem_image_of_mem i hz))
  exact ⟨hMax, hMax ▸ preimage_image_eq _ hi⟩

end Order

/-- Once the preceding maxima compare, canonicality of the actual next
blowup is equivalent. An empty native centre gives an empty ambient centre,
and an ambient maximum centre pulls back to the native one. -/
theorem canonical_step_iff_of_max_loci_image {n m : ℕ} {Λ Γ : Type*}
    [LinearOrder Λ] [LinearOrder Γ] {X Y Z : CMfd.{0} n} {A B C : CMfd.{0} m}
    (M : MarkedIdeal n X) (K : MarkedIdeal m A) (T : BlowupTower X Y) (N : BlowupTower A B)
    (f : ∀ {Y' : CMfd.{0} n}, BlowupTower X Y' → Y' → Λ)
    (g : ∀ {B' : CMfd.{0} m}, BlowupTower A B' → B' → Γ)
    (i : B → Y) (hi : Function.Injective i)
    (hImage : i '' maxLocus (g N) (geoTransformAlong K N).cosupp =
      maxLocus (f T) (geoTransformAlong M T).cosupp)
    (hPrefix : IsCanonical M f T ↔ IsCanonical K g N)
    (D : Set B) (π : Z → Y) (ρ : C → B)
    (hπ : IsBlowupAlong n (i '' D) π) (hρ : IsBlowupAlong m D ρ) :
    IsCanonical M f (.step T (i '' D) π hπ) ↔ IsCanonical K g (.step N D ρ hρ) := by
  change (IsCanonical M f T ∧ (i '' D = ∅ ∨
      i '' D = maxLocus (f T) (geoTransformAlong M T).cosupp)) ↔
    (IsCanonical K g N ∧ (D = ∅ ∨ D = maxLocus (g N) (geoTransformAlong K N).cosupp))
  rw [← hImage]
  refine and_congr hPrefix (or_congr image_eq_empty ?_)
  constructor
  · intro h
    simpa only [preimage_image_eq _ hi] using congrArg (fun E => i ⁻¹' E) h
  · exact congrArg (fun E => i '' E)

set_option backward.isDefEq.respectTransparency false in
/-- Comparisons on the actual lifted predecessor prefixes give canonicality
equivalence for the entire history. The prefix quantifier asks only for stages
which have an actual nonempty ambient tail back to the given tower, and
whose native tail leads to the given native tower. -/
theorem Lift.canonical_iff_of_prefix_max_loci {n m : ℕ} {Λ Γ : Type*}
    [LinearOrder Λ] [LinearOrder Γ] {X Y : CMfd.{0} n} {hm : m ≤ n}
    {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x m}
    (M : MarkedIdeal n X) (K : MarkedIdeal m (nativeManifold hm W hW))
    (f : ∀ {Y' : CMfd.{0} n}, BlowupTower X Y' → Y' → Λ)
    (g : ∀ {Z' : CMfd.{0} m}, BlowupTower (nativeManifold hm W hW) Z' → Z' → Γ)
    {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀ y ∈ V, RegularAtDim (n := n) V y m}
    {N : BlowupTower (nativeManifold hm W hW) (nativeManifold hm V hV)}
    (hLift : Lift hm W hWc hW M.E T V hVc hV N)
    (hCompare : ∀ {Y' : CMfd.{0} n} (T' : BlowupTower X Y')
      {V' : Set Y'} {hV'c : IsClosed V'} {hV' : ∀ y ∈ V', RegularAtDim (n := n) V' y m}
      (N' : BlowupTower (nativeManifold hm W hW) (nativeManifold hm V' hV')),
      Lift hm W hWc hW M.E T' V' hV'c hV' N' →
      (∃ ambientTail : BlowupTower Y' Y, T'.append ambientTail = T ∧ 0 < ambientTail.length) →
      (∃ R : BlowupTower (nativeManifold hm V' hV') (nativeManifold hm V hV),
        N'.append R = N) →
      (Subtype.val : nativeManifold hm V' hV' → Y') ''
          maxLocus (g N') (geoTransformAlong K N').cosupp =
        maxLocus (f T') (geoTransformAlong M T').cosupp) :
    IsCanonical M f T ↔ IsCanonical K g N := by
  induction hLift with
  | refl => exact Iff.rfl
  | @step Y Z T V hVc hV N hLift D hD hint π hπ hNC ih =>
    let ρ := nativeProjection hm hVc hV D π hπ
    have hρ := nativeProjection_genuine hm hVc hV D hD hint π hπ
    have hPrefix := ih (by
      intro Y' T' V' hV'c hV' N' hLift' hT' hN'
      obtain ⟨ambientTail, hS, _⟩ := hT'
      obtain ⟨R, hR⟩ := hN'
      exact hCompare T' N' hLift'
        ⟨.step ambientTail _ π hπ, by rw [BlowupTower.append_step, hS], Nat.succ_pos _⟩
        ⟨.step R D ρ hρ, by rw [BlowupTower.append_step, hR]⟩)
    have hMax := hCompare T N hLift
      ⟨.step .refl _ π hπ, by rw [BlowupTower.append_step, BlowupTower.append_refl], Nat.succ_pos _⟩
      ⟨.step .refl D ρ hρ, by rw [BlowupTower.append_step, BlowupTower.append_refl]⟩
    exact canonical_step_iff_of_max_loci_image M K T N f g Subtype.val Subtype.val_injective
      hMax hPrefix D π ρ hπ hρ

section ActualStepOne

variable {n k : ℕ} {U : Opens (ComplexModel n)} (hn : 0 < n)
  (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
  {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
  (hT : IsGeoTestTower (properNormalMarked Q) T)
  {V : Set Y} {hVc : IsClosed V} {hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n}
  {N : BlowupTower (nativeManifold (Y := CMfd.of (n := n + 1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
    (nativeManifold (Nat.le_succ n) V hV)}
  {hWc : IsClosed (zeroPlane U)}
  (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc
    (zeroPlane_regular U) (sectionMarked Q).E T V hVc hV N)

local notation "X" => CMfd.of (n := n + 1) (productOpen U)
local notation "Yₙ" => nativeManifold (Nat.le_succ n) V hV
local notation "P" => properNormalMarked Q
local notation "B" => nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U)
  (zeroPlane_regular U) (sectionMarked Q)
local notation "i" => (Subtype.val : Yₙ → Y)
local notation "S" => (MarkedIdeal.cosupp (n := n + 1) (M := Y) (geoTransformAlong (Y := Y) P T))
local notation "Sₙ" => (MarkedIdeal.cosupp (n := n) (M := Yₙ) (geoTransformAlong (Y := Yₙ) B N))
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) P T
local notation "g" => Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k - 1)) B N

include hQ hT hLift in
set_option backward.isDefEq.respectTransparency false in
private theorem actual_step_one_geometry :
    i '' Sₙ = S ∧ ∀ w : Yₙ, level P T w.val = level B N w := by
  let Sec := sectionMarked Q
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hEq := properNormalMarked_locWPEquiv_section Q hQ
  have hCS : S = (geoTransformAlong Sec T).cosupp := (hEq.wEquiv.2 T).2 hT
  have hSupport : Sec.N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hTrans : NormalCrossings.IsTransverse (n + 1) (zeroPlane U) Sec.E := by
    change NormalCrossings.IsTransverse (n + 1) (liftedCarrier (univ : Set U))
      (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier _ _
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hPre : Sₙ = i ⁻¹' S := by
    rw [hCS]
    exact HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift
      (Nat.succ_pos n) hSec.isWellFormed.isSNCDivisor hTrans Sec rfl hSupport
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hSec.isWellFormed.isCoherent hg)
  have hRange : S ⊆ V := by
    rw [hCS]
    exact (geoTransformAlong Sec T).cosupp_subset_N.trans
      (HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift Sec hSupport)
  have hImage : i '' Sₙ = S := by
    rw [hPre, image_preimage_eq_inter_range, Subtype.range_coe]
    exact inter_eq_left.mpr hRange
  have hChron := actual_section_step_one_chronology U Q.N hQ.isWellFormed.isClosedSubmanifold_N
    Q.E hQ.isWellFormed.isSNCDivisor Sec.ideal hSec.isWellFormed.isCoherent Q.d hLift
  exact ⟨hImage, fun w =>
    (HironakaG8MemberLoci.level_eq_of_E_eq (show MarkedIdeal.E P = Sec.E from rfl) T w.val).trans
      (hChron.2.2.1 w).1⟩

private theorem stepOneInvM_level {d q : ℕ} {A C : CMfd.{0} d}
    (hd : 0 < d) (M : MarkedIdeal d A) (R : BlowupTower A C) (z : C) :
    (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hd q) M R z)).1 = level M R z :=
  Seq.StepOneValueMasked.stepOneInvL_fst (invFamily hd q) M
    (StepOneValueMasked.lowerMarkedM M) R z

include hQ hT hLift in
set_option backward.isDefEq.respectTransparency false in
/-- On the actual padded and literal native Step One histories, both maximum
loci are transported by the actual section inclusion under the lower branch
comparison. The first-component and cosupport comparisons are derived from
the original TEST and whole lifted history. -/
theorem positive_normal_max_loci_of_lower_branch_comparison
    (h : LowerBranchComparison f g i Sₙ) :
    i '' maxLocus g Sₙ = maxLocus f S ∧ i ⁻¹' maxLocus f S = maxLocus g Sₙ := by
  obtain ⟨hImage, hLevels⟩ := actual_step_one_geometry Q hQ T hT hLift
  have hFirst (w : Yₙ) : (ofLex (f (i w))).1 = (ofLex (g w)).1 :=
    (stepOneInvM_level (q := k) (Nat.succ_pos n) P T w.val).trans
      ((hLevels w).trans (stepOneInvM_level (q := k - 1) hn B N w).symm)
  exact h.max_loci (fun w _ => hFirst w) Subtype.val_injective hImage


include hQ hT hLift in
set_option backward.isDefEq.respectTransparency false in
/-- A comparison of the original padded and native lower branches on each
actual paired prefix transfers canonicality of the full Step One towers. -/
theorem positive_normal_canonical_iff_of_prefix_branch_comparisons
    (hRecoding : ∀ {Y' : CMfd.{0} (n + 1)} (T' : BlowupTower X Y')
      {V' : Set Y'} {hV'c : IsClosed V'}
      {hV' : ∀ y ∈ V', RegularAtDim (n := n + 1) V' y n}
      (N' : BlowupTower (nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Nat.le_succ n) V' hV')),
      Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) (sectionMarked Q).E
        T' V' hV'c hV' N' →
      (∃ ambientTail : BlowupTower Y' Y, T'.append ambientTail = T ∧ 0 < ambientTail.length) →
      (∃ R : BlowupTower (nativeManifold (Nat.le_succ n) V' hV') Yₙ, N'.append R = N) →
      Nonempty (LowerBranchComparison
        (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) P T')
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k - 1)) B N')
        (Subtype.val : nativeManifold (Nat.le_succ n) V' hV' → Y')
        (geoTransformAlong B N').cosupp)) :
    IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) P) T ↔
      IsCanonical B (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k - 1)) B) N := by
  apply Lift.canonical_iff_of_prefix_max_loci P B _ _ hLift
  intro Y' T' V' hV'c hV' N' hLift' hT' hN'
  have hTest' : IsGeoTestTower P T' := by
    obtain ⟨ambientTail, hS, _⟩ := hT'
    exact ((isGeoTestTower_append_iff P T' ambientTail).mp (hS.symm ▸ hT)).1
  obtain ⟨hRecoding'⟩ := hRecoding T' N' hLift' hT' hN'
  exact (positive_normal_max_loci_of_lower_branch_comparison hn Q hQ T' hTest' hLift' hRecoding').1

end ActualStepOne

end

end Hironaka.HironakaG1NormalCentreComparison
