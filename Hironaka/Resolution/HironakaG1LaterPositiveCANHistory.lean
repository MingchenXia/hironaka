import Hironaka.Resolution.HironakaG1LaterPositiveStratumCentres

/-!
# Canonicality along a literal native lift from realized later positive tuples
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LaterPositiveCANHistory

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres StepOneValue
  StepOneValueMasked HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaActualOpenZeroSectionDifferentials HironakaG1LaterPositiveBranchOrder
  HironakaG1LaterPositiveStratumCentres HironakaG1NormalCentreComparison
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionFiniteHistory
  HironakaActualSectionBoundaryGeometry HironakaActualNativeSectionInitialBar
  HironakaG1ProperCarrierNormalLocalClass

variable {n k : ℕ} {U : Opens (ComplexModel n)} (hn : 0 < n) (Q : MarkedIdeal n U)

variable {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
  {V : Set Y} {hV : ∀ x ∈ V, RegularAtDim (n := n + 1) V x n}
  (N : BlowupTower (nativeManifold (Y := CMfd.of (n := n + 1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
    (nativeManifold (Nat.le_succ n) V hV))

local notation "X" => CMfd.of (n := n + 1) (productOpen U)
local notation "P" => properNormalMarked Q
local notation "B" => nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U)
  (zeroPlane_regular U) (sectionMarked Q)
local notation "A" => nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P
local notation "g" => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) B

local notation "Z" => nativeManifold (Nat.le_succ n) V hV
local notation "ι" => (Subtype.val : Z → Y)
local notation "C" => (MarkedIdeal.cosupp (n := n + 1) (M := Y) (geoTransformAlong (Y := Y) P T))
local notation "D" => (MarkedIdeal.cosupp (n := n) (M := Z) (geoTransformAlong (Y := Z) B N))

/-- Readback at a matched prefix. The positive case compares the actual
padded tuples to the literal native values at the common highest level. -/
inductive PrefixRead : Prop
  | exactMax : (ι '' maxLocus (g N) D = maxLocus (f T) C) → PrefixRead
  | empty (hNative : D = ∅) (hPadded : C = ∅) : PrefixRead
  | positive (s : ℕ) (hImage : ι '' D = C)
      (hLevel : ∀ x ∈ D, level B N x = level P T (ι x))
      (hBound : ∀ x ∈ D, level B N x ≤ s + 1)
      (hTop : ∃ x ∈ D, level B N x = s + 1)
      (F : ∀ x : {x : Z // x ∈ D ∧ level B N x = s + 1},
        LaterPositiveRead Q T (ι x.val) k s)
      (hOrder : ∀ x y, laterTuple (F x) < laterTuple (F y) ↔ g N x.val < g N y.val) :
      PrefixRead

private theorem value_lt_of_level_lt {d q : ℕ} {M W : CMfd.{0} d}
    (hd : 0 < d) (J : MarkedIdeal d M) (L : BlowupTower M W) {x y : W}
    (h : level J L x < level J L y) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hd q) J L x <
      Seq.StepOneValueMasked.stepOneInvM (invFamily hd q) J L y := by
  rw [Prod.Lex.lt_iff, Seq.StepOneValueMasked.stepOneInvL_fst,
    Seq.StepOneValueMasked.stepOneInvL_fst]
  exact Or.inl h

set_option maxHeartbeats 700000 in
/-- Each permitted prefix branch determines the exact whole-cosupport
maximum image for the native inclusion. -/
theorem PrefixRead.max_image (h : PrefixRead (k := k) hn Q T N) :
    ι '' maxLocus (g N) D = maxLocus (f T) C := by
  rcases h with h | ⟨hNative, hPadded⟩ | ⟨s, hImage, hLevel, hBound, ⟨t, htD, htLevel⟩, F, hOrder⟩
  · exact h
  · rw [hNative, hPadded]
    simp [maxLocus]
  have hDom (x : Z) (hx : x ∈ D) (y : Z) (hy : y ∈ D)
      (hxy : level B N x < level B N y) :
      g N x < g N y ∧ f T (ι x) < f T (ι y) := by
    refine ⟨value_lt_of_level_lt (q := k) hn B N hxy, ?_⟩
    exact value_lt_of_level_lt (q := k + 1) (Nat.succ_pos n) P T
      ((hLevel x hx).symm.trans_lt (hxy.trans_eq (hLevel y hy)))
  have hCompare (x y : Z) (hx : x ∈ D) (hy : y ∈ D)
      (hxTop : level B N x = s + 1) (hyTop : level B N y = s + 1) :
      g N x ≤ g N y ↔ f T (ι x) ≤ f T (ι y) := by
    have hlt : f T (ι y) < f T (ι x) ↔ g N y < g N x :=
      (upper_lt_iff_later_tuple_lt (F ⟨y, hy, hyTop⟩) (F ⟨x, hx, hxTop⟩)).trans
        (hOrder ⟨y, hy, hyTop⟩ ⟨x, hx, hxTop⟩)
    simpa only [not_lt] using not_congr hlt.symm
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hMax⟩, rfl⟩
    have hxTop : level B N x = s + 1 := by
      by_contra hne
      exact (not_lt_of_ge (hMax t htD))
        (hDom x hx t htD ((lt_of_le_of_ne (hBound x hx) hne).trans_eq htLevel.symm)).1
    refine ⟨hImage ▸ mem_image_of_mem ι hx, fun y hy => ?_⟩
    rw [← hImage] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    by_cases hwTop : level B N w = s + 1
    · exact (hCompare w x hw hx hwTop hxTop).mp (hMax w hw)
    · exact (hDom w hw x hx ((lt_of_le_of_ne (hBound w hw) hwTop).trans_eq hxTop.symm)).2.le
  · rintro ⟨hz, hMax⟩
    rw [← hImage] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxTop : level B N x = s + 1 := by
      by_contra hne
      exact (not_lt_of_ge (hMax (ι t) (hImage ▸ mem_image_of_mem ι htD)))
        (hDom x hx t htD ((lt_of_le_of_ne (hBound x hx) hne).trans_eq htLevel.symm)).2
    refine ⟨x, ⟨hx, fun w hw => ?_⟩, rfl⟩
    by_cases hwTop : level B N w = s + 1
    · exact (hCompare w x hw hx hwTop hxTop).mpr
        (hMax (ι w) (hImage ▸ mem_image_of_mem ι hw))
    · exact (hDom w hw x hx ((lt_of_le_of_ne (hBound w hw) hwTop).trans_eq hxTop.symm)).1.le

variable {hWc : IsClosed (zeroPlane U)} {hVc : IsClosed V}

set_option maxHeartbeats 700000 in
/-- The actual paired predecessor cuts suffice for equivalence of whole
canonical histories. A cut can supply a positive realized comparison,
empty cosupports, or an exact maximum readback such as one from a zero
level or special branch. -/
theorem canonical_iff_of_later_positive_prefix_reads
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc
      (zeroPlane_regular U) (sectionMarked Q).E T V hVc hV N)
    (hRead : ∀ {Y' : CMfd.{0} (n + 1)} (T' : BlowupTower X Y')
      {V' : Set Y'} {hV'c : IsClosed V'} {hV' : ∀ y ∈ V', RegularAtDim (n := n + 1) V' y n}
      (N' : BlowupTower A (nativeManifold (Nat.le_succ n) V' hV')),
      Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) (sectionMarked Q).E
        T' V' hV'c hV' N' →
      (∃ ambientTail : BlowupTower Y' Y, T'.append ambientTail = T ∧ 0 < ambientTail.length) →
      (∃ R : BlowupTower (nativeManifold (Nat.le_succ n) V' hV') Z, N'.append R = N) →
      PrefixRead (k := k) hn Q T' N') :
    IsCanonical P f T ↔ IsCanonical B g N := by
  apply Lift.canonical_iff_of_prefix_max_loci P B f g hLift
  intro Y' T' V' hV'c hV' N' hLift' hT' hN'
  exact (hRead T' N' hLift' hT' hN').max_image

end

end Hironaka.HironakaG1LaterPositiveCANHistory
