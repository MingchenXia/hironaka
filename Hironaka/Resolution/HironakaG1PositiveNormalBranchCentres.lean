import Hironaka.Resolution.HironakaG1PositiveNormalChronology
import Hironaka.Resolution.HironakaActualNativeSectionOrderHistory

/-!
# Maximum loci at a positive section-special endpoint

The actual padded and section values can have distinct second components
at the same positive top level. The native maximum is the top stratum,
while membership of the anchor in the padded maximum still depends on
the finite padded lower values at that level.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalBranchCentres

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver StepOneValue CanonicalCentres
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG8HomStable
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionInitialBar
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionStepOneHistory
  HironakaActualSectionBoundaryGeometry HironakaActualNativeSectionOrderHistory
  RelativePrincipalizationSpan MarkedIdealBiholomorphism
open HomogenizedIdealAlong (IsMaximalOrderAlong)

private theorem maxLocus_top_branch {A Λ : Type*} [LinearOrder Λ]
    (f : A → ℕ ×ₗ WithTop Λ) (S : Set A) (a : A) (s : ℕ)
    (ha : a ∈ S) (hTop : f a = toLex (s, ⊤))
    (hLevel : ∀ x ∈ S, (ofLex (f x)).1 ≤ s) :
    maxLocus f S = {x | x ∈ S ∧ (ofLex (f x)).1 = s ∧ (ofLex (f x)).2 = ⊤} := by
  have hBound (x : A) (hx : x ∈ S) : f x ≤ f a := by
    rw [hTop, Prod.Lex.le_iff]
    rcases (hLevel x hx).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, le_top⟩
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    have hEq := le_antisymm (hBound x hx) (hmax a ha)
    simp [hEq, hTop, hx]
  · rintro ⟨hx, hfirst, hlower⟩
    have hEq : f x = f a := by
      rw [hTop]
      exact congrArg toLex (Prod.ext hfirst hlower)
    exact ⟨hx, fun y hy => (hBound y hy).trans_eq hEq.symm⟩

private theorem mem_maxLocus_top_level_iff {A Λ : Type*} [LinearOrder Λ]
    (f : A → ℕ ×ₗ WithTop Λ) (S : Set A) (a : A) (s : ℕ)
    (ha : a ∈ S) (hTop : (ofLex (f a)).1 = s)
    (hLevel : ∀ x ∈ S, (ofLex (f x)).1 ≤ s) :
    a ∈ maxLocus f S ↔
      ∀ x ∈ S, (ofLex (f x)).1 = s → (ofLex (f x)).2 ≤ (ofLex (f a)).2 := by
  constructor
  · intro h x hx he
    rcases Prod.Lex.le_iff.mp (h.2 x hx) with hlt | ⟨_, hle⟩
    · exact (Nat.not_lt_of_ge (he.trans hTop.symm).ge hlt).elim
    · exact hle
  · intro h
    refine ⟨ha, fun x hx => Prod.Lex.le_iff.mpr ?_⟩
    rcases (hLevel x hx).lt_or_eq with hlt | he
    · exact Or.inl (hlt.trans_eq hTop.symm)
    · exact Or.inr ⟨he.trans hTop.symm, h x hx he⟩

/-- A native maximum can define a native canonical successor and fail to
define an ambient canonical successor along its exact image, even when both
steps are admissible tests. The obstruction
is a native maximum point whose ambient image has a strictly larger competitor. -/
theorem canonical_step_mismatch_of_native_maximum {n m : ℕ} {Λ Γ : Type*}
    [LinearOrder Λ] [LinearOrder Γ] {X Y Z : CMfd.{0} n} {A B C : CMfd.{0} m}
    (M : MarkedIdeal n X) (K : MarkedIdeal m A) (T : BlowupTower X Y) (N : BlowupTower A B)
    (f : ∀ {Y' : CMfd.{0} n}, BlowupTower X Y' → Y' → Λ)
    (g : ∀ {B' : CMfd.{0} m}, BlowupTower A B' → B' → Γ)
    (i : B → Y) (z : B) (hz : z ∈ maxLocus (g N) (geoTransformAlong K N).cosupp)
    (w : Y) (hw : w ∈ (geoTransformAlong M T).cosupp) (hBetter : f T (i z) < f T w)
    (hCan : IsCanonical K g N)
    (hT : IsGeoTestTower M T) (hN : IsGeoTestTower K N)
    (hAdmM : (geoTransformAlong M T).IsAdmissibleCentre
      (i '' maxLocus (g N) (geoTransformAlong K N).cosupp))
    (hAdmK : (geoTransformAlong K N).IsAdmissibleCentre (maxLocus (g N) (geoTransformAlong K N).cosupp))
    (π : Z → Y) (ρ : C → B)
    (hπ : IsBlowupAlong n (i '' maxLocus (g N) (geoTransformAlong K N).cosupp) π)
    (hρ : IsBlowupAlong m (maxLocus (g N) (geoTransformAlong K N).cosupp) ρ) :
    IsGeoTestTower M (.step T _ π hπ) ∧ IsGeoTestTower K (.step N _ ρ hρ) ∧
      IsCanonical K g (.step N _ ρ hρ) ∧ ¬ IsCanonical M f (.step T _ π hπ) := by
  refine ⟨⟨hT, hAdmM⟩, ⟨hN, hAdmK⟩, ⟨hCan, Or.inr rfl⟩, ?_⟩
  have hzImage : i z ∈ i '' maxLocus (g N) (geoTransformAlong K N).cosupp :=
    mem_image_of_mem i hz
  rintro ⟨_, hEmpty | hMax⟩
  · rw [hEmpty] at hzImage
    exact hzImage
  · rw [hMax] at hzImage
    exact (not_lt_of_ge (hzImage.2 w hw)) hBetter

private theorem stepOneInvM_first {n q : ℕ} {X Y : CMfd.{0} n}
    (hn : 0 < n) (P : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) :
    (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) P T y)).1 = level P T y :=
  Seq.StepOneValueMasked.stepOneInvL_fst (invFamily hn q) P (StepOneValueMasked.lowerMarkedM P) T y

private theorem stepOneInvM_finite_of_nonspecial {n q d : ℕ} {X Y : CMfd.{0} n}
    (hn : 0 < n) (P : MarkedIdeal n X) (hP : IsInvDomain d P)
    (hMax : IsMaximalOrderAlong P.N P.ideal P.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked P) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked P) T).cosupp)
    (hNS : ¬ IsSpecial P T y) :
    (ofLex (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) P T y)).2 ≠ ⊤ := by
  change (ofLex (Seq.StepOneValueMasked.stepOneInvL (invFamily hn q) P
    (StepOneValueMasked.lowerMarkedM P) T y)).2 ≠ ⊤
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial _ P _ T hNS]
  exact Seq.StepOneValueMasked.lowerValueL_ne_top P (invFamily hn q) hP.isWellFormed hP.one_le_d
    hn hMax _ T hT hy hNS

set_option maxHeartbeats 240000 in
set_option backward.isDefEq.respectTransparency false in
/-- On the actual section lift, a section-special anchor at the highest
positive level attains the native maximum. Its padded lower value is
finite, and it attains the padded maximum exactly when every other
padded lower value at the same level is at most that finite value. -/
theorem positive_normal_branch_max_loci {n k s : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T)
    {V : Set Y} {hVc : IsClosed V} {hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n}
    {N : BlowupTower (nativeManifold (Y := CMfd.of (n := n + 1) (productOpen U))
      (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)) (nativeManifold (Nat.le_succ n) V hV)}
    {hWc : IsClosed (zeroPlane U)}
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc
      (zeroPlane_regular U) (sectionMarked Q).E T V hVc hV N)
    (z : nativeManifold (Nat.le_succ n) V hV)
    (hz : z.val ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hTop : level (properNormalMarked Q) T z.val = s + 1)
    (hLevel : ∀ x ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp,
      level (properNormalMarked Q) T x ≤ s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T z.val)
    (hSpecial : IsSpecial (sectionMarked Q) T z.val) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let B := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (sectionMarked Q)
    let P := properNormalMarked Q
    let S := (geoTransformAlong P T).cosupp
    let Sₙ := (geoTransformAlong B N).cosupp
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) P T
    let g := Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k - 1)) B N
    Sₙ = (Subtype.val : V → Y) ⁻¹' S ∧
      (Subtype.val : V → Y) '' Sₙ = S ∧
      (ofLex (f z.val)).2 ≠ ⊤ ∧
      z ∈ maxLocus g Sₙ ∧
      maxLocus g Sₙ = {w | w ∈ Sₙ ∧ level P T w.val = s + 1 ∧ (ofLex (g w)).2 = ⊤} ∧
      (z.val ∈ maxLocus f S ↔ ∀ x ∈ S, level P T x = s + 1 →
        (ofLex (f x)).2 ≤ (ofLex (f z.val)).2) ∧
      (∀ w ∈ S, level P T w = s + 1 → (ofLex (f z.val)).2 < (ofLex (f w)).2 →
        f z.val < f w ∧ (Subtype.val : V → Y) '' maxLocus g Sₙ ≠ maxLocus f S) := by
  intro X B P S Sₙ f g
  let Sec := sectionMarked Q
  have hP := properNormalMarked_isInvDomain Q hQ
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hEq := properNormalMarked_locWPEquiv_section Q hQ
  have hCS : S = (geoTransformAlong Sec T).cosupp := (hEq.wEquiv.2 T).2 hT
  have hSupport : Sec.N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hTrans : NormalCrossings.IsTransverse (n + 1) (zeroPlane U) Sec.E := by
    change NormalCrossings.IsTransverse (n + 1) (liftedCarrier (univ : Set U))
      (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier _ _
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hPre : Sₙ = (Subtype.val : V → Y) ⁻¹' S := by
    rw [hCS]
    exact HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift
      (Nat.succ_pos n) hSec.isWellFormed.isSNCDivisor hTrans Sec rfl hSupport
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hSec.isWellFormed.isCoherent hg)
  have hRange : S ⊆ V := by
    rw [hCS]
    exact (geoTransformAlong Sec T).cosupp_subset_N.trans
      (HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift Sec hSupport)
  have hImage : (Subtype.val : V → Y) '' Sₙ = S := by
    rw [hPre, image_preimage_eq_inter_range, Subtype.range_coe]
    exact inter_eq_left.mpr hRange
  have hChron := actual_section_step_one_chronology U Q.N hQ.isWellFormed.isClosedSubmanifold_N
    Q.E hQ.isWellFormed.isSNCDivisor Sec.ideal hSec.isWellFormed.isCoherent Q.d hLift
  have hLevels (w : nativeManifold (Nat.le_succ n) V hV) : level P T w.val = level B N w :=
    (HironakaG8MemberLoci.level_eq_of_E_eq (show P.E = Sec.E from rfl) T w.val).trans (hChron.2.2.1 w).1
  have hzSpecial : IsSpecial B N z := (hChron.2.2.1 z).2.mp hSpecial
  have hzNative : z ∈ Sₙ := hPre.symm ▸ hz
  have hPBar := bar_local_any_boundary (X := X) P hP
  have hTBar := ((hPBar.wEquiv.2 T).1).mp hT
  have hzBar := ((hPBar.wEquiv.2 T).2 hT).symm ▸ hz
  have hFinite : (ofLex (f z.val)).2 ≠ ⊤ := by
    have hFin := stepOneInvM_finite_of_nonspecial (q := k) (Nat.succ_pos n) P hP
      (properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent) T hTBar z.val hzBar hNS
    exact hFin
  have hgTop : g z = toLex (s + 1, ⊤) := by
    change Seq.StepOneValueMasked.stepOneInvL (invFamily hn (k - 1)) B
      (StepOneValueMasked.lowerMarkedM B) N z = toLex (s + 1, ⊤)
    rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial _ B _ N hzSpecial, ← hLevels z, hTop]
  have hgLevel (w : nativeManifold (Nat.le_succ n) V hV) : (ofLex (g w)).1 = level P T w.val :=
    (stepOneInvM_first (q := k - 1) hn B N w).trans (hLevels w).symm
  have hfLevel (x : Y) : (ofLex (f x)).1 = level P T x :=
    stepOneInvM_first (q := k) (Nat.succ_pos n) P T x
  have hMax := maxLocus_top_branch g Sₙ z (s + 1) hzNative hgTop
    (fun w hw => (hgLevel w).trans_le (hLevel w.val ((Set.ext_iff.mp hPre w).mp hw)))
  simp only [hgLevel] at hMax
  have hzMax : z ∈ maxLocus g Sₙ := by
    rw [hMax]
    exact ⟨hzNative, hTop, congrArg (fun w => (ofLex w).2) hgTop⟩
  have hfMax : z.val ∈ maxLocus f S ↔ ∀ x ∈ S, level P T x = s + 1 →
      (ofLex (f x)).2 ≤ (ofLex (f z.val)).2 := by
    simpa only [hfLevel] using mem_maxLocus_top_level_iff f S z.val (s + 1) hz
      ((hfLevel z.val).trans hTop) (fun x hx => (hfLevel x).trans_le (hLevel x hx))
  refine ⟨hPre, hImage, hFinite, hzMax, hMax, hfMax, ?_⟩
  intro w hw hwLevel hBetter
  refine ⟨Prod.Lex.lt_iff.mpr (Or.inr
    ⟨(hfLevel z.val).trans (hTop.trans (hwLevel.symm.trans (hfLevel w).symm)), hBetter⟩), ?_⟩
  intro hEqMax
  have hPadMax : z.val ∈ maxLocus f S := hEqMax ▸ mem_image_of_mem (Subtype.val : V → Y) hzMax
  exact (not_lt_of_ge (hfMax.mp hPadMax w hw hwLevel)) hBetter

end

end Hironaka.HironakaG1PositiveNormalBranchCentres
