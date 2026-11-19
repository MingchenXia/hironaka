import Hironaka.Resolution.HironakaDisjointCoherentNormalRecoding

/-! # Initial zero-level Step One maxima on the actual mark-one stabilization -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set

namespace Hironaka.HironakaG1InitialZeroRecodedCentres

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  HironakaDisjointCoherentNormalRecoding HironakaActualZeroCoordinateContactSeed
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaRelativeNormalIdeal GeneralValue NonmonomialOrderLocal NonmonomialOrderTail
  StepOneRegime CompanionRebase CompanionReductionAlong MonomialPartAlong
  HomogenizedIdealAlong HironakaSharpOriginalProductTraceOrder BlowupTowerTransforms
  MarkedIdealBiholomorphism

variable {n q : ℕ} {I : GermIdeal n (ComplexModel n)}

local notation "X₀" => CMfd.of (n := n) (ComplexModel n)
local notation "X₁" => CMfd.of (n := n + 1) (ComplexModel (n + 1))
local notation "C" => MarkedIdeal.cosupp (stabilizedMarked I)
local notation "D" => MarkedIdeal.cosupp (baseMarked I)
local notation "i" => tangentInclusion n 1

private theorem stabilized_cosupport_image (hI : I.IsCoherent) :
    i '' D = C := by
  rw [stabilized_cosupport hI]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa only [tangentProjection_tangentInclusion] using hx,
      actualJointNormalProjection_tangent n 1 x⟩
  · rintro ⟨hz, hzero⟩
    refine ⟨tangentProjection n 1 z, hz, ?_⟩
    have hq : actualJointNormalProjection n 1 z = 0 := hzero
    simpa only [HironakaActualIntrinsicStableAmbientIso.join, hq, map_zero, add_zero]
      using (join_projections (n := n) (m := 1) z)

set_option maxHeartbeats 900000 in
/-- The whole initial zero-level Step One maximum of the coherent
mark-one stabilization is the image of the native general maximum.
The two maximum sets also have exact preimage equality under the
actual zero-section inclusion. -/
theorem initial_zero_stepOne_max_loci (hn : 0 < n)
    (hI : IsInvDomain q (baseMarked I)) :
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
      (X := X₁) (stabilizedMarked I) .refl
    let g := (invFamily hn q).inv (X := X₀) (baseMarked I) .refl
    i '' maxLocus g D = maxLocus f C ∧ i ⁻¹' maxLocus f C = maxLocus g D := by
  intro f g
  have hCos : i '' D = C := stabilized_cosupport_image (I := I) hI.isWellFormed.isCoherent
  have hinj : Function.Injective i := fun x y h =>
    (tangentProjection_tangentInclusion n 1 x).symm.trans
      ((congrArg (tangentProjection n 1) h).trans (tangentProjection_tangentInclusion n 1 y))
  have hOrder (x y : ComplexModel n) (hx : x ∈ D) (hy : y ∈ D) :
      f (i x) ≤ f (i y) ↔ g x ≤ g y := by
    change Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
      (X := X₁) (stabilizedMarked I) .refl (i x) ≤
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
        (X := X₁) (stabilizedMarked I) .refl (i y) ↔ _
    rw [stabilized_stepOne_initial_value hn hI x hx, stabilized_stepOne_initial_value hn hI y hy]
    simp only [Prod.Lex.toLex_le_toLex, lt_self_iff_false, true_and, false_or, WithTop.coe_le_coe, g]
  have hImage : i '' maxLocus g D = maxLocus f C := by
    ext z
    constructor
    · rintro ⟨x, ⟨hx, hMax⟩, rfl⟩
      refine ⟨hCos ▸ mem_image_of_mem i hx, fun y hy => ?_⟩
      rw [← hCos] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      exact (hOrder w x hw hx).mpr (hMax w hw)
    · rintro ⟨hz, hMax⟩
      rw [← hCos] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨x, ⟨hx, fun w hw =>
        (hOrder w x hw hx).mp (hMax (i w) (hCos ▸ mem_image_of_mem i hw))⟩, rfl⟩
  exact ⟨hImage, hImage ▸ preimage_image_eq _ hinj⟩

/-- The fixed nonmonomial constructor of a maximal-order mark-one native
reader at its initial cut. -/
def nativeInitialCode (k : ℕ) (v : ℕ ×ₗ WithTop (ValTy k)) : ValTy (k + 1) :=
  toLex (1, Sum.inrₗ (v : WithTop (ℕ ×ₗ WithTop (ValTy k))))

theorem nativeInitialCode_strictMono (k : ℕ) : StrictMono (nativeInitialCode k) := by
  intro x y h
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Sum.Lex.inr_lt_inr_iff.mpr (WithTop.coe_lt_coe.mpr h)⟩)

set_option maxHeartbeats 1500000 in
/-- At genuine native maximal order the initial general read is a fixed
strict recoding of the literal native lower-depth Step One read. -/
theorem native_mark_one_initial_general_read (hn : 0 < n)
    (hI : IsInvDomain (q + 1) (baseMarked I))
    (hMax : IsMaximalOrderAlong (baseMarked I).N (baseMarked I).ideal (baseMarked I).d)
    (x : ComplexModel n) (hx : x ∈ D) :
    (invFamily hn (q + 1)).inv (X := X₀) (baseMarked I) .refl x =
      nativeInitialCode q (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q)
        (X := X₀) (baseMarked I) .refl x) := by
  let J : MarkedIdeal n X₀ := baseMarked I
  let T : BlowupTower X₀ X₀ := .refl
  let R := invFamily hn q
  let O := ordMask (M := X₀) J 1
  let F := fun {A : CMfd.{0} n} (L : MarkedIdeal n A) {B : CMfd.{0} n}
    (S : BlowupTower A B) (y : B) => Seq.StepOneValueMasked.stepOneInvM R L S y
  have hCoh : I.IsCoherent := hI.isWellFormed.isCoherent
  have hOrdGe (d : ℕ) : ordGe (M := X₀) J d = GermIdealOrder.cosupport n univ I d :=
    ordGe_ordinaryTraceMarked_eq_cosupport (X := X₀) univ I hCoh d
  have hNot : x ∉ ordGe (M := X₀) J 2 := by
    rw [hOrdGe]
    exact hMax x
  have hOrder : nmOrd (M := X₀) J x = 1 := by
    apply Nat.le_antisymm (nmOrd_le_of_notMem hNot)
    apply (mem_ordGe_iff hI.isWellFormed hI.isNonzeroAlongAt (J.cosupp_subset_N hx) 1).mp
    rw [hOrdGe]
    exact hx
  have hm : x ∈ O :=
    (mem_ordMask_iff hn (M := X₀) (𝔫 := J) hI.isWellFormed hI.isNonzeroAlongAt 1 x).mpr hNot
  let J' : MarkedIdeal n (CMfd.of (n := n) O) := MarkedIdeal.pullback (Subtype.val : O → X₀) J
  have hJ' : IsInvDomain (q + 1) J' := InvDomainTowerAlong.isInvDomain_pullback_val O hI
  have hRecord : compAt (X := X₀) J 1 T = J' := by
    change companionOf n (M := CMfd.of (n := n) O) J' 1 = J'
    simp only [companionOf, companionAlong, show J'.d = 1 from rfl, lt_self_iff_false, if_false]
    have hN : J'.N = univ := preimage_univ
    have hE : J'.E = [] := rfl
    rw [hE, hN, nonmonomialPartAlong_nil_eq_restrictOn,
      BlowupTowerTransforms.restrictOn_univ hJ'.isWellFormed.isCoherent]
    exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN.symm hE.symm rfl rfl
  have hStep := StepOneSeq.isMaxOrderValue_stepOneInvM (k := q + 1) R hn
  have hRestr := hStep.restrictOpen J hI hMax O T
    (by trivial) (⟨x, hm⟩ : openPreimage T O) hx
  rw [invFamily_succ, generalStep_inv]
  change genInv (X := X₀) F J T x = _
  rw [genInv_of_nmOrd_ne_zero (X := X₀) F J T hOrder (by decide)]
  change toLex (1, Sum.inrₗ (genLowerValue (X := X₀) F J 1 T T x)) = _
  rw [genLowerValue_eq_of_mem (X := X₀) F J (T₀ := T) (T₁ := T) hm, hRecord]
  exact congrArg (nativeInitialCode q) hRestr

/-- The exact padded zero-level value inserts a finite native general
constructor around the literal native lower-depth Step One read. -/
theorem initial_zero_stepOne_literal_read (hn : 0 < n)
    (hI : IsInvDomain (q + 1) (baseMarked I))
    (hMax : IsMaximalOrderAlong (baseMarked I).N (baseMarked I).ideal (baseMarked I).d)
    (x : ComplexModel n) (hx : x ∈ D) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (q + 1))
      (X := X₁) (stabilizedMarked I) .refl (i x) =
    toLex (0, (nativeInitialCode q (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q)
      (X := X₀) (baseMarked I) .refl x) : WithTop (ValTy (q + 1)))) := by
  rw [stabilized_stepOne_initial_value hn hI x hx,
    native_mark_one_initial_general_read hn hI hMax x hx]

set_option maxHeartbeats 900000 in
/-- Literal Step One at the lower native depth has the exact padded
maximum image for this maximal-order empty-boundary mark-one class. -/
theorem initial_zero_stepOne_literal_max_loci (hn : 0 < n)
    (hI : IsInvDomain (q + 1) (baseMarked I))
    (hMax : IsMaximalOrderAlong (baseMarked I).N (baseMarked I).ideal (baseMarked I).d) :
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (q + 1))
      (X := X₁) (stabilizedMarked I) .refl
    let g := Seq.StepOneValueMasked.stepOneInvM (invFamily hn q)
      (X := X₀) (baseMarked I) .refl
    i '' maxLocus g D = maxLocus f C ∧ i ⁻¹' maxLocus f C = maxLocus g D := by
  intro f g
  have hOrder (x y : ComplexModel n) (hx : x ∈ D) (hy : y ∈ D) :
      (invFamily hn (q + 1)).inv (X := X₀) (baseMarked I) .refl x ≤
        (invFamily hn (q + 1)).inv (X := X₀) (baseMarked I) .refl y ↔ g x ≤ g y := by
    rw [native_mark_one_initial_general_read hn hI hMax x hx,
      native_mark_one_initial_general_read hn hI hMax y hy]
    exact (nativeInitialCode_strictMono q).le_iff_le
  have hG : maxLocus ((invFamily hn (q + 1)).inv (X := X₀) (baseMarked I) .refl) D =
      maxLocus g D := by
    ext x
    constructor
    · rintro ⟨hx, hm⟩
      exact ⟨hx, fun y hy => (hOrder y x hy hx).mp (hm y hy)⟩
    · rintro ⟨hx, hm⟩
      exact ⟨hx, fun y hy => (hOrder y x hy hx).mpr (hm y hy)⟩
  have hMain := initial_zero_stepOne_max_loci hn hI
  change i '' maxLocus ((invFamily hn (q + 1)).inv (X := X₀) (baseMarked I) .refl) D =
    maxLocus f C ∧ i ⁻¹' maxLocus f C =
      maxLocus ((invFamily hn (q + 1)).inv (X := X₀) (baseMarked I) .refl) D at hMain
  rw [hG] at hMain
  exact hMain

end
end Hironaka.HironakaG1InitialZeroRecodedCentres
