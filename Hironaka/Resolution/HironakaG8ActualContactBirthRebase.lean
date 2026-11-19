import Hironaka.Resolution.HironakaG8ActualContactEndpoint
/-! # Actual contact birth rebasing and test suffix -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ActualContactBirthRebase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupRestrictOpen MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealOperationsAlong.MarkedIdeal
  DivisorExponentAlong HironakaG8DomainExponents HomogenizedGlueingTower TangentDirectionAlong StepOneValue ResolutionInvariantSpec
  HironakaG11InvBMLower HironakaG11InvBMStage HironakaG11InvBMRebase HironakaG11ActualContactTailTest

/-- At a literal birth of the actual contact coefficient record, the
geometric transform of the pre-birth contact is restricted-equivalent to
the actual post-birth contact. The literal restricted suffix tests both. -/
theorem actual_contact_birth_rebase
    {n : ℕ} {X Y Z W : CMfd.{0} n} (A : MarkedIdeal n X) {k : ℕ}
    (hA : IsInvDomain k A) (U : Opens X) {f : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (P : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (Q : BlowupTower Z W)
    (hT : IsGeoTestTower (barMarked A) ((BlowupTower.step P C π hπ).append Q)) :
    let V := openPreimage P U
    let V₁ : Opens Z := ⟨π ⁻¹' (V : Set Y), V.isOpen.preimage hπ.contMDiff.continuous⟩
    let ρ : V₁ → V := fun x => ⟨π x.val,x.2⟩
    let C' := (Subtype.val : V → Y) ⁻¹' C
    let L := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
    let L₁ := MarkedIdeal.pullback (Subtype.val : V₁ → Z) (contactCoeffBM A f (.step P C π hπ))
    L.IsWellFormed ∧ L.IsAdmissibleCentre C' ∧
      RestrictEquiv (L.geoTransform C' ρ) L₁ ∧
      (L.geoTransform C' ρ).IsWellFormed ∧ L₁.IsWellFormed ∧
      IsGeoTestTower L₁ (restrict V₁ Q) ∧
      IsGeoTestTower (L.geoTransform C' ρ) (restrict V₁ Q) := by
  let V := openPreimage P U
  let V₁ : Opens Z := ⟨π ⁻¹' (V : Set Y), V.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V₁ → V := fun x => ⟨π x.val,x.2⟩
  let C' := (Subtype.val : V → Y) ⁻¹' C
  let L := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
  let L₁ := MarkedIdeal.pullback (Subtype.val : V₁ → Z) (contactCoeffBM A f (.step P C π hπ))
  let One : BlowupTower Y Z := .step .refl C π hπ
  have hStepBar : IsGeoTestTower (barMarked A) (.step P C π hπ) :=
    (isGeoTestTower_append_iff (barMarked A) (.step P C π hπ) Q).mp hT |>.1
  have hStepA : IsGeoTestTower A (.step P C π hπ) :=
    ((StepOneBridge.barMarked_wEquiv A hA).2 _).1.mp hStepBar
  have hStepE := isGeoTestTower_emptyBoundary A _ hStepA
  have hStepC := isGeoTestTower_coeffEmptyBM hA.isWellFormed hA.one_le_d _ hStepE
  obtain ⟨hPC,hCC⟩ := (isGeoTestTower_step_iff (coeffEmptyBM A) P C π hπ).mp hStepC
  have hOneC : IsGeoTestTower (geoTransformAlong (coeffEmptyBM A) P) One := ⟨trivial,hCC⟩
  have hRE0 := restrictEquiv_tail_contactCoeffBM hA.isWellFormed hA.one_le_d U hf P hPC V (fun _ h => h) One hOneC
  have hRE : RestrictEquiv (L.geoTransform C' ρ) L₁ := by
    change RestrictEquiv (L.geoTransform C' ρ) L₁ at hRE0
    exact hRE0
  have hOneBar : IsGeoTestTower (barMarked A) (P.append One) := hStepBar
  have hTail0 := actual_contact_tail_test A hA U hf P One hOneBar
  have hL : L.IsWellFormed := hTail0.1
  have hCL : L.IsAdmissibleCentre C' := by
    have ht := hTail0.2
    change True ∧ L.IsAdmissibleCentre C' at ht
    exact ht.2
  have hLtrans : (L.geoTransform C' ρ).IsWellFormed := by
    have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hL (restrict V One) hTail0.2
    exact hw
  have hTail1 := actual_contact_tail_test A hA U hf (.step P C π hπ) Q hT
  have hL₁ : L₁.IsWellFormed := hTail1.1
  have hQ₁ : IsGeoTestTower (X := CMfd.of (n := n) V₁) L₁ (restrict V₁ Q) := hTail1.2
  have hweak := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv
    (X := CMfd.of (n := n) V₁) hRE
    hLtrans.isClosedSubmanifold_N.1 hLtrans.isCoherent hL₁.isCoherent
  have hQtrans := (hweak.2 (restrict V₁ Q)).1.mpr hQ₁
  exact ⟨hL,hCL,hRE,hLtrans,hL₁,hQ₁,hQtrans⟩


/-- Restricted equivalence survives a test tower, including the empty tower;
after the first blowup the two actual records are literally equal. -/
theorem restrictEquiv_geoTransformAlong_of_test
    {n : ℕ} {X Y : CMfd.{0} n} {M N : MarkedIdeal n X}
    (hM : M.IsWellFormed) (hN : N.ideal.IsCoherent) (h : RestrictEquiv M N)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    RestrictEquiv (geoTransformAlong M T) (geoTransformAlong N T) := by
  cases T with
  | refl => exact h
  | step T C π hπ =>
    have he := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq
      h hM.isClosedSubmanifold_N.1 hM.isCoherent hN T C π hπ
    rw [← he]
    exact RestrictEquiv.refl
      (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM (.step T C π hπ) hT).isCoherent

/-- Consequently, all boundary exponents agree at the endpoint of every
literal common test suffix of restricted-equivalent records. -/
theorem divExpAlong_geoTransformAlong_eq_of_restrictEquiv
    {n : ℕ} {X Y : CMfd.{0} n} {M N : MarkedIdeal n X}
    (hM : M.IsWellFormed) (hN : N.ideal.IsCoherent) (h : RestrictEquiv M N)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (H : Set Y) (y : Y) :
    divExpAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal H y =
      divExpAlong n (geoTransformAlong N T).N (geoTransformAlong N T).ideal H y :=
  divExpAlong_eq_of_restrictEquiv (restrictEquiv_geoTransformAlong_of_test hM hN h T hT) H y

end
end Hironaka.HironakaG8ActualContactBirthRebase
