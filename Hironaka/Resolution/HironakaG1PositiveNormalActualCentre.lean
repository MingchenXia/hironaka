import Hironaka.Resolution.HironakaG1PositiveNormalChronology

/-!
# The actual centres at the positive section restart

The two adjacent steps of an actual native lift have literal corresponding
centres. At a strict positive restart the original projected special point
lies on the ambient centre, and its native projection lies on the native one.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalActualCentre

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec StepOneValue StepOneRegime
  HironakaActualNativeSectionFiniteHistory HironakaG1PositiveNormalChronology
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaActualNativeSectionInitialBar
  HironakaActualOpenZeroSectionDifferentials
open HomogenizedGlueingTower (strictAlong)

set_option backward.isDefEq.respectTransparency false in
private theorem adjacent_last_step {n k : ℕ} {X Y Z : CMfd.{0} n} {B : CMfd.{0} k}
    {hk : k ≤ n} {W : Set X} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀ y ∈ V, RegularAtDim (n := n) V y k}
    (T : BlowupTower X Y) (N : BlowupTower B (nativeManifold hk V hV))
    (hRange : V = strictAlong T W)
    (D : Set (nativeManifold hk V hV)) (hD : IsClosedSubmanifold k D)
    (hint : interior D = ∅) (π : Z → Y) (hπ : IsBlowupAlong n ((Subtype.val : V → Y) '' D) π) :
    let T' := T.step ((Subtype.val : V → Y) '' D) π hπ
    let ρ := nativeProjection hk hVc hV D π hπ
    let N' := N.step D ρ (nativeProjection_genuine hk hVc hV D hD hint π hπ)
    ∃ (i : (split N' 1).1 → (split T' 1).1)
      (D' : Set (split N' 1).1) (π' : (split T' 0).1 → (split T' 1).1)
      (ρ' : (split N' 0).1 → (split N' 1).1)
      (hπ' : IsBlowupAlong n (i '' D') π') (hρ' : IsBlowupAlong k D' ρ'),
      head T' 0 = .step (head T' 1) (i '' D') π' hπ' ∧
      head N' 0 = .step (head N' 1) D' ρ' hρ' ∧
      Function.Injective i ∧ range i = strictAlong (head T' 1) W ∧
      ∀ z, i ((tail N' 1).proj z) = (tail T' 1).proj z.val := by
  let ρ := nativeProjection hk hVc hV D π hπ
  have hρ := nativeProjection_genuine hk hVc hV D hD hint π hπ
  have hr : range (Subtype.val : nativeManifold hk V hV → Y) = strictAlong T W :=
    Subtype.range_coe.trans hRange
  cases T <;> cases N <;>
    exact ⟨Subtype.val, D, π, ρ, hπ, hρ, rfl, rfl, Subtype.val_injective, hr, fun _ => rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual centre one step before the given split is the image of the
native centre under the inclusion of the corresponding native stage. -/
theorem Lift.adjacent_centres {n k : ℕ} {X Y : CMfd.{0} n} {hk : k ≤ n}
    {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x k}
    {E : List (Set X)} {T : BlowupTower X Y}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀ y ∈ V, RegularAtDim (n := n) V y k}
    {N : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW E T V hVc hV N) (j : ℕ) (hj : j < T.length) :
    ∃ (i : (split N (j + 1)).1 → (split T (j + 1)).1)
      (D : Set (split N (j + 1)).1)
      (π : (split T j).1 → (split T (j + 1)).1)
      (ρ : (split N j).1 → (split N (j + 1)).1)
      (hπ : IsBlowupAlong n (i '' D) π) (hρ : IsBlowupAlong k D ρ),
      head T j = .step (head T (j + 1)) (i '' D) π hπ ∧
      head N j = .step (head N (j + 1)) D ρ hρ ∧
      Function.Injective i ∧ range i = strictAlong (head T (j + 1)) W ∧
      ∀ z : nativeManifold hk V hV, i ((tail N (j + 1)).proj z) = (tail T (j + 1)).proj z.val := by
  induction h generalizing j with
  | refl => exact (Nat.not_lt_zero _ hj).elim
  | @step Y Z T V hVc hV N h D hD hint π hπ hNC ih =>
    cases j with
    | zero => exact adjacent_last_step T N h.carrier D hD hint π hπ
    | succ j =>
      have hj' : j < T.length := Nat.lt_of_succ_lt_succ hj
      obtain ⟨i, D₀, π₀, ρ₀, hπ₀, hρ₀, hT₀, hN₀, hi, hRange, hSquare⟩ := ih j hj'
      exact ⟨i, D₀, π₀, ρ₀, hπ₀, hρ₀, hT₀, hN₀, hi, hRange,
        fun z => hSquare (nativeProjection hk hVc hV D π hπ z)⟩

set_option backward.isDefEq.respectTransparency false in
/-- At a strict positive restart on the given actual lift, the projected
native point lies in the actual native centre. The ambient centre is its
literal image under the previous-stage section inclusion. -/
theorem positive_normal_native_restart_centre {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T)
    {hWc : IsClosed (zeroPlane U)} {E : List (Set (productOpen U))}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n}
    {N : BlowupTower
      (nativeManifold (Y := CMfd.of (n := n + 1) (productOpen U))
        (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
      (nativeManifold (Nat.le_succ n) V hV)}
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) E T V hVc hV N)
    (z : nativeManifold (Nat.le_succ n) V hV)
    (hSecNS : ¬ IsSpecial (sectionMarked Q) T z.val)
    (hStrict : regimeRun (stepRegime (sectionMarked Q) (s + 1)) T z.val <
      regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T z.val) :
    let r := regimeRun (stepRegime (sectionMarked Q) (s + 1)) T z.val
    let p := (tail T (r + 1)).proj z.val
    let b := (tail N (r + 1)).proj z
    ∃ (i : (split N (r + 1)).1 → (split T (r + 1)).1)
      (D : Set (split N (r + 1)).1) (C : Set (split T (r + 1)).1)
      (π : (split T r).1 → (split T (r + 1)).1)
      (ρ : (split N r).1 → (split N (r + 1)).1)
      (hπ : IsBlowupAlong (n + 1) C π) (hρ : IsBlowupAlong n D ρ),
      head T r = .step (head T (r + 1)) C π hπ ∧
      head N r = .step (head N (r + 1)) D ρ hρ ∧
      Function.Injective i ∧ range i = strictAlong (head T (r + 1)) (zeroPlane U) ∧
      i '' D = C ∧ i ⁻¹' C = D ∧ i b = p ∧ b ∈ D ∧ p ∈ C ∧
      IsSpecial (sectionMarked Q) (head T (r + 1)) p := by
  intro r p b
  have hr : r < T.length :=
    hStrict.trans_le (regimeRun_le_length (stepRegime (properNormalMarked Q) (s + 1)) T z.val)
  obtain ⟨i, D, π, ρ, hπ, hρ, hAmbient, hNative, hi, hRange, hSquare⟩ :=
    Lift.adjacent_centres hLift r hr
  obtain ⟨C, π₀, hπ₀, hAmbient₀, _, hp⟩ :=
    positive_normal_section_restart_centre Q hQ (s := s) T hT z.val hSecNS hStrict
  have hCentre : i '' D = C :=
    eq_of_heq (BlowupTower.step.inj (hAmbient.symm.trans hAmbient₀)).2.2.1
  have hb : b ∈ D := by
    have hpImage : p ∈ i '' D := hCentre.symm ▸ hp
    obtain ⟨a, ha, hab⟩ := hpImage
    have hab' : a = b := hi (hab.trans (hSquare z).symm)
    simpa only [← hab'] using ha
  have hSpecial := (positive_normal_section_run_cutoff Q (s := s) T hT z.val hStrict).2.2
  have hp' : p ∈ i '' D := hCentre.symm ▸ hp
  exact ⟨i, D, i '' D, π, ρ, hπ, hρ, hAmbient, hNative, hi, hRange,
    rfl, preimage_image_eq D hi, hSquare z, hb, hp', hSpecial⟩

end

end Hironaka.HironakaG1PositiveNormalActualCentre
