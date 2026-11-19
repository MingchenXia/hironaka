import Hironaka.Resolution.HironakaG8LabelledNativeHistory
import Hironaka.Invariant.StepOneTangentChange

/-! Recover the first physical phase and its actual labelled suffix,
including after arbitrary verified restrictions and transports. -/

set_option autoImplicit false
set_option maxHeartbeats 3600000

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LabelledNativeHead

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealTowerTransport HironakaEmbeddedAnalytic
  HironakaHolomorphicJetChartInvariance HironakaG8NativePhaseCertificate HironakaG8LabelledNativeHistory
  HironakaActualVanishingIntrinsicHSTransport HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsSeparationChoiceComparison HironakaActualOpenEmbeddingVanishingIdeal
  HironakaEmbeddedBoundary HironakaResolutionSpaceLocal HironakaOriginalCanonicalDimensionList
  HironakaSmoothSubmersionOriginalGlobalFinite HomogenizedGlueingTower StepOneTangentChange
  BlowupTowerIsoTail

variable {n : ℕ}

private abbrev original {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) : MarkedIdeal n X :=
  ⟨univ,E,vanishingIdeal (n := n) W,1⟩

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)

def HasHeadPhase {X Y : CMfd.{0} n} (W : Set X) (E : List (Set X)) (K : Set X)
    (T : BlowupTower X Y) (H : ℕ → ℕ) (L : List (ℕ → ℕ)) : Prop :=
  ∃ (A Z : CMfd.{0} n) (P : BlowupTower X A) (Q : BlowupTower A Z)
    (χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z),
    ActualNativePhase W E H P ∧
    (∀ x ∈ K ∩ singularSet (n := n) W, toLex (HS[W] x) ≤ toLex H) ∧
    (∀ h ∈ L, toLex h < toLex H) ∧
    LabelledNativeTower n (strictTransform n P.proj W) (geoTransformAlong (original W E) P).E
      (P.proj ⁻¹' K) Q L ∧
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) T (P.append Q) χ

private theorem HasHeadPhase.restrictOpen {X Y : CMfd.{0} n}
    {W K : Set X} {E : List (Set X)} {T : BlowupTower X Y}
    {H : ℕ → ℕ} {L : List (ℕ → ℕ)} (h : HasHeadPhase W E K T H L)
    (hW : IsComplexAnalyticSubset (n := n) W) (O : Opens X) :
    HasHeadPhase ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·))
      ((Subtype.val : O → X) ⁻¹' K) (restrict O T) H L := by
  obtain ⟨A,Z,P,Q,χ,hPhase,hTop,hOrder,hTail,hIso⟩ := h
  let U := openPreimage P O
  let P₀ := restrict O P
  let Q₀ := restrict U Q
  let W₀ := (Subtype.val : O → X) ⁻¹' W
  let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let K₀ := (Subtype.val : O → X) ⁻¹' K
  have hCarrier : strictTransform n P₀.proj W₀ =
      (Subtype.val : U → A) ⁻¹' strictTransform n P.proj W :=
    strictTransform_restricted_tower O P W
  have hBoundary : (geoTransformAlong (original W₀ E₀) P₀).E =
      (geoTransformAlong (original W E) P).E.map ((Subtype.val : U → A) ⁻¹' ·) := by
    have hMark : MarkedIdeal.pullback (Subtype.val : O → X) (original W E) =
        original (X := CMfd.of (n := n) O) W₀ E₀ := pullback_val_mk_vanishingIdeal O E W
    have hGeo := MarkedIdealRestrictOpen.geoTransformAlong_restrict O isClosedSubmanifold_univ
      (CartanIrreducible.cartanCoherence W hW) P hPhase.test
    rw [hMark] at hGeo
    exact congrArg MarkedIdeal.E hGeo
  have hTask : P₀.proj ⁻¹' K₀ = (Subtype.val : U → A) ⁻¹' (P.proj ⁻¹' K) := by
    ext z
    change (P₀.proj z).val ∈ K ↔ P.proj z.val ∈ K
    exact iff_of_eq (congrArg (· ∈ K) (proj_restrict O P z))
  have hTr := hTail.restrictOpen U
  have hTr' : LabelledNativeTower n (strictTransform n P₀.proj W₀)
      (geoTransformAlong (original W₀ E₀) P₀).E (P₀.proj ⁻¹' K₀) Q₀ L := by
    rw [hCarrier,hBoundary,hTask]
    exact hTr
  have hTop₀ : ∀ z ∈ K₀ ∩ singularSet (n := n) W₀, toLex (HS[W₀] z) ≤ toLex H := by
    rintro z ⟨hz,hzSing⟩
    change z ∈ singularSet (n := n) ((Subtype.val : O → X) ⁻¹' W) at hzSing
    rw [singularSet_preimage_val] at hzSing
    change toLex (HS[(Subtype.val : O → X) ⁻¹' W] z) ≤ toLex H
    rw [funext (hilbertSamuelAt_vanishing_actual_open_any O W z)]
    exact hTop z.val ⟨hz,hzSing⟩
  have hBase : ∀ x : X, x ∈ O ↔ (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) X ∞) x ∈ O := fun _ => Iff.rfl
  have hr := isTowerIso_restrictOpens hBase hIso (isTowerIso_mem_openPreimage_iff hIso hBase)
  have hr' := BlowupTowerSplitIso.IsTowerIso.congr_base hr
    (Φ' := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) O) ∞) (fun z => Subtype.ext rfl)
  let η := (diffeoOpens χ (openPreimage T O) (openPreimage (P.append Q) O)
    (isTowerIso_mem_openPreimage_iff hIso hBase)).trans (opensCongr (openPreimage_append P Q O).symm)
  have hc := hr'.trans (isTowerIso_restrict_append O P Q)
  refine ⟨_,_,P₀,Q₀,η,hPhase.restrictOpen hW O,hTop₀,hOrder,hTr',?_⟩
  simpa only [Diffeomorph.refl_trans] using hc

private theorem HasHeadPhase.of_isTowerIso {X X' Y Y' : CMfd.{0} n}
    {W K : Set X} {E : List (Set X)} {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    {H : ℕ → ℕ} {L : List (ℕ → ℕ)} (h : HasHeadPhase W E K T H L)
    (hW : IsComplexAnalyticSubset (n := n) W)
    {φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {ψ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T ψ) :
    HasHeadPhase (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) (φ ⁻¹' K) T' H L := by
  obtain ⟨A,Z,P,Q,χ,hPhase,hTop,hOrder,hTail,hFact⟩ := h
  let p := transport φ P
  let q := transport p.back Q
  let W₀ := φ ⁻¹' W
  let E₀ := E.map (φ ⁻¹' ·)
  let K₀ := φ ⁻¹' K
  have hP := transport_isTowerIso φ P
  have hQ := transport_isTowerIso p.back Q
  have hPhase₀ := hPhase.of_isTowerIso hW hP
  have hCarrier : strictTransform n p.tower.proj W₀ =
      p.back ⁻¹' strictTransform n P.proj W :=
    strictTransform_preimage_of_square φ p.back p.tower.contMDiff_proj P.contMDiff_proj W
      hW.isClosed (fun z => (hP.proj_comm z).symm)
  have hBoundary : (geoTransformAlong (original W₀ E₀) p.tower).E =
      (geoTransformAlong (original W E) P).E.map (p.back ⁻¹' ·) := by
    have hMark : MarkedIdeal.pullback φ (original W E) = original (X := X') W₀ E₀ := by
      change (MarkedIdeal.mk (φ ⁻¹' univ) E₀
        (GermIdeal.pullback (m := n) φ (vanishingIdeal (n := n) W)) 1 : MarkedIdeal n X') = _
      rw [preimage_univ,pullback_vanishingIdeal_of_biholomorphism]
    have hGeo := IsTowerIso.geoTransformAlong_eq φ isClosedSubmanifold_univ
      (CartanIrreducible.cartanCoherence W hW) hP hPhase.test
    rw [hMark] at hGeo
    exact congrArg MarkedIdeal.E hGeo
  have hTask : p.tower.proj ⁻¹' K₀ = p.back ⁻¹' (P.proj ⁻¹' K) := by
    ext z
    change φ (p.tower.proj z) ∈ K ↔ P.proj (p.back z) ∈ K
    rw [hP.proj_comm]
  have hTr := hTail.of_isTowerIso hQ
  have hTr' : LabelledNativeTower n (strictTransform n p.tower.proj W₀)
      (geoTransformAlong (original W₀ E₀) p.tower).E (p.tower.proj ⁻¹' K₀) q.tower L := by
    rw [hCarrier,hBoundary,hTask]
    exact hTr
  have hTop₀ : ∀ z ∈ K₀ ∩ singularSet (n := n) W₀, toLex (HS[W₀] z) ≤ toLex H := by
    rintro z ⟨hz,hzSing⟩
    change z ∈ singularSet (n := n) (φ ⁻¹' W) at hzSing
    rw [singularSet_preimage_eq (isSubmersion_biholomorphism φ)] at hzSing
    change toLex (HS[φ ⁻¹' W] z) ≤ toLex H
    rw [funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any φ W z)]
    exact hTop (φ z) ⟨hz,hzSing⟩
  have hPhysical : IsTowerIso φ T' (P.append Q) (ψ.trans χ) := by
    simpa only [Diffeomorph.trans_refl] using hIso.trans hFact
  have hc := hPhysical.trans (hP.append hQ).symm
  refine ⟨_,_,p.tower,q.tower,(ψ.trans χ).trans q.back.symm,hPhase₀,hTop₀,hOrder,hTr',?_⟩
  apply BlowupTowerSplitIso.IsTowerIso.congr_base hc
  exact fun z => (φ.symm_apply_apply z).symm

/-- Nonempty labels expose the same literal physical head phase and its
terminal native data through all previous restrictions and transports. -/
theorem exists_head_phase {X Y : CMfd.{0} n} {W K : Set X} {E : List (Set X)}
    {T : BlowupTower X Y} {L : List (ℕ → ℕ)} (h : LabelledNativeTower n W E K T L) :
    ∀ H L₀, L = H :: L₀ → HasHeadPhase W E K T H L₀ := by
  induction h with
  | smooth _ _ _ => intro H L hEq; cases hEq
  | @phase X A Y W E K S T H L hW hE hTop hPhase hOrder hTail ih =>
    intro H₀ L₀ he
    cases he
    exact ⟨A,Y,S,T,_,hPhase,hTop,hOrder,hTail,IsTowerIso.refl_self _⟩
  | restrictOpen h O ih =>
    intro H L he
    exact (ih H L he).restrictOpen h.source_analytic O
  | of_isTowerIso h hIso ih =>
    intro H L he
    exact (ih H L he).of_isTowerIso h.source_analytic hIso

/-- A finished labelled history has no stages and its initial carrier
was smooth, even if its current description is up to a tower isomorphism. -/
theorem finished_of_empty_labels {X Y : CMfd.{0} n} {W K : Set X} {E : List (Set X)}
    {T : BlowupTower X Y} {L : List (ℕ → ℕ)} (h : LabelledNativeTower n W E K T L) :
    L = [] → T.length = 0 ∧ IsClosedSubmanifold n W := by
  induction h with
  | smooth _ _ hW => exact fun _ => ⟨rfl,hW⟩
  | phase _ _ _ _ _ _ _ => intro h; cases h
  | @restrictOpen X Y W E K T L h O ih =>
    intro hNil
    obtain ⟨hLen,hW⟩ := ih hNil
    exact ⟨(length_restrict O T).trans hLen,BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O⟩
  | @of_isTowerIso X X' Y Y' W E K T T' L h φ χ hIso ih =>
    intro hNil
    obtain ⟨hLen,hW⟩ := ih hNil
    exact ⟨hIso.length_eq.trans hLen,(isClosedSubmanifold_preimage_iff φ).mpr hW⟩

end
end Hironaka.HironakaG8LabelledNativeHead
