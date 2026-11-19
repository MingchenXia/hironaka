import Hironaka.Resolution.HironakaG1PositiveNormalChronology
import Hironaka.Resolution.HironakaSmoothSubmersionCanonicalValueDimensionShift
import Hironaka.Resolution.HironakaG1ProperCarrierNormalLocalClass
import Hironaka.Analytic.PointSupportedIdealPrincipalization
import Hironaka.Blowup.BlowupExistenceOriginIdeal
import Hironaka.Resolution.HironakaPrincipalizationBoundary
import Hironaka.Resolution.HironakaEmbeddedReducible

/-!
# A positive padded nonspecial point with a special section

The point at the origin has one original boundary member. Its intersection
with the section is a point, whereas in the padded carrier it contains the
whole normal fibre.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalSpecialExample

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec StepOneValue StepOneRegime BoundaryCount MemberInterLocusAlong
  NormalCrossings NormalCrossingsInvariance DivisorExponentAlong
  HironakaActualOpenZeroSectionDifferentials HironakaActualCentreJointJets
  HironakaRelativeNormalIdeal HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalLocalClass
  HironakaG8HomStable

private abbrev U : Opens (ComplexModel 1) := ⊤
private def o : U := ⟨0, mem_univ _⟩
private abbrev X := CMfd.of (n := 2) (productOpen U)
private def Q : MarkedIdeal 1 U := ⟨univ, [{o}], vanishingIdeal {o}, 1⟩

private theorem coordSubspace_one :
    coordSubspace ({(0 : Fin 1)} : Finset (Fin 1)) = complexCoordinatePlane 1 0 := by
  ext v
  constructor
  · intro hv i _
    have hi : i = 0 := Subsingleton.elim _ _
    exact hv i (hi ▸ Finset.mem_singleton_self _)
  · intro hv i _
    exact hv i (Nat.zero_le _)

private theorem singleton_preimage :
    (Subtype.val : U → ComplexModel 1) ⁻¹' ({0} : Set (ComplexModel 1)) = {o} := by
  ext x
  exact ⟨fun hx => Subtype.ext hx, fun hx => congrArg Subtype.val hx⟩

private theorem snc_singleton : IsSNCDivisor 1 ([{o}] : List (Set U)) := by
  refine ⟨fun D hD => ?_, fun x => ?_⟩
  · simp only [List.mem_singleton] at hD
    exact hD ▸ isClosed_singleton
  · refine ⟨fun _ => {0}, ?_, fun _ _ => Finset.card_singleton _, ?_⟩
    · by_cases hx : x = o
      · subst x
        have hReg : RegularAtDim (n := 1) ({o} : Set U) o 0 := by
          rw [← singleton_preimage]
          exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
            (BlowupExistenceOriginIdeal.regularAtDim_zero (d := 1))
        obtain ⟨_, _, Φ, hΦ, hzero, hmem⟩ := hReg
        refine ⟨Φ, hΦ, hzero, ?_⟩
        intro i _ y hy hΦy
        rw [coordSubspace_one]
        have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
        simpa [List.get_eq_getElem, hi] using hmem hy hΦy
      · obtain ⟨Φ,hΦ,hzero⟩ := exists_centred_coordinates (n := 1) x
        exact ⟨Φ,hΦ,hzero,fun i hi => (hx (by simpa using hi)).elim⟩
    · intro i _ j _ _
      exact Fin.eq_zero i |>.trans (Fin.eq_zero j).symm

private theorem Q_domain : IsInvDomain 1 Q := by
  refine HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor
    (VanishingIdealCoherent.isCoherent_vanishingIdeal
      (PointSupportedIdealPrincipalization.singleton_geometry_and_coherence (n := 1) o).1) ?_ snc_singleton
  intro x
  have hThin : interior ({o} : Set U) = ∅ := by
    have hf : IsOpenMap (Subtype.val : U → ComplexModel 1) := U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
    rw [← singleton_preimage, ← hf.preimage_interior_eq_interior_preimage continuous_subtype_val,
      interior_singleton, preimage_empty]
  exact HironakaEmbeddedReducible.isNonzeroAlongAt_vanishingIdeal_of_interior_eq_empty
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (PointSupportedIdealPrincipalization.singleton_geometry_and_coherence (n := 1) o).1) hThin x

private def fibre (v : ComplexModel 1) : productOpen U :=
  ⟨actualJointNormalInclusion 1 1 v, mem_univ _⟩

private theorem fibre_continuous : Continuous fibre :=
  (actualJointNormalInclusion 1 1).continuous.subtype_mk _

private theorem fibre_zero : fibre 0 = zeroSection U o := by
  apply Subtype.ext
  change actualJointNormalInclusion 1 1 0 = tangentInclusion 1 1 0
  simp

private theorem projection_fibre (v : ComplexModel 1) : projection U (fibre v) = o := by
  apply Subtype.ext
  exact tangentProjection_actualJointNormalInclusion 1 1 v

/-- Even at the empty tower a positive padded nonspecial point can be section-special. -/
theorem exists_positive_padded_nonspecial_section_special :
    ∃ (Q : MarkedIdeal 1 U) (p : X),
      IsInvDomain 1 Q ∧
      IsGeoTestTower (properNormalMarked Q) (BlowupTower.refl (X := X)) ∧
      p ∈ (properNormalMarked Q).cosupp ∧
      level (properNormalMarked Q) (BlowupTower.refl (X := X)) p = 1 ∧
      ¬ IsSpecial (properNormalMarked Q) (BlowupTower.refl (X := X)) p ∧
      IsSpecial (sectionMarked Q) (BlowupTower.refl (X := X)) p := by
  classical
  let p := zeroSection U o
  let P := properNormalMarked Q
  let S := sectionMarked Q
  let T : BlowupTower X X := .refl
  let D : Set X := projection U ⁻¹' {o}
  have hQ : IsInvDomain 1 Q := Q_domain
  have hP := properNormalMarked_isInvDomain Q hQ
  have hS := HironakaActualSectionBoundaryGeometry.section_projected_domain 1 Q.N Q.E Q.ideal Q.d hQ
  have hQCos : Q.cosupp = {o} := by
    change GermIdealOrder.cosupport 1 univ (vanishingIdeal {o}) 1 = {o}
    rw [GermIdealOrder.cosupport_one SmoothCentreLocus.holomorphicAt_of_mem_vanishingIdeal,
      univ_inter, BlowupExceptionalDivisor.zeroLocus_vanishingIdeal isClosed_singleton]
  have hPCos : P.cosupp = {p} := by
    rw [properNormalMarked_cosupp Q hQ, hQCos, image_singleton]
  have hBarP : (barMarked (X := X) P).cosupp = {p} :=
    (((bar_local_any_boundary (X := X) P hP).wEquiv.2 T).2 trivial).symm.trans hPCos
  have hBarS : (barMarked (X := X) S).cosupp = {p} :=
    ((((properNormalMarked_locWPEquiv_section Q hQ).trans
      (bar_local_any_boundary (X := X) S hS)).wEquiv.2 T).2 trivial).symm.trans hPCos
  have hPD : origMembers P T = [D] := rfl
  have hSD : origMembers S T = [D] := rfl
  have hpD : p ∈ D := by
    change zeroSection U o ∈ D
    rw [← fibre_zero]
    exact mem_singleton_iff.mpr (projection_fibre 0)
  have hLevelP : level P T p = 1 := by
    simp [level, hPD, boundaryCount, hpD]
  have hLevelS : level S T p = 1 := by
    simp [level, hSD, boundaryCount, hpD]
  refine ⟨Q, p, hQ, trivial, hPCos.symm ▸ mem_singleton _, hLevelP, ?_, ?_⟩
  · rintro (⟨h0, _⟩ | ⟨_, hp⟩)
    · exact Nat.one_ne_zero (hLevelP.symm.trans h0)
    · rw [hPD, geoTransformAlong_refl, hBarP, mem_memberInterLocus_iff] at hp
      have h0 : fibre 0 = p := fibre_zero
      have hF : Tendsto fibre (𝓝 0) (𝓝 p) := h0 ▸ fibre_continuous.continuousAt
      have hNear := hF.eventually hp.2
      have hEq : ∀ᶠ v : ComplexModel 1 in 𝓝 0, v = 0 := hNear.mono fun v hv => by
        have h : fibre v ∈ ({p} : Set X) :=
          hv (mem_univ _) (fun H hH _ => by simp [List.mem_singleton.mp hH, D, projection_fibre])
        have hProj := congrArg (fun z : productOpen U => actualJointNormalProjection 1 1 z.val)
          (mem_singleton_iff.mp h)
        change actualJointNormalProjection 1 1 (actualJointNormalInclusion 1 1 v) =
          actualJointNormalProjection 1 1 (tangentInclusion 1 1 o.val) at hProj
        simpa only [actualJointNormalProjection_inclusion, actualJointNormalProjection_tangent] using hProj
      have hNE : ∀ᶠ v : ComplexModel 1 in 𝓝[≠] 0, v ∈ ({0} : Set (ComplexModel 1))ᶜ :=
        self_mem_nhdsWithin
      obtain ⟨_, hne, heq⟩ := (hNE.and (hEq.filter_mono nhdsWithin_le_nhds)).exists
      exact hne (mem_singleton_iff.mpr heq)
  · refine Or.inr ⟨hLevelS.ge, ?_⟩
    rw [hSD, geoTransformAlong_refl, hBarS, mem_memberInterLocus_iff]
    refine ⟨mem_singleton _, Eventually.of_forall fun y hy hD => ?_⟩
    have hyD : projection U y = o := hD D (by simp) hpD
    have hyNorm : actualJointNormalProjection 1 1 y.val = 0 := hy.2
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    have hTan : tangentProjection 1 1 y.val = 0 := congrArg Subtype.val hyD
    ext i
    fin_cases i
    · change y.val ((0 : Fin 1).castAdd 1) = _
      rw [show p.val = 0 by simp [p, zeroSection, o]]
      exact congrArg (fun v : ComplexModel 1 => v (0 : Fin 1)) hTan
    · change y.val ((0 : Fin 1).natAdd 1) = _
      rw [show p.val = 0 by simp [p, zeroSection, o]]
      exact congrArg (fun v : ComplexModel 1 => v (0 : Fin 1)) hyNorm

open HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionInitialBar
  HironakaSmoothSubmersionCanonicalValueDimensionShift CanonicalCentres
  HironakaG1PositiveNormalChronology

private theorem stepDimensionMap_finite {α β : Type} (f : α → β)
    (v : ℕ ×ₗ WithTop α) (hv : (ofLex v).2 ≠ ⊤) :
    (ofLex (stepDimensionMap f v)).2 ≠ ⊤ := by
  change WithTop.map f (ofLex v).2 ≠ ⊤
  cases h : (ofLex v).2 with
  | top => exact (hv h).elim
  | coe a => exact WithTop.coe_ne_top

/-- In the common initial history the padded and native Step One lower
values are finite and top, respectively, at the same positive level. Any
comparison that preserves finiteness of the lower coordinate fails there. -/
theorem exists_positive_normal_stepOne_value_discrepancy :
    ∃ (Q : MarkedIdeal 1 U) (p : X), IsInvDomain 1 Q ∧
      p ∈ (properNormalMarked Q).cosupp ∧
      let B := nativePullback (Y := X) (Nat.le_succ 1) (zeroPlane U) (zeroPlane_regular U) (sectionMarked Q)
      ∃ (V : Set X) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := 2) V z 1)
        (N : BlowupTower (nativeManifold (Y := X) (Nat.le_succ 1) (zeroPlane U) (zeroPlane_regular U))
          (nativeManifold (Nat.le_succ 1) V hV))
        (z : nativeManifold (Nat.le_succ 1) V hV) (hZero : IsClosed (zeroPlane U)),
        Lift (Nat.le_succ 1) (zeroPlane U) hZero (zeroPlane_regular U)
          (sectionMarked Q).E (BlowupTower.refl (X := X)) V hVc hV N ∧ z.val = p ∧
        let v := Seq.StepOneValueMasked.stepOneInvM (invFamily (show 0 < 2 by decide) 1)
          (properNormalMarked Q) (BlowupTower.refl (X := X)) p
        let w := Seq.StepOneValueMasked.stepOneInvM (invFamily Nat.one_pos 0) B N z
        (ofLex v).1 = 1 ∧ (ofLex v).2 ≠ ⊤ ∧ w = toLex (1, (⊤ : WithTop (ValTy 0))) ∧
        (∀ c : (ℕ ×ₗ WithTop (ValTy 1)) → (ℕ ×ₗ WithTop (ValTy 0)),
          (∀ a, (ofLex a).2 ≠ ⊤ → (ofLex (c a)).2 ≠ ⊤) → c v ≠ w) ∧
        (∀ f : ValTy 1 → ValTy 0, stepDimensionMap f v ≠ w) ∧
        (∀ g : ValTy 0 → ValTy 1, stepDimensionMap g w ≠ v) := by
  obtain ⟨Q, p, hQ, hT, hp, hLevel, hNS, hS⟩ :=
    exists_positive_padded_nonspecial_section_special
  let T : BlowupTower X X := .refl
  have hpT : p ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp := hp
  obtain ⟨V, hVc, hV, N, z, hZero, hLift, hz, _, hFirst, hFinite, hTop⟩ :=
    positive_normal_native_special_values (s := 0) Nat.one_pos Q hQ T hT p hpT hLevel hNS hS
  refine ⟨Q, p, hQ, hp, V, hVc, hV, N, z, hZero, hLift, hz, hFirst, hFinite, hTop, ?_⟩
  let v := Seq.StepOneValueMasked.stepOneInvM (invFamily (show 0 < 2 by decide) 1) (properNormalMarked Q) T p
  let B := nativePullback (Y := X) (Nat.le_succ 1) (zeroPlane U) (zeroPlane_regular U) (sectionMarked Q)
  let w := Seq.StepOneValueMasked.stepOneInvM (invFamily Nat.one_pos 0) B N z
  have hObstruction (c : (ℕ ×ₗ WithTop (ValTy 1)) → (ℕ ×ₗ WithTop (ValTy 0)))
      (hc : ∀ a, (ofLex a).2 ≠ ⊤ → (ofLex (c a)).2 ≠ ⊤) : c v ≠ w := by
    intro hEq
    have hw : w = toLex (1, (⊤ : WithTop (ValTy 0))) := hTop
    exact hc v hFinite (congrArg (fun a : ℕ ×ₗ WithTop (ValTy 0) => (ofLex a).2) (hEq.trans hw))
  refine ⟨hObstruction, fun f => hObstruction _ (stepDimensionMap_finite f), ?_⟩
  intro g hEq
  have hw : w = toLex (1, (⊤ : WithTop (ValTy 0))) := hTop
  change stepDimensionMap g w = v at hEq
  rw [hw] at hEq
  exact hFinite (congrArg (fun a : ℕ ×ₗ WithTop (ValTy 1) => (ofLex a).2) hEq.symm)

/-- An actual empty-centre step already realizes strict shortening of
the positive section clock. -/
theorem exists_strict_positive_normal_section_run :
    ∃ (Q : MarkedIdeal 1 U) (p : X) (T : BlowupTower X X),
      IsInvDomain 1 Q ∧ IsGeoTestTower (properNormalMarked Q) T ∧ T.length = 1 ∧
      regimeRun (stepRegime (properNormalMarked Q) 1) T p = 1 ∧
      regimeRun (stepRegime (sectionMarked Q) 1) T p = 0 := by
  obtain ⟨Q, p, hQ, hTest, _, hLevel, hNS, hSpecial⟩ :=
    exists_positive_padded_nonspecial_section_special
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let T₀ : BlowupTower X X := .refl
  have hπ : IsBlowupAlong 2 (∅ : Set X) (id : X → X) :=
    BlowupExistenceCodimOne.isBlowupAlong_id_empty
  let T : BlowupTower X X := .step T₀ ∅ id hπ
  have hP : stepRegime P 1 T₀ (id p) := ⟨hLevel, hNS⟩
  have hSec : ¬ stepRegime Sec 1 T₀ (id p) := fun h => h.2 hSpecial
  refine ⟨Q, p, T, hQ, ⟨hTest, P.isAdmissibleCentre_empty⟩, rfl, ?_, ?_⟩
  · exact regimeRun_step_of (stepRegime P 1) T₀ ∅ id hπ (z := p) hP
  · exact regimeRun_step_of_not (stepRegime Sec 1) T₀ ∅ id hπ (z := p) hSec

end

end Hironaka.HironakaG1PositiveNormalSpecialExample
