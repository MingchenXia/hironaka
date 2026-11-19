import Hironaka.Resolution.HironakaG8OddCuspHistoricalNative
import Hironaka.Resolution.HironakaActualAnalyticCanonicalVertices
import Hironaka.Resolution.HironakaActualSameCurrentGeometricStage

/-! The actual canonical cusp family in the displayed identity coordinates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Polynomial
open scoped Topology MonomialOrder Manifold ContDiff
namespace Hironaka.HironakaG8OddCuspPrescribedFamily
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HolGerm OkaRelationSheaf OkaIdealOperations HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualFormalInitialDiagram HironakaActualNormalZeroAnalyticSaturation
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticFormalNormalPowers
  HironakaActualAnalyticCanonicalVertices HironakaActualRelativeNormalJetDivision
  HironakaActualReducedFormalStandardBasis HironakaActualInheritedNestedContactFlag
  HironakaActualFixedInheritedSelector HironakaActualAnalyticBlockGraphTranslation
  HironakaActualCanonicalBlockJacobian HironakaActualInheritedAnalyticBlockJacobian
  HironakaActualSameCurrentGeometricStage HironakaActualGeometricCurrentNeighborhoodHS
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
  HironakaG8NativeCuspDiagram HironakaG8OddCuspVanishingStalk
  HironakaG8OddCuspGeometricSource HironakaG8SameHSCuspContact
  HironakaRelativeNormalDeformationInitialRelations HironakaSmoothCentreRealDomainSaturation HironakaSmoothCentreRealDomainDeformation

abbrev cuspJ (p : ℕ) := analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p)
abbrev cuspV (p : ℕ) := actualInitialVertices MonomialOrder.degLex (cuspJ p)
abbrev yExp : Fin 3 →₀ ℕ := Finsupp.single 1 2
abbrev zExp : Fin 3 →₀ ℕ := Finsupp.single 2 1

theorem cuspV_eq (p : ℕ) (hp : 2 < p) : cuspV p = {yExp,zExp} := by
  have hLift : actualJoinedExponent cuspVertex (0 : Fin 1 →₀ ℕ) = yExp := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [show actualJoinedExponent cuspVertex (0 : Fin 1 →₀ ℕ) (i.castAdd 1) = cuspVertex i by
        simp [actualJoinedExponent]]
      fin_cases i <;> simp
    · rw [show actualJoinedExponent cuspVertex (0 : Fin 1 →₀ ℕ) (i.natAdd 2) = 0 by
        simp [actualJoinedExponent]]
      fin_cases i; simp
  change actualInitialVertices MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom 3).toRingHom (embeddedCuspIdeal p)) = _
  rw [embedded_cusp_vertices p hp,hLift]

theorem cuspV_cases {p : ℕ} (hp : 2 < p) (a : cuspV p) : a.val = yExp ∨ a.val = zExp := by
  have h : a.val ∈ ({yExp,zExp} : Finset _) := cuspV_eq p hp ▸ a.property
  simpa using h

private theorem cuspFormal {p : ℕ} (hp : 2 < p) (a : cuspV p) :
    actualReducedVertexSeries MonomialOrder.degLex (cuspJ p) a =
    if a.val = yExp then (MvPowerSeries.X (1 : Fin 3))^2 - (MvPowerSeries.X (0 : Fin 3))^p
    else MvPowerSeries.X (2 : Fin 3) := by
  have hn : zExp ≠ yExp := by
    intro h
    have hh := congrArg (fun a : Fin 3 →₀ ℕ => a 1) h
    simp at hh
  rcases embedded_cusp_reduced_series p hp a with ⟨ha,h⟩ | ⟨ha,h⟩
  · rw [if_pos ha,h,cuspSeries,map_sub,map_pow,map_pow,MvPowerSeries.rename_X,MvPowerSeries.rename_X]
    rfl
  · rw [if_neg (ha.trans_ne hn),h]

theorem exists_cusp_canonical_inherited_family (p : ℕ) :
    ∃ G : ActualAnalyticInheritedFamily 3 0 (cuspJ p),
      Ideal.span (range G.germs) = embeddedCuspIdeal p ∧
      (∀ a, actualUnshiftedTaylorAlgHom 3 (G.germs a) =
        actualReducedVertexSeries MonomialOrder.degLex (cuspJ p) a) ∧
      (∀ k,ActualInheritedPrefixReducedAt G k) := by
  obtain ⟨F,hF,hSpan⟩ := exists_actualAnalyticCanonicalVertexFamily 3 (embeddedCuspIdeal p)
  let G : ActualAnalyticInheritedFamily 3 0 (cuspJ p) :=
    ⟨F,fun a => (hF a).2.2.choose_spec.2,fun a b hb => by
      rw [(hF a).2.1]
      exact actualReducedVertexSeries_coefficient_lower _ _ a b hb⟩
  exact ⟨G,hSpan,fun a => (hF a).2.1,
    fun k => actualInheritedPrefixReducedAt_of_canonical G (fun a => (hF a).2.1) k⟩

/-- The displayed graphs already satisfy every inherited contact block. -/
theorem cusp_canonical_inherited_contact (p : ℕ) (hp : 2 < p)
    (G : ActualAnalyticInheritedFamily 3 0 (cuspJ p))
    (hG : ∀ a, actualUnshiftedTaylorAlgHom 3 (G.germs a) =
      actualReducedVertexSeries MonomialOrder.degLex (cuspJ p) a)
    (k : ℕ) :
    actualFixedSelectorContactAt (actualInitialFixedInheritedSelector (cuspJ p)) G.germs k := by
  let S := actualInitialFixedInheritedSelector (cuspJ p)
  intro j
  let j' := fixedSelectorBlockEssential k j
  let a := S.selected j'
  have hPos : a.val j.val ≠ 0 := S.positive j'
  rcases cuspV_cases hp a with ha | ha
  · have hj : j.val = 1 := by
      by_contra h
      apply hPos
      simp [ha, Finsupp.single_eq_of_ne h]
    have hb : fixedSelectorBeta S j' = Finsupp.single (1 : Fin 3) 1 := by
      change a.val - Finsupp.single j.val 1 = _
      rw [ha,hj]
      ext i
      fin_cases i <;> simp
    have hDer : actualFixedSelectorDerivative S G.germs j' =
        2 * coordinateGerm (1 : Fin 3) := by
      apply actualUnshiftedTaylorAlgHom_injective 3
      rw [actualFixedSelectorDerivative, actualTaylor_actualAnalyticMultiDerivative, hb]
      change actualFormalMultiDerivative _ (actualUnshiftedTaylorAlgHom 3 (G.germs a)) = _
      rw [hG,cuspFormal hp,if_pos ha]
      rw [← zero_add (Finsupp.single (1 : Fin 3) 1), actualFormalMultiDerivative_add_single,
        actualFormalMultiDerivative_zero, map_mul,map_ofNat, actualUnshiftedTaylor_coordinate]
      simp
    rw [hDer]
    apply Ideal.mul_mem_left
    exact Ideal.subset_span ⟨1,hj ▸ j.property,rfl⟩
  · have hj : j.val = 2 := by
      by_contra h
      apply hPos
      simp [ha, Finsupp.single_eq_of_ne h]
    have hb : fixedSelectorBeta S j' = 0 := by
      change a.val - Finsupp.single j.val 1 = _
      rw [ha,hj,tsub_self]
    have hn : a.val ≠ yExp := by
      rw [ha]
      intro h
      have hh := congrArg (fun a : Fin 3 →₀ ℕ => a 1) h
      simp at hh
    have hDer : actualFixedSelectorDerivative S G.germs j' = coordinateGerm (2 : Fin 3) := by
      apply actualUnshiftedTaylorAlgHom_injective 3
      rw [actualFixedSelectorDerivative, actualTaylor_actualAnalyticMultiDerivative, hb,
        actualFormalMultiDerivative_zero]
      change actualUnshiftedTaylorAlgHom 3 (G.germs a) = _
      rw [hG,cuspFormal hp,if_neg hn,actualUnshiftedTaylor_coordinate]
    rw [hDer]
    exact Ideal.subset_span ⟨2,hj ▸ j.property,rfl⟩


def cuspRepresentative (p : ℕ) (a : cuspV p) : ComplexModel 3 → ℂ :=
  if a.val = yExp then embeddedCuspEquations p 0 else embeddedCuspEquations p 1

theorem cuspRepresentative_differentiable (p : ℕ) (a : cuspV p) :
    Differentiable ℂ (cuspRepresentative p a) := by
  unfold cuspRepresentative
  split
  · change Differentiable ℂ (fun z : ComplexModel 3 => z.ofLp 1 ^ 2 - z.ofLp 0 ^ p)
    exact ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).differentiable.pow 2).sub
      ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiable.pow p)
  · change Differentiable ℂ (fun z : ComplexModel 3 => z.ofLp 2)
    exact (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable

theorem cuspRepresentative_holAt (p : ℕ) (a : cuspV p) :
    HolAt (cuspRepresentative p a) 0 := Eventually.of_forall (cuspRepresentative_differentiable p a)

private theorem cuspRepresentative_germ_eq (p : ℕ) (hp : 2 < p)
    (G : ActualAnalyticInheritedFamily 3 0 (cuspJ p))
    (hG : ∀ a, actualUnshiftedTaylorAlgHom 3 (G.germs a) =
      actualReducedVertexSeries MonomialOrder.degLex (cuspJ p) a)
    (a : cuspV p) :
    HolGerm.mk (cuspRepresentative p a) (cuspRepresentative_holAt p a) = G.germs a := by
  apply actualUnshiftedTaylorAlgHom_injective 3
  rw [hG,cuspFormal hp]
  by_cases ha : a.val = yExp
  · rw [if_pos ha]
    have he : HolGerm.mk (cuspRepresentative p a) (cuspRepresentative_holAt p a) =
        (coordinateGerm (1 : Fin 3))^2 - (coordinateGerm (0 : Fin 3))^p := by
      unfold coordinateGerm
      rw [← mk_pow, ← mk_pow, ← mk_sub]
      exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun _ => by
        simp [cuspRepresentative, ha, embeddedCuspEquations])
    rw [he,map_sub,map_pow,map_pow,actualUnshiftedTaylor_coordinate,actualUnshiftedTaylor_coordinate]
  · rw [if_neg ha]
    have he : HolGerm.mk (cuspRepresentative p a) (cuspRepresentative_holAt p a) =
        coordinateGerm (2 : Fin 3) := by
      unfold coordinateGerm
      exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun _ => by
        simp [cuspRepresentative, ha, embeddedCuspEquations])
    rw [he,actualUnshiftedTaylor_coordinate]

/-- The supplied-representative provider retains the literal polynomial
functions in its whole geometric HS neighbourhood and the full contact flag. -/
theorem exists_cusp_prescribed_family_hs_window (p : ℕ) (hp : Odd p) (hp2 : 2 < p)
    (U : Opens (ComplexModel 3)) (hU : (0 : ComplexModel 3) ∈ U) :
    let A := vanishingIdeal (n := 3) (embeddedCuspSet p)
    let R := fun l => hilbertSamuelAt A 0 l
    ∃ (G : ActualAnalyticInheritedFamily 3 0 (cuspJ p))
      (PHS : ActualGeometricInheritedNeighborhoodHS A (embeddedCuspIdeal p) G R),
      Ideal.span (range G.germs) = embeddedCuspIdeal p ∧
      (∀ k,ActualInheritedPrefixReducedAt G k) ∧
      (∀ k,actualFixedSelectorContactAt (actualInitialFixedInheritedSelector (cuspJ p)) G.germs k) ∧
      PHS.representatives = cuspRepresentative p ∧ PHS.neighborhood ⊆ U := by
  intro A R
  obtain ⟨G,hSpan,hTaylor,hRed⟩ := exists_cusp_canonical_inherited_family p
  have hI : embeddedCuspIdeal p = originalCoherentOriginIdeal A :=
    (embedded_odd_cusp_vanishing_stalk p hp).symm
  have hC : A.IsCoherent := CartanIrreducible.cartanCoherence _ (embedded_cusp_isAnalytic p)
  have hFg : IdealFGAt A.mem (0 : ComplexModel 3) :=
    idealFGAt_of_coherentOn A univ (coherentOn_of_isCoherent A hC univ isOpen_univ) (mem_univ _)
  obtain ⟨P,hRep,hSub⟩ := exists_actual_same_representatives_neighborhood_hs A hFg
    (embeddedCuspIdeal p) G hSpan hRed hI R (fun _=>rfl)
    (cuspRepresentative p) (cuspRepresentative_holAt p)
    (cuspRepresentative_germ_eq p hp2 G hTaylor) (U : Set (ComplexModel 3)) U.isOpen hU
  exact ⟨G,P,hSpan,hRed,cusp_canonical_inherited_contact p hp2 G hTaylor,hRep,hSub⟩

end
end Hironaka.HironakaG8OddCuspPrescribedFamily
