/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticCentreVertexFamily
import Hironaka.Resolution.HironakaActualFormalFamilyStrictGenerators

/-! Actual analytic exceptional quotients and whole original normalized-member ideals. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAnalyticStrictGenerators
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan
  HironakaActualOriginalFormalTaylor HironakaActualFormalIdealContraction
  HironakaActualFormalInitialDiagram HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticBlowupTaylor HironakaActualFormalCoordinatePowerDivision
  HironakaActualReducedFormalStandardBasis HironakaActualReducedBasisDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalStrictGenerators
  HironakaActualAnalyticCentreVertexFamily HironakaActualFormalFamilyStrictGenerators

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem unshifted_extension_injective (n : ℕ) :
    Function.Injective (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    Function.Injective (Ideal.map f.toRingHom)
  exact unshiftedTaylor_property n P (original_formal_ideal_extension_injective n)

/-- Genuine analytic quotients are internally constructed from centre-compatible analytic generators. -/
theorem exists_actual_analytic_strict_vertex_generators (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I),
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a ∈
          actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val) :
    ∃ G H : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel n),
      (∀ a,G a ∈ I ∧ G a ∈ actualAnalyticCoordinateIdeal A ^
          Finsupp.weight (actualCoordinateWeight A) a.val ∧
        ∃ hne : actualUnshiftedTaylorAlgHom n (G a) ≠ 0,
          actualInitialExponent MonomialOrder.degLex (actualUnshiftedTaylorAlgHom n (G a)) hne=a.val ∧
          MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (G a))=1) ∧
      Ideal.span (range G)=I ∧
      (∀ a,(coordinateGerm e)^Finsupp.weight (actualCoordinateWeight A) a.val*H a=
        actualAnalyticBlowupPullback A e b (G a)) ∧
      actualFormalStrictTransform (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) A e he b=
        Ideal.span (range (fun a => actualUnshiftedTaylorAlgHom n (H a))) := by
  obtain ⟨G,hG,hspan⟩ := exists_actual_analytic_centre_vertex_family n I A hV
  let J := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  have hl (a : actualInitialVertices MonomialOrder.degLex J) (β : Fin n →₀ ℕ)
      (hβ : MonomialOrder.degLex.toSyn β<MonomialOrder.degLex.toSyn a.val) :
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (G a))=0 := by
    obtain ⟨hne,hinit,_⟩ := (hG a).2.2
    apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _ hne
    rwa [hinit]
  let B : ActualMonicVertexFamily MonomialOrder.degLex J :=
    { series := fun a => actualUnshiftedTaylorAlgHom n (G a)
      mem := fun a => Ideal.mem_map_of_mem _ (hG a).1
      monic := fun a => ((hG a).2.2.choose_spec).2
      lower := hl }
  have hB (a : actualInitialVertices MonomialOrder.degLex J) :
      familyVertexSeries MonomialOrder.degLex J B a ∈ actualFormalCoordinateIdeal n A ^
        Finsupp.weight (actualCoordinateWeight A) a.val :=
    actualTaylor_mem_coordinateCentre_pow A _ (G a) (hG a).2.1
  have hq (a : actualInitialVertices MonomialOrder.degLex J) :=
    exists_actualAnalyticBlowup_quotient A e he b _ (G a) (hG a).2.1
  choose H hH using hq
  refine ⟨G,H,hG,hspan,fun a => (hH a).1,?_⟩
  have hf : familyNormalizedFormalVertex MonomialOrder.degLex J B A e he b hB=
      fun a => actualUnshiftedTaylorAlgHom n (H a) := by
    funext a
    exact (hH a).2.symm
  rw [← hf]
  exact actualFormalStrictTransform_eq_family_span MonomialOrder.degLex J B A e he b hB

/-- Entire analytic span of all actual original centre-power members with genuine exceptional quotients. -/
def actualAnalyticNormalizedMemberIdeal {n : ℕ} (I : Ideal (HolGerm (ComplexModel n)))
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) : Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span {H | ∃ (d : ℕ) (g : HolGerm (ComplexModel n)),
    g ∈ I ∧ g ∈ actualAnalyticCoordinateIdeal A ^ d ∧
      (coordinateGerm e)^d*H=actualAnalyticBlowupPullback A e b g}

/-- Whole Taylor naturality sends every genuine analytic normalized member into the actual formal strict ideal. -/
theorem map_actualAnalyticNormalizedMemberIdeal_le_formalStrictTransform {n : ℕ}
    (I : Ideal (HolGerm (ComplexModel n))) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (actualAnalyticNormalizedMemberIdeal I A e b) ≤
      actualFormalStrictTransform (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) A e he b := by
  rw [actualAnalyticNormalizedMemberIdeal,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro F ⟨H,⟨d,g,hI,hC,hH⟩,rfl⟩
  have hC' := actualTaylor_mem_coordinateCentre_pow A d g hC
  have hnorm : actualUnshiftedTaylorAlgHom n H=actualNormalizedFormalMember A e he b d
      (actualUnshiftedTaylorAlgHom n g) hC' := by
    apply actualNormalizedFormalMember_unique
    have ht := congrArg (actualUnshiftedTaylorAlgHom n) hH
    rw [map_mul,map_pow,actualUnshiftedTaylor_coordinate] at ht
    exact ht.trans (DFunLike.congr_fun (actualTaylor_analyticBlowupPullback A e b) g)
  change actualUnshiftedTaylorAlgHom n H ∈
    actualFormalStrictTransform (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) A e he b
  rw [hnorm,actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  exact Ideal.subset_span ⟨d,actualUnshiftedTaylorAlgHom n g,Ideal.mem_map_of_mem _ hI,hC',rfl⟩

/-- Both entire analytic and formal ideals are generated by internally produced actual analytic quotients. -/
theorem exists_actual_analytic_normalized_member_generators (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I),
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a ∈
          actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val) :
    ∃ H : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel n),
      actualAnalyticNormalizedMemberIdeal I A e b=Ideal.span (range H) ∧
      Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (actualAnalyticNormalizedMemberIdeal I A e b)=
        actualFormalStrictTransform (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) A e he b := by
  obtain ⟨G,H,hG,_,hH,hformal⟩ := exists_actual_analytic_strict_vertex_generators n I A e he b hV
  have hspan : Ideal.span (range H) ≤ actualAnalyticNormalizedMemberIdeal I A e b := by
    apply Ideal.span_le.mpr
    rintro f ⟨a,rfl⟩
    exact Ideal.subset_span ⟨_,G a,(hG a).1,(hG a).2.1,hH a⟩
  have hm : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range H))=
      actualFormalStrictTransform (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) A e he b := by
    rw [Ideal.map_span,← Set.range_comp]
    exact hformal.symm
  have hmap : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (actualAnalyticNormalizedMemberIdeal I A e b)=
      actualFormalStrictTransform (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) A e he b := by
    apply le_antisymm (map_actualAnalyticNormalizedMemberIdeal_le_formalStrictTransform I A e he b)
    rw [← hm]
    exact Ideal.map_mono hspan
  exact ⟨H,(unshifted_extension_injective n (hm.trans hmap.symm)).symm,hmap⟩

end
end Hironaka.HironakaActualAnalyticStrictGenerators
