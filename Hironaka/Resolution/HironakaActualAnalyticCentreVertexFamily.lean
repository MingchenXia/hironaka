/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticVertexBasis
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor
import Hironaka.Resolution.HironakaActualReducedBasisDivision

/-! Genuine analytic monic vertices retaining literal whole coordinate-centre powers. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAnalyticCentreVertexFamily
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction HironakaActualFormalIdealIntersections
  HironakaActualFormalInitialDiagram HironakaActualFormalStandardMonomialHS
  HironakaActualAnalyticVertexBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticBlowupTaylor HironakaActualFormalCoordinatePowerDivision
  HironakaActualReducedFormalStandardBasis HironakaActualReducedBasisDivision

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

private theorem unshifted_ideal_jet_lift (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) (q : ℕ) :
    ∃ g ∈ I, ∀ α : Fin n →₀ ℕ, normalExponentDegree α<q →
      MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n g)=MvPowerSeries.coeff α F := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (J : Ideal (HolGerm (ComplexModel m))) (H : MvPowerSeries (Fin n) ℂ),
      H ∈ Ideal.map f.toRingHom J → ∀ q : ℕ, ∃ g ∈ J,
        ∀ α : Fin n →₀ ℕ,normalExponentDegree α<q → MvPowerSeries.coeff α (f g)=MvPowerSeries.coeff α H
  have h : P (0+n) (originalTaylorAlgHom n) := exists_original_ideal_member_jet_lift n
  exact unshiftedTaylor_property n P h I F hF q

private theorem unshifted_map_inf (n : ℕ) (I J : Ideal (HolGerm (ComplexModel n))) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (I⊓J)=
      Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I ⊓
        Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom J := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ K L : Ideal (HolGerm (ComplexModel m)),
      Ideal.map f.toRingHom (K⊓L)=Ideal.map f.toRingHom K⊓Ideal.map f.toRingHom L
  have h : P (0+n) (originalTaylorAlgHom n) := map_inf_originalTaylorAlgHom n
  exact unshiftedTaylor_property n P h I J

private theorem unshifted_extension_injective (n : ℕ) :
    Function.Injective (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    Function.Injective (Ideal.map f.toRingHom)
  exact unshiftedTaylor_property n P (original_formal_ideal_extension_injective n)

/-- Literal formal centre compatibility constructs true analytic monic vertices in the WHOLE original intersection ideals. -/
theorem exists_actual_analytic_centre_vertex_family (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (A : Set (Fin n))
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I),
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a ∈
          actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val) :
    ∃ G : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel n),
      (∀ a,G a ∈ I ∧ G a ∈ actualAnalyticCoordinateIdeal A ^
          Finsupp.weight (actualCoordinateWeight A) a.val ∧
        ∃ hne : actualUnshiftedTaylorAlgHom n (G a) ≠ 0,
          actualInitialExponent MonomialOrder.degLex (actualUnshiftedTaylorAlgHom n (G a)) hne=a.val ∧
          MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (G a))=1) ∧
      Ideal.span (range G)=I := by
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  have hv (a : actualInitialVertices MonomialOrder.degLex K) :
      ∃ g ∈ I⊓actualAnalyticCoordinateIdeal A ^ Finsupp.weight (actualCoordinateWeight A) a.val,
        ∀ α : Fin n →₀ ℕ,normalExponentDegree α<normalExponentDegree a.val+1 →
          MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n g)=
            MvPowerSeries.coeff α (actualReducedVertexSeries MonomialOrder.degLex K a) := by
    apply unshifted_ideal_jet_lift n _ _ _ (normalExponentDegree a.val+1)
    rw [unshifted_map_inf,Ideal.map_pow,map_actualAnalyticCoordinateIdeal_taylor]
    exact ⟨actualReducedVertexSeries_mem MonomialOrder.degLex K a,hV a⟩
  choose G hG hjet using hv
  have hc (a : actualInitialVertices MonomialOrder.degLex K) :
      MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (G a))=1 :=
    (hjet a a.val (by omega)).trans (actualReducedVertexSeries_coefficient MonomialOrder.degLex K a)
  have hl (a : actualInitialVertices MonomialOrder.degLex K) (β : Fin n →₀ ℕ)
      (hβ : MonomialOrder.degLex.toSyn β<MonomialOrder.degLex.toSyn a.val) :
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (G a))=0 := by
    have hd := actual_degree_le_of_deglex_lt β a.val hβ
    rw [hjet a β (by omega)]
    exact actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex K a β hβ
  let B : ActualMonicVertexFamily MonomialOrder.degLex K :=
    { series := fun a => actualUnshiftedTaylorAlgHom n (G a)
      mem := fun a => Ideal.mem_map_of_mem _ (hG a).1
      monic := hc
      lower := hl }
  refine ⟨G,?_,?_⟩
  · intro a
    have hne : actualUnshiftedTaylorAlgHom n (G a) ≠ 0 := by
      intro hz
      have h := hc a
      rw [hz,map_zero] at h
      exact zero_ne_one h
    refine ⟨(hG a).1,(hG a).2,hne,?_,hc a⟩
    exact actualInitialExponent_eq_of_coefficients MonomialOrder.degLex _ hne a.val
      (by rw [hc a];exact one_ne_zero) (hl a)
  · apply unshifted_extension_injective n
    rw [Ideal.map_span,← Set.range_comp]
    change Ideal.span (range (familyVertexSeries MonomialOrder.degLex K B))=K
    exact (family_formal_ideal_eq_span_vertex_series MonomialOrder.degLex K B).symm

end
end Hironaka.HironakaActualAnalyticCentreVertexFamily
