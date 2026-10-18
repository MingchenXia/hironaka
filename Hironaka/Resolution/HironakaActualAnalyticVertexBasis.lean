/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalColonSaturation
import Hironaka.Support.ActualDegreeLexBoundExact

/-! Internally constructed genuine original analytic monic vertices generate the WHOLE original ideal. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAnalyticVertexBasis
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction HironakaActualFormalInitialDiagram
  HironakaActualFormalVertexDivision HironakaActualFormalStandardMonomialHS

/-- Every actual formal extended member has an internally constructed true original ideal jet representative. -/
theorem exists_original_ideal_member_jet_lift (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ Ideal.map (originalTaylorAlgHom n).toRingHom I) (q : ℕ) :
    ∃ g ∈ I, ∀ α : Fin n →₀ ℕ, normalExponentDegree α<q →
      MvPowerSeries.coeff α (originalTaylorAlgHom n g)=MvPowerSeries.coeff α F := by
  let := isNoetherianRing_holGerm_euclidean (0+n)
  obtain ⟨r,G,hG⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  have hspan : Ideal.span (range G)=I := hG
  have hmap : Ideal.map (originalTaylorAlgHom n).toRingHom I=
      Ideal.span (range fun i => originalTaylorAlgHom n (G i)) := by
    rw [← hspan,Ideal.map_span,← Set.range_comp]
    rfl
  rw [hmap] at hF
  obtain ⟨A,hA⟩ := Ideal.mem_span_range_iff_exists_fun.mp hF
  let g := ∑ i,actualFormalApproximation n q (A i)*G i
  have hg : g ∈ I := by
    apply Ideal.sum_mem
    intro i _
    apply Ideal.mul_mem_left
    rw [← hspan]
    exact Ideal.mem_span_range_self (x := i)
  refine ⟨g,hg,?_⟩
  intro α hα
  calc
    _=∑ i,MvPowerSeries.coeff α
        (originalTaylorAlgHom n (actualFormalApproximation n q (A i))*originalTaylorAlgHom n (G i)) := by
      simp only [g,map_sum,map_mul]
    _=∑ i,MvPowerSeries.coeff α (A i*originalTaylorAlgHom n (G i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact actualFormalApproximation_mul_coefficient n q (A i) _ α (by omega)
    _=MvPowerSeries.coeff α F := by rw [← hA,map_sum]

private theorem formal_ideal_eq_of_initial_diagram {n : ℕ} (m : MonomialOrder (Fin n))
    (J K : Ideal (MvPowerSeries (Fin n) ℂ)) (hJK : J≤K)
    (hD : actualInitialDiagram m J=actualInitialDiagram m K) : J=K := by
  apply le_antisymm hJK
  intro F hF
  have hs : (∑ a : actualInitialVertices m J,
      actualFormalQuotient m J F a*actualVertexSeries m J a) ∈ J :=
    J.sum_mem fun a _ => J.mul_mem_left _ (actualVertexSeries_spec m J a).1
  have he : actualFormalRemainder m J F=F-
      ∑ a : actualInitialVertices m J,actualFormalQuotient m J F a*actualVertexSeries m J a := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (actual_formal_vertex_division m J F).symm
  have hr : actualFormalRemainder m J F ∈ K := by
    rw [he]
    exact K.sub_mem hF (hJK hs)
  have hz : actualFormalRemainder m J F=0 := by
    by_contra hne
    let c := actualInitialExponent m (actualFormalRemainder m J F) hne
    have hc : c ∈ actualInitialDiagram m K := ⟨_,hr,hne,rfl⟩
    rw [← hD] at hc
    exact (actualInitialExponent_spec m (actualFormalRemainder m J F) hne).1
      (actualFormalRemainder_coefficient_diagram m J F c hc)
  have h := actual_formal_vertex_division m J F
  rw [hz,add_zero] at h
  rw [h]
  exact hs

/-- A true internally finite analytic monic vertex family generates the ENTIRE original ideal. -/
theorem exists_actual_original_analytic_vertex_basis (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) :
    ∃ G : actualInitialVertices MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom I) →
        HolGerm (ComplexModel (0+n)),
      (∀ a,G a ∈ I ∧ ∃ hne : originalTaylorAlgHom n (G a) ≠ 0,
        actualInitialExponent MonomialOrder.degLex (originalTaylorAlgHom n (G a)) hne=a.val ∧
        MvPowerSeries.coeff a.val (originalTaylorAlgHom n (G a))=1) ∧
      Ideal.span (range G)=I := by
  let K := Ideal.map (originalTaylorAlgHom n).toRingHom I
  have hv (a : actualInitialVertices MonomialOrder.degLex K) :
      ∃ g ∈ I, ∃ hne : originalTaylorAlgHom n g ≠ 0,
        actualInitialExponent MonomialOrder.degLex (originalTaylorAlgHom n g) hne=a.val ∧
        MvPowerSeries.coeff a.val (originalTaylorAlgHom n g)=1 := by
    obtain ⟨g,hg,hjet⟩ := exists_original_ideal_member_jet_lift n I
      (actualVertexSeries MonomialOrder.degLex K a) (actualVertexSeries_spec MonomialOrder.degLex K a).1
      (normalExponentDegree a.val+1)
    have hc : MvPowerSeries.coeff a.val (originalTaylorAlgHom n g)=1 :=
      (hjet a.val (by omega)).trans (actualVertexSeries_coefficient MonomialOrder.degLex K a)
    have hne : originalTaylorAlgHom n g ≠ 0 := by
      intro hz
      rw [hz,map_zero] at hc
      exact zero_ne_one hc
    refine ⟨g,hg,hne,?_,hc⟩
    apply actualInitialExponent_eq_of_coefficients
    · rw [hc]
      exact one_ne_zero
    · intro β hβ
      have hd := actual_degree_le_of_deglex_lt β a.val hβ
      rw [hjet β (by omega)]
      exact actualVertexSeries_coefficient_lower MonomialOrder.degLex K a β hβ
  choose G hGI hne hinit hcoeff using hv
  refine ⟨G,fun a => ⟨hGI a,hne a,hinit a,hcoeff a⟩,?_⟩
  let J := Ideal.span (range G)
  have hJI : J≤I := Ideal.span_le.mpr (by rintro g ⟨a,rfl⟩; exact hGI a)
  have hmap : Ideal.map (originalTaylorAlgHom n).toRingHom J≤K := Ideal.map_mono hJI
  have hD : actualInitialDiagram MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom J)=
      actualInitialDiagram MonomialOrder.degLex K := by
    apply le_antisymm
    · rintro α ⟨F,hF,hFne,he⟩
      exact ⟨F,hmap hF,hFne,he⟩
    · intro β hβ
      obtain ⟨α,hα,hαβ⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K β).mp hβ
      let a : actualInitialVertices MonomialOrder.degLex K := ⟨α,hα⟩
      apply actualInitialDiagram_upper MonomialOrder.degLex _ α β _ hαβ
      exact ⟨originalTaylorAlgHom n (G a),
        Ideal.mem_map_of_mem _ (Ideal.mem_span_range_self (x := a)),hne a,hinit a⟩
  have he := formal_ideal_eq_of_initial_diagram MonomialOrder.degLex
    (Ideal.map (originalTaylorAlgHom n).toRingHom J) K hmap hD
  exact original_formal_ideal_extension_injective n he

end
end Hironaka.HironakaActualAnalyticVertexBasis
