/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualInitialCoordinateQuotient
import Hironaka.Resolution.HironakaActualInitialNormalExtension
import Hironaka.Resolution.HironakaActualRelativeTaylorCoefficients
import Hironaka.Resolution.HironakaActualJointBaseFibre

/-! # Actual original and zero-base fibre diagrams on pure normal exponents

The actual homogeneous initial ideal is compared with the entire tangent cut
before either diagram is compared. A literal normal-coordinate retraction
retains every pure-normal leading witness. Original tangent initial
differential stability produces all compatibility used by the final theorem.
-/

set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalFibreDiagramCompare
noncomputable section
open HolGerm HironakaActualFormalInitialDiagram HironakaActualHomogeneousInitialHS
  HironakaActualInitialCoordinateQuotient HironakaActualInitialNormalExtension
  HironakaActualCoefficientPresentationCentrePower HironakaActualRelativeTaylorCoefficients
  HironakaRelativeNormalFibreHilbertSamuel HironakaActualJointBaseFibre

/-- The actual formal ideal of all original tangent coordinate variables. -/
def formalTangentIdeal (d t : ℕ) : Ideal (MvPowerSeries (Fin (d+t)) ℂ) :=
  Ideal.span (Set.range fun i : Fin d => (MvPowerSeries.X (i.castAdd t) : MvPowerSeries (Fin (d+t)) ℂ))

/-- Kill every tangent variable and literally include the remaining normal series again. -/
def normalProjection (d t : ℕ) :
    MvPowerSeries (Fin (d+t)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (d+t)) ℂ :=
  (MvPowerSeries.rename (actualNormalFormalEmbedding d t)).comp
    (MvPowerSeries.killCompl (actualNormalFormalEmbedding d t))

/-- The literal formal normal projection preserves precisely the actual pure-normal coefficients. -/
theorem normalProjection_coefficient (d t : ℕ)
    (F : MvPowerSeries (Fin (d+t)) ℂ) (a : Fin (d+t) →₀ ℕ) :
    MvPowerSeries.coeff a (normalProjection d t F)=
      if a ∈ Set.range (Finsupp.embDomain (actualNormalFormalEmbedding d t))
        then MvPowerSeries.coeff a F else 0 := by
  by_cases ha : a ∈ Set.range (Finsupp.embDomain (actualNormalFormalEmbedding d t))
  · obtain ⟨γ,rfl⟩ := ha
    simp [normalProjection,MvPowerSeries.coeff_killCompl]
  · rw [if_neg ha]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨γ,hγ⟩
    apply ha
    refine ⟨γ,?_⟩
    rw [Finsupp.embDomain_eq_mapDomain]
    exact hγ

private theorem normalProjection_pure_coefficient (d t : ℕ)
    (F : MvPowerSeries (Fin (d+t)) ℂ) (γ : Fin t →₀ ℕ) :
    MvPowerSeries.coeff (actualJoinedExponent (0 : Fin d →₀ ℕ) γ) (normalProjection d t F)=
      MvPowerSeries.coeff (actualJoinedExponent (0 : Fin d →₀ ℕ) γ) F := by
  rw [actualJoinedExponent_normal_embedding]
  simp [normalProjection,MvPowerSeries.coeff_killCompl]

private theorem tangent_not_mem_normal_embedding (d t : ℕ) (i : Fin d) :
    i.castAdd t ∉ Set.range (actualNormalFormalEmbedding d t) := by
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  change d+j.val=i.val at hh
  omega

/-- A genuine normal-extension ideal retains all its pure-normal diagram members after the entire tangent cut. -/
theorem pure_normal_diagram_add_tangent_of_normal_extension (d t : ℕ)
    (m : MonomialOrder (Fin (d+t))) (J : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (hJ : J=Ideal.map (MvPowerSeries.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom
      (Ideal.comap (MvPowerSeries.rename (Fin.natAdd d : Fin t → Fin (d+t))).toRingHom J))
    (γ : Fin t →₀ ℕ) :
    actualJoinedExponent (0 : Fin d →₀ ℕ) γ ∈ actualInitialDiagram m (J ⊔ formalTangentIdeal d t) ↔
      actualJoinedExponent (0 : Fin d →₀ ℕ) γ ∈ actualInitialDiagram m J := by
  let ρ := (MvPowerSeries.rename (actualNormalFormalEmbedding d t) :
    MvPowerSeries (Fin t) ℂ →ₐ[ℂ] MvPowerSeries (Fin (d+t)) ℂ).toRingHom
  have hτρ : (normalProjection d t).toRingHom.comp ρ=ρ := by
    apply RingHom.ext
    intro F
    change MvPowerSeries.rename (actualNormalFormalEmbedding d t)
      (MvPowerSeries.killCompl (actualNormalFormalEmbedding d t)
        (MvPowerSeries.rename (actualNormalFormalEmbedding d t) F))=
          MvPowerSeries.rename (actualNormalFormalEmbedding d t) F
    rw [MvPowerSeries.killCompl_rename_app]
  have hmapJ : Ideal.map (normalProjection d t).toRingHom J=J := by
    calc
      _ = Ideal.map (normalProjection d t).toRingHom (Ideal.map ρ (Ideal.comap ρ J)) :=
        congrArg (Ideal.map (normalProjection d t).toRingHom) hJ
      _ = Ideal.map ρ (Ideal.comap ρ J) := by rw [Ideal.map_map,hτρ]
      _ = J := hJ.symm
  have hmapT : Ideal.map (normalProjection d t).toRingHom (formalTangentIdeal d t)=⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker _).mpr
    apply Ideal.span_le.mpr
    rintro F ⟨i,rfl⟩
    change normalProjection d t (MvPowerSeries.X (i.castAdd t))=0
    simp only [normalProjection,AlgHom.comp_apply,
      MvPowerSeries.killCompl_X_eq_zero (tangent_not_mem_normal_embedding d t i),map_zero]
  constructor
  · rintro ⟨F,hF,hFne,he⟩
    have hτF : normalProjection d t F ∈ J := by
      have hm := Ideal.mem_map_of_mem (normalProjection d t).toRingHom hF
      rw [Ideal.map_sup,hmapJ,hmapT,sup_bot_eq] at hm
      exact hm
    have hcoef : MvPowerSeries.coeff (actualJoinedExponent (0 : Fin d →₀ ℕ) γ) F ≠ 0 := by
      rw [← he]
      exact (actualInitialExponent_spec m F hFne).1
    have hτcoef : MvPowerSeries.coeff (actualJoinedExponent (0 : Fin d →₀ ℕ) γ)
        (normalProjection d t F) ≠ 0 := by
      rw [normalProjection_pure_coefficient]
      exact hcoef
    have hτne : normalProjection d t F ≠ 0 := by
      intro hz
      exact hτcoef (by rw [hz,map_zero])
    refine ⟨normalProjection d t F,hτF,hτne,?_⟩
    apply actualInitialExponent_eq_of_coefficients m _ hτne _ hτcoef
    intro a ha
    rw [normalProjection_coefficient]
    split_ifs
    · exact coeff_eq_zero_of_lt_actualInitialExponent m F hFne a (by rw [he]; exact ha)
    · rfl
  · rintro ⟨F,hF,hFne,he⟩
    exact ⟨F,Ideal.mem_sup_left hF,hFne,he⟩

private theorem successiveCoordinateQuotient_eq_sup_span {n : ℕ}
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (L : List (Fin n)) :
    successiveCoordinateQuotient K L =
      K ⊔ Ideal.span ((MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) ℂ) '' {i | i ∈ L}) := by
  induction L generalizing K with
  | nil => simp [successiveCoordinateQuotient]
  | cons i L ih =>
    have hs : (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) ℂ) '' {j | j ∈ i :: L} =
        {MvPowerSeries.X i} ∪ MvPowerSeries.X '' {j | j ∈ L} := by
      ext F
      simp only [Set.mem_image,Set.mem_ofPred_eq,List.mem_cons,Set.mem_union,Set.mem_singleton_iff]
      constructor
      · rintro ⟨j,hj,rfl⟩
        rcases hj with rfl | hj
        · exact Or.inl rfl
        · exact Or.inr ⟨j,hj,rfl⟩
      · rintro (rfl | ⟨j,hj,rfl⟩)
        · exact ⟨i,Or.inl rfl,rfl⟩
        · exact ⟨j,Or.inr hj,rfl⟩
    rw [successiveCoordinateQuotient,ih,hs,Ideal.span_union,sup_assoc]

private theorem successive_tangent_quotient_eq (d t : ℕ)
    (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ)) :
    successiveCoordinateQuotient K (List.ofFn (Fin.castAdd t : Fin d → Fin (d+t))) =
      K ⊔ formalTangentIdeal d t := by
  rw [successiveCoordinateQuotient_eq_sup_span]
  have hs : {i : Fin (d+t) | i ∈ List.ofFn (Fin.castAdd t : Fin d → Fin (d+t))} =
      Set.range (Fin.castAdd t : Fin d → Fin (d+t)) := by
    ext i
    exact List.mem_ofFn' (Fin.castAdd t : Fin d → Fin (d+t)) i
  rw [hs,← Set.range_comp]
  rfl

/-- Whole tangent formal differential stability gives the actual all-tangent initial-ideal equality internally. -/
theorem actualInitialIdeal_add_all_tangent (d t : ℕ)
    (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (hD : ∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
      F ∈ actualHomogeneousInitialIdeal K →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal K) :
    actualHomogeneousInitialIdeal (K ⊔ formalTangentIdeal d t) =
      actualHomogeneousInitialIdeal K ⊔ formalTangentIdeal d t := by
  let L := List.ofFn (Fin.castAdd t : Fin d → Fin (d+t))
  have hL : L.Nodup := List.nodup_ofFn.mpr (by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (d+t) => z.val) hij))
  have hDL : ∀ i ∈ L, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K := by
    intro i hi F hF
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    exact hD j F hF
  have he := (actualInitialIdeal_successive_coordinate_quotients K L hL hDL).1
  simpa only [L,successive_tangent_quotient_eq] using he

/-- Pure normal membership in the true fibre diagram is exactly membership in the original true point diagram. -/
theorem pure_normal_diagram_add_tangent_iff (d t : ℕ)
    (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (hD : ∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
      F ∈ actualHomogeneousInitialIdeal K →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal K)
    (γ : Fin t →₀ ℕ) :
    actualJoinedExponent (0 : Fin d →₀ ℕ) γ ∈
        actualInitialDiagram MonomialOrder.degLex (K ⊔ formalTangentIdeal d t) ↔
      actualJoinedExponent (0 : Fin d →₀ ℕ) γ ∈ actualInitialDiagram MonomialOrder.degLex K := by
  have hDP : ∀ (i : Fin d) (P : MvPolynomial (Fin (d+t)) ℂ),
      (P : MvPowerSeries (Fin (d+t)) ℂ) ∈ actualHomogeneousInitialIdeal K →
      (MvPolynomial.pderiv (i.castAdd t) P : MvPowerSeries (Fin (d+t)) ℂ) ∈
        actualHomogeneousInitialIdeal K := by
    intro i P hP
    rw [← MvPowerSeries.pderiv_coe]
    exact hD i P hP
  rw [← actual_homogeneous_initial_ideal_diagram (K ⊔ formalTangentIdeal d t),
    actualInitialIdeal_add_all_tangent d t K hD,
    ← actual_homogeneous_initial_ideal_diagram K]
  exact pure_normal_diagram_add_tangent_of_normal_extension d t MonomialOrder.degLex _
    (actualHomogeneousInitialIdeal_eq_normal_extension_of_tangent_pderiv d t K hDP) γ

/-- Taylor sends the entire original base maximal ideal to precisely all formal tangent variables. -/
theorem map_originalBaseMaximalIdeal_actualTaylor (d t : ℕ) :
    Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (originalBaseMaximalIdeal d t) =
      formalTangentIdeal d t := by
  rw [baseMaximalIdeal_eq_tangent_span,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact actualUnshiftedTaylor_coordinate (d+t) (i.castAdd t)

/-- The same original ideal's literal zero-base fibre has exactly the same pure-normal diagram labels. -/
theorem pure_normal_fibre_diagram_iff (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hD : ∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
      F ∈ actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) →
      MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈
        actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I))
    (γ : Fin t →₀ ℕ) :
    actualJoinedExponent (0 : Fin d →₀ ℕ) γ ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (I ⊔ originalBaseMaximalIdeal d t)) ↔
      actualJoinedExponent (0 : Fin d →₀ ℕ) γ ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) := by
  rw [Ideal.map_sup,map_originalBaseMaximalIdeal_actualTaylor]
  exact pure_normal_diagram_add_tangent_iff d t _ hD γ

end
end Hironaka.HironakaActualNormalFibreDiagramCompare
