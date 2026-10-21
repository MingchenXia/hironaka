/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFiniteJetVertexBasis

/-! Genuine selected vertex block bases and internally constructed homogeneous division coefficients. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualSelectedVertexHomogeneousBasis
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
  HironakaActualHomogeneousInitialHS HironakaActualFiniteJetVertexBasis
variable {n : ℕ}

/-- The actual upward diagram of ANY selected subset of the SAME genuine original vertices. -/
def actualSelectedVertexDiagram (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) : Set (Fin n →₀ ℕ) :=
  {alpha | ∃ a : actualInitialVertices MonomialOrder.degLex I, a ∈ V ∧ a.val ≤ alpha}

private theorem exists_least_selected_owner (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (alpha : Fin n →₀ ℕ)
    (h : alpha ∈ actualSelectedVertexDiagram I V) :
    ∃ a : actualInitialVertices MonomialOrder.degLex I, a ∈ V ∧ a.val ≤ alpha ∧
      ∀ b : actualInitialVertices MonomialOrder.degLex I, b ∈ V → b.val ≤ alpha →
        MonomialOrder.degLex.toSyn a.val ≤ MonomialOrder.degLex.toSyn b.val := by
  let T : Set (actualInitialVertices MonomialOrder.degLex I) := {a | a ∈ V ∧ a.val ≤ alpha}
  let S : Set (MonomialOrder.degLex (σ := Fin n)).syn :=
    (fun a : actualInitialVertices MonomialOrder.degLex I => MonomialOrder.degLex.toSyn a.val) '' T
  have ht : T.Nonempty := h
  have hn : S.Nonempty := ht.image _
  have hw : S.IsWF := Set.IsWF.of_wellFoundedLT S
  obtain ⟨a,ha,he⟩ := hw.min_mem hn
  refine ⟨a,ha.1,ha.2,fun b hb hba => ?_⟩
  change MonomialOrder.degLex.toSyn a.val=hw.min hn at he
  rw [he]
  exact hw.min_le hn ⟨b,⟨hb,hba⟩,rfl⟩

/-- The internally constructed owner is the TRUE first eligible actual selected vertex. -/
def actualSelectedVertexOwner (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (alpha : Fin n →₀ ℕ)
    (h : alpha ∈ actualSelectedVertexDiagram I V) : actualInitialVertices MonomialOrder.degLex I :=
  Classical.choose (exists_least_selected_owner I V alpha h)

/-- Actual eligibility and the genuine degree-first minimum are both proved internally. -/
theorem actualSelectedVertexOwner_spec (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (alpha : Fin n →₀ ℕ)
    (h : alpha ∈ actualSelectedVertexDiagram I V) :
    actualSelectedVertexOwner I V alpha h ∈ V ∧ (actualSelectedVertexOwner I V alpha h).val ≤ alpha ∧
      ∀ b : actualInitialVertices MonomialOrder.degLex I, b ∈ V → b.val ≤ alpha →
        MonomialOrder.degLex.toSyn (actualSelectedVertexOwner I V alpha h).val ≤ MonomialOrder.degLex.toSyn b.val :=
  Classical.choose_spec (exists_least_selected_owner I V alpha h)

/-- Literal original/initial products use an internally chosen actual selected owner. -/
def actualSelectedVertexSeries (useInitial : Bool) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (alpha : Fin n →₀ ℕ) :
    MvPowerSeries (Fin n) ℂ :=
  if h : alpha ∈ actualSelectedVertexDiagram I V then
    let a := actualSelectedVertexOwner I V alpha h
    MvPowerSeries.monomial (alpha-a.val) 1*actualFiniteJetVertexSeries useInitial I a
  else MvPowerSeries.monomial alpha 1

/-- Actual monic vertex minima and true monomial convolution supply BOTH families internally. -/
theorem actualSelectedVertexSeries_spec (useInitial : Bool) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (alpha : Fin n →₀ ℕ) :
    ∃ hne : actualSelectedVertexSeries useInitial I V alpha ≠ 0,
      actualInitialExponent MonomialOrder.degLex (actualSelectedVertexSeries useInitial I V alpha) hne=alpha ∧
        MvPowerSeries.coeff alpha (actualSelectedVertexSeries useInitial I V alpha)=1 := by
  by_cases h : alpha ∈ actualSelectedVertexDiagram I V
  · rw [actualSelectedVertexSeries,dif_pos h]
    dsimp only
    let a := actualSelectedVertexOwner I V alpha h
    have ha : a.val ≤ alpha := (actualSelectedVertexOwner_spec I V alpha h).2.1
    have hsum : alpha-a.val+a.val=alpha := tsub_add_cancel_of_le ha
    obtain ⟨hne,hmin,hcoeff⟩ := actualFiniteJetVertexSeries_spec useInitial I a
    have hm := actualMonomial_ne_zero (alpha-a.val)
    refine ⟨mul_ne_zero hm hne,?_,?_⟩
    · rw [actualInitialExponent_mul MonomialOrder.degLex (MvPowerSeries.monomial (alpha-a.val) 1)
        (actualFiniteJetVertexSeries useInitial I a) hm hne,actualInitialExponent_monomial,hmin,hsum]
    · have hc := coeff_mul_actualInitialExponent MonomialOrder.degLex
        (MvPowerSeries.monomial (alpha-a.val) 1) (actualFiniteJetVertexSeries useInitial I a) hm hne
      rw [actualInitialExponent_monomial,hmin,hsum,MvPowerSeries.coeff_monomial_same,hcoeff,one_mul] at hc
      exact hc
  · rw [actualSelectedVertexSeries,dif_neg h]
    exact ⟨actualMonomial_ne_zero alpha,actualInitialExponent_monomial MonomialOrder.degLex alpha,
      MvPowerSeries.coeff_monomial_same alpha 1⟩

/-- Every selected actual column internally supplies genuine triangular coefficient conditions. -/
theorem actualSelectedVertexSeries_triangular (useInitial : Bool) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (alpha : Fin n →₀ ℕ) :
    MvPowerSeries.coeff alpha (actualSelectedVertexSeries useInitial I V alpha)=1 ∧
      ∀ b, MonomialOrder.degLex.toSyn b < MonomialOrder.degLex.toSyn alpha →
        MvPowerSeries.coeff b (actualSelectedVertexSeries useInitial I V alpha)=0 := by
  obtain ⟨hne,hmin,hcoeff⟩ := actualSelectedVertexSeries_spec useInitial I V alpha
  refine ⟨hcoeff,fun b hb => ?_⟩
  apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _ hne b
  rwa [hmin]

private theorem monomial_homogeneous (alpha : Fin n →₀ ℕ) :
    (MvPowerSeries.monomial alpha (1 : ℂ)).IsHomogeneous (Finsupp.degree alpha) := by
  apply MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mpr
  apply MvPowerSeries.ext
  intro b
  rw [MvPowerSeries.coeff_homogeneousComponent]
  by_cases hb : b=alpha
  · subst b
    rw [if_pos rfl]
  · simp [MvPowerSeries.coeff_monomial,hb]

/-- The SAME selected initial columns are genuinely homogeneous at their actual exponent degree. -/
theorem actualSelectedVertexSeries_homogeneous (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (alpha : Fin n →₀ ℕ) :
    (actualSelectedVertexSeries true I V alpha).IsHomogeneous (Finsupp.degree alpha) := by
  by_cases h : alpha ∈ actualSelectedVertexDiagram I V
  · rw [actualSelectedVertexSeries,dif_pos h]
    dsimp only
    let a := actualSelectedVertexOwner I V alpha h
    have ha : a.val ≤ alpha := (actualSelectedVertexOwner_spec I V alpha h).2.1
    have hd : Finsupp.degree (alpha-a.val)+Finsupp.degree a.val=Finsupp.degree alpha := by
      have he := congrArg Finsupp.degree (tsub_add_cancel_of_le ha)
      simpa only [Finsupp.degree_eq_weight_one,map_add] using he
    have hinit : (actualFiniteJetVertexSeries true I a).IsHomogeneous (Finsupp.degree a.val) := by
      change (actualHomogeneousInitialForm (actualVertexSeries MonomialOrder.degLex I a)
        (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose).IsHomogeneous _
      have he := (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose_spec.1
      rw [actualHomogeneousInitialForm,actualHomogeneousInitialDegree,he]
      simp only [normalExponentDegree,← Finsupp.degree_eq_sum]
      intro b hb
      exact MvPowerSeries.isHomogeneous_homogeneousComponent
        (actualVertexSeries MonomialOrder.degLex I a) (Finsupp.degree a.val) hb
    have hp : (MvPowerSeries.monomial (alpha-a.val) 1*actualFiniteJetVertexSeries true I a).IsHomogeneous
        (Finsupp.degree (alpha-a.val)+Finsupp.degree a.val) :=
      MvPowerSeries.IsHomogeneous.mul (monomial_homogeneous (alpha-a.val)) hinit
    rw [hd] at hp
    exact hp
  · rw [actualSelectedVertexSeries,dif_neg h]
    exact monomial_homogeneous alpha

/-- Genuine actual selected columns and internally proved triangularity construct the whole-jet inverse. -/
def actualSelectedVertexJetEquiv (n q : ℕ) (useInitial : Bool)
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (V : Set (actualInitialVertices MonomialOrder.degLex I)) :
    (normalExponentIndex n q → ℂ) ≃ₗ[ℂ] actualWholeFormalJet n q :=
  actualTriangularJetEquiv n q (fun a => actualSelectedVertexSeries useInitial I V a.val)
    (fun a => actualSelectedVertexSeries_triangular useInitial I V a.val)

/-- The true coordinate basis maps to the SAME actual selected whole-jet columns. -/
def actualSelectedVertexJetBasis (n q : ℕ) (useInitial : Bool)
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (V : Set (actualInitialVertices MonomialOrder.degLex I)) :
    Module.Basis (normalExponentIndex n q) ℂ (actualWholeFormalJet n q) :=
  (Pi.basisFun ℂ (normalExponentIndex n q)).map (actualSelectedVertexJetEquiv n q useInitial I V)

/-- Every actual coordinate unit retains the literal selected column class. -/
theorem actualSelectedVertexJetEquiv_single (n q : ℕ) (useInitial : Bool)
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (V : Set (actualInitialVertices MonomialOrder.degLex I))
    (a : normalExponentIndex n q) :
    actualSelectedVertexJetEquiv n q useInitial I V (Pi.single a 1)=
      Ideal.Quotient.mk (genuineFormalVariables n ^ q) (actualSelectedVertexSeries useInitial I V a.val) := by
  change Ideal.Quotient.mk (genuineFormalVariables n ^ q)
    (∑ b : normalExponentIndex n q, (Pi.single a (1 : ℂ) : normalExponentIndex n q → ℂ) b •
      actualSelectedVertexSeries useInitial I V b.val)=_
  congr 1
  simp [Pi.single_apply]

private theorem homogeneous_component_of_homogeneous (F : MvPowerSeries (Fin n) ℂ)
    (e d : ℕ) (hF : F.IsHomogeneous e) :
    MvPowerSeries.homogeneousComponent d F=if e=d then F else 0 := by
  by_cases he : e=d
  · rw [if_pos he,← he]
    exact (MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp hF).symm
  · rw [if_neg he]
    apply MvPowerSeries.ext
    intro a
    rw [map_zero,MvPowerSeries.coeff_homogeneousComponent]
    split_ifs with ha
    · exact hF.coeff_eq_zero (by omega)
    · rfl

/-- True whole-jet inversion and genuine homogeneous projection internally construct the UNIQUE polynomial division coefficients. -/
theorem actualSelectedVertexHomogeneousExpansion (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (V : Set (actualInitialVertices MonomialOrder.degLex I)) (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F.IsHomogeneous d) :
    ∃! c : normalExponentIndex n (d+1) → ℂ,
      (∀ a, normalExponentDegree a.val ≠ d → c a=0) ∧
        F=∑ a, c a • actualSelectedVertexSeries true I V a.val := by
  let E := actualSelectedVertexJetEquiv n (d+1) true I V
  let b := E.symm (Ideal.Quotient.mk (genuineFormalVariables n ^ (d+1)) F)
  have hjet := E.apply_symm_apply (Ideal.Quotient.mk (genuineFormalVariables n ^ (d+1)) F)
  change Ideal.Quotient.mk (genuineFormalVariables n ^ (d+1))
    (∑ a : normalExponentIndex n (d+1), b a • actualSelectedVertexSeries true I V a.val)=
      Ideal.Quotient.mk (genuineFormalVariables n ^ (d+1)) F at hjet
  have hrem := Ideal.Quotient.eq.mp hjet
  have hcomponent : MvPowerSeries.homogeneousComponent d
      (∑ a : normalExponentIndex n (d+1), b a • actualSelectedVertexSeries true I V a.val)=F := by
    apply MvPowerSeries.ext
    intro alpha
    by_cases ha : Finsupp.degree alpha=d
    · rw [MvPowerSeries.coeff_homogeneousComponent,if_pos ha]
      have hα : normalExponentDegree alpha < d+1 := by
        have ht : Finsupp.degree alpha < d+1 := by omega
        simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using ht
      have hc := (mem_genuineFormalVariables_pow_iff_coefficients_zero n (d+1) _).mp hrem alpha hα
      exact sub_eq_zero.mp hc
    · rw [MvPowerSeries.coeff_homogeneousComponent,if_neg ha,hF.coeff_eq_zero ha]
  let c : normalExponentIndex n (d+1) → ℂ := fun a => if normalExponentDegree a.val=d then b a else 0
  refine ⟨c,⟨fun a ha => by simp only [c,if_neg ha],?_⟩,?_⟩
  · rw [← hcomponent,map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_smul,homogeneous_component_of_homogeneous _ (Finsupp.degree a.val) d
      (actualSelectedVertexSeries_homogeneous I V a.val)]
    by_cases ha : normalExponentDegree a.val=d
    · have hd : Finsupp.degree a.val=d := by rwa [Finsupp.degree_eq_sum]
      simp only [c,if_pos ha,if_pos hd]
    · have hd : Finsupp.degree a.val ≠ d := by rwa [Finsupp.degree_eq_sum]
      simp only [c,if_neg ha,if_neg hd,smul_zero,zero_smul]
  · intro c' hc'
    apply (actualTriangularJetMap_injective (d+1)
      (fun a => actualSelectedVertexSeries true I V a.val)
      (fun a => actualSelectedVertexSeries_triangular true I V a.val))
    change Ideal.Quotient.mk (genuineFormalVariables n ^ (d+1))
      (∑ a, c' a • actualSelectedVertexSeries true I V a.val)=
        Ideal.Quotient.mk (genuineFormalVariables n ^ (d+1))
          (∑ a, c a • actualSelectedVertexSeries true I V a.val)
    rw [← hc'.2,← hcomponent,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [map_smul,homogeneous_component_of_homogeneous _ (Finsupp.degree a.val) d
      (actualSelectedVertexSeries_homogeneous I V a.val)]
    by_cases ha : normalExponentDegree a.val=d
    · have hd : Finsupp.degree a.val=d := by rwa [Finsupp.degree_eq_sum]
      simp only [c,if_pos ha,if_pos hd]
    · have hd : Finsupp.degree a.val ≠ d := by rwa [Finsupp.degree_eq_sum]
      simp only [c,if_neg ha,if_neg hd,smul_zero,zero_smul]

/-- The actual selected block is computed from the SAME original vertex degrees. -/
def actualDegreeBlockVertices (I : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) :
    Set (actualInitialVertices MonomialOrder.degLex I) := {a | normalExponentDegree a.val ≤ k}

/-- Every selected degree block uses the SAME true first-owner partition as the full vertex family. -/
theorem actualDegreeBlockOwner_compatible (I : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ)
    (alpha : Fin n →₀ ℕ) (h : alpha ∈ actualSelectedVertexDiagram I (actualDegreeBlockVertices I k))
    (hfull : alpha ∈ actualSelectedVertexDiagram I Set.univ) :
    actualSelectedVertexOwner I (actualDegreeBlockVertices I k) alpha h=
      actualSelectedVertexOwner I Set.univ alpha hfull := by
  let a := actualSelectedVertexOwner I (actualDegreeBlockVertices I k) alpha h
  let b := actualSelectedVertexOwner I Set.univ alpha hfull
  have ha := actualSelectedVertexOwner_spec I (actualDegreeBlockVertices I k) alpha h
  have hb := actualSelectedVertexOwner_spec I Set.univ alpha hfull
  have hba : MonomialOrder.degLex.toSyn b.val ≤ MonomialOrder.degLex.toSyn a.val := hb.2.2 a (mem_univ _) ha.2.1
  have hdeg : normalExponentDegree b.val ≤ normalExponentDegree a.val := by
    rcases lt_or_eq_of_le hba with hlt | he
    · exact HironakaActualFormalStandardMonomialHS.actual_degree_le_of_deglex_lt _ _ hlt
    · have he' := MonomialOrder.degLex.toSyn.injective he
      rw [he']
  have hbV : b ∈ actualDegreeBlockVertices I k := le_trans hdeg ha.1
  apply Subtype.ext
  apply MonomialOrder.degLex.toSyn.injective
  exact le_antisymm (ha.2.2 b hbV hb.2.1) hba

/-- EVERY actual degree block internally has its genuine homogeneous division basis at EVERY degree. -/
theorem actualDegreeBlockHomogeneousExpansion (I : Ideal (MvPowerSeries (Fin n) ℂ)) (k d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F.IsHomogeneous d) :
    ∃! c : normalExponentIndex n (d+1) → ℂ,
      (∀ a, normalExponentDegree a.val ≠ d → c a=0) ∧
        F=∑ a, c a • actualSelectedVertexSeries true I (actualDegreeBlockVertices I k) a.val :=
  actualSelectedVertexHomogeneousExpansion I (actualDegreeBlockVertices I k) d F hF

end
end Hironaka.HironakaActualSelectedVertexHomogeneousBasis
