/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualReducedBasisDivision
import Hironaka.Support.FormalStandardMonomialHSComplementExact

set_option autoImplicit false
open Set Classical
open scoped MonomialOrder
namespace Hironaka.HironakaActualWeightedVertexHS
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualReducedBasisDivision
  HironakaActualFormalStandardMonomialHS HironakaActualOriginalFormalHSTransfer
variable {n : ℕ}

/-- Actual coefficient projection for arbitrary nonnegative coordinate weights, including zero tangent weights. -/
def actualWeightedComponent (w : Fin n → ℕ) (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries (Fin n) ℂ := fun a => if Finsupp.weight w a=d then MvPowerSeries.coeff a F else 0

theorem actualWeightedComponent_coefficient (w : Fin n → ℕ) (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (a : Fin n →₀ ℕ) :
    MvPowerSeries.coeff a (actualWeightedComponent w d F)=
      if Finsupp.weight w a=d then MvPowerSeries.coeff a F else 0 := rfl

/-- The actual original least nonzero coefficient survives at its own weight. -/
theorem actualWeightedComponent_ne_zero (m : MonomialOrder (Fin n)) (w : Fin n → ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) :
    actualWeightedComponent w (Finsupp.weight w (actualInitialExponent m F hF)) F ≠ 0 := by
  intro hz
  have he := congrArg (MvPowerSeries.coeff (actualInitialExponent m F hF)) hz
  rw [actualWeightedComponent_coefficient,if_pos rfl,map_zero] at he
  exact (actualInitialExponent_spec m F hF).1 he

/-- The actual component retains precisely the same genuine minimum for the same original monomial order. -/
theorem actualWeightedComponent_initialExponent (m : MonomialOrder (Fin n)) (w : Fin n → ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) :
    actualInitialExponent m (actualWeightedComponent w (Finsupp.weight w (actualInitialExponent m F hF)) F)
      (actualWeightedComponent_ne_zero m w F hF)=actualInitialExponent m F hF := by
  apply actualInitialExponent_eq_of_coefficients
  · rw [actualWeightedComponent_coefficient,if_pos rfl]
    exact (actualInitialExponent_spec m F hF).1
  · intro a ha
    rw [actualWeightedComponent_coefficient]
    split_ifs
    · exact coeff_eq_zero_of_lt_actualInitialExponent m F hF a ha
    · rfl

/-- The entire ideal spanned by the actual components of a genuine monic original vertex family. -/
def actualWeightedVertexIdeal (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : ActualMonicVertexFamily m I) (w : Fin n → ℕ) : Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.span (range fun a : actualInitialVertices m I =>
    actualWeightedComponent w (Finsupp.weight w a.val) (B.series a))

/-- Every actual original diagram exponent remains in the entire component ideal diagram. -/
theorem actualInitialDiagram_subset_weightedVertexIdeal (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (w : Fin n → ℕ) :
    actualInitialDiagram m I ⊆ actualInitialDiagram m (actualWeightedVertexIdeal m I B w) := by
  intro c hc
  obtain ⟨a,ha,hac⟩ := (mem_actualInitialDiagram_iff_vertex_le m I c).mp hc
  let av : actualInitialVertices m I := ⟨a,ha⟩
  have hF : B.series av ≠ 0 := by
    intro hz
    have he := congrArg (MvPowerSeries.coeff a) hz
    rw [show MvPowerSeries.coeff a (B.series av)=1 from B.monic av,map_zero] at he
    exact one_ne_zero he
  have he : actualInitialExponent m (B.series av) hF=a :=
    actualInitialExponent_eq_of_coefficients m _ hF a (by rw [B.monic av]; exact one_ne_zero)
      (B.lower av)
  have hcomp := actualWeightedComponent_ne_zero m w (B.series av) hF
  rw [he] at hcomp
  have hmin : actualInitialExponent m (actualWeightedComponent w (Finsupp.weight w a) (B.series av)) hcomp=a := by
    simpa only [he] using actualWeightedComponent_initialExponent m w (B.series av) hF
  apply actualInitialDiagram_upper m _ a c _ hac
  exact ⟨_,Ideal.subset_span ⟨av,rfl⟩,hcomp,hmin⟩

/-- Every original whole formal quotient dimension satisfies the genuine all-order vertex-weight inequality. -/
theorem genuineFormalHilbertSamuelValue_weightedVertex_le
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily MonomialOrder.degLex I)
    (w : Fin n → ℕ) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n (actualWeightedVertexIdeal MonomialOrder.degLex I B w) ℓ ≤
      genuineFormalHilbertSamuelValue n I ℓ := by
  rw [genuineFormalHilbertSamuelValue_eq_card_standardIndex,genuineFormalHilbertSamuelValue_eq_card_standardIndex]
  let f : actualStandardIndex n (actualWeightedVertexIdeal MonomialOrder.degLex I B w) (ℓ+1) →
      actualStandardIndex n I (ℓ+1) := fun a =>
    ⟨a.val,fun ha => a.property (actualInitialDiagram_subset_weightedVertexIdeal MonomialOrder.degLex I B w ha)⟩
  apply Fintype.card_le_of_injective f
  intro a b h
  apply Subtype.ext
  exact congrArg (fun t : actualStandardIndex n I (ℓ+1) => t.val) h

end
end Hironaka.HironakaActualWeightedVertexHS
