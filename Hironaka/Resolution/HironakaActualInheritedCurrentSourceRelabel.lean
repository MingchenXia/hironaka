import Hironaka.Resolution.HironakaActualInheritedHSDirections
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Literal old labels are transported to the CURRENT whole Taylor ideal.
The actual selected least-degree vertices are preserved by congruence of
one raw finite-set existence predicate and proof irrelevance, including ties.
The last theorem really supplies the CURRENT-family hypotheses of the actual
HS direction producer; old-ideal membership is never inferred. -/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualInheritedCurrentSourceRelabel

noncomputable section

open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalInitialDiagram
  HironakaActualRelativeNormalJetDivision HironakaActualCanonicalBlockJacobian
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualInheritedNestedContactFlag
  HironakaActualRelativeStandardnessBlockSupport HironakaActualAnalyticBlockGraphTranslation
  HironakaActualInheritedHSDirections HironakaActualAnalyticBlowupTaylor
  HironakaActualFormalStrictGenerators HironakaActualOriginalFormalHSTransfer

variable {n : ℕ} {K0 K1 : Ideal (MvPowerSeries (Fin n) ℂ)}

/-- Whole diagram equality gives exact finite vertices, not just equal cards. -/
theorem actualInitialVertices_eq_of_diagram_eq
    (hD : actualInitialDiagram MonomialOrder.degLex K0 =
      actualInitialDiagram MonomialOrder.degLex K1) :
    actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1 := by
  ext a
  simp only [actualInitialVertices, Set.Finite.mem_toFinset, hD]

/-- Same exponents with only their membership proofs changed. -/
def actualVertexRelabel
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1) :
    actualInitialVertices MonomialOrder.degLex K0 ≃ actualInitialVertices MonomialOrder.degLex K1 where
  toFun a := ⟨a.val, by rw [← hV]; exact a.property⟩
  invFun a := ⟨a.val, by rw [hV]; exact a.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

private theorem raw_selected_value_congr
    (V W : Finset (Fin n →₀ ℕ)) (hVW : V = W) (j : Fin n)
    (hV : ∃ a : V, a.val j ≠ 0 ∧ ∀ b : V, b.val j ≠ 0 →
      normalExponentDegree a.val ≤ normalExponentDegree b.val)
    (hW : ∃ a : W, a.val j ≠ 0 ∧ ∀ b : W, b.val j ≠ 0 →
      normalExponentDegree a.val ≤ normalExponentDegree b.val) :
    (Classical.choose hV).val = (Classical.choose hW).val := by
  subst W
  rfl

/-- This is congruence of the SAME raw existence predicate. Least-degree ties
are NOT treated as a uniqueness assertion. -/
theorem actualCanonicalDerivativeVertex_val_congr
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (j : Fin n) (hj0 : j ∈ actualCanonicalEssentialVariables MonomialOrder.degLex K0)
    (hj1 : j ∈ actualCanonicalEssentialVariables MonomialOrder.degLex K1) :
    (actualCanonicalDerivativeVertex MonomialOrder.degLex K0 ⟨j, hj0⟩).val =
      (actualCanonicalDerivativeVertex MonomialOrder.degLex K1 ⟨j, hj1⟩).val := by
  have h0 : ∃ a : actualInitialVertices MonomialOrder.degLex K0,
      a.val j ≠ 0 ∧ ∀ b : actualInitialVertices MonomialOrder.degLex K0, b.val j ≠ 0 →
        normalExponentDegree a.val ≤ normalExponentDegree b.val :=
    ⟨actualCanonicalDerivativeVertex MonomialOrder.degLex K0 ⟨j, hj0⟩,
      actualCanonicalDerivativeVertex_spec MonomialOrder.degLex K0 ⟨j, hj0⟩⟩
  have h1 : ∃ a : actualInitialVertices MonomialOrder.degLex K1,
      a.val j ≠ 0 ∧ ∀ b : actualInitialVertices MonomialOrder.degLex K1, b.val j ≠ 0 →
        normalExponentDegree a.val ≤ normalExponentDegree b.val :=
    ⟨actualCanonicalDerivativeVertex MonomialOrder.degLex K1 ⟨j, hj1⟩,
      actualCanonicalDerivativeVertex_spec MonomialOrder.degLex K1 ⟨j, hj1⟩⟩
  change (Classical.choose h0).val = (Classical.choose h1).val
  exact raw_selected_value_congr _ _ hV j h0 h1

theorem actualCanonicalDerivativeExponent_congr
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (j : Fin n) (hj0 : j ∈ actualCanonicalEssentialVariables MonomialOrder.degLex K0)
    (hj1 : j ∈ actualCanonicalEssentialVariables MonomialOrder.degLex K1) :
    actualCanonicalDerivativeExponent MonomialOrder.degLex K0 ⟨j, hj0⟩ =
      actualCanonicalDerivativeExponent MonomialOrder.degLex K1 ⟨j, hj1⟩ := by
  unfold actualCanonicalDerivativeExponent
  rw [actualCanonicalDerivativeVertex_val_congr hV j hj0 hj1]

theorem actualEssentialVariables_eq_of_vertices_eq
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1) :
    actualCanonicalEssentialVariables MonomialOrder.degLex K0 =
      actualCanonicalEssentialVariables MonomialOrder.degLex K1 := by
  ext i
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨actualVertexRelabel hV a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨(actualVertexRelabel hV).symm a, ha⟩

theorem actualPrefixVariables_eq_of_vertices_eq
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (k : ℕ) :
    actualDegreePrefixVariables MonomialOrder.degLex K0 k =
      actualDegreePrefixVariables MonomialOrder.degLex K1 k := by
  ext i
  constructor
  · rintro ⟨a, ha, hai⟩
    exact ⟨actualVertexRelabel hV a, ha, hai⟩
  · rintro ⟨a, ha, hai⟩
    exact ⟨(actualVertexRelabel hV).symm a, ha, hai⟩

def actualEssentialRelabel
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1) :
    actualCanonicalEssentialVariables MonomialOrder.degLex K0 ≃
      actualCanonicalEssentialVariables MonomialOrder.degLex K1 :=
  Equiv.setCongr (actualEssentialVariables_eq_of_vertices_eq hV)

def actualPrefixRelabel
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (k : ℕ) :
    actualDegreePrefixVariables MonomialOrder.degLex K0 k ≃
      actualDegreePrefixVariables MonomialOrder.degLex K1 k :=
  Equiv.setCongr (actualPrefixVariables_eq_of_vertices_eq hV k)

/-- No new germ is chosen: only the literal finite vertex membership proof changes. -/
def actualInheritedRelabelFamily (G : ActualAnalyticInheritedFamily n 0 K0)
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1) :
    ActualAnalyticInheritedFamily n 0 K1 where
  germs a := G.germs ((actualVertexRelabel hV).symm a)
  monic a := G.monic ((actualVertexRelabel hV).symm a)
  lower a β hβ := G.lower ((actualVertexRelabel hV).symm a) β hβ

theorem actualInheritedRelabelFamily_germ (G : ActualAnalyticInheritedFamily n 0 K0)
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (a : actualInitialVertices MonomialOrder.degLex K0) :
    (actualInheritedRelabelFamily G hV).germs (actualVertexRelabel hV a) = G.germs a := rfl

theorem actualInheritedRelabelFamily_range (G : ActualAnalyticInheritedFamily n 0 K0)
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1) :
    range (actualInheritedRelabelFamily G hV).germs = range G.germs := by
  ext F
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(actualVertexRelabel hV).symm a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨actualVertexRelabel hV a, rfl⟩

theorem actualInheritedRelabelFamily_selected_derivative
    (G : ActualAnalyticInheritedFamily n 0 K0)
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (j : actualCanonicalEssentialVariables MonomialOrder.degLex K0) :
    actualInheritedEssentialDerivative (actualInheritedRelabelFamily G hV) (actualEssentialRelabel hV j) =
      actualInheritedEssentialDerivative G j := by
  have hvertex : actualVertexRelabel hV (actualCanonicalDerivativeVertex MonomialOrder.degLex K0 j) =
      actualCanonicalDerivativeVertex MonomialOrder.degLex K1 (actualEssentialRelabel hV j) := by
    apply Subtype.ext
    exact actualCanonicalDerivativeVertex_val_congr hV j.val j.property
      (actualEssentialRelabel hV j).property
  have hβ := actualCanonicalDerivativeExponent_congr hV j.val j.property
    (actualEssentialRelabel hV j).property
  change actualCanonicalDerivativeExponent MonomialOrder.degLex K0 j =
    actualCanonicalDerivativeExponent MonomialOrder.degLex K1 (actualEssentialRelabel hV j) at hβ
  unfold actualInheritedEssentialDerivative
  rw [← hβ, ← hvertex, actualInheritedRelabelFamily_germ]

private theorem block_derivative_relabel (G : ActualAnalyticInheritedFamily n 0 K0)
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (k : ℕ) (j : actualDegreePrefixVariables MonomialOrder.degLex K0 k) :
    actualInheritedEssentialDerivative (actualInheritedRelabelFamily G hV)
        (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K1 k (actualPrefixRelabel hV k j)) =
      actualInheritedEssentialDerivative G (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K0 k j) := by
  have he : actualCanonicalBlockEssentialVariable MonomialOrder.degLex K1 k (actualPrefixRelabel hV k j) =
      actualEssentialRelabel hV (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K0 k j) :=
    Subtype.ext rfl
  rw [he]
  exact actualInheritedRelabelFamily_selected_derivative G hV _

theorem actualInheritedRelabelFamily_prefix_reduced
    (G : ActualAnalyticInheritedFamily n 0 K0)
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (k : ℕ) (hred : ActualInheritedPrefixReducedAt G k) :
    ActualInheritedPrefixReducedAt (actualInheritedRelabelFamily G hV) k := by
  intro a ha b hb α hbα
  exact hred ((actualVertexRelabel hV).symm a) ha ((actualVertexRelabel hV).symm b) hb α hbα

theorem actualInheritedRelabelFamily_normal_powers
    (G : ActualAnalyticInheritedFamily n 0 K0)
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (A : Set (Fin n))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal A ^ normalExponentDegree a.val) :
    ∀ a, (actualInheritedRelabelFamily G hV).germs a ∈
      actualAnalyticCoordinateIdeal A ^ normalExponentDegree a.val := by
  intro a
  exact hpower ((actualVertexRelabel hV).symm a)

theorem actualInheritedRelabelFamily_contact
    (G : ActualAnalyticInheritedFamily n 0 K0)
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (k : ℕ) (hadapt : ActualInheritedContactAt G k) :
    ActualInheritedContactAt (actualInheritedRelabelFamily G hV) k := by
  intro j
  let j0 := (actualPrefixRelabel hV k).symm j
  have hj : actualPrefixRelabel hV k j0 = j := (actualPrefixRelabel hV k).apply_symm_apply j
  have hd := block_derivative_relabel G hV k j0
  rw [hj] at hd
  rw [hd]
  have hi : actualAnalyticCoordinateBlockIdeal (actualDegreePrefixVariables MonomialOrder.degLex K0 k) =
      actualAnalyticCoordinateBlockIdeal (actualDegreePrefixVariables MonomialOrder.degLex K1 k) :=
    congrArg actualAnalyticCoordinateBlockIdeal (actualPrefixVariables_eq_of_vertices_eq hV k)
  exact hi ▸ hadapt j0

/-- The TRUE analytic matrices agree after the literal simultaneous relabeling. -/
theorem actualInheritedRelabelFamily_jacobian
    (G : ActualAnalyticInheritedFamily n 0 K0)
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (k : ℕ) :
    (actualInheritedBlockJacobian (actualInheritedRelabelFamily G hV) k).submatrix
        (actualPrefixRelabel hV k) (actualPrefixRelabel hV k) = actualInheritedBlockJacobian G k := by
  ext j i
  change HolGerm.eval (actualAnalyticCoordinateDerivative i.val
    (actualInheritedEssentialDerivative (actualInheritedRelabelFamily G hV)
      (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K1 k (actualPrefixRelabel hV k j)))) = _
  rw [block_derivative_relabel]
  rfl

theorem actualInheritedRelabelFamily_jacobian_det
    (G : ActualAnalyticInheritedFamily n 0 K0)
    (hV : actualInitialVertices MonomialOrder.degLex K0 = actualInitialVertices MonomialOrder.degLex K1)
    (k : ℕ) :
    (actualInheritedBlockJacobian (actualInheritedRelabelFamily G hV) k).det =
      (actualInheritedBlockJacobian G k).det := by
  rw [← Matrix.det_submatrix_equiv_self (actualPrefixRelabel hV k),
    actualInheritedRelabelFamily_jacobian]

/-- This is the CURRENT Taylor ideal, with no claim that its members lie in K0. -/
def actualInheritedCurrentSourceIdeal (J : Ideal (HolGerm (ComplexModel n))) :
    Ideal (MvPowerSeries (Fin n) ℂ) := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom J

/-- The initial flag's whole SOURCE diagram equality determines the literal
current family internally, rather than supplying it as a target certificate. -/
def actualCurrentSourceInheritedFamily (G : ActualAnalyticInheritedFamily n 0 K0)
    (J : Ideal (HolGerm (ComplexModel n)))
    (hD : actualInitialDiagram MonomialOrder.degLex (actualInheritedCurrentSourceIdeal J) =
      actualInitialDiagram MonomialOrder.degLex K0) :
    ActualAnalyticInheritedFamily n 0 (actualInheritedCurrentSourceIdeal J) :=
  actualInheritedRelabelFamily G (actualInitialVertices_eq_of_diagram_eq hD.symm)

theorem actualCurrentSourceInheritedFamily_span (G : ActualAnalyticInheritedFamily n 0 K0)
    (J : Ideal (HolGerm (ComplexModel n))) (hspan : Ideal.span (range G.germs) = J)
    (hD : actualInitialDiagram MonomialOrder.degLex (actualInheritedCurrentSourceIdeal J) =
      actualInitialDiagram MonomialOrder.degLex K0) :
    Ideal.span (range (actualCurrentSourceInheritedFamily G J hD).germs) = J := by
  rw [actualCurrentSourceInheritedFamily, actualInheritedRelabelFamily_range, hspan]

/-- Membership is produced from the real analytic span generator and actual
Taylor ideal map; no old-ideal membership certificate is assumed. -/
theorem actualCurrentSourceInheritedFamily_mem (G : ActualAnalyticInheritedFamily n 0 K0)
    (J : Ideal (HolGerm (ComplexModel n))) (hspan : Ideal.span (range G.germs) = J)
    (hD : actualInitialDiagram MonomialOrder.degLex (actualInheritedCurrentSourceIdeal J) =
      actualInitialDiagram MonomialOrder.degLex K0) :
    ∀ a, actualUnshiftedTaylorAlgHom n ((actualCurrentSourceInheritedFamily G J hD).germs a) ∈
      actualInheritedCurrentSourceIdeal J := by
  intro a
  have hm : (actualCurrentSourceInheritedFamily G J hD).germs a ∈ J :=
    (le_of_eq (actualCurrentSourceInheritedFamily_span G J hspan hD))
      (Ideal.subset_span ⟨a, rfl⟩)
  exact Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom hm

/-- The CURRENT-family direction theorem is really applied here. Whole source
span/diagram outputs of the actual flag suffice; genuine membership is internal. -/
theorem actual_normal_hs_equal_inherited_flag_chart_conditions_of_current_span
    (G : ActualAnalyticInheritedFamily n 0 K0)
    (J : Ideal (HolGerm (ComplexModel n))) (hspan : Ideal.span (range G.germs) = J)
    (hD : actualInitialDiagram MonomialOrder.degLex (actualInheritedCurrentSourceIdeal J) =
      actualInitialDiagram MonomialOrder.degLex K0)
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal A ^ normalExponentDegree a.val)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀ k, ActualInheritedContactAt G k)
    (hHS : ∀ q : ℕ, genuineFormalHilbertSamuelValue n
        (actualFormalStrictTransform (actualInheritedCurrentSourceIdeal J) A e he b) q =
      genuineFormalHilbertSamuelValue n (actualInheritedCurrentSourceIdeal J) q) :
    ∀ k : ℕ, actualDegreePrefixVariables MonomialOrder.degLex K0 k ⊆ A \ {e} ∧
      ∀ i ∈ actualDegreePrefixVariables MonomialOrder.degLex K0 k, b i = 0 := by
  let hV := actualInitialVertices_eq_of_diagram_eq hD.symm
  let Gcurrent := actualCurrentSourceInheritedFamily G J hD
  have hmem := actualCurrentSourceInheritedFamily_mem G J hspan hD
  have hp := actualInheritedRelabelFamily_normal_powers G hV A hpower
  have hr := fun k => actualInheritedRelabelFamily_prefix_reduced G hV k (hred k)
  have ha := fun k => actualInheritedRelabelFamily_contact G hV k (hadapt k)
  have hlegal := actual_normal_hs_equal_inherited_flag_chart_conditions Gcurrent hmem A e he b hp hr ha hHS
  intro k
  have hblocks := actualPrefixVariables_eq_of_vertices_eq hV k
  simpa only [← hblocks] using hlegal k

end

end Hironaka.HironakaActualInheritedCurrentSourceRelabel
