import DeJongAlterations.Algebra.NodeFieldSeriesJetScalar
import DeJongAlterations.Algebra.NodeFieldCubicRelation
import DeJongAlterations.Algebra.NodeFieldUVJetScalarRelation
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Build the actual geometric cubic-jet evaluation from genuine finite scalar quotients. -/

noncomputable section

open IsLocalRing TensorProduct

namespace DeJongAlterations.Algebra.NodeFieldGeometricCubicMap

open NodeFormalMorse NodeVariableMorse NodeGeometricCompletionFormalUV

universe u v w
variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
  (C : Type w) [CommRing C] [IsLocalRing C] [Algebra K C]
  (φ : Series K →ₐ[K] C)
  (hV : (variableIdeal K).map φ.toRingHom = maximalIdeal C)
  (e : L ⊗[K] (C ⧸ maximalIdeal C ^ 3) ≃ₐ[L]
    (FormalUV L ⧸ maximalIdeal (FormalUV L) ^ 3))

def evaluation : Series L →ₐ[L] NodeFieldUVJetTangent.Jet L :=
  (NodeFieldUVJetBasis.nativeJetEquiv L 3).toAlgHom.comp
    (e.toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id L L) (NodeFieldCubicRelation.cubicMap K C φ hV)).comp
        ((NodeFieldSeriesJetScalar.scalarEquiv K L 3).symm.toAlgHom.comp
          (Ideal.Quotient.mkₐ L (variableIdeal L ^ 3)))))

theorem evaluation_surjective (hφ : Function.Surjective φ) :
    Function.Surjective (evaluation K L C φ hV e) := by
  apply (NodeFieldUVJetBasis.nativeJetEquiv L 3).surjective.comp
  apply e.surjective.comp
  apply (Algebra.TensorProduct.map_surjective
    (f := AlgHom.id L L) (g := NodeFieldCubicRelation.cubicMap K C φ hV)
    Function.surjective_id (NodeFieldCubicRelation.cubicMap_surjective K C φ hV hφ)).comp
  exact (NodeFieldSeriesJetScalar.scalarEquiv K L 3).symm.surjective.comp
    Ideal.Quotient.mk_surjective

theorem evaluation_map (F : Series K) :
    evaluation K L C φ hV e (MvPowerSeries.map (algebraMap K L) F) =
      NodeFieldUVJetBasis.nativeJetEquiv L 3
        (e (1 ⊗ₜ[K] Ideal.Quotient.mk _ (φ F))) := by
  have h : NodeFieldSeriesJetScalar.scalarEquiv K L 3
      (1 ⊗ₜ[K] Ideal.Quotient.mk _ F) =
      Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap K L) F) := by
    simpa only [one_smul] using NodeFieldSeriesJetScalar.scalarEquiv_tmul_mk K L 3 1 F
  change NodeFieldUVJetBasis.nativeJetEquiv L 3
    (e (Algebra.TensorProduct.map (AlgHom.id L L) (NodeFieldCubicRelation.cubicMap K C φ hV)
      ((NodeFieldSeriesJetScalar.scalarEquiv K L 3).symm
        (Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap K L) F))))) = _
  rw [← h, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
  rfl

include L hV e in
theorem relation_discriminant_ne_zero (hφ : Function.Surjective φ) (F : Series K)
    (hF : φ F = 0) (hF2 : F ∈ variableIdeal K ^ 2) (hF3 : F ∉ variableIdeal K ^ 3) :
    jetDiscriminant F ≠ 0 := by
  apply NodeFieldUVJetScalarRelation.original_discriminant_ne_zero
    (algebraMap K L) F hF2 hF3 (evaluation K L C φ hV e)
    (evaluation_surjective K L C φ hV e hφ)
  rw [evaluation_map, hF, map_zero, tmul_zero, map_zero, map_zero]

end DeJongAlterations.Algebra.NodeFieldGeometricCubicMap
