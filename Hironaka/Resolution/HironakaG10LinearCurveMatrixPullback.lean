import Hironaka.Resolution.HironakaG10CurveChartQuotient

/-! Actual linear base change of a finite holomorphic complex, its whole
one-row entry ideal and its unchanged actual special fibre. -/

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace Hironaka.HironakaG10LinearCurveMatrixPullback
noncomputable section
open HolGerm OkaRelationSheaf OkaGermBridge
  HironakaRelativeNormalIdeal HironakaRelativeNormalFibreHilbertSamuel
  HironakaActualAnalyticBaseChangeCoefficients HironakaActualCentreJointJets
  HironakaHolomorphicJetChartInvariance HironakaG10CurveChartQuotient
  HironakaG10LocFibreOpen HironakaG10FlatSliceResolution HironakaG10FlatResolutionStart

def linearJointMap (d t : ℕ) (L : ComplexModel 1 →L[ℂ] ComplexModel d) :
    ComplexModel (1 + t) →L[ℂ] ComplexModel (d + t) :=
  (tangentInclusion d t).comp (L.comp (tangentProjection 1 t)) +
    (actualJointNormalInclusion d t).comp (actualJointNormalProjection 1 t)

theorem linearJointMap_apply (d t : ℕ) (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (w : ComplexModel (1 + t)) :
    linearJointMap d t L w = jointBaseMap d 1 t L w := rfl

def curveFamily {a b : ℕ} (d t : ℕ) (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ) :
    Fin a → Fin b → ComplexModel (1 + t) → ℂ :=
  fun i j w => F i j (jointBaseMap d 1 t L w)

def entryIdeal {b : ℕ} (d t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel (d + t) → ℂ) :
    Ideal (HolGerm (ComplexModel (d + t))) :=
  Ideal.span (Set.range fun j => germAt 0 (F 0 j))

def curveProductFamily {a b : ℕ} (d t : ℕ) (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ) :
    Fin a → Fin b → ℂ × ComplexModel t → ℂ :=
  productFamily t (curveFamily d t L F)

theorem holAt_curveFamily {a b : ℕ} (d t : ℕ)
    (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    ∀ i j, HolAt (curveFamily d t L F i j) 0 :=
  fun i j => eventually_differentiableAt_comp_clm (linearJointMap d t L) (hF i j)

theorem holAt_curveProductFamily {a b : ℕ} (d t : ℕ)
    (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    ∀ i j, HolAt (curveProductFamily d t L F i j) 0 :=
  holAt_productFamily t _ (holAt_curveFamily d t L F hF)

theorem jointBasePullback_germAt (d t : ℕ)
    (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (f : ComplexModel (d + t) → ℂ) (hf : HolAt f 0) :
    jointBasePullback d 1 t L (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero
      (germAt 0 f) = germAt 0 (fun w => f (jointBaseMap d 1 t L w)) := by
  have hfp : HolAt (fun w => f (jointBaseMap d 1 t L w)) 0 :=
    eventually_differentiableAt_comp_clm (linearJointMap d t L) hf
  rw [germAt_of_holAt hf, germAt_of_holAt hfp]
  unfold jointBasePullback
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun w => by simp

theorem map_entryIdeal_eq_native {b : ℕ} (d t : ℕ)
    (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (F : Fin 1 → Fin b → ComplexModel (d + t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    Ideal.map (jointBasePullback d 1 t L
      (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero).toRingHom
        (entryIdeal d t F) = nativeEntryIdeal t (curveFamily d t L F) := by
  unfold entryIdeal nativeEntryIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  exact jointBasePullback_germAt d t L (F 0 j) (hF 0 j)

theorem zero_comp_curveProductFamily {a b c : ℕ} (d t : ℕ)
    (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ)
    (G : Fin b → Fin c → ComplexModel (d + t) → ℂ)
    (hcomp : ∀ i k, ∀ᶠ x in 𝓝 (0 : ComplexModel (d + t)),
      ∑ j, F i j x * G j k x = 0) :
    ∀ i k, ∀ᶠ x in 𝓝 ((0 : ℂ), (0 : ComplexModel t)),
      ∑ j, curveProductFamily d t L F i j x * curveProductFamily d t L G j k x = 0 := by
  intro i k
  have hlin : Tendsto (linearJointMap d t L) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (linearJointMap d t L).continuous.tendsto 0
  have hprod : Tendsto (productModelEquiv t).symm (𝓝 (0 : ℂ × ComplexModel t)) (𝓝 0) := by
    simpa only [map_zero] using (productModelEquiv t).symm.continuous.tendsto 0
  exact hprod.eventually (hlin.eventually (hcomp i k))

theorem productModelEquiv_normalInclusion (t : ℕ) (z : ComplexModel t) :
    productModelEquiv t (actualJointNormalInclusion 1 t z) = (0, z) := by
  apply Prod.ext
  · rw [productModelEquiv_fst, tangentProjection_actualJointNormalInclusion, map_zero]
  · ext i
    simp [productModelEquiv, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      LinearIsometryEquiv.piLpCongrLeft_apply, actualJointNormalInclusion_normal]

theorem productModelEquiv_symm_zero (t : ℕ) (z : ComplexModel t) :
    (productModelEquiv t).symm (0, z) = actualJointNormalInclusion 1 t z := by
  apply (productModelEquiv t).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, productModelEquiv_normalInclusion]

theorem jointBaseMap_normalInclusion (d t : ℕ)
    (L : ComplexModel 1 →L[ℂ] ComplexModel d) (z : ComplexModel t) :
    jointBaseMap d 1 t L (actualJointNormalInclusion 1 t z) =
      actualJointNormalInclusion d t z := by
  simp only [jointBaseMap, tangentProjection_actualJointNormalInclusion, map_zero,
    actualJointNormalProjection_inclusion, zero_add]

theorem sliceZero_curveProductFamily {a b : ℕ} (d t : ℕ)
    (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ) :
    sliceZero (curveProductFamily d t L F) =
      (fun i j z => F i j (actualJointNormalInclusion d t z)) := by
  funext i j z
  change F i j (jointBaseMap d 1 t L ((productModelEquiv t).symm (0, z))) = _
  rw [productModelEquiv_symm_zero, jointBaseMap_normalInclusion]

theorem fibre_exact_curveProductFamily {a b c : ℕ} (d t : ℕ)
    (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ)
    (G : Fin b → Fin c → ComplexModel (d + t) → ℂ)
    (hfib : ∀ v : Fin b → ComplexModel t → ℂ,
      IsRelationAt (fun i j z => F i j (actualJointNormalInclusion d t z)) 0 v →
        IsCombinationAt (columns (fun j k z => G j k (actualJointNormalInclusion d t z))) 0 v) :
    ∀ v : Fin b → ComplexModel t → ℂ,
      IsRelationAt (sliceZero (curveProductFamily d t L F)) 0 v →
        IsCombinationAt (columns (sliceZero (curveProductFamily d t L G))) 0 v := by
  simpa only [sliceZero_curveProductFamily] using hfib

end
end Hironaka.HironakaG10LinearCurveMatrixPullback
