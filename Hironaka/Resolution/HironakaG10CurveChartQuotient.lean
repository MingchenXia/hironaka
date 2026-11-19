import Hironaka.Resolution.HironakaG10HirChartFlattener
import Hironaka.Resolution.HironakaG10OneParameterQuotientFlatness
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The actual one-parameter native chart map, transported to product coordinates,
with its whole ideal and literal first-projection scalar action. -/

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace Hironaka.HironakaG10CurveChartQuotient
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaG10HirChartFlattener
  HironakaG10OneParameterCokernelFlatness HironakaG10OneParameterQuotientFlatness
  OkaRelationSheaf OkaGermBridge HironakaG10FlatSliceResolution

def baseModelEquiv : ComplexModel 1 ≃L[ℂ] ℂ :=
  PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => ℂ)

/-- The actual split into the single base coordinate and all original normal coordinates. -/
def productModelEquiv (t : ℕ) : ComplexModel (1 + t) ≃L[ℂ] ℂ × ComplexModel t :=
  EuclideanSpace.finAddEquivProd.toContinuousLinearEquiv.trans
    (baseModelEquiv.prodCongr (ContinuousLinearEquiv.refl ℂ (ComplexModel t)))

theorem productModelEquiv_fst (t : ℕ) (w : ComplexModel (1 + t)) :
    (productModelEquiv t w).1 = baseModelEquiv (tangentProjection 1 t w) := by
  congr 1

theorem tangentProjection_productModelEquiv_symm (t : ℕ) (w : ℂ × ComplexModel t) :
    tangentProjection 1 t ((productModelEquiv t).symm w) = baseModelEquiv.symm w.1 := by
  apply baseModelEquiv.injective
  rw [← productModelEquiv_fst, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]

def baseGermEquiv : HolGerm (ComplexModel 1) ≃+* HolGerm ℂ :=
  HolGerm.comapEquiv baseModelEquiv.symm

def ambientGermEquiv (t : ℕ) :
    HolGerm (ComplexModel (1 + t)) ≃+* HolGerm (ℂ × ComplexModel t) :=
  HolGerm.comapEquiv (productModelEquiv t).symm

/-- The full germ scalar square, not just the equality of coordinate germs. -/
theorem ambientGermEquiv_tangentPullback (t : ℕ) (a : HolGerm (ComplexModel 1)) :
    ambientGermEquiv t (tangentPullback 1 t a) =
      basePullback (ComplexModel t) (baseGermEquiv a) := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    change HolGerm.mk (fun w => f (tangentProjection 1 t ((productModelEquiv t).symm w)))
      (eventually_differentiableAt_comp_clm
        ((tangentProjection 1 t).comp (productModelEquiv t).symm.toContinuousLinearMap) hf) =
      HolGerm.mk (fun w => f (baseModelEquiv.symm w.1))
        (eventually_differentiableAt_comp_clm
          (baseModelEquiv.symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.fst ℂ ℂ (ComplexModel t))) hf)
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun w => congrArg f (tangentProjection_productModelEquiv_symm t w)

def productIdeal (t : ℕ) (I : Ideal (HolGerm (ComplexModel (1 + t)))) :
    Ideal (HolGerm (ℂ × ComplexModel t)) := Ideal.map (ambientGermEquiv t).toRingHom I

def quotientProductEquiv (t : ℕ) (I : Ideal (HolGerm (ComplexModel (1 + t)))) :
    HolGerm (ComplexModel (1 + t)) ⧸ I ≃+*
      HolGerm (ℂ × ComplexModel t) ⧸ productIdeal t I :=
  Ideal.quotientEquiv I (productIdeal t I) (ambientGermEquiv t) rfl

def productStructureMap (t : ℕ) (I : Ideal (HolGerm (ComplexModel (1 + t)))) :
    HolGerm ℂ →+* HolGerm (ℂ × ComplexModel t) ⧸ productIdeal t I :=
  (Ideal.Quotient.mk (productIdeal t I)).comp (basePullback (ComplexModel t))

theorem quotientProductEquiv_chartMap (t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (1 + t)))) :
    (quotientProductEquiv t I).toRingHom.comp (chartMap 1 t I) =
      (productStructureMap t I).comp baseGermEquiv.toRingHom := by
  ext a
  change Ideal.Quotient.mk (productIdeal t I) (ambientGermEquiv t (tangentPullback 1 t a)) =
    Ideal.Quotient.mk (productIdeal t I) (basePullback (ComplexModel t) (baseGermEquiv a))
  rw [ambientGermEquiv_tangentPullback]

/-- Flatness is transported with both of the actual scalar maps and the whole ideal. -/
theorem chartMap_flat_iff_product (t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (1 + t)))) :
    (chartMap 1 t I).Flat ↔ (productStructureMap t I).Flat := by
  calc
    (chartMap 1 t I).Flat ↔
        ((quotientProductEquiv t I).toRingHom.comp (chartMap 1 t I)).Flat :=
      (RingHom.Flat.comp_iff_of_bijective_left (quotientProductEquiv t I).bijective).symm
    _ ↔ ((productStructureMap t I).comp baseGermEquiv.toRingHom).Flat :=
      Iff.of_eq (congrArg RingHom.Flat (quotientProductEquiv_chartMap t I))
    _ ↔ (productStructureMap t I).Flat :=
      RingHom.Flat.comp_iff_of_bijective_right baseGermEquiv.bijective

def productFamily {a b : ℕ} (t : ℕ)
    (F : Fin a → Fin b → ComplexModel (1 + t) → ℂ) :
    Fin a → Fin b → ℂ × ComplexModel t → ℂ :=
  fun i j w => F i j ((productModelEquiv t).symm w)

def nativeEntryIdeal {b : ℕ} (t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel (1 + t) → ℂ) :
    Ideal (HolGerm (ComplexModel (1 + t))) :=
  Ideal.span (Set.range fun j => germAt 0 (F 0 j))

theorem holAt_productFamily {a b : ℕ} (t : ℕ)
    (F : Fin a → Fin b → ComplexModel (1 + t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    ∀ i j, HolAt (productFamily t F i j) 0 :=
  fun i j => eventually_differentiableAt_comp_clm
    (productModelEquiv t).symm.toContinuousLinearMap (hF i j)

theorem ambientGermEquiv_germAt (t : ℕ) (f : ComplexModel (1 + t) → ℂ)
    (hf : HolAt f 0) :
    ambientGermEquiv t (germAt 0 f) =
      germAt 0 (fun w => f ((productModelEquiv t).symm w)) := by
  have hfp : HolAt (fun w => f ((productModelEquiv t).symm w)) 0 :=
    eventually_differentiableAt_comp_clm (productModelEquiv t).symm.toContinuousLinearMap hf
  rw [germAt_of_holAt hf, germAt_of_holAt hfp]
  change HolGerm.mk (fun w => f (0 + (productModelEquiv t).symm w))
    (eventually_differentiableAt_comp_clm
      (productModelEquiv t).symm.toContinuousLinearMap hf.translate) =
      HolGerm.mk (fun w => f ((productModelEquiv t).symm (0 + w))) hfp.translate
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun w => by simp

theorem productIdeal_nativeEntryIdeal {b : ℕ} (t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel (1 + t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    productIdeal t (nativeEntryIdeal t F) = entryIdeal (productFamily t F) 0 := by
  unfold productIdeal nativeEntryIdeal entryIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  exact ambientGermEquiv_germAt t (F 0 j) (hF 0 j)

/-- The actual native chart flatness conclusion from the one-parameter regularity criterion. -/
theorem chartMap_nativeEntryIdeal_flat_of_regularAt {b : ℕ} (t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel (1 + t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0)
    (hreg : RegularAt (productFamily t F) (fun x => x.1) ((0 : ℂ), (0 : ComplexModel t))) :
    (chartMap 1 t (nativeEntryIdeal t F)).Flat := by
  have h := quotientStructureMap_flat_of_regularAt (productFamily t F) 0
    (holAt_productFamily t F hF) hreg
  let e := Ideal.quotientEquiv (nativeEntryIdeal t F) (entryIdeal (productFamily t F) 0)
    (ambientGermEquiv t) (productIdeal_nativeEntryIdeal t F hF).symm
  have he : e.toRingHom.comp (chartMap 1 t (nativeEntryIdeal t F)) =
      (HironakaG10OneParameterQuotientFlatness.quotientStructureMap (productFamily t F) 0).comp
        baseGermEquiv.toRingHom := by
    ext a
    change Ideal.Quotient.mk (entryIdeal (productFamily t F) 0)
      (ambientGermEquiv t (tangentPullback 1 t a)) =
        Ideal.Quotient.mk (entryIdeal (productFamily t F) 0)
          (basePullback (ComplexModel t) (baseGermEquiv a))
    rw [ambientGermEquiv_tangentPullback]
  apply (RingHom.Flat.comp_iff_of_bijective_left e.bijective).mp
  exact (Iff.of_eq (congrArg RingHom.Flat he)).mpr
    (RingHom.Flat.comp (.of_bijective baseGermEquiv.bijective) h)

end
end Hironaka.HironakaG10CurveChartQuotient
