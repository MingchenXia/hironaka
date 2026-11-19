import Hironaka.Resolution.HironakaChowFibreSupportedUniqueness
import Hironaka.Resolution.HironakaChowFibreSupportModules
import Mathlib.LinearAlgebra.Isomorphisms

/-! Native A-linear supported reassembly/inverse/remainder for the SAME
ORIGINAL lifted fibre family, then WHOLE original quotient S/I = N/R(I).
No entire-lift-ideal direct sum or flatness certificate is assumed.
Blueprint FIRST: hironaka-g10-fibre-division-remainder.tex. -/
set_option autoImplicit false
namespace Hironaka.HironakaChowFibreDivisionRemainder
noncomputable section
open Set Classical HolGerm HironakaRelativeNormalIdeal
  HironakaActualJointBaseFibre HironakaActualWeightedVertexSmallTails
  HironakaChowFibreLiftUniformTails HironakaChowOriginalFibreSupportedDivision
  HironakaChowFibreSupportedUniqueness HironakaChowFibreSupportModules
  HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition
  HironakaActualCoefficientPresentationCentrePower

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/-- The ORIGINAL multiplication/sum/inclusions on native supported modules. -/
def supportedReassembly (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I) :
    fibreDivisionModule d t I →ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)) where
  toFun z := (∑ j, (z.1 j : HolGerm (ComplexModel (d+t))) *
    P.lift (fibreEnumeration d t I j)) + (z.2 : HolGerm (ComplexModel (d+t)))
  map_add' z z' := by
    change (∑ j, ((z.1 j : HolGerm (ComplexModel (d+t))) + (z'.1 j : HolGerm (ComplexModel (d+t)))) *
      P.lift (fibreEnumeration d t I j)) +
      ((z.2 : HolGerm (ComplexModel (d+t))) + (z'.2 : HolGerm (ComplexModel (d+t)))) = _
    simp only [add_mul,Finset.sum_add_distrib]
    ring
  map_smul' a z := by
    change (∑ j, (tangentPullback d t a * (z.1 j : HolGerm (ComplexModel (d+t)))) *
      P.lift (fibreEnumeration d t I j)) + tangentPullback d t a * (z.2 : HolGerm (ComplexModel (d+t))) =
      tangentPullback d t a * ((∑ j, (z.1 j : HolGerm (ComplexModel (d+t))) *
        P.lift (fibreEnumeration d t I j)) + (z.2 : HolGerm (ComplexModel (d+t))))
    rw [mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- ORIGINAL I internally chooses the family and actual native base-linear division. -/
theorem exists_original_fibre_linear_division (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ (P : FibreLiftUniformTailData d t I)
      (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t))),
      ∀ z, e z = supportedReassembly d t I P z := by
  obtain ⟨P,hP⟩ := exists_original_fibre_unique_division d t I
  let f := supportedReassembly d t I P
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨z,hz,_⟩ := hP g
    let q : ∀ j, fibreQuotientModule d t I j := fun j =>
      ⟨z.1 j,(mem_fibreQuotientModule_iff d t I j (z.1 j)).mpr (hz.2.1 j)⟩
    let r : fibreRemainderModule d t I :=
      ⟨z.2,(mem_fibreRemainderModule_iff d t I z.2).mpr hz.2.2⟩
    exact ⟨(q,r),hz.1.symm⟩
  have hinj : Function.Injective f := by
    intro z z' he
    let p := ((fun j => (z.1 j : HolGerm (ComplexModel (d+t)))),
      (z.2 : HolGerm (ComplexModel (d+t))))
    let p' := ((fun j => (z'.1 j : HolGerm (ComplexModel (d+t)))),
      (z'.2 : HolGerm (ComplexModel (d+t))))
    have hp : f z = (∑ j, p.1 j * P.lift (fibreEnumeration d t I j)) + p.2 ∧
        (∀ j β, ¬ AvoidsCones ((List.ofFn (fibreHeadWords d t I)).take j.val)
          (β + wordExponent (fibreHeadWords d t I j)) →
          MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (p.1 j)) = 0) ∧
        ∀ β, ¬ AvoidsCones (List.ofFn (fibreHeadWords d t I)) β →
          MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) p.2) = 0 :=
      ⟨rfl,fun j => (mem_fibreQuotientModule_iff d t I j _).mp (z.1 j).property,
        (mem_fibreRemainderModule_iff d t I _).mp z.2.property⟩
    have hp' : f z = (∑ j, p'.1 j * P.lift (fibreEnumeration d t I j)) + p'.2 ∧
        (∀ j β, ¬ AvoidsCones ((List.ofFn (fibreHeadWords d t I)).take j.val)
          (β + wordExponent (fibreHeadWords d t I j)) →
          MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (p'.1 j)) = 0) ∧
        ∀ β, ¬ AvoidsCones (List.ofFn (fibreHeadWords d t I)) β →
          MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) p'.2) = 0 :=
      ⟨he,fun j => (mem_fibreQuotientModule_iff d t I j _).mp (z'.1 j).property,
        (mem_fibreRemainderModule_iff d t I _).mp z'.2.property⟩
    have hu : p = p' := (hP (f z)).unique hp hp'
    apply Prod.ext
    · funext j
      apply Subtype.ext
      exact congrFun (congrArg Prod.fst hu) j
    · apply Subtype.ext
      exact congrArg Prod.snd hu
  exact ⟨P,LinearEquiv.ofBijective f ⟨hinj,hsurj⟩,fun _ => rfl⟩

/-- Actual second projection of the native inverse, with no copied scalar action. -/
def divisionRemainder (I : Ideal (HolGerm (ComplexModel (d+t))))
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t))) :
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)] fibreRemainderModule d t I :=
  (LinearMap.snd (HolGerm (ComplexModel d)) (∀ j, fibreQuotientModule d t I j)
    (fibreRemainderModule d t I)).comp e.symm.toLinearMap

/-- WHOLE original ideal image in the SAME actual remainder module. -/
def idealRemainder (I : Ideal (HolGerm (ComplexModel (d+t))))
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t))) :
    Submodule (HolGerm (ComplexModel d)) (fibreRemainderModule d t I) :=
  (I.restrictScalars (HolGerm (ComplexModel d))).map (divisionRemainder d t I e)

private theorem remainder_retract (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (n : fibreRemainderModule d t I) : divisionRemainder d t I e n = n := by
  have hn : e (0,n) = (n : HolGerm (ComplexModel (d+t))) := by
    rw [he]
    change (∑ j, (0 : HolGerm (ComplexModel (d+t))) * P.lift (fibreEnumeration d t I j)) +
      (n : HolGerm (ComplexModel (d+t))) = _
    simp only [zero_mul,Finset.sum_const_zero,zero_add]
  have hi := e.symm_apply_apply (0,n)
  rw [hn] at hi
  exact congrArg Prod.snd hi

private theorem kernel_remainder_le (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z) :
    LinearMap.ker (divisionRemainder d t I e) ≤ I.restrictScalars (HolGerm (ComplexModel d)) := by
  intro g hg
  have hr : ((e.symm g).2 : HolGerm (ComplexModel (d+t))) = 0 := by
    change divisionRemainder d t I e g = 0 at hg
    exact congrArg (fun n : fibreRemainderModule d t I => (n : HolGerm (ComplexModel (d+t)))) hg
  have hEq := he (e.symm g)
  rw [e.apply_symm_apply] at hEq
  change g = (∑ j, ((e.symm g).1 j : HolGerm (ComplexModel (d+t))) *
    P.lift (fibreEnumeration d t I j)) + ((e.symm g).2 : HolGerm (ComplexModel (d+t))) at hEq
  rw [hr,add_zero] at hEq
  change g ∈ I
  rw [hEq]
  apply I.sum_mem
  intro j _
  exact I.mul_mem_left _ (P.member_trace (fibreEnumeration d t I j)).1

/-- Actual WHOLE original quotient equals native remainder quotient; all data produced internally. -/
theorem exists_original_ideal_remainder_quotient (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ (P : FibreLiftUniformTailData d t I)
      (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t))),
      (∀ z, e z = supportedReassembly d t I P z) ∧
      (∀ n : fibreRemainderModule d t I, divisionRemainder d t I e n = n) ∧
      LinearMap.ker (divisionRemainder d t I e) ≤ I.restrictScalars (HolGerm (ComplexModel d)) ∧
      Nonempty ((HolGerm (ComplexModel (d+t)) ⧸ I.restrictScalars (HolGerm (ComplexModel d))) ≃ₗ[HolGerm (ComplexModel d)]
        ((fibreRemainderModule d t I) ⧸ idealRemainder d t I e)) := by
  obtain ⟨P,e,he⟩ := exists_original_fibre_linear_division d t I
  let R := divisionRemainder d t I e
  let K := idealRemainder d t I e
  let J := I.restrictScalars (HolGerm (ComplexModel d))
  have hr := remainder_retract d t I P e he
  have hk := kernel_remainder_le d t I P e he
  let f := K.mkQ.comp R
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨n,rfl⟩ := K.mkQ_surjective b
    refine ⟨(n : HolGerm (ComplexModel (d+t))),?_⟩
    change K.mkQ (R n) = K.mkQ n
    rw [hr]
  have hker : LinearMap.ker f = J := by
    ext g
    change (Submodule.Quotient.mk (R g) : (fibreRemainderModule d t I) ⧸ K) = 0 ↔ g ∈ J
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨i,hi,hRi⟩
      have hd : g-i ∈ LinearMap.ker R := by
        change R (g-i) = 0
        rw [map_sub,← hRi,sub_self]
      simpa only [sub_add_cancel] using J.add_mem (hk hd) hi
    · intro hg
      exact ⟨g,hg,rfl⟩
  let q := (Submodule.quotEquivOfEq J (LinearMap.ker f) hker.symm).trans
    (f.quotKerEquivOfSurjective hf)
  exact ⟨P,e,he,hr,hk,⟨q⟩⟩

end
end Hironaka.HironakaChowFibreDivisionRemainder
