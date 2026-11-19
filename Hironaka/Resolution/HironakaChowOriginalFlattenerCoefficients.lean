import Hironaka.Resolution.HironakaChowOriginalRemainderInfinitesimal
import Hironaka.Resolution.HironakaChowNormalSupportQuotientFlatness
import Hironaka.Resolution.HironakaChowBaseIdealNormalCoefficients
import Hironaka.Analytic.HolomorphicGermNoetherian

/-! WHOLE original analytic coefficient ideal and quotient-base flatness.
The original ideal internally yields SAME remainder data before ALL base
quotients; arbitrary analytic base-map universality remains separate.
Blueprint first: hironaka-g10-original-flattener-coefficients.tex. -/
set_option autoImplicit false
namespace Hironaka.HironakaChowOriginalFlattenerCoefficients
noncomputable section
open Set Classical HolGerm HironakaRelativeNormalIdeal
  HironakaActualRelativeCoefficientGerms HironakaChowFibreSupportModules
  HironakaChowFibreDivisionRemainder HironakaChowNormalSupportProjection
  HironakaChowNormalSupportBaseChange HironakaChowBaseIdealNormalCoefficients
  HironakaChowOriginalFibreSupportedDivision HironakaChowFibreLiftUniformTails
  HironakaChowOriginalRemainderInfinitesimal HironakaChowNormalSupportQuotientFlatness

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/- Pin the SAME existing native quotient factories as the imported167
mother; no scalar operation is copied or quotient dictionary supplied. -/
local instance (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : Ideal (HolGerm (ComplexModel d))) :
    Module (HolGerm (ComplexModel d) ⧸ a)
      (normalSupportQuotient d t (assignedRemainderNormalMask (fibreHeadWords d t I)) a) :=
  (Module.isTorsionBySet_quotient_ideal_smul (fibreRemainderModule d t I) a).module

local instance (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : Ideal (HolGerm (ComplexModel d))) :
    SMul (Ideal (HolGerm (ComplexModel d) ⧸ a))
      (Submodule (HolGerm (ComplexModel d) ⧸ a)
        (normalSupportQuotient d t (assignedRemainderNormalMask (fibreHeadWords d t I)) a)) :=
  Submodule.moduleSubmodule.toSMul

/-- ALL genuine analytic normal coefficients of the WHOLE original remainder ideal. -/
def coefficientIdeal (I : Ideal (HolGerm (ComplexModel (d+t))))
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t))) :
    Ideal (HolGerm (ComplexModel d)) :=
  Ideal.span {c | ∃ i : HolGerm (ComplexModel (d+t)), i ∈ I ∧
    ∃ γ : Fin t →₀ ℕ,
      actualNormalAnalyticCoefficientGerm d t (divisionRemainder d t I e i).val γ = c}

/-- Genuine analytic Noetherianity supplies FG; no finite original ideal sample is input. -/
theorem coefficientIdeal_fg (I : Ideal (HolGerm (ComplexModel (d+t))))
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t))) :
    (coefficientIdeal d t I e).FG := by
  let : IsNoetherianRing (HolGerm (ComplexModel d)) := isNoetherianRing_holGerm_euclidean d
  exact Ideal.fg_of_isNoetherianRing _

private theorem support_mem_base_iff_coefficients
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : Ideal (HolGerm (ComplexModel d))) (n : fibreRemainderModule d t I) :
    n ∈ a • (⊤ : Submodule (HolGerm (ComplexModel d)) (fibreRemainderModule d t I)) ↔
      ∀ γ, actualNormalAnalyticCoefficientGerm d t n.val γ ∈ a := by
  let Δ := assignedRemainderNormalMask (fibreHeadWords d t I)
  change n ∈ a • (⊤ : Submodule (HolGerm (ComplexModel d)) (normalSupportSubmodule d t Δ)) ↔ _
  rw [← normal_support_comap_base_ideal d t Δ a]
  change (n : HolGerm (ComplexModel (d+t))) ∈ a •
    (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)))) ↔ _
  rw [Ideal.smul_top_eq_map]
  exact mem_extended_base_ideal_iff_all_normal_coefficients d t a n.val

/-- EVERY original base ideal detects the WHOLE coefficient ideal via SAME actual K=R(I). -/
theorem coefficientIdeal_le_iff (I : Ideal (HolGerm (ComplexModel (d+t))))
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (a : Ideal (HolGerm (ComplexModel d))) :
    coefficientIdeal d t I e ≤ a ↔ idealRemainder d t I e ≤
      a • (⊤ : Submodule (HolGerm (ComplexModel d)) (fibreRemainderModule d t I)) := by
  constructor
  · intro hp n hn
    obtain ⟨i,hi,rfl⟩ := hn
    apply (support_mem_base_iff_coefficients d t I a _).mpr
    intro γ
    exact hp (Ideal.subset_span ⟨i,hi,γ,rfl⟩)
  · intro hK
    apply Ideal.span_le.mpr
    rintro c ⟨i,hi,γ,rfl⟩
    exact (support_mem_base_iff_coefficients d t I a _).mp (hK ⟨i,hi,rfl⟩) γ

/-- Canonical native quotient algebra of the WHOLE ORIGINAL sum ideal. -/
instance originalQuotientBaseAlgebra (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : Ideal (HolGerm (ComplexModel d))) :
    Algebra (HolGerm (ComplexModel d) ⧸ a)
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a)) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    ((Ideal.le_comap_map : a ≤ (Ideal.map (tangentPullback d t).toRingHom a).comap
      (tangentPullback d t).toRingHom).trans (Ideal.comap_mono le_sup_right))

/-- Native quotient scalar tower, with literal original algebra maps. -/
instance originalQuotientBaseTower (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : Ideal (HolGerm (ComplexModel d))) :
    IsScalarTower (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d) ⧸ a)
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a)) :=
  IsScalarTower.of_algebraMap_eq
    (R := HolGerm (ComplexModel d)) (S := HolGerm (ComplexModel d) ⧸ a)
    (A := HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a))
    fun _ => rfl

private theorem reassembly_difference_mem (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z) (g : HolGerm (ComplexModel (d+t))) :
    g - (divisionRemainder d t I e g : HolGerm (ComplexModel (d+t))) ∈ I := by
  have hEq := he (e.symm g)
  rw [e.apply_symm_apply] at hEq
  change g = (∑ j, ((e.symm g).1 j : HolGerm (ComplexModel (d+t))) *
    P.lift (fibreEnumeration d t I j)) + ((e.symm g).2 : HolGerm (ComplexModel (d+t))) at hEq
  change g - ((e.symm g).2 : HolGerm (ComplexModel (d+t))) ∈ I
  rw [sub_eq_iff_eq_add.mpr hEq]
  exact I.sum_mem fun j _ => I.mul_mem_left _ (P.member_trace (fibreEnumeration d t I j)).1

/-- Native WHOLE ORIGINAL quotient on EVERY base quotient, retaining SAME R/K. -/
def original_quotient_remainder_equiv (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (hr : ∀ n : fibreRemainderModule d t I, divisionRemainder d t I e n = n)
    (a : Ideal (HolGerm (ComplexModel d))) :
    (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a)) ≃ₗ[
      HolGerm (ComplexModel d) ⧸ a]
      (normalSupportQuotient d t (assignedRemainderNormalMask (fibreHeadWords d t I)) a ⧸
        normalSupportKernelImage d t (assignedRemainderNormalMask (fibreHeadWords d t I)) a
          (idealRemainder d t I e)) := by
  let A := HolGerm (ComplexModel d)
  let S := HolGerm (ComplexModel (d+t))
  let N := fibreRemainderModule d t I
  let Δ := assignedRemainderNormalMask (fibreHeadWords d t I)
  let R := divisionRemainder d t I e
  let K := idealRemainder d t I e
  let J := I.restrictScalars A
  let aN := a • (⊤ : Submodule A N)
  let aS := a • (⊤ : Submodule A S)
  let Na := normalSupportQuotient d t Δ a
  let Ka := normalSupportKernelImage d t Δ a K
  let Q : N →ₗ[A] Na := aN.mkQ
  let B : Na →ₗ[A] Na ⧸ Ka := Ka.mkQ.restrictScalars A
  let f := B.comp (Q.comp R)
  have hRsurj : Function.Surjective R := fun n => ⟨(n : S),hr n⟩
  have hf : Function.Surjective f := Ka.mkQ_surjective.comp (aN.mkQ_surjective.comp hRsurj)
  have hKR : LinearMap.ker R ≤ J := by
    intro g hg
    have hi := reassembly_difference_mem d t I P e he g
    change R g = 0 at hg
    have hz : (R g : S) = 0 := congrArg (fun n : N => (n : S)) hg
    rw [hz,sub_zero] at hi
    exact hi
  have hKa : Ka.restrictScalars A = K.map Q := by
    ext n
    rfl
  have hB : LinearMap.ker B = Ka.restrictScalars A := by
    ext n
    change (Submodule.Quotient.mk n : Na ⧸ Ka) = 0 ↔ n ∈ Ka
    exact Submodule.Quotient.mk_eq_zero _
  have hQ : LinearMap.ker Q = aN := Submodule.ker_mkQ _
  have hMap : (J ⊔ aS).map R = K ⊔ aN := by
    rw [Submodule.map_sup]
    congr 1
    change (a • (⊤ : Submodule A S)).map R = a • (⊤ : Submodule A N)
    rw [Submodule.map_smul'',Submodule.map_top,LinearMap.range_eq_top.mpr hRsurj]
  have hker : LinearMap.ker f = J ⊔ aS := by
    rw [LinearMap.ker_comp,hB,hKa,Submodule.comap_comp,Submodule.comap_map_eq,hQ,
      ← hMap,Submodule.comap_map_eq,sup_of_le_left (hKR.trans le_sup_left)]
  let b := I ⊔ Ideal.map (tangentPullback d t).toRingHom a
  have hb : b.restrictScalars A = J ⊔ aS := by
    rw [Submodule.restrictScalars_sup]
    congr 1
    exact (Ideal.smul_top_eq_map a).symm
  have hFull : LinearMap.ker f = b.restrictScalars A := hker.trans hb.symm
  let qA : (S ⧸ b) ≃ₗ[A] Na ⧸ Ka :=
    (Submodule.Quotient.restrictScalarsEquiv A b).symm.trans
      ((Submodule.quotEquivOfEq _ _ hFull.symm).trans (f.quotKerEquivOfSurjective hf))
  exact qA.extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- EVERY original representative maps to the SAME actual remainder class. -/
theorem original_quotient_remainder_equiv_mk (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (hr : ∀ n : fibreRemainderModule d t I, divisionRemainder d t I e n = n)
    (a : Ideal (HolGerm (ComplexModel d))) (g : HolGerm (ComplexModel (d+t))) :
    original_quotient_remainder_equiv d t I P e he hr a
      (Ideal.Quotient.mk (I ⊔ Ideal.map (tangentPullback d t).toRingHom a) g) =
      (Submodule.Quotient.mk (Submodule.Quotient.mk (divisionRemainder d t I e g) :
        normalSupportQuotient d t (assignedRemainderNormalMask (fibreHeadWords d t I)) a) :
        normalSupportQuotient d t (assignedRemainderNormalMask (fibreHeadWords d t I)) a ⧸
          normalSupportKernelImage d t (assignedRemainderNormalMask (fibreHeadWords d t I)) a
            (idealRemainder d t I e)) := by
  rfl

/-- ORIGINAL I alone internally yields a SAME full coefficient ideal for ALL actual base quotients. -/
theorem exists_original_quotient_flattening_ideal (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ (P : FibreLiftUniformTailData d t I)
      (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t))),
      (∀ z, e z = supportedReassembly d t I P z) ∧ (coefficientIdeal d t I e).FG ∧
      ∀ a : Ideal (HolGerm (ComplexModel d)),
        Module.Flat (HolGerm (ComplexModel d) ⧸ a)
          (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a)) ↔
        coefficientIdeal d t I e ≤ a := by
  obtain ⟨P,e,he,hr,_hKI,hmin,_hquot⟩ := exists_original_remainder_infinitesimal d t I
  refine ⟨P,e,he,coefficientIdeal_fg d t I e,?_⟩
  intro a
  let Δ := assignedRemainderNormalMask (fibreHeadWords d t I)
  let K := idealRemainder d t I e
  let q := original_quotient_remainder_equiv d t I P e he hr a
  constructor
  · intro hFlat
    let := hFlat
    have hTarget : Module.Flat (HolGerm (ComplexModel d) ⧸ a)
        (normalSupportQuotient d t Δ a ⧸ normalSupportKernelImage d t Δ a K) :=
      Module.Flat.of_linearEquiv q.symm
    exact (coefficientIdeal_le_iff d t I e a).mpr
      ((flat_normalSupportQuotientKernel_iff d t Δ a K hmin).mp hTarget)
  · intro hp
    have hTarget := (flat_normalSupportQuotientKernel_iff d t Δ a K hmin).mpr
      ((coefficientIdeal_le_iff d t I e a).mp hp)
    let := hTarget
    exact Module.Flat.of_linearEquiv q

end
end Hironaka.HironakaChowOriginalFlattenerCoefficients
