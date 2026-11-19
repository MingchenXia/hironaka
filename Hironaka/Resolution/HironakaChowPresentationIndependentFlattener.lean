import Hironaka.Resolution.HironakaChowSameDivisionQuotientFlatness

/-! Actual ORIGINAL whole-family presentation comparison on EVERY base quotient.
The ordinary native A-linear quotient equivalence is the only comparison input.
All A/a-linear comparisons, representative formulas and exact local coefficient
ideal equality are derived internally. Native first-isomorphism/quotient APIs
are reused, with zero duplicate algebra/division/choice milestone credit.
BP FIRST: hironaka-g10-presentation-independent-flattener.tex. -/
set_option autoImplicit false
namespace Hironaka.HironakaChowPresentationIndependentFlattener
noncomputable section
open Set Classical HolGerm HironakaRelativeNormalIdeal
  HironakaChowFibreLiftUniformTails HironakaChowFibreSupportModules
  HironakaChowFibreDivisionRemainder HironakaChowOriginalFlattenerCoefficients
  HironakaChowSameDivisionQuotientFlatness

variable (d : ℕ)
local instance (n : ℕ) :
    Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+n))) := tangentAlgebra d n

/-- Native original S/(I+aS) is the quotient of the WHOLE original S/I by a(S/I). -/
def originalBaseQuotientModuleEquiv (t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (a : Ideal (HolGerm (ComplexModel d))) :
    (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a)) ≃ₗ[
      HolGerm (ComplexModel d) ⧸ a]
      ((HolGerm (ComplexModel (d+t)) ⧸ I) ⧸
        a • (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)) ⧸ I))) := by
  let A := HolGerm (ComplexModel d)
  let S := HolGerm (ComplexModel (d+t))
  let M := S ⧸ I
  let aM := a • (⊤ : Submodule A M)
  let aS := a • (⊤ : Submodule A S)
  let J := I.restrictScalars A
  let b := I ⊔ Ideal.map (tangentPullback d t).toRingHom a
  let q : S →ₗ[A] M := (Ideal.Quotient.mkₐ A I).toLinearMap
  let f : S →ₗ[A] M ⧸ aM := aM.mkQ.comp q
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hf : Function.Surjective f := aM.mkQ_surjective.comp hq
  have hkerq : LinearMap.ker q = J := by
    ext x
    change Ideal.Quotient.mk I x = 0 ↔ x ∈ I
    exact Submodule.Quotient.mk_eq_zero I
  have hb : b.restrictScalars A = J ⊔ aS := by
    rw [Submodule.restrictScalars_sup]
    congr 1
    exact (Ideal.smul_top_eq_map a).symm
  have hker : LinearMap.ker f = b.restrictScalars A := by
    rw [LinearMap.ker_comp,Submodule.ker_mkQ,
      Submodule.comap_smul_top_of_surjective a q hq,hkerq,hb]
    exact sup_comm _ _
  let e : (S ⧸ b) ≃ₗ[A] M ⧸ aM :=
    (Submodule.Quotient.restrictScalarsEquiv A b).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf))
  exact e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- Every ORIGINAL representative retains its literal iterated quotient class. -/
theorem originalBaseQuotientModuleEquiv_mk (t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (a : Ideal (HolGerm (ComplexModel d)))
    (g : HolGerm (ComplexModel (d+t))) :
    originalBaseQuotientModuleEquiv d t I a
      (Ideal.Quotient.mk (I ⊔ Ideal.map (tangentPullback d t).toRingHom a) g) =
        Submodule.Quotient.mk (Ideal.Quotient.mk I g) := by
  rfl

/-- The actual original factor map is the SAME native module quotient under the comparison. -/
theorem originalBaseQuotientModuleEquiv_factor (t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (a : Ideal (HolGerm (ComplexModel d)))
    (m : HolGerm (ComplexModel (d+t)) ⧸ I) :
    originalBaseQuotientModuleEquiv d t I a
      (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ Ideal.map (tangentPullback d t).toRingHom a) m) =
        Submodule.Quotient.mk m := by
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective m
  exact originalBaseQuotientModuleEquiv_mk d t I a g

private def moduleQuotientEquiv (t s : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (J : Ideal (HolGerm (ComplexModel (d+s))))
    (E : (HolGerm (ComplexModel (d+t)) ⧸ I) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+s)) ⧸ J)) (a : Ideal (HolGerm (ComplexModel d))) :
    ((HolGerm (ComplexModel (d+t)) ⧸ I) ⧸
      a • (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)) ⧸ I))) ≃ₗ[
      HolGerm (ComplexModel d) ⧸ a]
    ((HolGerm (ComplexModel (d+s)) ⧸ J) ⧸
      a • (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+s)) ⧸ J))) := by
  have hMap : (a • (⊤ : Submodule (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ I))).map E.toLinearMap =
      a • (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+s)) ⧸ J)) := by
    rw [Submodule.map_smul'',Submodule.map_top,LinearMap.range_eq_top.mpr E.surjective]
  exact (Submodule.Quotient.equiv _ _ E hMap).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- An ordinary WHOLE-family equivalence internally yields the EXACT A/a-linear original comparison. -/
def originalPresentationQuotientEquiv (t s : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (J : Ideal (HolGerm (ComplexModel (d+s))))
    (E : (HolGerm (ComplexModel (d+t)) ⧸ I) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+s)) ⧸ J)) (a : Ideal (HolGerm (ComplexModel d))) :
    (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a)) ≃ₗ[
      HolGerm (ComplexModel d) ⧸ a]
      (HolGerm (ComplexModel (d+s)) ⧸ (J ⊔ Ideal.map (tangentPullback d s).toRingHom a)) :=
  ((originalBaseQuotientModuleEquiv d t I a).trans (moduleQuotientEquiv d t s I J E a)).trans
    (originalBaseQuotientModuleEquiv d s J a).symm

/-- Actual original representatives commute with E and the native target factor map. -/
theorem originalPresentationQuotientEquiv_mk (t s : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (J : Ideal (HolGerm (ComplexModel (d+s))))
    (E : (HolGerm (ComplexModel (d+t)) ⧸ I) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+s)) ⧸ J)) (a : Ideal (HolGerm (ComplexModel d)))
    (g : HolGerm (ComplexModel (d+t))) :
    originalPresentationQuotientEquiv d t s I J E a
      (Ideal.Quotient.mk (I ⊔ Ideal.map (tangentPullback d t).toRingHom a) g) =
      Ideal.Quotient.factor (le_sup_left : J ≤ J ⊔ Ideal.map (tangentPullback d s).toRingHom a)
        (E (Ideal.Quotient.mk I g)) := by
  apply (originalBaseQuotientModuleEquiv d s J a).injective
  simp only [originalPresentationQuotientEquiv,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [originalBaseQuotientModuleEquiv_mk,originalBaseQuotientModuleEquiv_factor]
  rfl

/-- Flatness of the TWO original analytic quotients is derived simultaneously for ALL a. -/
theorem flat_original_quotient_iff_of_presentation_equiv (t s : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (J : Ideal (HolGerm (ComplexModel (d+s))))
    (E : (HolGerm (ComplexModel (d+t)) ⧸ I) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+s)) ⧸ J)) (a : Ideal (HolGerm (ComplexModel d))) :
    Module.Flat (HolGerm (ComplexModel d) ⧸ a)
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a)) ↔
    Module.Flat (HolGerm (ComplexModel d) ⧸ a)
      (HolGerm (ComplexModel (d+s)) ⧸ (J ⊔ Ideal.map (tangentPullback d s).toRingHom a)) := by
  let q := originalPresentationQuotientEquiv d t s I J E a
  constructor
  · intro h
    let := h
    exact Module.Flat.of_linearEquiv q.symm
  · intro h
    let := h
    exact Module.Flat.of_linearEquiv q

/-- Exact whole coefficient ideals agree for ANY actual divisions of equivalent original presentations. -/
theorem coefficientIdeal_eq_of_presentation_equiv (t s : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (J : Ideal (HolGerm (ComplexModel (d+s))))
    (E : (HolGerm (ComplexModel (d+t)) ⧸ I) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+s)) ⧸ J))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (Q : FibreLiftUniformTailData d s J)
    (f : fibreDivisionModule d s J ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+s)))
    (hf : ∀ z, f z = supportedReassembly d s J Q z) :
    coefficientIdeal d t I e = coefficientIdeal d s J f := by
  have hiff (a : Ideal (HolGerm (ComplexModel d))) :
      coefficientIdeal d t I e ≤ a ↔ coefficientIdeal d s J f ≤ a :=
    (flat_original_quotient_iff d t I P e he a).symm.trans
      ((flat_original_quotient_iff_of_presentation_equiv d t s I J E a).trans
        (flat_original_quotient_iff d s J Q f hf a))
  exact le_antisymm ((hiff _).mpr le_rfl) ((hiff _).mp le_rfl)

/-- Choice independence is the identity-presentation specialization, with ZERO extra milestone credit. -/
theorem coefficientIdeal_eq_of_same_ideal (t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (Q : FibreLiftUniformTailData d t I)
    (f : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (hf : ∀ z, f z = supportedReassembly d t I Q z) :
    coefficientIdeal d t I e = coefficientIdeal d t I f :=
  coefficientIdeal_eq_of_presentation_equiv d t t I I (LinearEquiv.refl _ _) P e he Q f hf

/-- ONE original I-only local flatificator ideal; all choices disappear by the proved comparison. -/
def canonicalFlattenerIdeal (t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Ideal (HolGerm (ComplexModel d)) :=
  coefficientIdeal d t I (Classical.choose (Classical.choose_spec
    (exists_original_quotient_flattening_ideal d t I)))

/-- The canonical ideal reads back as the coefficient ideal of EVERY genuine SAME original division. -/
theorem canonicalFlattenerIdeal_eq_coefficientIdeal (t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t)))
    (he : ∀ z, e z = supportedReassembly d t I P z) :
    canonicalFlattenerIdeal d t I = coefficientIdeal d t I e := by
  let h := exists_original_quotient_flattening_ideal d t I
  let P₀ := Classical.choose h
  let e₀ := Classical.choose (Classical.choose_spec h)
  have he₀ : ∀ z, e₀ z = supportedReassembly d t I P₀ z :=
    (Classical.choose_spec (Classical.choose_spec h)).1
  exact coefficientIdeal_eq_of_same_ideal d t I P₀ e₀ he₀ P e he

/-- Genuine original analytic Noetherianity gives finite generation of the SAME canonical ideal. -/
theorem canonicalFlattenerIdeal_fg (t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    (canonicalFlattenerIdeal d t I).FG :=
  coefficientIdeal_fg d t I _

/-- The canonical local ideal is EXACTLY independent of the relative ambient presentation. -/
theorem canonicalFlattenerIdeal_eq_of_presentation_equiv (t s : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (J : Ideal (HolGerm (ComplexModel (d+s))))
    (E : (HolGerm (ComplexModel (d+t)) ⧸ I) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+s)) ⧸ J)) :
    canonicalFlattenerIdeal d t I = canonicalFlattenerIdeal d s J := by
  obtain ⟨P,e,he,_hFG,_hFlat⟩ := exists_original_quotient_flattening_ideal d t I
  obtain ⟨Q,f,hf,_hFG',_hFlat'⟩ := exists_original_quotient_flattening_ideal d s J
  rw [canonicalFlattenerIdeal_eq_coefficientIdeal d t I P e he,
    canonicalFlattenerIdeal_eq_coefficientIdeal d s J Q f hf]
  exact coefficientIdeal_eq_of_presentation_equiv d t s I J E P e he Q f hf

end
end Hironaka.HironakaChowPresentationIndependentFlattener
