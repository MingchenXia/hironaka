/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Algebra.RegularQuotientFamily
import DeJongAlterations.Geometry.RegularNode
import DeJongAlterations.Geometry.GenericSmoothness
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Regularity of actual smooth algebras and schemes over a field

Extended partial derivatives make the localized relation classes of a native
submersive presentation independent. Quotienting by these actual parameters
proves that every actual smooth algebra and scheme over a field is regular.
The converse implication over perfect fields in source 2.10 remains separate.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open IsLocalRing TensorProduct

namespace DeJongAlterations.Geometry.RegularSmooth

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] [IsLocalRing R]

/-- A derivation, restricted to the maximal ideal and reduced modulo that ideal, is linear. -/
def residueDerivation (D : Derivation k R R) : maximalIdeal R →ₗ[R] ResidueField R where
  toFun x := residue R (D x)
  map_add' x y := by simp
  map_smul' a x := by
    change residue R (D (a * (x : R))) = a • residue R (D x)
    have hx : residue R (x : R) = 0 := (residue_eq_zero_iff (x : R)).mpr x.property
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hx, zero_mul,
      add_zero, Algebra.smul_def, ResidueField.algebraMap_eq]

/-- A derivation induces an actual residue-field linear map on the local cotangent space. -/
def cotangentDerivation (D : Derivation k R R) :
    CotangentSpace R →ₗ[ResidueField R] ResidueField R := by
  let f := residueDerivation D
  have hf (x y : maximalIdeal R) : f (x * y) = 0 := by
    have hx : residue R (x : R) = 0 := (residue_eq_zero_iff (x : R)).mpr x.property
    have hy : residue R (y : R) = 0 := (residue_eq_zero_iff (y : R)).mpr y.property
    simp [f, residueDerivation, Derivation.leibniz, hx, hy]
  let g := Ideal.Cotangent.lift f hf
  exact
    { g.toAddMonoidHom with
      map_smul' a x := by
        obtain ⟨a, rfl⟩ := residue_surjective a
        change g (residue R a • x) = residue R a • g x
        simpa only [← ResidueField.algebraMap_eq, IsScalarTower.algebraMap_smul] using
          g.map_smul a x }

@[simp]
theorem cotangentDerivation_toCotangent (D : Derivation k R R) (x : maximalIdeal R) :
    cotangentDerivation D ((maximalIdeal R).toCotangent x) = residue R (D x) := rfl

/-- Independent residue derivative vectors imply independent actual cotangent classes. -/
theorem linearIndependent_cotangent_of_derivations {ι σ : Type*}
    (D : ι → Derivation k R R) (t : σ → maximalIdeal R)
    (h : LinearIndependent (ResidueField R) (fun j i ↦ residue R (D i (t j)))) :
    LinearIndependent (ResidueField R) (fun j ↦ (maximalIdeal R).toCotangent (t j)) := by
  let F : CotangentSpace R →ₗ[ResidueField R] (ι → ResidueField R) :=
    LinearMap.pi fun i ↦ cotangentDerivation (D i)
  apply LinearIndependent.of_comp F
  change LinearIndependent (ResidueField R)
    (fun j i ↦ cotangentDerivation (D i) ((maximalIdeal R).toCotangent (t j)))
  simpa only [cotangentDerivation_toCotangent] using h

variable {A L : Type*} [CommRing A] [CommRing L] [Algebra k A] [Algebra k L]
    [Algebra A L] [IsScalarTower k A L]

/-- The actual extension of a derivation to a localization, via localized differentials. -/
def localizedDerivation (M : Submonoid A) [IsLocalization M L] (D : Derivation k A A) :
    Derivation k L L := by
  let : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization M
  let f : Ω[A⁄k] →ₗ[A] L := (Algebra.linearMap A L).comp D.liftKaehlerDifferential
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A L
  exact KaehlerDifferential.linearMapEquivDerivation k L
    ((f.liftBaseChange L).comp e.symm.toLinearMap)

@[simp]
theorem localizedDerivation_algebraMap (M : Submonoid A) [IsLocalization M L]
    (D : Derivation k A A) (a : A) :
    localizedDerivation (L := L) M D (algebraMap A L a) = algebraMap A L (D a) := by
  let : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization M
  simp only [localizedDerivation, KaehlerDifferential.linearMapEquivDerivation_apply_apply,
    LinearMap.comp_apply]
  apply (congrArg (LinearMap.liftBaseChange L
      ((Algebra.linearMap A L).comp D.liftKaehlerDifferential))
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap k A L a)).trans
  simp only [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, Algebra.linearMap_apply,
    Derivation.liftKaehlerDifferential_comp_D, one_smul]

variable {S ι σ : Type*} [CommRing S] [Algebra k S]

/-- Actual relation elements in the maximal ideal of the ambient polynomial localization. -/
def localizedRelationFamily [Finite σ] (P : Algebra.SubmersivePresentation k S ι σ)
    (q : Ideal S) [q.IsPrime] :
    σ → maximalIdeal (Localization.AtPrime (q.comap (algebraMap P.Ring S))) := fun j ↦
  ⟨algebraMap P.Ring (Localization.AtPrime (q.comap (algebraMap P.Ring S))) (P.relation j), by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply Ideal.mem_map_of_mem
    change algebraMap P.Ring S (P.relation j) ∈ q
    rw [P.toPresentation.toGenerators.algebraMap_apply, P.toPresentation.aeval_val_relation]
    exact q.zero_mem⟩

/-- A native submersive Jacobian forces the actual localized relation classes to be independent. -/
theorem submersive_localizedRelations_linearIndependent [Fintype σ]
    (P : Algebra.SubmersivePresentation k S ι σ) (q : Ideal S) [q.IsPrime] :
    LinearIndependent
      (ResidueField (Localization.AtPrime (q.comap (algebraMap P.Ring S))))
      (fun j ↦ (maximalIdeal (Localization.AtPrime (q.comap (algebraMap P.Ring S)))).toCotangent
        (localizedRelationFamily P q j)) := by
  classical
  let p := q.comap (algebraMap P.Ring S)
  let L := Localization.AtPrime p
  let B := P.toPreSubmersivePresentation
  have hdet : B.jacobiMatrix.det ∉ p := by
    change algebraMap P.Ring S B.jacobiMatrix.det ∉ q
    rw [← B.jacobian_eq_jacobiMatrix_det]
    exact q.notMem_of_isUnit P.jacobian_isUnit
  let J : Matrix σ σ (ResidueField L) :=
    fun i j ↦ residue L (algebraMap P.Ring L
      (MvPolynomial.pderiv (P.map i) (P.relation j)))
  have hmatrix : J = ((residue L).comp (algebraMap P.Ring L)).mapMatrix B.jacobiMatrix := by
    ext i j
    change J i j = residue L (algebraMap P.Ring L (B.jacobiMatrix i j))
    rw [B.jacobiMatrix_apply]
  have hJ : J.det ≠ 0 := by
    rw [hmatrix, ← RingHom.map_det]
    change residue L (algebraMap P.Ring L B.jacobiMatrix.det) ≠ 0
    apply (residue_ne_zero_iff_isUnit _).mpr
    exact (IsLocalization.AtPrime.isUnit_to_map_iff L p _).mpr hdet
  let D : σ → Derivation k L L :=
    fun i ↦ localizedDerivation p.primeCompl (MvPolynomial.pderiv (P.map i))
  apply linearIndependent_cotangent_of_derivations D (localizedRelationFamily P q)
  have hcols := Matrix.linearIndependent_cols_of_det_ne_zero hJ
  convert hcols using 1
  funext j i
  change residue L (localizedDerivation (L := L) p.primeCompl (MvPolynomial.pderiv (P.map i))
    (algebraMap P.Ring L (P.relation j))) = _
  rw [localizedDerivation_algebraMap]
  rfl
  all_goals rfl

/-- Quotienting the actual ambient localization of a presentation gives the target local ring. -/
def presentationLocalizationEquiv (P : Algebra.Presentation k S ι σ)
    (q : Ideal S) [q.IsPrime] :
    ((Localization.AtPrime (q.comap (algebraMap P.Ring S))) ⧸
      P.ker.map (algebraMap P.Ring (Localization.AtPrime (q.comap (algebraMap P.Ring S))))) ≃+*
        Localization.AtPrime q := by
  let e := P.quotientEquiv.toRingEquiv
  let q' := q.comap e.toRingHom
  let e₁ := RegularNode.quotientLocalizationEquiv P.ker q'
  exact e₁.trans (IsLocalization.ringEquivOfRingEquiv
    (M := q'.primeCompl) (T := q.primeCompl)
    (Localization.AtPrime q') (Localization.AtPrime q) e (e.map_primeCompl_comap_eq q))

/-- Every actual local ring of a finite-variable submersive algebra over a field is regular. -/
theorem submersive_localization_isRegularLocalRing {K : Type*} [Field K]
    {T : Type*} [CommRing T] [Algebra K T] [Finite ι] [Fintype σ]
    (P : Algebra.SubmersivePresentation K T ι σ) (q : Ideal T) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let p := q.comap (algebraMap P.Ring T)
  let L := Localization.AtPrime p
  let t := localizedRelationFamily P q
  have hI : Ideal.span (Set.range fun j ↦ (t j : L)) =
      P.ker.map (algebraMap P.Ring L) := by
    rw [← P.toPresentation.span_range_relation_eq_ker, Ideal.map_span, ← Set.range_comp]
    rfl
  have hreg := Algebra.RegularQuotientFamily.isRegularLocalRing_quotient_family L t
    (submersive_localizedRelations_linearIndependent P q)
  rw [hI] at hreg
  let : IsRegularLocalRing (L ⧸ P.ker.map (algebraMap P.Ring L)) := hreg
  exact IsRegularLocalRing.of_ringEquiv
    (R := L ⧸ P.ker.map (algebraMap P.Ring L)) (presentationLocalizationEquiv P.toPresentation q)

/-- Actual standard smooth algebras over a field have regular local rings at every prime. -/
theorem isRegularRing_of_isStandardSmooth (K T : Type*) [Field K] [CommRing T]
    [Algebra K T] [Algebra.IsStandardSmooth K T] : IsRegularRing T := by
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  rw [isRegularRing_iff]
  intro q hq
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := K) (S := T)
  let : Fintype σ := Fintype.ofFinite σ
  exact submersive_localization_isRegularLocalRing P q

/-- Every actual smooth algebra over a field is regular; perfectness is unnecessary here. -/
theorem isRegularRing_of_smooth (K T : Type*) [Field K] [CommRing T]
    [Algebra K T] [Algebra.Smooth K T] : IsRegularRing T := by
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  rw [isRegularRing_iff]
  intro q hq
  obtain ⟨f, hf, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K q
  let S := Localization.Away f
  let q' := q.map (algebraMap T S)
  have hdisj : Disjoint (Submonoid.powers f : Set T) (q : Set T) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  have : q'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) S q hq hdisj
  let : IsRegularRing S := isRegularRing_of_isStandardSmooth K S
  have : IsLocalization.AtPrime (Localization.AtPrime q') q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers f) (Localization.AtPrime q') q' using 1
    exact (IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers f) S hq hdisj).symm
  exact IsRegularLocalRing.of_ringEquiv
    (R := Localization.AtPrime q')
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q')
      (Localization.AtPrime q)).toRingEquiv

open AlgebraicGeometry CategoryTheory

universe u

/-- Actual smooth schemes over any field have regular actual stalks. -/
theorem isRegularScheme_of_smooth {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) [Smooth p] : IsRegularScheme X := by
  intro x
  obtain ⟨R, f, hf, y, hy⟩ := Scheme.exists_Spec_apply_eq x
  let : IsOpenImmersion f := hf
  let q := f ≫ p
  have hq : Smooth q := inferInstance
  let B := Γ(Spec (CommRingCat.of K), ⊤)
  let : Field B :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  let F := q.appTop.hom
  let : Algebra B Γ(Spec R, ⊤) := F.toAlgebra
  have hF : F.Smooth := HasRingHomProperty.appTop (@Smooth) q hq
  let : Algebra.Smooth B Γ(Spec R, ⊤) := hF
  let : IsRegularRing Γ(Spec R, ⊤) := isRegularRing_of_smooth B Γ(Spec R, ⊤)
  let : IsRegularRing R :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  let z : PrimeSpectrum R := y
  let : z.asIdeal.IsPrime := z.isPrime
  let : IsRegularLocalRing ((Spec R).presheaf.stalk y) :=
    IsRegularLocalRing.of_ringEquiv
      (R := Localization.AtPrime z.asIdeal)
      (Spec.stalkIso R z).symm.commRingCatIsoToRingEquiv
  have hr : IsRegularLocalRing (X.presheaf.stalk (f y)) :=
    IsRegularLocalRing.of_ringEquiv
      (R := (Spec R).presheaf.stalk y)
      (asIso (f.stalkMap y)).symm.commRingCatIsoToRingEquiv
  change f y = x at hy
  rw [hy] at hr
  exact hr

/-- The native smooth locus over any field consists of actual regular local rings. -/
theorem isRegularLocalRing_of_mem_smoothLocus {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFinitePresentation p]
    (x : X) (hx : x ∈ p.smoothLocus) : IsRegularLocalRing (X.presheaf.stalk x) := by
  let U := p.smoothLocus
  let : Smooth (U.ι ≫ p) := GenericSmoothness.smooth_smoothLocus p
  let : IsRegularLocalRing ((U : Scheme).presheaf.stalk ⟨x, hx⟩) :=
    isRegularScheme_of_smooth (U.ι ≫ p) ⟨x, hx⟩
  exact IsRegularLocalRing.of_ringEquiv
    (R := (U : Scheme).presheaf.stalk ⟨x, hx⟩)
    (asIso (U.ι.stalkMap ⟨x, hx⟩)).symm.commRingCatIsoToRingEquiv

end DeJongAlterations.Geometry.RegularSmooth
