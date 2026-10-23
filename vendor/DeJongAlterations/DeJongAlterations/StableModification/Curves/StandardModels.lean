import DeJongAlterations.StableModification.Curves.Basic
import DeJongAlterations.Geometry.NodeFamilyGeometricPurity
import DeJongAlterations.Geometry.NodeFamilySmooth
import DeJongAlterations.Geometry.NodeFamilySmoothDensityBaseChange
import DeJongAlterations.Geometry.NodeNormal
import DeJongAlterations.Geometry.NodeCompletion
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The standard models and strictly semi-stable curves

The two standard models of M. Temkin, *Stable modification of relative curves*, §4.3
(`references/temkin10-stable-modification/source/semi-stable.tex`, T:2949–2953) over a ring `A`:

* `smoothModel A : Spec A[T] ⟶ Spec A` with marks `smoothModelMarks A = {T = 0}` (the
  scheme-theoretic image of the zero section `smoothModelZeroSection A`);
* `nodeModel a : Spec A[u,v]/(uv - a) ⟶ Spec A` (Codex's `Geometry.NodeFamilyFlat.nodeMorphism`),
  without marks.

`IsStrictlySemistable g D` asks that `C` be covered by opens `U` with `U ⟶ S` factoring
through an open `Spec A ⊆ S` and an étale map to a standard model, the marks being the preimage
of the marks of the model.

## Main results

* `isNodalCurve_smoothModel`, `isNodalCurve_nodeModel`: the standard models are nodal curves
  (`lem:sm-smooth-model-nodal`, `lem:sm-node-model-nodal`); over a field the only non-smooth
  point of `K[u,v]/(uv - t)` is the origin for `t = 0`, an ordinary double point
  (`isNodalFiber_node`, using Codex's completed local ring of the split node).
* `IsStrictlySemistable.isSemistablePair`: strictly semi-stable pairs are semi-stable pairs
  (Temkin T:2953, "obviously"; `lem:sm-standard-model-fibres`).
* `isNormalScheme_smoothModel`: `Spec A[T]` is normal over a normal domain; for the node model
  see Codex's `Geometry.NodeNormal.node_isNormalScheme` (`lem:sm-standard-model-normal`).
* `isDomain_isIntegrallyClosed_localization_of_etale`, `isNormalScheme_of_etale`: étale over
  an integrally closed domain is normal (via Mathlib's "integral closure commutes with smooth
  base change" and the fact that the generic fibre of a local étale algebra is a field);
  `isNormalScheme_of_etale_smoothModel`, `isNormalScheme_of_etale_nodeModel`
  (`lem:sm-etale-normal`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Polynomial
open scoped TensorProduct

namespace DeJongAlterations.StableModification.Curves

universe u

open DeJong (IsNodalCurve IsSemistablePair IsSmoothAt)
open Geometry (IsGeometricOrdinaryDoublePoint)
open Geometry.NodeFamilyFlat (nodeMorphism)

section Models

variable (A : Type u) [CommRing A]

/-- The smooth standard model `Spec A[T] ⟶ Spec A` (Temkin T:2949). -/
def smoothModel : Spec (.of A[X]) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A A[X]))

/-- The zero section `T = 0` of the smooth standard model. -/
def smoothModelZeroSection : Spec (.of A) ⟶ Spec (.of A[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A)))

/-- The marks `{T = 0}` of the smooth standard model: the scheme-theoretic image of the zero
section (the closed subscheme `Spec A[T]/(T)`). -/
def smoothModelMarks : (Spec (.of A[X])).IdealSheafData :=
  (smoothModelZeroSection A).ker

/-- The nodal standard model `Spec A[u,v]/(uv - a) ⟶ Spec A` (Temkin T:2950), Codex's
`Geometry.NodeFamilyFlat.nodeMorphism`. -/
abbrev nodeModel {A : Type u} [CommRing A] (a : A) :
    Spec (.of (Algebra.NodeBlowupChart.Node A a)) ⟶ Spec (.of A) :=
  nodeMorphism a

instance algebraSmooth_polynomial : Algebra.Smooth A A[X] := ⟨inferInstance, inferInstance⟩

instance smoothModel_smooth : Smooth (smoothModel A) :=
  (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr inferInstance)

theorem smoothModelZeroSection_comp : smoothModelZeroSection A ≫ smoothModel A = 𝟙 _ := by
  rw [smoothModelZeroSection, smoothModel, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  simp

instance isClosedImmersion_smoothModelZeroSection : IsClosedImmersion (smoothModelZeroSection A) :=
  IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨Polynomial.C a, by simp⟩

/-- The marks of the smooth model map isomorphically to the base. -/
instance isIso_smoothModelMarks_subschemeι_comp :
    IsIso ((smoothModelMarks A).subschemeι ≫ smoothModel A) := by
  change IsIso ((smoothModelZeroSection A).imageι ≫ smoothModel A)
  have h : (smoothModelZeroSection A).imageι =
      inv (smoothModelZeroSection A).toImage ≫ smoothModelZeroSection A := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [h, Category.assoc, smoothModelZeroSection_comp, Category.comp_id]
  infer_instance

instance flat_nodeModel (a : A) : Flat (nodeModel a) := Geometry.NodeFamilyFlat.nodeMorphism_flat a

instance locallyOfFinitePresentation_nodeModel (a : A) :
    LocallyOfFinitePresentation (nodeModel a) :=
  Geometry.NodeFamilyFlat.nodeMorphism_locallyOfFinitePresentation a

end Models

section SmoothModel

/-- For a field `K` with `A ⟶ K`, the fibre of the smooth model is `Spec K[T]`. -/
def smoothModelFieldBaseChangeIso (A K : Type u) [CommRing A] [Field K] [Algebra A K] :
    pullback (smoothModel A) (Spec.map (CommRingCat.ofHom (algebraMap A K))) ≅
      Spec (.of K[X]) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso A K A[X] ≪≫
    Scheme.Spec.mapIso (polyEquivTensor' A K).symm.toRingEquiv.toCommRingCatIso.symm.op

set_option backward.isDefEq.respectTransparency false in
theorem smoothModelFieldBaseChangeIso_structure (A K : Type u) [CommRing A] [Field K]
    [Algebra A K] :
    (smoothModelFieldBaseChangeIso A K).hom ≫ smoothModel K = pullback.snd _ _ := by
  have h := Geometry.NodeFamilySmoothDensityBaseChange.specAlgEquiv_structure (R := K)
    (S := K ⊗[A] A[X]) (T := K[X]) (polyEquivTensor' A K).symm
  dsimp only [smoothModelFieldBaseChangeIso, Iso.trans_hom, smoothModel]
  rw [Category.assoc, Category.assoc, h, pullbackSpecIso_hom_fst',
    pullbackSymmetry_hom_comp_fst]

/-- `Spec K[T]` is a nodal (indeed smooth) curve over the field `K`. -/
theorem isNodalFiber_smoothModel (K : Type u) [Field K] : IsNodalFiber (smoothModel K) where
  pure Z hZ := by
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph]
    change topologicalKrullDim (PrimeSpectrum K[X]) = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    rfl
  nodes y _ := Or.inl (isSmoothAt_of_smooth _ y)

/-- **The smooth standard model is a nodal curve.** -/
instance isNodalCurve_smoothModel (A : Type u) [CommRing A] : IsNodalCurve (smoothModel A) := by
  refine IsNodalCurve.of_isNodalFiber _ fun K _ _ a ↦ ?_
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = a := ⟨Spec.preimage a, Spec.map_preimage a⟩
  let : Algebra A K := φ.hom.toAlgebra
  have h := (isNodalFiber_smoothModel K).of_etale (smoothModelFieldBaseChangeIso A K).hom
  rw [smoothModelFieldBaseChangeIso_structure] at h
  exact h

end SmoothModel

section NodeModel

open Algebra.NodeBlowupChart Geometry.NodeFamilySmooth

/-- The formal node `K[[u,v]]/(uv)` in the two normalizations used by Codex. -/
def formalNodeEquivFormalUV (K : Type u) [Field K] :
    Algebra.NodeCompletion.FormalNode K ≃ₐ[K]
      Algebra.NodeGeometricCompletionFormalUV.FormalUV K :=
  Ideal.quotientEquivAlgOfEq K (by
    simp [Algebra.NodeCompletion.formalNodeIdeal,
      Algebra.NodeGeometricCompletionFormalUV.uvPolynomial, MvPolynomial.coe_mul,
      MvPolynomial.coe_X])

/-- At a point of `Spec K[u,v]/(uv - t)` at which neither coordinate is invertible, `t = 0`. -/
theorem eq_zero_of_not_mem_coordinateOpen {K : Type u} [Field K] {t : K}
    (y : Spec (.of (Node K t))) (h0 : y ∉ coordinateOpen t 0) (h1 : y ∉ coordinateOpen t 1) :
    t = 0 := by
  have hu : coordinate t 0 ∈ y.asIdeal := by
    by_contra h
    exact h0 ((PrimeSpectrum.mem_basicOpen _ _).mpr h)
  have hv : coordinate t 1 ∈ y.asIdeal := by
    by_contra h
    exact h1 ((PrimeSpectrum.mem_basicOpen _ _).mpr h)
  have hprod : algebraMap K (Node K t) t ∈ y.asIdeal := by
    rw [← Algebra.NodeDomain.nodeCoordinateProduct]
    exact y.asIdeal.mul_mem_right _ hu
  by_contra ht
  apply y.isPrime.ne_top
  exact Ideal.eq_top_of_isUnit_mem _ hprod ((IsUnit.mk0 t ht).map _)

/-- A point of `Spec K[u,v]/(uv)` at which neither coordinate is invertible is the origin. -/
theorem eq_originPoint_of_not_mem_coordinateOpen {K : Type u} [Field K]
    (y : Spec (.of (Node K 0))) (h0 : y ∉ coordinateOpen (0 : K) 0)
    (h1 : y ∉ coordinateOpen (0 : K) 1) : y = Geometry.NodeCompletion.originPoint K := by
  have hu : coordinate (0 : K) 0 ∈ y.asIdeal := by
    by_contra h
    exact h0 ((PrimeSpectrum.mem_basicOpen _ _).mpr h)
  have hv : coordinate (0 : K) 1 ∈ y.asIdeal := by
    by_contra h
    exact h1 ((PrimeSpectrum.mem_basicOpen _ _).mpr h)
  have hle : Algebra.NodeCompletion.originIdeal K ≤ y.asIdeal := by
    rw [Algebra.NodeCompletion.originIdeal, Ideal.map_le_iff_le_comap,
      MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hv
  have hmax : (Algebra.NodeCompletion.originIdeal K).IsMaximal := by
    rw [Algebra.NodeCompletion.originIdeal_eq_ker]
    exact RingHom.ker_isMaximal_of_surjective _
      (Algebra.NodeCompletion.originEvaluation_surjective K)
  exact PrimeSpectrum.ext (hmax.eq_of_le y.isPrime.ne_top hle).symm

/-- `Spec K[u,v]/(uv - t)` is a nodal curve over the field `K`: its points with an invertible
coordinate are smooth, and the remaining point is the origin, which only exists for `t = 0`,
where it is an ordinary double point. -/
theorem isNodalFiber_node (K : Type u) [Field K] (t : K) : IsNodalFiber (nodeModel t) where
  pure Z hZ := Geometry.NodeFamilyGeometricPurity.node_component_dimension K t Z hZ
  nodes y _ := by
    by_cases h0 : y ∈ coordinateOpen t 0
    · exact Or.inl (coordinateOpen_le_smoothLocus t 0 h0)
    by_cases h1 : y ∈ coordinateOpen t 1
    · exact Or.inl (coordinateOpen_le_smoothLocus t 1 h1)
    right
    have ht := eq_zero_of_not_mem_coordinateOpen y h0 h1
    subst ht
    have hy := eq_originPoint_of_not_mem_coordinateOpen y h0 h1
    subst hy
    let := Scheme.completedLocalRingAlgebra (nodeModel (0 : K))
      (Geometry.NodeCompletion.originPoint K)
    exact ⟨(Geometry.NodeCompletion.completedLocalRingEquiv K).trans
      (formalNodeEquivFormalUV K)⟩

/-- **The nodal standard model is a nodal curve.** -/
instance isNodalCurve_nodeModel {A : Type u} [CommRing A] (a : A) :
    IsNodalCurve (nodeModel a) := by
  refine IsNodalCurve.of_isNodalFiber _ fun K _ _ b ↦ ?_
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = b := ⟨Spec.preimage b, Spec.map_preimage b⟩
  let : Algebra A K := φ.hom.toAlgebra
  have h := (isNodalFiber_node K (algebraMap A K a)).of_etale
    (Geometry.NodeFamilyGeometricPurity.nodeFieldBaseChangeIso K a).hom
  rw [Geometry.NodeFamilySmoothDensityBaseChange.nodeFieldBaseChangeIso_structure] at h
  exact h

end NodeModel

section StrictlySemistable

variable {C S : Scheme.{u}}

/-- `(C, D)` is *strictly semi-stable* over `S` (Temkin §4.3, T:2949–2953): every point of `C`
has an open neighbourhood `U` such that `U ⟶ S` factors through an open immersion
`ι : Spec A ⟶ S` and `h : U ⟶ Spec A`, where `h` is an étale map `e` followed by a standard
model, with `D ∩ U = e⁻¹{T = 0}` for the smooth model and `D ∩ U = ∅` for the nodal
model. -/
def IsStrictlySemistable (g : C ⟶ S) (D : C.IdealSheafData) : Prop :=
  ∀ x : C, ∃ U : C.Opens, x ∈ U ∧ ∃ (A : Type u) (_ : CommRing A)
    (ι : Spec (.of A) ⟶ S) (_ : IsOpenImmersion ι) (h : U.toScheme ⟶ Spec (.of A)),
    h ≫ ι = U.ι ≫ g ∧
    ((∃ e : U.toScheme ⟶ Spec (.of A[X]), Etale e ∧ e ≫ smoothModel A = h ∧
        D.comap U.ι = (smoothModelMarks A).comap e) ∨
      (∃ (a : A) (e : U.toScheme ⟶ Spec (.of (Algebra.NodeBlowupChart.Node A a))), Etale e ∧
        e ≫ nodeModel a = h ∧ D.comap U.ι = ⊤))

/-- Étaleness is local on the source, for covers by open immersions. -/
theorem etale_of_cover {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ x : X, ∃ (V : Scheme.{u}) (j : V ⟶ X) (_ : IsOpenImmersion j),
      x ∈ Set.range j ∧ Etale (j ≫ f)) : Etale f := by
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
  choose V j hj hx hE using h
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale.{u}) (fun x ↦ (j x).opensRange)
    (eq_top_iff.mpr fun y _ ↦ Opens.mem_iSup.mpr ⟨y, hx y⟩) fun x ↦ ?_
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
  have := hE x
  infer_instance

/-- A strictly semi-stable curve is a nodal curve. -/
theorem IsStrictlySemistable.isNodalCurve {g : C ⟶ S} {D : C.IdealSheafData}
    (hs : IsStrictlySemistable g D) : IsNodalCurve g := by
  refine IsNodalCurve.of_openCover g fun x ↦ ?_
  obtain ⟨U, hxU, A, _, ι, _, h, hh, hcase⟩ := hs x
  refine ⟨U, hxU, ?_⟩
  rw [← hh]
  have : IsNodalCurve h := by
    rcases hcase with ⟨e, he, rfl, -⟩ | ⟨a, e, he, rfl, -⟩
    · exact IsNodalCurve.etale_comp e (smoothModel A)
    · exact IsNodalCurve.etale_comp e (nodeModel a)
  exact IsNodalCurve.comp_isOpenImmersion h ι

/-- The marks of a strictly semi-stable curve are étale over the base. -/
theorem IsStrictlySemistable.etale_marks {g : C ⟶ S} {D : C.IdealSheafData}
    (hs : IsStrictlySemistable g D) : Etale (D.subschemeι ≫ g) := by
  refine etale_of_cover _ fun d ↦ ?_
  obtain ⟨U, hxU, A, _, ι, _, h, hh, hcase⟩ := hs (D.subschemeι d)
  refine ⟨_, (D.comapIso U.ι).hom ≫ pullback.snd U.ι D.subschemeι, inferInstance, ?_, ?_⟩
  · have hd : d ∈ Set.range (pullback.snd U.ι D.subschemeι) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      change D.subschemeι d ∈ Set.range U.ι
      rw [Scheme.Opens.range_ι]
      exact hxU
    obtain ⟨w, rfl⟩ := hd
    exact ⟨(D.comapIso U.ι).inv w, by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]⟩
  · have e1 : ((D.comapIso U.ι).hom ≫ pullback.snd U.ι D.subschemeι) ≫ D.subschemeι ≫ g =
        (D.comap U.ι).subschemeι ≫ h ≫ ι := by
      rw [Category.assoc, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
        Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc, hh]
    rw [e1]
    rcases hcase with ⟨e, he, rfl, hD⟩ | ⟨a, e, he, rfl, hD⟩
    · rw [hD]
      have e2 : ((smoothModelMarks A).comap e).subschemeι ≫ (e ≫ smoothModel A) ≫ ι =
          ((smoothModelMarks A).comapIso e).hom ≫
            pullback.snd e (smoothModelMarks A).subschemeι ≫
              ((smoothModelMarks A).subschemeι ≫ smoothModel A) ≫ ι := by
        rw [← Scheme.IdealSheafData.comapIso_hom_fst_assoc]
        simp only [Category.assoc]
        rw [pullback.condition_assoc]
      rw [e2]
      infer_instance
    · have : IsEmpty (D.comap U.ι).subscheme := by
        refine ⟨fun w ↦ ?_⟩
        have hw : (D.comap U.ι).subschemeι w ∈ ((D.comap U.ι).support : Set U.toScheme) := by
          rw [← Scheme.IdealSheafData.range_subschemeι]
          exact ⟨w, rfl⟩
        have hsupp : (D.comap U.ι).support = ⊥ := by
          rw [hD, Scheme.IdealSheafData.support_top]
        rw [hsupp] at hw
        exact hw
      infer_instance

/-- A strictly semi-stable curve is smooth along its marks. -/
theorem IsStrictlySemistable.isSmoothAt {g : C ⟶ S} {D : C.IdealSheafData}
    (hs : IsStrictlySemistable g D) {x : C} (hx : x ∈ (D.support : Set C)) :
    IsSmoothAt g x := by
  obtain ⟨U, hxU, A, _, ι, _, h, hh, hcase⟩ := hs x
  have hxU' : (⟨x, hxU⟩ : U.toScheme) ∈ ((D.comap U.ι).support : Set U.toScheme) := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hx
  rcases hcase with ⟨e, he, rfl, hD⟩ | ⟨a, e, he, rfl, hD⟩
  · have : Smooth (U.ι ≫ g) := by
      rw [← hh]
      infer_instance
    have h2 :=
      isSmoothAt_of_isOpenImmersion_comp U.ι (isSmoothAt_of_smooth (U.ι ≫ g) ⟨x, hxU⟩)
    simpa using h2
  · rw [hD, Scheme.IdealSheafData.support_top] at hxU'
    exact (hxU' : False).elim

/-- **Strictly semi-stable curves are semi-stable** (Temkin T:2953). -/
theorem IsStrictlySemistable.isSemistablePair {g : C ⟶ S} {D : C.IdealSheafData}
    (hs : IsStrictlySemistable g D) : IsSemistablePair g D where
  nodal := hs.isNodalCurve
  etale := hs.etale_marks
  smoothAlong _ hx := hs.isSmoothAt hx

end StrictlySemistable

section Normal

/-- In a local ring the only idempotents are `0` and `1`. -/
theorem eq_zero_or_one_of_isIdempotentElem_of_isLocalRing {T : Type*} [CommRing T]
    [IsLocalRing T] {t : T} (ht : IsIdempotentElem t) : t = 0 ∨ t = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self t with h | h
  · right
    have : t * t = t * 1 := by rw [ht.eq, mul_one]
    exact h.mul_left_cancel this
  · left
    have h0 : t * (1 - t) = 0 := by rw [mul_sub, mul_one, ht.eq, sub_self]
    have := congrArg (· * h.unit⁻¹.val) h0
    simpa [mul_assoc] using this

/-- A nontrivial reduced Artinian ring without nontrivial idempotents is a field. -/
theorem isField_of_isArtinianRing_of_isReduced {A : Type*} [CommRing A] [Nontrivial A]
    [IsArtinianRing A] [IsReduced A] (h : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsField A := by
  classical
  have hsub : ∀ I J : MaximalSpectrum A, I = J := by
    intro I J
    by_contra hIJ
    let e : A := (IsArtinianRing.equivPi A).symm (Pi.single I 1)
    have he : IsIdempotentElem e := by
      unfold IsIdempotentElem
      rw [← map_mul, ← Pi.single_mul, mul_one]
    have hEI : (IsArtinianRing.equivPi A) e = Pi.single I 1 := AlgEquiv.apply_symm_apply _ _
    have : Nontrivial (A ⧸ I.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr I.isMaximal.ne_top
    have : Nontrivial (A ⧸ J.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr J.isMaximal.ne_top
    rcases h e he with h0 | h1
    · have := congrFun hEI I
      rw [h0, map_zero, Pi.single_eq_same] at this
      exact zero_ne_one this
    · have := congrFun hEI J
      rw [h1, map_one, Pi.single_eq_of_ne (Ne.symm hIJ)] at this
      exact one_ne_zero this
  have : IsLocalRing A := by
    refine IsLocalRing.of_unique_max_ideal ?_
    obtain ⟨M, hM⟩ := Ideal.exists_maximal A
    refine ⟨M, hM, fun N hN ↦ ?_⟩
    exact congrArg MaximalSpectrum.asIdeal (hsub ⟨N, hN⟩ ⟨M, hM⟩)
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing A


/-- An idempotent is integral. -/
theorem isIntegral_of_isIdempotentElem {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {b : B} (hb : IsIdempotentElem b) : IsIntegral A b := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by decide))
  · simp [pow_two, hb.eq]

/-- **Étale over an integrally closed domain is normal** (local form): the localizations of an
étale algebra over an integrally closed domain at primes are integrally closed domains. -/
theorem isDomain_isIntegrallyClosed_localization_of_etale (R : Type u) {S : Type u} [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let T := Localization.AtPrime q
  let K := FractionRing R
  have : Module.Flat S T := IsLocalization.flat T q.primeCompl
  have : Module.Flat R T := Module.Flat.trans R S T
  have hbij : Function.Bijective (TensorProduct.toIntegralClosure R T K) :=
    TensorProduct.toIntegralClosure_bijective_of_tower (S := S)
      TensorProduct.toIntegralClosure_bijective_of_smooth
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := S) (S := T) q.primeCompl)
  have hinj : Function.Injective (algebraMap T (T ⊗[R] K)) :=
    Algebra.TensorProduct.includeLeft_injective (S := T) (IsFractionRing.injective R K)
  have key : ∀ x : T ⊗[R] K, IsIntegral T x → ∃ t : T, algebraMap T (T ⊗[R] K) t = x := by
    intro x hx
    obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
    have hall : ∀ y : T ⊗[R] integralClosure R K, ∃ t : T,
        algebraMap T _ t = (TensorProduct.toIntegralClosure R T K y : T ⊗[R] K) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul t b =>
        obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R K r = b :=
          IsIntegrallyClosed.isIntegral_iff.mp b.2
        refine ⟨algebraMap R T r * t, ?_⟩
        simp only [TensorProduct.toIntegralClosure, AlgHom.coe_codRestrict,
          Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Subalgebra.coe_val, ← hr,
          Algebra.algebraMap_eq_smul_one]
        rw [← TensorProduct.smul_tmul, smul_mul_assoc, one_mul, Algebra.TensorProduct.one_def,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add y z hy hz =>
        obtain ⟨a, ha⟩ := hy
        obtain ⟨b, hb⟩ := hz
        exact ⟨a + b, by rw [map_add, ha, hb, map_add, Subalgebra.coe_add]⟩
    obtain ⟨t, ht⟩ := hall y
    exact ⟨t, by rw [ht, hy]⟩
  -- the generic fibre `K ⊗[R] T` is a field
  have : Algebra.EssFiniteType S T := Algebra.EssFiniteType.of_isLocalization T q.primeCompl
  have : Algebra.EssFiniteType R T := Algebra.EssFiniteType.comp R S T
  have : Algebra.FormallyUnramified S T := Algebra.FormallyUnramified.of_isLocalization q.primeCompl
  have : Algebra.FormallyUnramified R T := Algebra.FormallyUnramified.comp R S T
  have : Algebra.EssFiniteType K (K ⊗[R] T) := inferInstance
  have : Algebra.FormallyUnramified K (K ⊗[R] T) := inferInstance
  have : Module.Finite K (K ⊗[R] T) := Algebra.FormallyUnramified.finite_of_free K _
  have : IsReduced (K ⊗[R] T) := Algebra.FormallyUnramified.isReduced_of_field K _
  have : IsArtinianRing (K ⊗[R] T) := isArtinian_of_tower K inferInstance
  let e : T ⊗[R] K ≃ₐ[R] K ⊗[R] T := Algebra.TensorProduct.comm R T K
  have : Nontrivial (T ⊗[R] K) := hinj.nontrivial
  have : Nontrivial (K ⊗[R] T) := e.injective.nontrivial
  have hfield : IsField (K ⊗[R] T) := isField_of_isArtinianRing_of_isReduced fun z hz ↦ by
    have hw : IsIdempotentElem (e.symm z) := by
      unfold IsIdempotentElem
      rw [← map_mul, hz.eq]
    obtain ⟨t, ht⟩ := key _ (isIntegral_of_isIdempotentElem hw)
    have htt : IsIdempotentElem t := hinj (by rw [map_mul, ht, hw.eq])
    rcases eq_zero_or_one_of_isIdempotentElem_of_isLocalRing htt with h0 | h1
    · left
      rw [← e.apply_symm_apply z, ← ht, h0, map_zero, map_zero]
    · right
      rw [← e.apply_symm_apply z, ← ht, h1, map_one, map_one]
  have hL : IsField (T ⊗[R] K) := MulEquiv.isField hfield e.toMulEquiv
  let : Field (T ⊗[R] K) := hL.toField
  have : IsDomain T := hinj.isDomain (algebraMap T (T ⊗[R] K))
  refine ⟨this, ?_⟩
  have : IsFractionRing T (T ⊗[R] K) := by
    refine IsLocalization.of_le (Algebra.algebraMapSubmonoid T (nonZeroDivisors R)) _ ?_ ?_
    · rintro _ ⟨m, hm, rfl⟩
      apply mem_nonZeroDivisors_of_ne_zero
      intro h0
      have hu := IsLocalization.map_units (T ⊗[R] K)
        (⟨algebraMap R T m, m, hm, rfl⟩ : Algebra.algebraMapSubmonoid T (nonZeroDivisors R))
      simp [h0] at hu
    · intro r hr
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hr))
  exact (isIntegrallyClosed_iff (T ⊗[R] K)).mpr fun {x} hx ↦ key x hx

/-- **Étale over a normal affine scheme is normal**: a scheme étale over the spectrum of an
integrally closed domain is normal (`lem:sm-etale-normal`). -/
theorem isNormalScheme_of_etale {X : Scheme.{u}} (B : Type u) [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] (e : X ⟶ Spec (.of B)) [Etale e] : IsNormalScheme X := by
  intro x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let φ : CommRingCat.of B ⟶ Γ(X, V) := (Scheme.ΓSpecIso (.of B)).inv ≫ e.appLE ⊤ V le_top
  have hφ : φ.hom.Etale := by
    have h := HasRingHomProperty.appLE (P := @Etale) e inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    exact (RingHom.Etale.respectsIso.cancel_left_isIso _ _).mpr h
  algebraize [φ.hom]
  have : Algebra.Etale B Γ(X, V) := hφ
  obtain ⟨h1, h2⟩ :=
    isDomain_isIntegrallyClosed_localization_of_etale B (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  let f : Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal ≃+* X.presheaf.stalk x :=
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl _ _).toRingEquiv
  exact ⟨f.symm.injective.isDomain f.symm.toRingHom, IsIntegrallyClosed.of_equiv f⟩

/-- **`Spec A[T]` is normal over a normal domain** (`lem:sm-standard-model-normal`; for the
nodal model see `Geometry.NodeNormal.node_isNormalScheme`). -/
theorem isNormalScheme_smoothModel (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] :
    IsNormalScheme (Spec (.of A[X])) :=
  isNormalScheme_spec A[X]

/-- A scheme étale over a standard model over a normal domain is normal; for the nodal model
the parameter must be nonzero (`lem:sm-etale-normal`). -/
theorem isNormalScheme_of_etale_smoothModel {X : Scheme.{u}} (A : Type u) [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] (e : X ⟶ Spec (.of A[X])) [Etale e] :
    IsNormalScheme X :=
  isNormalScheme_of_etale A[X] e

/-- A scheme étale over the nodal model `Spec A[u,v]/(uv - a)`, `A` a normal domain and
`a ≠ 0`, is normal (`lem:sm-etale-normal`). -/
theorem isNormalScheme_of_etale_nodeModel {X : Scheme.{u}} {A : Type u} [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] {a : A} (ha : a ≠ 0)
    (e : X ⟶ Spec (.of (Algebra.NodeBlowupChart.Node A a))) [Etale e] : IsNormalScheme X := by
  have : IsDomain (Algebra.NodeBlowupChart.Node A a) :=
    Algebra.NodeDomain.nodeQuotient_isDomain a ha
  have : IsIntegrallyClosed (Algebra.NodeBlowupChart.Node A a) :=
    Algebra.NodeNormal.node_isIntegrallyClosed a ha
  exact isNormalScheme_of_etale _ e

end Normal

end DeJongAlterations.StableModification.Curves
