import DeJongAlterations.StableModification.DeJong.Interface
import DeJongAlterations.StableModification.DeJong.Dimension
import DeJongAlterations.Geometry.CurveBoundaryBasic
import DeJongAlterations.Geometry.GenericFiberIntegral
import DeJongAlterations.Geometry.RegularSmoothConverse
import DeJongAlterations.Geometry.VarietyFunctionFieldDimension

/-!
# The generic fibre of a curve fibration and its horizontal boundary

This file contains the generic-fibre part of the Temkin-ready fibration (blueprint chapter
`sm-dj-fibration`; de Jong, *Smoothness, semi-stability and alterations*, 1996, 4.11–4.12,
`dejong96-alterations:page-0018`–`page-0020`). De Jong's 4.11–4.12 control all fibres of a curve
fibration `f : X ⟶ Y`; once Temkin's stable modification theorem (Temkin, *Stable modification
of relative curves*, §1.2) replaces de Jong 4.13–4.21, only the generic fibre of `f` and the
horizontal part of the boundary are used.

## Dimension of geometric fibres

* `ringKrullDim_tensorProduct_field`: `dim (A ⊗_K K') = dim A` for a finitely generated algebra
  `A` over a field `K` and any field extension `K'/K` (Noether normalization).
* `topologicalKrullDim_pullback_field`: the same for integral schemes locally of finite type.
* `isNodalCurve_of_smooth`: a smooth, geometrically integral curve over a field is a nodal curve
  in the sense of `IsNodalCurve`.

## Generic fibres

* `isNormalScheme_genericFiber`: the generic fibre of a normal scheme is normal (its local rings
  are local rings of the source).
* `topologicalKrullDim_genericFiber_eq`: for varieties, `dim X_η = dim X - dim Y`.

## The horizontal boundary

* `etale_of_isReduced_of_t1`: a reduced scheme locally of finite type over a field `K`, all of
  whose points are closed and whose residue fields are separable over `K`, is étale over `K`.
* `horizontalPart f W`, `horizontalIdeal f W`: the closure `W^h` of the points of `W` over the
  generic point `η` of `Y`, with its reduced structure (de Jong's horizontal boundary, 4.15).
* `exists_closeds_ne_top_subset_horizontalPart_union`: `W ⊆ W^h ∪ f⁻¹(T)` for a closed `T ⊊ Y`.
* `SeparableResidueFieldsAlong`, `etale_fiberMarks_horizontalIdeal`,
  `isSemistablePair_genericFiber`: if `X_η` is smooth, geometrically integral of dimension one
  and the points of `W ∩ X_η` have separable residue fields over `κ(η)`, then `(X_η, (W^h)_η)` is
  a semi-stable pair over `κ(η)`.

## Characteristic zero

* `smooth_genericFiber_of_charZero`, `separableResidueFieldsAlong_of_charZero`: in
  characteristic zero both hypotheses hold automatically when the generic fibre of a morphism
  from a normal variety is a curve (normal curves are regular, regular schemes over perfect
  fields are smooth, and closed points of curves have finite residue fields).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace DeJongAlterations.StableModification.DeJong

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Dimension

/-- The Krull dimension of a finitely generated algebra `A` over a field `K` is unchanged by an
extension `K'` of the ground field: by Noether normalization `A` is finite over a polynomial
ring `K[X₁, …, Xₛ] ⊆ A`, so `A ⊗_K K'` is finite over `K'[X₁, …, Xₛ] ⊆ A ⊗_K K'` (flatness of
`K'` over `K`), and both have dimension `s`. -/
theorem ringKrullDim_tensorProduct_field (K A K' : Type u) [Field K] [CommRing A] [Nontrivial A]
    [Algebra K A] [Algebra.FiniteType K A] [Field K'] [Algebra K K'] :
    ringKrullDim (A ⊗[K] K') = ringKrullDim A := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  let P := MvPolynomial (Fin s) K
  have hP : ringKrullDim P = s := by
    simp [P, MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hint : g.toRingHom.IsIntegral := hfin.to_isIntegral
  have hA : ringKrullDim A = s := by
    apply le_antisymm
    · exact (Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral g.toRingHom
        hint).trans_eq hP
    · exact hP ▸ Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral_of_injective
        g.toRingHom hint hinj
  let g' : P ⊗[K] K' →ₐ[K] A ⊗[K] K' := Algebra.TensorProduct.map g (AlgHom.id K K')
  have hinj' : Function.Injective g' :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := K') g.toLinearMap hinj
  have hint' : g'.toRingHom.IsIntegral := by
    let := g'.toRingHom.toAlgebra
    let : Algebra P A := g.toRingHom.toAlgebra
    have key : ∀ x : A ⊗[K] K', IsIntegral (P ⊗[K] K') x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => exact isIntegral_zero
      | add x y hx hy => exact hx.add hy
      | tmul a c =>
        have ha : IsIntegral P a := hint a
        have h1 : IsIntegral (P ⊗[K] K') (a ⊗ₜ[K] (1 : K')) := by
          refine ha.map_of_comp_eq (Algebra.TensorProduct.includeLeftRingHom)
            (Algebra.TensorProduct.includeLeftRingHom) ?_
          refine RingHom.ext fun p => ?_
          change g' (p ⊗ₜ 1) = g p ⊗ₜ 1
          exact Algebra.TensorProduct.map_tmul _ _ _ _
        have h2 : IsIntegral (P ⊗[K] K') ((1 : A) ⊗ₜ[K] c) := by
          have : (1 : A) ⊗ₜ[K] c = algebraMap (P ⊗[K] K') (A ⊗[K] K') (1 ⊗ₜ c) := by
            simp [g', RingHom.algebraMap_toAlgebra]
          rw [this]
          exact isIntegral_algebraMap
        have : a ⊗ₜ[K] c = (a ⊗ₜ[K] (1 : K')) * ((1 : A) ⊗ₜ[K] c) := by
          simp
        rw [this]
        exact h1.mul h2
    exact key
  have hP' : ringKrullDim (P ⊗[K] K') = s := by
    have e := (MvPolynomial.algebraTensorAlgEquiv (σ := Fin s) K K').toRingEquiv
    rw [ringKrullDim_eq_of_ringEquiv ((Algebra.TensorProduct.comm K P K').toRingEquiv.trans e)]
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  rw [hA]
  apply le_antisymm
  · exact (Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral g'.toRingHom
        hint').trans_eq hP'
  · exact hP' ▸ Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral_of_injective
        g'.toRingHom hint' hinj'

/-- The base change of an affine scheme of finite type over a field `K` to a field extension
`K'` has the same dimension. -/
theorem topologicalKrullDim_pullback_specMap {K : Type u} [Field K] {A : CommRingCat.{u}}
    (φ : CommRingCat.of K ⟶ A) (hφ : φ.hom.FiniteType) (K' : Type u) [Field K']
    (ψ : CommRingCat.of K ⟶ CommRingCat.of K') :
    topologicalKrullDim (pullback (C := Scheme.{u}) (Spec.map φ) (Spec.map ψ)) =
      ringKrullDim A := by
  algebraize [φ.hom, ψ.hom]
  have e := pullbackSpecIso K A K'
  have he : topologicalKrullDim (pullback (C := Scheme.{u}) (Spec.map φ) (Spec.map ψ)) =
      topologicalKrullDim (Spec (.of (A ⊗[K] K'))) :=
    e.schemeIsoToHomeo.isHomeomorph.topologicalKrullDim_eq
  rw [he]
  change topologicalKrullDim (PrimeSpectrum (A ⊗[K] K')) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton (A ⊗[K] K') := by
      constructor
      intro x y
      have h01 : (1 : A ⊗[K] K') = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : A) 0, TensorProduct.zero_tmul]
      exact (subsingleton_of_zero_eq_one h01.symm).elim x y
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · have : Algebra.FiniteType K A := hφ
    exact ringKrullDim_tensorProduct_field K A K'

/-- The dimension of an integral scheme locally of finite type over a field `K` is unchanged
by base change to any field extension `K'`. -/
theorem topologicalKrullDim_pullback_field {K : Type u} [Field K] {T : Scheme.{u}} [IsIntegral T]
    (g : T ⟶ Spec (.of K)) [LocallyOfFiniteType g] (K' : Type u) [Field K']
    (a : Spec (.of K') ⟶ Spec (.of K)) (n : ℕ) (hT : topologicalKrullDim T = n) :
    topologicalKrullDim (pullback (C := Scheme.{u}) g a) = n := by
  let ψ : CommRingCat.of K ⟶ CommRingCat.of K' := Spec.preimage a
  have ha : Spec.map ψ = a := Spec.map_preimage a
  let 𝒱 := T.affineOpenCover
  let φ : ∀ i, CommRingCat.of K ⟶ 𝒱.X i := fun i ↦ Spec.preimage (𝒱.f i ≫ g)
  have hφ : ∀ i, Spec.map (φ i) = 𝒱.f i ≫ g := fun i ↦ Spec.map_preimage _
  have hft : ∀ i, (φ i).hom.FiniteType := by
    intro i
    have : LocallyOfFiniteType (Spec.map (φ i)) := by rw [hφ i]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  let 𝒰 : (pullback (C := Scheme.{u}) g a).OpenCover := 𝒱.openCover.pullback₁ (pullback.fst g a)
  have hopen : ∀ i, IsOpenImmersion (𝒱.f i) := fun i ↦ 𝒱.openCover.map_prop i
  have hX : ∀ i, topologicalKrullDim (𝒰.X i) = ringKrullDim (𝒱.X i) := by
    intro i
    change topologicalKrullDim (pullback (C := Scheme.{u}) (pullback.fst g a) (𝒱.f i)) = _
    let e₁ : pullback (pullback.fst g a) (𝒱.f i) ≅ pullback (𝒱.f i ≫ g) a :=
      pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso g a (𝒱.f i)
    rw [e₁.schemeIsoToHomeo.isHomeomorph.topologicalKrullDim_eq, ← hφ i, ← ha]
    exact topologicalKrullDim_pullback_specMap (φ i) (hft i) K' ψ
  have hle : ∀ i, ringKrullDim (𝒱.X i) ≤ n := by
    intro i
    have := hopen i
    have h := (𝒱.f i).isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    change topologicalKrullDim (PrimeSpectrum (𝒱.X i)) ≤ _ at h
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hT] at h
    exact h
  apply le_antisymm
  · apply Geometry.FunctionFieldDimension.topologicalKrullDim_le_of_openCover _ n 𝒰
    intro i
    rw [hX i]
    exact hle i
  · obtain ⟨i, y, -⟩ := 𝒱.openCover.exists_eq (Classical.choice (inferInstance : Nonempty T))
    have : Nonempty (Spec (𝒱.X i)) := ⟨y⟩
    have := hopen i
    have : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have hi := Geometry.FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion g (𝒱.f i)
    change topologicalKrullDim (PrimeSpectrum (𝒱.X i)) = _ at hi
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hT] at hi
    have h := (𝒰.f i).isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    rw [hX i, hi] at h
    exact h

end Dimension

section GenericFiber

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The inclusion of the generic fibre is flat. -/
theorem flat_fiberι_genericPoint [IsIntegral Y] : Flat (f.fiberι (genericPoint Y)) := by
  have : Flat (Y.fromSpecResidueField (genericPoint Y)) :=
    Geometry.GenericFiberIntegral.fromSpecResidueField_flat Y
  change Flat (pullback.fst _ _)
  infer_instance

/-- The generic fibre of a morphism from a normal scheme to an integral scheme is normal: its
local rings are local rings of the source. -/
theorem isNormalScheme_genericFiber [IsIntegral Y] (hX : IsNormalScheme X) :
    IsNormalScheme (f.fiber (genericPoint Y)) := by
  have := flat_fiberι_genericPoint f
  intro z
  have : IsIso ((f.fiberι (genericPoint Y)).stalkMap z) :=
    Geometry.GenericFiberIntegral.stalkMap_isIso_of_flat_preimmersion _ z
  let e := (asIso ((f.fiberι (genericPoint Y)).stalkMap z)).commRingCatIsoToRingEquiv
  obtain ⟨h1, h2⟩ := hX (f.fiberι (genericPoint Y) z)
  have : IsDomain ((f.fiber (genericPoint Y)).presheaf.stalk z) := e.symm.toMulEquiv.isDomain
  exact ⟨this, (IsIntegrallyClosed.of_equiv e)⟩

/-- Dimension count for the generic fibre: if `dim X = a + b` and `dim Y = a` for varieties,
the generic fibre of a dominant `f : X ⟶ Y` has dimension `b` (transcendence degrees add). -/
theorem topologicalKrullDim_genericFiber_eq {k : Type u} [Field k] [IsIntegral X] [IsIntegral Y]
    (pY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType pY] [IsDominant f] [LocallyOfFiniteType f]
    (a b : ℕ) (hX : topologicalKrullDim X = (a + b : ℕ)) (hY : topologicalKrullDim Y = a) :
    topologicalKrullDim (f.fiber (genericPoint Y)) = b := by
  let := Geometry.SeparableGenericSmoothness.functionFieldAlgebra pY
  let := Geometry.SeparableGenericSmoothness.functionFieldAlgebra (f ≫ pY)
  let := Geometry.FiniteBirationalNormal.functionFieldAlgebra f
  let := Geometry.VarietyFunctionFieldDimension.functionFieldScalarTower pY f
  obtain ⟨n, hS, htrS⟩ := Geometry.FunctionFieldDimension.exists_dimension_and_trdeg pY
  obtain ⟨d, hd, htrX⟩ := Geometry.FunctionFieldDimension.exists_dimension_and_trdeg (f ≫ pY)
  obtain ⟨r, hr, hrel⟩ := Geometry.SteinGenericFiber.exists_dimension_and_trdeg f
  have hsum := trdeg_add_eq k Y.functionField (A := X.functionField)
  rw [htrS, hrel, htrX] at hsum
  have hnat : n + r = d := by exact_mod_cast hsum
  have hna : n = a := by exact_mod_cast hS.symm.trans hY
  have hdab : d = a + b := by exact_mod_cast hd.symm.trans hX
  rw [hr]
  congr 1
  omega

end GenericFiber

section Nodal

/-- A smooth, geometrically integral curve over a field is a nodal curve in the sense of the
interface (all points of all geometric fibres are smooth points). -/
theorem isNodalCurve_of_smooth {K : Type u} [Field K] {T : Scheme.{u}} (g : T ⟶ Spec (.of K))
    [Smooth g] [GeometricallyIntegral g] [IsIntegral T] (hdim : topologicalKrullDim T = 1) :
    IsNodalCurve g where
  pureGeometricFibers K' _ _ a Z hZ := by
    have : IsIntegral (pullback (C := Scheme.{u}) g a) :=
      GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
    have hZu : Z = Set.univ := by
      rw [irreducibleComponents_eq_singleton] at hZ
      exact hZ
    subst hZu
    rw [(Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq]
    exact_mod_cast topologicalKrullDim_pullback_field g K' a 1 (by exact_mod_cast hdim)
  geometricNodes K' _ _ a y _ := by
    left
    have : Smooth (pullback.snd g a) := inferInstance
    rw [Scheme.Hom.smoothLocus_eq_top_iff.mpr this]
    trivial

end Nodal

section Etale

/-- The local rings of a reduced scheme all of whose points are closed are fields. -/
theorem isField_stalk_of_isReduced_of_t1 (M : Scheme.{u}) [IsReduced M] [T1Space M] (z : M) :
    IsField (M.presheaf.stalk z) := by
  have hm : IsMax z := by
    intro w hzw
    have hwz : w = z := (show w ⤳ z from hzw).eq
    exact hwz.le
  have hco : Order.coheight z = 0 := Order.coheight_eq_zero.mpr hm
  have : Ring.KrullDimLE 0 (M.presheaf.stalk z) := krullDimLE_of_coheight_le hco.le
  exact Ring.KrullDimLE.isField_of_isReduced

/-- The residue map of a local ring which is a field is an isomorphism. -/
theorem isIso_residue_of_isField (M : Scheme.{u}) (z : M) (h : IsField (M.presheaf.stalk z)) :
    IsIso (M.residue z) := by
  let := h.toField
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨(M.residue z).hom.injective, M.residue_surjective z⟩

/-- **Étale criterion over a field.** A reduced scheme all of whose points are closed, locally
of finite type over a field `K`, is étale over `K` as soon as all its residue field extensions
are formally unramified (i.e. finite separable). -/
theorem etale_of_isReduced_of_t1 {K : Type u} [Field K] {M : Scheme.{u}} (q : M ⟶ Spec (.of K))
    [LocallyOfFiniteType q] [IsReduced M] [T1Space M]
    (hsep : ∀ z : M, (q.residueFieldMap z).hom.FormallyUnramified) : Etale q := by
  have : FormallyUnramified q := by
    refine HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime ?_
    intro z
    have h1 : IsIso (M.residue z) :=
      isIso_residue_of_isField M z (isField_stalk_of_isReduced_of_t1 M z)
    have h2 : IsIso ((Spec (.of K)).residue (q z)) :=
      isIso_residue_of_isField _ _ (Geometry.RegularSmoothConverse.specFieldStalk_isField (q z))
    have h := Scheme.residue_residueFieldMap q z
    have key : RingHom.FormallyUnramified (q.stalkMap z ≫ M.residue z).hom := by
      rw [← h]
      exact (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso _ _).mpr (hsep z)
    exact (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso _ _).mp key
  exact Etale.of_formallyUnramified_of_flat q

/-- Residue field maps of preimmersions are isomorphisms. -/
theorem isIso_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  have h := Scheme.residue_residueFieldMap f x
  have hs : Function.Surjective (f.stalkMap x ≫ X.residue x) :=
    (X.residue_surjective x).comp (f.stalkMap_surjective x)
  rw [← h] at hs
  intro b
  obtain ⟨a, ha⟩ := hs b
  exact ⟨Y.residue (f x) a, ha⟩

end Etale

section Boundary

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The *horizontal part* of a closed subset `W ⊆ X` with respect to `f : X ⟶ Y`: the closure
of the points of `W` lying over the generic point of `Y` (de Jong 4.12 (vi) d), 4.15). -/
def horizontalPart [IsIntegral Y] (W : Closeds X) : Closeds X :=
  Closeds.closure ((W : Set X) ∩ f ⁻¹' {genericPoint Y})

/-- The reduced closed subscheme structure on the horizontal part. -/
def horizontalIdeal [IsIntegral Y] (W : Closeds X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (horizontalPart f W)

/-- The horizontal part of `W` is contained in `W`. -/
theorem horizontalPart_le [IsIntegral Y] (W : Closeds X) : horizontalPart f W ≤ W := by
  intro x hx
  exact closure_minimal Set.inter_subset_left W.isClosed hx

/-- The support of the reduced horizontal boundary is the horizontal part. -/
theorem support_horizontalIdeal [IsIntegral Y] (W : Closeds X) :
    (horizontalIdeal f W).support = horizontalPart f W :=
  SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- **Vertical part.** If `X` is a Noetherian space, every point of `W` off the horizontal part
lies over a proper closed subset of `Y`: the irreducible components of `W` whose generic point
does not lie over the generic point of `Y` map into the closures of the images of their generic
points, none of which contains the generic point of `Y`. -/
theorem exists_closeds_ne_top_subset_horizontalPart_union [IsIntegral Y] [NoetherianSpace X]
    (W : Closeds X) :
    ∃ T : Closeds Y, T ≠ ⊤ ∧
      (W : Set X) ⊆ (horizontalPart f W : Set X) ∪ f ⁻¹' (T : Set Y) := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨⊥, ?_, fun x ↦ (IsEmpty.false x).elim⟩
    intro h
    have : genericPoint Y ∈ ((⊤ : Closeds Y) : Set Y) := trivial
    rw [← h] at this
    exact this
  obtain ⟨S, hSf, hScl, hSirr, hWS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible W.isClosed
  have hgen : ∀ t ∈ S, ∃ ξ : X, IsGenericPoint ξ t := fun t ht ↦
    QuasiSober.sober (hSirr t ht) (hScl t ht)
  choose! ξ hξ using hgen
  let S' := {t ∈ S | f (ξ t) ≠ genericPoint Y}
  let Tset : Set Y := ⋃ t ∈ S', closure {f (ξ t)}
  have hTcl : IsClosed Tset :=
    (hSf.subset (Set.sep_subset _ _)).isClosed_biUnion (fun _ _ ↦ isClosed_closure)
  refine ⟨⟨Tset, hTcl⟩, ?_, ?_⟩
  · intro hT
    have hη : genericPoint Y ∈ Tset := by
      have : genericPoint Y ∈ ((⊤ : Closeds Y) : Set Y) := trivial
      rw [← hT] at this
      exact this
    simp only [Tset, S', Set.mem_iUnion] at hη
    obtain ⟨t, ⟨htS, hne⟩, hmem⟩ := hη
    apply hne
    have h1 : f (ξ t) ⤳ genericPoint Y := specializes_iff_mem_closure.mpr hmem
    exact (h1.antisymm (genericPoint_specializes _)).eq
  · intro x hx
    rw [hWS] at hx
    obtain ⟨t, htS, hxt⟩ := hx
    have hspec : ξ t ⤳ x := (hξ t htS).specializes hxt
    by_cases hft : f (ξ t) = genericPoint Y
    · left
      have hξW : ξ t ∈ (W : Set X) := by
        rw [hWS]
        exact ⟨t, htS, (hξ t htS).mem⟩
      change x ∈ closure _
      exact closure_mono (Set.singleton_subset_iff.mpr
        (show ξ t ∈ (W : Set X) ∩ f ⁻¹' {genericPoint Y} from ⟨hξW, hft⟩))
        (specializes_iff_mem_closure.mp hspec)
    · right
      show f x ∈ Tset
      exact Set.mem_biUnion (x := t) (show t ∈ S' from ⟨htS, hft⟩)
        (specializes_iff_mem_closure.mp (hspec.map f.continuous))

end Boundary

section Marks

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The residue fields of the points of the fibre of `f` over `y` lying on `W` are separable
over the residue field of `y` (with the algebra structure given by the residue field maps of
the structure morphism of the fibre). This is the condition "the boundary points of the
generic fibre have separable residue fields" of the purely inseparable base change step. -/
def SeparableResidueFieldsAlong (y : Y) (W : Set X) : Prop :=
  ∀ z : f.fiber y, f.fiberι y z ∈ W →
    letI := ((f.fiberToSpecResidueField y).residueFieldMap z).hom.toAlgebra
    Algebra.IsSeparable ((Spec (Y.residueField y)).residueField (f.fiberToSpecResidueField y z))
      ((f.fiber y).residueField z)

variable [IsIntegral X] [IsIntegral Y] [IsDominant f]

/-- The generic point of the generic fibre maps to the generic point of the source. -/
theorem exists_fiberι_eq_genericPoint :
    ∃ z : f.fiber (genericPoint Y), f.fiberι (genericPoint Y) z = genericPoint X :=
  ⟨(f.fiberHomeo (genericPoint Y)).symm ⟨genericPoint X, genericPoint_map_of_isDominant f⟩,
    f.fiberι_fiberHomeo_symm _ _⟩

/-- **The horizontal boundary is étale over the generic point.** Let `f : X ⟶ Y` be dominant of
finite type between integral schemes, with generic fibre of dimension at most one, and let
`W ⊆ X` be closed and not containing the generic point of `X`. If the points of the generic
fibre lying on `W` have separable residue fields, then the generic fibre of the reduced
horizontal part of `W` is étale over `κ(η)`. Indeed it is a reduced closed subscheme (flat base
change of a reduced scheme along the generic fibre inclusion, a flat preimmersion) with proper
support on an integral curve, so all its points are closed (`CurveBoundary.t1_subscheme`), and
its residue fields are those of the points of `W` in the generic fibre. -/
theorem etale_fiberMarks_horizontalIdeal [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim (f.fiber (genericPoint Y)) ≤ 1)
    (W : Closeds X) (hW : genericPoint X ∉ W)
    (hsep : SeparableResidueFieldsAlong f (genericPoint Y) W) :
    Etale ((fiberMarks f (horizontalIdeal f W) (genericPoint Y)).subschemeι ≫
      f.fiberToSpecResidueField (genericPoint Y)) := by
  have : IsIntegral (f.fiber (genericPoint Y)) :=
    Geometry.GenericFiberIntegral.genericFiber_isIntegral f
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (genericPoint Y)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  let Dh := horizontalIdeal f W
  let D := fiberMarks f Dh (genericPoint Y)
  have := flat_fiberι_genericPoint f
  have : IsReduced Dh.subscheme :=
    Geometry.ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme _
  have : IsPreimmersion (pullback.snd (f.fiberι (genericPoint Y)) Dh.subschemeι) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsReduced (pullback (f.fiberι (genericPoint Y)) Dh.subschemeι) :=
    Geometry.GenericFiberIntegral.isReduced_of_flat_preimmersion (pullback.snd _ _)
  have : IsReduced D.subscheme :=
    isReduced_of_isOpenImmersion (Dh.comapIso (f.fiberι (genericPoint Y))).hom
  have hDW : ∀ z, z ∈ (D.support : Set (f.fiber (genericPoint Y))) →
      f.fiberι (genericPoint Y) z ∈ (W : Set X) := by
    intro z hz
    have hz' : f.fiberι (genericPoint Y) z ∈ (Dh.support : Set X) := by
      simpa [D, Scheme.IdealSheafData.support_comap] using hz
    rw [support_horizontalIdeal] at hz'
    exact horizontalPart_le f W hz'
  have hD : D.support ≠ ⊤ := by
    intro htop
    obtain ⟨z₀, hz₀⟩ := exists_fiberι_eq_genericPoint f
    apply hW
    rw [← hz₀]
    apply hDW
    rw [htop]
    trivial
  have : T1Space D.subscheme := Geometry.CurveBoundary.t1_subscheme hdim D hD
  apply etale_of_isReduced_of_t1
  intro z
  rw [Scheme.residueFieldMap_comp]
  have := isIso_residueFieldMap_of_isPreimmersion D.subschemeι z
  apply (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso _ _).mpr
  have hz : f.fiberι (genericPoint Y) (D.subschemeι z) ∈ (W : Set X) := by
    apply hDW
    rw [← D.range_subschemeι]
    exact ⟨z, rfl⟩
  exact @Algebra.FormallyUnramified.of_isSeparable _ _ _ _
    ((f.fiberToSpecResidueField (genericPoint Y)).residueFieldMap (D.subschemeι z)).hom.toAlgebra
    (hsep _ hz)

/-- **The generic fibre with its horizontal boundary is a semi-stable pair** (the generic part of
de Jong 4.12 (vi) c), d), in the form of Temkin's §1.2): if the generic fibre of `f` is smooth,
geometrically integral and of dimension one, and the boundary points of the generic fibre have
separable residue fields, then the generic fibre with the generic fibre of the reduced
horizontal boundary is a semi-stable pair over `κ(η)`. -/
theorem isSemistablePair_genericFiber [LocallyOfFiniteType f]
    [hsm : Smooth (f.fiberToSpecResidueField (genericPoint Y))]
    [hgi : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y))]
    (hdim : topologicalKrullDim (f.fiber (genericPoint Y)) = 1)
    (W : Closeds X) (hW : genericPoint X ∉ W)
    (hsep : SeparableResidueFieldsAlong f (genericPoint Y) W) :
    IsSemistablePair (f.fiberToSpecResidueField (genericPoint Y))
      (fiberMarks f (horizontalIdeal f W) (genericPoint Y)) where
  nodal := by
    have : IsIntegral (f.fiber (genericPoint Y)) :=
      Geometry.GenericFiberIntegral.genericFiber_isIntegral f
    exact @isNodalCurve_of_smooth (Y.residueField (genericPoint Y)) _ _
      (f.fiberToSpecResidueField (genericPoint Y)) hsm hgi this hdim
  etale := etale_fiberMarks_horizontalIdeal f hdim.le W hW hsep
  smoothAlong x _ := by
    rw [isSmoothAt_iff_mem_smoothLocus, Scheme.Hom.smoothLocus_eq_top_iff.mpr hsm]
    trivial

end Marks

section CharZero

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} [IsIntegral Y]
  (pY : Y ⟶ Spec (.of k)) (f : X ⟶ Y)

include pY in
/-- Over a ground field of characteristic zero, the generic residue field of a `k`-scheme has
characteristic zero. -/
theorem charZero_residueField_genericPoint : CharZero (Y.residueField (genericPoint Y)) := by
  let := Geometry.SeparableGenericSmoothness.functionFieldAlgebra pY
  let φ : k →+* Y.residueField (genericPoint Y) :=
    (Geometry.SteinGenericFiber.genericResidueIso (S := Y)).hom.hom.comp
      (algebraMap k Y.functionField)
  exact charZero_of_injective_ringHom φ.injective

include pY in
/-- **Characteristic zero: the generic fibre is smooth.** If `X` is normal and the generic fibre
of `f` has dimension at most one, it is a normal, hence regular
(`isRegularScheme_of_isNormalScheme_of_topologicalKrullDim_le_one`), curve over the perfect
field `κ(η)`, hence smooth (de Jong 2.10, Codex's `smooth_of_isRegularScheme`). -/
theorem smooth_genericFiber_of_charZero [LocallyOfFiniteType f] (hX : IsNormalScheme X)
    (hdim : topologicalKrullDim (f.fiber (genericPoint Y)) ≤ 1) :
    Smooth (f.fiberToSpecResidueField (genericPoint Y)) := by
  have := charZero_residueField_genericPoint pY
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (genericPoint Y)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsLocallyNoetherian (f.fiber (genericPoint Y)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (genericPoint Y))
  have hreg := isRegularScheme_of_isNormalScheme_of_topologicalKrullDim_le_one _
    (isNormalScheme_genericFiber f hX) hdim
  exact Geometry.RegularSmoothConverse.smooth_of_isRegularScheme
    (k := Y.residueField (genericPoint Y)) (f.fiberToSpecResidueField (genericPoint Y)) hreg

include pY in
/-- **Characteristic zero: the boundary points have separable residue fields.** A point of the
generic fibre lying on a closed `W` not containing the generic point of `X` is a closed point of
the generic curve, so its residue field is finite over `κ(η)`, hence separable in
characteristic zero. -/
theorem separableResidueFieldsAlong_of_charZero [IsIntegral X] [IsDominant f]
    [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim (f.fiber (genericPoint Y)) ≤ 1) (W : Closeds X)
    (hW : genericPoint X ∉ W) : SeparableResidueFieldsAlong f (genericPoint Y) W := by
  intro z hz
  have : IsIntegral (f.fiber (genericPoint Y)) :=
    Geometry.GenericFiberIntegral.genericFiber_isIntegral f
  let T := f.fiber (genericPoint Y)
  let g := f.fiberToSpecResidueField (genericPoint Y)
  have : LocallyOfFiniteType g := MorphismProperty.pullback_snd _ _ inferInstance
  have hzgen : z ≠ genericPoint T := by
    intro hzη
    obtain ⟨z₀, hz₀⟩ := exists_fiberι_eq_genericPoint f
    apply hW
    have hsp : f.fiberι (genericPoint Y) z ⤳ f.fiberι (genericPoint Y) z₀ := by
      rw [hzη]
      exact (genericPoint_specializes z₀).map (f.fiberι (genericPoint Y)).continuous
    rw [hz₀] at hsp
    exact hsp.mem_closed W.isClosed hz
  have hcl : IsClosed ({z} : Set T) :=
    Geometry.CurveBoundary.isClosed_singleton_of_ne_genericPoint hdim z hzgen
  have : IsClosedImmersion (T.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hcl
  have hfin : IsFinite (T.fromSpecResidueField z ≫ g) := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at hfin
  have : IsFinite (Spec.map (g.residueFieldMap z)) :=
    IsFinite.of_comp _ (Scheme.fromSpecResidueField _ _)
  have hφ := (IsFinite.SpecMap_iff (g.residueFieldMap z)).mp this
  let := (g.residueFieldMap z).hom.toAlgebra
  have : Module.Finite _ _ := hφ
  have : CharZero ((Spec (Y.residueField (genericPoint Y))).residueField (g z)) := by
    have := charZero_residueField_genericPoint pY
    let ψ : Y.residueField (genericPoint Y) ⟶
        (Spec (Y.residueField (genericPoint Y))).residueField (g z) :=
      (Scheme.ΓSpecIso _).inv ≫ (Spec _).presheaf.germ ⊤ (g z) trivial ≫ (Spec _).residue (g z)
    exact charZero_of_injective_ringHom ψ.hom.injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end CharZero

end DeJongAlterations.StableModification.DeJong
