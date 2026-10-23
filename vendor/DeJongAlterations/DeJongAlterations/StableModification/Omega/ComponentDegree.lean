/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.PoleChart
import DeJongAlterations.StableModification.Omega.ComponentNormalizationSmooth
import DeJongAlterations.StableModification.Omega.ComponentNormalizationUnramified
import DeJongAlterations.StableModification.Omega.BaseChangeFibreUnramified
import DeJongAlterations.StableModification.Omega.BaseChangeFibre
import DeJongAlterations.StableModification.Omega.RosenlichtComponentDegree
import DeJongAlterations.StableModification.BlowDown.NoClosedExc
import DeJongAlterations.StableModification.BlowDown.NodalReduced
import DeJongAlterations.StableModification.CurvesField.StableDownSchemeTop
import DeJongAlterations.StableModification.CurvesField.AmpleSection

/-!
# The degree of `ω` on the normalization of a component of a geometric fibre

Let `f : X ⟶ S` be a nodal curve over an integral, normal, locally Noetherian scheme, smooth over
the generic point, `K = K̄`, `a : Spec K ⟶ S`, `X_K = X ×_S Spec K` the geometric fibre
(projective over `K`), and `η` a generic point of `X_K`. Let `ν₀ : Z̃ = C̃_η → X_K` be the
normalization of the irreducible component `Z = closure {η}`
(`CurvesField.Genus.normalizationPoints {η}`, whose genus is `componentGenus η`),
`ν = ν₀ ≫ pr₁ : Z̃ → X` and `q = ν₀ ≫ pr₂ : Z̃ → Spec K`. Then
(`degree_pullback_dualizingSheaf_component`, blueprint
`cor:sm-omega-bcf-restriction-component`; Temkin, `semi-stable.tex`, l. 1736–1737 and
App. B, l. 4384–4433)

`deg ν^* ω = χ(ν^* ω) - χ(𝒪_Z̃) = 2 g(η) - 2 + #E`,  `E = ν⁻¹(X ∖ Sm f)`,

and, for a twist `ν^*ω → G'` at a finite set `M` of closed points (the points over the marks),
`deg G' = 2 g(η) - 2 + #E + #M` (`degree_twist_component`).

The normalization data (blueprint `lem:sm-omega-cd-normalization`): `Z̃` is integral, normal,
locally Noetherian, smooth of relative dimension one and projective over `K`, of dimension one;
`ν₀` is formally unramified, so `ν` is unramified relative to the base change at every point;
`E` is a finite set of closed points. With the pole charts (`PoleChart.hasPoleCharts`) the
conditional degree theorem `RosenlichtComponent.degree_pullback_dualizingSheaf_of_isNodalCurve`
becomes unconditional (`degree_pullback_dualizingSheaf_of_isUnramifiedAt`).
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.StableModification.Omega.ComponentDegree

open RosenlichtComponent Cohomology CurvesField CurvesField.Genus ComponentNormalization
open DeJong (IsNodalCurve IsSmoothAt)

section Unramified

variable {X S Y : Scheme.{u}} (f : X ⟶ S) {K : Type u} [Field K] [IsAlgClosed K]
  (q : Y ⟶ Spec (.of K)) (ν : Y ⟶ X) (a : Spec (.of K) ⟶ S) (sq : ν ≫ f = q ≫ a)

include sq in
/-- **The degree of `ν^* ω` for `ν` unramified relative to the base change** (blueprint
`cor:sm-omega-bcf-restriction-component`, without the pole-chart hypothesis): the hypotheses of
`RosenlichtComponent.degree_pullback_dualizingSheaf_of_isNodalCurve`, with `ν` unramified relative
to the base change at every point (also at `E`) and `Y` locally Noetherian; the pole charts are
`PoleChart.hasPoleCharts`. Then `deg ν^* ω = 2 p_a(Y) - 2 + #E`. -/
theorem degree_pullback_dualizingSheaf_of_isUnramifiedAt [IsNodalCurve f] [IsIntegral S]
    [IsLocallyNoetherian S] (hS : IsNormalScheme S)
    (hgen : ∀ x : X, f x = genericPoint S → IsSmoothAt f x)
    [IsIntegral Y] [CompactSpace Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    [SmoothOfRelativeDimension 1 q] [IsLocallyNoetherian Y] (hp : IsProjectiveOver q)
    (hdim : topologicalKrullDim Y ≤ 1) (hpt : ∃ y : Y, y ≠ genericPoint Y)
    (hnormal : IsNormalScheme Y) (E : Finset Y) (hE : ∀ y, y ∈ E ↔ ν y ∉ f.smoothLocus)
    (hEc : ∀ y ∈ E, IsClosed ({y} : Set Y)) (hun : ∀ y, IsUnramifiedAt f q ν y) :
    (∀ i, FiniteDimensional K
        (cohomology ((Scheme.Modules.pullback ν).obj (dualizingSheaf f)) (structureCoeff q) i)) ∧
      DualityScheme.eulerCharOf ((Scheme.Modules.pullback ν).obj (dualizingSheaf f))
          (structureCoeff q) - eulerChar Y (structureCoeff q) =
        2 * arithmeticGenus Y (structureCoeff q) - 2 + E.card := by
  have : IsNoetherian Y := {}
  exact degree_pullback_dualizingSheaf_of_isNodalCurve f q ν a sq hS hgen hp hdim hpt hnormal E hE
    hEc (fun y _ => hun y)
    (PoleChart.hasPoleCharts f q ν a sq hS hgen hnormal hdim hpt E hE hEc fun y _ => hun y)

end Unramified

section Fibre

variable {X S : Scheme.{u}} (f : X ⟶ S) {K : Type u} [Field K] [IsAlgClosed K]
  (a : Spec (.of K) ⟶ S)

/-- The geometric fibre of a nodal curve has dimension at most one. -/
theorem topologicalKrullDim_fibre_le_one [IsNodalCurve f] :
    topologicalKrullDim (pullback (C := Scheme.{u}) f a) ≤ 1 :=
  BlowDown.topologicalKrullDim_le_one_of_forall_irreducibleComponents fun W hW =>
    (IsNodalCurve.pureGeometricFibers (g := f) K a W hW).le

/-- The closed points of the geometric fibre of a nodal curve are not generic. -/
theorem not_mem_genericPoints_fibre [IsNodalCurve f] {z : pullback (C := Scheme.{u}) f a}
    (hz : IsClosed ({z} : Set (pullback (C := Scheme.{u}) f a))) : z ∉ genericPoints (pullback (C := Scheme.{u}) f a) :=
  BlowDown.not_mem_genericPoints_of_isClosed (IsNodalCurve.pureGeometricFibers (g := f) K a) hz

/-- The irreducible component `closure {η}` of the geometric fibre of a nodal curve is not a
point. -/
theorem exists_mem_closure_ne [IsNodalCurve f] {η : pullback (C := Scheme.{u}) f a}
    (hη : η ∈ genericPoints (pullback (C := Scheme.{u}) f a)) :
    ∃ z ∈ closure ({η} : Set (pullback (C := Scheme.{u}) f a)), z ≠ η := by
  by_contra h
  push Not at h
  have hdim := IsNodalCurve.pureGeometricFibers (g := f) K a (closure {η}) hη
  have : Subsingleton (closure ({η} : Set (pullback (C := Scheme.{u}) f a))) :=
    ⟨fun x y => Subtype.ext ((h x x.2).trans (h y y.2).symm)⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology (closure ({η} : Set (pullback (C := Scheme.{u}) f a)))
  rw [hdim] at h0
  exact absurd h0 (by decide)

omit [IsAlgClosed K] in
/-- A projective geometric fibre has affine diagonal (the instance needed by
`normalizationPoints`). -/
theorem isAffineHom_diagonal_fibre (hp : IsProjectiveOver (pullback.snd f a)) :
    IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) f a))) := by
  have := hp.isProper
  exact CurvesField.Ample.isAffineHom_diagonal_of_isSeparated (pullback.snd f a)

omit [IsAlgClosed K] in
/-- A projective geometric fibre is quasi-compact (the instance needed by `componentGenus`). -/
theorem compactSpace_fibre (hp : IsProjectiveOver (pullback.snd f a)) :
    CompactSpace (pullback (C := Scheme.{u}) f a) := by
  have := hp.isProper
  exact CurvesField.Ample.compactSpace_of_quasiCompact (pullback.snd f a)

variable [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) f a)))]

/-- The normalization of the component of `X_K` with generic point `η`. -/
abbrev componentNormalization (η : pullback (C := Scheme.{u}) f a) : Scheme.{u} :=
  normalizationPoints ({η} : Set (pullback (C := Scheme.{u}) f a))

/-- The map `Z̃ → X` from the normalization of a component of `X_K`. -/
abbrev componentMap (η : pullback (C := Scheme.{u}) f a) : componentNormalization f a η ⟶ X :=
  normalizationPointsMap ({η} : Set (pullback (C := Scheme.{u}) f a)) ≫ pullback.fst f a

/-- The structure map `Z̃ → Spec K` of the normalization of a component of `X_K`. -/
abbrev componentStructure (η : pullback (C := Scheme.{u}) f a) : componentNormalization f a η ⟶ Spec (.of K) :=
  normalizationPointsMap ({η} : Set (pullback (C := Scheme.{u}) f a)) ≫ pullback.snd f a

omit [IsAlgClosed K] in
theorem componentMap_comp (η : pullback (C := Scheme.{u}) f a) :
    componentMap f a η ≫ f = componentStructure f a η ≫ a := by
  simp only [Category.assoc, pullback.condition]

omit [IsAlgClosed K] in
/-- The lift `Z̃ → X_K` of `(ν, q)` is the normalization map `ν₀`. -/
theorem lift_componentMap (η : pullback (C := Scheme.{u}) f a) :
    pullback.lift (componentMap f a η) (componentStructure f a η) (componentMap_comp f a η) =
      normalizationPointsMap ({η} : Set (pullback (C := Scheme.{u}) f a)) :=
  pullback.hom_ext (by rw [pullback.lift_fst]) (by rw [pullback.lift_snd])

omit [IsAlgClosed K] in
/-- The genus of the normalization of a component is `componentGenus η`. -/
theorem arithmeticGenus_componentNormalization [CompactSpace (pullback (C := Scheme.{u}) f a)] (η : pullback (C := Scheme.{u}) f a) :
    arithmeticGenus (componentNormalization f a η) (structureCoeff (componentStructure f a η)) =
      componentGenus (structureCoeff (pullback.snd f a)) η :=
  rfl

variable [IsNodalCurve f] [CompactSpace (pullback (C := Scheme.{u}) f a)] (hp : IsProjectiveOver (pullback.snd f a))
  {η : pullback (C := Scheme.{u}) f a} (hη : η ∈ genericPoints (pullback (C := Scheme.{u}) f a))

include hη in
/-- **The normalization of a component of a geometric fibre of a nodal curve is unramified** over
the fibre (`ν₀` formally unramified; blueprint `lem:sm-omega-cd-unramified`). -/
theorem formallyUnramified_componentNormalization :
    FormallyUnramified (normalizationPointsMap ({η} : Set (pullback (C := Scheme.{u}) f a))) := by
  have : IsReduced (pullback (C := Scheme.{u}) f a) := IsNodalCurve.isReduced_pullback_of_isAlgClosed f K a
  have : Finite (genericPoints (pullback (C := Scheme.{u}) f a)) := finite_genericPoints (pullback.snd f a)
  exact formallyUnramified_normalizationPointsMap_singleton (pullback.snd f a)
    (topologicalKrullDim_fibre_le_one f a) (fun z hz => not_mem_genericPoints_fibre f a hz)
    (fun z hz => IsNodalCurve.geometricNodes (g := f) K a z hz) hη

include hη in
/-- **`ν` is unramified relative to the base change at every point** of the normalization of a
component (blueprint `lem:sm-omega-cd-normalization`). -/
theorem isUnramifiedAt_componentMap (y : componentNormalization f a η) :
    IsUnramifiedAt f (componentStructure f a η) (componentMap f a η) y := by
  have := formallyUnramified_componentNormalization f a hη
  have : FormallyUnramified (pullback.lift (componentMap f a η) (componentStructure f a η)
      (componentMap_comp f a η)) := by
    rw [lift_componentMap]; infer_instance
  exact isUnramifiedAt_of_formallyUnramified f _ _ a (componentMap_comp f a η) y

omit [CompactSpace (pullback (C := Scheme.{u}) f a)] in
include hη in
/-- **The normalization of a component is smooth of relative dimension one** over `K`. -/
theorem smoothOfRelativeDimension_componentStructure :
    SmoothOfRelativeDimension 1 (componentStructure f a η) := by
  obtain ⟨z, hz, hzη⟩ := exists_mem_closure_ne f a hη
  exact smoothOfRelativeDimension_one _ (isNormalScheme_normalizationPoints η)
    (topologicalKrullDim_normalizationPoints_le η (pullback.snd f a)
      (topologicalKrullDim_fibre_le_one f a))
    (exists_ne_genericPoint η hz hzη)

include hp hη in
/-- **The points of `Z̃` over the non-smooth locus of `f` form a finite set of closed points.** -/
theorem finite_nonSmooth_componentNormalization :
    {y : componentNormalization f a η | componentMap f a η y ∉ f.smoothLocus}.Finite ∧
      ∀ y : componentNormalization f a η, componentMap f a η y ∉ f.smoothLocus →
        IsClosed ({y} : Set (componentNormalization f a η)) := by
  have : IsReduced (pullback (C := Scheme.{u}) f a) := IsNodalCurve.isReduced_pullback_of_isAlgClosed f K a
  have : Finite (genericPoints (pullback (C := Scheme.{u}) f a)) := finite_genericPoints (pullback.snd f a)
  have : IsNoetherian (pullback (C := Scheme.{u}) f a) := {}
  have : IsFinite (normalizationPointsMap ({η} : Set (pullback (C := Scheme.{u}) f a))) :=
    isFinite_normalizationPointsMap_singleton η (pullback.snd f a)
  have hdimXK := topologicalKrullDim_fibre_le_one f a
  have hsm : ∀ x : pullback (C := Scheme.{u}) f a, pullback.fst f a x ∈ f.smoothLocus ↔
      x ∈ (pullback.snd f a).smoothLocus := fun x => by
    rw [← preimage_smoothLocus_eq_of_isNodalCurve f K a]; rfl
  -- the non-smooth locus of `X_K` is a finite set of closed points
  have hgenK : ∀ v ∈ genericPoints (pullback (C := Scheme.{u}) f a), v ∈ (pullback.snd f a).smoothLocus :=
    fun v hv => BlowDown.NoClosedExc.isSmoothAt_of_mem_genericPoints (pullback.snd f a) hdimXK hp
      (IsNodalCurve.pureGeometricFibers (g := f) K a)
      (fun z hz => IsNodalCurve.geometricNodes (g := f) K a z hz) hv
  have hfinK : ((pullback.snd f a).smoothLocus : Set (pullback (C := Scheme.{u}) f a))ᶜ.Finite :=
    finite_of_isClosed_of_disjoint_genericPoints hdimXK
      (pullback.snd f a).smoothLocus.isOpen.isClosed_compl fun v hv hvg => hv (hgenK v hvg)
  have hset : {y : componentNormalization f a η | componentMap f a η y ∉ f.smoothLocus} =
      normalizationPointsMap ({η} : Set (pullback (C := Scheme.{u}) f a)) ⁻¹'
        ((pullback.snd f a).smoothLocus : Set (pullback (C := Scheme.{u}) f a))ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe]
    rw [← hsm]
    rfl
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hset]
    exact hfinK.preimage' fun x _ => (normalizationPointsMap _).finite_preimage_singleton x
  · obtain ⟨z, hz, hzη⟩ := exists_mem_closure_ne f a hη
    refine Geometry.CurveBoundary.isClosed_singleton_of_ne_genericPoint
      (topologicalKrullDim_normalizationPoints_le η (pullback.snd f a) hdimXK) y fun hyg => hy ?_
    change pullback.fst f a (normalizationPointsMap ({η} : Set (pullback (C := Scheme.{u}) f a)) y) ∈ f.smoothLocus
    rw [hyg, normalizationPointsMap_genericPoint, hsm]
    exact hgenK η hη

include hp hη in
/-- **The degree of `ω` on the normalization of a component of a geometric fibre** (blueprint
`cor:sm-omega-bcf-restriction-component`, unconditional). For a nodal curve `f : X ⟶ S` over an
integral, normal, locally Noetherian scheme, smooth over the generic point, a geometric point
`a : Spec K ⟶ S` (`K = K̄`) with projective fibre `X_K`, and a generic point `η` of `X_K`, let
`ν : Z̃ → X` be the normalization of the component `closure {η}` and `E = ν⁻¹(X ∖ Sm f)`. Then `E`
is a finite set of closed points, the cohomology of `ν^* ω` is finite-dimensional and
`deg ν^* ω = χ(ν^* ω) - χ(𝒪_Z̃) = 2 g(η) - 2 + #E`. -/
theorem degree_pullback_dualizingSheaf_component [IsIntegral S] [IsLocallyNoetherian S]
    (hS : IsNormalScheme S) (hgen : ∀ x : X, f x = genericPoint S → IsSmoothAt f x) :
    ∃ E : Finset (componentNormalization f a η),
      (∀ y, y ∈ E ↔ componentMap f a η y ∉ f.smoothLocus) ∧
      (∀ y ∈ E, IsClosed ({y} : Set (componentNormalization f a η))) ∧
      (∀ i, FiniteDimensional K (cohomology ((Scheme.Modules.pullback (componentMap f a η)).obj
        (dualizingSheaf f)) (structureCoeff (componentStructure f a η)) i)) ∧
      DualityScheme.eulerCharOf ((Scheme.Modules.pullback (componentMap f a η)).obj
          (dualizingSheaf f)) (structureCoeff (componentStructure f a η)) -
        eulerChar (componentNormalization f a η) (structureCoeff (componentStructure f a η)) =
        2 * componentGenus (structureCoeff (pullback.snd f a)) η - 2 + E.card := by
  classical
  obtain ⟨hfin, hcl⟩ := finite_nonSmooth_componentNormalization f a hp hη
  refine ⟨hfin.toFinset, fun y => by rw [Set.Finite.mem_toFinset]; rfl,
    fun y hy => hcl y ((Set.Finite.mem_toFinset hfin).mp hy), ?_⟩
  have := smoothOfRelativeDimension_componentStructure f a hη
  have := isLocallyNoetherian_normalizationPoints η (pullback.snd f a)
  obtain ⟨z, hz, hzη⟩ := exists_mem_closure_ne f a hη
  rw [← arithmeticGenus_componentNormalization f a η]
  exact degree_pullback_dualizingSheaf_of_isUnramifiedAt f _ _ a (componentMap_comp f a η) hS hgen
    (isProjectiveOver_normalizationPoints η (pullback.snd f a) hp)
    (topologicalKrullDim_normalizationPoints_le η (pullback.snd f a)
      (topologicalKrullDim_fibre_le_one f a))
    (exists_ne_genericPoint η hz hzη) (isNormalScheme_normalizationPoints η) hfin.toFinset
    (fun y => by rw [Set.Finite.mem_toFinset]; rfl)
    (fun y hy => hcl y ((Set.Finite.mem_toFinset hfin).mp hy))
    (isUnramifiedAt_componentMap f a hη)

include hp hη in
/-- **The degree of a twist of `ν^* ω` at the marks** (blueprint
`cor:sm-omega-bcf-restriction-component`, with marks): if `α' : ν^* ω ⟶ G'` is a twist at a finite
set `M` of closed points of `Z̃` (injective on affine opens, bijective on affine opens missing `M`,
with one-dimensional cokernel near each point of `M`; e.g. `G' = ν^*(ω(D))` and `M = ν⁻¹ D`),
then `deg G' = 2 g(η) - 2 + #E + #M`. -/
theorem degree_twist_component [IsIntegral S] [IsLocallyNoetherian S]
    (hS : IsNormalScheme S) (hgen : ∀ x : X, f x = genericPoint S → IsSmoothAt f x)
    {G' : (componentNormalization f a η).Modules} [G'.IsQuasicoherent]
    (α' : (Scheme.Modules.pullback (componentMap f a η)).obj (dualizingSheaf f) ⟶ G')
    (M : Finset (componentNormalization f a η))
    (hMc : ∀ y ∈ M, IsClosed ({y} : Set (componentNormalization f a η)))
    (hinj : ∀ W : (componentNormalization f a η).Opens, IsAffineOpen W →
      Function.Injective (α'.app W))
    (hsurj : ∀ W : (componentNormalization f a η).Opens, IsAffineOpen W → (∀ y ∈ M, y ∉ W) →
      Function.Surjective (α'.app W))
    (hloc : ∀ y ∈ M, ∃ W : (componentNormalization f a η).Opens, IsAffineOpen W ∧ y ∈ W ∧
      (∀ z ∈ M, z ∈ W → z = y) ∧
      FiniteDimensional K (sectionsCoker (structureCoeff (componentStructure f a η)) α' W) ∧
      Module.finrank K (sectionsCoker (structureCoeff (componentStructure f a η)) α' W) = 1) :
    ∃ E : Finset (componentNormalization f a η),
      (∀ y, y ∈ E ↔ componentMap f a η y ∉ f.smoothLocus) ∧
      (∀ y ∈ E, IsClosed ({y} : Set (componentNormalization f a η))) ∧
      (∀ i, FiniteDimensional K (cohomology G' (structureCoeff (componentStructure f a η)) i)) ∧
      DualityScheme.eulerCharOf G' (structureCoeff (componentStructure f a η)) -
        eulerChar (componentNormalization f a η) (structureCoeff (componentStructure f a η)) =
        2 * componentGenus (structureCoeff (pullback.snd f a)) η - 2 + E.card + M.card := by
  have hω := isInvertibleModule_dualizingSheaf_of_isNodalCurve f hS hgen
  have : (dualizingSheaf f).IsQuasicoherent := isQuasicoherent_of_isInvertibleModule _ hω
  obtain ⟨E, hE, hEc, hfd, hdeg⟩ := degree_pullback_dualizingSheaf_component f a hp hη hS hgen
  have : IsNoetherian (componentNormalization f a η) :=
    { toIsLocallyNoetherian := isLocallyNoetherian_normalizationPoints η (pullback.snd f a) }
  rw [← arithmeticGenus_componentNormalization f a η] at hdeg ⊢
  refine ⟨E, hE, hEc, degree_twist _ α' M hMc hinj hsurj hloc hfd E.card hdeg⟩

end Fibre

end DeJongAlterations.StableModification.Omega.ComponentDegree
