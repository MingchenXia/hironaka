/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.CanonicalComponentGenericSmooth

/-! # Original canonical-component degrees with projectivity only of the component normalization -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Omega.ComponentDegreeMinimal

universe u

open ComponentDegree RosenlichtComponent Cohomology CurvesField CurvesField.Genus ComponentNormalization
open DeJong (IsNodalCurve IsSmoothAt)

set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme.{u}} (f : X ⟶ S) {K : Type u} [Field K] [IsAlgClosed K]
  (a : Spec (.of K) ⟶ S)
  [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) f a)))]
  [IsNodalCurve f] [CompactSpace (pullback (C := Scheme.{u}) f a)]
  {η : pullback (C := Scheme.{u}) f a} (hη : η ∈ genericPoints (pullback (C := Scheme.{u}) f a))

include hη in
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
    fun v hv => genericPoint_mem_smoothLocus (pullback.snd f a) v hv
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

include hη in
/-- **The degree of `ω` on the normalization of a component of a geometric fibre** (blueprint
`thm:canonical-component-dualizing-degree-minimal`). For a nodal curve `f : X ⟶ S` over an
integral, normal, locally Noetherian scheme, smooth over the generic point, a geometric point
`a : Spec K ⟶ S` (`K = K̄`) whose original canonical component normalization is projective, and a generic point `η` of `X_K`, let
`ν : Z̃ → X` be the normalization of the component `closure {η}` and `E = ν⁻¹(X ∖ Sm f)`. Then `E`
is a finite set of closed points, the cohomology of `ν^* ω` is finite-dimensional and
`deg ν^* ω = χ(ν^* ω) - χ(𝒪_Z̃) = 2 g(η) - 2 + #E`. -/
theorem degree_pullback_dualizingSheaf_component
    (hN : IsProjectiveOver (componentStructure f a η)) [IsIntegral S] [IsLocallyNoetherian S]
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
  obtain ⟨hfin, hcl⟩ := finite_nonSmooth_componentNormalization f a hη
  refine ⟨hfin.toFinset, fun y => by rw [Set.Finite.mem_toFinset]; rfl,
    fun y hy => hcl y ((Set.Finite.mem_toFinset hfin).mp hy), ?_⟩
  have := smoothOfRelativeDimension_componentStructure f a hη
  have := isLocallyNoetherian_normalizationPoints η (pullback.snd f a)
  obtain ⟨z, hz, hzη⟩ := exists_mem_closure_ne f a hη
  rw [← arithmeticGenus_componentNormalization f a η]
  exact degree_pullback_dualizingSheaf_of_isUnramifiedAt f _ _ a (componentMap_comp f a η) hS hgen
    hN
    (topologicalKrullDim_normalizationPoints_le η (pullback.snd f a)
      (topologicalKrullDim_fibre_le_one f a))
    (exists_ne_genericPoint η hz hzη) (isNormalScheme_normalizationPoints η) hfin.toFinset
    (fun y => by rw [Set.Finite.mem_toFinset]; rfl)
    (fun y hy => hcl y ((Set.Finite.mem_toFinset hfin).mp hy))
    (isUnramifiedAt_componentMap f a hη)

include hη in
/-- **The degree of a twist of `ν^* ω` at the marks** (blueprint
`thm:canonical-component-twist-degree-minimal`): if `α' : ν^* ω ⟶ G'` is a twist at a finite
set `M` of closed points of `Z̃` (injective on affine opens, bijective on affine opens missing `M`,
with one-dimensional cokernel near each point of `M`; e.g. `G' = ν^*(ω(D))` and `M = ν⁻¹ D`),
then `deg G' = 2 g(η) - 2 + #E + #M`. -/
theorem degree_twist_component
    (hN : IsProjectiveOver (componentStructure f a η)) [IsIntegral S] [IsLocallyNoetherian S]
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
  obtain ⟨E, hE, hEc, hfd, hdeg⟩ := degree_pullback_dualizingSheaf_component f a hη hN hS hgen
  have : IsNoetherian (componentNormalization f a η) :=
    { toIsLocallyNoetherian := isLocallyNoetherian_normalizationPoints η (pullback.snd f a) }
  rw [← arithmeticGenus_componentNormalization f a η] at hdeg ⊢
  refine ⟨E, hE, hEc, degree_twist _ α' M hMc hinj hsurj hloc hfd E.card hdeg⟩


end DeJongAlterations.StableModification.Omega.ComponentDegreeMinimal
