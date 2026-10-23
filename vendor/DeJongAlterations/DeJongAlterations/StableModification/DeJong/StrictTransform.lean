import DeJongAlterations.StableModification.DeJong.BaseStepFibers

/-!
# Strict transforms

For `w : W → S` and `ψ : S' → S` with `S'` irreducible with generic point `η'`, the strict
transform `strictTransform w ψ` (`Interface.lean`) is the scheme-theoretic closure of the
generic fibre `(W ×_S S')_{η'}` in `W ×_S S'` (de Jong 2.18, 2.20, `dejong96-alterations:page-0011`,
`page-0012`; Temkin §3.4). This file proves the two properties used in the base step 4.22:

* `strictTransform_fiberMap_isIso`, `strictTransformFiberIso`: the strict transform has the
  same generic fibre as `W ×_S S'` (the inclusion of the generic fibre factors through its
  scheme-theoretic image, which splits the closed immersion of generic fibres);
* `exists_isClosed_forall_mem_closure_fiber`, `exists_closed_forall_mem_strictTransform_support`:
  if `W ×_S S'` is a Noetherian space and `W ×_S S' → S'` is closed, then over the complement of
  a closed subset not containing `η'` every point of `W ×_S S'` lies on the strict transform
  (its irreducible components meeting the generic fibre lie in its closure; the others have
  closed image avoiding `η'`). This is the boundary bookkeeping of de Jong 4.22
  (`lem:sm-dj-boundary-bookkeeping`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {W S S' : Scheme.{u}}

/-- The closed immersion of the strict transform into `W ×_S S'`. -/
abbrev strictTransformι (w : W ⟶ S) (ψ : S' ⟶ S) [IrreducibleSpace S'] :
    (strictTransform w ψ).subscheme ⟶ pullback w ψ :=
  (strictTransform w ψ).subschemeι

/-- The structure morphism of the strict transform to `S'`. -/
abbrev strictTransformHom (w : W ⟶ S) (ψ : S' ⟶ S) [IrreducibleSpace S'] :
    (strictTransform w ψ).subscheme ⟶ S' :=
  strictTransformι w ψ ≫ pullback.snd w ψ

/-- The map of generic fibres induced by the inclusion of the strict transform. -/
def strictTransformFiberMap (w : W ⟶ S) (ψ : S' ⟶ S) [IrreducibleSpace S'] :
    (strictTransformHom w ψ).fiber (genericPoint S') ⟶
      (pullback.snd w ψ).fiber (genericPoint S') :=
  pullback.map (strictTransformHom w ψ) (S'.fromSpecResidueField (genericPoint S'))
    (pullback.snd w ψ) (S'.fromSpecResidueField (genericPoint S')) (strictTransformι w ψ)
    (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem strictTransformFiberMap_fiberToSpecResidueField (w : W ⟶ S) (ψ : S' ⟶ S)
    [IrreducibleSpace S'] :
    strictTransformFiberMap w ψ ≫ (pullback.snd w ψ).fiberToSpecResidueField (genericPoint S') =
      (strictTransformHom w ψ).fiberToSpecResidueField (genericPoint S') := by
  simp [strictTransformFiberMap, Scheme.Hom.fiberToSpecResidueField]

/-- **The strict transform has the same generic fibre.** The inclusion of the strict
transform induces an isomorphism of generic fibres. -/
theorem strictTransform_fiberMap_isIso (w : W ⟶ S) (ψ : S' ⟶ S) [IrreducibleSpace S'] :
    IsIso (strictTransformFiberMap w ψ) := by
  let j := (pullback.snd w ψ).fiberι (genericPoint S')
  let F := S'.fromSpecResidueField (genericPoint S')
  -- the strict transform is the scheme-theoretic image of `j`
  have hj : j.toImage ≫ strictTransformι w ψ = j := j.toImage_imageι
  let sec : (pullback.snd w ψ).fiber (genericPoint S') ⟶
      (strictTransformHom w ψ).fiber (genericPoint S') :=
    pullback.lift j.toImage ((pullback.snd w ψ).fiberToSpecResidueField (genericPoint S')) (by
      rw [strictTransformHom, reassoc_of% hj]
      exact pullback.condition)
  have hsec : sec ≫ strictTransformFiberMap w ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [sec, strictTransformFiberMap, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, Category.id_comp]
      exact hj
    · simp [sec, strictTransformFiberMap, Scheme.Hom.fiberToSpecResidueField]
  have : Mono (strictTransformFiberMap w ψ) := by
    refine ⟨fun a b hab ↦ ?_⟩
    apply pullback.hom_ext
    · rw [← cancel_mono (strictTransformι w ψ), Category.assoc, Category.assoc]
      have h1 : pullback.fst (strictTransformHom w ψ) F ≫ strictTransformι w ψ =
          strictTransformFiberMap w ψ ≫ pullback.fst (pullback.snd w ψ) F := by
        simp [strictTransformFiberMap, F]
      rw [h1, reassoc_of% hab]
    · have h2 : pullback.snd (strictTransformHom w ψ) F =
          strictTransformFiberMap w ψ ≫ pullback.snd (pullback.snd w ψ) F := by
        simp [strictTransformFiberMap, F]
      rw [h2, reassoc_of% hab]
  have : IsSplitEpi (strictTransformFiberMap w ψ) := ⟨⟨⟨sec, hsec⟩⟩⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- The isomorphism of generic fibres between the strict transform and `W ×_S S'`. -/
def strictTransformFiberIso (w : W ⟶ S) (ψ : S' ⟶ S) [IrreducibleSpace S'] :
    (strictTransformHom w ψ).fiber (genericPoint S') ≅
      (pullback.snd w ψ).fiber (genericPoint S') :=
  have := strictTransform_fiberMap_isIso w ψ
  asIso (strictTransformFiberMap w ψ)

@[reassoc (attr := simp)]
theorem strictTransformFiberIso_hom_fiberToSpecResidueField (w : W ⟶ S) (ψ : S' ⟶ S)
    [IrreducibleSpace S'] :
    (strictTransformFiberIso w ψ).hom ≫
        (pullback.snd w ψ).fiberToSpecResidueField (genericPoint S') =
      (strictTransformHom w ψ).fiberToSpecResidueField (genericPoint S') :=
  strictTransformFiberMap_fiberToSpecResidueField w ψ

/-- Points of `W ×_S S'` over the generic point lie on the strict transform. -/
theorem closure_fiber_subset_strictTransform_support (w : W ⟶ S) (ψ : S' ⟶ S)
    [IrreducibleSpace S'] :
    closure (pullback.snd w ψ ⁻¹' {genericPoint S'}) ⊆
      ((strictTransform w ψ).support : Set (pullback w ψ : Scheme.{u})) := by
  rw [(strictTransform w ψ).support.isClosed.closure_subset_iff, ← Scheme.Hom.range_fiberι]
  exact Scheme.Hom.range_subset_ker_support _

/-- **Boundary bookkeeping for strict transforms** (topological form). Let `h : Q → T` be a
continuous closed map from a Noetherian quasi-sober space to a `T₀` space with a generic
point `η`. Then there is a closed `E ⊆ T` with `η ∉ E` such that every point of `Q` over
`T ∖ E` lies in the closure of the fibre `h⁻¹(η)`. -/
theorem exists_isClosed_forall_mem_closure_fiber {Q T : Type*} [TopologicalSpace Q]
    [TopologicalSpace T] [NoetherianSpace Q] [QuasiSober Q] [T0Space T] (h : Q → T)
    (hc : Continuous h) (hcl : IsClosedMap h) {η : T} (hη : IsGenericPoint η Set.univ) :
    ∃ E : Set T, IsClosed E ∧ η ∉ E ∧ ∀ x, h x ∉ E → x ∈ closure (h ⁻¹' {η}) := by
  let F : Set Q := h ⁻¹' {η}
  -- points over `η` are stable under generization
  have hgen : ∀ x y : Q, x ⤳ y → y ∈ F → x ∈ F := by
    intro x y hxy hy
    have h1 : h x ⤳ η := by
      have := hxy.map hc
      simpa [F, show h y = η from hy] using this
    have h2 : η ⤳ h x := hη.specializes (Set.mem_univ _)
    exact (h1.antisymm h2).eq
  let 𝒦 : Set (Set Q) := {K | K ∈ irreducibleComponents Q ∧ Disjoint K F}
  have h𝒦 : Set.Finite 𝒦 :=
    Set.Finite.subset NoetherianSpace.finite_irreducibleComponents fun K hK ↦ hK.1
  let N : Set Q := ⋃ K ∈ 𝒦, K
  have hN : IsClosed N :=
    h𝒦.isClosed_biUnion fun K hK ↦ isClosed_of_mem_irreducibleComponents K hK.1
  refine ⟨h '' N, hcl N hN, ?_, ?_⟩
  · rintro ⟨x, hxN, hx⟩
    obtain ⟨K, hK, hxK⟩ := Set.mem_iUnion₂.mp hxN
    exact Set.disjoint_left.mp hK.2 hxK (show x ∈ F from hx)
  · intro x hx
    obtain ⟨K, hK, hxK⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
      isIrreducible_singleton
    have hxK' : x ∈ K := hxK rfl
    have hKF : ¬ Disjoint K F := fun hdisj ↦
      hx ⟨x, Set.mem_iUnion₂.mpr ⟨K, ⟨hK, hdisj⟩, hxK'⟩, rfl⟩
    obtain ⟨y, hyK, hyF⟩ := Set.not_disjoint_iff.mp hKF
    obtain ⟨k, hk⟩ := QuasiSober.sober hK.1 (isClosed_of_mem_irreducibleComponents K hK)
    have hkF : k ∈ F := hgen k y (hk.specializes hyK) hyF
    have hKsub : K ⊆ closure F := by
      rw [← hk.def]
      exact closure_mono (Set.singleton_subset_iff.mpr hkF)
    exact hKsub hxK'

/-- **Boundary bookkeeping for strict transforms.** If `W ×_S S'` is a Noetherian scheme and
its projection to the irreducible `S'` is universally closed, then there is a closed subset
`E ⊆ S'` not containing the generic point such that every point of `W ×_S S'` over `S' ∖ E`
lies on the strict transform. -/
theorem exists_closed_forall_mem_strictTransform_support (w : W ⟶ S) (ψ : S' ⟶ S)
    [IrreducibleSpace S'] [IsNoetherian (pullback w ψ)] [UniversallyClosed (pullback.snd w ψ)] :
    ∃ E : Set S', IsClosed E ∧ genericPoint S' ∉ E ∧
      ∀ x : (pullback w ψ : Scheme.{u}), pullback.snd w ψ x ∉ E →
        x ∈ ((strictTransform w ψ).support : Set (pullback w ψ : Scheme.{u})) := by
  obtain ⟨E, hE, hηE, hcov⟩ := exists_isClosed_forall_mem_closure_fiber
    (pullback.snd w ψ) (pullback.snd w ψ).continuous (pullback.snd w ψ).isClosedMap
    (genericPoint_spec S')
  exact ⟨E, hE, hηE, fun x hx ↦ closure_fiber_subset_strictTransform_support w ψ (hcov x hx)⟩

end DeJongAlterations.StableModification.DeJong
