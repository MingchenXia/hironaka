import DeJongAlterations.StableModification.DeJong.Interface
import DeJongAlterations.Geometry.CompletedLocalRingEtale
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Nodal curves, modifications and stable modifications

This file develops the basic theory of nodal curves and semi-stable pairs of
`DeJongAlterations.StableModification.DeJong.Interface` and fixes the notions of
M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited as `T:<line>`),
§1.2 (T:1671–1690) and §3 (T:2240–2243), in the form used by the stable-modification
route to de Jong's Theorem 4.1 (blueprint chapters `sm-statements.tex` and
`sm-semistable-models.tex`).

## Nodal curves over a field and their locality

* `IsNodalFiber q`: a scheme `q : Y ⟶ Spec K` all of whose irreducible components have
  dimension one and whose closed points are smooth or geometric ordinary double points.
  `IsNodalCurve g` is the same condition on every geometric fibre
  (`IsNodalCurve.isNodalFiber`, `IsNodalCurve.of_isNodalFiber`).
* `IsNodalFiber.of_etale`: over an algebraically closed field, étale maps preserve
  nodal fibres (dimension of components via generizations and discrete fibres, smoothness
  by composition, nodes by Codex's completed-local-ring comparison for étale maps).
* `IsNodalFiber.of_cover`: the condition is local for open covers.
* `IsNodalCurve.etale_comp`, `IsNodalCurve.of_openCover`,
  `IsNodalCurve.comp_isOpenImmersion`, `isNodalCurve_pullback_snd`: nodal curves are
  stable under étale maps, local on the source, stable under open immersions of bases and
  under base change; `IsSemistablePair.pullback`, `IsSemistablePair.etale_comp`
  (Temkin T:1686–1690).

## Temkin's notions

* `MapsMarks f D' D`: `f : C' ⟶ C` is a morphism `(C', D') ⟶ (C, D)` of multipointed
  curves (T:1675).
* `IsSchematicModification f`: proper with an isomorphism between schematically dense
  opens (T:1677, T:2241); `IsEtaModification f g`: moreover an isomorphism on generic fibres
  (T:2243). Between integral schemes this is de Jong's `IsModification`
  (`IsSchematicModification.isModification`, `IsModification.isSchematicModification`).
* `IsExceptionalComponent β g D' a Z` (T:1687–1690, T:4459): a component of a geometric
  fibre which is the image of a closed immersion of `ℙ¹`, contracted by `β`, with at most two
  special points.
* `IsStableModification β g D D'` (T:1685–1690 with Remark 4.1, T:2810): an
  η-modification whose source with the transported marks `D'` is a semi-stable pair without
  exceptional components; `isStableModification_of_isIso` (non-vacuity),
  `IsExceptionalComponent.of_iso` and `not_isExceptionalComponent_pullback` (absence of
  exceptional components is fibrewise, hence stable under base change).
* `IsStableModification.support_iff_of_isIso`,
  `hasStableModification_of_isStableModification`: over the isomorphism locus the marks
  correspond, and the packaging into the consumed form `DeJong.HasStableModification`
  (first half of `lem:sm-dejong-bridge`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.Curves

universe u v

open DeJong (IsNodalCurve IsSemistablePair IsSmoothAt IsMultipointedCurve)
open Geometry (IsGeometricOrdinaryDoublePoint)

/-- Étale morphisms are locally quasi-finite. -/
instance (priority := low) locallyQuasiFinite_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] : LocallyQuasiFinite f := by
  have h := HasRingHomProperty.eq_affineLocally (P := @Etale)
  have hf : affineLocally RingHom.Etale f := by rw [← h]; infer_instance
  rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
  refine affineLocally_le ?_ f hf
  intro R S _ _ φ hφ
  algebraize [φ]
  have : Algebra.Etale R S := hφ
  exact (inferInstance : Algebra.QuasiFinite R S)

section NodalFiber

/-- A scheme `q : Y ⟶ Spec K` over a field is a *nodal curve over `K`*: every irreducible
component of `Y` has dimension one, and every closed point of `Y` is a smooth point of `q`
or a geometric ordinary double point (its completed local `K`-algebra is `K[[u,v]]/(uv)`).
This is the fibre condition of `DeJong.IsNodalCurve` (de Jong 2.21, Temkin T:1683–1685). -/
structure IsNodalFiber {K : Type u} [Field K] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K)) :
    Prop where
  pure : ∀ Z ∈ irreducibleComponents Y, topologicalKrullDim Z = 1
  nodes : ∀ y : Y, IsClosed ({y} : Set Y) →
    IsSmoothAt q y ∨ IsGeometricOrdinaryDoublePoint q y

variable {C S : Scheme.{u}}

/-- The geometric fibres of a nodal curve are nodal curves over their fields. -/
theorem IsNodalCurve.isNodalFiber (g : C ⟶ S) [h : IsNodalCurve g] (K : Type u) [Field K]
    [IsAlgClosed K] (a : Spec (.of K) ⟶ S) : IsNodalFiber (pullback.snd g a) :=
  ⟨h.pureGeometricFibers K a, fun y hy ↦ h.geometricNodes K a y hy⟩

/-- A flat morphism locally of finite presentation whose geometric fibres are nodal curves
over their fields is a nodal curve. -/
theorem IsNodalCurve.of_isNodalFiber (g : C ⟶ S) [Flat g] [LocallyOfFinitePresentation g]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S),
      IsNodalFiber (pullback.snd g a)) : IsNodalCurve g where
  pureGeometricFibers K _ _ a := (h K a).pure
  geometricNodes K _ _ a y hy := (h K a).nodes y hy

end NodalFiber

section ClosedPoints

variable {K : Type u} [Field K] [IsAlgClosed K] {Y Y' : Scheme.{u}}
  {q : Y ⟶ Spec (.of K)} {q' : Y' ⟶ Spec (.of K)}

/-- A morphism of schemes locally of finite type over an algebraically closed field maps
closed points to closed points. -/
theorem isClosed_image_of_isClosed [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (f : Y ⟶ Y') (hf : f ≫ q' = q) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    IsClosed ({f y} : Set Y') := by
  let p := pointOfClosedPoint q y hy
  have hp : (p ≫ f) ≫ q' = 𝟙 _ := by
    rw [Category.assoc, hf]
    exact pointOfClosedPoint_comp q y hy
  have hval : (p ≫ f) (IsLocalRing.closedPoint K) = f y := by
    change f (p (IsLocalRing.closedPoint K)) = f y
    exact congrArg f (pointOfClosedPoint_apply q y hy _)
  have hmem := ((pointEquivClosedPoint q') ⟨p ≫ f, hp⟩).2
  rw [mem_closedPoints_iff] at hmem
  rw [← hval]
  exact hmem

/-- At a closed point, the residue field extension of a morphism of schemes locally of
finite type over an algebraically closed field is trivial. -/
theorem isIso_residueFieldMap_of_isClosed [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (f : Y ⟶ Y') (hf : f ≫ q' = q) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    IsIso (f.residueFieldMap y) := by
  have hfy := isClosed_image_of_isClosed f hf hy
  let φ := residueFieldIsoBase q y hy
  let ψ := residueFieldIsoBase q' (f y) hfy
  have key : ψ.inv ≫ f.residueFieldMap y = φ.inv := by
    apply Spec.map_injective
    rw [Spec.map_comp, SpecMap_residueFieldIsoBase_inv, SpecMap_residueFieldIsoBase_inv,
      ← Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Category.assoc, hf]
  have : f.residueFieldMap y = ψ.hom ≫ φ.inv := by
    rw [← key, Iso.hom_inv_id_assoc]
  rw [this]
  infer_instance

end ClosedPoints

section Smooth

/-- Smoothness at a point is stable under composition. -/
theorem isSmoothAt_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {x : X}
    (hf : IsSmoothAt f x) (hg : IsSmoothAt g (f x)) : IsSmoothAt (f ≫ g) x := by
  have e := Scheme.Hom.stalkMap_comp f g x
  unfold IsSmoothAt at *
  rw [e]
  exact RingHom.FormallySmooth.comp hg hf

/-- A smooth morphism is smooth at every point. -/
theorem isSmoothAt_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    IsSmoothAt f x := by
  have h : x ∈ f.smoothLocus := by rw [f.smoothLocus_eq_top]; trivial
  exact h

/-- Smoothness at a point transfers along open immersions. -/
theorem isSmoothAt_of_isOpenImmersion_comp {X Y Z : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {g : Y ⟶ Z} {x : X} (h : IsSmoothAt (j ≫ g) x) : IsSmoothAt g (j x) := by
  have e := Scheme.Hom.stalkMap_comp j g x
  unfold IsSmoothAt at *
  rw [e] at h
  exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso (g.stalkMap (j x))
    (j.stalkMap x)).mp h

end Smooth

section Nodes

variable {K : Type u} [Field K] {Y Y' : Scheme.{u}}

/-- Geometric ordinary double points transfer along étale maps with trivial residue field
extension. -/
theorem isGeometricOrdinaryDoublePoint_of_etale (e : Y ⟶ Y') [Etale e]
    (q' : Y' ⟶ Spec (.of K)) (y : Y) [IsIso (e.residueFieldMap y)]
    (h : IsGeometricOrdinaryDoublePoint q' (e y)) :
    IsGeometricOrdinaryDoublePoint (e ≫ q') y := by
  let := Scheme.completedLocalRingAlgebra q' (e y)
  let := Scheme.completedLocalRingAlgebra (e ≫ q') y
  obtain ⟨φ⟩ := h
  exact ⟨(Geometry.CompletedLocalRingEtale.completedLocalRingAlgEquiv e q' y).symm.trans φ⟩

/-- Geometric ordinary double points descend along open immersions. -/
theorem isGeometricOrdinaryDoublePoint_of_isOpenImmersion (j : Y ⟶ Y') [IsOpenImmersion j]
    (q : Y' ⟶ Spec (.of K)) (y : Y) (h : IsGeometricOrdinaryDoublePoint (j ≫ q) y) :
    IsGeometricOrdinaryDoublePoint q (j y) := by
  let := Scheme.completedLocalRingAlgebra q (j y)
  let := Scheme.completedLocalRingAlgebra (j ≫ q) y
  obtain ⟨φ⟩ := h
  exact ⟨(Geometry.CompletedLocalRingEtale.completedLocalRingAlgEquiv j q y).trans φ⟩

end Nodes


section Components

section Topology

attribute [local instance] specializationOrder

/-- For quasi-sober `T₀` spaces the topological Krull dimension is the Krull dimension of the
specialization order on points. -/
theorem topologicalKrullDim_eq_krullDim (T : Type*) [TopologicalSpace T] [QuasiSober T]
    [T0Space T] : topologicalKrullDim T = Order.krullDim T :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- A continuous map of quasi-sober `T₀` spaces which is injective on every specialization
does not increase the Krull dimension. -/
theorem topologicalKrullDim_le_of_specializes_injective {T T' : Type*} [TopologicalSpace T]
    [TopologicalSpace T'] [QuasiSober T] [T0Space T] [QuasiSober T'] [T0Space T']
    (f : T → T') (hf : Continuous f) (hinj : ∀ x y, x ⤳ y → f x = f y → x = y) :
    topologicalKrullDim T ≤ topologicalKrullDim T' := by
  rw [topologicalKrullDim_eq_krullDim, topologicalKrullDim_eq_krullDim]
  apply Order.krullDim_le_of_strictMono f
  intro a b hab
  have h1 : b ⤳ a := hab.le
  refine lt_of_le_of_ne (h1.map hf) ?_
  intro heq
  exact hab.ne (hinj b a h1 heq.symm).symm

/-- In a quasi-sober `T₀` space of dimension at most zero there are no proper
specializations. -/
theorem eq_of_specializes_of_topologicalKrullDim_le_zero {T : Type*} [TopologicalSpace T]
    [QuasiSober T] [T0Space T] (h : topologicalKrullDim T ≤ 0) {x y : T} (hxy : x ⤳ y) :
    x = y := by
  rw [topologicalKrullDim_eq_krullDim, Order.krullDim_nonpos_iff_forall_isMax] at h
  have hle : y ≤ x := hxy
  exact ((h y).eq_of_le hle).symm

/-- A quasi-sober `T₀` space covered by open embeddings of spaces of dimension at most `n`
has dimension at most `n`. -/
theorem topologicalKrullDim_le_of_isOpenEmbedding_cover {T : Type v} [TopologicalSpace T]
    [QuasiSober T] [T0Space T] {n : WithBot ℕ∞}
    (h : ∀ x : T, ∃ (T' : Type v) (_ : TopologicalSpace T') (_ : QuasiSober T')
      (_ : T0Space T') (f : T' → T), IsOpenEmbedding f ∧ x ∈ Set.range f ∧
        topologicalKrullDim T' ≤ n) :
    topologicalKrullDim T ≤ n := by
  rw [topologicalKrullDim_eq_krullDim, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  obtain ⟨T', _, _, _, f, hf, ⟨x', rfl⟩, hn⟩ := h x
  rw [Topology.IsOpenEmbedding.coheight_eq f hf]
  rw [topologicalKrullDim_eq_krullDim] at hn
  exact (Order.coheight_le_krullDim x').trans hn

end Topology

/-- An element of `WithBot ℕ∞` which is at most one and not at most zero is one. -/
theorem eq_one_of_le_one_of_not_le_zero {x : WithBot ℕ∞} (h1 : x ≤ 1) (h0 : ¬ x ≤ 0) :
    x = 1 := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd bot_le h0
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd h1 (by decide)
    | coe m =>
      have hm1 : m ≤ 1 := by exact_mod_cast h1
      have hm0 : ¬ m ≤ 0 := fun h ↦ h0 (by exact_mod_cast h)
      have : m = 1 := by omega
      subst this
      rfl

variable {Y Y' : Scheme.{u}}

/-- Under a flat morphism the image of the generic point of an irreducible component is the
generic point of an irreducible component. -/
theorem genericPoint_image_mem_irreducibleComponents (e : Y ⟶ Y') [Flat e] {Z : Set Y}
    (hZ : Z ∈ irreducibleComponents Y) :
    closure {e hZ.1.genericPoint} ∈ irreducibleComponents Y' := by
  have hζ : IsGenericPoint hZ.1.genericPoint Z :=
    hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure {e hZ.1.genericPoint}) isIrreducible_singleton.closure
  have hw : IsGenericPoint hW.1.genericPoint W :=
    hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  have hwe : hW.1.genericPoint ⤳ e hZ.1.genericPoint := hw.specializes (hsub (subset_closure rfl))
  obtain ⟨ζ', hζ', hζ'e⟩ := Flat.generalizingMap e hwe
  have hZsub : Z ⊆ closure {ζ'} := by
    rw [← hζ.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hζ'.mem_closure) isClosed_closure
  have hmax := hZ.2 isIrreducible_singleton.closure hZsub
  have hζ'Z : ζ' ∈ Z := hmax (subset_closure rfl)
  have heq : ζ' = hZ.1.genericPoint := (hζ'.antisymm (hζ.specializes hζ'Z)).eq
  rw [heq] at hζ'e
  rw [hζ'e, hw.def]
  exact hW

/-- The restriction of an étale morphism to an irreducible component does not increase its
dimension. -/
theorem topologicalKrullDim_component_le_of_etale (e : Y ⟶ Y') [Etale e] {Z : Set Y}
    (hZ : Z ∈ irreducibleComponents Y) :
    topologicalKrullDim Z ≤ topologicalKrullDim (closure {e hZ.1.genericPoint} : Set Y') := by
  have hZc := isClosed_of_mem_irreducibleComponents Z hZ
  have hζ : IsGenericPoint hZ.1.genericPoint Z := hZ.1.isGenericPoint_genericPoint hZc
  have : QuasiSober Z := hZc.isClosedEmbedding_subtypeVal.quasiSober
  have : QuasiSober (closure {e hZ.1.genericPoint} : Set Y') :=
    isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  have hmaps : ∀ z ∈ Z, e z ∈ closure {e hZ.1.genericPoint} := fun z hz ↦
    ((hζ.specializes hz).map e.continuous).mem_closure
  refine topologicalKrullDim_le_of_specializes_injective
    (fun z : Z ↦ (⟨e z, hmaps z z.2⟩ : (closure {e hZ.1.genericPoint} : Set Y')))
    (by fun_prop) ?_
  intro x y hxy hexy
  have hxy' : (x : Y) ⤳ y := (IsInducing.subtypeVal.specializes_iff).mpr hxy
  have hexy' : e x = e y := congrArg Subtype.val hexy
  have hdisc := e.isDiscrete_preimage_singleton (e y)
  have : DiscreteTopology (e ⁻¹' {e y}) := hdisc.to_subtype
  have hsp : (⟨x, hexy'⟩ : e ⁻¹' {e y}) ⤳ ⟨y, rfl⟩ :=
    (IsInducing.subtypeVal.specializes_iff).mp hxy'
  have hseq : (⟨x, hexy'⟩ : e ⁻¹' {e y}) = ⟨y, rfl⟩ := specializes_iff_eq.mp hsp
  exact Subtype.ext (Subtype.mk.inj hseq)

/-- Over an algebraically closed field, an irreducible component of the source of an étale
morphism has dimension one if the image of its generic point spans a component of dimension
one. -/
theorem component_dimension_of_etale {K : Type u} [Field K] [IsAlgClosed K]
    {q' : Y' ⟶ Spec (.of K)} [LocallyOfFiniteType q'] (e : Y ⟶ Y') [Etale e] {Z : Set Y}
    (hZ : Z ∈ irreducibleComponents Y)
    (h1 : topologicalKrullDim (closure {e hZ.1.genericPoint} : Set Y') = 1) :
    topologicalKrullDim Z = 1 := by
  have hle := (topologicalKrullDim_component_le_of_etale e hZ).trans h1.le
  refine eq_one_of_le_one_of_not_le_zero hle fun h0 ↦ ?_
  have hZc := isClosed_of_mem_irreducibleComponents Z hZ
  have hζ : IsGenericPoint hZ.1.genericPoint Z := hZ.1.isGenericPoint_genericPoint hZc
  have : QuasiSober Z := hZc.isClosedEmbedding_subtypeVal.quasiSober
  have hZeq : Z = {hZ.1.genericPoint} := by
    refine Set.Subset.antisymm (fun z hz ↦ ?_) (Set.singleton_subset_iff.mpr hζ.mem)
    have hsp : (⟨hZ.1.genericPoint, hζ.mem⟩ : Z) ⤳ ⟨z, hz⟩ :=
      (IsInducing.subtypeVal.specializes_iff).mp (hζ.specializes hz)
    exact (congrArg Subtype.val (eq_of_specializes_of_topologicalKrullDim_le_zero h0 hsp)).symm
  have hcl : IsClosed ({hZ.1.genericPoint} : Set Y) := hZeq ▸ hZc
  have hecl := isClosed_image_of_isClosed (q := e ≫ q') e rfl hcl
  rw [hecl.closure_eq] at h1
  have h0' := topologicalKrullDim_zero_of_discreteTopology ({e hZ.1.genericPoint} : Set Y')
  rw [h1] at h0'
  exact absurd h0' (by decide)

end Components

section EtaleCover

variable {K : Type u} [Field K]

/-- **Étale maps preserve nodal curves over an algebraically closed field**: components keep
dimension one, smooth points stay smooth, ordinary double points stay ordinary double
points. -/
theorem IsNodalFiber.of_etale [IsAlgClosed K] {Y Y' : Scheme.{u}} {q' : Y' ⟶ Spec (.of K)}
    [LocallyOfFiniteType q'] (e : Y ⟶ Y') [Etale e] (h : IsNodalFiber q') :
    IsNodalFiber (e ≫ q') where
  pure Z hZ := component_dimension_of_etale (q' := q') e hZ
    (h.pure _ (genericPoint_image_mem_irreducibleComponents e hZ))
  nodes y hy := by
    have hey := isClosed_image_of_isClosed (q := e ≫ q') e rfl hy
    have := isIso_residueFieldMap_of_isClosed (q := e ≫ q') e rfl hy
    rcases h.nodes (e y) hey with hs | hn
    · exact Or.inl (isSmoothAt_comp (isSmoothAt_of_smooth e y) hs)
    · exact Or.inr (isGeometricOrdinaryDoublePoint_of_etale e q' y hn)

/-- **Nodal curves over a field are local**: if `Y` is covered by open subschemes which are
nodal curves over `K`, then so is `Y`. -/
theorem IsNodalFiber.of_cover {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K))
    (h : ∀ y : Y, ∃ (V : Scheme.{u}) (j : V ⟶ Y) (_ : IsOpenImmersion j),
      y ∈ Set.range j ∧ IsNodalFiber (j ≫ q)) : IsNodalFiber q where
  nodes y hy := by
    obtain ⟨V, j, hj, ⟨v, rfl⟩, hV⟩ := h y
    have hv : IsClosed ({v} : Set V) := by
      have : ({v} : Set V) = j ⁻¹' {j v} := by
        ext w
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        exact ⟨fun h ↦ h ▸ rfl, fun h ↦ j.isOpenEmbedding.injective h⟩
      rw [this]
      exact hy.preimage j.continuous
    rcases hV.nodes v hv with hs | hn
    · exact Or.inl (isSmoothAt_of_isOpenImmersion_comp j hs)
    · exact Or.inr (isGeometricOrdinaryDoublePoint_of_isOpenImmersion j q v hn)
  pure Z hZ := by
    have hZc := isClosed_of_mem_irreducibleComponents Z hZ
    have hζ : IsGenericPoint hZ.1.genericPoint Z := hZ.1.isGenericPoint_genericPoint hZc
    have : QuasiSober Z := hZc.isClosedEmbedding_subtypeVal.quasiSober
    -- the trace of `Z` on a chart is a component of the chart, of dimension one
    have hchart : ∀ (V : Scheme.{u}) (j : V ⟶ Y) [IsOpenImmersion j], IsNodalFiber (j ≫ q) →
        (Z ∩ Set.range j).Nonempty → topologicalKrullDim (j ⁻¹' Z) = 1 := by
      intro V j _ hV hne
      exact hV.pure _ (preimage_mem_irreducibleComponents hZ j.isOpenEmbedding hne)
    apply le_antisymm
    · refine topologicalKrullDim_le_of_isOpenEmbedding_cover fun z ↦ ?_
      obtain ⟨V, j, hj, ⟨v, hv⟩, hV⟩ := h z.1
      have hvZ : v ∈ j ⁻¹' Z := by rw [Set.mem_preimage, hv]; exact z.2
      have : QuasiSober (j ⁻¹' Z) :=
        (hZc.preimage j.continuous).isClosedEmbedding_subtypeVal.quasiSober
      refine ⟨j ⁻¹' Z, inferInstance, inferInstance, inferInstance, Z.restrictPreimage j,
        j.isOpenEmbedding.restrictPreimage Z, ⟨⟨v, hvZ⟩, Subtype.ext hv⟩, ?_⟩
      exact (hchart V j hV ⟨z.1, z.2, v, hv⟩).le
    · obtain ⟨V, j, hj, ⟨v, hv⟩, hV⟩ := h hZ.1.genericPoint
      have h1 := hchart V j hV ⟨_, hζ.mem, v, hv⟩
      rw [← h1]
      exact (j.isOpenEmbedding.restrictPreimage Z).isInducing.topologicalKrullDim_le

end EtaleCover


section PullbackCompMap

variable {C C' S T : Scheme.{u}}

/-- The morphism `C' ×_S T ⟶ C ×_S T` induced by `β : C' ⟶ C` over `g : C ⟶ S`; for a
geometric point `a : Spec K ⟶ S` this is the map `β_a : C'_a ⟶ C_a` of geometric fibres. -/
def pullbackCompMap (β : C' ⟶ C) (g : C ⟶ S) (a : T ⟶ S) :
    pullback (β ≫ g) a ⟶ pullback g a :=
  pullback.map (β ≫ g) a g a β (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem pullbackCompMap_snd (β : C' ⟶ C) (g : C ⟶ S) (a : T ⟶ S) :
    pullbackCompMap β g a ≫ pullback.snd g a = pullback.snd (β ≫ g) a := by
  unfold pullbackCompMap
  rw [pullback.lift_snd, Category.comp_id]

@[reassoc (attr := simp)]
theorem pullbackCompMap_fst (β : C' ⟶ C) (g : C ⟶ S) (a : T ⟶ S) :
    pullbackCompMap β g a ≫ pullback.fst g a = pullback.fst (β ≫ g) a ≫ β := by
  unfold pullbackCompMap
  rw [pullback.lift_fst]

/-- `pullbackCompMap β g a` is the base change of `β` along `C ×_S T ⟶ C`. -/
theorem pullbackCompMap_eq (β : C' ⟶ C) (g : C ⟶ S) (a : T ⟶ S) :
    pullbackCompMap β g a =
      (pullbackRightPullbackFstIso g a β).inv ≫ pullback.snd β (pullback.fst g a) := by
  apply pullback.hom_ext <;> simp

instance etale_pullbackCompMap (β : C' ⟶ C) [Etale β] (g : C ⟶ S) (a : T ⟶ S) :
    Etale (pullbackCompMap β g a) := by
  rw [pullbackCompMap_eq]
  infer_instance

instance isOpenImmersion_pullbackCompMap (β : C' ⟶ C) [IsOpenImmersion β] (g : C ⟶ S)
    (a : T ⟶ S) : IsOpenImmersion (pullbackCompMap β g a) := by
  rw [pullbackCompMap_eq]
  infer_instance

instance isIso_pullbackCompMap (β : C' ⟶ C) [IsIso β] (g : C ⟶ S) (a : T ⟶ S) :
    IsIso (pullbackCompMap β g a) := by
  unfold pullbackCompMap
  infer_instance

/-- For an open immersion `β`, `pullbackCompMap β g a` is the inclusion of the preimage of the
image of `β`. -/
theorem range_pullbackCompMap (β : C' ⟶ C) [IsOpenImmersion β] (g : C ⟶ S) (a : T ⟶ S) :
    Set.range (pullbackCompMap β g a) = pullback.fst g a ⁻¹' Set.range β := by
  rw [pullbackCompMap_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (pullbackRightPullbackFstIso g a β).inv.surjective, Set.image_univ,
    IsOpenImmersion.range_pullbackSnd]
  rfl

end PullbackCompMap

section NodalCurve

variable {C S : Scheme.{u}}

/-- **Étale maps preserve nodal curves** (restriction to open subschemes in particular). -/
theorem IsNodalCurve.etale_comp {U : Scheme.{u}} (e : U ⟶ C) [Etale e] (g : C ⟶ S)
    [IsNodalCurve g] : IsNodalCurve (e ≫ g) := by
  refine IsNodalCurve.of_isNodalFiber _ fun K _ _ a ↦ ?_
  have h := (IsNodalCurve.isNodalFiber g K a).of_etale (pullbackCompMap e g a)
  rwa [pullbackCompMap_snd] at h

/-- **Nodal curves are local on the source.** -/
theorem IsNodalCurve.of_openCover (g : C ⟶ S)
    (h : ∀ x : C, ∃ U : C.Opens, x ∈ U ∧ IsNodalCurve (U.ι ≫ g)) : IsNodalCurve g := by
  choose U hxU hU using h
  have hsup : iSup U = ⊤ := eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩
  have : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{u}) (Q := RingHom.Flat)
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
      (Q := RingHom.FinitePresentation)
  have : Flat g := IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat.{u}) U hsup
    fun x ↦ (hU x).toFlat
  have : LocallyOfFinitePresentation g :=
    IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFinitePresentation.{u}) U hsup
      fun x ↦ (hU x).toLocallyOfFinitePresentation
  refine IsNodalCurve.of_isNodalFiber _ fun K _ _ a ↦ ?_
  refine IsNodalFiber.of_cover _ fun y ↦ ?_
  let x := pullback.fst g a y
  have := hU x
  refine ⟨_, pullbackCompMap (U x).ι g a, inferInstance, ?_, ?_⟩
  · rw [range_pullbackCompMap, Scheme.Opens.range_ι]
    exact hxU x
  · rw [pullbackCompMap_snd]
    exact IsNodalCurve.isNodalFiber _ K a

/-- **Nodal curves stay nodal over a larger base containing the base as an open
subscheme.** -/
theorem IsNodalCurve.comp_isOpenImmersion {T : Scheme.{u}} (g : C ⟶ S) [IsNodalCurve g]
    (ι : S ⟶ T) [IsOpenImmersion ι] : IsNodalCurve (g ≫ ι) := by
  refine IsNodalCurve.of_isNodalFiber _ fun K _ _ a ↦ ?_
  by_cases ha : Set.range a ⊆ Set.range ι
  · obtain ⟨a', rfl⟩ : ∃ a', a' ≫ ι = a := ⟨IsOpenImmersion.lift ι a ha,
      IsOpenImmersion.lift_fac ι a ha⟩
    let F : pullback g a' ⟶ pullback (g ≫ ι) (a' ≫ ι) :=
      pullback.map g a' (g ≫ ι) (a' ≫ ι) (𝟙 _) (𝟙 _) ι (by simp) (by simp)
    have hF : IsIso F := by
      refine ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _) ?_, ?_, ?_⟩
      · rw [← cancel_mono ι, Category.assoc, Category.assoc, pullback.condition]
      · apply pullback.hom_ext
        · simp only [F, Category.assoc, pullback.lift_fst, Category.id_comp, Category.comp_id]
        · simp only [F, Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]
      · apply pullback.hom_ext
        · simp only [F, Category.assoc, pullback.lift_fst, Category.id_comp, Category.comp_id]
        · simp only [F, Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]
    have h := (IsNodalCurve.isNodalFiber g K a').of_etale (inv F)
    have hc : inv F ≫ pullback.snd g a' = pullback.snd (g ≫ ι) (a' ≫ ι) := by
      rw [IsIso.inv_comp_eq]
      simp only [F]
      rw [pullback.lift_snd, Category.comp_id]
    rwa [hc] at h
  · have hempty : IsEmpty ↑(pullback (C := Scheme.{u}) (g ≫ ι) a) := by
      refine ⟨fun y ↦ ha ?_⟩
      rintro _ ⟨b, rfl⟩
      have hb : b = pullback.snd (g ≫ ι) a y := Subsingleton.elim _ _
      rw [hb, ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact ⟨fun Z hZ ↦ (hZ.1.1.ne_empty (Set.eq_empty_of_isEmpty Z)).elim,
      fun y ↦ (hempty.false y).elim⟩

/-- **Base change of nodal curves.** -/
instance isNodalCurve_pullback_snd {S' : Scheme.{u}} (g : C ⟶ S) [IsNodalCurve g]
    (ψ : S' ⟶ S) : IsNodalCurve (pullback.snd g ψ) := by
  refine IsNodalCurve.of_isNodalFiber _ fun K _ _ a ↦ ?_
  have h := (IsNodalCurve.isNodalFiber g K (a ≫ ψ)).of_etale
    (pullbackLeftPullbackSndIso g ψ a).hom
  rwa [pullbackLeftPullbackSndIso_hom_snd] at h

end NodalCurve


section BaseChange

variable {C S S' : Scheme.{u}}

/-- The preimage of the smooth locus under the projection of a base change is contained in the
smooth locus of the base change. -/
theorem preimage_smoothLocus_le_smoothLocus_pullback_snd (g : C ⟶ S)
    [LocallyOfFinitePresentation g] (ψ : S' ⟶ S) :
    pullback.fst g ψ ⁻¹ᵁ g.smoothLocus ≤ (pullback.snd g ψ).smoothLocus := by
  intro x hx
  have hW : Smooth (g.smoothLocus.ι ≫ g) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      Scheme.Opens.ι_preimage_self]
  obtain ⟨z, rfl⟩ : x ∈ Set.range (pullbackCompMap g.smoothLocus.ι g ψ) := by
    rw [range_pullbackCompMap, Scheme.Opens.range_ι]
    exact hx
  have hz : IsSmoothAt (pullbackCompMap g.smoothLocus.ι g ψ ≫ pullback.snd g ψ) z := by
    rw [pullbackCompMap_snd]
    exact isSmoothAt_of_smooth _ z
  exact isSmoothAt_of_isOpenImmersion_comp _ hz

/-- The base change `D ×_C (C ×_S S') ⟶ S'` of a closed subscheme `D ⊆ C` is, up to
isomorphism, the base change of `D ⟶ S` along `ψ`. -/
theorem comap_fst_subschemeι_snd_eq (g : C ⟶ S) (ψ : S' ⟶ S) (D : C.IdealSheafData) :
    (D.comap (pullback.fst g ψ)).subschemeι ≫ pullback.snd g ψ =
      (D.comapIso _).hom ≫ (pullbackSymmetry _ _).hom ≫
        (pullbackRightPullbackFstIso g ψ D.subschemeι).hom ≫
          pullback.snd (D.subschemeι ≫ g) ψ := by
  rw [pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- Flatness of the marks is stable under base change. -/
theorem flat_comap_fst_subschemeι_snd (g : C ⟶ S) (ψ : S' ⟶ S) (D : C.IdealSheafData)
    [Flat (D.subschemeι ≫ g)] :
    Flat ((D.comap (pullback.fst g ψ)).subschemeι ≫ pullback.snd g ψ) := by
  rw [comap_fst_subschemeι_snd_eq]
  infer_instance

/-- **Base change of semi-stable pairs** (Temkin T:1686–1690). -/
theorem IsSemistablePair.pullback {g : C ⟶ S} {D : C.IdealSheafData}
    (h : IsSemistablePair g D) (ψ : S' ⟶ S) :
    IsSemistablePair (pullback.snd g ψ) (D.comap (pullback.fst g ψ)) where
  nodal := by
    have := h.nodal
    infer_instance
  etale := by
    have := h.etale
    rw [comap_fst_subschemeι_snd_eq]
    infer_instance
  smoothAlong x hx := by
    have := h.nodal
    have hx' : pullback.fst g ψ x ∈ (D.support : Set C) := by
      rw [Scheme.IdealSheafData.support_comap] at hx
      exact hx
    exact preimage_smoothLocus_le_smoothLocus_pullback_snd g ψ (h.smoothAlong _ hx')

/-- **Semi-stable pairs restrict along étale maps**, in particular to open subschemes. -/
theorem IsSemistablePair.etale_comp {U : Scheme.{u}} {g : C ⟶ S} {D : C.IdealSheafData}
    (h : IsSemistablePair g D) (e : U ⟶ C) [Etale e] :
    IsSemistablePair (e ≫ g) (D.comap e) where
  nodal := by
    have := h.nodal
    exact IsNodalCurve.etale_comp e g
  etale := by
    have := h.etale
    have he : (D.comap e).subschemeι ≫ e ≫ g =
        (D.comapIso e).hom ≫ pullback.snd e D.subschemeι ≫ D.subschemeι ≫ g := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst_assoc, pullback.condition_assoc]
    rw [he]
    infer_instance
  smoothAlong x hx := by
    have hx' : e x ∈ (D.support : Set C) := by
      rw [Scheme.IdealSheafData.support_comap] at hx
      exact hx
    exact isSmoothAt_comp (isSmoothAt_of_smooth e x) (h.smoothAlong _ hx')

end BaseChange


section Marks

variable {C C' C'' S : Scheme.{u}}

/-- `f : C' ⟶ C` maps the closed subscheme `D'` into `D`: `D' ⊆ f⁻¹(D)` as closed subschemes,
i.e. the pullback of the ideal of `D` is contained in the ideal of `D'`. Then `f` is a morphism
`(C', D') ⟶ (C, D)` of multipointed curves in the sense of Temkin §1.2 (T:1675), with
restriction `MapsMarks.restrict`. -/
def MapsMarks (f : C' ⟶ C) (D' : C'.IdealSheafData) (D : C.IdealSheafData) : Prop :=
  D.comap f ≤ D'

/-- The restriction `f_D : D' ⟶ D` of a morphism of multipointed curves. -/
def MapsMarks.restrict {f : C' ⟶ C} {D' : C'.IdealSheafData} {D : C.IdealSheafData}
    (h : MapsMarks f D' D) : D'.subscheme ⟶ D.subscheme :=
  D'.subschemeMap D f (Scheme.IdealSheafData.le_map_iff_comap_le.mpr h)

@[reassoc (attr := simp)]
theorem MapsMarks.restrict_subschemeι {f : C' ⟶ C} {D' : C'.IdealSheafData}
    {D : C.IdealSheafData} (h : MapsMarks f D' D) :
    h.restrict ≫ D.subschemeι = D'.subschemeι ≫ f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

theorem MapsMarks.id (D : C.IdealSheafData) : MapsMarks (𝟙 C) D D := by
  unfold MapsMarks
  rw [Scheme.IdealSheafData.comap_id]

theorem MapsMarks.comp {f : C' ⟶ C} {h : C'' ⟶ C'} {D : C.IdealSheafData}
    {D' : C'.IdealSheafData} {D'' : C''.IdealSheafData} (hf : MapsMarks f D' D)
    (hh : MapsMarks h D'' D') : MapsMarks (h ≫ f) D'' D := by
  unfold MapsMarks at *
  rw [Scheme.IdealSheafData.comap_comp]
  exact (Scheme.IdealSheafData.comap_mono h hf).trans hh

theorem MapsMarks.support_subset {f : C' ⟶ C} {D' : C'.IdealSheafData} {D : C.IdealSheafData}
    (h : MapsMarks f D' D) : (D'.support : Set C') ⊆ f ⁻¹' (D.support : Set C) := by
  intro x hx
  have : x ∈ ((D.comap f).support : Set C') := Scheme.IdealSheafData.support_antitone h hx
  rwa [Scheme.IdealSheafData.support_comap] at this

theorem mapsMarks_comap (f : C' ⟶ C) (D : C.IdealSheafData) : MapsMarks f (D.comap f) D :=
  le_rfl

/-- **The marks lie in the closure of the generic marks** when they are flat over an
irreducible base: every point of `D` is a specialization of a point of `D` over the generic
point. -/
theorem support_subset_closure_genericMarks [IrreducibleSpace S] (g : C ⟶ S)
    (D : C.IdealSheafData) [Flat (D.subschemeι ≫ g)] :
    (D.support : Set C) ⊆ closure ((D.support : Set C) ∩ g ⁻¹' {genericPoint S}) := by
  intro x hx
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨d, rfl⟩ := hx
  obtain ⟨d', hd', hd'η⟩ :=
    Flat.generalizingMap (D.subschemeι ≫ g) (genericPoint_specializes ((D.subschemeι ≫ g) d))
  have hmem : D.subschemeι d' ∈ (D.support : Set C) ∩ g ⁻¹' {genericPoint S} := by
    refine ⟨by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨d', rfl⟩, ?_⟩
    simpa using hd'η
  exact closure_mono (Set.singleton_subset_iff.mpr hmem)
    ((hd'.map D.subschemeι.continuous).mem_closure)

end Marks

section Modifications

variable {X Y C C' S : Scheme.{u}}

/-- A *modification* in the sense of Temkin (§1.2, T:1677; §3, T:2241): a proper morphism
inducing an isomorphism between schematically dense open subschemes, i.e. there is an open
`V ⊆ Y` such that `V` and `f⁻¹(V)` are schematically dense (their inclusions are
scheme-theoretically dominant) and `f⁻¹(V) ⟶ V` is an isomorphism. -/
structure IsSchematicModification (f : X ⟶ Y) : Prop extends IsProper f where
  exists_isIso : ∃ V : Y.Opens, IsSchemeTheoreticallyDominant V.ι ∧
    IsSchemeTheoreticallyDominant (f ⁻¹ᵁ V).ι ∧ IsIso (f ∣_ V)

/-- Isomorphisms are modifications. -/
theorem IsSchematicModification.of_isIso (f : X ⟶ Y) [IsIso f] : IsSchematicModification f where
  exists_isIso := by
    have hY : IsIso (⊤ : Y.Opens).ι := inferInstanceAs (IsIso Y.topIso.hom)
    have hX : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
    refine ⟨⊤, inferInstance, ?_, inferInstance⟩
    rw [Scheme.Hom.preimage_top]
    infer_instance

/-- A schematically dense open subscheme of a nonempty scheme is nonempty. -/
theorem nonempty_of_isSchemeTheoreticallyDominant [Nonempty Y] (V : Y.Opens)
    [IsSchemeTheoreticallyDominant V.ι] : (V : Set Y).Nonempty := by
  by_contra hV
  rw [Set.not_nonempty_iff_eq_empty] at hV
  have : IsEmpty V.toScheme := ⟨fun x ↦ by
    have hx : x.1 ∈ (V : Set Y) := x.2
    rw [hV] at hx
    exact hx⟩
  have htop := V.ι.ker_eq_top_iff_isEmpty.mpr this
  rw [V.ι.ker_eq_bot] at htop
  obtain ⟨y⟩ := ‹Nonempty Y›
  have hy : y ∈ ((⊥ : Y.IdealSheafData).support : Set Y) := by
    rw [Scheme.IdealSheafData.support_bot]
    trivial
  rw [htop, Scheme.IdealSheafData.support_top] at hy
  exact hy

/-- **Modifications of integral schemes**: between integral schemes, a modification in
Temkin's sense is a modification in the sense of de Jong 2.17
(`DeJongAlterations.IsModification`). -/
theorem IsSchematicModification.isModification [IsIntegral X] [IsIntegral Y] {f : X ⟶ Y}
    (h : IsSchematicModification f) : IsModification f where
  toIsProper := h.toIsProper
  sourceIntegral := inferInstance
  targetIntegral := inferInstance
  birational := by
    obtain ⟨V, hV, hV', hiso⟩ := h.exists_isIso
    refine ⟨⟨f ⁻¹ᵁ V,
      (f ⁻¹ᵁ V).isOpen.dense (nonempty_of_isSchemeTheoreticallyDominant _), V,
      V.isOpen.dense (nonempty_of_isSchemeTheoreticallyDominant _), asIso (f ∣_ V)⟩, ?_⟩
    change (f ∣_ V) ≫ V.ι ≫ 𝟙 Y = (f ⁻¹ᵁ V).ι ≫ f
    rw [Category.comp_id, morphismRestrict_ι]

/-- A nonempty open subscheme of an integral scheme is schematically dense. -/
theorem isSchemeTheoreticallyDominant_ι_of_nonempty [IsIntegral Y] (V : Y.Opens)
    (hV : (V : Set Y).Nonempty) : IsSchemeTheoreticallyDominant V.ι := by
  refine ⟨le_bot_iff.mp fun W ↦ ?_⟩
  refine (V.ι.ideal_ker_le W).trans fun a ha ↦ ?_
  change a = 0
  by_cases hW : (W.1 : Set Y).Nonempty
  · have hne : Nonempty (V.ι ''ᵁ V.ι ⁻¹ᵁ W.1) := by
      obtain ⟨y, hyV, hyW⟩ := nonempty_preirreducible_inter V.isOpen W.1.isOpen hV hW
      exact ⟨⟨y, ⟨⟨y, hyV⟩, hyW, rfl⟩⟩⟩
    rw [RingHom.mem_ker, Scheme.Opens.ι_app] at ha
    exact map_injective_of_isIntegral Y _ (ha.trans (map_zero _).symm)
  · have hbot : W.1 = ⊥ := by
      apply Opens.ext
      rw [Opens.coe_bot]
      exact Set.not_nonempty_iff_eq_empty.mp hW
    have : Subsingleton Γ(Y, W.1) := hbot ▸ inferInstance
    exact Subsingleton.elim _ _

/-- **De Jong's modifications are modifications in Temkin's sense**: a modification
`DeJongAlterations.IsModification f` of integral schemes is proper and an isomorphism over a
dense, hence schematically dense, open subscheme of the target whose preimage is the dense
source open of the birational partial isomorphism. -/
theorem IsModification.isSchematicModification {f : X ⟶ Y} [hf : IsModification f] :
    IsSchematicModification f where
  toIsProper := inferInstance
  exists_isIso := by
    have := hf.sourceIntegral
    have := hf.targetIntegral
    obtain ⟨e, he⟩ := hf.birational
    have he' : e.iso.hom ≫ e.target.ι = e.source.ι ≫ f := by
      simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using he
    set V := e.target
    have hle : e.source ≤ f ⁻¹ᵁ V := by
      intro x hx
      change f x ∈ V
      have := congrArg (fun φ : e.source.toScheme ⟶ Y ↦ φ ⟨x, hx⟩) he'
      have h1 : (e.source.ι ≫ f) ⟨x, hx⟩ = f x := rfl
      have h2 : (e.iso.hom ≫ e.target.ι) ⟨x, hx⟩ = (e.iso.hom ⟨x, hx⟩).1 := rfl
      simp only at this
      rw [h1, h2] at this
      rw [← this]
      exact (e.iso.hom ⟨x, hx⟩).2
    -- the section `V ⟶ f⁻¹(V)` of `f ∣_ V` given by the partial isomorphism
    let sec : V.toScheme ⟶ (f ⁻¹ᵁ V).toScheme := e.iso.inv ≫ X.homOfLE hle
    have hsec : sec ≫ (f ∣_ V) = 𝟙 _ := by
      rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, Category.id_comp]
      simp only [sec, Category.assoc, Scheme.homOfLE_ι_assoc]
      rw [← he', Iso.inv_hom_id_assoc]
    have : IsClosedImmersion sec := by
      have : IsClosedImmersion (sec ≫ (f ∣_ V)) := by rw [hsec]; infer_instance
      exact IsClosedImmersion.of_comp sec (f ∣_ V)
    have hne : (e.source : Set X).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      exact (e.dense_source.nonempty_iff.mpr inferInstance).ne_empty h
    have : Nonempty (f ⁻¹ᵁ V).toScheme := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨⟨x, hle hx⟩⟩
    have hsurj : Function.Surjective sec := by
      have hcl : IsClopen (Set.range sec) :=
        ⟨sec.isClosedEmbedding.isClosed_range, sec.isOpenEmbedding.isOpen_range⟩
      have hrange : Set.range sec = Set.univ := by
        refine hcl.eq_univ ?_
        obtain ⟨v⟩ : Nonempty V.toScheme := by
          obtain ⟨x, hx⟩ := hne
          exact ⟨e.iso.hom ⟨x, hx⟩⟩
        exact ⟨_, v, rfl⟩
      exact Set.range_eq_univ.mp hrange
    have : IsIso sec := by
      rw [isIso_iff_isOpenImmersion_and_epi_base]
      exact ⟨inferInstance, (TopCat.epi_iff_surjective _).mpr hsurj⟩
    have hiso : IsIso (f ∣_ V) := by
      have : IsIso (sec ≫ (f ∣_ V)) := by rw [hsec]; infer_instance
      exact IsIso.of_isIso_comp_left sec (f ∣_ V)
    obtain ⟨x, hx⟩ := hne
    exact ⟨V, isSchemeTheoreticallyDominant_ι_of_nonempty V ⟨f x, hle hx⟩,
      isSchemeTheoreticallyDominant_ι_of_nonempty _ ⟨x, hle hx⟩, hiso⟩

/-- The morphism `f_s : C'_s ⟶ C_s` of fibres over `s ∈ S` induced by `f : C' ⟶ C` over
`g : C ⟶ S`. -/
def fiberMap (f : C' ⟶ C) (g : C ⟶ S) (s : S) : (f ≫ g).fiber s ⟶ g.fiber s :=
  pullbackCompMap f g (S.fromSpecResidueField s)

@[reassoc (attr := simp)]
theorem fiberMap_fiberι (f : C' ⟶ C) (g : C ⟶ S) (s : S) :
    fiberMap f g s ≫ g.fiberι s = (f ≫ g).fiberι s ≫ f :=
  pullbackCompMap_fst f g _

@[reassoc (attr := simp)]
theorem fiberMap_fiberToSpecResidueField (f : C' ⟶ C) (g : C ⟶ S) (s : S) :
    fiberMap f g s ≫ g.fiberToSpecResidueField s = (f ≫ g).fiberToSpecResidueField s :=
  pullbackCompMap_snd f g _

instance isIso_fiberMap (f : C' ⟶ C) [IsIso f] (g : C ⟶ S) (s : S) : IsIso (fiberMap f g s) :=
  inferInstanceAs (IsIso (pullbackCompMap f g (S.fromSpecResidueField s)))

/-- An *η-modification* (Temkin §3, T:2243): a modification `f : C' ⟶ C` which is an
isomorphism on the generic fibres over the irreducible base `S`. -/
structure IsEtaModification (f : C' ⟶ C) (g : C ⟶ S) [IrreducibleSpace S] : Prop
    extends IsSchematicModification f where
  isIso_fiberMap : IsIso (fiberMap f g (genericPoint S))

/-- Isomorphisms are η-modifications. -/
theorem IsEtaModification.of_isIso [IrreducibleSpace S] (f : C' ⟶ C) [IsIso f] (g : C ⟶ S) :
    IsEtaModification f g where
  toIsSchematicModification := .of_isIso f
  isIso_fiberMap := inferInstance

end Modifications

section Stable

variable {C C' S : Scheme.{u}}

/-- An *exceptional component* (Temkin §1.2, T:1687–1690; Appendix B, T:4459–4462) of the
geometric fibre `C'_a` of `β ≫ g` over `a : Spec K ⟶ S`: an irreducible component `Z` which is
the image of a closed immersion `ℙ¹_K ⟶ C'_a` over `K` (as `ℙ¹_K` is reduced, this says that
`Z` with its reduced structure is isomorphic to `ℙ¹_K`), is contracted to a point by
`β_a : C'_a ⟶ C_a`, and contains at most two points lying on the marks `D'` or at which
`C'_a ⟶ Spec K` is not smooth. -/
structure IsExceptionalComponent (β : C' ⟶ C) (g : C ⟶ S) (D' : C'.IdealSheafData)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    (Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a)) : Prop where
  mem_irreducibleComponents : Z ∈ irreducibleComponents (pullback (C := Scheme.{u}) (β ≫ g) a)
  exists_projectiveLine : ∃ i : projectiveSpace K 1 ⟶ pullback (C := Scheme.{u}) (β ≫ g) a,
    IsClosedImmersion i ∧ i ≫ pullback.snd (β ≫ g) a = projectiveSpaceStructure K 1 ∧
      Set.range i = Z
  contracted : (pullbackCompMap β g a '' Z).Subsingleton
  encard_special_le_two : (Z ∩ (pullback.fst (β ≫ g) a ⁻¹' (D'.support : Set C') ∪
    {y | ¬ IsSmoothAt (pullback.snd (β ≫ g) a) y})).encard ≤ 2

/-- **Exceptional components transport along isomorphisms** of geometric fibres compatible with
the structure maps to `Spec K`, the maps of geometric fibres and the marks. -/
theorem IsExceptionalComponent.of_iso {C₁ C₁' S₁ C₂ C₂' S₂ : Scheme.{u}} {β₁ : C₁' ⟶ C₁}
    {g₁ : C₁ ⟶ S₁} {D₁ : C₁'.IdealSheafData} {β₂ : C₂' ⟶ C₂} {g₂ : C₂ ⟶ S₂}
    {D₂ : C₂'.IdealSheafData} {K : Type u} [Field K] {a₁ : Spec (.of K) ⟶ S₁}
    {a₂ : Spec (.of K) ⟶ S₂}
    (φ : pullback (β₁ ≫ g₁) a₁ ≅ pullback (β₂ ≫ g₂) a₂) (χ : pullback g₁ a₁ ⟶ pullback g₂ a₂)
    (hsnd : φ.hom ≫ pullback.snd (β₂ ≫ g₂) a₂ = pullback.snd (β₁ ≫ g₁) a₁)
    (hmap : φ.hom ≫ pullbackCompMap β₂ g₂ a₂ = pullbackCompMap β₁ g₁ a₁ ≫ χ)
    (hmarks : ∀ y, pullback.fst (β₂ ≫ g₂) a₂ (φ.hom y) ∈ (D₂.support : Set C₂') ↔
      pullback.fst (β₁ ≫ g₁) a₁ y ∈ (D₁.support : Set C₁'))
    {Z : Set (pullback (C := Scheme.{u}) (β₁ ≫ g₁) a₁)} (h : IsExceptionalComponent β₁ g₁ D₁ a₁ Z) :
    IsExceptionalComponent β₂ g₂ D₂ a₂ (φ.hom '' Z) where
  mem_irreducibleComponents := by
    refine image_mem_irreducibleComponents_of_isPreirreducible_fiber φ.hom φ.hom.continuous
      φ.hom.homeomorph.isOpenMap (fun x ↦ ?_) φ.hom.homeomorph.surjective
      h.mem_irreducibleComponents
    exact (Set.subsingleton_singleton.preimage φ.hom.homeomorph.injective).isPreirreducible
  exists_projectiveLine := by
    obtain ⟨i, hi, hiK, hrange⟩ := h.exists_projectiveLine
    refine ⟨i ≫ φ.hom, inferInstance, by rw [Category.assoc, hsnd, hiK], ?_⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
  contracted := by
    rw [Set.image_image]
    have : (fun y ↦ pullbackCompMap β₂ g₂ a₂ (φ.hom y)) = fun y ↦ χ (pullbackCompMap β₁ g₁ a₁ y) :=
      funext fun y ↦ by
        rw [← Scheme.Hom.comp_apply, hmap, Scheme.Hom.comp_apply]
    rw [this, ← Set.image_image]
    exact h.contracted.image _
  encard_special_le_two := by
    have hsm : ∀ y, IsSmoothAt (pullback.snd (β₂ ≫ g₂) a₂) (φ.hom y) ↔
        IsSmoothAt (pullback.snd (β₁ ≫ g₁) a₁) y := by
      intro y
      rw [← hsnd]
      exact ⟨fun h' ↦ isSmoothAt_comp (isSmoothAt_of_smooth φ.hom y) h',
        fun h' ↦ isSmoothAt_of_isOpenImmersion_comp φ.hom h'⟩
    have hA : φ.hom '' Z ∩ (pullback.fst (β₂ ≫ g₂) a₂ ⁻¹' (D₂.support : Set C₂') ∪
        {y | ¬ IsSmoothAt (pullback.snd (β₂ ≫ g₂) a₂) y}) =
        φ.hom '' (Z ∩ (pullback.fst (β₁ ≫ g₁) a₁ ⁻¹' (D₁.support : Set C₁') ∪
          {y | ¬ IsSmoothAt (pullback.snd (β₁ ≫ g₁) a₁) y})) := by
      ext w
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hw⟩
        refine ⟨y, ⟨hy, ?_⟩, rfl⟩
        rcases hw with hw | hw
        · exact Or.inl ((hmarks y).mp hw)
        · exact Or.inr fun hs ↦ hw ((hsm y).mpr hs)
      · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
        refine ⟨⟨y, hy, rfl⟩, ?_⟩
        rcases hy' with hy' | hy'
        · exact Or.inl ((hmarks y).mpr hy')
        · exact Or.inr fun hs ↦ hy' ((hsm y).mp hs)
    have hinj : Function.Injective φ.hom := φ.hom.homeomorph.injective
    rw [hA, Set.InjOn.encard_image hinj.injOn]
    exact h.encard_special_le_two

/-- The *transported marks* of `β : C' ⟶ C` along `D ⊆ C` at `s ∈ S`: the schematic closure
in `C'` of `β_s⁻¹(D_s) ⊆ C'_s` (Temkin Remark 4.1, T:2810). -/
def genericMarksClosure (β : C' ⟶ C) (g : C ⟶ S) (D : C.IdealSheafData) (s : S) :
    C'.IdealSheafData :=
  (((DeJong.fiberMarks g D s).comap (fiberMap β g s)).subschemeι ≫ (β ≫ g).fiberι s).ker

/-- A *stable η-modification* of `(C, D)` over the irreducible base `S` (Temkin §1.2,
T:1685–1690, with Remark 4.1, T:2810): an η-modification `β : C' ⟶ C` whose source, with the
transported marks `D'`, is a semi-stable pair without exceptional components in any geometric
fibre. -/
structure IsStableModification (β : C' ⟶ C) (g : C ⟶ S) (D : C.IdealSheafData)
    (D' : C'.IdealSheafData) [IrreducibleSpace S] : Prop extends IsEtaModification β g where
  marks_eq : D' = genericMarksClosure β g D (genericPoint S)
  isSemistablePair : IsSemistablePair (β ≫ g) D'
  not_isExceptionalComponent : ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S) (Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a)),
    ¬ IsExceptionalComponent β g D' a Z

/-- **Isomorphisms have no exceptional components**: the geometric fibre map is injective and
components of geometric fibres of nodal curves are not points. -/
theorem not_isExceptionalComponent_of_isIso (β : C' ⟶ C) [IsIso β] (g : C ⟶ S)
    [IsNodalCurve (β ≫ g)] (D' : C'.IdealSheafData) (K : Type u) [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S) (Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a)) :
    ¬ IsExceptionalComponent β g D' a Z := by
  intro h
  have hdim := IsNodalCurve.pureGeometricFibers (g := β ≫ g) K a Z h.mem_irreducibleComponents
  have hinj : Function.Injective (pullbackCompMap β g a) :=
    (pullbackCompMap β g a).isOpenEmbedding.injective
  have hsub : Z.Subsingleton := fun x hx y hy ↦
    hinj (h.contracted ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
  have : Subsingleton Z := hsub.coe_sort
  have h0 := topologicalKrullDim_zero_of_discreteTopology Z
  rw [hdim] at h0
  exact absurd h0 (by decide)

/-- **Non-vacuity**: an isomorphism whose source, with the transported marks, is a semi-stable
pair is a stable η-modification. -/
theorem isStableModification_of_isIso [IrreducibleSpace S] (β : C' ⟶ C) [IsIso β] (g : C ⟶ S)
    (D : C.IdealSheafData)
    (h : IsSemistablePair (β ≫ g) (genericMarksClosure β g D (genericPoint S))) :
    IsStableModification β g D (genericMarksClosure β g D (genericPoint S)) where
  toIsEtaModification := .of_isIso β g
  marks_eq := rfl
  isSemistablePair := h
  not_isExceptionalComponent K _ _ a Z := by
    have := h.nodal
    exact not_isExceptionalComponent_of_isIso β g _ K a Z

/-- **Absence of exceptional components is stable under base change** (stability is a condition
on geometric fibres, Temkin T:1686–1690): if no geometric fibre of `β ≫ g` has an exceptional
component, the same holds for the base change of `(β, g, D')` along any `ψ : S' ⟶ S`. -/
theorem not_isExceptionalComponent_pullback {S' : Scheme.{u}} (β : C' ⟶ C) (g : C ⟶ S)
    (D' : C'.IdealSheafData) (ψ : S' ⟶ S)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
      (Z : Set (pullback (C := Scheme.{u}) (β ≫ g) a)), ¬ IsExceptionalComponent β g D' a Z)
    (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S')
    (Z : Set (pullback (C := Scheme.{u}) (pullbackCompMap β g ψ ≫ pullback.snd g ψ) a)) :
    ¬ IsExceptionalComponent (pullbackCompMap β g ψ) (pullback.snd g ψ)
      (D'.comap (pullback.fst (β ≫ g) ψ)) a Z := by
  intro hZ
  let φ : pullback (pullbackCompMap β g ψ ≫ pullback.snd g ψ) a ≅ pullback (β ≫ g) (a ≫ ψ) :=
    pullback.congrHom (pullbackCompMap_snd β g ψ) rfl ≪≫ pullbackLeftPullbackSndIso (β ≫ g) ψ a
  let χ : pullback (pullback.snd g ψ) a ⟶ pullback g (a ≫ ψ) :=
    (pullbackLeftPullbackSndIso g ψ a).hom
  have hfst : φ.hom ≫ pullback.fst (β ≫ g) (a ≫ ψ) =
      pullback.fst _ a ≫ pullback.fst (β ≫ g) ψ := by
    simp only [φ, Iso.trans_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      pullback.congrHom_hom]
    rw [pullback.lift_fst_assoc, Category.comp_id]
  have hsnd : φ.hom ≫ pullback.snd (β ≫ g) (a ≫ ψ) = pullback.snd _ a := by
    simp only [φ, Iso.trans_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      pullback.congrHom_hom]
    rw [pullback.lift_snd, Category.comp_id]
  refine h K (a ≫ ψ) _ (hZ.of_iso φ χ hsnd ?_ ?_)
  · apply pullback.hom_ext
    · simp only [χ, Category.assoc, pullbackCompMap_fst, pullbackLeftPullbackSndIso_hom_fst,
        pullbackCompMap_fst_assoc]
      rw [← Category.assoc, hfst, Category.assoc]
    · simp only [χ, Category.assoc, pullbackCompMap_snd, pullbackLeftPullbackSndIso_hom_snd]
      exact hsnd
  · intro y
    have := congrArg (fun m ↦ m y) hfst
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, Scheme.IdealSheafData.support_comap]
    rfl


theorem IsStableModification.mapsMarks [IrreducibleSpace S] {β : C' ⟶ C} {g : C ⟶ S}
    {D : C.IdealSheafData} {D' : C'.IdealSheafData} (h : IsStableModification β g D D') :
    MapsMarks β D' D := by
  rw [h.marks_eq]
  unfold MapsMarks genericMarksClosure
  set E := (DeJong.fiberMarks g D (genericPoint S)).comap (fiberMap β g (genericPoint S))
  rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.le_map_iff_comap_le,
    ← Scheme.IdealSheafData.comap_comp, Category.assoc, ← fiberMap_fiberι,
    ← Category.assoc, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
  change E.comap E.subschemeι ≤ ⊥
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_subschemeι]

/-- **Marks over the isomorphism locus.** Let `β` be a stable η-modification of `(C, D)` with
`D` flat over `S`, an isomorphism over `g⁻¹(U)` for a nonempty open `U ⊆ S`. Then a point of
`C'` over `U` lies on the marks `D'` if and only if its image lies on `D`. -/
theorem IsStableModification.support_iff_of_isIso [IrreducibleSpace S] {β : C' ⟶ C}
    {g : C ⟶ S} {D : C.IdealSheafData} {D' : C'.IdealSheafData}
    (h : IsStableModification β g D D') [Flat (D.subschemeι ≫ g)] (U : S.Opens)
    (hU : (U : Set S).Nonempty) (hiso : IsIso (β ∣_ (g ⁻¹ᵁ U))) (x : C')
    (hx : (β ≫ g) x ∈ U) : x ∈ (D'.support : Set C') ↔ β x ∈ (D.support : Set C) := by
  refine ⟨fun hx' ↦ h.mapsMarks.support_subset hx', fun hβx ↦ ?_⟩
  have hηU : genericPoint S ∈ U :=
    ((genericPoint_spec S).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  -- a generization of `β x` on `D` over the generic point
  rw [← Scheme.IdealSheafData.range_subschemeι] at hβx
  obtain ⟨d, hd⟩ := hβx
  obtain ⟨d₀, hd₀, hd₀η⟩ :=
    Flat.generalizingMap (D.subschemeι ≫ g) (genericPoint_specializes ((D.subschemeι ≫ g) d))
  set d' := D.subschemeι d₀
  have hd'η : g d' = genericPoint S := hd₀η
  have hd'x : d' ⤳ β x := hd ▸ hd₀.map D.subschemeι.continuous
  -- lift `d'` along the isomorphism over `g⁻¹(U)`
  set V := g ⁻¹ᵁ U
  have hd'V : d' ∈ V := by
    change g d' ∈ U
    rw [hd'η]
    exact hηU
  have hxV : x ∈ β ⁻¹ᵁ V := hx
  let φ := (β ∣_ V).homeomorph
  let x₀ : (β ⁻¹ᵁ V).toScheme := ⟨x, hxV⟩
  let y₀ : V.toScheme := ⟨β x, hx⟩
  let d₁ : V.toScheme := ⟨d', hd'V⟩
  obtain ⟨x', hx'⟩ := φ.surjective d₁
  have hβx' : β x'.1 = d' := by
    have := congrArg Subtype.val hx'
    rwa [show (φ x').1 = β x'.1 from morphismRestrict_base_coe β V x'] at this
  have hspV : d₁ ⤳ y₀ := (IsInducing.subtypeVal.specializes_iff).mp hd'x
  have hφx : φ x₀ = y₀ := Subtype.ext (morphismRestrict_base_coe β V x₀)
  have hsp : x' ⤳ x₀ := by
    have := hspV.map φ.symm.continuous
    rwa [← hx', ← hφx, φ.symm_apply_apply, φ.symm_apply_apply] at this
  have hsp' : x'.1 ⤳ x := (IsInducing.subtypeVal.specializes_iff).mpr hsp
  -- `x'` lies on the transported generic marks
  have hx'η : (β ≫ g) x'.1 = genericPoint S := by
    rw [Scheme.Hom.comp_apply, hβx', hd'η]
  obtain ⟨z, hz⟩ : x'.1 ∈ Set.range ((β ≫ g).fiberι (genericPoint S)) := by
    rw [Scheme.Hom.range_fiberι]
    exact hx'η
  set E := (DeJong.fiberMarks g D (genericPoint S)).comap (fiberMap β g (genericPoint S))
  have hzE : z ∈ (E.support : Set _) := by
    simp only [E, DeJong.fiberMarks, Scheme.IdealSheafData.support_comap]
    change g.fiberι _ (fiberMap β g _ z) ∈ (D.support : Set C)
    rw [← Scheme.Hom.comp_apply, fiberMap_fiberι, Scheme.Hom.comp_apply, hz, hβx']
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨d₀, rfl⟩
  rw [← Scheme.IdealSheafData.range_subschemeι] at hzE
  obtain ⟨w, hw⟩ := hzE
  have hx'D : x'.1 ∈ (D'.support : Set C') := by
    rw [h.marks_eq]
    apply Scheme.Hom.range_subset_ker_support
    exact ⟨w, by rw [Scheme.Hom.comp_apply, hw, hz]⟩
  exact closure_minimal (Set.singleton_subset_iff.mpr hx'D) D'.support.isClosed
    hsp'.mem_closure

end Stable

section Bridge

variable {k : Type u} [Field k]

/-- **The consumed form of a stable modification** (first half of `lem:sm-dejong-bridge`).
A stable η-modification `β : C' ⟶ C ×_S S'` of `(C, D) ×_S S'` along a generically étale
alteration `ψ`, with finite marks, projective, and an isomorphism over a nonempty open of `S'`,
is a stable modification in the consumed form `DeJong.HasStableModification`. -/
theorem hasStableModification_of_isStableModification {S C : Scheme.{u}}
    (pS : S ⟶ Spec (.of k)) (g : C ⟶ S) (D : C.IdealSheafData) (hD : IsMultipointedCurve g D)
    {S' C' : Scheme.{u}} [IsIntegral S'] (ψ : S' ⟶ S) [IsAlteration ψ]
    (β : C' ⟶ pullback g ψ) (D' : C'.IdealSheafData)
    (hβ : IsStableModification β (pullback.snd g ψ) (D.comap (pullback.fst g ψ)) D')
    (hfin : IsFinite (D'.subschemeι ≫ β ≫ pullback.snd g ψ))
    (hproj : DeJong.IsRelativelyProjective (pullback.snd g ψ ≫ ψ ≫ pS) β)
    (U : S'.Opens) (hU : Nonempty U) (hiso : IsIso (β ∣_ ((pullback.snd g ψ) ⁻¹ᵁ U))) :
    DeJong.HasStableModification k pS g D := by
  have := hD.marksFlat
  have := flat_comap_fst_subschemeι_snd g ψ D
  refine ⟨S', ψ, C', D', β, inferInstance, hβ.isSemistablePair, hfin, hproj, U, hU, hiso,
    fun x hx ↦ ?_⟩
  have hne : (U : Set S').Nonempty := ⟨hU.some.1, hU.some.2⟩
  rw [hβ.support_iff_of_isIso U hne hiso x hx, Scheme.IdealSheafData.support_comap]
  rfl

end Bridge

end DeJongAlterations.StableModification.Curves
