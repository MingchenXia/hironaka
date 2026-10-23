import DeJongAlterations.StableModification.DeJong.Interface
import DeJongAlterations.Geometry.CurveFibrationBaseChange

/-!
# Nodal curves under isomorphism and base change

The base step 4.22 of de Jong (*Smoothness, semi-stability and alterations*, 1996,
`dejong96-alterations:page-0025`, `page-0026`) pulls the semi-stable family produced by
Temkin's stable modification theorem (Temkin, *Stable modification of relative curves*,
§1.2, `semi-stable.tex` l.1683–1687) back along alterations of the base. This file proves
that the notions of `Interface.lean` survive this.

* `forall_irreducibleComponents_dim_of_homeomorph`: pure dimension of irreducible
  components is a topological invariant.
* `isSmoothAt_comp_iff_of_isOpenImmersion`, `isSmoothAt_of_isPullback`: smoothness at a
  point is local on the source and is preserved by base change (Temkin §1.2: "the
  non-smoothness locus is compatible with base change").
* `isGeometricOrdinaryDoublePoint_of_iso`: ordinary double points are invariant under
  isomorphisms of `K`-schemes (the completed local `K`-algebras are isomorphic).
* `IsNodalCurve.of_geometricFiberIso`, `IsNodalCurve.of_iso`, `IsNodalCurve.pullback_snd`,
  `IsNodalCurve.of_isPullback` (`lem:sm-dj-nodal-base-change`): every geometric fibre of a
  base change `C ×_S S' → S'` is a geometric fibre of `C → S`, so nodal curves are stable
  under base change (Temkin §1.2, "obviously `C → S` is semi-stable if and only if its
  geometric fibers are so").
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Geometry (IsGeometricOrdinaryDoublePoint)

/-- If every irreducible component of `B` has dimension `n` and `A ≃ₜ B`, then every
irreducible component of `A` has dimension `n`. -/
theorem forall_irreducibleComponents_dim_of_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (h : A ≃ₜ B) {n : WithBot ℕ∞}
    (hB : ∀ Z ∈ irreducibleComponents B, topologicalKrullDim Z = n) :
    ∀ Z ∈ irreducibleComponents A, topologicalKrullDim Z = n := by
  intro Z hZ
  have h1 : h.symm ⁻¹' Z ∈ irreducibleComponents B := by
    refine preimage_mem_irreducibleComponents hZ h.symm.isOpenEmbedding ?_
    rw [h.symm.surjective.range_eq, Set.inter_univ]
    exact hZ.1.1
  have h2 : h.symm ⁻¹' Z = h '' Z := (h.image_eq_preimage_symm Z).symm
  rw [← hB _ h1, h2]
  exact IsHomeomorph.topologicalKrullDim_eq _ (h.image Z).isHomeomorph

section Smooth

variable {U C S : Scheme.{u}}

/-- Smoothness at a point is local on the source. -/
theorem isSmoothAt_comp_iff_of_isOpenImmersion (j : U ⟶ C) [IsOpenImmersion j] (g : C ⟶ S)
    (x : U) : IsSmoothAt (j ≫ g) x ↔ IsSmoothAt g (j x) := by
  unfold IsSmoothAt
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_right_isIso (g.stalkMap (j x)) (j.stalkMap x)

/-- Smoothness at a point is invariant under isomorphisms of the source. -/
theorem isSmoothAt_iso_comp_iff (e : U ≅ C) (g : C ⟶ S) (x : U) :
    IsSmoothAt (e.hom ≫ g) x ↔ IsSmoothAt g (e.hom x) :=
  isSmoothAt_comp_iff_of_isOpenImmersion e.hom g x

/-- **Base change of smoothness at points.** If `g` is smooth at the image of `x` in `C`,
then the base change `C ×_S S' → S'` is smooth at `x`. -/
theorem isSmoothAt_pullback_snd {S' : Scheme.{u}} (g : C ⟶ S) [LocallyOfFinitePresentation g]
    (ψ : S' ⟶ S) (x : (pullback g ψ : Scheme.{u})) (hx : IsSmoothAt g (pullback.fst g ψ x)) :
    IsSmoothAt (pullback.snd g ψ) x := by
  let V := (pullback.fst g ψ) ⁻¹ᵁ g.smoothLocus
  have hV : Smooth (V.ι ≫ pullback.snd g ψ) :=
    Geometry.CurveFibrationBaseChange.smooth_originalLocus g ψ
  have hxV : x ∈ V := (isSmoothAt_iff_mem_smoothLocus g _).mp hx
  have h1 : (⟨x, hxV⟩ : V) ∈ (V.ι ≫ pullback.snd g ψ).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  have h2 := (isSmoothAt_comp_iff_of_isOpenImmersion V.ι (pullback.snd g ψ) ⟨x, hxV⟩).mp h1
  simpa using h2

/-- Base change of smoothness at points, for an arbitrary cartesian square. -/
theorem isSmoothAt_of_isPullback {S' P : Scheme.{u}} {fst : P ⟶ C} {snd : P ⟶ S'}
    {g : C ⟶ S} {ψ : S' ⟶ S} [LocallyOfFinitePresentation g] (H : IsPullback fst snd g ψ)
    (x : P) (hx : IsSmoothAt g (fst x)) : IsSmoothAt snd x := by
  have hsnd : snd = H.isoPullback.hom ≫ pullback.snd g ψ := (H.isoPullback_hom_snd).symm
  rw [hsnd, isSmoothAt_iso_comp_iff]
  apply isSmoothAt_pullback_snd
  rw [← Scheme.Hom.comp_apply, H.isoPullback_hom_fst]
  exact hx

end Smooth

section Nodes

variable {K : Type u} [Field K] {A B : Scheme.{u}}

/-- Ordinary double points are invariant under isomorphisms of `K`-schemes. -/
theorem isGeometricOrdinaryDoublePoint_of_iso (E : A ≅ B) (qA : A ⟶ Spec (.of K))
    (qB : B ⟶ Spec (.of K)) (h : E.hom ≫ qB = qA) (y : A)
    (hy : IsGeometricOrdinaryDoublePoint qB (E.hom y)) :
    IsGeometricOrdinaryDoublePoint qA y := by
  obtain ⟨φ⟩ := hy
  let := Scheme.completedLocalRingAlgebra qB (E.hom y)
  let := Scheme.completedLocalRingAlgebra qA y
  exact ⟨(Scheme.completedLocalRingAlgEquivOfIsoOver E qA qB h y).symm.trans φ⟩

end Nodes

section NodalCurve

variable {C S C' S' : Scheme.{u}}

/-- **Transport of nodal curves along geometric fibres.** If every geometric fibre of the
flat, locally finitely presented `g'` is isomorphic over its geometric point to a geometric
fibre of the nodal curve `g`, then `g'` is a nodal curve. -/
theorem IsNodalCurve.of_geometricFiberIso (g : C ⟶ S) [hg : IsNodalCurve g] (g' : C' ⟶ S')
    [Flat g'] [LocallyOfFinitePresentation g']
    (H : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S'),
      ∃ (b : Spec (.of K) ⟶ S) (E : pullback g' a ≅ pullback g b),
        E.hom ≫ pullback.snd g b = pullback.snd g' a) :
    IsNodalCurve g' where
  pureGeometricFibers := by
    intro K _ _ a Z hZ
    obtain ⟨b, E, -⟩ := H K a
    exact forall_irreducibleComponents_dim_of_homeomorph (Scheme.homeoOfIso E)
      (hg.pureGeometricFibers K b) Z hZ
  geometricNodes := by
    intro K _ _ a y hy
    obtain ⟨b, E, hE⟩ := H K a
    have hy' : IsClosed ({E.hom y} : Set (pullback g b : Scheme.{u})) := by
      have := (Scheme.homeoOfIso E).isClosed_image.mpr hy
      simpa using this
    rcases hg.geometricNodes K b (E.hom y) hy' with hsm | hnode
    · left
      have h1 : IsSmoothAt (pullback.snd g b) (E.hom y) :=
        (isSmoothAt_iff_mem_smoothLocus _ _).mpr hsm
      rw [← isSmoothAt_iso_comp_iff, hE] at h1
      exact (isSmoothAt_iff_mem_smoothLocus _ _).mp h1
    · right
      exact isGeometricOrdinaryDoublePoint_of_iso E _ _ hE y hnode

/-- Nodal curves are invariant under isomorphisms of the source. -/
theorem IsNodalCurve.of_iso (e : C' ≅ C) (g : C ⟶ S) [IsNodalCurve g] :
    IsNodalCurve (e.hom ≫ g) := by
  refine IsNodalCurve.of_geometricFiberIso g (e.hom ≫ g) fun K _ _ a ↦ ?_
  refine ⟨a, asIso (pullback.map (e.hom ≫ g) a g a e.hom (𝟙 _) (𝟙 _) (by simp) (by simp)), ?_⟩
  simp

/-- **Nodal curves are stable under base change** (`lem:sm-dj-nodal-base-change`). -/
instance IsNodalCurve.pullback_snd (g : C ⟶ S) [IsNodalCurve g] (ψ : S' ⟶ S) :
    IsNodalCurve (pullback.snd g ψ) := by
  refine IsNodalCurve.of_geometricFiberIso g (pullback.snd g ψ) fun K _ _ a ↦ ?_
  exact ⟨a ≫ ψ, pullbackLeftPullbackSndIso g ψ a, pullbackLeftPullbackSndIso_hom_snd g ψ a⟩

/-- Nodal curves are stable under base change, for an arbitrary cartesian square. -/
theorem IsNodalCurve.of_isPullback {P : Scheme.{u}} {fst : P ⟶ C} {snd : P ⟶ S'}
    {g : C ⟶ S} {ψ : S' ⟶ S} [IsNodalCurve g] (H : IsPullback fst snd g ψ) :
    IsNodalCurve snd := by
  have hsnd : snd = H.isoPullback.hom ≫ pullback.snd g ψ := (H.isoPullback_hom_snd).symm
  rw [hsnd]
  exact IsNodalCurve.of_iso H.isoPullback (pullback.snd g ψ)

end NodalCurve

end DeJongAlterations.StableModification.DeJong
