/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.StabilityLocal
import DeJongAlterations.StableModification.Limits.SpreadDimension
import DeJongAlterations.Geometry.FiberDimensionCurveComponents

/-!
# Pure fibre dimension of the target of a contraction

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), Lemma 4.4.5
(T:3178–3186): an exceptional blow-down `C' → C''` of a semi-stable curve is semi-stable. The proof
uses the openness of the semi-stable locus (Lemma 5.1(i), lane SS2's
`Curves.SemistableOpen.exists_isNodalCurve_nbhd`), which is stated for curves whose geometric
fibres have pure dimension one. For the target `C''` of a contraction this is not part of the
hypotheses; this file proves it (blueprint `lem:sm-bdg-pure-dimension`, `sm-blow-down-global.tex`):

* `topologicalKrullDim_le_one_of_specializingMap`: a specializing (e.g. closed) surjection does
  not increase a dimension `≤ 1` (specialization chains lift);
* `hasPureFiberDimension_of_isNodalCurve_comp`: if `b : X → Y` is proper and surjective, `b ≫ p`
  is a nodal curve, `Y` and the base are integral and the generic fibre of `p` is nonempty of
  dimension at least one, then every irreducible component of every fibre of `p` has dimension one
  (lower bound: Codex's `one_le_fiberComponentDimension_of_one_le_genericFiberDimension`; upper
  bound: the fibres of `b ≫ p` have dimension one and `b_s` is a closed surjection);
* `pureOneDimensionalFibres_of_isNodalCurve_comp`: the same for the geometric fibres
  (lane LIM2's `pureOneDimensionalFibres_of_hasPureFiberDimension`).
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

section Topology

variable {T T' : Type*} [TopologicalSpace T] [TopologicalSpace T'] [QuasiSober T] [T0Space T]
  [QuasiSober T'] [T0Space T']

/-- **Dimension at most one descends along specializing surjections**: if `f : T → T'` is
continuous, specializing (e.g. closed) and surjective and `T` has dimension at most one, so has
`T'` (a chain `b ⤳ y ⤳ a` of proper specializations in `T'` lifts to `T`). -/
theorem topologicalKrullDim_le_one_of_specializingMap (f : T → T') (hf : Continuous f)
    (hsp : SpecializingMap f) (hsurj : Function.Surjective f) (h : topologicalKrullDim T ≤ 1) :
    topologicalKrullDim T' ≤ 1 := by
  rw [topologicalKrullDim_le_one_iff_specializes] at h ⊢
  intro y
  by_contra hy
  push Not at hy
  obtain ⟨⟨a, hya, hay⟩, ⟨c, hcy, hyc⟩⟩ := hy
  obtain ⟨xc, rfl⟩ := hsurj c
  obtain ⟨xy, hxcy, rfl⟩ := hsp hcy
  obtain ⟨xa, hxya, rfl⟩ := hsp hya
  rcases h xy with h1 | h2
  · exact hay ((h1 xa hxya).map hf)
  · exact hyc ((h2 xc hxcy).map hf)

end Topology

section Fibres

variable {S X Y : Scheme.{u}} (p : Y ⟶ S) (b : X ⟶ Y)

/-- A geometric point over `s`: `Spec κ(s)^a ⟶ S`. -/
abbrev geometricPointOver (s : S) :
    Spec (CommRingCat.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
    (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s

theorem geometricPointOver_apply (s : S)
    (t : Spec (CommRingCat.of (AlgebraicClosure (S.residueField s)))) :
    geometricPointOver s t = s := by
  rw [Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply s _

/-- **The fibres of a nodal curve have pure dimension one** (from the geometric fibre over
`κ(s)^a`, lane LIM2's `pure_fiber_of_pure_pullback`). -/
theorem pure_fiber_of_nodal (g : X ⟶ S) [DeJong.IsNodalCurve g] (s : S) :
    ∀ W ∈ irreducibleComponents (g.fiber s), topologicalKrullDim W = 1 := by
  have h := Limits.Spread.pure_fiber_of_pure_pullback g (geometricPointOver s)
    (DeJong.IsNodalCurve.pureGeometricFibers (g := g) _ (geometricPointOver s))
  rwa [geometricPointOver_apply] at h

/-- **The fibres of a nodal curve have dimension at most one.** -/
theorem topologicalKrullDim_fiber_le_one_of_nodal (g : X ⟶ S) [DeJong.IsNodalCurve g]
    (s : S) : topologicalKrullDim (g.fiber s) ≤ 1 :=
  topologicalKrullDim_le_one_of_forall_irreducibleComponents fun W hW =>
    (pure_fiber_of_nodal g s W hW).le

/-- **A nonempty fibre of a nodal curve has dimension one.** -/
theorem one_le_topologicalKrullDim_fiber_of_nodal (g : X ⟶ S) [DeJong.IsNodalCurve g]
    (s : S) [Nonempty (g.fiber s)] : 1 ≤ topologicalKrullDim (g.fiber s) := by
  obtain ⟨x⟩ : Nonempty (g.fiber s) := inferInstance
  have hW := irreducibleComponent_mem_irreducibleComponents x
  rw [← pure_fiber_of_nodal g s _ hW]
  exact topologicalKrullDim_subspace_le _ _

instance surjective_fiberMap [Surjective b] (s : S) : Surjective (Curves.fiberMap b p s) := by
  unfold Curves.fiberMap
  rw [Curves.pullbackCompMap_eq]
  infer_instance

/-- **The fibres of the target of a nodal source have dimension at most one**: `b_s : X_s → Y_s`
is a closed surjection. -/
theorem topologicalKrullDim_fiber_le_one_of_isNodalCurve_comp [IsProper b] [Surjective b]
    [DeJong.IsNodalCurve (b ≫ p)] (s : S) : topologicalKrullDim (p.fiber s) ≤ 1 :=
  topologicalKrullDim_le_one_of_specializingMap (Curves.fiberMap b p s)
    (Curves.fiberMap b p s).continuous (Curves.fiberMap b p s).isClosedMap.specializingMap
    (Curves.fiberMap b p s).surjective
    (topologicalKrullDim_fiber_le_one_of_nodal (b ≫ p) s)

/-- **Pure fibre dimension of the target of a contraction** (blueprint
`lem:sm-bdg-pure-dimension`): let `b : X → Y` be proper and surjective with `b ≫ p` a nodal curve,
`Y` and `S` integral, `p` quasi-compact, locally of finite type and dominant, and the generic fibre
of `p` of dimension at least one. Then every irreducible component of every fibre of `p` has
dimension one. -/
theorem hasPureFiberDimension_of_isNodalCurve_comp [IsIntegral Y] [IsIntegral S]
    [LocallyOfFiniteType p] [QuasiCompact p] [IsDominant p] [IsProper b] [Surjective b]
    [DeJong.IsNodalCurve (b ≫ p)]
    (hgen : 1 ≤ Geometry.FiberDimension.fiberDimension p (genericPoint S)) :
    DeJong.HasPureFiberDimension p 1 := by
  intro s W hW
  refine le_antisymm ?_ ?_
  · exact (topologicalKrullDim_subspace_le _ W).trans
      (topologicalKrullDim_fiber_le_one_of_isNodalCurve_comp p b s)
  · exact Geometry.FiberDimensionCurveComponents.one_le_fiberComponentDimension_of_one_le_genericFiberDimension
      p hgen s W hW

/-- **The generic fibre of the target of an η-modification of a nodal curve has dimension at
least one**, if it is nonempty. -/
theorem one_le_fiberDimension_genericPoint [IrreducibleSpace S] [DeJong.IsNodalCurve (b ≫ p)]
    (hb : IsIso (Curves.fiberMap b p (genericPoint S)))
    [Nonempty ((b ≫ p).fiber (genericPoint S))] :
    1 ≤ Geometry.FiberDimension.fiberDimension p (genericPoint S) := by
  unfold Geometry.FiberDimension.fiberDimension
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (Curves.fiberMap b p (genericPoint S)).homeomorph.isHomeomorph]
  exact one_le_topologicalKrullDim_fiber_of_nodal (b ≫ p) _

/-- **Pure one-dimensional geometric fibres of the target of a contraction** (blueprint
`lem:sm-bdg-pure-dimension`): under the hypotheses of `hasPureFiberDimension_of_isNodalCurve_comp`
(with the generic-fibre condition supplied by an η-modification), every irreducible component of
every geometric fibre of `p` has dimension one. -/
theorem pureOneDimensionalFibres_of_isNodalCurve_comp [IsIntegral Y] [IsIntegral S]
    [LocallyOfFiniteType p] [QuasiCompact p] [IsDominant p] [IsProper b] [Surjective b]
    [DeJong.IsNodalCurve (b ≫ p)] (hb : IsIso (Curves.fiberMap b p (genericPoint S)))
    [Nonempty ((b ≫ p).fiber (genericPoint S))] :
    Curves.SemistableOpen.PureOneDimensionalFibres p :=
  Limits.Spread.pureOneDimensionalFibres_of_hasPureFiberDimension p
    (hasPureFiberDimension_of_isNodalCurve_comp p b (one_le_fiberDimension_genericPoint p b hb))

end Fibres

end

end DeJongAlterations.StableModification.BlowDown
