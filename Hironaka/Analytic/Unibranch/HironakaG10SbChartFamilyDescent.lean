import Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk
import Hironaka.Resolution.HironakaG10PNKernelSquare
import Hironaka.Resolution.HironakaG10HirIdealGerms

/-!
# Descent of locally generated ideal families through one singular base chart (G10-02-05)

Lane G10SB, run 0081, plan item G10-02-05.  Let `e` be a local embedding of the (possibly singular)
reduced complex space `X`, with ambient open `Ω ⊆ ℂⁿ` and carrier `C ⊆ Ω`.  An ideal family `H` on
the AMBIENT manifold `Ω` (e.g. an actual Schur coefficient family, a `spanFamily` of global
sections) descends through the defining quotient and the open immersion to the family

  `descendFamily e H = kerFamily e.map (pullFamily (actualSubspaceInclusion C) H)`

on `X` (the unit ideal off the chart).  Proved:

* `descendFamily_apply`, `descendFamily_apply_at` — **stalk compatibility**: at `x = e c` the
  descended ideal is the image of the ambient germ ideal `H c` (read in the translated chart germs)
  under the base presentation `baseChartLift e c` of G10-02-03;
* `descendFamily_le_iff_at` — containment in a test ideal `J ⊆ 𝒪_{X,x}` is containment of the
  ambient germ ideal in the lifted ideal `J̃` (the form used by the flattener criteria);
* `descendFamily_of_not_mem_range` — the unit ideal off the chart;
* `isLocallyFinitelyGeneratedAt_descendFamily` — **coherence descends**: local finite generation of
  `H` at `c` gives local finite generation of the descended family at `e c`;
* `isLocallyFinitelyGeneratedOn_descendFamily`, `…_of_isLocallyFinitelyGenerated` — the descended
  family is locally finitely generated on the chart image (`IsLocallyFinitelyGeneratedOn`, the
  coherence field of `LocalFlattener`).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10SbChartFamilyDescent

open Hironaka Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaG10PNIdealFamily HironakaG10PNKernelFamily HironakaG10PNKernelSquare
  HironakaG10HirIdealGerms
  Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk

noncomputable section

variable {X : SourceReducedComplexSpace} (e : LocalEmbedding X)

/-- The ambient manifold of a local embedding as a locally ringed space. -/
abbrev AmbientSpace : LocallyRingedSpace.{0} :=
  ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel e.dim) e.ambient

/-- **The descended family**: pull the ambient family to the carrier model through the defining
quotient, then transport it to `X` through the open immersion (unit ideal off the chart). -/
def descendFamily (H : ∀ z : AmbientSpace e, Ideal ((AmbientSpace e).presheaf.stalk z)) :
    ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x) :=
  kerFamily e.map (pullFamily (actualSubspaceInclusion (n := e.dim) e.carrier) H)

/-- The model inclusion stalk map, factored through the base presentation. -/
theorem inclusion_stalkMap_eq (c : e.carrier) :
    ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c).hom =
      (embeddingStalkEquiv e c).toRingHom.comp
        ((baseChartLift e c).comp (actualStalkChartEquiv (n := e.dim) c.val).toRingHom) := by
  ext r
  apply (actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c).injective
  refine (inclusion_stalk_chart (n := e.dim) e.carrier c r).trans ?_
  change _ = actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c
    (embeddingStalkEquiv e c (baseChartLift e c (actualStalkChartEquiv (n := e.dim) c.val r)))
  rw [embeddingStalkEquiv_baseChartLift, RingEquiv.apply_symm_apply]

/-- **Stalk compatibility (G10-02-05).**  At a chart point the descended ideal is the image of the
ambient germ ideal under the base presentation. -/
theorem descendFamily_apply (H : ∀ z : AmbientSpace e, Ideal ((AmbientSpace e).presheaf.stalk z))
    (c : e.carrier) :
    descendFamily e H (e.toPoint c) =
      Ideal.map (baseChartLift e c)
        (Ideal.map (actualStalkChartEquiv (n := e.dim) c.val).toRingHom (H c.val)) := by
  have hinj : Function.Injective e.map.base := e.toPoint_injective
  change kerFamily e.map _ (e.map.base c) = _
  rw [kerFamily_apply_of_injective e.map hinj, pullFamily]
  change Ideal.comap ((e.map.stalkMap c).hom)
    (Ideal.map ((actualSubspaceInclusion (n := e.dim) e.carrier).stalkMap c).hom (H c.val)) = _
  rw [inclusion_stalkMap_eq, ← Ideal.map_map, ← Ideal.map_map]
  change Ideal.comap (embeddingStalkEquiv e c).toRingHom
    (Ideal.map (embeddingStalkEquiv e c).toRingHom _) = _
  exact Ideal.comap_map_of_bijective _ (embeddingStalkEquiv e c).bijective

/-- Stalk compatibility at any point equal to a chart point. -/
theorem descendFamily_apply_at (H : ∀ z : AmbientSpace e, Ideal ((AmbientSpace e).presheaf.stalk z))
    (c : e.carrier) (x : X.obj.left) (hc : e.toPoint c = x) :
    descendFamily e H x =
      Ideal.map (baseChartLiftAt e c x hc)
        (Ideal.map (actualStalkChartEquiv (n := e.dim) c.val).toRingHom (H c.val)) := by
  subst hc
  rw [descendFamily_apply]
  rfl

/-- Containment of the descended family in a test ideal is read on the lifted ideal. -/
theorem descendFamily_le_iff_at
    (H : ∀ z : AmbientSpace e, Ideal ((AmbientSpace e).presheaf.stalk z))
    (c : e.carrier) (x : X.obj.left) (hc : e.toPoint c = x)
    (J : Ideal (X.obj.left.presheaf.stalk x)) :
    descendFamily e H x ≤ J ↔
      Ideal.map (actualStalkChartEquiv (n := e.dim) c.val).toRingHom (H c.val) ≤
        J.comap (baseChartLiftAt e c x hc) := by
  rw [descendFamily_apply_at e H c x hc]
  exact Ideal.map_le_iff_le_comap

/-- Off the chart the descended family is the unit ideal. -/
theorem descendFamily_of_not_mem_range
    (H : ∀ z : AmbientSpace e, Ideal ((AmbientSpace e).presheaf.stalk z))
    {x : X.obj.left} (hx : x ∉ range e.toPoint) : descendFamily e H x = ⊤ :=
  kerFamily_of_not_mem_range e.map _ hx

/-- **Coherence descends (G10-02-05).**  Local finite generation of the ambient family at a chart
point gives local finite generation of the descended family at its image. -/
theorem isLocallyFinitelyGeneratedAt_descendFamily
    (H : ∀ z : AmbientSpace e, Ideal ((AmbientSpace e).presheaf.stalk z))
    (c : e.carrier) (hH : IsLocallyFinitelyGeneratedAt (AmbientSpace e) H c.val) :
    IsLocallyFinitelyGeneratedAt X.obj.left (descendFamily e H) (e.toPoint c) := by
  have : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  have hpull : pullFamily e.map (descendFamily e H) =
      pullFamily (actualSubspaceInclusion (n := e.dim) e.carrier) H :=
    pullFamily_kerFamily_of_surjective e.map e.toPoint_injective
      (fun y => (stalkMap_bijective_of_openImmersion e.map y).2) _
  have hK : IsLocallyFinitelyGeneratedAt (actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier)
      (pullFamily (actualSubspaceInclusion (n := e.dim) e.carrier) H) c :=
    IsLocallyFinitelyGeneratedAt.pull (actualSubspaceInclusion (n := e.dim) e.carrier) hH
  have hK' : IsLocallyFinitelyGeneratedAt (modelOver e.ambient e.carrier).left
      (pullFamily e.map (descendFamily e H)) c := by
    rw [hpull]
    exact hK
  exact IsLocallyFinitelyGeneratedAt.of_openImmersion e.map hK'

/-- **The descended family is coherent on the chart image** (the `fg` field of a local
flattener). -/
theorem isLocallyFinitelyGeneratedOn_descendFamily
    (H : ∀ z : AmbientSpace e, Ideal ((AmbientSpace e).presheaf.stalk z))
    (hH : ∀ c : e.carrier, IsLocallyFinitelyGeneratedAt (AmbientSpace e) H c.val) :
    IsLocallyFinitelyGeneratedOn X.obj.left (range e.toPoint) (descendFamily e H) := by
  rintro _ ⟨c, rfl⟩
  obtain ⟨W, hxW, r, s, hs⟩ := isLocallyFinitelyGeneratedAt_descendFamily e H c (hH c)
  exact ⟨W, hxW, r, s, fun y hy _ => hs y hy⟩

/-- A globally locally finitely generated ambient family descends to a family coherent on the
chart image. -/
theorem isLocallyFinitelyGeneratedOn_descendFamily_of_isLocallyFinitelyGenerated
    (H : ∀ z : AmbientSpace e, Ideal ((AmbientSpace e).presheaf.stalk z))
    (hH : IsLocallyFinitelyGenerated (AmbientSpace e) H) :
    IsLocallyFinitelyGeneratedOn X.obj.left (range e.toPoint) (descendFamily e H) :=
  isLocallyFinitelyGeneratedOn_descendFamily e H fun c => hH c.val

end

end Hironaka.Analytic.Unibranch.HironakaG10SbChartFamilyDescent
