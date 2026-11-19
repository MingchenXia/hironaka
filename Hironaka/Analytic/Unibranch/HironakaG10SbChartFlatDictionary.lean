import Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk
import Hironaka.Analytic.Unibranch.HironakaG10SbQuotientFlat
import Hironaka.Analytic.Unibranch.HironakaG10SingularNativeChartFlattener

/-!
# Flatness dictionary for arbitrary test ideals through one singular base chart (G10-02-04)

Lane G10SB, run 0081, plan item G10-02-04.  Setting of G10-02-03: a morphism `p : Y ⟶ X` of
reduced complex spaces (singular `X` allowed), a base local embedding `eX`, a source local
embedding `eY` and an actual chart square
`actualSubspaceMap hf hCD ≫ eX.map = (eY.restrict U hUV).map ≫ p`
(`HironakaG10ReducedLocalMapSquare.exists_reduced_local_map_square`).  At a source carrier point
`x'` over `x = p (e' x')`:

* `R = 𝒪_{ℂⁿ,0}` (ambient base germs at the base chart point, `n = eX.dim`);
* `K = nativeRelativeGraphIdeal hf C' x' ⊆ 𝒪_{ℂ^{n+m},0}` — the whole relative graph ideal of the
  source chart (base coordinates first), with `𝒪_{ℂ^{n+m},0} ⧸ K ≅ 𝒪_{Y, y}` over `R`
  (`HironakaChowRelativeGraphPresentation`);
* `J̃ = J.comap (baseChartLiftAt …)` — the lift of a test ideal `J ⊆ 𝒪_{X,x}`; it contains the whole
  base defining ideal, and every ideal above that ideal is such a lift.

Proved, for EVERY test ideal (zero divisors and nilpotents allowed):

* `quotMap_fibre_flat_iff_graph` — native flatness of `𝒪_{X,x}/J → 𝒪_{Y,y}/J𝒪_{Y,y}` iff
  flatness of `R ⧸ J̃ → (R^{n+m} ⧸ K) ⧸ J̃` (the chart map over `V(J̃)`);
* `quotMap_fibre_flat_iff_tensor` — iff `Module.Flat (R ⧸ J̃) ((R ⧸ J̃) ⊗[R] (𝒪_{ℂ^{n+m},0} ⧸ K))`;
* `quotMap_fibre_flat_iff_graph_of_le` — the same read on ideals `I ⊇ chartIdeal` of `R`;
* `map_chartIdeal_le_graphIdeal` — the pulled base defining ideal lies in `K`;
* `isPointFlattenerAt_graph` — **the native pointed flattener of `p` at `y` over a singular base is
  the image of the canonical flattener ideal of the graph chart** (Hironaka (1.14.2) at one point,
  over a singular base, via `isFlattenerIdeal_of_chart_stalk_square`).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10SbChartFlatDictionary

open Hironaka Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaRelativeNormalIdeal
  HironakaChowRelativeGraphPresentation HironakaG10HirFlatQuotient HironakaG10HirChartFlattener
  HironakaChowPresentationIndependentFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
  Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk Hironaka.Analytic.Unibranch.HironakaG10SbQuotientFlat
  Hironaka.Analytic.Unibranch.HironakaG10SingularNativeChartFlattener

noncomputable section

local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

variable {X Y : SourceReducedComplexSpace} (p : Y ⟶ X) (eX : LocalEmbedding X)
  (eY : LocalEmbedding Y) {U : Opens (ComplexModel eY.dim)} (hUV : U ≤ eY.ambient)
  {f : U → eX.ambient} (hf : ContMDiff 𝓘(ℂ, ComplexModel eY.dim) 𝓘(ℂ, ComplexModel eX.dim) ∞ f)
  (hCD : ∀ z ∈ (eY.restrict U hUV).carrier, f z ∈ eX.carrier)
  (hsq : actualSubspaceMap hf hCD ≫ eX.map = (eY.restrict U hUV).map ≫ p.hom.left)

/-- The source stalk as the ambient relative graph quotient. -/
def graphStalkEquiv (x' : (eY.restrict U hUV).carrier) :
    (HolGerm (ComplexModel (eX.dim + eY.dim)) ⧸
        nativeRelativeGraphIdeal hf (eY.restrict U hUV).carrier x') ≃+*
      Y.obj.left.presheaf.stalk ((eY.restrict U hUV).toPoint x') :=
  (nativeRelativeGraphEquiv hf (eY.restrict U hUV).carrier x').trans
    (embeddingStalkEquiv (eY.restrict U hUV) x').symm

include hsq in
/-- The presentation square: native stalk map ∘ base presentation = graph equivalence ∘ chart map. -/
theorem fibreStalkMap_square (x' : (eY.restrict U hUV).carrier) (x : X.obj.left)
    (h : p.hom.left.base ((eY.restrict U hUV).toPoint x') = x)
    (hc : eX.toPoint ((actualSubspaceMap hf hCD).base x') = x) :
    (fibreStalkMap p x ((eY.restrict U hUV).toPoint x') h).comp
        (baseChartLiftAt eX ((actualSubspaceMap hf hCD).base x') x hc) =
      (graphStalkEquiv eX eY hUV hf x').toRingHom.comp
        (algebraMap (HolGerm (ComplexModel eX.dim))
          (HolGerm (ComplexModel (eX.dim + eY.dim)) ⧸
            nativeRelativeGraphIdeal hf (eY.restrict U hUV).carrier x')) := by
  rw [fibreStalkMap_comp_baseChartLiftAt p eX eY hUV hf hCD hsq x' x h hc]
  ext a
  change (embeddingStalkEquiv (eY.restrict U hUV) x').symm
      (nativeBasePullback hf (eY.restrict U hUV).carrier x' a) =
    (embeddingStalkEquiv (eY.restrict U hUV) x').symm
      (nativeRelativeGraphEquiv hf (eY.restrict U hUV).carrier x'
        (Ideal.Quotient.mk _ (tangentPullback eX.dim eY.dim a)))
  rw [nativeRelativeGraphEquiv_base]

include hsq in
/-- **G10-02-04.**  For EVERY test ideal `J ⊆ 𝒪_{X,x}` the native fibre map over `V(J)` is flat
iff the ambient graph chart map is flat over the lifted ideal `J̃`. -/
theorem quotMap_fibre_flat_iff_graph (x' : (eY.restrict U hUV).carrier) (x : X.obj.left)
    (h : p.hom.left.base ((eY.restrict U hUV).toPoint x') = x)
    (hc : eX.toPoint ((actualSubspaceMap hf hCD).base x') = x)
    (J : Ideal (X.obj.left.presheaf.stalk x)) :
    (quotMap (fibreStalkMap p x ((eY.restrict U hUV).toPoint x') h) J).Flat ↔
      (quotMap (algebraMap (HolGerm (ComplexModel eX.dim))
          (HolGerm (ComplexModel (eX.dim + eY.dim)) ⧸
            nativeRelativeGraphIdeal hf (eY.restrict U hUV).carrier x'))
        (J.comap (baseChartLiftAt eX ((actualSubspaceMap hf hCD).base x') x hc))).Flat :=
  quotMap_flat_iff_of_square _ _ (baseChartLiftAt_surjective eX _ x hc) _
    (graphStalkEquiv eX eY hUV hf x') (fibreStalkMap_square p eX eY hUV hf hCD hsq x' x h hc) J

include hsq in
/-- **G10-02-04, module form**: the base-changed graph module `(R ⧸ J̃) ⊗[R] (𝒪_{ℂ^{n+m},0} ⧸ K)`. -/
theorem quotMap_fibre_flat_iff_tensor (x' : (eY.restrict U hUV).carrier) (x : X.obj.left)
    (h : p.hom.left.base ((eY.restrict U hUV).toPoint x') = x)
    (hc : eX.toPoint ((actualSubspaceMap hf hCD).base x') = x)
    (J : Ideal (X.obj.left.presheaf.stalk x)) :
    (quotMap (fibreStalkMap p x ((eY.restrict U hUV).toPoint x') h) J).Flat ↔
      Module.Flat
        (HolGerm (ComplexModel eX.dim) ⧸
          J.comap (baseChartLiftAt eX ((actualSubspaceMap hf hCD).base x') x hc))
        ((HolGerm (ComplexModel eX.dim) ⧸
            J.comap (baseChartLiftAt eX ((actualSubspaceMap hf hCD).base x') x hc)) ⊗[HolGerm (ComplexModel eX.dim)]
          (HolGerm (ComplexModel (eX.dim + eY.dim)) ⧸
            nativeRelativeGraphIdeal hf (eY.restrict U hUV).carrier x')) := by
  rw [quotMap_fibre_flat_iff_graph p eX eY hUV hf hCD hsq x' x h hc J,
    quotMap_algebraMap_flat_iff_tensor]

include hsq in
/-- **G10-02-04, read on base ideals**: for every ideal `I ⊇ chartIdeal` of the ambient base germs,
native flatness over the image of `I` is chart flatness over `I` itself. -/
theorem quotMap_fibre_flat_iff_graph_of_le (x' : (eY.restrict U hUV).carrier) (x : X.obj.left)
    (h : p.hom.left.base ((eY.restrict U hUV).toPoint x') = x)
    (hc : eX.toPoint ((actualSubspaceMap hf hCD).base x') = x)
    (I : Ideal (HolGerm (ComplexModel eX.dim)))
    (hI : chartIdeal eX ((actualSubspaceMap hf hCD).base x') ≤ I) :
    (quotMap (fibreStalkMap p x ((eY.restrict U hUV).toPoint x') h)
        (I.map (baseChartLiftAt eX ((actualSubspaceMap hf hCD).base x') x hc))).Flat ↔
      (quotMap (algebraMap (HolGerm (ComplexModel eX.dim))
          (HolGerm (ComplexModel (eX.dim + eY.dim)) ⧸
            nativeRelativeGraphIdeal hf (eY.restrict U hUV).carrier x')) I).Flat :=
  quotMap_flat_iff_of_square' _ _ (baseChartLiftAt_surjective eX _ x hc) _
    (graphStalkEquiv eX eY hUV hf x') (fibreStalkMap_square p eX eY hUV hf hCD hsq x' x h hc) I
    ((ker_baseChartLiftAt eX _ x hc).le.trans hI)

/-- Lifted test ideals contain the whole base defining ideal. -/
theorem chartIdeal_le_comap (c : eX.carrier) (x : X.obj.left) (hc : eX.toPoint c = x)
    (J : Ideal (X.obj.left.presheaf.stalk x)) :
    chartIdeal eX c ≤ J.comap (baseChartLiftAt eX c x hc) := by
  rw [← ker_baseChartLiftAt eX c x hc]
  exact ker_le_comap _ J

include hsq in
/-- The pulled whole base defining ideal lies in the relative graph ideal. -/
theorem map_chartIdeal_le_graphIdeal (x' : (eY.restrict U hUV).carrier) :
    (chartIdeal eX ((actualSubspaceMap hf hCD).base x')).map
        (tangentPullback eX.dim eY.dim).toRingHom ≤
      nativeRelativeGraphIdeal hf (eY.restrict U hUV).carrier x' := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  apply (nativeRelativeGraphEquiv hf (eY.restrict U hUV).carrier x').injective
  rw [map_zero]
  change nativeRelativeGraphEquiv hf (eY.restrict U hUV).carrier x'
    (Ideal.Quotient.mk _ (tangentPullback eX.dim eY.dim a)) = 0
  rw [nativeRelativeGraphEquiv_base]
  exact nativeBasePullback_chartIdeal p eX eY hUV hf hCD hsq x' a ha

/-- The base chart equivalence, inverted and transported to a point equal to the chart point. -/
def baseChartQuotientEquivAt (c : eX.carrier) (x : X.obj.left) (hc : eX.toPoint c = x) :
    (HolGerm (ComplexModel eX.dim) ⧸ chartIdeal eX c) ≃+* X.obj.left.presheaf.stalk x :=
  (baseChartStalkEquiv eX c).symm.trans
    (eqToIso (congrArg X.obj.left.presheaf.stalk hc)).commRingCatIsoToRingEquiv

theorem baseChartQuotientEquivAt_mk (c : eX.carrier) (x : X.obj.left) (hc : eX.toPoint c = x)
    (a : HolGerm (ComplexModel eX.dim)) :
    baseChartQuotientEquivAt eX c x hc (Ideal.Quotient.mk _ a) = baseChartLiftAt eX c x hc a :=
  rfl

include hsq in
/-- **The native pointed flattener over a singular base** (Hironaka (1.14.2) at one point): the
image in `𝒪_{X,x}` of the canonical flattener ideal of the ambient graph chart. -/
theorem isPointFlattenerAt_graph (x' : (eY.restrict U hUV).carrier) (x : X.obj.left)
    (h : p.hom.left.base ((eY.restrict U hUV).toPoint x') = x)
    (hc : eX.toPoint ((actualSubspaceMap hf hCD).base x') = x) :
    IsPointFlattenerAt p x ((eY.restrict U hUV).toPoint x') h
      (((canonicalFlattenerIdeal eX.dim eY.dim
          (nativeRelativeGraphIdeal hf (eY.restrict U hUV).carrier x')).map
        (Ideal.Quotient.mk (chartIdeal eX ((actualSubspaceMap hf hCD).base x')))).map
          (baseChartQuotientEquivAt eX ((actualSubspaceMap hf hCD).base x') x hc).toRingHom) := by
  have hsq' : (fibreStalkMap p x ((eY.restrict U hUV).toPoint x') h).comp
      (baseChartQuotientEquivAt eX ((actualSubspaceMap hf hCD).base x') x hc).toRingHom =
      (graphStalkEquiv eX eY hUV hf x').toRingHom.comp
        (singularChartMap eX.dim eY.dim (chartIdeal eX ((actualSubspaceMap hf hCD).base x'))
          (nativeRelativeGraphIdeal hf (eY.restrict U hUV).carrier x')
          (map_chartIdeal_le_graphIdeal p eX eY hUV hf hCD hsq x')) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    exact RingHom.congr_fun (fibreStalkMap_square p eX eY hUV hf hCD hsq x' x h hc) a
  exact isFlattenerIdeal_of_chart_stalk_square eX.dim eY.dim _ _
    (map_chartIdeal_le_graphIdeal p eX eY hUV hf hCD hsq x')
    (fibreStalkMap p x ((eY.restrict U hUV).toPoint x') h)
    (baseChartQuotientEquivAt eX ((actualSubspaceMap hf hCD).base x') x hc)
    (graphStalkEquiv eX eY hUV hf x') hsq'

end

end Hironaka.Analytic.Unibranch.HironakaG10SbChartFlatDictionary
