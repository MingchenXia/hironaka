import Hironaka.Analytic.Unibranch.HironakaG10ReducedLocalMapSquare
import Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
import Hironaka.Resolution.HironakaChowRelativeGraphPresentation

/-!
# The quotient-stalk isomorphism of one actual base chart (G10-02-03)

Lane G10SB, run 0081, plan item G10-02-03.  Let `X` be a reduced complex space (possibly singular)
and `e` a local embedding: an open immersion of the actual reduced model `(Ω, C)`, `C ⊆ Ω ⊆ ℂⁿ`
analytic, into `X`.  At a carrier point `c`:

* `embeddingStalkEquiv e c` — the stalk isomorphism `𝒪_{X, e c} ≅ 𝒪_{C, c}` of the open immersion;
* `baseChartStalkEquiv e c` — **`𝒪_{X, e c} ≅ 𝒪_{ℂⁿ,0} ⧸ I_c`**, where `I_c = chartIdeal e c` is
  the WHOLE defining ideal of `C` at `c` (all vanishing germs, translated to the origin);
* `baseChartLift e c : 𝒪_{ℂⁿ,0} →+* 𝒪_{X, e c}` — the surjective presentation, with kernel exactly
  `I_c` (`ker_baseChartLift`), and its transport `baseChartLiftAt` to any point equal to `e c`.

**Commutation with the original morphism.**  For a morphism `p : Y ⟶ X` and an actual chart square
`actualSubspaceMap hf hCD ≫ eX.map = (eY.restrict U hUV).map ≫ p` (as produced by
`HironakaG10ReducedLocalMapSquare.exists_reduced_local_map_square`, with singular target carrier),
the native stalk map of `p` at every source carrier point `x'`, composed with the base presentation,
is the native base pullback of the ambient holomorphic representative `f`
(`fibreStalkMap_baseChartLiftAt`).  In particular the ambient pullback kills the whole base defining
ideal (`nativeBasePullback_chartIdeal`).

No smoothness of `X`, no reducedness of test ideals; no named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaHolomorphicJetRankLoci HironakaChowRelativeGraphPresentation
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease

noncomputable section

/-! ### Generic facts -/

/-- Two transports between stalks along equal points compose. -/
theorem eqToHom_stalk_trans {T : LocallyRingedSpace.{0}} {a b d : T} (h₁ : a = b) (h₂ : b = d)
    (r : T.presheaf.stalk a) :
    (eqToHom (congrArg T.presheaf.stalk h₂)).hom ((eqToHom (congrArg T.presheaf.stalk h₁)).hom r) =
      (eqToHom (congrArg T.presheaf.stalk (h₁.trans h₂))).hom r := by
  subst h₁
  subst h₂
  rfl

/-- A round trip of transports between stalks is the identity. -/
theorem eqToHom_stalk_roundtrip {T : LocallyRingedSpace.{0}} {a b : T} (h₁ : a = b) (h₂ : b = a)
    (r : T.presheaf.stalk a) :
    (eqToHom (congrArg T.presheaf.stalk h₂)).hom ((eqToHom (congrArg T.presheaf.stalk h₁)).hom r) = r := by
  subst h₁
  rfl

/-- A transport between stalks along a point equal to itself is the identity. -/
theorem eqToHom_stalk_self {T : LocallyRingedSpace.{0}} {a : T} (h : a = a)
    (r : T.presheaf.stalk a) : (eqToHom (congrArg T.presheaf.stalk h)).hom r = r :=
  rfl

/-- **Stalks of a commutative square.**  In a square `j ≫ q = g ≫ i` of locally ringed spaces, the
two composite stalk maps agree after the point transports. -/
theorem stalk_square_apply {A B C D : LocallyRingedSpace.{0}} (g : A ⟶ C) (i : C ⟶ D)
    (j : A ⟶ B) (q : B ⟶ D) (H : j ≫ q = g ≫ i) (a : A) (x : D) (h : q.base (j.base a) = x)
    (hc : i.base (g.base a) = x) (u : D.presheaf.stalk (i.base (g.base a))) :
    (j.stalkMap a).hom ((q.stalkMap (j.base a)).hom
      ((eqToHom (congrArg D.presheaf.stalk h.symm)).hom
        ((eqToHom (congrArg D.presheaf.stalk hc)).hom u))) =
      (g.stalkMap a).hom ((i.stalkMap (g.base a)).hom u) := by
  subst h
  have hb : (g ≫ i).base a = (j ≫ q).base a := hc
  have e1 := stalkMap_eq_of_eq (j ≫ q) (g ≫ i) H a hb
    ((eqToHom (congrArg D.presheaf.stalk hc)).hom u)
  have e2 : (eqToHom (congrArg D.presheaf.stalk hb.symm)).hom
      ((eqToHom (congrArg D.presheaf.stalk hc)).hom u) = u :=
    eqToHom_stalk_roundtrip hc hb.symm u
  rw [e2] at e1
  rw [LocallyRingedSpace.stalkMap_comp, LocallyRingedSpace.stalkMap_comp] at e1
  exact e1

/-- The literal subspace inclusion stalk map read in the chart quotient. -/
theorem inclusion_stalk_chart {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (D : Set M) (x : D)
    (r : actualComplexStructureStalk (n := n) x.val) :
    actualSubspaceStalkChartEquiv (n := n) D x ((actualSubspaceInclusion (n := n) D).stalkMap x r) =
      Ideal.Quotient.mk _ (actualStalkChartEquiv (n := n) x.val r) := by
  change (Ideal.quotientEquiv _ _ (actualStalkChartEquiv (n := n) x.val)
      (map_actualWholeSheafStalkIdeal (vanishingIdeal (n := n) D) x.val).symm)
    (actualSubspaceStalkWholeEquiv (n := n) D x
      ((actualSubspaceInclusion (n := n) D).stalkMap x r)) = _
  rw [actualSubspaceInclusion_stalk]
  rfl

/-! ### The base chart presentation -/

variable {X : SourceReducedComplexSpace}

/-- The WHOLE defining ideal of the carrier at a carrier point, in the translated chart germs. -/
abbrev chartIdeal (e : LocalEmbedding X) (c : e.carrier) : Ideal (HolGerm (ComplexModel e.dim)) :=
  wholeChartStalkIdeal (vanishingIdeal (n := e.dim) e.carrier) c.val c.val
    (mem_chart_source (ComplexModel e.dim) c.val)

/-- The stalk isomorphism of the open immersion of a local embedding. -/
def embeddingStalkEquiv (e : LocalEmbedding X) (c : e.carrier) :
    X.obj.left.presheaf.stalk (e.toPoint c) ≃+*
      ((actualSubspaceSheaf (n := e.dim) e.carrier).presheaf.stalk c).carrier :=
  letI : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  haveI : IsIso (e.map.stalkMap c) := LocallyRingedSpace.IsOpenImmersion.stalk_iso e.map c
  (asIso (e.map.stalkMap c)).commRingCatIsoToRingEquiv

theorem embeddingStalkEquiv_apply (e : LocalEmbedding X) (c : e.carrier)
    (r : X.obj.left.presheaf.stalk (e.toPoint c)) :
    embeddingStalkEquiv e c r = (e.map.stalkMap c).hom r :=
  rfl

/-- **G10-02-03 (a).**  The native stalk at a chart point is the ambient chart germ ring modulo the
WHOLE defining ideal of the carrier. -/
def baseChartStalkEquiv (e : LocalEmbedding X) (c : e.carrier) :
    X.obj.left.presheaf.stalk (e.toPoint c) ≃+* HolGerm (ComplexModel e.dim) ⧸ chartIdeal e c :=
  (embeddingStalkEquiv e c).trans (actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c)

/-- The surjective presentation `𝒪_{ℂⁿ,0} → 𝒪_{X, e c}` of the base stalk. -/
def baseChartLift (e : LocalEmbedding X) (c : e.carrier) :
    HolGerm (ComplexModel e.dim) →+* X.obj.left.presheaf.stalk (e.toPoint c) :=
  (baseChartStalkEquiv e c).symm.toRingHom.comp (Ideal.Quotient.mk (chartIdeal e c))

theorem baseChartLift_apply (e : LocalEmbedding X) (c : e.carrier) (a : HolGerm (ComplexModel e.dim)) :
    baseChartLift e c a = (baseChartStalkEquiv e c).symm (Ideal.Quotient.mk (chartIdeal e c) a) :=
  rfl

theorem baseChartLift_surjective (e : LocalEmbedding X) (c : e.carrier) :
    Function.Surjective (baseChartLift e c) :=
  (baseChartStalkEquiv e c).symm.surjective.comp Ideal.Quotient.mk_surjective

/-- The kernel of the presentation is the WHOLE defining ideal. -/
theorem ker_baseChartLift (e : LocalEmbedding X) (c : e.carrier) :
    RingHom.ker (baseChartLift e c) = chartIdeal e c := by
  ext a
  rw [RingHom.mem_ker, baseChartLift_apply,
    map_eq_zero_iff _ (baseChartStalkEquiv e c).symm.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- The presentation read through the stalk isomorphism of the embedding. -/
theorem embeddingStalkEquiv_baseChartLift (e : LocalEmbedding X) (c : e.carrier)
    (a : HolGerm (ComplexModel e.dim)) :
    embeddingStalkEquiv e c (baseChartLift e c a) =
      (actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c).symm (Ideal.Quotient.mk _ a) := by
  rw [baseChartLift_apply]
  change embeddingStalkEquiv e c ((embeddingStalkEquiv e c).symm
    ((actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c).symm (Ideal.Quotient.mk _ a))) = _
  rw [RingEquiv.apply_symm_apply]

/-- The presentation transported to any point equal to the chart point. -/
def baseChartLiftAt (e : LocalEmbedding X) (c : e.carrier) (x : X.obj.left)
    (hc : e.toPoint c = x) : HolGerm (ComplexModel e.dim) →+* X.obj.left.presheaf.stalk x :=
  (eqToHom (congrArg X.obj.left.presheaf.stalk hc)).hom.comp (baseChartLift e c)

theorem baseChartLiftAt_surjective (e : LocalEmbedding X) (c : e.carrier) (x : X.obj.left)
    (hc : e.toPoint c = x) : Function.Surjective (baseChartLiftAt e c x hc) := by
  subst hc
  intro r
  exact baseChartLift_surjective e c r

theorem ker_baseChartLiftAt (e : LocalEmbedding X) (c : e.carrier) (x : X.obj.left)
    (hc : e.toPoint c = x) : RingHom.ker (baseChartLiftAt e c x hc) = chartIdeal e c := by
  subst hc
  ext a
  rw [RingHom.mem_ker, ← ker_baseChartLift e c, RingHom.mem_ker]
  exact Iff.rfl

/-- A carrier point of a local embedding inside a smaller ambient open, as a carrier point of the
restricted embedding (the point `c` of `exists_reduced_local_map_square`). -/
def restrictPoint (e : LocalEmbedding X) {U : Opens (ComplexModel e.dim)} (hUV : U ≤ e.ambient)
    (c : e.carrier) (hc : c.val.val ∈ U) : (e.restrict U hUV).carrier :=
  ⟨⟨c.val.val, hc⟩, c.property⟩

theorem restrictPoint_toPoint (e : LocalEmbedding X) {U : Opens (ComplexModel e.dim)}
    (hUV : U ≤ e.ambient) (c : e.carrier) (hc : c.val.val ∈ U) :
    (e.restrict U hUV).toPoint (restrictPoint e hUV c hc) = e.toPoint c :=
  rfl

/-! ### Commutation with the original morphism -/

section Square

variable {Y : SourceReducedComplexSpace} (p : Y ⟶ X) (eX : LocalEmbedding X) (eY : LocalEmbedding Y)
  {U : Opens (ComplexModel eY.dim)} (hUV : U ≤ eY.ambient) {f : U → eX.ambient}
  (hf : ContMDiff 𝓘(ℂ, ComplexModel eY.dim) 𝓘(ℂ, ComplexModel eX.dim) ∞ f)
  (hCD : ∀ z ∈ (eY.restrict U hUV).carrier, f z ∈ eX.carrier)
  (hsq : actualSubspaceMap hf hCD ≫ eX.map = (eY.restrict U hUV).map ≫ p.hom.left)

include hsq in
/-- The base point of the chart square. -/
theorem square_base (x' : (eY.restrict U hUV).carrier) :
    eX.toPoint ((actualSubspaceMap hf hCD).base x') =
      p.hom.left.base ((eY.restrict U hUV).toPoint x') :=
  congrArg (fun k => k.base x') hsq

include hsq in
/-- The base carrier point of the square is THE carrier point over the image (the base embedding is
injective), so one fixed base chart point serves every source point of its fibre. -/
theorem square_base_eq (x' : (eY.restrict U hUV).carrier) (c : eX.carrier) (x : X.obj.left)
    (h : p.hom.left.base ((eY.restrict U hUV).toPoint x') = x) (hc : eX.toPoint c = x) :
    (actualSubspaceMap hf hCD).base x' = c :=
  eX.toPoint_injective ((square_base p eX eY hUV hf hCD hsq x').trans (h.trans hc.symm))

/-- The ambient native base pullback through the target subspace map. -/
theorem nativeBasePullback_eq_subspaceMap (x' : (eY.restrict U hUV).carrier)
    (a : HolGerm (ComplexModel eX.dim)) :
    nativeBasePullback hf (eY.restrict U hUV).carrier x' a =
      ((actualSubspaceMap hf hCD).stalkMap x').hom
        ((actualSubspaceStalkChartEquiv (n := eX.dim) eX.carrier
          ((actualSubspaceMap hf hCD).base x')).symm (Ideal.Quotient.mk _ a)) := by
  have hsq' := ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square hf hCD x')
    ((actualStalkChartEquiv (n := eX.dim) (f x'.val)).symm a)
  simp only [ConcreteCategory.comp_apply] at hsq'
  have hincl : (actualSubspaceInclusion (n := eX.dim) eX.carrier).stalkMap
      ((actualSubspaceMap hf hCD).base x')
        ((actualStalkChartEquiv (n := eX.dim) (f x'.val)).symm a) =
      (actualSubspaceStalkChartEquiv (n := eX.dim) eX.carrier
        ((actualSubspaceMap hf hCD).base x')).symm (Ideal.Quotient.mk _ a) := by
    apply (actualSubspaceStalkChartEquiv (n := eX.dim) eX.carrier
      ((actualSubspaceMap hf hCD).base x')).injective
    rw [RingEquiv.apply_symm_apply]
    have h : actualSubspaceStalkChartEquiv (n := eX.dim) eX.carrier
        ((actualSubspaceMap hf hCD).base x')
        ((actualSubspaceInclusion (n := eX.dim) eX.carrier).stalkMap
          ((actualSubspaceMap hf hCD).base x')
            ((actualStalkChartEquiv (n := eX.dim) (f x'.val)).symm a)) =
        Ideal.Quotient.mk (chartIdeal eX ((actualSubspaceMap hf hCD).base x'))
          (actualStalkChartEquiv (n := eX.dim) (f x'.val)
            ((actualStalkChartEquiv (n := eX.dim) (f x'.val)).symm a)) :=
      inclusion_stalk_chart (n := eX.dim) eX.carrier ((actualSubspaceMap hf hCD).base x')
        ((actualStalkChartEquiv (n := eX.dim) (f x'.val)).symm a)
    rw [RingEquiv.apply_symm_apply] at h
    exact h
  refine hsq'.symm.trans ?_
  exact congrArg (fun z => ((actualSubspaceMap hf hCD).stalkMap x').hom z) hincl

include hsq in
/-- **G10-02-03 (b): commutation with the original morphism.**  The native stalk map of `p` at a
source carrier point, composed with the base presentation, is the ambient native base pullback of
the holomorphic representative `f`, read in the source model stalk. -/
theorem fibreStalkMap_baseChartLiftAt (x' : (eY.restrict U hUV).carrier) (x : X.obj.left)
    (h : p.hom.left.base ((eY.restrict U hUV).toPoint x') = x)
    (hc : eX.toPoint ((actualSubspaceMap hf hCD).base x') = x)
    (a : HolGerm (ComplexModel eX.dim)) :
    embeddingStalkEquiv (eY.restrict U hUV) x'
      (fibreStalkMap p x ((eY.restrict U hUV).toPoint x') h
        (baseChartLiftAt eX ((actualSubspaceMap hf hCD).base x') x hc a)) =
      nativeBasePullback hf (eY.restrict U hUV).carrier x' a := by
  rw [nativeBasePullback_eq_subspaceMap eX eY hUV hf hCD x' a]
  have key := stalk_square_apply (actualSubspaceMap hf hCD) eX.map (eY.restrict U hUV).map
    p.hom.left hsq.symm x' x h hc (baseChartLift eX ((actualSubspaceMap hf hCD).base x') a)
  have hu : (eX.map.stalkMap ((actualSubspaceMap hf hCD).base x')).hom
      (baseChartLift eX ((actualSubspaceMap hf hCD).base x') a) =
      (actualSubspaceStalkChartEquiv (n := eX.dim) eX.carrier
        ((actualSubspaceMap hf hCD).base x')).symm (Ideal.Quotient.mk _ a) :=
    embeddingStalkEquiv_baseChartLift eX _ a
  exact key.trans (congrArg (fun z => ((actualSubspaceMap hf hCD).stalkMap x').hom z) hu)

include hsq in
/-- The same commutation as an equality of ring maps out of the ambient base germs. -/
theorem fibreStalkMap_comp_baseChartLiftAt (x' : (eY.restrict U hUV).carrier) (x : X.obj.left)
    (h : p.hom.left.base ((eY.restrict U hUV).toPoint x') = x)
    (hc : eX.toPoint ((actualSubspaceMap hf hCD).base x') = x) :
    (fibreStalkMap p x ((eY.restrict U hUV).toPoint x') h).comp
        (baseChartLiftAt eX ((actualSubspaceMap hf hCD).base x') x hc) =
      (embeddingStalkEquiv (eY.restrict U hUV) x').symm.toRingHom.comp
        (nativeBasePullback hf (eY.restrict U hUV).carrier x') := by
  ext a
  apply (embeddingStalkEquiv (eY.restrict U hUV) x').injective
  rw [RingHom.comp_apply, fibreStalkMap_baseChartLiftAt p eX eY hUV hf hCD hsq x' x h hc a]
  change _ = embeddingStalkEquiv (eY.restrict U hUV) x'
    ((embeddingStalkEquiv (eY.restrict U hUV) x').symm _)
  rw [RingEquiv.apply_symm_apply]

include hsq in
/-- The ambient native base pullback kills the WHOLE base defining ideal. -/
theorem nativeBasePullback_chartIdeal (x' : (eY.restrict U hUV).carrier)
    (a : HolGerm (ComplexModel eX.dim))
    (ha : a ∈ chartIdeal eX ((actualSubspaceMap hf hCD).base x')) :
    nativeBasePullback hf (eY.restrict U hUV).carrier x' a = 0 := by
  have hz : baseChartLiftAt eX ((actualSubspaceMap hf hCD).base x')
      (p.hom.left.base ((eY.restrict U hUV).toPoint x'))
      (square_base p eX eY hUV hf hCD hsq x') a = 0 := by
    rw [← RingHom.mem_ker, ker_baseChartLiftAt]
    exact ha
  rw [← fibreStalkMap_baseChartLiftAt p eX eY hUV hf hCD hsq x' _ rfl
    (square_base p eX eY hUV hf hCD hsq x') a, hz, map_zero, map_zero]

end Square

end

end Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk
