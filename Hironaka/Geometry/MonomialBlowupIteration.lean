import Hironaka.Algebra.MonomialBlowupIteration
import Hironaka.Geometry.BlowupPrincipalFactor
import Hironaka.Geometry.PrincipalBlowup
import Hironaka.Geometry.NodeBlowupRegular

/-!
# Native blowup comparisons for the finite monomial node procedure

These are actual native scheme isomorphisms for actual mapped prefix centres.
They supply the local recurrence without assuming any comparison or regularity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Geometry.MonomialBlowupIteration

open Algebra.NodeBlowupChart Algebra.MonomialBlowupIteration

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- Transport an actual native blowup through equality of its centre ideals. -/
def blowupCenterEqIso {I J : Ideal A} (h : I = J) : affineBlowup I ≅ affineBlowup J :=
  eqToIso (congrArg affineBlowup h)

@[reassoc]
theorem blowupCenterEqIso_hom_structure {I J : Ideal A} (h : I = J) :
    (blowupCenterEqIso h).hom ≫ affineBlowupStructure J = affineBlowupStructure I := by
  subst J
  simp [blowupCenterEqIso]

@[reassoc]
theorem blowupCenterEqIso_inv_structure {I J : Ideal A} (h : I = J) :
    (blowupCenterEqIso h).inv ≫ affineBlowupStructure I = affineBlowupStructure J := by
  subst J
  simp [blowupCenterEqIso]

variable [IsDomain A]

/-- The nonzero coefficient factor remains nonzero in the genuine smaller node. -/
theorem coefficient_ne_zero (p q : A) (hp : p ≠ 0) (hq : q ≠ 0) :
    algebraMap A (Node A q) p ≠ 0 :=
  (map_ne_zero_iff _ (Algebra.NodeDomain.algebraMap_nodeQuotient_injective q hq)).mpr hp

/-- The next blowup on the continuing native chart is exactly the smaller-centre blowup. -/
def continuationCenterBlowupIso (p q s : A) (hp : p ≠ 0) (hq : q ≠ 0) :
    affineBlowup ((prefixCenter (p * q) (p * s)).map (continuationMap p q).toRingHom) ≅
      affineBlowup (prefixCenter q s) := by
  let : IsDomain (Node A q) := Algebra.NodeDomain.nodeQuotient_isDomain q hq
  exact (blowupCenterEqIso (prefixCenter_map_continuation p q s)).trans
    (BlowupPrincipalFactor.blowupPrincipalFactorIso
      (algebraMap A (Node A q) p) (prefixCenter q s) (coefficient_ne_zero p q hp hq))

@[reassoc]
theorem continuationCenterBlowupIso_hom_structure (p q s : A) (hp : p ≠ 0) (hq : q ≠ 0) :
    (continuationCenterBlowupIso p q s hp hq).hom ≫ affineBlowupStructure (prefixCenter q s) =
      affineBlowupStructure
        ((prefixCenter (p * q) (p * s)).map (continuationMap p q).toRingHom) := by
  let : IsDomain (Node A q) := Algebra.NodeDomain.nodeQuotient_isDomain q hq
  simp only [continuationCenterBlowupIso, Iso.trans_hom, Category.assoc,
    BlowupPrincipalFactor.blowupPrincipalFactorIso_hom_structure,
    blowupCenterEqIso_hom_structure]

/-- Every later original prefix centre gives an isomorphism on a finished native chart. -/
def finishedCenterBlowupIso (t q s : A) [Fact (t ≠ 0)] [Fact (q ≠ 0)] :
    affineBlowup ((prefixCenter (t * q) (t * s)).map (uChartOriginalMap t q).toRingHom) ≅
      Spec (CommRingCat.of (Node A t)) := by
  let : IsDomain (Node A t) := Algebra.NodeDomain.nodeQuotient_isDomain t Fact.out
  exact (blowupCenterEqIso (prefixCenter_map_uChart t q s)).trans
    (PrincipalBlowup.principalBlowupIso (coordinate t 0)
      (Algebra.NodeDomain.nodeCoordinate_ne_zero t Fact.out 0))

@[reassoc]
theorem finishedCenterBlowupIso_hom_structure (t q s : A)
    [Fact (t ≠ 0)] [Fact (q ≠ 0)] :
    (finishedCenterBlowupIso t q s).hom = affineBlowupStructure
      ((prefixCenter (t * q) (t * s)).map (uChartOriginalMap t q).toRingHom) := by
  let : IsDomain (Node A t) := Algebra.NodeDomain.nodeQuotient_isDomain t Fact.out
  change (blowupCenterEqIso (prefixCenter_map_uChart t q s)).hom ≫
    affineBlowupStructure (Ideal.span {coordinate t 0}) = _
  exact blowupCenterEqIso_hom_structure _

/-- The native blowup after any actual finite prefix has the accumulated principal factor removed. -/
def prefixCenterBlowupIso (a b : List A) (s : A) (ha : (0 : A) ∉ a) (hb : (0 : A) ∉ b) :
    affineBlowup ((prefixCenter (a ++ b).prod (a.prod * s)).map (prefixMap a b).toRingHom) ≅
      affineBlowup (prefixCenter b.prod s) := by
  let : IsDomain (Node A b.prod) := Algebra.NodeDomain.nodeQuotient_isDomain b.prod (List.prod_ne_zero hb)
  exact (blowupCenterEqIso (prefixCenter_map_prefix a b s)).trans
    (BlowupPrincipalFactor.blowupPrincipalFactorIso
      (algebraMap A (Node A b.prod) a.prod) (prefixCenter b.prod s)
      (coefficient_ne_zero a.prod b.prod (List.prod_ne_zero ha) (List.prod_ne_zero hb)))

@[reassoc]
theorem prefixCenterBlowupIso_hom_structure (a b : List A) (s : A)
    (ha : (0 : A) ∉ a) (hb : (0 : A) ∉ b) :
    (prefixCenterBlowupIso a b s ha hb).hom ≫ affineBlowupStructure (prefixCenter b.prod s) =
      affineBlowupStructure
        ((prefixCenter (a ++ b).prod (a.prod * s)).map (prefixMap a b).toRingHom) := by
  let : IsDomain (Node A b.prod) := Algebra.NodeDomain.nodeQuotient_isDomain b.prod (List.prod_ne_zero hb)
  simp only [prefixCenterBlowupIso, Iso.trans_hom, Category.assoc,
    BlowupPrincipalFactor.blowupPrincipalFactorIso_hom_structure,
    blowupCenterEqIso_hom_structure]

/-- The actual continuation chart, reoriented to retain the original coordinate order. -/
def continuationChartInclusion (t q : A) [Fact (t ≠ 0)] [Fact (q ≠ 0)] :
    Spec (CommRingCat.of (Node A q)) ⟶ affineBlowup (centerIdeal t q) :=
  Spec.map (nodeSwap q).toRingEquiv.toCommRingCatIso.hom ≫ tChartInclusion t q

instance continuationChartInclusion_isOpenImmersion (t q : A)
    [Fact (t ≠ 0)] [Fact (q ≠ 0)] : IsOpenImmersion (continuationChartInclusion t q) := by
  dsimp only [continuationChartInclusion]
  infer_instance

@[reassoc]
theorem continuationChartInclusion_structure (t q : A) [Fact (t ≠ 0)] [Fact (q ≠ 0)] :
    continuationChartInclusion t q ≫ affineBlowupStructure (centerIdeal t q) =
      Spec.map (CommRingCat.ofHom (continuationMap t q).toRingHom) := by
  rw [continuationChartInclusion, Category.assoc, tChartInclusion_structure,
    ← Spec.map_comp, continuationMap_eq_native]
  rfl

/-- The exact native chart maps with a consistent continuation coordinate at every recursive step. -/
def orientedNodeChartMap (t q : A) [Fact (t ≠ 0)] [Fact (q ≠ 0)] :
    (b : Bool) → NodeBlowupCover.nodeChartSource t q b ⟶ affineBlowup (centerIdeal t q)
  | false => uChartInclusion t q
  | true => continuationChartInclusion t q

instance orientedNodeChartMap_isOpenImmersion (t q : A)
    [Fact (t ≠ 0)] [Fact (q ≠ 0)] (b : Bool) : IsOpenImmersion (orientedNodeChartMap t q b) := by
  cases b <;> dsimp only [orientedNodeChartMap] <;> infer_instance

/-- Reorienting the parameter node gives a genuine native cover, not merely a ring presentation. -/
def orientedNodeBlowupOpenCover (t q : A) [Fact (t ≠ 0)] [Fact (q ≠ 0)] :
    (affineBlowup (centerIdeal t q)).OpenCover.{0} :=
  Scheme.Cover.mkOfCovers Bool (NodeBlowupCover.nodeChartSource t q) (orientedNodeChartMap t q) (by
    intro x
    have hcont : (continuationChartInclusion t q).opensRange = (tChartInclusion t q).opensRange := by
      dsimp only [continuationChartInclusion]
      rw [Scheme.Hom.opensRange_comp_of_isIso]
    have hx : x ∈ (uChartInclusion t q).opensRange ⊔ (continuationChartInclusion t q).opensRange := by
      rw [hcont, NodeBlowupCover.chartInclusions_sup_opensRange]
      trivial
    rcases hx with hu | ht
    · exact ⟨false, hu⟩
    · exact ⟨true, ht⟩)

/-- The next actual stage after removing a finite prefix, expressed by its genuine smaller centre. -/
def prefixStageBlowupIso (a : List A) (t : A) (b : List A)
    (ha : (0 : A) ∉ a) (ht : t ≠ 0) (hb : (0 : A) ∉ b) :
    affineBlowup ((prefixCenter (a ++ t :: b).prod (a.prod * t)).map
      (prefixMap a (t :: b)).toRingHom) ≅ affineBlowup (centerIdeal t b.prod) :=
  prefixCenterBlowupIso a (t :: b) t ha (by simp [Ne.symm ht, hb])

/-- The next original-prefix-centre blowup has its actual two smaller-node covering charts. -/
def prefixStageOpenCover (a : List A) (t : A) (b : List A)
    (ha : (0 : A) ∉ a) [Fact (t ≠ 0)] (hb : (0 : A) ∉ b) :
    (affineBlowup ((prefixCenter (a ++ t :: b).prod (a.prod * t)).map
      (prefixMap a (t :: b)).toRingHom)).OpenCover.{0} := by
  let : Fact (b.prod ≠ 0) := ⟨List.prod_ne_zero hb⟩
  exact (orientedNodeBlowupOpenCover t b.prod).pushforwardIso
    (prefixStageBlowupIso a t b ha Fact.out hb).inv

@[simp]
theorem prefixStageOpenCover_source_false (a : List A) (t : A) (b : List A)
    (ha : (0 : A) ∉ a) [Fact (t ≠ 0)] (hb : (0 : A) ∉ b) :
    (prefixStageOpenCover a t b ha hb).X false = Spec (CommRingCat.of (Node A t)) := rfl

@[simp]
theorem prefixStageOpenCover_source_true (a : List A) (t : A) (b : List A)
    (ha : (0 : A) ∉ a) [Fact (t ≠ 0)] (hb : (0 : A) ∉ b) :
    (prefixStageOpenCover a t b ha hb).X true = Spec (CommRingCat.of (Node A b.prod)) := rfl

@[simp]
theorem prefixStageOpenCover_map_false (a : List A) (t : A) (b : List A)
    (ha : (0 : A) ∉ a) [Fact (t ≠ 0)] (hb : (0 : A) ∉ b) :
    letI : Fact (b.prod ≠ 0) := ⟨List.prod_ne_zero hb⟩
    (prefixStageOpenCover a t b ha hb).f false =
      uChartInclusion t b.prod ≫ (prefixStageBlowupIso a t b ha Fact.out hb).inv := rfl

@[simp]
theorem prefixStageOpenCover_map_true (a : List A) (t : A) (b : List A)
    (ha : (0 : A) ∉ a) [Fact (t ≠ 0)] (hb : (0 : A) ∉ b) :
    letI : Fact (b.prod ≠ 0) := ⟨List.prod_ne_zero hb⟩
    (prefixStageOpenCover a t b ha hb).f true =
      continuationChartInclusion t b.prod ≫ (prefixStageBlowupIso a t b ha Fact.out hb).inv := rfl

/-- Every recursive prefix-map step factors through the actual native blowup and its actual chart. -/
theorem prefixMap_cons_factors_native (t : A) (a b : List A)
    [Fact (t ≠ 0)] (hab : (a ++ b).prod ≠ 0) :
    letI : Fact ((a ++ b).prod ≠ 0) := ⟨hab⟩
    Spec.map (CommRingCat.ofHom (prefixMap (t :: a) b).toRingHom) =
      Spec.map (CommRingCat.ofHom (prefixMap a b).toRingHom) ≫
        continuationChartInclusion t (a ++ b).prod ≫
          affineBlowupStructure (centerIdeal t (a ++ b).prod) := by
  let : Fact ((a ++ b).prod ≠ 0) := ⟨hab⟩
  rw [continuationChartInclusion_structure, ← Spec.map_comp]
  rfl

/-- The blowup of every later original centre is an isomorphism on a finished finite-prefix chart. -/
def finishedPrefixCenterBlowupIso (a : List A) (t : A) (b : List A) (s : A)
    (ha : (0 : A) ∉ a) [Fact (t ≠ 0)] [Fact (b.prod ≠ 0)] :
    affineBlowup ((prefixCenter (a ++ t :: b).prod (a.prod * (t * s))).map
      (finishedPrefixMap a t b).toRingHom) ≅ Spec (CommRingCat.of (Node A t)) := by
  let : IsDomain (Node A t) := Algebra.NodeDomain.nodeQuotient_isDomain t Fact.out
  exact (blowupCenterEqIso (prefixCenter_map_finishedPrefix a t b s)).trans
    (PrincipalBlowup.principalBlowupIso
      (algebraMap A (Node A t) a.prod * coordinate t 0)
      (mul_ne_zero (coefficient_ne_zero a.prod t (List.prod_ne_zero ha) Fact.out)
        (Algebra.NodeDomain.nodeCoordinate_ne_zero t Fact.out 0)))

@[reassoc]
theorem finishedPrefixCenterBlowupIso_hom_structure (a : List A) (t : A) (b : List A) (s : A)
    (ha : (0 : A) ∉ a) [Fact (t ≠ 0)] [Fact (b.prod ≠ 0)] :
    (finishedPrefixCenterBlowupIso a t b s ha).hom = affineBlowupStructure
      ((prefixCenter (a ++ t :: b).prod (a.prod * (t * s))).map
        (finishedPrefixMap a t b).toRingHom) := by
  let : IsDomain (Node A t) := Algebra.NodeDomain.nodeQuotient_isDomain t Fact.out
  change (blowupCenterEqIso (prefixCenter_map_finishedPrefix a t b s)).hom ≫
    affineBlowupStructure (Ideal.span {algebraMap A (Node A t) a.prod * coordinate t 0}) = _
  exact blowupCenterEqIso_hom_structure _

variable [IsRegularRing A]

/-- A finished chart remains regular under every later actual prefix-centre blowup. -/
theorem finishedCenterBlowup_isRegular (t q s : A) [Fact (t ≠ 0)] [Fact (q ≠ 0)]
    (ht : ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉ maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularScheme
      (affineBlowup ((prefixCenter (t * q) (t * s)).map (uChartOriginalMap t q).toRingHom)) :=
  (RegularNode.isRegularScheme_nodeQuotient t ht).of_isOpenImmersion
    (finishedCenterBlowupIso t q s).hom

/-- The finished chart at every actual finite stage is genuinely regular under the base parameter condition. -/
theorem prefixStage_finishedChart_isRegular (a : List A) (t : A) (b : List A)
    (ha : (0 : A) ∉ a) [Fact (t ≠ 0)] (hb : (0 : A) ∉ b)
    (ht : ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉ maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularScheme ((prefixStageOpenCover a t b ha hb).X false) :=
  RegularNode.isRegularScheme_nodeQuotient t ht

/-- Actual regularity also survives every later original centre after an arbitrary removed prefix. -/
theorem finishedPrefixCenterBlowup_isRegular (a : List A) (t : A) (b : List A) (s : A)
    (ha : (0 : A) ∉ a) [Fact (t ≠ 0)] [Fact (b.prod ≠ 0)]
    (ht : ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉ maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularScheme (affineBlowup ((prefixCenter (a ++ t :: b).prod (a.prod * (t * s))).map
      (finishedPrefixMap a t b).toRingHom)) :=
  (RegularNode.isRegularScheme_nodeQuotient t ht).of_isOpenImmersion
    (finishedPrefixCenterBlowupIso a t b s ha).hom

omit [IsDomain A] in
/-- The empty remaining product is a genuine regular terminal node. -/
theorem terminalNode_isRegular : IsRegularScheme (Spec (CommRingCat.of (Node A 1))) := by
  apply RegularNode.isRegularScheme_nodeQuotient
  intro p hp h
  exact False.elim (hp.ne_top (p.eq_top_iff_one.mpr h))

end Hironaka.Geometry.MonomialBlowupIteration
