import Hironaka.Resolution.HironakaChowRelativeGraphPresentation
import Hironaka.Resolution.HironakaG10FlatSimultaneousFlattener
import Hironaka.Coherence.CartanLocalReduction

/-! # G10.FLAT.01/02: the intrinsic point flattener of an ordinary intrinsic morphism

Let `G : C ⟶ D` be an ordinary intrinsic model morphism between actual analytic
subspaces (`C ⊆ M`, `M` a complex manifold of dimension `m`; `D ⊆ V`, `V` open in
`ℂ^n`), compatible with the point maps. Every point `x ∈ C` has local holomorphic
lifts `f : O → V` of `G` (`exists_actualSubspaceMap_local_holomorphic_lift`), and
each lift gives the actual relative graph presentation of the native stalk
`O_{C,x}` over the base germ ring `HolGerm ℂ^n` (translated at `G x`).

* `canonicalFlattenerIdeal_relativeGraph_eq`: two holomorphic maps whose germ
  pullbacks agree modulo the source ideal `J` give the SAME canonical flattener of
  their relative graph ideals (the identity of `S/J` is base-linear).
* `pullback_sub_mem_of_agree`: two lifts that agree pointwise on `C` near `x` have
  germ pullbacks congruent modulo the WHOLE chart stalk ideal of the vanishing ideal
  of `C` (actual subspaces are reduced).
* `pointFlattener G hG x`: ONE ideal of the base germ ring, chosen from `G` and `x`
  alone, before every target map and ideal; it equals the canonical flattener of the
  relative graph ideal of EVERY lift (`pointFlattener_eq`), is finitely generated and
  satisfies the universal flatness criterion for every analytic base map and every
  target ideal, both for the graph presentation and for the native stalk with its
  native base scalars (`flat_nativeStalk_iff`).
* FLAT.02: `fibreFlattener G hG L` is the SUM over an arbitrary set `L ⊆ C` of
  points (e.g. a compact subset of one fibre); it is finitely generated, a finite
  subset of `L` chosen before all target maps already generates it, and it gives the
  simultaneous universal criterion for ANY choice of lifts.

No persistence at nearby base points, no openness of flatness and no global
flattening is claimed. BP: hironaka-g10-flat-ordinary-point-flattener.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG10FlatOrdinaryPointFlattener
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaActualWholeStalkHolomorphicPullback
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaActualVanishingIntrinsicHSTransport
  HironakaActualAnalyticSubspaceIntrinsicLifting HironakaReducedComplexAnalyticSpaces
  HironakaChowRelativeGraphPresentation HironakaChowPresentationIndependentFlattener
  HironakaActualAnalyticBaseChangeCoefficients
  HironakaG10FlatSimultaneousFlattener

/-! ## The algebraic comparison -/

section Algebra
variable (d t : ℕ)
local instance (k : ℕ) :
    Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+k))) := tangentAlgebra d k

/-- Two relative graph quotients over the SAME source ideal `J` are base-linearly
equivalent as soon as the two germ pullbacks agree modulo `J`. -/
def relativeGraphLinearEquiv (F₁ F₂ : ComplexModel t → ComplexModel d)
    (hF₁ : ∀ᶠ z in 𝓝 (0 : ComplexModel t), DifferentiableAt ℂ F₁ z) (hF₁0 : F₁ 0 = 0)
    (hF₂ : ∀ᶠ z in 𝓝 (0 : ComplexModel t), DifferentiableAt ℂ F₂ z) (hF₂0 : F₂ 0 = 0)
    (J : Ideal (HolGerm (ComplexModel t)))
    (h : ∀ a, compAlgHom F₁ hF₁ hF₁0 a - compAlgHom F₂ hF₂ hF₂0 a ∈ J) :
    (HolGerm (ComplexModel (d+t)) ⧸ relativeGraphIdeal d t F₁ hF₁ J) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ relativeGraphIdeal d t F₂ hF₂ J) :=
  let Φ₁ := relativeGraphQuotientEquiv d t F₁ hF₁ hF₁0 J
  let Φ₂ := relativeGraphQuotientEquiv d t F₂ hF₂ hF₂0 J
  let E := Φ₁.trans Φ₂.symm
  have hbase : ∀ a : HolGerm (ComplexModel d),
      E (Ideal.Quotient.mk _ (tangentPullback d t a)) = Ideal.Quotient.mk _ (tangentPullback d t a) := by
    intro a
    apply Φ₂.injective
    change Φ₂ (Φ₂.symm (Φ₁ _)) = _
    rw [RingEquiv.apply_symm_apply, relativeGraphQuotientEquiv_mk, relativeGraphQuotientEquiv_mk,
      relativeGraphTrace_basePullback, relativeGraphTrace_basePullback]
    exact Ideal.Quotient.eq.mpr (h a)
  { E with
    map_smul' := fun a q => by
      change E (a • q) = a • E q
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      exact hbase a }

/-- Hence the canonical flattener ideals of the two relative graph ideals agree. -/
theorem canonicalFlattenerIdeal_relativeGraph_eq (F₁ F₂ : ComplexModel t → ComplexModel d)
    (hF₁ : ∀ᶠ z in 𝓝 (0 : ComplexModel t), DifferentiableAt ℂ F₁ z) (hF₁0 : F₁ 0 = 0)
    (hF₂ : ∀ᶠ z in 𝓝 (0 : ComplexModel t), DifferentiableAt ℂ F₂ z) (hF₂0 : F₂ 0 = 0)
    (J : Ideal (HolGerm (ComplexModel t)))
    (h : ∀ a, compAlgHom F₁ hF₁ hF₁0 a - compAlgHom F₂ hF₂ hF₂0 a ∈ J) :
    canonicalFlattenerIdeal d t (relativeGraphIdeal d t F₁ hF₁ J) =
      canonicalFlattenerIdeal d t (relativeGraphIdeal d t F₂ hF₂ J) :=
  canonicalFlattenerIdeal_eq_of_presentation_equiv d t t _ _
    (relativeGraphLinearEquiv d t F₁ F₂ hF₁ hF₁0 hF₂ hF₂0 J h)

/-- An `A`-algebra equivalence `S/I ≃ R` gives the `A/a`-linear equivalence of the
two reductions modulo `a`, for every ideal `a` of `A`. -/
def quotientSmulTopEquiv {A P R : Type*} [CommRing A] [CommRing P] [CommRing R]
    [Algebra A P] [Algebra A R] (Φ : P ≃ₐ[A] R) (a : Ideal A) :
    (P ⧸ a • (⊤ : Submodule A P)) ≃ₗ[A ⧸ a] (R ⧸ a • (⊤ : Submodule A R)) := by
  have hMap : (a • (⊤ : Submodule A P)).map Φ.toLinearEquiv.toLinearMap =
      a • (⊤ : Submodule A R) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr Φ.toLinearEquiv.surjective]
  exact (Submodule.Quotient.equiv _ _ Φ.toLinearEquiv hMap).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

end Algebra

/-! ## Germs vanishing on `C` -/

variable {m n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]

/-- Step 1 (germ membership). A germ whose representative vanishes on `C` (read in the
preferred chart at `x`, translated to the origin) lies in the WHOLE chart stalk ideal of
the vanishing ideal of `C`. -/
theorem mk_mem_wholeChartStalkIdeal_vanishing (C : Set M) (x : M)
    (H : ComplexModel m → ℂ) (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ H z)
    (hvan : ∀ᶠ y in 𝓝 x, y ∈ C →
      H ((chartAt (ComplexModel m) x) y - (chartAt (ComplexModel m) x) x) = 0) :
    HolGerm.mk H hH ∈ wholeChartStalkIdeal (vanishingIdeal (n := m) C) x x (mem_chart_source _ x) := by
  set e := chartAt (ComplexModel m) x
  set c := e x
  let f : M → ℂ := fun y => H (e y - c)
  have hW : OkaRelationSheaf.HolAt (fun w => H (w - c)) (e x) := by
    have ht : Tendsto (fun w : ComplexModel m => w - c) (𝓝 c) (𝓝 0) := by
      have := (continuous_sub_right c).tendsto c
      rwa [sub_self] at this
    filter_upwards [ht.eventually hH] with w hw
    exact hw.comp w (differentiableAt_id.sub_const c)
  have hf : HolomorphicAt m f x :=
    CartanLocalReduction.holomorphicAt_comp_chart (mem_chart_source _ x) hW
  refine Ideal.subset_span ⟨f, hf, ⟨hf, hvan⟩, ?_⟩
  unfold chartTranslatedGerm translatedGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  have hT : ∀ᶠ z in 𝓝 (0 : ComplexModel m), z + c ∈ e.target := by
    have : Tendsto (fun z : ComplexModel m => z + c) (𝓝 0) (𝓝 c) := by
      have := (continuous_add_const c).tendsto (0 : ComplexModel m)
      rwa [zero_add] at this
    exact this.eventually (e.open_target.mem_nhds (e.map_source (mem_chart_source _ x)))
  filter_upwards [hT] with z hz
  show H z = H (e (e.symm (z + c)) - c)
  rw [e.right_inv hz, add_sub_cancel_right]

omit [IsComplexManifold m M] in
/-- The translated map of a map defined on an open subset, evaluated at the chart
coordinate of a nearby point of the subset. -/
theorem actualTranslatedMap_open_apply {V : Opens (ComplexModel n)} {O : Opens M} (f : O → V)
    (x y : M) (hx : x ∈ O) (hy : y ∈ O) (hye : y ∈ (chartAt (ComplexModel m) x).source) :
    actualTranslatedMap (n := n) (m := m) f ⟨x,hx⟩
        ((chartAt (ComplexModel m) x) y - (chartAt (ComplexModel m) x) x) =
      (chartAt (ComplexModel n) (f ⟨x,hx⟩)) (f ⟨y,hy⟩) -
        (chartAt (ComplexModel n) (f ⟨x,hx⟩)) (f ⟨x,hx⟩) := by
  have hsrc : (⟨y,hy⟩ : O) ∈ (chartAt (ComplexModel m) (⟨x,hx⟩ : O)).source := by
    show (⟨y,hy⟩ : O) ∈ ((chartAt (ComplexModel m) x).subtypeRestr ⟨⟨x,hx⟩⟩).source
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hye
  have hc : (chartAt (ComplexModel m) x) y - (chartAt (ComplexModel m) x) x +
      (chartAt (ComplexModel m) (⟨x,hx⟩ : O)) ⟨x,hx⟩ =
        (chartAt (ComplexModel m) (⟨x,hx⟩ : O)) ⟨y,hy⟩ := by
    show (chartAt (ComplexModel m) x) y - (chartAt (ComplexModel m) x) x +
      (chartAt (ComplexModel m) x) x = (chartAt (ComplexModel m) x) y
    exact sub_add_cancel _ _
  unfold actualTranslatedMap
  rw [hc, (chartAt (ComplexModel m) (⟨x,hx⟩ : O)).left_inv hsrc]

/-- Step 2 (lift agreement ⇒ congruent base actions). Two holomorphic maps on open
neighbourhoods of `x ∈ C` that agree at every point of `C` give germ pullbacks that
agree modulo the WHOLE chart stalk ideal of the vanishing ideal of `C` at `x`. -/
theorem pullback_sub_mem_of_agree (C : Set M) {V : Opens (ComplexModel n)} {O₁ O₂ : Opens M}
    {f₁ : O₁ → V} {f₂ : O₂ → V}
    (hf₁ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f₁)
    (hf₂ : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f₂)
    (x : M) (h₁ : x ∈ O₁) (h₂ : x ∈ O₂) (hx : x ∈ C)
    (hagree : ∀ y ∈ C, ∀ (hy₁ : y ∈ O₁) (hy₂ : y ∈ O₂), f₁ ⟨y,hy₁⟩ = f₂ ⟨y,hy₂⟩)
    (a : HolGerm (ComplexModel n)) :
    actualHolomorphicGermPullback hf₁ ⟨x,h₁⟩ a - actualHolomorphicGermPullback hf₂ ⟨x,h₂⟩ a ∈
      wholeChartStalkIdeal (vanishingIdeal (n := m) C) x x (mem_chart_source _ x) := by
  induction a using HolGerm.induction_on with
  | h F hF =>
    unfold actualHolomorphicGermPullback
    rw [compAlgHom_mk, compAlgHom_mk, ← HolGerm.mk_sub']
    refine mk_mem_wholeChartStalkIdeal_vanishing C x _ _ ?_
    filter_upwards [O₁.isOpen.mem_nhds h₁, O₂.isOpen.mem_nhds h₂,
      (chartAt (ComplexModel m) x).open_source.mem_nhds (mem_chart_source _ x)] with y hy₁ hy₂ hye hyC
    show F (actualTranslatedMap (n := n) (m := m) f₁ ⟨x,h₁⟩ _) -
      F (actualTranslatedMap (n := n) (m := m) f₂ ⟨x,h₂⟩ _) = 0
    rw [actualTranslatedMap_open_apply f₁ x y h₁ hy₁ hye,
      actualTranslatedMap_open_apply f₂ x y h₂ hy₂ hye,
      hagree y hyC hy₁ hy₂, hagree x hx h₁ h₂, sub_self]

/-! ## Lifts of an ordinary intrinsic morphism -/

section Lift
variable {C : Set M} {V : Opens (ComplexModel n)} {D : Set V}
  (G : actualSubspaceLocallyRingedSpace (n := m) C ⟶ actualSubspaceLocallyRingedSpace (n := n) D)

/-- A local holomorphic lift of `G` near `x`, as supplied by
`exists_actualSubspaceMap_local_holomorphic_lift`. -/
structure OrdinaryLift (x : C) where
  /-- The open neighbourhood of `x` in the ambient manifold. -/
  O : Opens M
  mem : x.val ∈ O
  /-- The holomorphic lift. -/
  f : O → V
  hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f
  hCD : ∀ y ∈ (Subtype.val : O → M) ⁻¹' C, f y ∈ D
  lift : actualSubspaceMap hf hCD = actualOpenSubspaceMap (n := m) C O ≫ G

theorem nonempty_ordinaryLift (hG : G ≫ subspacePointMap (n := n) D = subspacePointMap (n := m) C)
    (x : C) : Nonempty (OrdinaryLift G x) := by
  obtain ⟨O,hx,f,hf,hCD,hLift⟩ := exists_actualSubspaceMap_local_holomorphic_lift G hG x
  exact ⟨⟨O,hx,f,hf,hCD,hLift⟩⟩

namespace OrdinaryLift
variable {G} {x : C} (L : OrdinaryLift G x)

/-- The point `x` in the open restriction of `C`. -/
def point : (Subtype.val : L.O → M) ⁻¹' C := ⟨⟨x.val,L.mem⟩,x.property⟩

/-- The actual relative graph ideal of the lift (whole source chart ideal, translated
original map, base coordinates first). -/
def graphIdeal : Ideal (HolGerm (ComplexModel (n+m))) :=
  nativeRelativeGraphIdeal L.hf _ L.point

/-- Step 3: a lift is pointwise equal to `G` on `C`. -/
theorem apply_eq (y : M) (hyO : y ∈ L.O) (hyC : y ∈ C) :
    L.f ⟨y,hyO⟩ = (G.base ⟨y,hyC⟩).val := by
  have h := congrArg (fun φ : actualSubspaceLocallyRingedSpace (n := m)
      ((Subtype.val : L.O → M) ⁻¹' C) ⟶ actualSubspaceLocallyRingedSpace (n := n) D =>
    (φ.base (⟨⟨y,hyO⟩,hyC⟩ : (Subtype.val : L.O → M) ⁻¹' C)).val) L.lift
  exact h

/-- Two lifts agree at every point of `C` in both domains. -/
theorem apply_eq_apply (L' : OrdinaryLift G x) (y : M) (hyC : y ∈ C) (hy : y ∈ L.O)
    (hy' : y ∈ L'.O) : L.f ⟨y,hy⟩ = L'.f ⟨y,hy'⟩ := by
  rw [L.apply_eq y hy hyC, L'.apply_eq y hy' hyC]

/-- The graph ideal, written with the M-level whole chart stalk ideal of `C`. -/
theorem graphIdeal_eq : L.graphIdeal =
    relativeGraphIdeal n m (actualTranslatedMap (n := n) (m := m) L.f ⟨x.val,L.mem⟩)
      (actualTranslatedMap_holomorphic L.hf ⟨x.val,L.mem⟩)
      (wholeChartStalkIdeal (vanishingIdeal (n := m) C) x.val x.val (mem_chart_source _ x.val)) := by
  have h := wholeChartStalkIdeal_vanishing_actual_open (n := m) L.O C ⟨x.val,L.mem⟩
  change relativeGraphIdeal n m _ _ (wholeChartStalkIdeal
    (vanishingIdeal (n := m) ((Subtype.val : L.O → M) ⁻¹' C)) ⟨x.val,L.mem⟩ ⟨x.val,L.mem⟩
      (mem_chart_source _ _)) = _
  rw [h]
  rfl

/-- Step 4 (lift independence): every two lifts have the SAME canonical flattener. -/
theorem canonicalFlattenerIdeal_graphIdeal_eq (L' : OrdinaryLift G x) :
    canonicalFlattenerIdeal n m L.graphIdeal = canonicalFlattenerIdeal n m L'.graphIdeal := by
  rw [L.graphIdeal_eq, L'.graphIdeal_eq]
  exact canonicalFlattenerIdeal_relativeGraph_eq n m _ _ _ (actualTranslatedMap_zero _ _) _
    (actualTranslatedMap_zero _ _) _ fun a =>
      pullback_sub_mem_of_agree C L.hf L'.hf x.val L.mem L'.mem x.property
        (fun y hyC hy hy' => L.apply_eq_apply L' y hyC hy hy') a

end OrdinaryLift

variable (hG : G ≫ subspacePointMap (n := n) D = subspacePointMap (n := m) C)

/-- The intrinsic point flattener: ONE ideal of the base germ ring `HolGerm ℂ^n`,
chosen from `G` and `x` alone, before all target maps and ideals. -/
def pointFlattener (x : C) : Ideal (HolGerm (ComplexModel n)) :=
  canonicalFlattenerIdeal n m (Classical.choice (nonempty_ordinaryLift G hG x)).graphIdeal

/-- The point flattener is the canonical flattener of EVERY lift. -/
theorem pointFlattener_eq (x : C) (L : OrdinaryLift G x) :
    pointFlattener G hG x = canonicalFlattenerIdeal n m L.graphIdeal :=
  OrdinaryLift.canonicalFlattenerIdeal_graphIdeal_eq _ L

theorem pointFlattener_fg (x : C) : (pointFlattener G hG x).FG :=
  canonicalFlattenerIdeal_fg n m _

local instance (k : ℕ) :
    Algebra (HolGerm (ComplexModel n)) (HolGerm (ComplexModel (n+k))) := tangentAlgebra n k

/-- Universal criterion at one point, for EVERY lift, EVERY analytic base map `φ` and
EVERY target ideal `a`. -/
theorem flat_iff_map_pointFlattener_le (x : C) (L : OrdinaryLift G x)
    (e : ℕ) (φ : ComplexModel e → ComplexModel n)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (a : Ideal (HolGerm (ComplexModel e))) :
    Module.Flat (HolGerm (ComplexModel e) ⧸ a)
      (HolGerm (ComplexModel (e+m)) ⧸
        (Ideal.map (jointBasePullback n e m φ hφ hφ0).toRingHom L.graphIdeal ⊔
          Ideal.map (tangentPullback e m).toRingHom a)) ↔
      Ideal.map (compAlgHom φ hφ hφ0).toRingHom (pointFlattener G hG x) ≤ a := by
  rw [pointFlattener_eq G hG x L]
  exact flat_iff_map_canonicalFlattenerIdeal_le n m L.graphIdeal e φ hφ hφ0 a

/-- Over the original base: flatness of the graph presentation modulo `a` is
`pointFlattener ≤ a`. -/
theorem flat_iff_pointFlattener_le (x : C) (L : OrdinaryLift G x)
    (a : Ideal (HolGerm (ComplexModel n))) :
    Module.Flat (HolGerm (ComplexModel n) ⧸ a)
      (HolGerm (ComplexModel (n+m)) ⧸ (L.graphIdeal ⊔ Ideal.map (tangentPullback n m).toRingHom a)) ↔
      pointFlattener G hG x ≤ a := by
  rw [pointFlattener_eq G hG x L]
  exact flat_iff_canonicalFlattenerIdeal_le n m L.graphIdeal a

/-- Native form: the actual stalk of `C` at `x` (in the open restriction of the lift),
with its NATIVE base scalars `nativeBasePullback`, is flat modulo `a` over
`HolGerm ℂ^n ⧸ a` exactly when `pointFlattener ≤ a`. -/
theorem flat_nativeStalk_iff (x : C) (L : OrdinaryLift G x)
    (a : Ideal (HolGerm (ComplexModel n))) :
    letI : Algebra (HolGerm (ComplexModel n))
        ((actualSubspaceSheaf (n := m) ((Subtype.val : L.O → M) ⁻¹' C)).presheaf.stalk L.point).carrier :=
      (nativeBasePullback L.hf _ L.point).toAlgebra
    Module.Flat (HolGerm (ComplexModel n) ⧸ a)
      (((actualSubspaceSheaf (n := m) ((Subtype.val : L.O → M) ⁻¹' C)).presheaf.stalk L.point).carrier ⧸
        a • (⊤ : Submodule (HolGerm (ComplexModel n))
          ((actualSubspaceSheaf (n := m) ((Subtype.val : L.O → M) ⁻¹' C)).presheaf.stalk
            L.point).carrier)) ↔
      pointFlattener G hG x ≤ a := by
  let : Algebra (HolGerm (ComplexModel n))
      ((actualSubspaceSheaf (n := m) ((Subtype.val : L.O → M) ⁻¹' C)).presheaf.stalk L.point).carrier :=
    (nativeBasePullback L.hf _ L.point).toAlgebra
  rw [← flat_iff_pointFlattener_le G hG x L a]
  let q₁ := originalBaseQuotientModuleEquiv n m L.graphIdeal a
  let q₂ := quotientSmulTopEquiv (nativeRelativeGraphAlgEquiv L.hf _ L.point) a
  let q := q₁.trans q₂
  constructor
  · intro h
    have := h
    exact Module.Flat.of_linearEquiv q
  · intro h
    have := h
    exact Module.Flat.of_linearEquiv q.symm

/-! ## FLAT.02: the fibre flattener -/

/-- The SUM (not the intersection) of the point flatteners over an arbitrary set of
points of `C` (e.g. a compact subset of one fibre). -/
def fibreFlattener (L : Set C) : Ideal (HolGerm (ComplexModel n)) :=
  ⨆ x : L, pointFlattener G hG x

/-- For ANY choice of lifts, the P1 family ideal is the fibre flattener. -/
theorem familyFlattenerIdeal_eq_fibreFlattener (L : Set C)
    (Λ : ∀ x : L, OrdinaryLift G x.val) :
    familyFlattenerIdeal n (fun _ : L => m) (fun x => (Λ x).graphIdeal) = fibreFlattener G hG L := by
  unfold familyFlattenerIdeal fibreFlattener
  exact iSup_congr fun x => (pointFlattener_eq G hG x.val (Λ x)).symm

theorem fibreFlattener_fg (L : Set C) : (fibreFlattener G hG L).FG := by
  let : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
  exact Ideal.fg_of_isNoetherianRing _

/-- FLAT.02: ONE finite subset `s ⊆ L`, chosen from `G` and `L` alone BEFORE all
target maps and ideals, generates the fibre flattener; for ANY lifts, ANY analytic
base map and ANY target ideal, flatness at the points of `s` is flatness at every
point of `L`, and both are equivalent to the containment of the pulled-back sum. -/
theorem exists_finite_fibre_selection (L : Set C) :
    ∃ s : Finset L, (⨆ x ∈ s, pointFlattener G hG x.val) = fibreFlattener G hG L ∧
      ∀ (Λ : ∀ x : L, OrdinaryLift G x.val)
        (e : ℕ) (φ : ComplexModel e → ComplexModel n)
        (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
        (a : Ideal (HolGerm (ComplexModel e))),
        ((∀ x ∈ s, Module.Flat (HolGerm (ComplexModel e) ⧸ a)
          (HolGerm (ComplexModel (e + m)) ⧸
            (Ideal.map (jointBasePullback n e m φ hφ hφ0).toRingHom (Λ x).graphIdeal ⊔
              Ideal.map (tangentPullback e m).toRingHom a))) ↔
        ∀ x : L, Module.Flat (HolGerm (ComplexModel e) ⧸ a)
          (HolGerm (ComplexModel (e + m)) ⧸
            (Ideal.map (jointBasePullback n e m φ hφ hφ0).toRingHom (Λ x).graphIdeal ⊔
              Ideal.map (tangentPullback e m).toRingHom a))) ∧
        ((∀ x : L, Module.Flat (HolGerm (ComplexModel e) ⧸ a)
          (HolGerm (ComplexModel (e + m)) ⧸
            (Ideal.map (jointBasePullback n e m φ hφ hφ0).toRingHom (Λ x).graphIdeal ⊔
              Ideal.map (tangentPullback e m).toRingHom a))) ↔
          Ideal.map (compAlgHom φ hφ hφ0).toRingHom (fibreFlattener G hG L) ≤ a) := by
  let : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
  obtain ⟨s,hs⟩ := exists_finset_iSup_eq (fun x : L => pointFlattener G hG x.val)
  refine ⟨s,hs,fun Λ e φ hφ hφ0 a => ?_⟩
  have hall : (∀ x : L, Module.Flat (HolGerm (ComplexModel e) ⧸ a)
      (HolGerm (ComplexModel (e + m)) ⧸
        (Ideal.map (jointBasePullback n e m φ hφ hφ0).toRingHom (Λ x).graphIdeal ⊔
          Ideal.map (tangentPullback e m).toRingHom a))) ↔
      Ideal.map (compAlgHom φ hφ hφ0).toRingHom (fibreFlattener G hG L) ≤ a := by
    rw [fibreFlattener, map_iSup_le_iff]
    exact forall_congr' fun x => flat_iff_map_pointFlattener_le G hG x.val (Λ x) e φ hφ hφ0 a
  refine ⟨?_, hall⟩
  rw [hall, fibreFlattener, ← hs, map_biSup_le_iff]
  exact forall₂_congr fun x _ => flat_iff_map_pointFlattener_le G hG x.val (Λ x) e φ hφ hφ0 a

/-- Over the original base, the fibre flattener is the LEAST ideal over which the
graph presentations at EVERY point of `L` (for ANY lifts) are flat. -/
theorem fibreFlattener_isLeast (L : Set C) (Λ : ∀ x : L, OrdinaryLift G x.val) :
    IsLeast {a : Ideal (HolGerm (ComplexModel n)) | ∀ x : L,
      Module.Flat (HolGerm (ComplexModel n) ⧸ a)
        (HolGerm (ComplexModel (n + m)) ⧸
          ((Λ x).graphIdeal ⊔ Ideal.map (tangentPullback n m).toRingHom a))}
      (fibreFlattener G hG L) := by
  rw [← familyFlattenerIdeal_eq_fibreFlattener G hG L Λ]
  exact familyFlattenerIdeal_isLeast n (fun _ : L => m) (fun x => (Λ x).graphIdeal)

end Lift

end
end Hironaka.HironakaG10FlatOrdinaryPointFlattener
