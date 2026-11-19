import Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference
import Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
import Hironaka.Analytic.ThinDimensionDrop
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Resolution.HironakaG11IntrinsicRegularOpenImmersion

/-!
# Native dimension bounds for subsets of reduced complex spaces (G10-03-14.a–d)

Run 0081 lane G10EP, plan items G10-03-14.a–d (consumer: Hironaka's `I_n`/`II_n` double induction, lane
G10RD).  Blueprint: `hironaka-g10ep-native-dimension.tex`.

`NativeDimLE X B n`: in EVERY native local embedding `(Ω, C) → X`, every regular point of the trace of `B`
in `Ω` has dimension `≤ n` (TN's `AnalyticDimensionBasics.DimLE`).  Main results:

* D1 `nativeDimLE_of_subset_of_dense`: a subset `C` of an analytic `B` with `B ⊆ closure (B \ C)` has
  dimension one less (TN `ThinDimensionDrop.dimLE_pred_of_thin`);
* D2 `relNonflat_eq_empty_of_nativeDimLE_zero`: over an analytic `B` of dimension `0` every family is flat
  (`B` is discrete, TN `not_accPt_of_locDimLE_zero`, and a reduced point is a flat base);
* D3 (general form) `nativeDimLE_closure_preimage`: the closure of `σ⁻¹ (B \ D)` for `σ` an isomorphism over
  `Dᶜ` and `B` closed has the same dimension bound (a chart of the source is pushed through the local
  isomorphism off the exceptional set; same ambient space, so no transition maps);
* D4 `exists_nativeDimLE_univ`: a compact space has a dimension bound (finitely many charts; regular
  dimension of chart carriers is intrinsic, `intrinsicRegularAtDim_model_iff`).
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10EpNativeDim

open Hironaka Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace HironakaG10HirGermFlattener HironakaG10RelativeNonflatStrata

noncomputable section

section Trace

variable {X : SourceReducedComplexSpace}

/-- The trace of a set of `X` in a local embedding, as a subset of the ambient open set. -/
def trace (e : LocalEmbedding X) (B : Set X.obj.left) : Set e.ambient :=
  Subtype.val '' (e.toPoint ⁻¹' B)

theorem mem_trace (e : LocalEmbedding X) (B : Set X.obj.left) (c : e.carrier) :
    c.val ∈ trace e B ↔ e.toPoint c ∈ B := by
  constructor
  · rintro ⟨c', hc', h⟩
    obtain rfl : c' = c := Subtype.ext h
    exact hc'
  · intro h
    exact ⟨c, h, rfl⟩

theorem trace_subset_carrier (e : LocalEmbedding X) (B : Set X.obj.left) :
    trace e B ⊆ e.carrier := by
  rintro _ ⟨c, -, rfl⟩
  exact c.property

theorem trace_univ (e : LocalEmbedding X) : trace e univ = e.carrier := by
  rw [trace, preimage_univ, image_univ, Subtype.range_coe]

theorem trace_mono (e : LocalEmbedding X) {B C : Set X.obj.left} (h : C ⊆ B) :
    trace e C ⊆ trace e B :=
  image_mono (preimage_mono h)

/-- The image in `X` of the carrier points lying in an open subset of the ambient space is open. -/
theorem isOpen_image_toPoint (e : LocalEmbedding X) {O : Set e.ambient} (hO : IsOpen O) :
    IsOpen (e.toPoint '' (Subtype.val ⁻¹' O)) :=
  e.isOpenEmbedding_toPoint.isOpenMap _ (hO.preimage continuous_subtype_val)

/-- **Regular points of chart carriers are intrinsic**: a carrier point is a regular point of the carrier
of dimension `d` iff its image is an intrinsic regular point of `X` of dimension `d`. -/
theorem regularAtDim_carrier_iff (e : LocalEmbedding X) (c : e.carrier) (d : ℕ) :
    RegularAtDim (n := e.dim) e.carrier c.val d ↔ intrinsicRegularAtDim X.obj (e.toPoint c) d :=
  (intrinsicRegularAtDim_model_iff e.carrier c).symm.trans
    (HironakaG11IntrinsicRegularOpenImmersion.intrinsicRegularAtDim_map_iff e.map
      e.isOpenImmersion e.overPoint c d).symm

end Trace

/-! ### The native dimension bound -/

/-- **`dim B ≤ n` natively**: in every local embedding, every regular point of the trace of `B` has
dimension at most `n`. -/
def NativeDimLE (X : SourceReducedComplexSpace) (B : Set X.obj.left) (n : ℕ) : Prop :=
  ∀ e : LocalEmbedding X, AnalyticDimensionBasics.DimLE (n := e.dim) (trace e B) n

variable {X : SourceReducedComplexSpace}

theorem NativeDimLE.mono {B : Set X.obj.left} {n m : ℕ} (h : NativeDimLE X B n) (hnm : n ≤ m) :
    NativeDimLE X B m :=
  fun e y k hy => (h e y k hy).trans hnm

theorem nativeDimLE_empty (X : SourceReducedComplexSpace) (n : ℕ) : NativeDimLE X ∅ n := by
  intro e y k hy
  have h := hy.2.1
  simp only [trace, preimage_empty, image_empty, mem_empty_iff_false] at h

/-- Analytic subsets of an analytic set of dimension `≤ n` have dimension `≤ n`. -/
theorem NativeDimLE.anti {B C : Set X.obj.left} (hB : X.IsAnalyticSubset B) (hCB : C ⊆ B) {n : ℕ}
    (h : NativeDimLE X B n) : NativeDimLE X C n := fun e =>
  DimensionMonotone.DimLE.anti
    (HironakaG10NativeAnalyticClosureDifference.analytic_image_trace hB e) (trace_mono e hCB) (h e)

/-! ### D1: nowhere dense subsets drop the dimension -/

/-- **D1.**  If `C ⊆ B`, `B` analytic, `B ⊆ closure (B \ C)` (`C` is nowhere dense in `B`) and
`dim B ≤ n + 1`, then `dim C ≤ n`. -/
theorem nativeDimLE_of_subset_of_dense {B C : Set X.obj.left} (hB : X.IsAnalyticSubset B)
    (hCB : C ⊆ B) (hdense : B ⊆ closure (B \ C)) {n : ℕ} (h : NativeDimLE X B (n + 1)) :
    NativeDimLE X C n := by
  intro e
  have hT := HironakaG10NativeAnalyticClosureDifference.analytic_image_trace hB e
  have hthin : ∀ O : Set e.ambient, IsOpen O → O ∩ trace e B ⊆ trace e C →
      O ∩ trace e B = ∅ := by
    intro O hO hOsub
    apply eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨hpO, c, hcB, rfl⟩
    have hmem : e.toPoint c ∈ e.toPoint '' (Subtype.val ⁻¹' O) := ⟨c, hpO, rfl⟩
    obtain ⟨_, ⟨c', hc'O, rfl⟩, hc'B, hc'C⟩ :=
      mem_closure_iff.mp (hdense hcB) _ (isOpen_image_toPoint e hO) hmem
    have hc' : c'.val ∈ trace e C := hOsub ⟨hc'O, (mem_trace e B c').mpr hc'B⟩
    exact hc'C ((mem_trace e C c').mp hc')
  have := ThinDimensionDrop.dimLE_pred_of_thin hT (trace_mono e hCB) hthin (h e)
  simpa using this

/-- **D1, in the shape of the double induction** (the analyticity of `C` is not needed). -/
theorem nativeDimLE_of_analytic_subset_of_dense {B C : Set X.obj.left} (hB : X.IsAnalyticSubset B)
    (_hC : X.IsAnalyticSubset C) (hCB : C ⊆ B) (hdense : B ⊆ closure (B \ C)) {n : ℕ}
    (h : NativeDimLE X B (n + 1)) : NativeDimLE X C n :=
  nativeDimLE_of_subset_of_dense hB hCB hdense h

/-! ### D2: zero-dimensional bases are flat -/

/-- Every point of an analytic set of native dimension `0` is isolated in it. -/
theorem exists_isolated_of_nativeDimLE_zero {B : Set X.obj.left} (hB : X.IsAnalyticSubset B)
    (h : NativeDimLE X B 0) {x : X.obj.left} (hx : x ∈ B) :
    ∃ U : Set X.obj.left, IsOpen U ∧ x ∈ U ∧ U ∩ B ⊆ {x} := by
  let e := LocalEmbedding.ofPoint X x
  obtain ⟨c, hc⟩ := LocalEmbedding.mem_range_ofPoint X x
  have hcx : e.toPoint c = x := hc
  have hT := HironakaG10NativeAnalyticClosureDifference.analytic_image_trace hB e
  have hcT : c.val ∈ trace e B := (mem_trace e B c).mpr (by rw [hcx]; exact hx)
  have hacc := AnalyticDimensionBasics.not_accPt_of_locDimLE_zero hT hcT ((h e).locDimLE c.val)
  rw [accPt_iff_nhds] at hacc
  push Not at hacc
  obtain ⟨N, hN, hNT⟩ := hacc
  obtain ⟨O, hON, hO, hcO⟩ := mem_nhds_iff.mp hN
  refine ⟨e.toPoint '' (Subtype.val ⁻¹' O), isOpen_image_toPoint e hO, ⟨c, hcO, hcx⟩, ?_⟩
  rintro _ ⟨⟨c', hc'O, rfl⟩, hc'B⟩
  have hval : c'.val = c.val := hNT c'.val ⟨hON hc'O, (mem_trace e B c').mpr hc'B⟩
  rw [mem_singleton_iff, ← hcx, Subtype.ext hval]

/-- At an isolated point of `B` the reduced vanishing ideal of `B` contains the maximal ideal. -/
theorem maximalIdeal_le_vanishingIdealAt {B : Set X.obj.left} {x : X.obj.left}
    {U : Set X.obj.left} (hU : IsOpen U) (hxU : x ∈ U) (hUB : U ∩ B ⊆ {x}) :
    IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk x) ≤
      vanishingIdealAt X.obj.left B x := by
  intro g hg
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.obj.left.presheaf g
  apply Ideal.subset_span
  let W : Opens X.obj.left := V ⊓ ⟨U, hU⟩
  have hxW : x ∈ W := ⟨hxV, hxU⟩
  refine ⟨W, hxW, X.obj.left.presheaf.map (homOfLE (show W ≤ V from inf_le_left)).op t, ?_, ?_⟩
  · exact X.obj.left.presheaf.germ_res_apply (homOfLE (show W ≤ V from inf_le_left)) x hxW t
  · intro z hz hzB
    have hzx : z = x := hUB ⟨hz.2, hzB⟩
    subst hzx
    rw [X.obj.left.presheaf.germ_res_apply (homOfLE (show W ≤ V from inf_le_left)) z hz t]
    exact hg

/-- **D2.**  Over an analytic set of native dimension `0` every family is flat: `s₁(f/B) = ∅`. -/
theorem relNonflat_eq_empty_of_nativeDimLE_zero {Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    {B : Set X.obj.left} (hB : X.IsAnalyticSubset B) (h : NativeDimLE X B 0) :
    relNonflat f B = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxB, hnf⟩
  obtain ⟨U, hU, hxU, hUB⟩ := exists_isolated_of_nativeDimLE_zero hB h hxB
  exact hnf (FlatOverAt.mono (maximalIdeal_le_vanishingIdealAt hU hxU hUB)
    (flatOverAt_maximalIdeal x))

/-! ### D4: compact spaces have finite dimension -/

/-- **D4.**  A compact reduced complex space has a native dimension bound. -/
theorem exists_nativeDimLE_univ (X : SourceReducedComplexSpace) [CompactSpace X.obj.left] :
    ∃ n, NativeDimLE X univ n := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X.obj.left => range (LocalEmbedding.ofPoint X x).toPoint)
    (fun x => (LocalEmbedding.ofPoint X x).isOpen_range_toPoint)
    (fun x _ => mem_iUnion.mpr ⟨x, LocalEmbedding.mem_range_ofPoint X x⟩)
  refine ⟨t.sup fun x => (LocalEmbedding.ofPoint X x).dim, ?_⟩
  intro e y k hy
  have hyC : y ∈ e.carrier := trace_subset_carrier e univ hy.2.1
  have hy' : RegularAtDim (n := e.dim) e.carrier y k := by
    rw [← trace_univ e]
    exact hy
  have hint := (regularAtDim_carrier_iff e ⟨y, hyC⟩ k).mp hy'
  obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.mp (ht (mem_univ (e.toPoint ⟨y, hyC⟩)))
  obtain ⟨c, hc⟩ := hx
  rw [← hc] at hint
  have hk := ((regularAtDim_carrier_iff _ c k).mpr hint).1
  exact hk.trans (Finset.le_sup (f := fun x => (LocalEmbedding.ofPoint X x).dim) hxt)

/-! ### D3 (general form): closures of inverse images under local isomorphisms -/

section Push

variable {X' : SourceReducedComplexSpace}

/-- Push a local embedding of `X'` forward along `σ : X' ⟶ X` when its image lies in the range of an
open immersion `j` with `j ≫ σ` an open immersion. -/
def pushChart (σ : X' ⟶ X) {V : LocallyRingedSpace.{0}} (j : V ⟶ X'.obj.left)
    [LocallyRingedSpace.IsOpenImmersion j] [LocallyRingedSpace.IsOpenImmersion (j ≫ σ.hom.left)]
    (e : LocalEmbedding X') (hr : range e.map.base ⊆ range j.base) : LocalEmbedding X where
  dim := e.dim
  ambient := e.ambient
  carrier := e.carrier
  analytic := e.analytic
  map := LocallyRingedSpace.IsOpenImmersion.lift j e.map hr ≫ j ≫ σ.hom.left
  isOpenImmersion := by
    have : LocallyRingedSpace.IsOpenImmersion
        (LocallyRingedSpace.IsOpenImmersion.lift j e.map hr ≫ j) := by
      rw [LocallyRingedSpace.IsOpenImmersion.lift_fac]
      exact e.isOpenImmersion
    have : LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift j e.map hr) :=
      HironakaG10ChowStrictTransformCalculus.isOpenImmersion_of_comp _ j
    infer_instance
  overPoint := by
    rw [Category.assoc, Category.assoc, Over.w σ.hom, ← Category.assoc,
      LocallyRingedSpace.IsOpenImmersion.lift_fac]
    exact e.overPoint

theorem pushChart_toPoint (σ : X' ⟶ X) {V : LocallyRingedSpace.{0}} (j : V ⟶ X'.obj.left)
    [LocallyRingedSpace.IsOpenImmersion j] [LocallyRingedSpace.IsOpenImmersion (j ≫ σ.hom.left)]
    (e : LocalEmbedding X') (hr : range e.map.base ⊆ range j.base) (c : e.carrier) :
    (pushChart σ j e hr).toPoint c = σ.hom.left.base (e.toPoint c) := by
  have h : (LocallyRingedSpace.IsOpenImmersion.lift j e.map hr ≫ j).base c = e.map.base c := by
    rw [LocallyRingedSpace.IsOpenImmersion.lift_fac]
  exact congrArg σ.hom.left.base h

end Push

/-- **D3, general form.**  Let `σ : X' ⟶ X` be an isomorphism over `Dᶜ` and `B ⊆ X` closed with
`dim B ≤ n`.  Then the closure of `σ⁻¹ (B \ D)` (the strict transform of `B`) has `dim ≤ n`. -/
theorem nativeDimLE_closure_preimage {X' : SourceReducedComplexSpace} (σ : X' ⟶ X)
    {D : Set X.obj.left} (hσ : IsIsoOver σ Dᶜ) {B : Set X.obj.left} (hB : IsClosed B) {n : ℕ}
    (h : NativeDimLE X B n) : NativeDimLE X' (closure (σ.hom.left.base ⁻¹' (B \ D))) n := by
  set B' := closure (σ.hom.left.base ⁻¹' (B \ D)) with hB'
  intro e y k hy
  obtain ⟨c, hcB', rfl⟩ := hy.2.1
  -- regular points of dimension `k` near `c`, and one of them off the exceptional set
  obtain ⟨N, hN, hNo, hcN⟩ := mem_nhds_iff.mp (RegularPatchNeighborhood.eventually_regularAtDim hy)
  obtain ⟨_, ⟨c', hc'N, rfl⟩, hc'⟩ :=
    mem_closure_iff.mp hcB' _ (isOpen_image_toPoint e hNo) ⟨c, hcN, rfl⟩
  have hc'B' : e.toPoint c' ∈ B' := subset_closure hc'
  have hreg : RegularAtDim (n := e.dim) (trace e B') c'.val k :=
    hN hc'N ((mem_trace e B' c').mpr hc'B')
  -- the local isomorphism off the exceptional set
  obtain ⟨V, j, hj, hjr, hjσ, -⟩ := hσ
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  let : LocallyRingedSpace.IsOpenImmersion (j ≫ σ.hom.left) := hjσ
  have hgood : ∀ x' : X'.obj.left, x' ∈ range j.base → (x' ∈ B' ↔ σ.hom.left.base x' ∈ B) := by
    intro x' hx'
    rw [hjr] at hx'
    constructor
    · intro hx'B
      exact closure_minimal (preimage_mono sdiff_subset)
        (hB.preimage σ.hom.left.base.hom.continuous) hx'B
    · intro hσx
      exact subset_closure ⟨hσx, hx'⟩
  -- restrict the chart to an ambient open set mapping into `range j`
  have hGo : IsOpen (e.toPoint ⁻¹' range j.base) :=
    hj.base_open.isOpen_range.preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hGo
  let T : Opens (ComplexModel e.dim) :=
    ⟨Subtype.val '' t, e.ambient.isOpen.isOpenMap_subtype_val t ht⟩
  have hT : T ≤ e.ambient := by
    rintro _ ⟨z, -, rfl⟩
    exact z.property
  have hmemT : ∀ z : e.ambient, z.val ∈ T → z ∈ t := by
    rintro z ⟨w, hw, hwz⟩
    obtain rfl : w = z := Subtype.ext hwz
    exact hw
  have hr : range (e.restrict T hT).map.base ⊆ range j.base := by
    rintro _ ⟨z, rfl⟩
    change e.toPoint ⟨Opens.inclusion hT z.val, z.property⟩ ∈ range j.base
    have hz : (⟨Opens.inclusion hT z.val, z.property⟩ : e.carrier) ∈ Subtype.val ⁻¹' t :=
      hmemT _ z.val.property
    rw [hts] at hz
    exact hz
  let e₂ : LocalEmbedding X := pushChart σ j (e.restrict T hT) hr
  have hpt : ∀ w : e₂.carrier, e₂.toPoint w =
      σ.hom.left.base (e.toPoint ⟨Opens.inclusion hT w.val, w.property⟩) :=
    fun w => pushChart_toPoint σ j (e.restrict T hT) hr w
  have hmemB : ∀ w : e₂.carrier, e₂.toPoint w ∈ B ↔
      e.toPoint ⟨Opens.inclusion hT w.val, w.property⟩ ∈ B' := by
    intro w
    rw [hpt]
    exact (hgood _ (hr ⟨w, rfl⟩)).symm
  -- the point `c'` in the restricted chart
  have hc'G : c' ∈ e.toPoint ⁻¹' range j.base := by
    rw [hjr]
    exact hc'.2
  rw [← hts] at hc'G
  have hc'T : c'.val.val ∈ T := ⟨c'.val, hc'G, rfl⟩
  have hinter : (Subtype.val '' trace e B' : Set (ComplexModel e.dim)) ∩ (T : Set (ComplexModel e.dim)) =
      (Subtype.val '' trace e₂ B : Set (ComplexModel e.dim)) ∩ (T : Set (ComplexModel e.dim)) := by
    ext v
    constructor
    · rintro ⟨⟨_, ⟨a, haB, rfl⟩, rfl⟩, hvT⟩
      exact ⟨⟨⟨a.val.val, hvT⟩, ⟨⟨⟨a.val.val, hvT⟩, a.property⟩, (hmemB _).mpr haB, rfl⟩, rfl⟩, hvT⟩
    · rintro ⟨⟨_, ⟨w, hwB, rfl⟩, rfl⟩, hvT⟩
      exact ⟨⟨Opens.inclusion hT w.val, ⟨⟨Opens.inclusion hT w.val, w.property⟩,
        (hmemB w).mp hwB, rfl⟩, rfl⟩, hvT⟩
  have h1 : RegularAtDim (n := e.dim) (Subtype.val '' trace e B' : Set (ComplexModel e.dim))
      c'.val.val k := AnalyticSubsetOpens.regularAtDim_image_val_iff.mpr hreg
  have h2 : RegularAtDim (n := e.dim) (Subtype.val '' trace e₂ B : Set (ComplexModel e.dim))
      c'.val.val k := RegularPointDimension.regularAtDim_of_inter_eq T.isOpen hc'T hinter h1
  have h3 : RegularAtDim (n := e₂.dim) (trace e₂ B) ⟨c'.val.val, hc'T⟩ k :=
    AnalyticSubsetOpens.regularAtDim_image_val_iff.mp h2
  exact h e₂ _ k h3

end

end Hironaka.Analytic.Unibranch.HironakaG10EpNativeDim
