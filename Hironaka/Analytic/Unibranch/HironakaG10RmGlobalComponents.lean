import Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus
import Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference
import Hironaka.Analytic.GlobalComponents

/-!
# Native global components of a reduced complex space (Remmert for reduced spaces, item 5.2)

Run 0081 lane G10R2, item 5.2 of `G10MW/remmert-reduced-spaces.md` (Demailly, *Complex analytic and
differential geometry*, II.5.3, for a reduced complex space instead of an analytic subset of a manifold).
Blueprint: `hironaka-g10rm-global-components.tex`.

Let `Y` be a reduced complex space and `R` its intrinsic regular locus (open and dense,
`OriginalIntrinsicSingularLocus`).  The *native global components* of `Y` are the closures of the
connected components of `R` (`nativeGlobalComponents`).

* `isIrreducibleAnalyticSubset_of_mem_nativeGlobalComponents`: each is an irreducible analytic subset;
* `locallyFinite_nativeGlobalComponents`: they form a locally finite family;
* `sUnion_nativeGlobalComponents`: their union is `Y`;
* `exists_pureDim_of_irreducible`: an irreducible space has pure dimension; its regular locus is
  connected (`nativeComponent_eq_of_irreducible`), and conversely (`isIrreducibleAnalyticSubset_univ_iff`).

Also: native components are open (`isOpen_nativeComponent`), `closure K ∩ R = K`
(`closure_nativeComponent_inter`), the intrinsic dimension is constant along a component
(`intrinsicRegularAtDim_of_mem_nativeComponent`), and the identity theorem along a component
(`nativeComponent_subset_of_isOpen`).

Everything is proved chartwise from TN's manifold results (`RegularLocusComponent`, `GlobalComponents`):
in a local embedding `(Ω, C)` the intrinsic regular points are the regular points of `C`
(`intrinsicRegularAtDim_localEmbedding_iff`), and a TN component of the regular locus of `C` is mapped into
a single native component (`toPoint_mem_nativeComponent_of_mem_component`).
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10RmGlobalComponents

open Hironaka Hironaka
  HironakaIntrinsicComplexAnalyticRegularLocus RegularLocusComponent GlobalComponents
  SourceReducedComplexSpace

noncomputable section

/-! ### Manifold lemmas -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A locally finite union of analytic subsets is analytic. -/
theorem isComplexAnalyticSubset_iUnion_of_locallyFinite {ι : Type*} {f : ι → Set M}
    (hlf : LocallyFinite f) (hf : ∀ i, IsComplexAnalyticSubset (n := n) (f i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i, f i) := by
  classical
  refine AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens fun p => ?_
  obtain ⟨U, hU, hfin⟩ := hlf p
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp hU
  refine ⟨⟨V, hV⟩, hpV, ?_⟩
  have heq : ((↑) ⁻¹' (⋃ i, f i) : Set (⟨V, hV⟩ : Opens M)) =
      (↑) ⁻¹' (⋃ i ∈ hfin.toFinset, f i) := by
    ext x
    simp only [mem_preimage, mem_iUnion, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, ⟨(x : M), hi, hVU x.2⟩, hi⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨i, hi⟩
  rw [heq]
  exact AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
    (ConstantRankImage.isComplexAnalyticSubset_biUnion _ fun i _ => hf i) _

/-- The closure of a union of connected components of the regular locus of an analytic set is
analytic (it is the locally finite union of the corresponding global components). -/
theorem isComplexAnalyticSubset_closure_of_saturated {A Q : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hQR : Q ⊆ regularPoints (n := n) A)
    (hQ : ∀ y ∈ Q, component (n := n) A y ⊆ Q) :
    IsComplexAnalyticSubset (n := n) (closure Q) := by
  let S : Set (Set M) :=
    {B | B ∈ globalComponents (n := n) A ∧ ∃ y ∈ Q, B = closure (component (n := n) A y)}
  have hlf : LocallyFinite (fun B : S => (B : Set M)) :=
    (locallyFinite_globalComponents hA).comp_injective
      (g := fun B : S => (⟨B.1, B.2.1⟩ : globalComponents (n := n) A))
      fun B B' h => Subtype.ext (Subtype.mk.inj h)
  have hcl : ∀ B : S, IsClosed (B : Set M) := by
    rintro ⟨B, -, y, -, rfl⟩
    exact isClosed_closure
  have heq : closure Q = ⋃ B : S, (B : Set M) := by
    refine Subset.antisymm (closure_minimal ?_ (hlf.isClosed_iUnion hcl)) (iUnion_subset ?_)
    · intro y hy
      obtain ⟨k, hk⟩ := hQR hy
      exact mem_iUnion.mpr ⟨⟨_, closure_component_mem_globalComponents hk, y, hy, rfl⟩,
        subset_closure (mem_component_self hk)⟩
    · rintro ⟨B, -, y, hy, rfl⟩
      exact closure_mono (hQ y hy)
  rw [heq]
  refine isComplexAnalyticSubset_iUnion_of_locallyFinite hlf ?_
  rintro ⟨B, hB, -⟩
  exact (isComplexAnalyticallyIrreducible_of_mem_globalComponents hA hB).analytic

end Manifold

/-! ### Native components -/

variable {Y : SourceReducedComplexSpace}

/-- The connected component through `c` of the intrinsic regular locus of `Y`. -/
def nativeComponent (Y : SourceReducedComplexSpace) (c : Y.obj.left) : Set Y.obj.left :=
  connectedComponentIn (intrinsicRegularLocus Y.obj) c

/-- **Native global components** of `Y`: the closures of the connected components of the
intrinsic regular locus. -/
def nativeGlobalComponents (Y : SourceReducedComplexSpace) : Set (Set Y.obj.left) :=
  {B | ∃ c ∈ intrinsicRegularLocus Y.obj, B = closure (nativeComponent Y c)}

theorem nativeComponent_subset (Y : SourceReducedComplexSpace) (c : Y.obj.left) :
    nativeComponent Y c ⊆ intrinsicRegularLocus Y.obj :=
  connectedComponentIn_subset _ _

theorem mem_nativeComponent_self {c : Y.obj.left} (hc : c ∈ intrinsicRegularLocus Y.obj) :
    c ∈ nativeComponent Y c :=
  mem_connectedComponentIn hc

theorem isPreconnected_nativeComponent (Y : SourceReducedComplexSpace) (c : Y.obj.left) :
    IsPreconnected (nativeComponent Y c) :=
  isPreconnected_connectedComponentIn

theorem nativeComponent_eq {c y : Y.obj.left} (h : y ∈ nativeComponent Y c) :
    nativeComponent Y c = nativeComponent Y y :=
  connectedComponentIn_eq h

theorem closure_nativeComponent_mem_nativeGlobalComponents {c : Y.obj.left}
    (hc : c ∈ intrinsicRegularLocus Y.obj) :
    closure (nativeComponent Y c) ∈ nativeGlobalComponents Y :=
  ⟨c, hc, rfl⟩

/-- To prove a property of every point, prove it at the images of the carrier points of all local
embeddings. -/
theorem forall_of_forall_toPoint {P : Y.obj.left → Prop}
    (h : ∀ (e : LocalEmbedding Y) (z : e.carrier), P (e.toPoint z)) (x : Y.obj.left) : P x := by
  obtain ⟨z, hz⟩ := LocalEmbedding.mem_range_ofPoint Y x
  exact hz ▸ h _ z

/-! ### Chart lemmas -/

section Chart

variable (e : LocalEmbedding Y)

private theorem isOpen_image_toPoint' {W : Set e.ambient} (hW : IsOpen W) :
    IsOpen (e.toPoint '' (Subtype.val ⁻¹' W)) :=
  e.isOpenEmbedding_toPoint.isOpenMap _ (hW.preimage continuous_subtype_val)

private theorem mem_trace_iff (T : Set Y.obj.left) (c : e.carrier) :
    c.val ∈ Subtype.val '' (e.toPoint ⁻¹' T) ↔ e.toPoint c ∈ T := by
  constructor
  · rintro ⟨c', hc', h⟩
    obtain rfl : c' = c := Subtype.ext h
    exact hc'
  · intro h
    exact ⟨c, h, rfl⟩

/-- In a local embedding, the intrinsic regular points are the regular points of the carrier. -/
theorem toPoint_mem_intrinsicRegularLocus_iff (z : e.carrier) :
    e.toPoint z ∈ intrinsicRegularLocus Y.obj ↔
      z.val ∈ regularPoints (n := e.dim) e.carrier := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, (OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff Y e z d).mp hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, (OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff Y e z d).mpr hd⟩

/-- **A TN component of the carrier lies in one native component.** -/
theorem toPoint_mem_nativeComponent_of_mem_component {z w : e.carrier}
    (hw : w.val ∈ component (n := e.dim) e.carrier z.val) :
    e.toPoint w ∈ nativeComponent Y (e.toPoint z) := by
  have hzR : z.val ∈ regularPoints (n := e.dim) e.carrier :=
    connectedComponentIn_nonempty_iff.mp ⟨_, hw⟩
  have hz : z.val ∈ component (n := e.dim) e.carrier z.val := mem_connectedComponentIn hzR
  have hpre : IsPreconnected
      (Subtype.val ⁻¹' component (n := e.dim) e.carrier z.val : Set e.carrier) := by
    refine Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (component_subset (n := e.dim) _ _)]
    exact isPreconnected_connectedComponentIn
  have hS := hpre.image e.toPoint e.isOpenEmbedding_toPoint.continuous.continuousOn
  refine hS.subset_connectedComponentIn ⟨z, hz, rfl⟩ ?_ ⟨w, hw, rfl⟩
  rintro _ ⟨u, hu, rfl⟩
  exact (toPoint_mem_intrinsicRegularLocus_iff e u).mpr
    (component_subset_regularPoints (n := e.dim) _ _ hu)

/-- Near a regular point of the carrier, the carrier lies in its TN component. -/
theorem exists_isOpen_inter_subset_component (z : e.carrier)
    (hz : z.val ∈ regularPoints (n := e.dim) e.carrier) :
    ∃ W : Set e.ambient, IsOpen W ∧ z.val ∈ W ∧
      e.carrier ∩ W ⊆ component (n := e.dim) e.carrier z.val := by
  obtain ⟨j, hj⟩ := hz
  obtain ⟨W, hW, hzW, hWC, -, -⟩ :=
    exists_isOpen_inter_subset (mem_component_self (n := e.dim) hj) hj
  exact ⟨W, hW, hzW, hWC⟩

/-- Two regular carrier points whose TN components have meeting closures go to the same native
component. -/
theorem nativeComponent_eq_of_mem_closure_component {z y : e.carrier}
    (hz : z.val ∈ regularPoints (n := e.dim) e.carrier)
    (hzy : z.val ∈ closure (component (n := e.dim) e.carrier y.val)) :
    nativeComponent Y (e.toPoint z) = nativeComponent Y (e.toPoint y) := by
  obtain ⟨W, hW, hzW, hWC⟩ := exists_isOpen_inter_subset_component e z hz
  obtain ⟨w, hwW, hwy⟩ := mem_closure_iff.mp hzy W hW hzW
  have hwC : w ∈ e.carrier := component_subset (n := e.dim) _ _ hwy
  have h1 := toPoint_mem_nativeComponent_of_mem_component e (z := z) (w := ⟨w, hwC⟩)
    (hWC ⟨hwC, hwW⟩)
  have h2 := toPoint_mem_nativeComponent_of_mem_component e (z := y) (w := ⟨w, hwC⟩) hwy
  rw [nativeComponent_eq h1, nativeComponent_eq h2]

theorem exists_isOpen_subset_nativeComponent_toPoint (z : e.carrier)
    (hz : e.toPoint z ∈ intrinsicRegularLocus Y.obj) :
    ∃ O : Set Y.obj.left, IsOpen O ∧ e.toPoint z ∈ O ∧ O ⊆ nativeComponent Y (e.toPoint z) := by
  obtain ⟨W, hW, hzW, hWC⟩ :=
    exists_isOpen_inter_subset_component e z ((toPoint_mem_intrinsicRegularLocus_iff e z).mp hz)
  refine ⟨e.toPoint '' (Subtype.val ⁻¹' W), isOpen_image_toPoint' e hW, ⟨z, hzW, rfl⟩, ?_⟩
  rintro _ ⟨u, huW, rfl⟩
  exact toPoint_mem_nativeComponent_of_mem_component e (hWC ⟨u.property, huW⟩)

/-- The inverse image of a closure in a local embedding. -/
theorem toPoint_preimage_closure (Q : Set Y.obj.left) :
    e.toPoint ⁻¹' closure Q = Subtype.val ⁻¹' closure (Subtype.val '' (e.toPoint ⁻¹' Q)) := by
  rw [e.isOpenEmbedding_toPoint.isOpenMap.preimage_closure_eq_closure_preimage
    e.isOpenEmbedding_toPoint.continuous,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]

end Chart

/-! ### Local connectedness of the regular locus -/

/-- Every regular point has an open neighbourhood inside its native component. -/
theorem exists_isOpen_subset_nativeComponent {y : Y.obj.left}
    (hy : y ∈ intrinsicRegularLocus Y.obj) :
    ∃ O : Set Y.obj.left, IsOpen O ∧ y ∈ O ∧ O ⊆ nativeComponent Y y := by
  revert hy
  exact forall_of_forall_toPoint (P := fun y => y ∈ intrinsicRegularLocus Y.obj →
    ∃ O : Set Y.obj.left, IsOpen O ∧ y ∈ O ∧ O ⊆ nativeComponent Y y)
    (fun e z hz => exists_isOpen_subset_nativeComponent_toPoint e z hz) y

/-- Native components are open. -/
theorem isOpen_nativeComponent (Y : SourceReducedComplexSpace) (c : Y.obj.left) :
    IsOpen (nativeComponent Y c) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨O, hO, hyO, hOK⟩ := exists_isOpen_subset_nativeComponent (nativeComponent_subset Y c hy)
  rw [nativeComponent_eq hy]
  exact Filter.mem_of_superset (hO.mem_nhds hyO) hOK

/-- A regular point in the closure of a native component lies in it. -/
theorem mem_nativeComponent_of_mem_closure {c y : Y.obj.left}
    (hy : y ∈ intrinsicRegularLocus Y.obj) (hcl : y ∈ closure (nativeComponent Y c)) :
    y ∈ nativeComponent Y c := by
  obtain ⟨O, hO, hyO, hOK⟩ := exists_isOpen_subset_nativeComponent hy
  obtain ⟨z, hzO, hzK⟩ := mem_closure_iff.mp hcl O hO hyO
  rw [nativeComponent_eq hzK, ← nativeComponent_eq (hOK hzO)]
  exact mem_nativeComponent_self hy

/-- `closure K ∩ R = K`. -/
theorem closure_nativeComponent_inter (Y : SourceReducedComplexSpace) (c : Y.obj.left) :
    closure (nativeComponent Y c) ∩ intrinsicRegularLocus Y.obj = nativeComponent Y c :=
  Subset.antisymm (fun _ hy => mem_nativeComponent_of_mem_closure hy.2 hy.1)
    fun _ hy => ⟨subset_closure hy, nativeComponent_subset Y c hy⟩

/-! ### Analyticity -/

/-- The closure of a union of native components is analytic. -/
theorem isAnalyticSubset_closure_of_saturated {Q : Set Y.obj.left}
    (hQR : Q ⊆ intrinsicRegularLocus Y.obj) (hQ : ∀ y ∈ Q, nativeComponent Y y ⊆ Q) :
    Y.IsAnalyticSubset (closure Q) := by
  intro x
  refine ⟨LocalEmbedding.ofPoint Y x, LocalEmbedding.mem_range_ofPoint Y x, _, ?_,
    toPoint_preimage_closure _ Q⟩
  refine isComplexAnalyticSubset_closure_of_saturated (LocalEmbedding.ofPoint Y x).analytic ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact (toPoint_mem_intrinsicRegularLocus_iff _ z).mp (hQR hz)
  · rintro _ ⟨z, hz, rfl⟩ w hw
    have hwC : w ∈ (LocalEmbedding.ofPoint Y x).carrier := component_subset _ _ hw
    exact ⟨⟨w, hwC⟩, hQ _ hz
      (toPoint_mem_nativeComponent_of_mem_component _ (w := ⟨w, hwC⟩) hw), rfl⟩

/-- **The closure of a native component is analytic.** -/
theorem isAnalyticSubset_closure_nativeComponent (Y : SourceReducedComplexSpace) (c : Y.obj.left) :
    Y.IsAnalyticSubset (closure (nativeComponent Y c)) :=
  isAnalyticSubset_closure_of_saturated (nativeComponent_subset Y c) fun _ hy =>
    (nativeComponent_eq hy).symm.subset

/-! ### The identity theorem along a native component -/

/-- The union of the open sets meeting the component inside `T`. -/
private def openPart (Y : SourceReducedComplexSpace) (c : Y.obj.left) (T : Set Y.obj.left) :
    Set Y.obj.left :=
  ⋃₀ {O : Set Y.obj.left | IsOpen O ∧ O ∩ nativeComponent Y c ⊆ T}

/-- Chart step of the identity theorem: the open part is relatively closed in the component. -/
private theorem toPoint_mem_openPart {T : Set Y.obj.left} (hT : Y.IsAnalyticSubset T)
    {c : Y.obj.left} (e : LocalEmbedding Y) (z : e.carrier)
    (hzK : e.toPoint z ∈ nativeComponent Y c)
    (hcl : e.toPoint z ∈ closure (nativeComponent Y c ∩ openPart Y c T)) :
    e.toPoint z ∈ openPart Y c T := by
  have hzR : z.val ∈ regularPoints (n := e.dim) e.carrier :=
    (toPoint_mem_intrinsicRegularLocus_iff e z).mp (nativeComponent_subset Y c hzK)
  obtain ⟨W, hW, hzW, hWC⟩ := exists_isOpen_inter_subset_component e z hzR
  have hCK : ∀ u : e.carrier, u.val ∈ component (n := e.dim) e.carrier z.val →
      e.toPoint u ∈ nativeComponent Y c := fun u hu => by
    rw [nativeComponent_eq hzK]
    exact toPoint_mem_nativeComponent_of_mem_component e hu
  have hTa := HironakaG10NativeAnalyticClosureDifference.analytic_image_trace hT e
  obtain ⟨_, ⟨u, huW, rfl⟩, -, huV⟩ :=
    mem_closure_iff.mp hcl _ (isOpen_image_toPoint' e hW) ⟨z, hzW, rfl⟩
  obtain ⟨O', ⟨hO', hO'T⟩, huO'⟩ := mem_sUnion.mp huV
  obtain ⟨OΩ, hOΩ, hOΩeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp
    (hO'.preimage e.isOpenEmbedding_toPoint.continuous)
  have hsub : component (n := e.dim) e.carrier z.val ⊆ Subtype.val '' (e.toPoint ⁻¹' T) := by
    refine component_subset_of_isOpen hTa (hOΩ.inter hW) ?_ ?_
    · have huC : u.val ∈ component (n := e.dim) e.carrier z.val := hWC ⟨u.property, huW⟩
      have huOΩ : u ∈ (Subtype.val ⁻¹' OΩ : Set e.carrier) := by rw [hOΩeq]; exact huO'
      exact ⟨u.val, ⟨huOΩ, huW⟩, huC⟩
    · rintro v ⟨⟨hvO, -⟩, hvC⟩
      have hvC' : v ∈ e.carrier := component_subset (n := e.dim) _ _ hvC
      have hvO' : (⟨v, hvC'⟩ : e.carrier) ∈ e.toPoint ⁻¹' O' := by rw [← hOΩeq]; exact hvO
      exact ⟨⟨v, hvC'⟩, hO'T ⟨hvO', hCK ⟨v, hvC'⟩ hvC⟩, rfl⟩
  refine mem_sUnion.mpr ⟨e.toPoint '' (Subtype.val ⁻¹' W),
    ⟨isOpen_image_toPoint' e hW, ?_⟩, ⟨z, hzW, rfl⟩⟩
  rintro _ ⟨⟨v, hvW, rfl⟩, -⟩
  exact (mem_trace_iff e T v).mp (hsub (hWC ⟨v.property, hvW⟩))

/-- **Identity theorem along a native component**: an analytic set containing a nonempty relatively
open part of a native component contains the whole component. -/
theorem nativeComponent_subset_of_isOpen {T : Set Y.obj.left} (hT : Y.IsAnalyticSubset T)
    {c : Y.obj.left} {O : Set Y.obj.left} (hO : IsOpen O)
    (hne : (O ∩ nativeComponent Y c).Nonempty) (hOT : O ∩ nativeComponent Y c ⊆ T) :
    nativeComponent Y c ⊆ T := by
  have hV : IsOpen (openPart Y c T) := isOpen_sUnion fun W hW => hW.1
  have hV' : IsOpen (closure (nativeComponent Y c ∩ openPart Y c T))ᶜ :=
    isClosed_closure.isOpen_compl
  have hstep : ∀ x : Y.obj.left, x ∈ nativeComponent Y c →
      x ∈ closure (nativeComponent Y c ∩ openPart Y c T) → x ∈ openPart Y c T :=
    forall_of_forall_toPoint (P := fun x => x ∈ nativeComponent Y c →
      x ∈ closure (nativeComponent Y c ∩ openPart Y c T) → x ∈ openPart Y c T)
      fun e z => toPoint_mem_openPart hT e z
  have hcover : nativeComponent Y c ⊆
      openPart Y c T ∪ (closure (nativeComponent Y c ∩ openPart Y c T))ᶜ := by
    intro x hxK
    by_cases hx : x ∈ closure (nativeComponent Y c ∩ openPart Y c T)
    · exact Or.inl (hstep x hxK hx)
    · exact Or.inr hx
  have hdisj : nativeComponent Y c ∩
      (openPart Y c T ∩ (closure (nativeComponent Y c ∩ openPart Y c T))ᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨hxK, hxV, hxcl⟩
    exact hxcl (subset_closure ⟨hxK, hxV⟩)
  rcases isPreconnected_iff_subset_of_disjoint.mp (isPreconnected_nativeComponent Y c) _ _ hV hV'
      hcover hdisj with hKV | hKV
  · intro x hxK
    obtain ⟨W, ⟨-, hWT⟩, hxW⟩ := mem_sUnion.mp (hKV hxK)
    exact hWT ⟨hxW, hxK⟩
  · exfalso
    obtain ⟨z, hzO, hzK⟩ := hne
    have hzV : z ∈ openPart Y c T := mem_sUnion.mpr ⟨O, ⟨hO, hOT⟩, hzO⟩
    exact hKV hzK (subset_closure ⟨hzK, hzV⟩)

/-! ### 5.2.1 Irreducibility -/

/-- **The closure of a native component is irreducible.** -/
theorem isIrreducibleAnalyticSubset_closure_nativeComponent {c : Y.obj.left}
    (hc : c ∈ intrinsicRegularLocus Y.obj) :
    Y.IsIrreducibleAnalyticSubset (closure (nativeComponent Y c)) := by
  have hcK := mem_nativeComponent_self hc
  refine ⟨isAnalyticSubset_closure_nativeComponent Y c, ⟨c, subset_closure hcK⟩, ?_⟩
  intro B₁ B₂ hB₁ hB₂ hB₁C hB₂C hunion
  by_cases h₁ : ∃ O : Set Y.obj.left, IsOpen O ∧ (O ∩ nativeComponent Y c).Nonempty ∧
      O ∩ nativeComponent Y c ⊆ B₁
  · obtain ⟨O, hO, hne, hOB⟩ := h₁
    exact Or.inl (Subset.antisymm
      (closure_minimal (nativeComponent_subset_of_isOpen hB₁ hO hne hOB) hB₁.isClosed) hB₁C)
  by_cases h₂ : ∃ O : Set Y.obj.left, IsOpen O ∧ (O ∩ nativeComponent Y c).Nonempty ∧
      O ∩ nativeComponent Y c ⊆ B₂
  · obtain ⟨O, hO, hne, hOB⟩ := h₂
    exact Or.inr (Subset.antisymm
      (closure_minimal (nativeComponent_subset_of_isOpen hB₂ hO hne hOB) hB₂.isClosed) hB₂C)
  exfalso
  have hsub : B₂ᶜ ∩ nativeComponent Y c ⊆ B₁ := by
    rintro z ⟨hz₂, hzK⟩
    have hz : z ∈ B₁ ∪ B₂ := by rw [← hunion]; exact subset_closure hzK
    exact hz.resolve_right hz₂
  have hempty : ¬ (B₂ᶜ ∩ nativeComponent Y c).Nonempty := fun hne =>
    h₁ ⟨B₂ᶜ, hB₂.isClosed.isOpen_compl, hne, hsub⟩
  have hK₂ : nativeComponent Y c ⊆ B₂ := by
    intro z hzK
    by_contra hz₂
    exact hempty ⟨z, hz₂, hzK⟩
  exact h₂ ⟨univ, isOpen_univ, ⟨c, mem_univ c, hcK⟩, fun z hz => hK₂ hz.2⟩

/-- **5.2.1** Each native global component is an irreducible analytic subset. -/
theorem isIrreducibleAnalyticSubset_of_mem_nativeGlobalComponents {B : Set Y.obj.left}
    (hB : B ∈ nativeGlobalComponents Y) : Y.IsIrreducibleAnalyticSubset B := by
  obtain ⟨c, hc, rfl⟩ := hB
  exact isIrreducibleAnalyticSubset_closure_nativeComponent hc

theorem isAnalyticSubset_of_mem_nativeGlobalComponents {B : Set Y.obj.left}
    (hB : B ∈ nativeGlobalComponents Y) : Y.IsAnalyticSubset B :=
  (isIrreducibleAnalyticSubset_of_mem_nativeGlobalComponents hB).1

theorem isClosed_of_mem_nativeGlobalComponents {B : Set Y.obj.left}
    (hB : B ∈ nativeGlobalComponents Y) : IsClosed B :=
  (isAnalyticSubset_of_mem_nativeGlobalComponents hB).isClosed

/-! ### 5.2.2 Local finiteness -/

private theorem exists_isOpen_finite_toPoint (e : LocalEmbedding Y) (z₀ : e.carrier) :
    ∃ U : Set Y.obj.left, IsOpen U ∧ e.toPoint z₀ ∈ U ∧
      {B | B ∈ nativeGlobalComponents Y ∧ (B ∩ U).Nonempty}.Finite := by
  classical
  obtain ⟨UΩ, hUΩ, hz₀U, hfin⟩ :=
    exists_isOpen_finite_globalComponents (n := e.dim) e.analytic z₀.val
  let Φ : Set e.ambient → Set Y.obj.left := fun B' =>
    if h : ∃ y : e.carrier, y.val ∈ regularPoints (n := e.dim) e.carrier ∧
        B' = closure (component (n := e.dim) e.carrier y.val)
    then closure (nativeComponent Y (e.toPoint h.choose)) else ∅
  refine ⟨e.toPoint '' (Subtype.val ⁻¹' UΩ), isOpen_image_toPoint' e hUΩ, ⟨z₀, hz₀U, rfl⟩,
    (hfin.image Φ).subset ?_⟩
  rintro B ⟨⟨c, -, rfl⟩, x, hxB, hxU⟩
  obtain ⟨_, ⟨z, hzU, rfl⟩, hzK⟩ :=
    mem_closure_iff.mp hxB _ (isOpen_image_toPoint' e hUΩ) hxU
  have hzR : z.val ∈ regularPoints (n := e.dim) e.carrier :=
    (toPoint_mem_intrinsicRegularLocus_iff e z).mp (nativeComponent_subset Y c hzK)
  obtain ⟨k, hk⟩ := hzR
  have hex : ∃ y : e.carrier, y.val ∈ regularPoints (n := e.dim) e.carrier ∧
      closure (component (n := e.dim) e.carrier z.val) =
        closure (component (n := e.dim) e.carrier y.val) := ⟨z, ⟨k, hk⟩, rfl⟩
  refine ⟨closure (component (n := e.dim) e.carrier z.val),
    ⟨closure_component_mem_globalComponents hk, z.val,
      subset_closure (mem_component_self hk), hzU⟩, ?_⟩
  have hmem : z.val ∈ closure (component (n := e.dim) e.carrier hex.choose.val) := by
    rw [← hex.choose_spec.2]
    exact subset_closure (mem_component_self hk)
  have h1 : nativeComponent Y (e.toPoint z) = nativeComponent Y (e.toPoint hex.choose) :=
    nativeComponent_eq_of_mem_closure_component e ⟨k, hk⟩ hmem
  show Φ _ = _
  simp only [Φ, dif_pos hex]
  rw [← h1, ← nativeComponent_eq hzK]

/-- Every point has an open neighbourhood meeting only finitely many native global components. -/
theorem exists_isOpen_finite_nativeGlobalComponents (p : Y.obj.left) :
    ∃ U : Set Y.obj.left, IsOpen U ∧ p ∈ U ∧
      {B | B ∈ nativeGlobalComponents Y ∧ (B ∩ U).Nonempty}.Finite :=
  forall_of_forall_toPoint (P := fun p => ∃ U : Set Y.obj.left, IsOpen U ∧ p ∈ U ∧
      {B | B ∈ nativeGlobalComponents Y ∧ (B ∩ U).Nonempty}.Finite)
    (fun e z => exists_isOpen_finite_toPoint e z) p

/-- **5.2.2** The native global components form a locally finite family. -/
theorem locallyFinite_nativeGlobalComponents (Y : SourceReducedComplexSpace) :
    LocallyFinite (fun B : nativeGlobalComponents Y => (B : Set Y.obj.left)) := by
  intro p
  obtain ⟨U, hU, hpU, hfin⟩ := exists_isOpen_finite_nativeGlobalComponents p
  exact ⟨U, hU.mem_nhds hpU,
    (hfin.preimage Subtype.val_injective.injOn).subset fun B hB => ⟨B.2, hB⟩⟩

/-! ### 5.2.3 Covering -/

/-- **5.2.3** The native global components cover `Y`. -/
theorem sUnion_nativeGlobalComponents (Y : SourceReducedComplexSpace) :
    ⋃₀ nativeGlobalComponents Y = univ := by
  have hcl : IsClosed (⋃₀ nativeGlobalComponents Y) := by
    rw [sUnion_eq_iUnion]
    exact (locallyFinite_nativeGlobalComponents Y).isClosed_iUnion fun B =>
      isClosed_of_mem_nativeGlobalComponents B.2
  refine eq_univ_of_univ_subset ?_
  rw [← (OriginalIntrinsicSingularLocus.dense_intrinsicRegularLocus Y).closure_eq]
  refine closure_minimal ?_ hcl
  intro y hy
  exact ⟨_, closure_nativeComponent_mem_nativeGlobalComponents hy,
    subset_closure (mem_nativeComponent_self hy)⟩

/-- Every point lies in some native global component. -/
theorem exists_mem_nativeGlobalComponents (y : Y.obj.left) :
    ∃ B ∈ nativeGlobalComponents Y, y ∈ B := by
  have hy : y ∈ ⋃₀ nativeGlobalComponents Y := by
    rw [sUnion_nativeGlobalComponents]; exact mem_univ y
  obtain ⟨B, hB, hyB⟩ := hy
  exact ⟨B, hB, hyB⟩

/-! ### 5.2.4 Dimension -/

/-- A point is not an intrinsic regular point of two different dimensions. -/
theorem eq_of_intrinsicRegularAtDim {y : Y.obj.left} {k j : ℕ}
    (hk : intrinsicRegularAtDim Y.obj y k) (hj : intrinsicRegularAtDim Y.obj y j) : k = j := by
  revert hk hj
  refine forall_of_forall_toPoint (P := fun y => intrinsicRegularAtDim Y.obj y k →
    intrinsicRegularAtDim Y.obj y j → k = j) (fun e z hk hj => ?_) y
  exact RegularPointDimension.eq_of_regularAtDim
    ((OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff Y e z k).mp hk)
    ((OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff Y e z j).mp hj)

/-- The intrinsic dimension is constant along a native component. -/
theorem intrinsicRegularAtDim_of_mem_nativeComponent {c : Y.obj.left} {d : ℕ}
    (hc : intrinsicRegularAtDim Y.obj c d) {y : Y.obj.left} (hy : y ∈ nativeComponent Y c) :
    intrinsicRegularAtDim Y.obj y d := by
  have hu : IsOpen {x : Y.obj.left | intrinsicRegularAtDim Y.obj x d} :=
    isOpen_intrinsicRegularAtDim Y.obj d
  have hv : IsOpen {x : Y.obj.left | ∃ j, j ≠ d ∧ intrinsicRegularAtDim Y.obj x j} := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨j, hjd, hj⟩
    exact Filter.mem_of_superset ((isOpen_intrinsicRegularAtDim Y.obj j).mem_nhds hj)
      fun z hz => ⟨j, hjd, hz⟩
  have hcover : nativeComponent Y c ⊆ {x : Y.obj.left | intrinsicRegularAtDim Y.obj x d} ∪
      {x : Y.obj.left | ∃ j, j ≠ d ∧ intrinsicRegularAtDim Y.obj x j} := by
    intro x hx
    obtain ⟨j, hj⟩ := nativeComponent_subset Y c hx
    by_cases hjd : j = d
    · exact Or.inl (hjd ▸ hj)
    · exact Or.inr ⟨j, hjd, hj⟩
  have hdisj : nativeComponent Y c ∩ ({x : Y.obj.left | intrinsicRegularAtDim Y.obj x d} ∩
      {x : Y.obj.left | ∃ j, j ≠ d ∧ intrinsicRegularAtDim Y.obj x j}) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨-, hxd, j, hjd, hj⟩
    exact hjd (eq_of_intrinsicRegularAtDim hj hxd)
  rcases isPreconnected_iff_subset_of_disjoint.mp (isPreconnected_nativeComponent Y c) _ _ hu hv
      hcover hdisj with hKu | hKv
  · exact hKu hy
  · exfalso
    obtain ⟨j, hjd, hj⟩ := hKv (mem_nativeComponent_self ⟨d, hc⟩)
    exact hjd (eq_of_intrinsicRegularAtDim hj hc)

/-- **An irreducible space has a connected regular locus**: it is the native component of any of its
regular points. -/
theorem nativeComponent_eq_of_irreducible (h : Y.IsIrreducibleAnalyticSubset univ)
    {c : Y.obj.left} (hc : c ∈ intrinsicRegularLocus Y.obj) :
    nativeComponent Y c = intrinsicRegularLocus Y.obj := by
  have hKR := nativeComponent_subset Y c
  have hQ : ∀ y ∈ intrinsicRegularLocus Y.obj \ nativeComponent Y c,
      nativeComponent Y y ⊆ intrinsicRegularLocus Y.obj \ nativeComponent Y c := by
    rintro y ⟨hyR, hyK⟩ x hx
    refine ⟨nativeComponent_subset Y y hx, fun hxK => hyK ?_⟩
    rw [nativeComponent_eq hxK, ← nativeComponent_eq hx]
    exact mem_nativeComponent_self hyR
  have hKa := isAnalyticSubset_closure_nativeComponent Y c
  have hQa := isAnalyticSubset_closure_of_saturated sdiff_subset hQ
  have hunion : (univ : Set Y.obj.left) = closure (nativeComponent Y c) ∪
      closure (intrinsicRegularLocus Y.obj \ nativeComponent Y c) := by
    rw [← closure_union, union_sdiff_cancel hKR,
      (OriginalIntrinsicSingularLocus.dense_intrinsicRegularLocus Y).closure_eq]
  rcases h.2.2 _ _ hKa hQa (subset_univ _) (subset_univ _) hunion with h1 | h2
  · refine Subset.antisymm hKR fun y hy => mem_nativeComponent_of_mem_closure hy ?_
    rw [← h1]
    exact mem_univ y
  · exfalso
    have hc' : c ∈ closure (intrinsicRegularLocus Y.obj \ nativeComponent Y c) := by
      rw [← h2]
      exact mem_univ c
    obtain ⟨y, hyK, -, hyK'⟩ :=
      mem_closure_iff.mp hc' _ (isOpen_nativeComponent Y c) (mem_nativeComponent_self hc)
    exact hyK' hyK

/-- **5.2.4** An irreducible reduced complex space has pure dimension: all intrinsic regular points
have the same dimension `d`, and every local-embedding carrier is of pure dimension `d`. -/
theorem exists_pureDim_of_irreducible (h : Y.IsIrreducibleAnalyticSubset univ) :
    ∃ d : ℕ, (∀ y k, intrinsicRegularAtDim Y.obj y k → k = d) ∧
      ∀ e : LocalEmbedding Y, AnalyticDimensionBasics.IsPureDim (n := e.dim) e.carrier d := by
  obtain ⟨x, -⟩ := h.2.1
  have : Nonempty Y.obj.left := ⟨x⟩
  obtain ⟨c, d, hd⟩ := (OriginalIntrinsicSingularLocus.dense_intrinsicRegularLocus Y).nonempty
  have hpure : ∀ y k, intrinsicRegularAtDim Y.obj y k → k = d := by
    intro y k hy
    have hyK : y ∈ nativeComponent Y c := by
      rw [nativeComponent_eq_of_irreducible h ⟨d, hd⟩]
      exact ⟨k, hy⟩
    exact eq_of_intrinsicRegularAtDim hy (intrinsicRegularAtDim_of_mem_nativeComponent hd hyK)
  refine ⟨d, hpure, fun e y j hy => ?_⟩
  exact hpure _ j ((OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff Y e
    ⟨y, hy.2.1⟩ j).mpr hy)

/-- **Irreducibility of a space**: `Y` is irreducible iff its regular locus is nonempty and
connected. -/
theorem isIrreducibleAnalyticSubset_univ_iff :
    Y.IsIrreducibleAnalyticSubset univ ↔
      (intrinsicRegularLocus Y.obj).Nonempty ∧ IsPreconnected (intrinsicRegularLocus Y.obj) := by
  constructor
  · intro h
    obtain ⟨x, -⟩ := h.2.1
    have : Nonempty Y.obj.left := ⟨x⟩
    obtain ⟨c, hc⟩ := (OriginalIntrinsicSingularLocus.dense_intrinsicRegularLocus Y).nonempty
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [← nativeComponent_eq_of_irreducible h hc]
    exact isPreconnected_nativeComponent Y c
  · rintro ⟨⟨c, hc⟩, hpre⟩
    have heq : closure (nativeComponent Y c) = univ := by
      rw [nativeComponent, hpre.connectedComponentIn hc,
        (OriginalIntrinsicSingularLocus.dense_intrinsicRegularLocus Y).closure_eq]
    rw [← heq]
    exact isIrreducibleAnalyticSubset_closure_nativeComponent hc

end

end Hironaka.Analytic.Unibranch.HironakaG10RmGlobalComponents
