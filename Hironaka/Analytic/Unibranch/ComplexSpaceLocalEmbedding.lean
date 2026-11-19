import Hironaka.Analytic.Unibranch.ReducedComplexSpaces
import Hironaka.Resolution.HironakaReducedComplexAnalyticMorphismCharts
import Hironaka.Analytic.AnalyticSubsetPreimage

/-!
# Local embeddings of reduced complex spaces

A complex space of the book is reduced, Hausdorff and paracompact; in this
project it is an object of `SourceReducedComplexSpace`, a locally ringed space
over the complex point which is locally isomorphic to an embedded model
`(Ω, C)`: an open set `Ω ⊆ ℂ^N`, a closed analytic subset `C ⊆ Ω`, and the
quotient of `𝒪_Ω` by the full vanishing ideal of `C`.

A *local embedding* of `X` (`LocalEmbedding`) is an open immersion of such a
model into `X` over the complex point. Its image `V` is an open subset of `X`
and the inverse isomorphism `V ≅ (Ω, C) ↪ Ω` is a closed immersion of `V` into
`Ω`; conversely, since all complex spaces are reduced, a closed immersion of an
open subspace `V` into `Ω` identifies `V` with the reduced closed subspace on an
analytic subset of `Ω`. Local embeddings are therefore the "closed immersions
`V ↪ Ω`" in `def:unibranch:L105`.

Main results:

* `LocalEmbedding.ofPoint`: every point lies in the image of a local embedding.
* `LocalEmbedding.restrict`: restriction of a local embedding to a smaller
  ambient open set.
* `LocalEmbedding.exists_domain`: every point has local embeddings into a
  *domain* (a ball) with image inside any prescribed open neighbourhood.
* `LocalEmbedding.exists_contMDiff_factor` and
  `LocalEmbedding.exists_differentiableOn_factor`: an arbitrary morphism from
  an embedded model to `X` is, near every point, induced by an ambient
  holomorphic map into the ambient space of any local embedding at the image
  point. For two local embeddings this gives the holomorphic transition maps.

Original source: Appendix B (`appendix_unibranch.tex`), §B.1 and
`def:unibranch:L105`. Blueprint: `claude-unibranch.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces
open Hironaka.HironakaActualAnalyticSubspace
open Hironaka.HironakaActualAnalyticSubspaceMaps
open Hironaka.HironakaActualAnalyticSubspaceOpenRestriction
open Hironaka.HironakaActualAnalyticSubspaceIntrinsicLifting
open Hironaka.HironakaReducedComplexAnalyticMorphismCharts

namespace Hironaka.Analytic.Unibranch

noncomputable section

/-! ### Holomorphic maps out of open submanifolds of coordinate space -/

/-- If every chart of a manifold `P` modelled on `ℂ^n` is given by the same
injective map `ι : P → ℂ^n` (as for nested open subsets of `ℂ^n`), then a
holomorphic map out of `P` extends along `ι` to a function on `ℂ^n` which is
complex smooth at every point of the image of `ι`. -/
theorem contDiffAt_extend_of_contMDiff {n m : ℕ} {P : Type*} [TopologicalSpace P]
    [ChartedSpace (ComplexModel n) P] [IsManifold 𝓘(ℂ, ComplexModel n) ∞ P]
    (ι : P → ComplexModel n) (hι : ∀ y y' : P, chartAt (ComplexModel n) y y' = ι y')
    (hinj : Function.Injective ι)
    {G : P → ComplexModel m} (hG : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ G)
    (y : P) : ContDiffAt ℂ ∞ (Function.extend ι G 0) (ι y) := by
  set e := chartAt (ComplexModel n) y with he
  have hy : y ∈ e.source := mem_chart_source (ComplexModel n) y
  have hey : e y = ι y := hι y y
  have hsymm : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm (e y) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)).contMDiffAt
      (e.open_target.mem_nhds (e.map_source hy))
  have hcomp : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ (G ∘ e.symm) (e y) := by
    have := hG (e.symm (e y))
    exact this.comp (e y) hsymm
  have hcd : ContDiffAt ℂ ∞ (G ∘ e.symm) (e y) := contMDiffAt_iff_contDiffAt.mp hcomp
  rw [← hey]
  refine hcd.congr_of_eventuallyEq ?_
  filter_upwards [e.open_target.mem_nhds (e.map_source hy)] with z hz
  have hz' : ι (e.symm z) = z := by rw [← hι y, e.right_inv hz]
  calc Function.extend ι G 0 z = Function.extend ι G 0 (ι (e.symm z)) := by rw [hz']
    _ = G (e.symm z) := hinj.extend_apply _ _ _

/-- Complex differentiability of the extension, see `contDiffAt_extend_of_contMDiff`. -/
theorem differentiableAt_extend_of_contMDiff {n m : ℕ} {P : Type*} [TopologicalSpace P]
    [ChartedSpace (ComplexModel n) P] [IsManifold 𝓘(ℂ, ComplexModel n) ∞ P]
    (ι : P → ComplexModel n) (hι : ∀ y y' : P, chartAt (ComplexModel n) y y' = ι y')
    (hinj : Function.Injective ι)
    {G : P → ComplexModel m} (hG : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ G)
    (y : P) : DifferentiableAt ℂ (Function.extend ι G 0) (ι y) :=
  (contDiffAt_extend_of_contMDiff ι hι hinj hG y).differentiableAt (by simp)

/-- Under the same hypothesis the image of `ι` is open: it is the union of the
chart targets. -/
theorem isOpen_range_of_chart_eq {n : ℕ} {P : Type*} [TopologicalSpace P]
    [ChartedSpace (ComplexModel n) P]
    (ι : P → ComplexModel n) (hι : ∀ y y' : P, chartAt (ComplexModel n) y y' = ι y') :
    IsOpen (range ι) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨y, rfl⟩
  set e := chartAt (ComplexModel n) y
  have hy : y ∈ e.source := mem_chart_source (ComplexModel n) y
  refine Filter.mem_of_superset (e.open_target.mem_nhds ?_) ?_
  · rw [← hι y y]
    exact e.map_source hy
  · intro z hz
    exact ⟨e.symm z, by rw [← hι y, e.right_inv hz]⟩

/-! ### Reassociating open subsets -/

/-- An open subset `T ≤ U` of coordinate space, viewed as an open subset of the
manifold `U`. -/
def opensWithin {n : ℕ} (U T : Opens (ComplexModel n)) : Opens U :=
  ⟨Subtype.val ⁻¹' (T : Set (ComplexModel n)), T.isOpen.preimage continuous_subtype_val⟩

/-- The tautological biholomorphism between an open `T ≤ U` of `ℂ^n` and the
same set viewed as an open subset of the manifold `U`. -/
def opensWithinDiffeo {n : ℕ} (U T : Opens (ComplexModel n)) (hT : T ≤ U) :
    T ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ opensWithin U T where
  toFun z := ⟨⟨z.val, hT z.2⟩, z.2⟩
  invFun w := ⟨w.val.val, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (opensWithin U T) _).mp
    exact contMDiff_inclusion hT
  contMDiff_invFun := by
    show ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun w : opensWithin U T => (⟨w.val.val, w.2⟩ : T))
    apply (ContMDiff.subtypeVal_comp_iff T _).mp
    have h : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (fun w : opensWithin U T => w.val.val) :=
      contMDiff_subtype_val.comp contMDiff_subtype_val
    exact h

/-! ### Local embeddings -/

/-- A local embedding of a complex space `X`: an embedded model `(Ω, C)` (an
open set `Ω ⊆ ℂ^N` and a closed analytic subset `C ⊆ Ω` with its reduced
structure) together with an open immersion of the model into `X` over the
complex point. -/
structure LocalEmbedding (X : SourceReducedComplexSpace) where
  /-- The dimension `N` of the ambient coordinate space. -/
  dim : ℕ
  /-- The ambient open set `Ω ⊆ ℂ^N`. -/
  ambient : Opens (ComplexModel dim)
  /-- The closed analytic subset `C ⊆ Ω` carrying the model. -/
  carrier : Set ambient
  analytic : IsComplexAnalyticSubset (n := dim) carrier
  /-- The open immersion of the model into `X`. -/
  map : (modelOver ambient carrier).left ⟶ X.obj.left
  isOpenImmersion : LocallyRingedSpace.IsOpenImmersion map
  overPoint : map ≫ X.obj.hom = (modelOver ambient carrier).hom

namespace LocalEmbedding

variable {X : SourceReducedComplexSpace}

/-- The underlying map of points `C → X` of a local embedding. -/
def toPoint (e : LocalEmbedding X) : e.carrier → X.obj.left := fun c => e.map.base c

theorem isOpenEmbedding_toPoint (e : LocalEmbedding X) : Topology.IsOpenEmbedding e.toPoint :=
  e.isOpenImmersion.base_open

theorem isOpen_range_toPoint (e : LocalEmbedding X) : IsOpen (range e.toPoint) :=
  e.isOpenEmbedding_toPoint.isOpen_range

theorem toPoint_injective (e : LocalEmbedding X) : Function.Injective e.toPoint :=
  e.isOpenEmbedding_toPoint.injective

/-- A local embedding through a prescribed point, from the defining local-model
property of `X`. -/
def ofPoint (X : SourceReducedComplexSpace) (x : X.obj.left) : LocalEmbedding X :=
  let h := X.property.2.2 x
  { dim := h.choose
    ambient := h.choose_spec.choose
    carrier := h.choose_spec.choose_spec.choose
    analytic := h.choose_spec.choose_spec.choose_spec.1
    map := h.choose_spec.choose_spec.choose_spec.2.choose
    isOpenImmersion := h.choose_spec.choose_spec.choose_spec.2.choose_spec.1
    overPoint := h.choose_spec.choose_spec.choose_spec.2.choose_spec.2.1 }

theorem mem_range_ofPoint (X : SourceReducedComplexSpace) (x : X.obj.left) :
    x ∈ range (ofPoint X x).toPoint :=
  (X.property.2.2 x).choose_spec.choose_spec.choose_spec.2.choose_spec.2.2

/-- The tautological local embedding of an embedded model. -/
abbrev model {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    LocalEmbedding (sourceReducedComplexSpaceModel U C hC) where
  dim := n
  ambient := U
  carrier := C
  analytic := hC
  map := 𝟙 _
  isOpenImmersion := inferInstance
  overPoint := Category.id_comp _

@[simp] theorem model_toPoint {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) (c : C) :
    (model U C hC).toPoint c = c := rfl

/-- The analytic subset of a smaller ambient open set `T ≤ Ω` cut out by `C`. -/
def restrictCarrier (e : LocalEmbedding X) (T : Opens (ComplexModel e.dim))
    (hT : T ≤ e.ambient) : Set T :=
  Opens.inclusion hT ⁻¹' e.carrier

theorem restrictCarrier_analytic (e : LocalEmbedding X) (T : Opens (ComplexModel e.dim))
    (hT : T ≤ e.ambient) :
    IsComplexAnalyticSubset (n := e.dim) (e.restrictCarrier T hT) :=
  Hironaka.AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (contMDiff_inclusion hT) e.analytic

/-- The model map induced by the inclusion `T ≤ Ω`, for any subset `C' ⊆ T` with
`C' = C ∩ T`, factored as an isomorphism of models followed by the open
restriction of the model `(Ω, C)`. -/
def restrictModelMapWith (e : LocalEmbedding X) (T : Opens (ComplexModel e.dim))
    (hT : T ≤ e.ambient) (C' : Set T) (hC' : ∀ z, z ∈ C' ↔ Opens.inclusion hT z ∈ e.carrier) :
    (modelOver T C').left ⟶ (modelOver e.ambient e.carrier).left :=
  (actualSubspaceBiholomorphicIso (opensWithinDiffeo e.ambient T hT)
      C' ((Subtype.val : opensWithin e.ambient T → e.ambient) ⁻¹' e.carrier)
      hC').hom ≫
    actualOpenSubspaceMap (n := e.dim) e.carrier (opensWithin e.ambient T)

instance restrictModelMapWith_isOpenImmersion (e : LocalEmbedding X)
    (T : Opens (ComplexModel e.dim)) (hT : T ≤ e.ambient) (C' : Set T)
    (hC' : ∀ z, z ∈ C' ↔ Opens.inclusion hT z ∈ e.carrier) :
    LocallyRingedSpace.IsOpenImmersion (e.restrictModelMapWith T hT C' hC') := by
  unfold restrictModelMapWith
  infer_instance

theorem restrictModelMapWith_over (e : LocalEmbedding X) (T : Opens (ComplexModel e.dim))
    (hT : T ≤ e.ambient) (C' : Set T) (hC' : ∀ z, z ∈ C' ↔ Opens.inclusion hT z ∈ e.carrier) :
    e.restrictModelMapWith T hT C' hC' ≫ (modelOver e.ambient e.carrier).hom =
      (modelOver T C').hom := by
  unfold restrictModelMapWith
  change _ ≫ subspacePointMap (n := e.dim) e.carrier = subspacePointMap (n := e.dim) _
  rw [Category.assoc, actualOpenSubspaceMap,
    actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)]
  exact actualSubspaceMap_point (opensWithinDiffeo e.ambient T hT).contMDiff _

/-- Restriction of a local embedding to a smaller ambient open set `T ≤ Ω`, with
carrier any set `C' ⊆ T` equal to `C ∩ T`. -/
def restrictWith (e : LocalEmbedding X) (T : Opens (ComplexModel e.dim)) (hT : T ≤ e.ambient)
    (C' : Set T) (hC' : ∀ z, z ∈ C' ↔ Opens.inclusion hT z ∈ e.carrier) :
    LocalEmbedding X where
  dim := e.dim
  ambient := T
  carrier := C'
  analytic := by
    have h : C' = e.restrictCarrier T hT := Set.ext hC'
    rw [h]
    exact e.restrictCarrier_analytic T hT
  map := e.restrictModelMapWith T hT C' hC' ≫ e.map
  isOpenImmersion := by
    let := e.isOpenImmersion
    infer_instance
  overPoint := by
    rw [Category.assoc, e.overPoint]
    exact e.restrictModelMapWith_over T hT C' hC'

theorem restrictWith_toPoint (e : LocalEmbedding X) (T : Opens (ComplexModel e.dim))
    (hT : T ≤ e.ambient) (C' : Set T) (hC' : ∀ z, z ∈ C' ↔ Opens.inclusion hT z ∈ e.carrier)
    (z : C') :
    (e.restrictWith T hT C' hC').toPoint z =
      e.toPoint ⟨Opens.inclusion hT z.val, (hC' z.val).mp z.property⟩ := rfl

/-- Restriction of a local embedding to a smaller ambient open set `T ≤ Ω`. -/
def restrict (e : LocalEmbedding X) (T : Opens (ComplexModel e.dim)) (hT : T ≤ e.ambient) :
    LocalEmbedding X :=
  e.restrictWith T hT (e.restrictCarrier T hT) (fun _ => Iff.rfl)

theorem restrict_toPoint (e : LocalEmbedding X) (T : Opens (ComplexModel e.dim))
    (hT : T ≤ e.ambient) (z : e.restrictCarrier T hT) :
    (e.restrict T hT).toPoint z = e.toPoint ⟨Opens.inclusion hT z.val, z.property⟩ := rfl

/-- Every point of a complex space lies in the image of a local embedding into a
domain (a ball of some `ℂ^N`), with image inside any prescribed open
neighbourhood. -/
theorem exists_domain (x : X.obj.left) {N : Set X.obj.left} (hN : IsOpen N) (hx : x ∈ N) :
    ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧ range e.toPoint ⊆ N ∧
      IsConnected (e.ambient : Set (ComplexModel e.dim)) := by
  set e₀ := ofPoint X x
  obtain ⟨c, hc⟩ := mem_range_ofPoint X x
  have hS : IsOpen (e₀.toPoint ⁻¹' N) := hN.preimage e₀.isOpenEmbedding_toPoint.continuous
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hS
  have hct : c.val ∈ t := by
    have : c ∈ e₀.toPoint ⁻¹' N := by
      change e₀.toPoint c ∈ N
      rw [hc]
      exact hx
    rw [← hts] at this
    exact this
  have hopen : IsOpen ((Subtype.val : e₀.ambient → ComplexModel e₀.dim) '' t) :=
    e₀.ambient.isOpen.isOpenMap_subtype_val t ht
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen c.val.val ⟨c.val, hct, rfl⟩
  let T : Opens (ComplexModel e₀.dim) := ⟨Metric.ball c.val.val r, Metric.isOpen_ball⟩
  have hT : T ≤ e₀.ambient := by
    intro z hz
    obtain ⟨u, -, rfl⟩ := hball hz
    exact u.property
  refine ⟨e₀.restrict T hT, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨c.val.val, Metric.mem_ball_self hr⟩, ?_⟩, ?_⟩
    · exact c.property
    · rw [restrict_toPoint]
      exact hc
  · rintro _ ⟨z, rfl⟩
    rw [restrict_toPoint]
    have hz : Opens.inclusion hT z.val ∈ t := by
      obtain ⟨u, hu, hu'⟩ := hball z.val.property
      have : u = Opens.inclusion hT z.val := Subtype.ext hu'
      rw [← this]
      exact hu
    have : (⟨Opens.inclusion hT z.val, z.property⟩ : e₀.carrier) ∈ e₀.toPoint ⁻¹' N := by
      rw [← hts]
      exact hz
    exact this
  · exact (convex_ball _ _).isConnected (Metric.nonempty_ball.mpr hr)

/-! ### Holomorphic factorization of morphisms through local embeddings -/

/-- An arbitrary morphism from an embedded model `(U, C)` to `X` over the complex
point is, near every point `c ∈ C`, induced by an ambient holomorphic map from an
open neighbourhood `O` of `c` in `U` into the ambient space of any local
embedding of `X` at the image of `c`. -/
theorem exists_contMDiff_factor {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (F : (modelOver U C).left ⟶ X.obj.left) (hF : F ≫ X.obj.hom = (modelOver U C).hom)
    (e : LocalEmbedding X) (c : C) (hc : F.base c ∈ range e.toPoint) :
    ∃ (O : Opens U), c.val ∈ O ∧ ∃ f : O → e.ambient,
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel e.dim) ∞ f ∧
      ∀ (y : C) (hy : y.val ∈ O), ∃ z : e.carrier,
        z.val = f ⟨y.val, hy⟩ ∧ e.toPoint z = F.base y := by
  let := e.isOpenImmersion
  obtain ⟨T, hcT, H, hHp, hHfac⟩ :=
    exists_actual_model_chart_factor (n := n) X.obj F hF e.map e.overPoint c hc
  let cT : ((Subtype.val : T → U) ⁻¹' C) := ⟨⟨c.val, hcT⟩, c.property⟩
  obtain ⟨O', hcO', f', hf', hCD', hfH⟩ :=
    exists_actualSubspaceMap_local_holomorphic_lift H hHp cT
  have hOopen : IsOpen ((Subtype.val : T → U) '' (O' : Set T)) :=
    T.isOpen.isOpenMap_subtype_val _ O'.isOpen
  let O : Opens U := ⟨(Subtype.val : T → U) '' (O' : Set T), hOopen⟩
  have memT : ∀ u : O, (u : U) ∈ T := by
    rintro ⟨u, t, -, rfl⟩
    exact t.property
  have memO' : ∀ u : O, (⟨u.val, memT u⟩ : T) ∈ O' := by
    rintro ⟨u, t, ht, rfl⟩
    exact ht
  let σ : O → O' := fun u => ⟨⟨u.val, memT u⟩, memO' u⟩
  have hσ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ σ := by
    apply (ContMDiff.subtypeVal_comp_iff O' σ).mp
    apply (ContMDiff.subtypeVal_comp_iff T _).mp
    exact contMDiff_subtype_val
  refine ⟨O, ⟨⟨c.val, hcT⟩, hcO', rfl⟩, f' ∘ σ, hf'.comp hσ, ?_⟩
  intro y hy
  let t : O' := σ ⟨y.val, hy⟩
  have hyt : t.val ∈ (Subtype.val : T → U) ⁻¹' C := y.property
  refine ⟨⟨f' t, hCD' t hyt⟩, rfl, ?_⟩
  have h1 := congrArg (fun k => k.base (⟨t, hyt⟩ : (Subtype.val : O' → T) ⁻¹'
    ((Subtype.val : T → U) ⁻¹' C))) hfH
  have h2 := congrArg (fun k => k.base (⟨t.val, hyt⟩ : (Subtype.val : T → U) ⁻¹' C)) hHfac
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at h1 h2
  change e.map.base ((actualSubspaceMap hf' hCD').base ⟨t, hyt⟩) = F.base y
  rw [h1]
  exact h2

/-- Coordinate form of `exists_contMDiff_factor`: the ambient holomorphic map is
a complex smooth (holomorphic) map `G : ℂ^n → ℂ^N` on an open neighbourhood `W ⊆ U` of
`c`, with values in the ambient open set of the local embedding. -/
theorem exists_contDiffOn_factor {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (F : (modelOver U C).left ⟶ X.obj.left) (hF : F ≫ X.obj.hom = (modelOver U C).hom)
    (e : LocalEmbedding X) (c : C) (hc : F.base c ∈ range e.toPoint) :
    ∃ W : Set (ComplexModel n), IsOpen W ∧ c.val.val ∈ W ∧ W ⊆ U ∧
      ∃ G : ComplexModel n → ComplexModel e.dim, ContDiffOn ℂ ∞ G W ∧
        MapsTo G W e.ambient ∧
        ∀ y : C, y.val.val ∈ W → ∃ z : e.carrier, z.val.val = G y.val.val ∧
          e.toPoint z = F.base y := by
  obtain ⟨O, hcO, f, hf, hfac⟩ := exists_contMDiff_factor F hF e c hc
  let ι : O → ComplexModel n := fun u => u.val.val
  have hι : ∀ y y' : O, chartAt (ComplexModel n) y y' = ι y' := fun _ _ => rfl
  have hinj : Function.Injective ι := fun a b h => Subtype.ext (Subtype.ext h)
  let g : O → ComplexModel e.dim := fun u => (f u).val
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel e.dim) ∞ g :=
    contMDiff_subtype_val.comp hf
  refine ⟨range ι, isOpen_range_of_chart_eq ι hι, ⟨⟨c.val, hcO⟩, rfl⟩, ?_,
    Function.extend ι g 0, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact u.val.property
  · rintro _ ⟨u, rfl⟩
    exact (contDiffAt_extend_of_contMDiff ι hι hinj hg u).contDiffWithinAt
  · rintro _ ⟨u, rfl⟩
    rw [hinj.extend_apply]
    exact (f u).property
  · rintro y ⟨u, hu⟩
    have huy : u.val = y.val := Subtype.ext hu
    have hy : y.val ∈ O := huy ▸ u.property
    obtain ⟨z, hz, hzF⟩ := hfac y hy
    refine ⟨z, ?_, hzF⟩
    have : ι ⟨y.val, hy⟩ = y.val.val := rfl
    rw [← this, hinj.extend_apply, hz]

/-- Complex differentiable form of `exists_contDiffOn_factor`. -/
theorem exists_differentiableOn_factor {n : ℕ} {U : Opens (ComplexModel n)} {C : Set U}
    (F : (modelOver U C).left ⟶ X.obj.left) (hF : F ≫ X.obj.hom = (modelOver U C).hom)
    (e : LocalEmbedding X) (c : C) (hc : F.base c ∈ range e.toPoint) :
    ∃ W : Set (ComplexModel n), IsOpen W ∧ c.val.val ∈ W ∧ W ⊆ U ∧
      ∃ G : ComplexModel n → ComplexModel e.dim, DifferentiableOn ℂ G W ∧
        MapsTo G W e.ambient ∧
        ∀ y : C, y.val.val ∈ W → ∃ z : e.carrier, z.val.val = G y.val.val ∧
          e.toPoint z = F.base y := by
  obtain ⟨W, hW, hcW, hWU, G, hG, hmaps, hfac⟩ := exists_contDiffOn_factor F hF e c hc
  exact ⟨W, hW, hcW, hWU, G, hG.differentiableOn (by simp), hmaps, hfac⟩

/-- Holomorphic transition maps between two local embeddings. -/
theorem exists_transition (e₁ e₂ : LocalEmbedding X) (c : e₁.carrier)
    (hc : e₁.toPoint c ∈ range e₂.toPoint) :
    ∃ W : Set (ComplexModel e₁.dim), IsOpen W ∧ c.val.val ∈ W ∧ W ⊆ e₁.ambient ∧
      ∃ G : ComplexModel e₁.dim → ComplexModel e₂.dim, DifferentiableOn ℂ G W ∧
        MapsTo G W e₂.ambient ∧
        ∀ y : e₁.carrier, y.val.val ∈ W → ∃ z : e₂.carrier, z.val.val = G y.val.val ∧
          e₂.toPoint z = e₁.toPoint y :=
  exists_differentiableOn_factor e₁.map e₁.overPoint e₂ c hc

/-- Holomorphic transition maps between two local embeddings, as complex smooth maps. -/
theorem exists_contDiff_transition (e₁ e₂ : LocalEmbedding X) (c : e₁.carrier)
    (hc : e₁.toPoint c ∈ range e₂.toPoint) :
    ∃ W : Set (ComplexModel e₁.dim), IsOpen W ∧ c.val.val ∈ W ∧ W ⊆ e₁.ambient ∧
      ∃ G : ComplexModel e₁.dim → ComplexModel e₂.dim, ContDiffOn ℂ ∞ G W ∧
        MapsTo G W e₂.ambient ∧
        ∀ y : e₁.carrier, y.val.val ∈ W → ∃ z : e₂.carrier, z.val.val = G y.val.val ∧
          e₂.toPoint z = e₁.toPoint y :=
  exists_contDiffOn_factor e₁.map e₁.overPoint e₂ c hc

end LocalEmbedding

end

end Hironaka.Analytic.Unibranch
