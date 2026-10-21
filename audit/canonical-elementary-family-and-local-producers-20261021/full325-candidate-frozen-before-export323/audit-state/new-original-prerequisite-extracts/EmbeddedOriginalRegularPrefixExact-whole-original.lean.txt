import TranscendentalNakamaye.Pending.SmoothCentreInvariant
import TranscendentalNakamaye.Pending.StrictTransformSubvarietySequence
import TranscendentalNakamaye.Pending.RegularLocusComponent
import TranscendentalNakamaye.Pending.RegularPointDimension
import TranscendentalNakamaye.Pending.RegularAtDimTransport
import TranscendentalNakamaye.Pending.AnalyticSubsetPreimage
import TranscendentalNakamaye.Pending.AnalyticSubsetOpens
import TranscendentalNakamaye.Pending.RestrictEmptyTower
import TranscendentalNakamaye.Pending.BlowupIsomorphismOff
import TranscendentalNakamaye.Pending.StrictTransformComposition
import TranscendentalNakamaye.Pending.ResolutionInvariantSegments
import TranscendentalNakamaye.Pending.InvDomainTowerAlong
import TranscendentalNakamaye.FirstPass.RegularPatchNeighborhood
import TranscendentalNakamaye.Pending.AnalyticIrreducibleComponents
import TranscendentalNakamaye.Pending.DerivativeIdeal
import TranscendentalNakamaye.Pending.HolomorphicGermAlgebra
import TranscendentalNakamaye.Pending.NormalCrossings

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution from the canonical resolution: the identity-principle step and the stopping

The rest of `hir:embedded-from-resolution` (`blueprint/src/hironaka.tex`, Hironaka phase H5b, TN-CLASSICAL's node), along
the direct route of finding F4 of the orchestrator's review; claim I-0981 C-0147.  Blueprint `mc:first-centre-smooth-part`,
`mc:first-centre-exists` (`blueprint/src/maximal-contact.tex`).  Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), the
embedded desingularization from the canonical resolution of `(X, X, ∅, 𝓘_V, 1)`; Bierstone--Milman 2008
(`bierstone-milman08-functoriality`).

Let `V` be a closed irreducible analytic subvariety of a compact complex manifold `X`, `U = X ∖ V_sing` (`regularOpen V`)
and `𝔪_V = (X, X, ∅, 𝓘_V, 1)`.  Along a canonical segment `T` of a value function with properties (1), (4), (5), (6) of a
resolution invariant whose centres miss the preimages of `U`, the first centre `C` meeting the preimage of `U` contains the
whole cosupport over `U`, which is the preimage of `V_reg` (`EmbeddingFields.inv_eq_over_open_of_isEmptyTower_of_pureDim`,
the generic form of `SmoothCentreInvariant.inv_eq_over_open_of_isEmptyTower_of_pureDim`).  The **identity principle** then shows that
the strict transform of `V` at that stage is the connected component of `C` through any point over `U`: a smooth closed
connected submanifold of dimension `dim V`; and the exceptional image of the segment lies in `V_sing`.  Stopping before
the blowup of `C` gives the embedded resolution.  Such a first centre exists along every canonical segment with empty
final cosupport, because `V_reg ≠ ∅` stays in the cosupport as long as the centres miss `U`.

## Main results

* over an open set the centres miss (`RestrictEmptyTower.CentresAvoid`): `notMem_exceptionalLocus_of_centresAvoid`,
  `image_exceptionalLocus_subset_compl` (no exceptional point over `U`), `strictTransform_subset_preimage`,
  `mem_strictTransform_iff_of_centresAvoid` (over `U` the strict transform of a closed set is its preimage);
* `regularOpen`, `isClosed_singularLocus`, `regularAtDim_of_mem_regularOpen`: `U = X ∖ V_sing` and `V ∩ U = V_reg`;
* **`strictTransform_eq_connectedComponentIn`** (the identity-principle step, no invariant involved): if the centres of `T`
  miss `U` and a closed submanifold `C` of the last stage agrees with the preimage of `V` over `U` and meets it, then the
  strict transform of `V` is the connected component of `C` through such a point, regular of dimension `dim V` at each
  of its points, and the exceptional image lies in `V_sing`;
* `EmbeddingFields n k inv`: the four properties used -- (1), (4), (5), (6) of a resolution invariant, in the shape of the
  fields of `ResolutionInvariantExt.ResolutionInvariant` -- for any value function `inv`
  (`embeddingFields_of_resolutionInvariant`); everything below is generic in `inv` (TN-CLASSICAL, I-0981 C-0148), and
  `EmbeddingFields.isGeoTestTower_of_isCanonical`, `.inv_eq_over_open_of_isEmptyTower_of_pureDim`, ... restate the
  smooth-centre lemmas of `SmoothCentreInvariant` (proved there for `ResolutionInvariantExt.ResolutionInvariant`) for it;
* `mem_cosupp_iff_of_centresAvoid`, **`mem_maxLocus_iff_of_centresAvoid`**: over `U` the cosupport of `𝔪_V` along `T` is
  the preimage of `V`, and so is the maximum locus once it meets the preimage of `U`;
* **`strictTransform_eq_connectedComponentIn_maxLocus`**: the identity-principle step for the first centre of a canonical
  segment meeting `U`;
* **`exists_first_centre`** (the stopping, any value function): a canonical segment whose centres do not all miss `U` has
  a canonical prefix whose centres miss `U` and whose maximum locus meets the preimage of `U`;
  `not_centresAvoid_of_cosupp_eq_empty`: a canonical segment with empty final cosupport has a centre meeting `U`;
* **`exists_embedded_of_isCanonical`**, **`exists_embeddedResolution_data_of_isCanonical`**: given a canonical segment of
  `𝔪_V` with empty final cosupport, its prefix before the first centre meeting `U` is a finite sequence of blowups with
  smooth centres whose exceptional image lies in `V_sing` and whose strict transform of `V` is regular of dimension `dim V` at
  each of its points -- the conclusion of `EmbeddedResolution.exists_embeddedResolution_smoothData`, with the field of
  `EmbeddedResolutionSmoothData` written out (that file is not imported); property (8) is not used;
  `exists_embeddedResolution_data_of_resolutionInvariant`: the same from a resolution invariant of the present structure
  (its driver uses (8)).

* the domain hypothesis away from Cartan's theorem (claim I-0981 C-0149): `interior_eq_empty_of_dim_lt` (a subvariety of
  dimension `< n` has empty interior), `isNonzeroAlongAt_vanishingIdeal_of_dim_lt` (its ideal is nonzero at every point),
  **`isInvDomain_vanishingIdeal_of_dim_lt`** (`(X, X, ∅, 𝓘_V, 1)` lies in the domain in dimension `≤ k ≥ n` once `𝓘_V` is
  coherent); the case `dim V = n`: `isClosedConnectedSubmanifold_of_dim_eq` (`V` is a connected component of `X`),
  `exists_embeddedResolution_data_of_dim_eq` (the identity is an embedded resolution);
* **`exists_embeddedResolution_data_of_resolutionInvariant_of_isCoherent`**: the conclusion of
  `EmbeddedResolution.exists_embeddedResolution_smoothData` from a resolution invariant of the present structure in dimension
  `≤ k`, `n ≤ k`, and the coherence of `𝓘_V`.

Not here: a resolution invariant itself (H4) and the coherence of `𝓘_V` for a singular `V` (Cartan's theorem); both are
hypotheses of the last theorem.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution` (the closedness of `V_sing` is re-proved here for that
reason; `StokesSingularLocusAnalytic` imports `RelativePrincipalization`).  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace TranscendentalNakamaye.Pending.EmbeddedFromResolution

open FirstPass FirstPass.NonKahlerLocus FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowerTransforms RestrictEmptyTower
  RegularLocusComponent
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionInvariantExt (IsEmptyTower)

noncomputable section

variable {n : ℕ}

/-! ### Towers whose centres miss an open set -/

section Avoid

variable {X : CMfd.{u} n}

/-- **No exceptional point over an open set the centres miss**: if every centre of `T` misses the preimage of `U`, the
composite `T.proj` has bijective differential at every point over `U` (`Exc(f ∘ π) = Exc π ∪ π⁻¹ Exc f`, and the
exceptional locus of a blowup lies over its centre). -/
theorem notMem_exceptionalLocus_of_centresAvoid (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresAvoid U T → ∀ y : Y, T.proj y ∈ U →
      y ∉ exceptionalLocus n T.proj
  | _, .refl, _, y, _ => by
      show y ∉ exceptionalLocus n (id : X → X)
      rw [exceptionalLocus_id]
      exact notMem_empty y
  | _, .step T C π hπ, h, y, hy => by
      obtain ⟨hT, hC⟩ : CentresAvoid U T ∧ Disjoint C (T.proj ⁻¹' (U : Set X)) := h
      show y ∉ exceptionalLocus n (T.proj ∘ π)
      rw [exceptionalLocus_comp (T.contMDiff_proj.mdifferentiable (by simp))
        (hπ.contMDiff.mdifferentiable (by simp))]
      rintro (h1 | h2)
      · exact Set.disjoint_left.mp hC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h1) hy
      · exact notMem_exceptionalLocus_of_centresAvoid U T hT (π y) hy h2

/-- **The exceptional image lies off an open set the centres miss.** -/
theorem image_exceptionalLocus_subset_compl (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (h : CentresAvoid U T) : T.proj '' exceptionalLocus n T.proj ⊆ (U : Set X)ᶜ := by
  rintro _ ⟨y, hy, rfl⟩ hyU
  exact notMem_exceptionalLocus_of_centresAvoid U T h y hyU hy

/-- The strict transform of a closed set lies in its preimage. -/
theorem strictTransform_subset_preimage {A : Set X} (hA : IsClosed A) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    strictTransform n T.proj A ⊆ T.proj ⁻¹' A :=
  closure_minimal sdiff_subset (hA.preimage T.contMDiff_proj.continuous)

/-- **Over an open set the centres miss, the strict transform of a closed set is its preimage.** -/
theorem mem_strictTransform_iff_of_centresAvoid (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (h : CentresAvoid U T) {A : Set X} (hA : IsClosed A) {y : Y} (hy : T.proj y ∈ U) :
    y ∈ strictTransform n T.proj A ↔ T.proj y ∈ A :=
  ⟨fun h' => strictTransform_subset_preimage hA T h',
    fun h' => subset_closure ⟨h', notMem_exceptionalLocus_of_centresAvoid U T h y hy⟩⟩

end Avoid

/-! ### The complement of the singular locus -/

section Regular

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The singular locus is closed** (regularity of a fixed dimension is relatively open).  The same statement as
`StokesSingularLocusAnalytic.isClosed_singularLocus`, re-proved for `NonKahlerLocus.singularLocus` so that this module
stays outside the import closure of `Pending.RelativePrincipalization`. -/
theorem isClosed_singularLocus (V : ClosedIrreducibleAnalyticSubvariety n M) : IsClosed (singularLocus V) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  by_cases hyV : y ∈ V.carrier
  · have hreg : RegularAtDim (n := n) V.carrier y V.dim := by
      by_contra h
      exact hy ⟨hyV, h⟩
    filter_upwards [RegularPatchNeighborhood.eventually_regularAtDim hreg] with z hz hzS
    exact hzS.2 (hz hzS.1)
  · filter_upwards [V.isClosed_carrier.isOpen_compl.mem_nhds hyV] with z hz hzS
    exact hz hzS.1

/-- **`U = X ∖ V_sing`**, the open set over which `V` is the closed submanifold `V_reg`. -/
def regularOpen (V : ClosedIrreducibleAnalyticSubvariety n M) : Opens M :=
  ⟨(singularLocus V)ᶜ, (isClosed_singularLocus V).isOpen_compl⟩

theorem mem_regularOpen_iff {V : ClosedIrreducibleAnalyticSubvariety n M} {x : M} :
    x ∈ regularOpen V ↔ x ∉ singularLocus V :=
  Iff.rfl

/-- **`V ∩ U = V_reg`**: a point of `V` off the singular locus is a regular point of dimension `dim V`. -/
theorem regularAtDim_of_mem_regularOpen {V : ClosedIrreducibleAnalyticSubvariety n M} {x : M} (hxV : x ∈ V.carrier)
    (hxU : x ∈ regularOpen V) : RegularAtDim (n := n) V.carrier x V.dim := by
  by_contra h
  exact hxU ⟨hxV, h⟩

/-- A regular point of dimension `dim V` lies in `U`. -/
theorem mem_regularOpen_of_regularAtDim {V : ClosedIrreducibleAnalyticSubvariety n M} {x : M}
    (hx : RegularAtDim (n := n) V.carrier x V.dim) : x ∈ regularOpen V :=
  fun h => h.2 hx

end Regular

/-! ### The identity-principle step -/

section Identity

variable {X : CMfd.{u} n}

/-- **The identity-principle step of `hir:embedded-from-resolution`** (no invariant involved).  Let `V` be a closed
irreducible analytic subvariety of the compact `X`, `T` a tower whose centres miss the preimages of `U = X ∖ V_sing`, and
`C` a closed submanifold of the last stage which over `U` is the preimage of `V`, with a point `c` over `U`.  Then the strict
transform of `V` is the connected component of `C` through `c`, it is regular of dimension `dim V` at each of its points,
and the exceptional image of `T` lies in `V_sing`.

Proof: over `U` the projection has no exceptional point, so the strict transform `S` is the preimage of `V` there and is
regular of dimension `dim V` at `c` (`RegularAtDimTransport.regularAtDim_of_preimage`); so is `C`.  `S` is irreducible
(`StrictTransformSubvarietySequence`), hence the closure of the component of its regular locus through `c`
(`StrictTransformSubvariety.eq_closure_component`).  The identity theorem along a component
(`RegularLocusComponent.component_subset_of_isOpen`), applied to `S ⊆ C` and `C ⊆ S` near `c`, puts each of the two
components through `c` into the other set; the component of `S` lies in the connected component `K` of `C` through `c`,
and every point of the closure of the former lies in `K` (near it `C` lies in its own component, which meets `K`). -/
theorem strictTransform_eq_connectedComponentIn [CompactSpace X] (V : ClosedIrreducibleAnalyticSubvariety n X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : CentresAvoid (regularOpen V) T) {C : Set Y}
    (hC : IsClosedSubmanifold n C) (hCV : ∀ y : Y, T.proj y ∈ regularOpen V → (y ∈ C ↔ T.proj y ∈ V.carrier))
    {c : Y} (hc : c ∈ C) (hcU : T.proj c ∈ regularOpen V) :
    T.proj '' exceptionalLocus n T.proj ⊆ singularLocus V ∧
      strictTransform n T.proj V.carrier = connectedComponentIn C c ∧
      ∀ x ∈ strictTransform n T.proj V.carrier,
        RegularAtDim (n := n) (strictTransform n T.proj V.carrier) x V.dim := by
  set S := strictTransform n T.proj V.carrier with hSdef
  set O : Set Y := T.proj ⁻¹' (regularOpen V : Set X) with hOdef
  have hO : IsOpen O := (regularOpen V).isOpen.preimage T.contMDiff_proj.continuous
  have hcO : c ∈ O := hcU
  -- the exceptional image
  have hExc : T.proj '' exceptionalLocus n T.proj ⊆ singularLocus V := by
    intro x hx
    by_contra hxs
    exact image_exceptionalLocus_subset_compl (regularOpen V) T hT hx hxs
  -- over `U`, `S` and `C` are the preimage of `V`
  have hSO : ∀ y ∈ O, y ∈ S ↔ T.proj y ∈ V.carrier := fun y hy =>
    mem_strictTransform_iff_of_centresAvoid (regularOpen V) T hT V.isClosed_carrier hy
  have hCS : ∀ y ∈ O, y ∈ C ↔ y ∈ S := fun y hy => (hCV y hy).trans (hSO y hy).symm
  have hSOC : S ∩ O = C ∩ O := by
    ext y
    exact ⟨fun h => ⟨(hCS y h.2).mpr h.1, h.2⟩, fun h => ⟨(hCS y h.2).mp h.1, h.2⟩⟩
  -- regularity at `c`
  have hfcV : T.proj c ∈ V.carrier := (hCV c hcU).mp hc
  have hSc : RegularAtDim (n := n) S c V.dim :=
    RegularAtDimTransport.regularAtDim_of_preimage T.contMDiff_proj
      (notMem_exceptionalLocus_of_centresAvoid (regularOpen V) T hT c hcU) hO hcO hSO
      (regularAtDim_of_mem_regularOpen hfcV hcU)
  have hCc : RegularAtDim (n := n) C c V.dim :=
    RegularPointDimension.regularAtDim_of_inter_eq hO hcO hSOC hSc
  -- `S` is irreducible and analytic, `C` analytic
  obtain ⟨Vt, hVt, -⟩ := StrictTransformSubvarietySequence.exists_strictTransform_subvariety_of_isBlowupSequence
    T.isBlowupSequence V
    (StrictTransformSubvarietySequence.not_subset_image_exceptionalLocus_of_image_exceptionalLocus_subset_singular
      V hExc)
  have hSirr : IsComplexAnalyticallyIrreducible (n := n) S := by rw [hSdef, ← hVt]; exact Vt.irreducible_carrier
  have hCan : IsComplexAnalyticSubset (n := n) C := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC
  -- the regular points of `C` are `C`
  have hRC : regularPoints (n := n) C = C :=
    Subset.antisymm (regularPoints_subset C) fun y hy => hC.2 y hy
  have hKC : component (n := n) C c = connectedComponentIn C c := by
    show connectedComponentIn (regularPoints (n := n) C) c = _
    rw [hRC]
  -- identity theorem, twice
  have hSK : component (n := n) S c ⊆ C :=
    component_subset_of_isOpen hCan hO ⟨c, hcO, mem_component_self hSc⟩ fun y hy =>
      (hCS y hy.1).mpr (component_subset S c hy.2)
  have hKS : component (n := n) C c ⊆ S :=
    component_subset_of_isOpen hSirr.analytic hO ⟨c, hcO, mem_component_self hCc⟩ fun y hy =>
      (hCS y hy.1).mp (component_subset C c hy.2)
  have hSKC : component (n := n) S c ⊆ component (n := n) C c :=
    subset_component_of_isPreconnected isPreconnected_connectedComponentIn
      (fun y hy => hRC.symm ▸ hSK hy) ⟨c, mem_component_self hSc, mem_component_self hCc⟩
  have hSeq : S = closure (component (n := n) S c) := StrictTransformSubvariety.eq_closure_component hSirr hSc
  have hSC : S ⊆ C := by
    rw [hSeq]
    exact closure_minimal hSK hC.1
  -- `S` is the component of `C` through `c`
  have hSeqK : S = component (n := n) C c := by
    refine Subset.antisymm (fun x hx => ?_) hKS
    obtain ⟨j, hj⟩ := hC.2 x (hSC hx)
    obtain ⟨W, hW, hxW, hWC⟩ := exists_open_inter_subset_component hj (mem_component_self hj)
    rw [hSeq] at hx
    obtain ⟨z, hzW, hzS⟩ := mem_closure_iff.mp hx W hW hxW
    have hzx : z ∈ component (n := n) C x := hWC ⟨hSK hzS, hzW⟩
    have hzc : z ∈ component (n := n) C c := hSKC hzS
    have h1 : component (n := n) C x = component (n := n) C c :=
      (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzc).symm
    exact h1 ▸ mem_component_self hj
  refine ⟨hExc, hSeqK.trans hKC, fun x hx => ?_⟩
  have hxK : x ∈ component (n := n) C c := hSeqK ▸ hx
  have hCx : RegularAtDim (n := n) C x V.dim := regularAtDim_of_mem_component hCc hxK
  obtain ⟨W, hW, hxW, hWC⟩ := exists_open_inter_subset_component hCc hxK
  refine RegularPointDimension.regularAtDim_of_inter_eq hW hxW ?_ hCx
  ext y
  exact ⟨fun h => ⟨hSeqK ▸ hWC h, h.2⟩, fun h => ⟨hSC h.1, h.2⟩⟩

end Identity

/-! ### The four properties used: (1), (4), (5), (6) -/

section Fields

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

variable (n k) in
/-- **The properties of a resolution invariant that the embedded-resolution argument uses** -- (1) admissibility of the
level sets of the maximum, (4) empty steps, (5) restriction to open sets and (6) isomorphisms of towers -- for a value
function `inv`, in the exact shape of the fields of `ResolutionInvariantExt.ResolutionInvariant`.  The statements below are
generic in `inv` (TN-CLASSICAL's request, I-0981 C-0148), so they serve whichever form the structure takes after I-1139;
`embeddingFields_of_resolutionInvariant` supplies them for the present structure. -/
structure EmbeddingFields (inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    Prop where
  /-- (1) Admissibility of the level sets of the maximum, on open sets. -/
  admissible : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
    ∀ (W : Opens Y) (l : Λ), (∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∈ W → inv 𝔪 T y ≤ l) →
      (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong 𝔪 T)).IsAdmissibleCentre
        ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ inv 𝔪 T y = l})
  /-- (4) Empty steps, after a canonical segment. -/
  emptyStep : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π), C = ∅ →
      IsCanonical 𝔪 (inv 𝔪) T → ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
        inv 𝔪 (.step T C π hπ) z = inv 𝔪 T (π z)
  /-- (5) Restriction to open sets, along canonical segments. -/
  restrictOpen : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ (U : Opens X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
    ∀ p : openPreimage T U, (p : Y) ∈ (geoTransformAlong 𝔪 T).cosupp →
      inv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = inv 𝔪 T p
  /-- (6) Isomorphisms of towers over biholomorphisms, along canonical segments. -/
  towerIso : ∀ {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y')
    (T : BlowupTower X Y) (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y),
      BlowupTowerIsomorphism.IsTowerIso Φ T' T χ → IsCanonical 𝔪 (inv 𝔪) T →
        ∀ p : Y', χ p ∈ (geoTransformAlong 𝔪 T).cosupp → inv (MarkedIdeal.pullback Φ 𝔪) T' p = inv 𝔪 T (χ p)

/-- A resolution invariant (`ResolutionInvariantExt.ResolutionInvariant`) has the four properties. -/
theorem embeddingFields_of_resolutionInvariant (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) :
    EmbeddingFields n k R.inv :=
  ⟨R.admissible, R.emptyStep, R.restrictOpen, R.towerIso⟩

namespace EmbeddingFields

variable {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The maximum locus is an admissible centre** along a canonical segment which is a multiple test blow-up (property (1)
on the whole last stage; `ResolutionInvariantExt.isAdmissibleCentre_maxLocus` for `inv` with the four properties). -/
theorem isAdmissibleCentre_maxLocus (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔪 (inv 𝔪) T)
    (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong 𝔪 T).IsAdmissibleCentre
      (ResolutionDriver.maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := by
  by_cases hne : (ResolutionDriver.maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hadm := hF.admissible 𝔪 h T hcan ⊤ (inv 𝔪 T y₀) (fun y hy _ => hy₀.2 y hy)
    rw [← ResolutionInvariantDriver.maxLocus_eq_level hy₀] at hadm
    have hcoh := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT).isCoherent
    exact ResolutionInvariantDriver.isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg) hadm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Canonical segments are multiple test blow-ups** (`ResolutionInvariantExt.isGeoTestTower_of_isCanonical` for `inv`). -/
theorem isGeoTestTower_of_isCanonical (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T → IsGeoTestTower 𝔪 T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (inv 𝔪) T ∧
          (C = ∅ ∨ C = ResolutionDriver.maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      have hTt := isGeoTestTower_of_isCanonical hF h T hT
      refine (isGeoTestTower_step_iff 𝔪 T C π hπ).mpr ⟨hTt, ?_⟩
      rcases hC with rfl | rfl
      · exact MarkedIdeal.isAdmissibleCentre_empty _
      · exact isAdmissibleCentre_maxLocus hF h T hT hTt

/-- **Along a segment with only empty centres the value is that of the empty tower** (property (4), one step at a time;
`SmoothCentreInvariant.inv_eq_inv_refl_of_isEmptyTower` for `inv`). -/
theorem inv_eq_inv_refl_of_isEmptyTower (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)
    (h : IsInvDomain k 𝔪) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T → ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp,
      T.proj y ∈ 𝔪.cosupp ∧ inv 𝔪 T y = inv 𝔪 (BlowupTower.refl : BlowupTower X X) (T.proj y)
  | _, .refl, _, y, hy => ⟨hy, rfl⟩
  | _, .step T C π hπ, hT, y, hy => by
      have hT' := hT
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := hT
      have hiff := SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower 𝔪
        h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent (.step T C π hπ) hT' y
      have hπy : π y ∈ (geoTransformAlong 𝔪 T).cosupp :=
        (SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower 𝔪 h.isWellFormed.isClosedSubmanifold_N
          h.isWellFormed.isCoherent T hT (π y)).mpr (hiff.mp hy)
      have hstep := hF.emptyStep 𝔪 h T C π hπ hC (ResolutionInvariantExt.isCanonical_of_isEmptyTower 𝔪 (inv 𝔪) T hT)
        y hy
      obtain ⟨hmem, heq⟩ := inv_eq_inv_refl_of_isEmptyTower hF 𝔪 h T hT (π y) hπy
      exact ⟨hmem, hstep.trans heq⟩

/-- **Two points of a smooth centre of the same local dimension have the same value along the empty tower** (properties
(5) and (6) through the biholomorphism of `SmoothCentreHomogeneity.exists_smoothCentre_iso`;
`SmoothCentreInvariant.inv_refl_eq_of_regularAtDim` for `inv`). -/
theorem inv_refl_eq_of_regularAtDim (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {Z : Set X}
    (hZ : IsClosedSubmanifold n Z) (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X))
    {x x' : X} {j : ℕ} (hxj : RegularAtDim (n := n) Z x j) (hx'j : RegularAtDim (n := n) Z x' j) :
    inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x' =
      inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) (BlowupTower.refl : BlowupTower X X) x := by
  set 𝔪 : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ with h𝔪
  have hcos : 𝔪.cosupp = Z := SmoothCentreLocus.cosupp_vanishingIdeal hZ.1 (subset_univ Z)
  have hx : x ∈ Z := hxj.2.1
  have hx' : x' ∈ Z := hx'j.2.1
  obtain ⟨U₁, U₂, Φ, hxU, hx'U, hΦx, -, hpb⟩ := SmoothCentreHomogeneity.exists_smoothCentre_iso hxj hx'j 1
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hdom.isWellFormed.isCoherent
  have h1 := hF.restrictOpen 𝔪 hdom U₁ BlowupTower.refl trivial ⟨x, hxU⟩
    (by show x ∈ 𝔪.cosupp; rw [hcos]; exact hx)
  have h2 := hF.restrictOpen 𝔪 hdom U₂ BlowupTower.refl trivial ⟨x', hx'U⟩
    (by show x' ∈ 𝔪.cosupp; rw [hcos]; exact hx')
  have hdom₂ := InvDomainTowerAlong.isInvDomain_pullback_val U₂ hdom
  have hc₂ : Φ ⟨x, hxU⟩ ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪)
      (BlowupTower.refl : BlowupTower (CMfd.of (n := n) U₂) (CMfd.of (n := n) U₂))).cosupp := by
    show Φ ⟨x, hxU⟩ ∈ (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪).cosupp
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val 𝔪 hhol U₂, hcos]
    show ((Φ ⟨x, hxU⟩ : U₂) : X) ∈ Z
    rw [hΦx]
    exact hx'
  have h3 := hF.towerIso Φ (MarkedIdeal.pullback (Subtype.val : U₂ → X) 𝔪) hdom₂ BlowupTower.refl BlowupTower.refl
    Φ BlowupTowerIsomorphism.IsTowerIso.refl trivial ⟨x, hxU⟩ hc₂
  rw [hpb] at h3
  have hΦx' : Φ ⟨x, hxU⟩ = ⟨x', hx'U⟩ := Subtype.ext hΦx
  rw [hΦx'] at h3
  exact h2.symm.trans (h3.symm.trans h1)

/-- **Along a segment with only empty centres the value is constant on the cosupport of a smooth centre of pure
dimension** (`SmoothCentreInvariant.inv_eq_of_isEmptyTower_of_pureDim` for `inv`). -/
theorem inv_eq_of_isEmptyTower_of_pureDim (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {Z : Set X}
    (hZ : IsClosedSubmanifold n Z) {j : ℕ} (hpure : ∀ x ∈ Z, RegularAtDim (n := n) Z x j)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsEmptyTower T) {y y' : Y}
    (hy : y ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hy' : y' ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T).cosupp) :
    inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T y' =
      inv (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X) T y := by
  have hcos : (⟨univ, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n X).cosupp = Z :=
    SmoothCentreLocus.cosupp_vanishingIdeal hZ.1 (subset_univ Z)
  obtain ⟨hm, he⟩ := inv_eq_inv_refl_of_isEmptyTower hF _ hdom T hT y hy
  obtain ⟨hm', he'⟩ := inv_eq_inv_refl_of_isEmptyTower hF _ hdom T hT y' hy'
  rw [hcos] at hm hm'
  rw [he, he']
  exact inv_refl_eq_of_regularAtDim hF hZ hdom (hpure _ hm) (hpure _ hm')

/-- **Over an open set on which the segment has only empty centres, the value on `(X, X, ∅, 𝓘_V, 1)` is constant on the
cosupport**, when `V ∩ U` is a closed submanifold of `U` of pure dimension (the middle step of
`hir:embedded-from-resolution`; `SmoothCentreInvariant.inv_eq_over_open_of_isEmptyTower_of_pureDim` for `inv`). -/
theorem inv_eq_over_open_of_isEmptyTower_of_pureDim (hF : EmbeddingFields n k inv) {X : CMfd.{u} n} {V : Set X}
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X))
    (U : Opens X) (hZ : IsClosedSubmanifold n ((Subtype.val : U → X) ⁻¹' V)) {j : ℕ}
    (hpure : ∀ x ∈ (Subtype.val : U → X) ⁻¹' V, RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' V) x j)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)
      (inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) T)
    (hT : IsEmptyTower (restrict U T)) {p p' : openPreimage T U}
    (hp : (p : Y) ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hp' : (p' : Y) ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp) :
    inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T p' =
      inv (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T p := by
  have h1 := hF.restrictOpen _ hdom U T hcan p hp
  have h2 := hF.restrictOpen _ hdom U T hcan p' hp'
  have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have hTt := isGeoTestTower_of_isCanonical hF hdom T hcan
  have hc := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent U T hTt
  have hq : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]; exact hp
  have hq' : p' ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
      (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]; exact hp'
  rw [SmoothCentreInvariant.pullback_val_smoothCentreMarked U V] at h1 h2 hdomU hq hq'
  rw [← h1, ← h2]
  exact inv_eq_of_isEmptyTower_of_pureDim hF hZ hpure hdomU (restrict U T) hT hq hq'

end EmbeddingFields

end Fields

/-! ### The first centre meeting the smooth part -/

section Invariant

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] {X : CMfd.{u} n}
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Over an open set the centres miss, the cosupport of `(X, X, ∅, 𝓘_V, 1)` is the preimage of `V`** (`V` closed, the
marked ideal in the domain, `T` a multiple test blow-up): restrict to `U`
(`ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict`), where the tower has only empty centres
(`RestrictEmptyTower.isEmptyTower_restrict_iff`) and the cosupport is the preimage of `V ∩ U`
(`SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower`). -/
theorem mem_cosupp_iff_of_centresAvoid {V : Set X} (hV : IsClosed V)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (U : Opens X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hTt : IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T) (hT : CentresAvoid U T)
    {y : Y} (hy : T.proj y ∈ U) :
    y ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp ↔ T.proj y ∈ V := by
  have hc := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent U T hTt
  have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  have he : IsEmptyTower (restrict U T) := (isEmptyTower_restrict_iff U T).mpr hT
  set p : openPreimage T U := ⟨y, hy⟩ with hp
  have h1 : y ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X) T).cosupp ↔
      p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X)
        (⟨univ, [], vanishingIdeal (n := n) V, 1⟩ : MarkedIdeal n X)) (restrict U T)).cosupp := by
    rw [hc]
    rfl
  rw [h1, SmoothCentreInvariant.mem_cosupp_geoTransformAlong_of_isEmptyTower _
    hdomU.isWellFormed.isClosedSubmanifold_N hdomU.isWellFormed.isCoherent (restrict U T) he p,
    SmoothCentreInvariant.pullback_val_smoothCentreMarked U V,
    SmoothCentreLocus.cosupp_vanishingIdeal (hV.preimage continuous_subtype_val) (subset_univ _)]
  show (((restrict U T).proj p : U) : X) ∈ V ↔ _
  rw [proj_restrict]

/-- **The maximum locus over `U`**: for a canonical segment `T` of `(X, X, ∅, 𝓘_V, 1)` whose centres miss the preimages of
`U = X ∖ V_sing`, once the maximum locus meets the preimage of `U` it contains, over `U`, exactly the preimage of `V`
(`EmbeddingFields.inv_eq_over_open_of_isEmptyTower_of_pureDim`: `V ∩ U = V_reg` is a closed submanifold of `U` of pure
dimension `dim V`). -/
theorem mem_maxLocus_iff_of_centresAvoid (hF : EmbeddingFields n k inv) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)
      (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) T)
    (hT : CentresAvoid (regularOpen V) T) {c : Y}
    (hc : c ∈ ResolutionDriver.maxLocus (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T)
      (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hcU : T.proj c ∈ regularOpen V) {y : Y} (hy : T.proj y ∈ regularOpen V) :
    y ∈ ResolutionDriver.maxLocus (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp ↔
      T.proj y ∈ V.carrier := by
  have hTt := hF.isGeoTestTower_of_isCanonical hdom T hcan
  have hcos := mem_cosupp_iff_of_centresAvoid V.isClosed_carrier hdom (regularOpen V) T hTt hT hy
  refine ⟨fun h => hcos.mp h.1, fun h => ?_⟩
  have hys := hcos.mpr h
  have hpure : ∀ x ∈ (Subtype.val : regularOpen V → X) ⁻¹' V.carrier,
      RegularAtDim (n := n) ((Subtype.val : regularOpen V → X) ⁻¹' V.carrier) x V.dim := fun x hx =>
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (regularAtDim_of_mem_regularOpen hx x.2)
  have hZ : IsClosedSubmanifold n ((Subtype.val : regularOpen V → X) ⁻¹' V.carrier) :=
    ⟨V.isClosed_carrier.preimage continuous_subtype_val, fun x hx => ⟨V.dim, hpure x hx⟩⟩
  have heq := hF.inv_eq_over_open_of_isEmptyTower_of_pureDim hdom (regularOpen V) hZ hpure T hcan
    ((isEmptyTower_restrict_iff (regularOpen V) T).mpr hT) (p := ⟨c, hcU⟩) (p' := ⟨y, hy⟩) hc.1 hys
  refine ⟨hys, fun y' hy' => ?_⟩
  rw [show inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T y =
      inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T c from heq]
  exact hc.2 y' hy'

/-- **The identity-principle step for the first centre meeting the smooth part** (`hir:embedded-from-resolution`): for a
value function `inv` with the four properties and `(X, X, ∅, 𝓘_V, 1)` in its domain, and a canonical segment `T` whose
centres miss the preimages of `U = X ∖ V_sing`, if the maximum locus `C` (the next centre) meets the preimage of `U` at `c`,
then the exceptional image of `T` lies in `V_sing` and the strict transform of `V` is the connected component of `C` through
`c`, regular of dimension `dim V` at each of its points (`C` is an admissible centre). -/
theorem strictTransform_eq_connectedComponentIn_maxLocus [CompactSpace X] (hF : EmbeddingFields n k inv)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)
      (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) T)
    (hT : CentresAvoid (regularOpen V) T) {c : Y}
    (hc : c ∈ ResolutionDriver.maxLocus (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T)
      (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hcU : T.proj c ∈ regularOpen V) :
    T.proj '' exceptionalLocus n T.proj ⊆ singularLocus V ∧
      strictTransform n T.proj V.carrier =
        connectedComponentIn (ResolutionDriver.maxLocus
          (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T)
          (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp) c ∧
      ∀ x ∈ strictTransform n T.proj V.carrier,
        RegularAtDim (n := n) (strictTransform n T.proj V.carrier) x V.dim := by
  have hTt := hF.isGeoTestTower_of_isCanonical hdom T hcan
  have hadm := hF.isAdmissibleCentre_maxLocus hdom T hcan hTt
  exact strictTransform_eq_connectedComponentIn V T hT hadm.1
    (fun y hy => mem_maxLocus_iff_of_centresAvoid hF V hdom T hcan hT hc hcU hy) hc hcU

end Invariant

/-! ### The stopping -/

section Stopping

variable {Λ : Type v} [LinearOrder Λ] {X : CMfd.{u} n}

/-- **The first centre meeting an open set** (any value function): along a canonical segment `T` whose centres do not all
miss the preimages of `U`, some prefix `T'` (`T = T' S`) is canonical, its centres miss the preimages of `U`, and its
maximum locus -- the next centre of `T`, which is nonempty -- meets the preimage of `U`. -/
theorem exists_first_centre (𝔪 : MarkedIdeal n X) (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 inv T → ¬ CentresAvoid U T →
      ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y') (S : BlowupTower Y' Y), T'.append S = T ∧
        IsCanonical 𝔪 inv T' ∧ CentresAvoid U T' ∧
        ∃ c ∈ ResolutionDriver.maxLocus (inv T') (geoTransformAlong 𝔪 T').cosupp, T'.proj c ∈ U
  | _, .refl, _, h => absurd trivial h
  | _, .step T C π hπ, hcan, h => by
      obtain ⟨hcT, hC⟩ : IsCanonical 𝔪 inv T ∧
          (C = ∅ ∨ C = ResolutionDriver.maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      by_cases hT : CentresAvoid U T
      · have hd : ¬ Disjoint C (T.proj ⁻¹' (U : Set X)) := fun hd => h ⟨hT, hd⟩
        obtain ⟨c, hcC, hcU⟩ := Set.not_disjoint_iff.mp hd
        rcases hC with hC | hC
        · rw [hC] at hcC
          exact absurd hcC (notMem_empty c)
        · exact ⟨_, T, .step .refl C π hπ, rfl, hcT, hT, c, by rw [← hC]; exact hcC, hcU⟩
      · obtain ⟨Y', T', S, hTS, h1, h2, h3⟩ := exists_first_centre 𝔪 inv U T hcT hT
        subst hTS
        exact ⟨Y', T', .step S C π hπ, rfl, h1, h2, h3⟩

/-- **Some centre meets the smooth part**: along a multiple test blow-up of `(X, X, ∅, 𝓘_V, 1)` with empty final cosupport
(a resolution), not every centre misses the preimage of `U = X ∖ V_sing` -- otherwise the cosupport over `U` would be the
preimage of `V_reg ≠ ∅` (`mem_cosupp_iff_of_centresAvoid`; the projection is onto, `X` being compact). -/
theorem not_centresAvoid_of_cosupp_eq_empty {k : ℕ} [CompactSpace X] (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hTt : IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T)
    (hres : (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp = ∅) :
    ¬ CentresAvoid (regularOpen V) T := by
  intro hT
  obtain ⟨x, hx⟩ := V.regularLocus_nonempty
  obtain ⟨y, rfl⟩ := (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective T.isBlowupSequence).2 x
  have hyU : T.proj y ∈ regularOpen V := mem_regularOpen_of_regularAtDim hx
  have hy := (mem_cosupp_iff_of_centresAvoid V.isClosed_carrier hdom (regularOpen V) T hTt hT hyU).mpr
    (regularLocus_subset _ _ hx)
  rw [hres] at hy
  exact hy

end Stopping

/-! ### Assembly -/

section Assembly

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Embedded resolution from a canonical resolution of `(X, X, ∅, 𝓘_V, 1)`** (`hir:embedded-from-resolution`, conditional
on a value function with the four properties): for `inv` with properties (1), (4), (5), (6) (`EmbeddingFields`), `X`
compact, `𝔪_V = (X, X, ∅, 𝓘_V, 1)` in the domain, and a canonical segment `T` of `𝔪_V` with empty final cosupport, the prefix
`T'` of `T` before the first centre meeting the preimage of `X ∖ V_sing` is a canonical segment whose exceptional image lies
in `V_sing` and whose strict transform of `V` is regular of dimension `dim V` at each of its points.  Property (8) is not
used. -/
theorem exists_embedded_of_isCanonical {X : CMfd.{u} n} [CompactSpace X] (hF : EmbeddingFields n k inv)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)
      (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) T)
    (hres : (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp = ∅) :
    ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y') (S : BlowupTower Y' Y), T'.append S = T ∧
      IsCanonical (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)
        (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) T' ∧
      CentresAvoid (regularOpen V) T' ∧
      T'.proj '' exceptionalLocus n T'.proj ⊆ singularLocus V ∧
      ∀ x ∈ strictTransform n T'.proj V.carrier,
        RegularAtDim (n := n) (strictTransform n T'.proj V.carrier) x V.dim := by
  have hTt := hF.isGeoTestTower_of_isCanonical hdom T hcan
  obtain ⟨Y', T', S, hTS, h1, h2, c, hc, hcU⟩ := exists_first_centre _ _ (regularOpen V) T hcan
    (not_centresAvoid_of_cosupp_eq_empty V hdom T hTt hres)
  obtain ⟨hE, -, hreg⟩ := strictTransform_eq_connectedComponentIn_maxLocus hF V hdom T' h1 h2 hc hcU
  exact ⟨Y', T', S, hTS, h1, h2, hE, hreg⟩

/-- **The conclusion of `EmbeddedResolution.exists_embeddedResolution_smoothData`, from a canonical resolution**, in that
statement's shape (the field `regularAtDim_strictTransform` of `EmbeddedResolutionSmoothData` written out; that file is not
imported): a finite sequence of blowups with smooth centres `μ : X̃ → X` with `μ(Exc μ) ⊆ V_sing` and a strict transform of `V`
regular of dimension `dim V` at each of its points.  Hypotheses: a value function with the four properties, `(X, X, ∅, 𝓘_V, 1)`
in its domain, and a canonical segment of it with empty final cosupport (from whichever driver resolves it). -/
theorem exists_embeddedResolution_data_of_isCanonical {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] (hF : EmbeddingFields n k inv)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X)))
    (hres : ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) X) Y),
      IsCanonical (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X))
        (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X))) T ∧
      (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X))
        T).cosupp = ∅) :
    ∃ (Xt : Type u) (_ : TopologicalSpace Xt) (_ : ChartedSpace (ComplexModel n) Xt) (_ : IsComplexManifold n Xt)
      (μ : Xt → X) (_ : IsBlowupSequence n X Xt μ),
      μ '' exceptionalLocus n μ ⊆ singularLocus V ∧
        ∀ x ∈ strictTransform n μ V.carrier, RegularAtDim (n := n) (strictTransform n μ V.carrier) x V.dim := by
  obtain ⟨Y, T, hcan, hcos⟩ := hres
  obtain ⟨Y', T', -, -, -, -, hE, hreg⟩ :=
    exists_embedded_of_isCanonical (X := CMfd.of (n := n) X) hF V hdom T hcan hcos
  exact ⟨Y', inferInstance, inferInstance, inferInstance, T'.proj, T'.isBlowupSequence, hE, hreg⟩

/-- **The same from a resolution invariant of the present structure** (`ResolutionInvariantExt.ResolutionInvariant`; its
canonical resolution, `ResolutionInvariantExt.exists_isGeoResolution_isCanonical`, uses property (8)). -/
theorem exists_embeddedResolution_data_of_resolutionInvariant {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X))) :
    ∃ (Xt : Type u) (_ : TopologicalSpace Xt) (_ : ChartedSpace (ComplexModel n) Xt) (_ : IsComplexManifold n Xt)
      (μ : Xt → X) (_ : IsBlowupSequence n X Xt μ),
      μ '' exceptionalLocus n μ ⊆ singularLocus V ∧
        ∀ x ∈ strictTransform n μ V.carrier, RegularAtDim (n := n) (strictTransform n μ V.carrier) x V.dim := by
  obtain ⟨Y, T, hcan, -, hcos⟩ := ResolutionInvariantExt.exists_isGeoResolution_isCanonical R hdom
  exact exists_embeddedResolution_data_of_isCanonical (embeddingFields_of_resolutionInvariant R) V hdom
    ⟨Y, T, hcan, hcos⟩

end Assembly

/-! ### The domain hypothesis away from Cartan's theorem, and the case `dim V = n` -/

section Domain

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A set containing a neighbourhood of `x` is regular of dimension `n` at `x`. -/
theorem regularAtDim_of_mem_nhds {S : Set M} {x : M} (hS : S ∈ 𝓝 x) : RegularAtDim (n := n) S x n := by
  obtain ⟨O, hOS, hOo, hxO⟩ := mem_nhds_iff.mp hS
  refine RegularPointDimension.regularAtDim_of_inter_eq hOo hxO ?_
    (AnalyticIrreducibleComponents.regularAtDim_univ x)
  rw [univ_inter, inter_eq_right.mpr hOS]

/-- A set regular of dimension `n` at `x` is a neighbourhood of `x`. -/
theorem mem_nhds_of_regularAtDim_self {S : Set M} {x : M} (hx : RegularAtDim (n := n) S x n) : S ∈ 𝓝 x := by
  obtain ⟨_, _, Φ, _, _, hflat⟩ := hx
  have hO : IsOpen ((complexChartAt (n := n) x).val.source ∩ (complexChartAt (n := n) x).val ⁻¹' Φ.source) :=
    (complexChartAt (n := n) x).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) x).val.open_source Φ.isOpen_source
  refine mem_of_superset (hO.mem_nhds ⟨mem_complexChartAt_source x, Φ.center_mem_source⟩) fun y hy => ?_
  refine (hflat hy.1 hy.2).mpr ?_
  intro i hi
  exact absurd i.2 (not_lt.mpr hi)

/-- **A subvariety of dimension `< n` has empty interior** (the identity theorem along a component and irreducibility): an
interior point is a regular point of dimension `n`, so `V` is the closure of the component of its regular locus through it
(`StrictTransformSubvariety.eq_closure_component`), whose points are all regular of dimension `n`; a regular point of
dimension `dim V` lies in that closure, hence in that component, and the two dimensions agree
(`RegularPointDimension.eq_of_regularAtDim`). -/
theorem interior_eq_empty_of_dim_lt (V : ClosedIrreducibleAnalyticSubvariety n M) (h : V.dim < n) :
    interior V.carrier = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hxn : RegularAtDim (n := n) V.carrier x n := regularAtDim_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨c, -, hc⟩ := V.exists_regular_point
  have hVeq := StrictTransformSubvariety.eq_closure_component V.irreducible_carrier hxn
  obtain ⟨W, hW, hcW, hWc⟩ := exists_open_inter_subset_component hc (mem_component_self hc)
  have hcl : c ∈ closure (component (n := n) V.carrier x) := hVeq ▸ hc.2.1
  obtain ⟨z, hzW, hzx⟩ := mem_closure_iff.mp hcl W hW hcW
  have hzc : z ∈ component (n := n) V.carrier c := hWc ⟨component_subset V.carrier x hzx, hzW⟩
  have h1 : component (n := n) V.carrier x = component (n := n) V.carrier c :=
    (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzc).symm
  have hcx : c ∈ component (n := n) V.carrier x := by
    rw [h1]
    exact mem_component_self hc
  have := RegularPointDimension.eq_of_regularAtDim hc (regularAtDim_of_mem_component hxn hcx)
  omega

/-- **The ideal of a subvariety of dimension `< n` is nonzero at every point** (`IsNonzeroAlongAt univ`): off `V` the
constant `1` lies in it; at a point of `V`, some local equation of `V` (in a presentation of the analytic set) does not vanish
identically near the point, since otherwise `V` would contain a neighbourhood of it (`interior_eq_empty_of_dim_lt`). -/
theorem isNonzeroAlongAt_vanishingIdeal_of_dim_lt (V : ClosedIrreducibleAnalyticSubvariety n M) (h : V.dim < n)
    (x : M) : DivisorExponentAlong.IsNonzeroAlongAt (univ : Set M) (vanishingIdeal (n := n) V.carrier) x := by
  by_cases hxV : x ∈ V.carrier
  · obtain ⟨P⟩ := V.analytic x
    set e := complexChartAt (n := n) x with he
    have hsrc : e.val.source ∈ 𝓝 x := e.val.open_source.mem_nhds (mem_complexChartAt_source x)
    have hnb : e.val ⁻¹' P.coordinateNeighborhood ∈ 𝓝 x :=
      (e.val.continuousAt (mem_complexChartAt_source x)).preimage_mem_nhds
        (P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood)
    by_cases hall : ∀ i, ∀ᶠ y in 𝓝 x, P.generator i (e.val y) = 0
    · exfalso
      have hVn : V.carrier ∈ 𝓝 x := by
        filter_upwards [eventually_all.mpr hall, hsrc, hnb] with y h1 h2 h3
        exact (P.zeroLocus h2 h3).mpr h1
      have hint : x ∈ interior V.carrier := mem_interior_iff_mem_nhds.mpr hVn
      rw [interior_eq_empty_of_dim_lt V h] at hint
      exact hint
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      refine ⟨fun y => P.generator i (e.val y), ⟨?_, ?_⟩, hi.mono fun y hy => ⟨mem_univ y, hy⟩⟩
      · refine DerivativeIdeal.holomorphicAt_comp_chart e (mem_complexChartAt_source x) ?_
        filter_upwards [P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood] with z hz
        exact (P.generator_holomorphic i z hz).differentiableAt (P.isOpen_coordinateNeighborhood.mem_nhds hz)
      · filter_upwards [hsrc, hnb] with y h2 h3 hyV
        exact (P.zeroLocus h2 h3).mp hyV i
  · refine ⟨fun _ => (1 : ℂ), ⟨holomorphicAt_const 1, ?_⟩,
      Frequently.of_forall fun y => ⟨mem_univ y, one_ne_zero⟩⟩
    filter_upwards [V.isClosed_carrier.isOpen_compl.mem_nhds hxV] with y hy hyV
    exact absurd hyV hy

/-- **`(X, X, ∅, 𝓘_V, 1)` lies in the domain of the invariants in dimension `≤ k`** for `n ≤ k`, a subvariety of dimension
`< n`, and a coherent ideal `𝓘_V` (Cartan's theorem, a hypothesis here). -/
theorem isInvDomain_vanishingIdeal_of_dim_lt {k : ℕ} (hnk : n ≤ k) (V : ClosedIrreducibleAnalyticSubvariety n M)
    (h : V.dim < n) (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) :
    IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n M) where
  isWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, hcoh, NormalCrossings.isSNCDivisor_nil,
    NormalCrossings.isTransverse_nil_of_isClosedSubmanifold HomogenizedGlueingTower.isClosedSubmanifold_univ⟩
  dimLE := fun x _ => ⟨n, hnk, AnalyticIrreducibleComponents.regularAtDim_univ x⟩
  one_le_d := le_rfl
  isNonzeroAlongAt := fun x _ => isNonzeroAlongAt_vanishingIdeal_of_dim_lt V h x

/-- **A subvariety of dimension `n` is a connected component of `M`**, hence a closed connected submanifold of dimension
`n`: at a regular point `c` of dimension `n` it is a neighbourhood of `c`, so it contains the connected component `K` of `c`
(identity theorem along the component `K` of the regular locus of `M`); `K` is open and closed, so `K` and `V ∖ K` are
analytic, and irreducibility gives `V = K`. -/
theorem isClosedConnectedSubmanifold_of_dim_eq (V : ClosedIrreducibleAnalyticSubvariety n M) (h : V.dim = n) :
    IsClosedConnectedSubmanifold n V.carrier n := by
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel n) M
  obtain ⟨c, -, hc⟩ := V.exists_regular_point
  rw [h] at hc
  obtain ⟨O, hOV, hOo, hcO⟩ := mem_nhds_iff.mp (mem_nhds_of_regularAtDim_self hc)
  have hKo : IsOpen (connectedComponent c) := isOpen_connectedComponent
  have hKc : IsClosed (connectedComponent c) := isClosed_connectedComponent
  have hRu : regularPoints (n := n) (univ : Set M) = univ :=
    eq_univ_of_forall fun y => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ y⟩
  have hcomp : component (n := n) (univ : Set M) c = connectedComponent c := by
    show connectedComponentIn (regularPoints (n := n) (univ : Set M)) c = _
    rw [hRu, connectedComponentIn_univ]
  have hKV : connectedComponent c ⊆ V.carrier := by
    rw [← hcomp]
    exact component_subset_of_isOpen V.analytic hOo
      ⟨c, hcO, mem_component_self (AnalyticIrreducibleComponents.regularAtDim_univ c)⟩ fun y hy => hOV hy.1
  have hKan : IsComplexAnalyticSubset (n := n) (connectedComponent c) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_locally_eq isComplexAnalyticSubset_univ hKc
      fun y hy => ⟨connectedComponent c, hKo, hy, by rw [univ_inter, inter_self]⟩
  have hDan : IsComplexAnalyticSubset (n := n) (V.carrier \ connectedComponent c) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_locally_eq V.analytic (V.isClosed_carrier.sdiff hKo)
      fun y hy => ⟨(connectedComponent c)ᶜ, hKc.isOpen_compl, hy.2, by
        ext z
        simp only [mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
        tauto⟩
  rcases V.irreducible_carrier.eq_left_or_eq_right hKan hDan hKV sdiff_subset (union_sdiff_cancel hKV).symm with
    hVK | hVD
  · refine ⟨V.isClosed_carrier, hVK ▸ isConnected_connectedComponent, fun x hx => ?_⟩
    have hxK : x ∈ connectedComponent c := hVK ▸ hx
    refine RegularPointDimension.regularAtDim_of_inter_eq hKo hxK ?_
      (AnalyticIrreducibleComponents.regularAtDim_univ x)
    rw [univ_inter, hVK, inter_self]
  · exfalso
    have hcV : c ∈ V.carrier := hKV mem_connectedComponent
    rw [hVD] at hcV
    exact hcV.2 mem_connectedComponent

end Domain

/-! ### Embedded resolution modulo the invariant and Cartan's theorem -/

section Final

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The case `dim V = n` of `hir:embedded-from-resolution`**: the identity is an embedded resolution (`V` is a closed
connected submanifold of dimension `n`, `isClosedConnectedSubmanifold_of_dim_eq`; no exceptional locus, the strict transform
is `V`). -/
theorem exists_embeddedResolution_data_of_dim_eq {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] (V : ClosedIrreducibleAnalyticSubvariety n X)
    (h : V.dim = n) :
    ∃ (Xt : Type u) (_ : TopologicalSpace Xt) (_ : ChartedSpace (ComplexModel n) Xt) (_ : IsComplexManifold n Xt)
      (μ : Xt → X) (_ : IsBlowupSequence n X Xt μ),
      μ '' exceptionalLocus n μ ⊆ singularLocus V ∧
        ∀ x ∈ strictTransform n μ V.carrier, RegularAtDim (n := n) (strictTransform n μ V.carrier) x V.dim := by
  have hV := isClosedConnectedSubmanifold_of_dim_eq V h
  have hst : strictTransform n (id : X → X) V.carrier = V.carrier := by
    simp [strictTransform, exceptionalLocus_id, V.isClosed_carrier.closure_eq]
  refine ⟨X, inferInstance, inferInstance, inferInstance, id, IsBlowupSequence.refl, ?_, fun x hx => ?_⟩
  · simp [exceptionalLocus_id]
  · rw [hst] at hx ⊢
    rw [h]
    exact hV.2.2 x hx

/-- **`hir:embedded-from-resolution` from a resolution invariant and Cartan's theorem**: for a resolution invariant `R` of
the present structure in dimension `≤ k` with `n ≤ k`, a compact `X`, and a subvariety `V` whose ideal sheaf `𝓘_V` is coherent
(Cartan's theorem, a hypothesis here), there is a finite sequence of blowups with smooth centres whose exceptional image lies
in `V_sing` and whose strict transform of `V` is regular of dimension `dim V` at each of its points -- the conclusion of
`EmbeddedResolution.exists_embeddedResolution_smoothData`. For `dim V = n` the identity; otherwise
`exists_embeddedResolution_data_of_resolutionInvariant` with the domain hypothesis `isInvDomain_vanishingIdeal_of_dim_lt`. -/
theorem exists_embeddedResolution_data_of_resolutionInvariant_of_isCoherent {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (R : ResolutionInvariantExt.ResolutionInvariant.{u, v} n k Λ) (hnk : n ≤ k)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) :
    ∃ (Xt : Type u) (_ : TopologicalSpace Xt) (_ : ChartedSpace (ComplexModel n) Xt) (_ : IsComplexManifold n Xt)
      (μ : Xt → X) (_ : IsBlowupSequence n X Xt μ),
      μ '' exceptionalLocus n μ ⊆ singularLocus V ∧
        ∀ x ∈ strictTransform n μ V.carrier, RegularAtDim (n := n) (strictTransform n μ V.carrier) x V.dim := by
  rcases V.dim_le.lt_or_eq with h | h
  · exact exists_embeddedResolution_data_of_resolutionInvariant R V
      (isInvDomain_vanishingIdeal_of_dim_lt (M := CMfd.of (n := n) X) hnk V h hcoh)
  · exact exists_embeddedResolution_data_of_dim_eq V h

end Final

end

end TranscendentalNakamaye.Pending.EmbeddedFromResolution
