import Hironaka.Resolution.HironakaEmbeddedResolution
import Hironaka.Resolution.HironakaLocalPrincipalization

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Local embedded resolution on a non-compact complex manifold (Hironaka)

Blueprint `hir:embedded-resolution-local` (`blueprint/src/hironaka.tex`; TN.5, the local (non-compact) form of the Hironaka
strengthening (H+1) for the standalone library: the analogue for embedded resolution of `hir:principalization-local`).
Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), §13 (the algorithm over relatively compact open subsets);
Włodarczyk 2005 (`wlodarczyk05-hironaka`), Theorem 1.0.2 (embedded desingularization) and §2.3.

**Statement.**  Let `X` be a complex manifold, not necessarily compact, `V ⊆ X` a closed irreducible analytic subvariety and
`K ⊆ X` compact.  There are an open neighbourhood `U` of `K`, a finite sequence of blowups with smooth centres `f : U' → U`
and a divisor `E = (E₁, …, E_r)` on `U'` with simple normal crossings such that

* `Exc f ⊆ E₁ ∪ ⋯ ∪ E_r ⊆ f⁻¹(V_sing)`, and `f` is an isomorphism over `U \ V_sing`;
* the strict transform `V'` of `V ∩ U` is a closed submanifold of `U'`, of dimension `dim V` at each of its points;
* `V'` has only normal crossings with `E`.

(`V ∩ U` need not be irreducible nor connected, so neither need `V'` be.)

**Route.**  The local canonical driver of `HironakaLocalPrincipalization`, now returning a *canonical segment*
(`exists_local_resolution_isCanonical`: canonical segments restrict to open sets, `isCanonical_restrict`, and correspond along
isomorphisms of towers, `isCanonical_of_isTowerIso`, for every value function with the properties
`EmbeddedFromResolution.EmbeddingFields`), applied to `(X, X, ∅, 𝓘_V, 1)`; over `U` this is `(U, U, ∅, 𝓘_{V ∩ U}, 1)`.  Then the
first-centre argument of `hir:embedded-from-resolution`, with an identity-principle step that needs neither compactness nor
irreducibility of the strict transform (`strictTransform_of_centresAvoid`): the strict transform `S` of an analytic set `W` is
analytic (`isComplexAnalyticSubset_strictTransform_proj`), it is the closure of its part over `U \ V_sing` (the regular points of
`W` of dimension `dim V` are dense in `W`), which there agrees with the first centre `C`; the identity theorem along each connected
component of the closed submanifold `C` meeting that part puts the component into `S`, so `S` agrees with `C` near each of its
points.

Compactness is removed along the way from the basic facts the embedded-resolution argument of `EmbeddedFromResolution` uses:
the image of the exceptional locus of a blowup is closed and analytic, the strict transform of an analytic set (resp. of an
irreducible subvariety) along any blowup sequence is analytic (resp. an irreducible subvariety of the same dimension, connected
when the exceptional image lies in `V_sing`), and the stopping and identity-principle steps of `EmbeddedFromResolution` hold on
any complex manifold.

## Main results

* `isClosed_image_exceptionalLocus`, `isComplexAnalyticSubset_image_exceptionalLocus`,
  `isComplexAnalyticSubset_strictTransform_of_isBlowupAlong`, `isComplexAnalyticSubset_strictTransform_proj`;
* `exists_strictTransform_subvariety_of_isBlowupAlong`, `exists_strictTransform_subvariety_of_isBlowupSequence`,
  `isConnected_strictTransform_of_isBlowupSequence`: `StrictTransformSubvariety(Sequence)` without `[CompactSpace]`;
* `strictTransform_eq_connectedComponentIn`, `strictTransform_eq_connectedComponentIn_maxLocus`,
  `not_centresAvoid_of_cosupp_eq_empty`, `exists_embedded_of_isCanonical`: the corresponding lemmas of `EmbeddedFromResolution`
  without `[CompactSpace]`;
* `isCanonical_of_isTowerIso`, **`exists_local_resolution_isCanonical`** (the local canonical driver with a canonical output);
* `mem_maxLocus_iff_of_centresAvoid_of_pureDim`, **`strictTransform_of_centresAvoid`** (the identity-principle step for an
  analytic set, not necessarily irreducible), `exceptionalDivisor_facts_of_centresAvoid`;
* **`exists_tower_embeddedResolution_local`** (tower form) and **`exists_embeddedResolution_local`** (the public statement).

Import discipline (standalone Hironaka library): this module imports `HironakaEmbeddedResolution` and
`HironakaLocalPrincipalization` only; it does not import, even transitively, `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaEmbeddedResolutionLocal

open Hironaka.NonKahlerLocus Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings
  Hironaka.RestrictEmptyTower Hironaka.RegularLocusComponent
  Hironaka.MarkedIdealBiholomorphism Hironaka.BlowupTowerIsomorphism
  Hironaka.BlowupTowerTransforms
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.EmbeddedFromResolution (EmbeddingFields regularOpen mem_regularOpen_iff
  regularAtDim_of_mem_regularOpen mem_regularOpen_of_regularAtDim notMem_exceptionalLocus_of_centresAvoid
  image_exceptionalLocus_subset_compl mem_strictTransform_iff_of_centresAvoid mem_cosupp_iff_of_centresAvoid
  mem_maxLocus_iff_of_centresAvoid exists_first_centre isInvDomain_vanishingIdeal_of_dim_lt
  isClosedConnectedSubmanifold_of_dim_eq)

noncomputable section

variable {n : ℕ}

/-! ### The image of the exceptional locus and strict transforms, without compactness -/

section Analytic

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M}

/-- **The image of the exceptional locus of a blowup is closed** (on any complex manifold; a blowup is a closed map,
`HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong`; `ExceptionalFibres.isClosed_image_exceptionalLocus` without
compactness). -/
theorem isClosed_image_exceptionalLocus (hπ : IsBlowupAlong n C π) : IsClosed (π '' exceptionalLocus n π) :=
  (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ).isClosedMap _
    (isOpen_compl_iff.mp (StrictTransformComposition.isOpen_compl_exceptionalLocus hπ.contMDiff))

open BlowupFlatCoordinates ExceptionalImageCodimension in
/-- **The image of the exceptional locus of a blowup is analytic** (on any complex manifold;
`ExceptionalImageAnalytic.isComplexAnalyticSubset_image_exceptionalLocus` without compactness: closedness and surjectivity
come from properness).  It is the union of the connected components of the centre of codimension at least two. -/
theorem isComplexAnalyticSubset_image_exceptionalLocus (hπ : IsBlowupAlong n C π) :
    IsComplexAnalyticSubset (n := n) (π '' exceptionalLocus n π) := by
  classical
  have hT : IsClosed (π '' exceptionalLocus n π) := isClosed_image_exceptionalLocus hπ
  have hsurj := HironakaLocalPrincipalization.surjective_of_isBlowupAlong hπ
  intro x
  by_cases hx : x ∈ π '' exceptionalLocus n π
  swap
  · exact PureDimension.nonempty_presentation_of_not_mem hT Subset.rfl hx
  have hxC : x ∈ C := ExceptionalFibres.image_exceptionalLocus_subset hπ hx
  obtain ⟨z₀, hz₀, rfl⟩ := hx
  obtain ⟨k, -, -, Φ, hΦt, -, hΦ⟩ := hπ.1.2 _ hxC
  have hz₀Φ : π z₀ ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hkn : k < n := lt_of_mem_flatDomain hπ hΦt hΦ hz₀Φ
  have hk2 : k + 2 ≤ n := by
    by_contra hk
    exact not_mem_exceptionalLocus hπ hΦt hΦ (by omega) hz₀Φ hz₀
  have hTC : ∀ y ∈ flatDomain Φ, y ∈ π '' exceptionalLocus n π ↔ y ∈ C := by
    intro y hy
    refine ⟨fun h => ExceptionalFibres.image_exceptionalLocus_subset hπ h, fun hyC => ?_⟩
    obtain ⟨z, rfl⟩ := hsurj y
    exact ⟨z, mem_exceptionalLocus_of_mem hπ hΦt hΦ hk2 hyC hy, rfl⟩
  refine ⟨{ generatorCount := n
            generator := fun i w => if k ≤ i.1 then Φ.toFun w i else 0
            coordinateNeighborhood := Φ.source
            isOpen_coordinateNeighborhood := Φ.isOpen_source
            center_mem_coordinateNeighborhood := Φ.center_mem_source
            coordinateNeighborhood_subset_target := hΦt
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · intro i
    by_cases hi : k ≤ i.1
    · simp only [hi, if_true]
      exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp_differentiableOn
        Φ.toFun_holomorphic
    · simp only [hi, if_false]
      exact differentiableOn_const 0
  · intro y hy hyU
    rw [hTC y ⟨hy, hyU⟩, hΦ hy hyU]
    simp only [complexCoordinatePlane, mem_ofPred_eq]
    refine forall_congr' fun i => ?_
    by_cases hi : k ≤ i.1 <;> simp [hi]

/-- **The strict transform of an analytic set under a blowup is analytic** (on any complex manifold, for any analytic set,
not necessarily irreducible): `π̃⁻¹ A = closure (π⁻¹ A \ π⁻¹ π(Exc π))` is the closure of a difference of analytic sets. -/
theorem isComplexAnalyticSubset_strictTransform_of_isBlowupAlong (hπ : IsBlowupAlong n C π) {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) : IsComplexAnalyticSubset (n := n) (strictTransform n π A) := by
  have hExc : π ⁻¹' (π '' exceptionalLocus n π) = exceptionalLocus n π :=
    ExceptionalFibres.preimage_image_exceptionalLocus hπ
  have h := ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hA)
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff
      (isComplexAnalyticSubset_image_exceptionalLocus hπ))
  rw [hExc] at h
  exact h

end Analytic

/-- **The strict transform of an analytic set along a tower is analytic** (any complex manifold, any analytic set): strict
transforms compose (`StrictTransformComposition.strictTransform_comp`). -/
theorem isComplexAnalyticSubset_strictTransform_proj {X : CMfd.{u} n} {A : Set X}
    (hA : IsComplexAnalyticSubset (n := n) A) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsComplexAnalyticSubset (n := n) (strictTransform n T.proj A)
  | _, .refl => by
      have h : strictTransform n (id : X → X) A = A := by
        simp [strictTransform, exceptionalLocus_id, hA.isClosed.closure_eq]
      show IsComplexAnalyticSubset (n := n) (strictTransform n (id : X → X) A)
      rw [h]
      exact hA
  | _, .step T _ π hπ => by
      show IsComplexAnalyticSubset (n := n) (strictTransform n (T.proj ∘ π) A)
      rw [StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff]
      exact isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ (isComplexAnalyticSubset_strictTransform_proj hA T)

/-! ### Strict transforms of irreducible subvarieties, without compactness -/

section Subvariety

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- **The strict transform of an irreducible subvariety under one blowup is an irreducible subvariety of the same
dimension** (`StrictTransformSubvariety.exists_strictTransform_subvariety_of_isBlowupAlong` on any complex manifold: the
image of the exceptional locus is closed and analytic, and the blowup is surjective, without compactness). -/
theorem exists_strictTransform_subvariety_of_isBlowupAlong {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y) (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g) :
    ∃ Wt : ClosedIrreducibleAnalyticSubvariety n Z,
      Wt.carrier = strictTransform n g W.carrier ∧ Wt.dim = W.dim := by
  classical
  set T := g '' exceptionalLocus n g with hTdef
  have hT : IsComplexAnalyticSubset (n := n) T := isComplexAnalyticSubset_image_exceptionalLocus hg
  have hTc : IsClosed T := isClosed_image_exceptionalLocus hg
  have hExc : g ⁻¹' T = exceptionalLocus n g := ExceptionalFibres.preimage_image_exceptionalLocus hg
  have hgc : Continuous g := hg.contMDiff.continuous
  have hsurj := HironakaLocalPrincipalization.surjective_of_isBlowupAlong hg
  set Ω : Set Z := (exceptionalLocus n g)ᶜ with hΩdef
  have hΩ : IsOpen Ω := StrictTransformComposition.isOpen_compl_exceptionalLocus hg.contMDiff
  set Wt : Set Z := strictTransform n g W.carrier with hWtdef
  -- analyticity
  have hWtA : IsComplexAnalyticSubset (n := n) Wt :=
    isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hg W.analytic
  have hpreW : IsClosed (g ⁻¹' W.carrier) := W.isClosed_carrier.preimage hgc
  have hWt_sub : Wt ⊆ g ⁻¹' W.carrier := closure_minimal sdiff_subset hpreW
  have hWtΩ : ∀ u ∈ Ω, u ∈ Wt ↔ g u ∈ W.carrier := fun u hu =>
    ⟨fun h => hWt_sub h, fun h => subset_closure ⟨h, hu⟩⟩
  -- a regular point of `W` off `T`
  obtain ⟨y, hyW, hyT⟩ := not_subset.mp hW
  obtain ⟨c, hcT, k, hck⟩ := RegularLocusDense.exists_regularAtDim_mem_of_isOpen W.analytic
    hTc.isOpen_compl hyW hyT
  have hkd : k = W.dim := AnalyticIrreducibleComponents.eq_dim_of_regularAtDim W hck
  subst hkd
  obtain ⟨ct, hct⟩ := hsurj c
  have hctΩ : ct ∈ Ω := fun h => hcT ⟨ct, h, hct⟩
  have hreg : ∀ u ∈ Ω, RegularAtDim (n := n) W.carrier (g u) W.dim →
      RegularAtDim (n := n) Wt u W.dim := fun u hu hr =>
    RegularAtDimTransport.regularAtDim_of_preimage hg.contMDiff hu hΩ hu hWtΩ hr
  have hctreg : RegularAtDim (n := n) Wt ct W.dim := hreg ct hctΩ (hct ▸ hck)
  -- the component through `c` and its part off `T`
  set K := component (n := n) W.carrier c with hKdef
  have hWK : W.carrier = closure K := StrictTransformSubvariety.eq_closure_component W.irreducible_carrier hck
  have hKT : ¬ K ⊆ T := fun h => hW (hWK ▸ closure_minimal h hTc)
  obtain ⟨hKTconn, hKTdense⟩ :=
    ComponentComplementConnected.isPreconnected_component_diff_and_subset_closure
      W.analytic hT hck hKT
  -- `g` on `Ω` is an injective open map
  let f : Ω → Y := fun u => g u
  have hfinj : Function.Injective f := fun u v huv =>
    Subtype.ext (ExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus hg v.2 huv)
  have hfopen : IsOpenMap f := by
    refine IsOpenMap.of_nhds_le fun u => ?_
    have h1 := StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus
      hg.contMDiff u.2
    have h2 : map ((↑) : Ω → Z) (𝓝 u) = 𝓝 (u : Z) := (hΩ.isOpenEmbedding_subtypeVal).map_nhds_eq u
    change 𝓝 (g u) ≤ map (g ∘ (↑)) (𝓝 u)
    rw [← map_map, h2, h1]
  have hrange : K \ T ⊆ range f := by
    rintro x ⟨-, hxT⟩
    obtain ⟨z, rfl⟩ := hsurj x
    exact ⟨⟨z, fun h => hxT ⟨z, h, rfl⟩⟩, rfl⟩
  set S : Set Z := (↑) '' (f ⁻¹' (K \ T)) with hSdef
  have hSconn : IsPreconnected S :=
    (hKTconn.preimage_of_isOpenMap hfinj hfopen hrange).image _ continuous_subtype_val.continuousOn
  have hSreg : S ⊆ regularPoints (n := n) Wt := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨W.dim, hreg u u.2 (regularAtDim_of_mem_component hck hu.1)⟩
  have hctS : ct ∈ S := ⟨⟨ct, hctΩ⟩, ⟨show g ct ∈ K by rw [hct]; exact mem_component_self hck,
    show g ct ∉ T by rw [hct]; exact hcT⟩, rfl⟩
  have hSK : S ⊆ component (n := n) Wt ct :=
    subset_component_of_isPreconnected hSconn hSreg ⟨ct, hctS, mem_component_self hctreg⟩
  -- density
  have hdense : Wt ⊆ closure (component (n := n) Wt ct) := by
    have h1 : g ⁻¹' W.carrier \ exceptionalLocus n g ⊆ closure S := by
      rintro u ⟨huW, huΩ⟩
      refine mem_closure_iff.mpr fun N hN huN => ?_
      have hmap := StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus
        hg.contMDiff huΩ
      have himg : g '' (N ∩ Ω) ∈ 𝓝 (g u) := by
        rw [← hmap]
        exact image_mem_map ((hN.inter hΩ).mem_nhds ⟨huN, huΩ⟩)
      have hgu : g u ∈ closure (K \ T) := by
        have h := hWK ▸ huW
        exact closure_minimal hKTdense isClosed_closure h
      obtain ⟨_, ⟨v, ⟨hvN, hvΩ⟩, rfl⟩, hvKT⟩ :=
        mem_closure_iff_nhds.mp hgu _ himg
      exact ⟨v, hvN, ⟨v, hvΩ⟩, hvKT, rfl⟩
    exact closure_minimal (h1.trans (closure_mono hSK)) isClosed_closure
  have hWt_eq : Wt = closure (component (n := n) Wt ct) :=
    Subset.antisymm hdense (closure_minimal (component_subset (n := n) Wt ct) hWtA.isClosed)
  have hirr : IsComplexAnalyticallyIrreducible (n := n) Wt := by
    rw [IsComplexAnalyticallyIrreducible.congr hWt_eq]
    exact isComplexAnalyticallyIrreducible_closure_component hWtA hctreg
  exact ⟨⟨Wt, hWtA.isClosed, hirr, W.dim, W.dim_le, ⟨ct, hctreg⟩⟩, rfl, rfl⟩

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Xt : Type u} [TopologicalSpace Xt] [ChartedSpace (ComplexModel n) Xt] [IsComplexManifold n Xt]

/-- **The strict transform of an irreducible subvariety along a blowup sequence is an irreducible subvariety of the same
dimension**, provided the subvariety is not exceptional for the whole sequence
(`StrictTransformSubvarietySequence.exists_strictTransform_subvariety_of_isBlowupSequence` on any complex manifold). -/
theorem exists_strictTransform_subvariety_of_isBlowupSequence {μ : Xt → X} (hμ : IsBlowupSequence n X Xt μ)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hV : ¬ V.carrier ⊆ μ '' exceptionalLocus n μ) :
    ∃ Vt : ClosedIrreducibleAnalyticSubvariety n Xt,
      Vt.carrier = strictTransform n μ V.carrier ∧ Vt.dim = V.dim := by
  induction hμ with
  | refl =>
      refine ⟨V, ?_, rfl⟩
      simp [strictTransform, exceptionalLocus_id, V.isClosed_carrier.closure_eq]
  | step f C g hfs hg ih =>
      have hsurjf := HironakaLocalPrincipalization.IsBlowupSequence.surjective hfs
      have hsurjg := HironakaLocalPrincipalization.surjective_of_isBlowupAlong hg
      have hVf : ¬ V.carrier ⊆ f '' exceptionalLocus n f := fun h =>
        hV (h.trans (StrictTransformComposition.image_exceptionalLocus_subset_comp
          (hfs.contMDiff.mdifferentiable (by simp)) (hg.contMDiff.mdifferentiable (by simp))
          hsurjg))
      obtain ⟨W, hWc, hWd⟩ := ih hVf
      have hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g := by
        rw [hWc]
        exact StrictTransformComposition.not_strictTransform_subset_image_exceptionalLocus
          hfs.contMDiff hg.contMDiff hsurjf hsurjg hV
      obtain ⟨Vt, hVc, hVd⟩ := exists_strictTransform_subvariety_of_isBlowupAlong hg W hW
      refine ⟨Vt, ?_, hVd.trans hWd⟩
      rw [hVc, hWc, StrictTransformComposition.strictTransform_comp hfs.contMDiff hg.contMDiff]

/-- **The strict transform is connected when the exceptional image lies in the singular locus**
(`StrictTransformSubvarietySequence.isConnected_strictTransform_of_isBlowupSequence` on any complex manifold). -/
theorem isConnected_strictTransform_of_isBlowupSequence {μ : Xt → X} (hμ : IsBlowupSequence n X Xt μ)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hExcS : μ '' exceptionalLocus n μ ⊆ singularLocus V) :
    IsConnected (strictTransform n μ V.carrier) := by
  obtain ⟨Vt, hVt, -⟩ := exists_strictTransform_subvariety_of_isBlowupSequence hμ V
    (StrictTransformSubvarietySequence.not_subset_image_exceptionalLocus_of_image_exceptionalLocus_subset_singular
      V hExcS)
  obtain ⟨c, -, hc⟩ := Vt.exists_regular_point
  have hcomponent : IsConnected (component (n := n) Vt.carrier c) := by
    change IsConnected (connectedComponentIn (regularPoints (n := n) Vt.carrier) c)
    exact isConnected_connectedComponentIn_iff.mpr ⟨Vt.dim, hc⟩
  rw [← hVt, StrictTransformSubvariety.eq_closure_component Vt.irreducible_carrier hc]
  exact hcomponent.closure

end Subvariety

/-! ### The identity-principle step and the stopping of `EmbeddedFromResolution`, without compactness -/

section Identity

variable {X : CMfd.{u} n}

/-- **The identity-principle step of `hir:embedded-from-resolution` on any complex manifold**
(`EmbeddedFromResolution.strictTransform_eq_connectedComponentIn` without `[CompactSpace]`; the same proof, with the strict
transform of an irreducible subvariety along a blowup sequence from `exists_strictTransform_subvariety_of_isBlowupSequence`). -/
theorem strictTransform_eq_connectedComponentIn (V : ClosedIrreducibleAnalyticSubvariety n X)
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
  have hExc : T.proj '' exceptionalLocus n T.proj ⊆ singularLocus V := by
    intro x hx
    by_contra hxs
    exact image_exceptionalLocus_subset_compl (regularOpen V) T hT hx hxs
  have hSO : ∀ y ∈ O, y ∈ S ↔ T.proj y ∈ V.carrier := fun y hy =>
    mem_strictTransform_iff_of_centresAvoid (regularOpen V) T hT V.isClosed_carrier hy
  have hCS : ∀ y ∈ O, y ∈ C ↔ y ∈ S := fun y hy => (hCV y hy).trans (hSO y hy).symm
  have hSOC : S ∩ O = C ∩ O := by
    ext y
    exact ⟨fun h => ⟨(hCS y h.2).mpr h.1, h.2⟩, fun h => ⟨(hCS y h.2).mp h.1, h.2⟩⟩
  have hfcV : T.proj c ∈ V.carrier := (hCV c hcU).mp hc
  have hSc : RegularAtDim (n := n) S c V.dim :=
    RegularAtDimTransport.regularAtDim_of_preimage T.contMDiff_proj
      (notMem_exceptionalLocus_of_centresAvoid (regularOpen V) T hT c hcU) hO hcO hSO
      (regularAtDim_of_mem_regularOpen hfcV hcU)
  have hCc : RegularAtDim (n := n) C c V.dim :=
    RegularPointDimension.regularAtDim_of_inter_eq hO hcO hSOC hSc
  obtain ⟨Vt, hVt, -⟩ := exists_strictTransform_subvariety_of_isBlowupSequence T.isBlowupSequence V
    (StrictTransformSubvarietySequence.not_subset_image_exceptionalLocus_of_image_exceptionalLocus_subset_singular
      V hExc)
  have hSirr : IsComplexAnalyticallyIrreducible (n := n) S := by rw [hSdef, ← hVt]; exact Vt.irreducible_carrier
  have hCan : IsComplexAnalyticSubset (n := n) C := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC
  have hRC : regularPoints (n := n) C = C :=
    Subset.antisymm (regularPoints_subset C) fun y hy => hC.2 y hy
  have hKC : component (n := n) C c = connectedComponentIn C c := by
    show connectedComponentIn (regularPoints (n := n) C) c = _
    rw [hRC]
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

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The identity-principle step for the first centre meeting the smooth part, on any complex manifold**
(`EmbeddedFromResolution.strictTransform_eq_connectedComponentIn_maxLocus` without `[CompactSpace]`). -/
theorem strictTransform_eq_connectedComponentIn_maxLocus (hF : EmbeddingFields n k inv)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)
      (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X)) T)
    (hT : CentresAvoid (regularOpen V) T) {c : Y}
    (hc : c ∈ maxLocus (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T)
      (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hcU : T.proj c ∈ regularOpen V) :
    T.proj '' exceptionalLocus n T.proj ⊆ singularLocus V ∧
      strictTransform n T.proj V.carrier =
        connectedComponentIn (maxLocus
          (inv (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T)
          (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp) c ∧
      ∀ x ∈ strictTransform n T.proj V.carrier,
        RegularAtDim (n := n) (strictTransform n T.proj V.carrier) x V.dim := by
  have hTt := hF.isGeoTestTower_of_isCanonical hdom T hcan
  have hadm := hF.isAdmissibleCentre_maxLocus hdom T hcan hTt
  exact strictTransform_eq_connectedComponentIn V T hT hadm.1
    (fun y hy => mem_maxLocus_iff_of_centresAvoid hF V hdom T hcan hT hc hcU hy) hc hcU

/-- **Some centre meets the smooth part, on any complex manifold**
(`EmbeddedFromResolution.not_centresAvoid_of_cosupp_eq_empty` without `[CompactSpace]`: blowup sequences are surjective,
`HironakaLocalPrincipalization.IsBlowupSequence.surjective`). -/
theorem not_centresAvoid_of_cosupp_eq_empty (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hTt : IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T)
    (hres : (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) T).cosupp = ∅) :
    ¬ CentresAvoid (regularOpen V) T := by
  intro hT
  obtain ⟨x, hx⟩ := V.regularLocus_nonempty
  obtain ⟨y, rfl⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence x
  have hyU : T.proj y ∈ regularOpen V := mem_regularOpen_of_regularAtDim hx
  have hy := (mem_cosupp_iff_of_centresAvoid V.isClosed_carrier hdom (regularOpen V) T hTt hT hyU).mpr
    (regularLocus_subset _ _ hx)
  rw [hres] at hy
  exact hy

/-- **Embedded resolution from a canonical resolution of `(X, X, ∅, 𝓘_V, 1)`, on any complex manifold**
(`EmbeddedFromResolution.exists_embedded_of_isCanonical` without `[CompactSpace]`): the prefix before the first centre meeting
the preimage of `X ∖ V_sing` has its exceptional image in `V_sing` and a strict transform of `V` regular of dimension `dim V` at
each of its points. -/
theorem exists_embedded_of_isCanonical (hF : EmbeddingFields n k inv) (V : ClosedIrreducibleAnalyticSubvariety n X)
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

end Identity

/-! ### Canonical segments along isomorphisms of towers, and the local canonical driver -/

section Canonical

variable {Λ : Type v} [LinearOrder Λ] {k : ℕ}
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **Canonical segments correspond along isomorphisms of towers** for every value function with the properties
`EmbeddingFields` (`ResolutionInvariantSegments.isCanonical_of_isTowerIso` for `inv`; property (6)): if `χ : T' → T` is an
isomorphism of towers over a biholomorphism `Φ` and `T` is a canonical segment of `𝔪`, then `T'` is one of `Φ^*𝔪`. -/
theorem isCanonical_of_isTowerIso (hF : EmbeddingFields n k inv) {X X' : CMfd.{u} n} {𝔪 : MarkedIdeal n X}
    (hdom : IsInvDomain k 𝔪) (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ T' T χ) :
    IsCanonical 𝔪 (inv 𝔪) T →
      IsCanonical (MarkedIdeal.pullback Φ 𝔪) (inv (MarkedIdeal.pullback Φ 𝔪)) T' := by
  induction hiso with
  | refl => exact fun _ => trivial
  | @step Y' Y Z' Z T' T χ hiso C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hcan
    obtain ⟨hT, hCc⟩ : IsCanonical 𝔪 (inv 𝔪) T ∧
        (C = ∅ ∨ C = maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
    have hTt := hF.isGeoTestTower_of_isCanonical hdom T hT
    show IsCanonical (MarkedIdeal.pullback Φ 𝔪) (inv (MarkedIdeal.pullback Φ 𝔪)) T' ∧
      (C' = ∅ ∨ C' = maxLocus (inv (MarkedIdeal.pullback Φ 𝔪) T')
        (geoTransformAlong (MarkedIdeal.pullback Φ 𝔪) T').cosupp)
    refine ⟨ih hT, ?_⟩
    subst hC
    rcases hCc with rfl | rfl
    · exact Or.inl preimage_empty
    · right
      rw [IsTowerIso.cosupp_geoTransformAlong Φ hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent
        hiso hTt]
      exact (ResolutionInvariantSegments.maxLocus_preimage_of_surjective χ.toEquiv.surjective
        (fun p hp => hF.towerIso Φ 𝔪 hdom T' T χ hiso hT p hp)).symm

end Canonical

section LocalDriver

variable {Λ : Type v} [LinearOrder Λ] [WellFoundedLT Λ] {k : ℕ}

/-- **Nothing of the cosupport over `K`, canonical form**: if no point of the cosupport along a canonical segment `T` lies over
the compact `K`, the restriction of `T` to the open complement of the image of the cosupport is a canonical segment resolving
`𝔪` over a neighbourhood of `K` (`HironakaLocalPrincipalization.exists_local_resolution_of_disjoint`, with canonicity from
`HironakaLocalPrincipalization.isCanonical_restrict`). -/
theorem exists_local_resolution_isCanonical_of_disjoint (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) {K : Set X} {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hcan : IsCanonical 𝔪 (R.inv 𝔪) T)
    (hne : ¬ ((geoTransformAlong 𝔪 T).cosupp ∩ T.proj ⁻¹' K).Nonempty) :
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y' : CMfd.{u} n) (T' : BlowupTower (CMfd.of (n := n) U) Y'),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
        (R.inv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)) T' ∧
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) T' := by
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq R
  have hTt := hF.isGeoTestTower_of_isCanonical hdom T hcan
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom T hTt
  have hSc : IsClosed (geoTransformAlong 𝔪 T).cosupp :=
    GiraudAlong.isClosed_cosupport_along hdomT.isWellFormed.isCoherent hdomT.isWellFormed.isClosedSubmanifold_N _
  let O : Opens X := ⟨(T.proj '' (geoTransformAlong 𝔪 T).cosupp)ᶜ,
    ((HironakaLocalPrincipalization.isProperMap_proj T).isClosedMap _ hSc).isOpen_compl⟩
  have hKO : K ⊆ O := by
    rintro x hx ⟨y, hyS, rfl⟩
    exact hne ⟨y, hyS, hx⟩
  refine ⟨O, hKO, _, restrict O T, HironakaLocalPrincipalization.isCanonical_restrict hF hdom O T hcan,
    MarkedIdealRestrictOpen.isGeoTestTower_restrict O hdom.isWellFormed.isClosedSubmanifold_N
      hdom.isWellFormed.isCoherent T hTt, ?_⟩
  rw [ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N
    hdom.isWellFormed.isCoherent O T hTt]
  refine eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  exact p.2 ⟨p, hp, rfl⟩

/-- **From an open set of an open set back to an open set of `X`, canonical form**
(`HironakaLocalPrincipalization.exists_resolution_of_nested` with canonicity transported along the tower isomorphism,
`isCanonical_of_isTowerIso`). -/
theorem exists_canonical_resolution_of_nested (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) {K : Set X}
    (O : Opens X) (hKO : K ⊆ O) (U₁ : Opens (CMfd.of (n := n) O)) (hKU₁ : (Subtype.val : O → X) ⁻¹' K ⊆ U₁)
    {Y₁ : CMfd.{u} n} (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁)
    (hcan₁ : IsCanonical (MarkedIdeal.pullback (Subtype.val : U₁ → O) (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪))
      (R.inv (MarkedIdeal.pullback (Subtype.val : U₁ → O) (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪))) T₁)
    (hres₁ : IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U₁ → O)
      (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪)) T₁) :
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y' : CMfd.{u} n) (T' : BlowupTower (CMfd.of (n := n) U) Y'),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
        (R.inv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)) T' ∧
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) T' := by
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq R
  obtain ⟨U, hUdef⟩ : ∃ U : Opens X, (U : Set X) = (Subtype.val : O → X) '' (U₁ : Set O) :=
    ⟨⟨_, O.isOpen.isOpenMap_subtype_val _ U₁.isOpen⟩, rfl⟩
  have hBD : ∀ q : O, q ∈ U₁ ↔ (q : X) ∈ U := fun q => by
    rw [← SetLike.mem_coe (x := (q : X)), hUdef]
    exact ⟨fun hq => ⟨q, hq, rfl⟩, fun ⟨q', hq', heq⟩ => (Subtype.ext heq : q' = q) ▸ hq'⟩
  have hDA : U ≤ O := by
    intro x hx
    rw [← SetLike.mem_coe, hUdef] at hx
    obtain ⟨q, -, rfl⟩ := hx
    exact q.2
  have hKU : K ⊆ U := fun x hx => (hBD ⟨x, hKO hx⟩).mp (hKU₁ hx)
  have hdomO := InvDomainTowerAlong.isInvDomain_pullback_val O hdom
  have hdom₁ := InvDomainTowerAlong.isInvDomain_pullback_val U₁ hdomO
  have hiso := BlowupTowerIsomorphism.transport_isTowerIso (MaxLocusLocal.nestedDiffeo (n := n) O U₁ U hBD hDA).symm T₁
  have hres := (BlowupTowerIsomorphism.IsTowerIso.isGeoResolution_iff
    (MaxLocusLocal.nestedDiffeo (n := n) O U₁ U hBD hDA).symm
    hdom₁.isWellFormed.isClosedSubmanifold_N hdom₁.isWellFormed.isCoherent hiso).mpr hres₁
  have hcan := isCanonical_of_isTowerIso hF hdom₁ (MaxLocusLocal.nestedDiffeo (n := n) O U₁ U hBD hDA).symm hiso hcan₁
  rw [HironakaLocalPrincipalization.pullback_symm_nestedDiffeo hdom.isWellFormed.isCoherent O U₁ U hBD hDA]
    at hres hcan
  exact ⟨U, hKU, _, _, hcan, hres⟩

/-- **The local canonical driver with a canonical output, inductive form**: along a canonical segment `T` of `𝔪` all of whose
values over the compact `K` are `< μ`, the marked ideal is resolved over an open neighbourhood `U` of `K` by a *canonical
segment* of `𝔪|_U` (`HironakaLocalPrincipalization.exists_local_resolution_of_lt`, keeping track of canonicity). -/
theorem exists_local_resolution_isCanonical_of_lt (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    (μ : WithTop Λ) :
    ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ (K : Set X), IsCompact K →
      ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (R.inv 𝔪) T →
      (∀ z ∈ (geoTransformAlong 𝔪 T).cosupp, T.proj z ∈ K → ((R.inv 𝔪 T z : Λ) : WithTop Λ) < μ) →
      ∃ U : Opens X, K ⊆ U ∧ ∃ (Y' : CMfd.{u} n) (T' : BlowupTower (CMfd.of (n := n) U) Y'),
        IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
          (R.inv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)) T' ∧
        IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) T' := by
  induction μ using WellFoundedLT.induction with
  | _ μ ih => ?_
  intro X 𝔪 hdom K hK Y T hcan hlt
  by_cases hne : ((geoTransformAlong 𝔪 T).cosupp ∩ T.proj ⁻¹' K).Nonempty
  · obtain ⟨z₀, hz₀, O, hKO, Y₁, T₁, hcan₁, hlt₁⟩ :=
      HironakaLocalPrincipalization.exists_shrink_step R hdom hK T hcan hne
    have hK₁ : IsCompact ((Subtype.val : O → X) ⁻¹' K) :=
      (Topology.IsInducing.subtypeVal.isCompact_preimage_iff (fun x hx => ⟨⟨x, hKO hx⟩, rfl⟩)).mpr hK
    obtain ⟨U₁, hKU₁, Y₂, T₂, hcan₂, hres₂⟩ := ih _ (hlt z₀ hz₀.1 hz₀.2)
      (MarkedIdeal.pullback (Subtype.val : O → X) 𝔪) (InvDomainTowerAlong.isInvDomain_pullback_val O hdom)
      ((Subtype.val : O → X) ⁻¹' K) hK₁ T₁ hcan₁ fun z hz hzK => WithTop.coe_lt_coe.mpr (hlt₁ z hz hzK)
    exact exists_canonical_resolution_of_nested R hdom O hKO U₁ hKU₁ T₂ hcan₂ hres₂
  · exact exists_local_resolution_isCanonical_of_disjoint R hdom T hcan hne

/-- **The local canonical driver, with a canonical output** (`hir:embedded-resolution-local`, first part): let `R` be a
resolution invariant in dimension `≤ k` with well-ordered values (e.g. `CanonicalCentres.canonicalInvariant`), `X` any complex
manifold, `𝔪` a marked ideal of the domain and `K ⊆ X` compact.  There are an open neighbourhood `U` of `K` and a canonical
segment of `𝔪|_U` (for the invariant `R`) which is a multiple test blow-up with empty final cosupport. -/
theorem exists_local_resolution_isCanonical (R : ResolutionInvariantSeq.ResolutionInvariant.{u, v} n k Λ)
    {X : CMfd.{u} n} {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
        (R.inv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)) T ∧
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) T :=
  exists_local_resolution_isCanonical_of_lt R ⊤ 𝔪 hdom K hK .refl trivial fun _ _ _ => WithTop.coe_lt_top _

end LocalDriver

/-! ### The identity-principle step for an analytic set that need not be irreducible -/

section General

variable {X : CMfd.{u} n}

/-- **The regular points of dimension `dim V` are dense in `V`** (irreducibility: `V` is the closure of the component of its
regular locus through a regular point, `StrictTransformSubvariety.eq_closure_component`). -/
theorem subset_closure_inter_regularOpen {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (V : ClosedIrreducibleAnalyticSubvariety n M) :
    V.carrier ⊆ closure (V.carrier ∩ regularOpen V) := by
  obtain ⟨c, -, hc⟩ := V.exists_regular_point
  have hV := StrictTransformSubvariety.eq_closure_component V.irreducible_carrier hc
  have hsub : component (n := n) V.carrier c ⊆ V.carrier ∩ regularOpen V := fun y hy =>
    ⟨component_subset _ _ hy, mem_regularOpen_of_regularAtDim (regularAtDim_of_mem_component hc hy)⟩
  intro x hx
  rw [hV] at hx
  exact closure_mono hsub hx

/-- **The identity-principle step for an analytic set, without irreducibility or compactness.**  Let `W` be an analytic
subset of any complex manifold `X` and `O ⊆ X` open such that `W` is regular of dimension `d` at each point of `W ∩ O` and
`W ⊆ closure (W ∩ O)`.  Let `T` be a tower whose centres miss the preimages of `O`, and `C` a closed submanifold of the last
stage which over `O` is the preimage of `W`.  Then the strict transform `S` of `W` lies in `C`, agrees with `C` near each of its
points, and is regular of dimension `d` at each of its points.

Proof: `S` is the closure of `C ∩ T⁻¹ O` (a point of `T⁻¹ W` off the exceptional locus is a limit of points over `W ∩ O`, the
projection being open there), and `S` is analytic (`isComplexAnalyticSubset_strictTransform_proj`).  For `x ∈ S` the connected
component of `C` through `x` meets `T⁻¹ O`, so it lies in `S` (identity theorem, `RegularLocusComponent.component_subset_of_isOpen`),
and it is a neighbourhood of `x` in `C`; its dimension is `d`, read off at a point over `O`. -/
theorem strictTransform_of_centresAvoid {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) (O : Opens X) {d : ℕ}
    (hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d) (hdense : W ⊆ closure (W ∩ O))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : CentresAvoid O T) {C : Set Y} (hC : IsClosedSubmanifold n C)
    (hCV : ∀ y : Y, T.proj y ∈ O → (y ∈ C ↔ T.proj y ∈ W)) :
    strictTransform n T.proj W ⊆ C ∧
      (∀ x ∈ strictTransform n T.proj W, ∀ᶠ y in 𝓝 x, y ∈ strictTransform n T.proj W ↔ y ∈ C) ∧
      ∀ x ∈ strictTransform n T.proj W, RegularAtDim (n := n) (strictTransform n T.proj W) x d := by
  set S := strictTransform n T.proj W with hSdef
  set Oy : Set Y := T.proj ⁻¹' (O : Set X) with hOydef
  have hOy : IsOpen Oy := O.isOpen.preimage T.contMDiff_proj.continuous
  have hSO : ∀ y ∈ Oy, y ∈ S ↔ T.proj y ∈ W := fun y hy =>
    mem_strictTransform_iff_of_centresAvoid O T hT hWa.isClosed hy
  have hCS : ∀ y ∈ Oy, y ∈ C ↔ y ∈ S := fun y hy => (hCV y hy).trans (hSO y hy).symm
  have hSOC : S ∩ Oy = C ∩ Oy := by
    ext y
    exact ⟨fun h => ⟨(hCS y h.2).mpr h.1, h.2⟩, fun h => ⟨(hCS y h.2).mp h.1, h.2⟩⟩
  -- `S` is the closure of its part over `O`, which is `C ∩ T⁻¹ O`
  have hScl : S ⊆ closure (C ∩ Oy) := by
    refine closure_minimal ?_ isClosed_closure
    rintro y ⟨hyW, hyE⟩
    rw [mem_closure_iff_nhds]
    intro t ht
    have ht' : t ∩ (exceptionalLocus n T.proj)ᶜ ∈ 𝓝 y :=
      inter_mem ht ((StrictTransformComposition.isOpen_compl_exceptionalLocus T.contMDiff_proj).mem_nhds hyE)
    have himg : T.proj '' (t ∩ (exceptionalLocus n T.proj)ᶜ) ∈ 𝓝 (T.proj y) := by
      rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus T.contMDiff_proj hyE]
      exact image_mem_map ht'
    obtain ⟨_, ⟨v, ⟨hvt, -⟩, rfl⟩, hvW, hvO⟩ := mem_closure_iff_nhds.mp (hdense hyW) _ himg
    exact ⟨v, hvt, (hCV v hvO).mpr hvW, hvO⟩
  have hSC : S ⊆ C := hScl.trans (closure_minimal inter_subset_left hC.1)
  have hSa : IsComplexAnalyticSubset (n := n) S := isComplexAnalyticSubset_strictTransform_proj hWa T
  -- near each of its points `S` is a component of `C`, of dimension `d`
  have key : ∀ x ∈ S, ∃ W' : Set Y, IsOpen W' ∧ x ∈ W' ∧ C ∩ W' ⊆ S ∧ RegularAtDim (n := n) C x d := by
    intro x hx
    obtain ⟨j, hj⟩ := hC.2 x (hSC hx)
    obtain ⟨W', hW', hxW', hW'K⟩ := exists_open_inter_subset_component hj (mem_component_self hj)
    obtain ⟨c, hcW', hcC, hcO⟩ := mem_closure_iff.mp (hScl hx) W' hW' hxW'
    have hcK : c ∈ component (n := n) C x := hW'K ⟨hcC, hcW'⟩
    have hKS : component (n := n) C x ⊆ S :=
      component_subset_of_isOpen hSa hOy ⟨c, hcO, hcK⟩ fun y hy => (hCS y hy.1).mp (component_subset C x hy.2)
    have hcS : c ∈ S := (hCS c hcO).mp hcC
    have hSc : RegularAtDim (n := n) S c d :=
      RegularAtDimTransport.regularAtDim_of_preimage T.contMDiff_proj
        (notMem_exceptionalLocus_of_centresAvoid O T hT c hcO) hOy hcO hSO (hreg _ ((hSO c hcO).mp hcS) hcO)
    have hCc : RegularAtDim (n := n) C c d := RegularPointDimension.regularAtDim_of_inter_eq hOy hcO hSOC hSc
    have h1 : component (n := n) C x = component (n := n) C c := connectedComponentIn_eq hcK
    have hxc : x ∈ component (n := n) C c := by
      rw [← h1]
      exact mem_component_self hj
    exact ⟨W', hW', hxW', fun y hy => hKS (hW'K hy), regularAtDim_of_mem_component hCc hxc⟩
  refine ⟨hSC, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨W', hW', hxW', hW'S, -⟩ := key x hx
    filter_upwards [hW'.mem_nhds hxW'] with y hy
    exact ⟨fun h => hSC h, fun h => hW'S ⟨h, hy⟩⟩
  · obtain ⟨W', hW', hxW', hW'S, hCx⟩ := key x hx
    refine RegularPointDimension.regularAtDim_of_inter_eq hW' hxW' ?_ hCx
    ext y
    exact ⟨fun h => ⟨hW'S h, h.2⟩, fun h => ⟨hSC h.1, h.2⟩⟩

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The maximum locus over an open set on which `W` is smooth of pure dimension**
(`EmbeddedFromResolution.mem_maxLocus_iff_of_centresAvoid` for any closed `W` and open `O` with `W ∩ O` regular of dimension `d`
at each of its points, in place of a subvariety and `X ∖ V_sing`): for a canonical segment `T` of `(X, X, ∅, 𝓘_W, 1)` whose
centres miss the preimages of `O`, once the maximum locus meets the preimage of `O` it contains, over `O`, exactly the preimage
of `W`. -/
theorem mem_maxLocus_iff_of_centresAvoid_of_pureDim (hF : EmbeddingFields n k inv) {W : Set X} (hW : IsClosed W)
    (O : Opens X) {d : ℕ} (hpure : ∀ x : O, (x : X) ∈ W → RegularAtDim (n := n) W x d)
    (hdom : IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
      (inv (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)) T)
    (hT : CentresAvoid O T) {c : Y}
    (hc : c ∈ maxLocus (inv (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
      (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).cosupp)
    (hcO : T.proj c ∈ O) {y : Y} (hy : T.proj y ∈ O) :
    y ∈ maxLocus (inv (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).cosupp ↔
      T.proj y ∈ W := by
  have hTt := hF.isGeoTestTower_of_isCanonical hdom T hcan
  have hcos := mem_cosupp_iff_of_centresAvoid hW hdom O T hTt hT hy
  refine ⟨fun h => hcos.mp h.1, fun h => ?_⟩
  have hys := hcos.mpr h
  have hpure' : ∀ x ∈ (Subtype.val : O → X) ⁻¹' W,
      RegularAtDim (n := n) ((Subtype.val : O → X) ⁻¹' W) x d := fun x hx =>
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hpure x hx)
  have hZ : IsClosedSubmanifold n ((Subtype.val : O → X) ⁻¹' W) :=
    ⟨hW.preimage continuous_subtype_val, fun x hx => ⟨d, hpure' x hx⟩⟩
  have heq := hF.inv_eq_over_open_of_isEmptyTower_of_pureDim hdom O hZ hpure' T hcan
    ((isEmptyTower_restrict_iff O T).mpr hT) (p := ⟨c, hcO⟩) (p' := ⟨y, hy⟩) hc.1 hys
  refine ⟨hys, fun y' hy' => ?_⟩
  rw [show inv (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T y =
      inv (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T c from heq]
  exact hc.2 y' hy'

/-- **The transformed divisor of a multiple test blow-up whose centres miss an open set** (for a marked ideal of the domain with
empty divisor): it has simple normal crossings, its union is the support of the exceptional divisor of the tower, which contains
the exceptional locus and lies over the complement of the open set. -/
theorem exceptionalDivisor_facts_of_centresAvoid {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪) (hE : 𝔪.E = [])
    (O : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hTt : IsGeoTestTower 𝔪 T) (hT : CentresAvoid O T) :
    IsSNCDivisor n (geoTransformAlong 𝔪 T).E ∧
      (BlowupTowerTransforms.exceptionalDivisor T).support = ⋃ H ∈ (geoTransformAlong 𝔪 T).E, H ∧
      exceptionalLocus n T.proj ⊆ (BlowupTowerTransforms.exceptionalDivisor T).support ∧
      (BlowupTowerTransforms.exceptionalDivisor T).support ⊆ T.proj ⁻¹' (O : Set X)ᶜ :=
  ⟨(InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom T hTt).isWellFormed.isSNCDivisor,
    HironakaPrincipalization.support_exceptionalDivisor_eq_biUnion 𝔪 hE T,
    HironakaPrincipalization.exceptionalLocus_subset_support T,
    HironakaEmbeddedResolution.support_exceptionalDivisor_subset_of_centresAvoid O T hT⟩

end General

/-! ### Local embedded resolution -/

section Local

/-- **Local embedded resolution, tower form** (`dim V < n`, `𝓘_V` coherent; `X` any complex manifold, `K ⊆ X` compact): there
are an open neighbourhood `U` of `K` and a multiple test blow-up `T` of `(U, U, ∅, 𝓘_{V ∩ U}, 1)` whose strict transform of
`V ∩ U` is a closed submanifold, regular of dimension `dim V` at each of its points, whose transformed divisor `E` has simple
normal crossings with union the support of the exceptional divisor `E_T`, which contains the exceptional locus of `T` and lies
over `V_sing`, and such that the strict transform has only normal crossings with `E`. -/
theorem exists_tower_embeddedResolution_local {X : CMfd.{u} n} (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : V.dim < n) (hcoh : (vanishingIdeal (n := n) V.carrier).IsCoherent) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' V.carrier), 1⟩ :
        MarkedIdeal n (CMfd.of (n := n) U)) T ∧
      IsClosedSubmanifold n (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' V.carrier)) ∧
      (∀ x ∈ strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' V.carrier),
        RegularAtDim (n := n) (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' V.carrier)) x V.dim) ∧
      IsSNCDivisor n (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' V.carrier), 1⟩ :
        MarkedIdeal n (CMfd.of (n := n) U)) T).E ∧
      (BlowupTowerTransforms.exceptionalDivisor T).support =
        ⋃ H ∈ (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' V.carrier), 1⟩ :
          MarkedIdeal n (CMfd.of (n := n) U)) T).E, H ∧
      exceptionalLocus n T.proj ⊆ (BlowupTowerTransforms.exceptionalDivisor T).support ∧
      (BlowupTowerTransforms.exceptionalDivisor T).support ⊆
        T.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' singularLocus V) ∧
      HasNormalCrossings n (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' V.carrier))
        (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' V.carrier), 1⟩ :
          MarkedIdeal n (CMfd.of (n := n) U)) T).E := by
  have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) :=
    isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV hcoh
  have hF := HironakaFromSeqInvariant.embeddingFields_of_seq (CanonicalCentres.canonicalInvariant.{u} n)
  obtain ⟨U, hKU, Y₀, T₀, hcan₀, hres₀⟩ :=
    exists_local_resolution_isCanonical (CanonicalCentres.canonicalInvariant.{u} n) hdom hK
  have hdomU := InvDomainTowerAlong.isInvDomain_pullback_val U hdom
  rw [SmoothCentreInvariant.pullback_val_smoothCentreMarked U V.carrier] at hcan₀ hres₀ hdomU
  refine ⟨U, hKU, ?_⟩
  -- the data on `U`
  set W : Set (CMfd.of (n := n) U) := (Subtype.val : U → X) ⁻¹' V.carrier with hWdef
  let O' : Opens (CMfd.of (n := n) U) :=
    ⟨(Subtype.val : U → X) ⁻¹' (regularOpen V : Set X), (regularOpen V).isOpen.preimage continuous_subtype_val⟩
  have hO'c : ∀ x : CMfd.of (n := n) U, x ∉ O' ↔ (x : X) ∈ singularLocus V := fun x =>
    show ¬ ((x : X) ∉ singularLocus V) ↔ _ from not_not
  have hWa : IsComplexAnalyticSubset (n := n) W :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val V.analytic
  have hreg : ∀ x ∈ W, x ∈ O' → RegularAtDim (n := n) W x V.dim := fun x hxW hxO =>
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (regularAtDim_of_mem_regularOpen hxW hxO)
  have hdense : W ⊆ closure (W ∩ O') := by
    intro x hx
    have h := subset_closure_inter_regularOpen V hx
    have h2 := (U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage continuous_subtype_val
      (V.carrier ∩ regularOpen V)
    exact (Set.ext_iff.mp h2 x).mp h
  have hTt₀ := hres₀.1
  have hsupp : ∀ {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) U) Y), CentresAvoid O' T →
      (BlowupTowerTransforms.exceptionalDivisor T).support ⊆
        T.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' singularLocus V) := fun T hT z hz =>
    (hO'c _).mp (HironakaEmbeddedResolution.support_exceptionalDivisor_subset_of_centresAvoid O' T hT hz)
  by_cases hA : CentresAvoid O' T₀
  · -- every centre misses the smooth part: then `V ∩ U` is empty
    have hWO : ∀ x ∈ W, x ∉ O' := fun x hxW hxO => by
      obtain ⟨y, rfl⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective T₀.isBlowupSequence x
      have hy := (mem_cosupp_iff_of_centresAvoid hWa.isClosed hdomU O' T₀ hTt₀ hA hxO).mpr hxW
      rw [hres₀.2] at hy
      exact hy
    have hW0 : W = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have h := hdense hx
      rw [show W ∩ (O' : Set (CMfd.of (n := n) U)) = ∅ from
        eq_empty_iff_forall_notMem.mpr fun y hy => hWO y hy.1 hy.2, closure_empty] at h
      exact h
    have hS0 : strictTransform n T₀.proj W = ∅ := by
      rw [hW0]
      simp [strictTransform]
    obtain ⟨hsnc, hsuppE, hexc, -⟩ :=
      exceptionalDivisor_facts_of_centresAvoid hdomU rfl O' T₀ hTt₀ hA
    refine ⟨Y₀, T₀, hTt₀, ?_, ?_, hsnc, hsuppE, hexc, hsupp T₀ hA, ?_⟩
    · rw [hS0]
      exact ⟨isClosed_empty, fun x hx => absurd hx (notMem_empty x)⟩
    · rw [hS0]
      exact fun x hx => absurd hx (notMem_empty x)
    · rw [hS0]
      exact fun x hx => absurd hx (notMem_empty x)
  · -- the first centre meeting the smooth part
    obtain ⟨Y', T', -, -, h1, h2, c, hc, hcU⟩ := exists_first_centre _ _ O' T₀ hcan₀ hA
    have hTt' := hF.isGeoTestTower_of_isCanonical hdomU T' h1
    have hadm := hF.isAdmissibleCentre_maxLocus hdomU T' h1 hTt'
    have hCV := fun y (hy : T'.proj y ∈ O') =>
      mem_maxLocus_iff_of_centresAvoid_of_pureDim hF hWa.isClosed O' (d := V.dim)
        (fun x hx => hreg x hx x.2) hdomU T' h1 h2 hc hcU hy
    obtain ⟨hSC, hev, hreg'⟩ := strictTransform_of_centresAvoid hWa O' hreg hdense T' h2 hadm.1 hCV
    obtain ⟨hsnc, hsuppE, hexc, -⟩ :=
      exceptionalDivisor_facts_of_centresAvoid hdomU rfl O' T' hTt' h2
    refine ⟨Y', T', hTt', ⟨isClosed_closure, fun x hx => ⟨V.dim, hreg' x hx⟩⟩, hreg', hsnc, hsuppE, hexc,
      hsupp T' h2, ?_⟩
    exact CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually fun x hx =>
      ⟨_, hSC hx, hev x hx, hadm.2.2⟩

/-- **Local embedded resolution** (Hironaka; `hir:embedded-resolution-local`): let `X` be a complex manifold, not necessarily
compact, `V ⊆ X` a closed irreducible analytic subvariety and `K ⊆ X` compact.  There are an open neighbourhood `U` of `K`, a
finite sequence of blowups with smooth centres `f : U' → U` and a divisor `E` on `U'` with simple normal crossings such that the
exceptional locus of `f` lies in `⋃ E`, `⋃ E` lies over `V_sing`, `f` is an isomorphism over `U \ V_sing`, and the strict
transform of `V ∩ U` is a closed submanifold of `U'`, of dimension `dim V` at each of its points, with only normal crossings
with `E`. -/
theorem exists_embeddedResolution_local {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (V : ClosedIrreducibleAnalyticSubvariety n X) {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧
    ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
      (_ : IsComplexManifold n U') (f : U' → U) (_ : IsBlowupSequence n U U' f) (E : List (Set U')),
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) ⊆ f ⁻¹' ((Subtype.val : U → X) ⁻¹' singularLocus V) ∧
      IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' singularLocus V)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) x V.dim) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : U → X) ⁻¹' V.carrier)) E := by
  rcases V.dim_le.lt_or_eq with h | h
  · obtain ⟨U, hKU, Y, T, -, hS, hreg, hsnc, hsupp, hexc, hsing, hnc⟩ :=
      exists_tower_embeddedResolution_local (X := CMfd.of (n := n) X) V h
        (CartanIrreducible.cartanCoherence V.carrier V.irreducible_carrier.analytic) hK
    refine ⟨U, hKU, Y, inferInstance, inferInstance, inferInstance, T.proj, T.isBlowupSequence, _, hsnc, ?_, ?_, ?_,
      hS, hreg, hnc⟩
    · rw [← hsupp]
      exact hexc
    · rw [← hsupp]
      exact hsing
    · refine HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
        T.isBlowupSequence ?_
      rintro x ⟨z, hz, rfl⟩
      exact hsing (hexc hz)
  · -- `dim V = n`: `V` is a connected component of `X`, and the identity over `U = X` works
    have hV := isClosedConnectedSubmanifold_of_dim_eq V h
    set W : Set (⊤ : Opens X) := (Subtype.val : (⊤ : Opens X) → X) ⁻¹' V.carrier with hWdef
    have hst : strictTransform n (id : (⊤ : Opens X) → (⊤ : Opens X)) W = W := by
      simp [strictTransform, exceptionalLocus_id, (V.isClosed_carrier.preimage continuous_subtype_val).closure_eq, W]
    have hregW : ∀ x ∈ W, RegularAtDim (n := n) W x V.dim := fun x hx =>
      AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (by rw [h]; exact hV.2.2 _ hx)
    have hWsub : IsClosedSubmanifold n W :=
      ⟨V.isClosed_carrier.preimage continuous_subtype_val, fun x hx => ⟨V.dim, hregW x hx⟩⟩
    refine ⟨⊤, fun x _ => trivial, _, inferInstance, inferInstance, inferInstance, id, IsBlowupSequence.refl, [],
      isSNCDivisor_nil, ?_, ?_,
      HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset IsBlowupSequence.refl
        (by simp [exceptionalLocus_id]), ?_, ?_, ?_⟩
    · simp [exceptionalLocus_id]
    · simp
    · rw [hst]
      exact hWsub
    · rw [hst]
      exact hregW
    · rw [hst]
      exact hasNormalCrossings_nil_of_isClosedSubmanifold hWsub

end Local

end

end Hironaka.HironakaEmbeddedResolutionLocal
