import Hironaka.Blowup.ExceptionalImageAnalytic
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Analytic.ComponentComplementConnected
import Hironaka.Analytic.AnalyticIrreducibleComponents

set_option autoImplicit false

/-!
# The strict transform of a subvariety under one blowup

Source: CT22, Section 4; Griffiths--Harris, Ch. 1 §4; blueprint
`ana:strict-transform-subvariety`.

Let `g : Z → Y` be the blowup of a compact complex manifold along a smooth centre, `T` the
image of its exceptional locus, and `W ⊆ Y` a closed irreducible analytic subvariety with
`W ⊄ T`.  Then the strict transform `W̃ = closure (g⁻¹ W \ Exc g)` is a closed irreducible
analytic subvariety with `dim W̃ = dim W`.

* Analyticity: `Exc g = g⁻¹ T` (`ExceptionalFibres`), so `W̃ = closure (g⁻¹ W \ g⁻¹ T)`
  is the closure of a difference of analytic sets.
* Dimension: pick a regular point `c ∉ T` of `W` of dimension `dim W`; its unique preimage
  `c̃` is not exceptional, `W̃` agrees with `g⁻¹ W` off `Exc g`, and regularity transports
  across the local biholomorphism.
* Irreducibility: `W` is the closure of the connected component `K` of its regular locus
  through `c` (`eq_closure_component`); `K \ T` is connected and dense in `K`
  (`ComponentComplementConnected`); since `g` restricted to `Z \ Exc g` is an injective
  open map, `g⁻¹ (K \ T)` is a connected set of regular points of `W̃`, hence lies in the
  component `K̃` through `c̃`, and it is dense in `W̃`.  So `W̃ = closure K̃` is irreducible.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StrictTransformSubvariety

open Hironaka.BlowupSequences RegularLocusComponent

noncomputable section

section Irreducible

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- An irreducible analytic set is the closure of the component of its regular locus through
any regular point. -/
theorem eq_closure_component {A : Set M} (hA : IsComplexAnalyticallyIrreducible (n := n) A)
    {c : M} {k : ℕ} (hc : RegularAtDim (n := n) A c k) :
    A = closure (component (n := n) A c) := by
  have hK := isComplexAnalyticSubset_closure_component hA.analytic hc
  have hS := ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff hA.analytic hK
  have hKA : closure (component (n := n) A c) ⊆ A :=
    closure_minimal (component_subset (n := n) A c) hA.analytic.isClosed
  have hSA : closure (A \ closure (component (n := n) A c)) ⊆ A :=
    closure_minimal sdiff_subset hA.analytic.isClosed
  have hunion : A = closure (component (n := n) A c) ∪
      closure (A \ closure (component (n := n) A c)) := by
    refine Subset.antisymm (fun x hx => ?_) (union_subset hKA hSA)
    by_cases hxK : x ∈ closure (component (n := n) A c)
    · exact Or.inl hxK
    · exact Or.inr (subset_closure ⟨hx, hxK⟩)
  rcases hA.eq_left_or_eq_right hK hS hKA hSA hunion with h | h
  · exact h
  · exfalso
    obtain ⟨W, hW, hcW, hWK⟩ := exists_open_inter_subset_component hc (mem_component_self hc)
    have hc' : c ∈ closure (A \ closure (component (n := n) A c)) := h ▸ hc.2.1
    obtain ⟨x, hxW, hxA, hxK⟩ := mem_closure_iff.mp hc' W hW hcW
    exact hxK (subset_closure (hWK ⟨hxA, hxW⟩))

end Irreducible

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- **The strict transform under one blowup is a subvariety of the same dimension.** -/
theorem exists_strictTransform_subvariety_of_isBlowupAlong [CompactSpace Y]
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g) :
    ∃ Wt : ClosedIrreducibleAnalyticSubvariety n Z,
      Wt.carrier = strictTransform n g W.carrier ∧ Wt.dim = W.dim := by
  classical
  set T := g '' exceptionalLocus n g with hTdef
  have hT : IsComplexAnalyticSubset (n := n) T :=
    ExceptionalImageAnalytic.isComplexAnalyticSubset_image_exceptionalLocus hg
  have hTc : IsClosed T := ExceptionalFibres.isClosed_image_exceptionalLocus hg
  have hExc : g ⁻¹' T = exceptionalLocus n g := ExceptionalFibres.preimage_image_exceptionalLocus hg
  have hgc : Continuous g := hg.contMDiff.continuous
  set Ω : Set Z := (exceptionalLocus n g)ᶜ with hΩdef
  have hΩ : IsOpen Ω := StrictTransformComposition.isOpen_compl_exceptionalLocus hg.contMDiff
  set Wt : Set Z := strictTransform n g W.carrier with hWtdef
  -- analyticity
  have hWtA : IsComplexAnalyticSubset (n := n) Wt := by
    have h := ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg.contMDiff W.analytic)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg.contMDiff hT)
    rwa [hExc] at h
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
  obtain ⟨ct, hct⟩ := StrictTransformComposition.surjective_of_isBlowupAlong hg c
  have hctΩ : ct ∈ Ω := fun h => hcT ⟨ct, h, hct⟩
  have hreg : ∀ u ∈ Ω, RegularAtDim (n := n) W.carrier (g u) W.dim →
      RegularAtDim (n := n) Wt u W.dim := fun u hu hr =>
    RegularAtDimTransport.regularAtDim_of_preimage hg.contMDiff hu hΩ hu hWtΩ hr
  have hctreg : RegularAtDim (n := n) Wt ct W.dim := hreg ct hctΩ (hct ▸ hck)
  -- the component through `c` and its part off `T`
  set K := component (n := n) W.carrier c with hKdef
  have hWK : W.carrier = closure K := eq_closure_component W.irreducible_carrier hck
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
    obtain ⟨z, rfl⟩ := StrictTransformComposition.surjective_of_isBlowupAlong hg x
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

end

end Hironaka.StrictTransformSubvariety
