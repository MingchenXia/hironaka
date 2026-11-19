import Hironaka.Analytic.Unibranch.HironakaG10FrChartIV9
import Hironaka.Analytic.Unibranch.HironakaG10GfWindow
import Hironaka.Analytic.Unibranch.HironakaG10RkNativeRank

/-!
# Frisch's Theorem (IV,9) for reduced complex spaces (ASM step 3b)

J. Frisch, Invent. Math. 4 (1967), Th. (IV,9) (p. 133), native form, for the family over the reduced structure of
an analytic `A ⊆ X` with the FIBRE-PRODUCT source `𝒪_Y ⧸ I_A 𝒪_Y` (auditor advisory A1, `G10AU/AUDIT-chain.md`):
for `f : Y ⟶ X` and `A ⊆ X` analytic, the source non-flat locus
`relNonflatSource f A = {y | f y ∈ A ∧ 𝒪_{Y,y} ⧸ I_A not flat over 𝒪_{X,f y} ⧸ I_A}` is analytic in `Y`
(**`isAnalyticSubset_relNonflatSource`**), and `relNonflat f A = f (relNonflatSource f A)`
(`relNonflat_eq_image`).

Proof: at `y`, lane G10GF's window chart (`HironakaG10GfWindow.exists_window_chart_vanishing`) reads native
flatness at the points of a source chart `eW` near `y` as chart flatness of a graph row `F` over the base ideal of
the trace `T` of `A` in a base chart `eX`, at the chart points `(ψ z, z)` (`ψ` an ambient lift of `f`,
`LocalEmbedding.exists_contMDiff_factor`); the chart non-flat set is analytic near `(ψ z₀, z₀)`
(`HironakaG10FrChartIV9.exists_opens_chartNonflat`), and its preimage under the graph map `z ↦ (ψ z, z)` is the
trace of `relNonflatSource f A` on an open of the source chart (`isAnalyticSubset_of_forall_opens_ambient`).

Explicit hypotheses as in step 3a: `hGF` (Frisch Th. (II,1), lane G10GN) and `h1` (item 1 for relatively exact
starts, lanes G10LF/G10GF). No named `Prop`.

Lane G10R3 (continuing lane G10FR), run 0081. Blueprint: `hironaka-g10fr-native-iv9.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10FrNativeIV9

open Hironaka Hironaka OkaRelationSheaf
  HironakaReducedComplexAnalyticSpaces
  HironakaG10HirFlatQuotient HironakaG10LocFibreOpen HironakaG10LocRelative
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily
  Hironaka.Analytic.Unibranch.HironakaG10FrRouteG Hironaka.Analytic.Unibranch.HironakaG10FrChartIV9
  Hironaka.Analytic.Unibranch.HironakaG10GfModStart Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
  Hironaka.Analytic.Unibranch.HironakaG10RkNativeRank

noncomputable section

/-! ### A pointwise criterion for native analyticity -/

section Criterion

variable {Y : SourceReducedComplexSpace}

/-- **Pointwise criterion for native analyticity**: it suffices that every point lies in a local embedding
which, on an open `W` of the ambient space around the point, cuts the set out as an analytic subset of `W`. -/
theorem isAnalyticSubset_of_forall_opens_ambient {N : Set Y.obj.left}
    (h : ∀ y, ∃ (e : LocalEmbedding Y) (c : e.carrier), e.toPoint c = y ∧ ∃ W : Opens e.ambient,
      c.val ∈ W ∧ ∃ A'' : Set W, IsComplexAnalyticSubset (n := e.dim) A'' ∧
        ∀ (z : e.carrier) (hz : z.val ∈ W), e.toPoint z ∈ N ↔ (⟨z.val, hz⟩ : W) ∈ A'') :
    Y.IsAnalyticSubset N := by
  intro y
  obtain ⟨e, c, hcy, W, hcW, A'', hA'', hiff⟩ := h y
  let O : Opens (ComplexModel e.dim) :=
    ⟨Subtype.val '' (W : Set e.ambient), e.ambient.isOpen.isOpenMap_subtype_val _ W.isOpen⟩
  have hO : O ≤ e.ambient := by
    rintro _ ⟨w, -, rfl⟩
    exact w.property
  have hOW : ∀ w : O, (⟨w.val, hO w.property⟩ : e.ambient) ∈ W := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    exact hw
  let κ : O → W := fun w => ⟨⟨w.val, hO w.property⟩, hOW w⟩
  have hκ : ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel e.dim) ∞ κ := by
    rw [← ContMDiff.subtypeVal_comp_iff, ← ContMDiff.subtypeVal_comp_iff]
    exact contMDiff_subtype_val
  let e' := e.restrict O hO
  have hcO : (c.val : ComplexModel e.dim) ∈ O := ⟨c.val, hcW, rfl⟩
  have hcC : (⟨(c.val : ComplexModel e.dim), hcO⟩ : O) ∈ e'.carrier := by
    change Opens.inclusion hO ⟨(c.val : ComplexModel e.dim), hcO⟩ ∈ e.carrier
    exact c.property
  refine ⟨e', ⟨⟨⟨(c.val : ComplexModel e.dim), hcO⟩, hcC⟩, ?_⟩, κ ⁻¹' A'',
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hκ hA'', ?_⟩
  · rw [LocalEmbedding.restrict_toPoint, ← hcy]
    rfl
  · ext z
    rw [mem_preimage, LocalEmbedding.restrict_toPoint, mem_preimage]
    exact hiff ⟨Opens.inclusion hO z.val, z.property⟩ (hOW z.val)

end Criterion

/-! ### The source non-flat locus -/

section Locus

variable {X Y : SourceReducedComplexSpace}

/-- **The source non-flat locus** `N_A` of `f` over the reduced structure of `A`: the points `y` over `A` at which
the fibre-product stalk `𝒪_{Y,y} ⧸ I_A 𝒪_{Y,y}` is not flat over `𝒪_{X,f y} ⧸ I_A`. -/
def relNonflatSource (f : Y ⟶ X) (A : Set X.obj.left) : Set Y.obj.left :=
  {y | f.hom.left.base y ∈ A ∧ ¬ (quotMap (fibreStalkMap f (f.hom.left.base y) y rfl)
    (vanishingIdealAt X.obj.left A (f.hom.left.base y))).Flat}

/-- Flatness at `y` does not depend on how the base point is named. -/
theorem flat_fibre_congr (f : Y ⟶ X) (A : Set X.obj.left) {y : Y.obj.left} {x : X.obj.left}
    (h : f.hom.left.base y = x) :
    (quotMap (fibreStalkMap f x y h) (vanishingIdealAt X.obj.left A x)).Flat ↔
      (quotMap (fibreStalkMap f (f.hom.left.base y) y rfl)
        (vanishingIdealAt X.obj.left A (f.hom.left.base y))).Flat := by
  subst h
  rfl

/-- **`relNonflat f A = f (N_A)`.** -/
theorem relNonflat_eq_image (f : Y ⟶ X) (A : Set X.obj.left) :
    relNonflat f A = f.hom.left.base '' relNonflatSource f A := by
  ext x
  constructor
  · rintro ⟨hxA, hnf⟩
    unfold FlatOverAt at hnf
    push Not at hnf
    obtain ⟨y, h, hy⟩ := hnf
    subst h
    exact ⟨y, ⟨hxA, hy⟩, rfl⟩
  · rintro ⟨y, ⟨hyA, hnf⟩, rfl⟩
    exact ⟨hyA, fun hall => hnf (hall y rfl)⟩

/-- **Frisch's Theorem (IV,9) for reduced complex spaces** (fibre-product family over the reduced structure of an
analytic `A ⊆ X`): the source non-flat locus is analytic in `Y`.  Explicit hypotheses: the chart local criterion
`h1` (item 1) and generic flatness at a fixed fibre point `hGF` (Frisch Th. (II,1)). -/
theorem isAnalyticSubset_relNonflatSource
    (h1 : ∀ {d t a b c : ℕ} {T : Set (ComplexModel d)} {W : Set (ComplexModel d × ComplexModel t)}
      {G : Fin b → Fin c → ComplexModel d × ComplexModel t → ℂ}
      {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}, RelExactStartOn T W G F → IsOpen W →
      ∀ {p : ComplexModel d × ComplexModel t}, p ∈ W → p.1 ∈ T →
        (ChartFlat d t F p (baseIdeal T p.1) ↔ FibreExactAt G F p.1 p.2))
    (hGF : ∀ (m t : ℕ) (p₀ : ComplexModel m) (P : Set (ComplexModel m)), IsAnalyticNear P p₀ → p₀ ∈ P →
      ∀ {a b c : ℕ} (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
      (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel m × ComplexModel t)), IsOpen Wn → (p₀, (0 : ComplexModel t)) ∈ Wn →
      RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧ IsHolZeroSetOn N P'' ∧ P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 p₀, p ∈ P → p ∉ P'' → FibreExactAt G A p 0)
    (f : Y ⟶ X) {A : Set X.obj.left} (hA : X.IsAnalyticSubset A) :
    Y.IsAnalyticSubset (relNonflatSource f A) := by
  classical
  apply isAnalyticSubset_of_forall_opens_ambient
  intro y
  -- the base chart and the window chart
  set eX := LocalEmbedding.ofPoint X (f.hom.left.base y) with heX
  obtain ⟨c₀, hc₀⟩ := LocalEmbedding.mem_range_ofPoint X (f.hom.left.base y)
  obtain ⟨eW, b, F, Ω, K, hΩ, hK, hKΩ, hF, ⟨zC₀, hz₀K, hz₀y⟩, hdict⟩ :=
    HironakaG10GfWindow.exists_window_chart_vanishing f eX y c₀ hc₀.symm
  -- an ambient lift `ψ₀` of `f`
  have hw : f.hom.left ≫ X.obj.hom = Y.obj.hom := Over.w f.hom
  have hFm : (eW.map ≫ f.hom.left) ≫ X.obj.hom = (modelOver eW.ambient eW.carrier).hom := by
    rw [Category.assoc, hw, eW.overPoint]
  have hfy : (eW.map ≫ f.hom.left).base zC₀ = f.hom.left.base y := by
    rw [← hz₀y]
    rfl
  obtain ⟨O₁, hz₀O₁, ψ₀, hψ₀, hfac⟩ := LocalEmbedding.exists_contMDiff_factor
    (eW.map ≫ f.hom.left) hFm eX zC₀ ⟨c₀, hc₀.trans hfy.symm⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Set (ComplexModel eX.dim), T = HironakaG10GfNativeVanishing.trace eX A :=
    ⟨_, rfl⟩
  -- the base point of the chart point over `zC₀`
  have hψz₀ : ψ₀ ⟨zC₀.val, hz₀O₁⟩ = c₀.val := by
    obtain ⟨c, hc, hct⟩ := hfac zC₀ hz₀O₁
    have : c = c₀ := eX.toPoint_injective (hct.trans (hfy.trans hc₀.symm))
    rw [← hc, this]
  -- `T` is analytic near `(c₀.val : ComplexModel eX.dim)`
  have hT : IsAnalyticNear T (c₀.val : ComplexModel eX.dim) := by
    have htr : HironakaG10GfNativeVanishing.traceIn eX A = Subtype.val '' (eX.toPoint ⁻¹' A) := by
      ext m
      constructor
      · rintro ⟨c, rfl, hc⟩
        exact ⟨c, hc, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c, rfl, hc⟩
    have hS : IsComplexAnalyticSubset (n := eX.dim) (HironakaG10GfNativeVanishing.traceIn eX A) := by
      rw [htr]
      exact HironakaG10NativeAnalyticClosureDifference.analytic_image_trace hA eX
    rw [hTdef]
    exact isAnalyticNear_image_val hS c₀.val
  have hz₀Ω : (zC₀.val : ComplexModel eW.dim) ∈ Ω := hKΩ (interior_subset hz₀K)
  have hFhol : ∀ i j, HolAt (F i j) ((c₀.val : ComplexModel eX.dim), (zC₀.val : ComplexModel eW.dim)) := fun i j =>
    holAt_of_differentiableOn (isOpen_univ.prod hΩ) (hF i j) ⟨mem_univ _, hz₀Ω⟩
  -- the chart non-flat set is analytic near the chart point
  obtain ⟨U, hw₀U, hU⟩ := exists_opens_chartNonflat (d := eX.dim) (t := eW.dim) h1 hT
    (hGF (eX.dim + eW.dim) eW.dim ((splitModel eX.dim eW.dim).symm ((c₀.val : ComplexModel eX.dim), (zC₀.val : ComplexModel eW.dim)))) F hFhol
  -- the graph map
  set γ : eW.ambient → ComplexModel (eX.dim + eW.dim) :=
    extendOpens O₁ (fun z => (splitModel eX.dim eW.dim).symm (((ψ₀ z : eX.ambient) : ComplexModel eX.dim),
      ((z : eW.ambient) : ComplexModel eW.dim))) 0 with hγ
  have hγO₁ : ∀ z (hz : z ∈ O₁), γ z =
      (splitModel eX.dim eW.dim).symm (((ψ₀ ⟨z, hz⟩ : eX.ambient) : ComplexModel eX.dim), (z : ComplexModel eW.dim)) :=
    fun z hz => extendOpens_of_mem O₁ _ 0 hz
  have hγsm : ∀ z ∈ O₁, ContMDiffAt 𝓘(ℂ, ComplexModel eW.dim) 𝓘(ℂ, ComplexModel (eX.dim + eW.dim)) ∞ γ z := by
    intro z hz
    refine contMDiffAt_extendOpens O₁ 0 hz ?_
    have h1' : ContMDiff 𝓘(ℂ, ComplexModel eW.dim) 𝓘(ℂ, ComplexModel eX.dim) ∞
        (fun z : O₁ => ((ψ₀ z : eX.ambient) : ComplexModel eX.dim)) := contMDiff_subtype_val.comp hψ₀
    have h2' : ContMDiff 𝓘(ℂ, ComplexModel eW.dim) 𝓘(ℂ, ComplexModel eW.dim) ∞
        (fun z : O₁ => ((z : eW.ambient) : ComplexModel eW.dim)) :=
      contMDiff_subtype_val.comp contMDiff_subtype_val
    have hpair := h1'.prodMk_space h2'
    exact ((splitModel eX.dim eW.dim).symm.contDiff.contMDiff.comp hpair) _
  have hγc : ContinuousOn γ O₁ := fun z hz => (hγsm z hz).continuousAt.continuousWithinAt
  -- the source open
  set W : Opens eW.ambient := ⟨(O₁ : Set eW.ambient) ∩ γ ⁻¹' (U : Set (ComplexModel (eX.dim + eW.dim))) ∩
      (Subtype.val ⁻¹' interior K),
    (hγc.isOpen_inter_preimage O₁.isOpen U.isOpen).inter
      (isOpen_interior.preimage continuous_subtype_val)⟩ with hW
  have hz₀W : zC₀.val ∈ W := by
    refine ⟨⟨hz₀O₁, ?_⟩, hz₀K⟩
    show γ zC₀.val ∈ U
    rw [hγO₁ _ hz₀O₁, hψz₀]
    exact hw₀U
  let γ' : W → U := fun z => ⟨γ z, z.property.1.2⟩
  have hγ' : ContMDiff 𝓘(ℂ, ComplexModel eW.dim) 𝓘(ℂ, ComplexModel (eX.dim + eW.dim)) ∞ γ' := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact AnalyticSubsetOpens.contMDiff_restrict (U := W)
      (fun z hz => (hγsm z hz.1.1).contMDiffWithinAt)
  have hA2 := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hγ' hU
  refine ⟨eW, zC₀, hz₀y, W, hz₀W, _, hA2, ?_⟩
  -- the trace of `N_A` on `W`
  intro z hz
  obtain ⟨c, hcψ, hct⟩ := hfac z hz.1.1
  have hzK : (z.val : ComplexModel eW.dim) ∈ K := interior_subset hz.2
  have hfz : f.hom.left.base (eW.toPoint z) = eX.toPoint c := hct.symm
  have hγz : splitModel eX.dim eW.dim (γ z.val) = ((c.val : ComplexModel eX.dim), (z.val : ComplexModel eW.dim)) := by
    rw [hγO₁ _ hz.1.1, ContinuousLinearEquiv.apply_symm_apply, ← hcψ]
  change _ ↔ splitModel eX.dim eW.dim (γ z.val) ∈ {q | q.1 ∈ T ∧ ¬ ChartFlat eX.dim eW.dim F q (baseIdeal T q.1)}
  rw [hγz]
  simp only [mem_ofPred_eq]
  have hTiff : (c.val : ComplexModel eX.dim) ∈ T ↔ f.hom.left.base (eW.toPoint z) ∈ A := by
    rw [hfz, hTdef]
    exact ⟨HironakaG10GfNativeVanishing.toPoint_mem_of_mem_trace eX,
      HironakaG10GfNativeVanishing.mem_trace_of_mem eX⟩
  have hflat := hdict z hzK c hfz A
  rw [flat_fibre_congr f A hfz] at hflat
  unfold relNonflatSource
  rw [mem_ofPred_eq, hTiff, hflat, hTdef]

end Locus

end

end Hironaka.Analytic.Unibranch.HironakaG10FrNativeIV9
