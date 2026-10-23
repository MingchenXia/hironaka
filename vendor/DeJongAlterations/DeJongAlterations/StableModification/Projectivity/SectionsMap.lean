/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3A)
-/
import DeJongAlterations.StableModification.Projectivity.LineBundleTwist
import DeJongAlterations.Geometry.FiniteProjectiveAffineCharts
import DeJongAlterations.Geometry.FiniteProjectiveLocal

/-!
# The morphism to `ℙᴺ` given by generating sections of a line bundle

Blueprint `sm-projectivity-core.tex`, `def:sm-lbd-map` and `lem:sm-lbd-map-preimage` (PLAN-OM3
M2; Hartshorne II.7.1). Let `L` be line-bundle data on `X ⟶ Spec R` and let
`s 0, …, s N` be global sections of `𝓛^m` without common zero. On an affine open `V` contained in
a chart `U i`, the coefficients `(s a)_i|_V` generate the unit ideal of `Γ(X, V)` and give Codex's
native tuple map `Spec Γ(X, V) ⟶ ℙᴺ_R` (`Geometry.FiniteProjective.affineTupleMap`); changing
the chart multiplies the tuple by the unit `(u k i)^m` (`affineTupleMap_unit`), and restriction to
smaller affine opens is coefficient extension (`affineTupleMap_naturality`). These chart maps glue
along the locally directed cover of `X` by all affine opens inside charts
(`Scheme.OpenCover.glueMorphismsOfLocallyDirected`) to

* `LineBundleData.toProjectiveSpace L p s hs : X ⟶ ℙᴺ_R`, with
* `toProjectiveSpace_structure`: it lies over `p : X ⟶ Spec R`;
* `toProjectiveSpace_preimage_coordinate` (`lem:sm-lbd-map-preimage`): the preimage of the
  coordinate chart `D₊(x_a)` is the non-vanishing locus `D(s a)`.

The construction follows Codex's `Geometry.FiniteProjective.tupleProjectiveMap` (sections of
`g^* 𝒪(d)` for a morphism `g` to projective space) with the trivializing cover of `L` in place of
the coordinate charts of `g`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace DeJongAlterations.StableModification.Projectivity

open Geometry.FiniteProjective Geometry.BlowupProjectiveEmbedding Geometry.BlowupGluing
  Geometry.ProjectiveIdeal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

namespace LineBundleData

variable (L : LineBundleData X)

/-! ### The cover by affine opens inside charts -/

/-- The affine opens (of the small affine Zariski site) contained in some chart of `L`. -/
def ChartSite := { V : X.AffineZariskiSite // ∃ i, V.1 ≤ L.U i }

instance : PartialOrder L.ChartSite :=
  inferInstanceAs (PartialOrder { V : X.AffineZariskiSite // ∃ i, V.1 ≤ L.U i })

/-- The open cover of `X` by all affine opens contained in charts of `L`. -/
def chartCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers L.ChartSite (fun V => V.1.1.toScheme) (fun V => V.1.1.ι) (by
    intro x
    obtain ⟨i, hi⟩ := L.exists_mem_U x
    obtain ⟨V, hV, hxV, hVi⟩ := exists_isAffineOpen_mem_and_subset hi
    exact ⟨⟨⟨V, hV⟩, i, hVi⟩, ⟨x, hxV⟩, rfl⟩)

instance chartCover_partialOrder : PartialOrder L.chartCover.I₀ :=
  inferInstanceAs (PartialOrder L.ChartSite)

instance chartCover_locallyDirected : L.chartCover.LocallyDirected where
  trans {U V} h := (Scheme.AffineZariskiSite.directedCover X).trans (homOfLE h.le)
  trans_id U := by
    exact (Scheme.AffineZariskiSite.directedCover X).trans_id U.1
  trans_comp h k := by
    exact (Scheme.AffineZariskiSite.directedCover X).trans_comp (homOfLE h.le) (homOfLE k.le)
  w h := by
    exact (Scheme.AffineZariskiSite.directedCover X).trans_map (homOfLE h.le)
  directed {U V} x := by
    obtain ⟨W, hWU, hWV, y, hy⟩ :=
      (Scheme.AffineZariskiSite.directedCover X).exists_lift_trans_eq x
    obtain ⟨i, hi⟩ := U.2
    let W' : L.ChartSite :=
      ⟨W, i, (Scheme.AffineZariskiSite.toOpens_mono hWU.le).trans hi⟩
    exact ⟨W', homOfLE hWU.le, homOfLE hWV.le, y, hy⟩
  property_trans h := by
    exact Scheme.Cover.LocallyDirected.property_trans
      (𝒰 := Scheme.AffineZariskiSite.directedCover X) (homOfLE h.le)

/-! ### Local tuples -/

variable {L} {m : ℤ} {N : ℕ}

lemma ringMap_map {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (h₃ : V₃ ≤ V₁)
    (r : Γ(X, V₁)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op r) =
      X.presheaf.map (homOfLE h₃).op r :=
  res_res h₁ h₂ h₃ r

/-- The `i`-th coefficient of a global section of `𝓛^m`, restricted to an open `V ⊆ U i`. -/
def localValue (s : L.Sections m ⊤) {V : X.Opens} (i : L.ι) (hi : V ≤ L.U i) : Γ(X, V) :=
  X.presheaf.map (homOfLE (le_inf le_top hi : V ≤ ⊤ ⊓ L.U i)).op (s.coeff i)

lemma localValue_restrict (s : L.Sections m ⊤) {U V : X.AffineZariskiSite} (h : U ⟶ V)
    (i : L.ι) (hi : V.1 ≤ L.U i) :
    coefficientMap h (localValue s i hi) =
      localValue s i ((Scheme.AffineZariskiSite.toOpens_mono h.le).trans hi) :=
  (ConcreteCategory.congr_hom
    (X.presheaf.map_comp (homOfLE (le_inf le_top hi : V.1 ≤ ⊤ ⊓ L.U i)).op
      ((Scheme.AffineZariskiSite.toOpensFunctor X).map h).op) (s.coeff i)).symm

/-- Changing the chart multiplies the local value by the unit `(u k i)^m`. -/
lemma localValue_transition (s : L.Sections m ⊤) {V : X.Opens} (i k : L.ι) (hi : V ≤ L.U i)
    (hk : V ≤ L.U k) :
    localValue s k hk = ((L.trans (le_inf hk hi : V ≤ L.U k ⊓ L.U i) ^ m : Γ(X, V)ˣ) : Γ(X, V)) *
      localValue s i hi := by
  have hle : V ≤ ⊤ ⊓ (L.U k ⊓ L.U i) := le_inf le_top (le_inf hk hi)
  have e := congrArg (X.presheaf.map (homOfLE hle).op) (s.coeff_compat k i)
  rw [ringMap_map _ _ (le_inf le_top hk), map_mul, ringMap_map _ _ (le_inf le_top hi),
    L.map_res_trans_zpow] at e
  exact e

lemma basicOpen_localValue (s : L.Sections m ⊤) {V : X.Opens} (i : L.ι) (hi : V ≤ L.U i) :
    X.basicOpen (localValue s i hi) = V ⊓ s.nonvanishingLocus := by
  rw [localValue, Scheme.basicOpen_res, ← s.nonvanishingLocus_inf i]
  apply le_antisymm
  · exact inf_le_inf_left _ inf_le_left
  · exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hi))

/-- Sections without common zero: their non-vanishing loci cover `X`. -/
def Generates (s : Fin (N + 1) → L.Sections m ⊤) : Prop :=
  ∀ x : X, ∃ a, x ∈ (s a).nonvanishingLocus

/-- On an affine open inside a chart, the local values of generating sections generate the unit
ideal. -/
lemma localSpan {s : Fin (N + 1) → L.Sections m ⊤} (hs : Generates s) (V : X.affineOpens)
    (i : L.ι) (hi : V.1 ≤ L.U i) :
    Ideal.span (Set.range fun a => localValue (s a) i hi) = ⊤ := by
  rw [← V.2.self_le_iSup_basicOpen_iff]
  intro x hx
  obtain ⟨a, ha⟩ := hs x
  have hx' : x ∈ X.basicOpen (localValue (s a) i hi) := by
    rw [basicOpen_localValue]
    exact ⟨hx, ha⟩
  exact Opens.mem_iSup.mpr ⟨⟨_, a, rfl⟩, hx'⟩

/-! ### Chart maps -/

variable (p : X ⟶ Spec (.of R)) {s : Fin (N + 1) → L.Sections m ⊤} (hs : Generates s)

/-- The native tuple map on an affine open `V ⊆ U i`. -/
def chartMap (V : X.affineOpens) (i : L.ι) (hi : V.1 ≤ L.U i) :
    V.1.toScheme ⟶ projectiveSpace R N :=
  V.2.isoSpec.hom ≫ affineTupleMap (affineBaseCoefficients p V)
    (fun a => localValue (s a) i hi) (localSpan hs V i hi)

/-- The chart map does not depend on the chart. -/
theorem chartMap_coordinate (V : X.affineOpens) (i k : L.ι) (hi : V.1 ≤ L.U i)
    (hk : V.1 ≤ L.U k) : chartMap p hs V k hk = chartMap p hs V i hi := by
  let v : Γ(X, V.1)ˣ := L.trans (le_inf hk hi : V.1 ≤ L.U k ⊓ L.U i) ^ m
  have hval : (fun a => localValue (s a) k hk) =
      (fun a => (v : Γ(X, V.1)) * localValue (s a) i hi) := by
    funext a
    exact localValue_transition (s a) i k hi hk
  dsimp only [chartMap]
  congr 1
  exact (affineTupleMap_congr rfl hval _
    (generator_span_unit ⊤ _ (localSpan hs V i hi) v)).trans
      (affineTupleMap_unit _ _ _ v)

/-- Restriction to a smaller affine open is coefficient extension. -/
theorem chartMap_naturality {U V : X.AffineZariskiSite} (h : U ⟶ V) (i k : L.ι)
    (hi : U.1 ≤ L.U i) (hk : V.1 ≤ L.U k) :
    X.homOfLE (Scheme.AffineZariskiSite.toOpens_mono h.le) ≫
      chartMap p hs ⟨V.1, V.2⟩ k hk = chartMap p hs ⟨U.1, U.2⟩ i hi := by
  let hkU := (Scheme.AffineZariskiSite.toOpens_mono h.le).trans hk
  have hspec : X.homOfLE (Scheme.AffineZariskiSite.toOpens_mono h.le) ≫ V.2.isoSpec.hom =
      U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (coefficientMap h)) :=
    (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map U.1 V.1
      (Scheme.AffineZariskiSite.toOpens_mono h.le)).symm
  have hspan : Ideal.span (Set.range (fun a =>
      coefficientMap h (localValue (s a) k hk))) = ⊤ := by
    simpa only [localValue_restrict] using localSpan hs ⟨U.1, U.2⟩ k hkU
  change _ ≫ (V.2.isoSpec.hom ≫ _) = _
  rw [← Category.assoc, hspec, Category.assoc, affineTupleMap_naturality _ _ _ _ hspan]
  change U.2.isoSpec.hom ≫ _ = _
  have H := affineTupleMap_congr (affineBaseCoefficients_restrict p h)
    (funext (fun a => localValue_restrict (s a) h k hk)) hspan
    (localSpan hs ⟨U.1, U.2⟩ k hkU)
  exact (congrArg (fun q => U.2.isoSpec.hom ≫ q) H).trans
    (chartMap_coordinate p hs ⟨U.1, U.2⟩ i k hi hkU)

/-- The chart map lies over `p`. -/
@[reassoc]
theorem chartMap_structure (V : X.affineOpens) (i : L.ι) (hi : V.1 ≤ L.U i) :
    chartMap p hs V i hi ≫ projectiveSpaceStructure R N = V.1.ι ≫ p := by
  rw [chartMap, Category.assoc, affineTupleMap_structure, affineBaseCoefficients_structure,
    ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

/-- The preimage of the `a`-th coordinate chart under a chart map. -/
theorem chartMap_preimage_coordinate (V : X.affineOpens) (i : L.ι) (hi : V.1 ≤ L.U i)
    (a : Fin (N + 1)) :
    chartMap p hs V i hi ⁻¹ᵁ nativeCoordinateOpen a =
      V.1.ι ⁻¹ᵁ X.basicOpen (localValue (s a) i hi) := by
  rw [chartMap, Scheme.Hom.comp_preimage, affineTupleMap_preimage_coordinate,
    IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_preimage_basicOpen]

/-- The chart maps on the cover by affine opens inside charts. -/
def chartCoverMap (V : L.chartCover.I₀) : L.chartCover.X V ⟶ projectiveSpace R N :=
  chartMap p hs ⟨V.1.1, V.1.2⟩ V.2.choose V.2.choose_spec

theorem chartCoverMap_compatible {U V : L.chartCover.I₀} (h : U ⟶ V) :
    L.chartCover.trans h ≫ chartCoverMap p hs V = chartCoverMap p hs U :=
  chartMap_naturality p hs (homOfLE h.le) _ _ U.2.choose_spec V.2.choose_spec

/-! ### The global map -/

/-- **The morphism `X ⟶ ℙᴺ_R` given by sections `s 0, …, s N` of `𝓛^m` without common zero**
(blueprint `def:sm-lbd-map`): on `D(s a) ∩ U i` it is `x ↦ (s 0 : … : s N)` in the coordinates of
the chart `U i`. -/
def toProjectiveSpace : X ⟶ projectiveSpace R N :=
  L.chartCover.glueMorphismsOfLocallyDirected (chartCoverMap p hs)
    (fun h => chartCoverMap_compatible p hs h)

/-- On every affine open inside a chart, the global map is the chart map. -/
@[reassoc]
theorem toProjectiveSpace_restrict (V : X.affineOpens) (i : L.ι) (hi : V.1 ≤ L.U i) :
    V.1.ι ≫ toProjectiveSpace p hs = chartMap p hs V i hi := by
  let V' : L.ChartSite := ⟨⟨V.1, V.2⟩, i, hi⟩
  have := L.chartCover.map_glueMorphismsOfLocallyDirected (chartCoverMap p hs)
    (fun h => chartCoverMap_compatible p hs h) V'
  exact this.trans (chartMap_coordinate p hs V i _ hi V'.2.choose_spec)

/-- **The map lies over the base** `p : X ⟶ Spec R`. -/
@[reassoc]
theorem toProjectiveSpace_structure :
    toProjectiveSpace p hs ≫ projectiveSpaceStructure R N = p := by
  apply L.chartCover.hom_ext
  intro V
  change V.1.1.ι ≫ _ = V.1.1.ι ≫ _
  rw [← Category.assoc, toProjectiveSpace_restrict p hs ⟨V.1.1, V.1.2⟩ _ V.2.choose_spec]
  exact chartMap_structure p hs ⟨V.1.1, V.1.2⟩ _ _

/-- **Preimages of coordinate charts** (blueprint `lem:sm-lbd-map-preimage`): the preimage of
`D₊(x_a)` under the map given by `s` is the non-vanishing locus `D(s a)`. -/
theorem toProjectiveSpace_preimage_coordinate (a : Fin (N + 1)) :
    toProjectiveSpace p hs ⁻¹ᵁ nativeCoordinateOpen a = (s a).nonvanishingLocus := by
  ext x
  obtain ⟨i, hi⟩ := L.exists_mem_U x
  obtain ⟨V, hV, hxV, hVi⟩ := exists_isAffineOpen_mem_and_subset hi
  have H := chartMap_preimage_coordinate p hs ⟨V, hV⟩ i hVi a
  rw [← toProjectiveSpace_restrict p hs ⟨V, hV⟩ i hVi, Scheme.Hom.comp_preimage,
    basicOpen_localValue] at H
  have H' : (⟨x, hxV⟩ : V.toScheme) ∈ V.ι ⁻¹ᵁ (toProjectiveSpace p hs ⁻¹ᵁ
      nativeCoordinateOpen a) ↔ (⟨x, hxV⟩ : V.toScheme) ∈ V.ι ⁻¹ᵁ (V ⊓ (s a).nonvanishingLocus) :=
    Iff.of_eq (congrArg (fun W => (⟨x, hxV⟩ : V.toScheme) ∈ W) H)
  exact H'.trans ⟨fun h => h.2, fun h => ⟨hxV, h⟩⟩

end LineBundleData

end DeJongAlterations.StableModification.Projectivity
