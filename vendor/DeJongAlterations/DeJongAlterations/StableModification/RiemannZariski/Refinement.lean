import DeJongAlterations.StableModification.RiemannZariski.Scheme
import DeJongAlterations.Geometry.ProjectiveIdealCharts
import DeJongAlterations.Projective
import DeJongAlterations.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Locus

/-!
# Refinement of Riemann–Zariski covers

Temkin, *Stable modification of relative curves* (J. Algebraic Geom. 19 (2010); arXiv v3,
`references/temkin10-stable-modification/source/semi-stable.tex`), §3.2: Lemma 3.2.3
(`ratfunlem`, lines 2356–2363) and Proposition 3.2.6 (`oetamodprop`, lines 2394–2409), with the
covering statement used in Proposition 4.5.1 (lines 3246–3249) and the remark that
`K^s`-modifications are generically étale alterations (lines 2310–2312).

Let `S` be a separated scheme and `η : Spec L → S` a point with values in a field `L`. Finitely
many morphisms `gᵢ : Tᵢ → S` locally of finite type, with `Tᵢ` affine mapping into affine opens
`Vᵢ` and points `ηTᵢ` over `η` (Temkin's `L`-quasi-modifications, in the affine case to which he
reduces), become open pieces `Wᵢ` of a single proper `p : S' → S` (an `L`-modification): there are
proper `hᵢ : Wᵢ → Tᵢ` over `S`, compatible with dominant `L`-points. If the Riemann–Zariski spaces
`RZ_L(Tᵢ)` cover `RZ_L(S)`, the `Wᵢ` cover `S'`. For `S` integral, separated and locally
Noetherian and `L` separable algebraic over its function field, `p` is a generically étale
alteration.

## Construction

* For an affine open `V ⊆ S` and `f₁, …, fₙ ∈ L`, the schematic image of
  `(η, (1 : f₁ : … : fₙ)) : Spec L → S ×_ℤ ℙⁿ_ℤ` has the affine chart over `V ×_ℤ D₊(x₀)` with ring
  `s_V(Γ(S, V))[f₁, …, fₙ] ⊆ L` (`graph_hasCharts`); with the `fⱼ` the images of generators of
  `Γ(T, ⊤)` over `Γ(S, V)`, this chart maps isomorphically (closed immersion in general) onto `T`
  (`exists_graph_realizes`). One projective space replaces Temkin's product of `ℙ¹`'s.
* Two such refinements are dominated by the schematic image of `(η₁, η₂)` in their fibre product
  over `S` (`dominate_isRefinement`); charts multiply (`dominate_hasCharts`) and realisations
  pass to dominating refinements by the valuative criterion (`Realizes.of_dominates`).
* All chart computations reduce to one fact about schematic images of field points: over an
  affine open `U` of the target the image is `Spec` of the subring `s_U(Γ(Y, U)) ⊆ L`
  (`range_sectionsToField_imageChart`, `injective_sectionsToField_imageChart`), and section rings
  of product charts are compositums (`range_sectionsToField_prodChart`).

## Main definitions

* `RiemannZariskiSpace.IsRefinement η p η'`: `p` proper, `S'` integral, `η'` dominant over `η`,
  every point of `S'` the centre of an extension of `η'` to a valuation ring of `L`.
* `RiemannZariskiSpace.HasCharts η p η' F`: affine charts with section ring `s_V(Γ(S, V))[F]` over
  every affine open `V`.
* `RiemannZariskiSpace.Realizes p η' g ηT`: an open of `S'` with a proper morphism to `T` over `S`
  compatible with the points, centring every valuation ring of `RZ_L(T)`.
* `RiemannZariskiSpace.graphPoint`, `RiemannZariskiSpace.graphProj`: the graph closure of
  finitely many elements of `L` (Temkin, Lemma 3.2.3).
* `RiemannZariskiSpace.functionFieldPoint S L`: the generic point `Spec L → Spec K(S) → S`.

## Main results

* `RiemannZariskiSpace.exists_refinement`: Temkin, Proposition 3.2.6 (affine pieces), with charts
  and the covering addendum.
* `RiemannZariskiSpace.isAlteration_isGenericallyEtale_of_hasCharts`,
  `RiemannZariskiSpace.exists_refinement_genericallyEtale`: the refinement over a separable
  algebraic extension of the function field is a generically étale alteration.
* `RiemannZariskiSpace.exists_etale_localization_of_separable`: a domain of finite type over a
  Noetherian domain, with separable fraction field extension, is étale after inverting one
  nonzero element.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

universe u

namespace DeJongAlterations.StableModification

namespace RiemannZariskiSpace

variable {L : Type u} [Field L]

/-! ### Sections and field points -/

section Sections

variable {X X' : Scheme.{u}}

/-- A point `ξ : Spec L → X` factoring through an affine open `U` is the composite of
`Spec (s_U)` with the canonical morphism `Spec Γ(X, U) → X`. -/
theorem SpecMap_sectionsToField_fromSpec (ξ : Spec (.of L) ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (h : ξ ⁻¹ᵁ U = ⊤) :
    Spec.map (CommRingCat.ofHom (sectionsToField ξ U h)) ≫ hU.fromSpec = ξ := by
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec ξ hU (isAffineOpen_top _) h.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h1
  rw [sectionsToField, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, h1,
    ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

/-- Proof irrelevance and congruence for `sectionsToField`. -/
lemma sectionsToField_congr {ξ₁ ξ₂ : Spec (.of L) ⟶ X} (e : ξ₁ = ξ₂) {U : X.Opens}
    (h₁ : ξ₁ ⁻¹ᵁ U = ⊤) (h₂ : ξ₂ ⁻¹ᵁ U = ⊤) :
    sectionsToField ξ₁ U h₁ = sectionsToField ξ₂ U h₂ := by
  subst e
  rfl

/-- `Spec γ` followed by the canonical morphism of an affine open `U` factors through `U`. -/
lemma preimage_SpecMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U)
    (γ : Γ(X, U) ⟶ CommRingCat.of L) : (Spec.map γ ≫ hU.fromSpec) ⁻¹ᵁ U = ⊤ := by
  rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
  rfl

/-- **Sections of a point given by a ring map.** For `γ : Γ(X, U) → L` and an affine open `U`,
the point `Spec γ` followed by `Spec Γ(X, U) → X` has `s_U = γ`. -/
theorem sectionsToField_SpecMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U)
    (γ : Γ(X, U) ⟶ CommRingCat.of L) :
    sectionsToField (Spec.map γ ≫ hU.fromSpec) U (preimage_SpecMap_fromSpec hU γ) = γ.hom := by
  have h := SpecMap_sectionsToField_fromSpec (Spec.map γ ≫ hU.fromSpec) hU
    (preimage_SpecMap_fromSpec hU γ)
  have h3 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h)
  exact congrArg CommRingCat.Hom.hom h3

/-- **Functoriality of the section rings.** If `ξ = ξ' ≫ f` and `U' ≤ f⁻¹ U`, the ring
`s_U(Γ(X, U))` is contained in `s_{U'}(Γ(X', U'))`. -/
theorem range_sectionsToField_le_of_comp (f : X' ⟶ X) {ξ : Spec (.of L) ⟶ X}
    {ξ' : Spec (.of L) ⟶ X'} (hf : ξ' ≫ f = ξ) {U : X.Opens} {U' : X'.Opens}
    (e : U' ≤ f ⁻¹ᵁ U) (hU : ξ ⁻¹ᵁ U = ⊤) (hU' : ξ' ⁻¹ᵁ U' = ⊤) :
    (sectionsToField ξ U hU).range ≤ (sectionsToField ξ' U' hU').range := by
  rw [← sectionsToField_comp_appLE f hf e hU' hU]
  rintro _ ⟨a, rfl⟩
  exact ⟨_, rfl⟩

/-- The section ring of a factorization through a surjective restriction map is unchanged. -/
theorem range_sectionsToField_eq_of_comp (f : X' ⟶ X) {ξ : Spec (.of L) ⟶ X}
    {ξ' : Spec (.of L) ⟶ X'} (hf : ξ' ≫ f = ξ) {U : X.Opens} {U' : X'.Opens}
    (e : U' ≤ f ⁻¹ᵁ U) (hU : ξ ⁻¹ᵁ U = ⊤) (hU' : ξ' ⁻¹ᵁ U' = ⊤)
    (hsurj : Function.Surjective (f.appLE U U' e)) :
    (sectionsToField ξ U hU).range = (sectionsToField ξ' U' hU').range := by
  refine le_antisymm (range_sectionsToField_le_of_comp f hf e hU hU') ?_
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, rfl⟩ := hsurj a
  rw [← sectionsToField_comp_appLE f hf e hU' hU]
  exact ⟨b, rfl⟩

/-- For the point `Spec γ` of `Spec R`, the section ring over `Spec R` is the image of `γ`. -/
theorem range_sectionsToField_SpecMap_top {R : CommRingCat.{u}} (γ : R ⟶ CommRingCat.of L)
    (h : (Spec.map γ) ⁻¹ᵁ ⊤ = ⊤) :
    (sectionsToField (Spec.map γ) ⊤ h).range = γ.hom.range := by
  have key : Spec.map γ = Spec.map ((Scheme.ΓSpecIso R).hom ≫ γ) ≫
      (isAffineOpen_top (Spec R)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp,
      Iso.inv_hom_id_assoc]
  rw [sectionsToField_congr key h (preimage_SpecMap_fromSpec (isAffineOpen_top (Spec R)) _),
    sectionsToField_SpecMap_fromSpec]
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(Scheme.ΓSpecIso R).inv a, ?_⟩
    show ((Scheme.ΓSpecIso R).inv ≫ (Scheme.ΓSpecIso R).hom ≫ γ).hom a = γ.hom a
    rw [Iso.inv_hom_id_assoc]

end Sections

/-! ### Schematic images of field points -/

section Image

variable {Y Z : Scheme.{u}} (φ : Spec (.of L) ⟶ Y)

/-- The spectrum of a field has one point. -/
instance subsingleton_Spec_field : Subsingleton (Spec (.of L)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum L))

/-- Every morphism from the spectrum of a field is quasi-compact. -/
instance quasiCompact_of_field : QuasiCompact φ :=
  ⟨fun _ _ _ => (Set.subsingleton_of_subsingleton).isCompact⟩

/-- An open of the target containing a point of the schematic image of a field point contains
the image of the point. -/
theorem preimage_eq_top_of_imageι_mem {U : Y.Opens} (x : φ.image) (hx : φ.imageι x ∈ U) :
    φ ⁻¹ᵁ U = ⊤ := by
  have hcl : φ.imageι x ∈ closure (Set.range φ) := by
    rw [← Scheme.Hom.support_ker, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨x, rfl⟩
  obtain ⟨_, hyU, y, rfl⟩ := mem_closure_iff.1 hcl U U.isOpen hx
  ext z
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  rw [Subsingleton.elim z y]
  exact hyU

/-- `appLE` over the full preimage is injective when `app` is. -/
lemma appLE_injective_of_le {X₁ X₂ : Scheme.{u}} {f : X₁ ⟶ X₂} {U : X₂.Opens} {V : X₁.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (hV : f ⁻¹ᵁ U ≤ V) (h : Function.Injective (f.app U)) :
    Function.Injective (f.appLE U V e) := by
  have : V = f ⁻¹ᵁ U := le_antisymm e hV
  subst this
  rwa [← Scheme.Hom.app_eq_appLE]

/-- The chart `ι⁻¹ U` of the schematic image over an affine open `U` is affine. -/
theorem imageChart_isAffineOpen {U : Y.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (φ.imageι ⁻¹ᵁ U) :=
  hU.preimage φ.imageι

/-- The induced point of the schematic image factors through every chart `ι⁻¹ U`. -/
lemma toImage_preimage_imageChart {U : Y.Opens} (hφU : φ ⁻¹ᵁ U = ⊤) :
    φ.toImage ⁻¹ᵁ (φ.imageι ⁻¹ᵁ U) = ⊤ := by
  rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toImage_imageι, hφU]

/-- On the chart over an affine open, the sections of the schematic image of a field point
inject into the field. -/
theorem injective_sectionsToField_imageChart {U : Y.Opens} (hU : IsAffineOpen U)
    (hφU : φ ⁻¹ᵁ U = ⊤) :
    Function.Injective (sectionsToField φ.toImage (φ.imageι ⁻¹ᵁ U)
      (toImage_preimage_imageChart φ hφU)) := by
  have h1 := appLE_injective_of_le (f := φ.toImage) (U := φ.imageι ⁻¹ᵁ U) (V := ⊤)
    (toImage_preimage_imageChart φ hφU).ge le_top
    (Scheme.Hom.toImage_app_injective φ ⟨U, hU⟩)
  exact (Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv.injective.comp h1

/-- On the chart over an affine open `U`, the section ring of the schematic image is the
section ring `s_U(Γ(Y, U))`. -/
theorem range_sectionsToField_imageChart {U : Y.Opens} (hU : IsAffineOpen U)
    (hφU : φ ⁻¹ᵁ U = ⊤) :
    (sectionsToField φ.toImage (φ.imageι ⁻¹ᵁ U) (toImage_preimage_imageChart φ hφU)).range =
      (sectionsToField φ U hφU).range := by
  refine (range_sectionsToField_eq_of_comp φ.imageι (Scheme.Hom.toImage_imageι φ) le_rfl hφU
    (toImage_preimage_imageChart φ hφU) ?_).symm
  rw [← Scheme.Hom.app_eq_appLE]
  exact Scheme.IdealSheafData.subschemeι_app_surjective _ ⟨U, hU⟩

/-- **Every point of an affine piece is a centre.** Let `ξ` be a point of `Z` factoring through an
affine open `W` with `s_W` injective. Every `x ∈ W` is the image of the closed point under an
extension of `ξ` to a valuation ring of `L`. -/
theorem exists_extension_closedPoint_eq (ξ : Spec (.of L) ⟶ Z) {W : Z.Opens}
    (hW : IsAffineOpen W) (hξW : ξ ⁻¹ᵁ W = ⊤)
    (hinj : Function.Injective (sectionsToField ξ W hξW)) {x : Z} (hx : x ∈ W) :
    ∃ (V : RiemannZariskiSpace L) (ψ : Spec (.of V.valuationSubring) ⟶ Z),
      toSpecValuationSubring V ≫ ψ = ξ ∧ ψ (specClosedPoint V) = x := by
  set s := sectionsToField ξ W hξW
  let 𝔭 := hW.primeIdealOf ⟨x, hx⟩
  let R := Localization.AtPrime 𝔭.asIdeal
  have hu : ∀ y : 𝔭.asIdeal.primeCompl, IsUnit (s y) := by
    intro ⟨y, hy⟩
    refine IsUnit.mk0 _ fun h0 => hy ?_
    have : y = 0 := hinj (by rw [h0, map_zero])
    rw [this]
    exact 𝔭.asIdeal.zero_mem
  let g : R →+* L := IsLocalization.lift (M := 𝔭.asIdeal.primeCompl) hu
  have hg : ∀ a, g (algebraMap _ R a) = s a := IsLocalization.lift_eq hu
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing g
  have hV : (⟨B⟩ : RiemannZariskiSpace L) ∈ ofRingHom s := by
    rw [mem_ofRingHom]
    intro a
    rw [← hg]
    exact hB _
  refine ⟨⟨B⟩, extensionOfMem ξ hW hξW _ hV,
    toSpecValuationSubring_comp_extensionOfMem hW hξW _ hV, ?_⟩
  have hp : Spec.map (CommRingCat.ofHom (s.codRestrict
      (⟨B⟩ : RiemannZariskiSpace L).valuationSubring (mem_ofRingHom.1 hV)))
      (specClosedPoint ⟨B⟩) = 𝔭 := by
    rw [Spec.map_apply]
    apply PrimeSpectrum.ext
    ext a
    change (s.codRestrict B (mem_ofRingHom.1 hV)) a ∈ IsLocalRing.maximalIdeal B ↔ a ∈ 𝔭.asIdeal
    have he : (s.codRestrict B (mem_ofRingHom.1 hV)) a =
        (g.codRestrict B.toSubring hB) (algebraMap _ R a) := Subtype.ext (hg a).symm
    rw [he, IsLocalRing.mem_maximalIdeal, ← IsLocalization.AtPrime.to_map_mem_maximal_iff R
      𝔭.asIdeal a, IsLocalRing.mem_maximalIdeal]
    exact map_mem_nonunits_iff (g.codRestrict B.toSubring hB) _
  rw [extensionOfMem, Scheme.Hom.comp_apply, hp]
  exact hW.fromSpec_primeIdealOf ⟨x, hx⟩

/-- **Centres on a schematic image.** Every point of the schematic image of a field point is the
centre of an extension of the induced point. -/
theorem image_exists_extension_closedPoint_eq (x : φ.image) :
    ∃ (V : RiemannZariskiSpace L) (ψ : Spec (.of V.valuationSubring) ⟶ φ.image),
      toSpecValuationSubring V ≫ ψ = φ.toImage ∧ ψ (specClosedPoint V) = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (φ.imageι x)) isOpen_univ
  have hφU := preimage_eq_top_of_imageι_mem φ x hxU
  exact exists_extension_closedPoint_eq φ.toImage (imageChart_isAffineOpen φ hU)
    (toImage_preimage_imageChart φ hφU) (injective_sectionsToField_imageChart φ hU hφU) hxU

/-- The schematic image of a field point is integral. -/
instance isIntegral_image : IsIntegral φ.image := by
  obtain ⟨z⟩ : Nonempty (Spec (.of L)) := inferInstance
  have hr : Set.range φ.toImage = {φ.toImage z} := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      rw [Subsingleton.elim w z]
      rfl
    · rintro rfl
      exact ⟨z, rfl⟩
  have : IrreducibleSpace φ.image := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← φ.toImage.denseRange.closure_range, hr]
    exact isIrreducible_singleton.closure
  have : IsReduced φ.image := by
    refine @IsReduced.of_openCover _ φ.ker.subschemeCover.openCover (fun U₀ => ?_)
    let U : Y.affineOpens := U₀
    have : _root_.IsReduced (Γ(Y, U.1) ⧸ φ.ker.ideal U) := by
      rw [Scheme.Hom.ker_apply]
      exact isReduced_of_injective _ (RingHom.kerLift_injective (φ.app U.1).hom)
    change IsReduced (Spec (CommRingCat.of (Γ(Y, U.1) ⧸ φ.ker.ideal U)))
    infer_instance
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A morphism whose composite with an open immersion is dominant is dominant. -/
lemma isDominant_of_comp_isOpenImmersion {T W X : Scheme.{u}} (e : T ⟶ W) (j : W ⟶ X)
    [IsOpenImmersion j] [IsDominant (e ≫ j)] : IsDominant e := by
  refine ⟨?_⟩
  have h : Set.range e = j ⁻¹' Set.range (e ≫ j) := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, j.isOpenEmbedding.injective (by simpa [Scheme.Hom.comp_apply] using ht)⟩
  rw [DenseRange, h]
  exact (e ≫ j).denseRange.preimage j.isOpenEmbedding.isOpenMap

end Image

/-! ### Product charts -/

section ProdChart

/-- The spectrum of an injective ring map is dominant. -/
lemma isDominant_SpecMap_of_injective {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : Function.Injective f.hom) : IsDominant (Spec.map f) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap f.hom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 hf]
  exact bot_le

variable {B X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ B) (f₂ : X₂ ⟶ B)

/-- The open immersion `W₁ ×_B W₂ → X₁ ×_B X₂` for opens `W₁ ⊆ X₁`, `W₂ ⊆ X₂`. -/
noncomputable def prodChartMap (W₁ : X₁.Opens) (W₂ : X₂.Opens) :
    pullback (W₁.ι ≫ f₁) (W₂.ι ≫ f₂) ⟶ pullback f₁ f₂ :=
  pullback.map _ _ _ _ W₁.ι W₂.ι (𝟙 B) (by simp) (by simp)

/-- `W₁ ×_B W₂ → X₁ ×_B X₂` is an open immersion. -/
instance (W₁ : X₁.Opens) (W₂ : X₂.Opens) : IsOpenImmersion (prodChartMap f₁ f₂ W₁ W₂) := by
  unfold prodChartMap
  infer_instance

/-- The *product chart* `W₁ ×_B W₂` as an open of `X₁ ×_B X₂`. -/
noncomputable def prodChart (W₁ : X₁.Opens) (W₂ : X₂.Opens) : (pullback f₁ f₂).Opens :=
  (prodChartMap f₁ f₂ W₁ W₂).opensRange

/-- Points of the product chart are those whose projections lie in `W₁` and `W₂`. -/
lemma mem_prodChart_iff {W₁ : X₁.Opens} {W₂ : X₂.Opens} (y : ↥(pullback f₁ f₂)) :
    y ∈ prodChart f₁ f₂ W₁ W₂ ↔ pullback.fst f₁ f₂ y ∈ W₁ ∧ pullback.snd f₁ f₂ y ∈ W₂ := by
  change y ∈ Set.range (prodChartMap f₁ f₂ W₁ W₂) ↔ _
  rw [prodChartMap, Scheme.Pullback.range_map]
  simp

/-- The product chart lies over `W₁`. -/
lemma prodChart_le_fst {W₁ : X₁.Opens} {W₂ : X₂.Opens} :
    prodChart f₁ f₂ W₁ W₂ ≤ pullback.fst f₁ f₂ ⁻¹ᵁ W₁ :=
  fun y hy => ((mem_prodChart_iff f₁ f₂ y).1 hy).1

/-- The product chart lies over `W₂`. -/
lemma prodChart_le_snd {W₁ : X₁.Opens} {W₂ : X₂.Opens} :
    prodChart f₁ f₂ W₁ W₂ ≤ pullback.snd f₁ f₂ ⁻¹ᵁ W₂ :=
  fun y hy => ((mem_prodChart_iff f₁ f₂ y).1 hy).2

/-- A morphism into `X₁ ×_B X₂` whose projections land in `W₁` and `W₂` lands in the product
chart. -/
lemma preimage_prodChart_eq_top {T : Scheme.{u}} (ξ : T ⟶ pullback f₁ f₂) {W₁ : X₁.Opens}
    {W₂ : X₂.Opens} (h₁ : (ξ ≫ pullback.fst f₁ f₂) ⁻¹ᵁ W₁ = ⊤)
    (h₂ : (ξ ≫ pullback.snd f₁ f₂) ⁻¹ᵁ W₂ = ⊤) : ξ ⁻¹ᵁ prodChart f₁ f₂ W₁ W₂ = ⊤ := by
  ext t
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  have ht₁ : t ∈ (ξ ≫ pullback.fst f₁ f₂) ⁻¹ᵁ W₁ := by rw [h₁]; trivial
  have ht₂ : t ∈ (ξ ≫ pullback.snd f₁ f₂) ⁻¹ᵁ W₂ := by rw [h₂]; trivial
  exact (mem_prodChart_iff f₁ f₂ (ξ t)).2 ⟨ht₁, ht₂⟩

/-- An affine open of a scheme maps to a separated scheme by an affine morphism. -/
lemma isAffineHom_of_isAffineOpen [B.IsSeparated] {X : Scheme.{u}} (f : X ⟶ B)
    {W : X.Opens} (hW : IsAffineOpen W) : IsAffineHom (W.ι ≫ f) := by
  have : IsAffine W.toScheme := hW
  exact IsAffineHom.of_comp _ (terminal.from B)

/-- Over a separated base, the product of two affine charts is an affine open. -/
theorem isAffineOpen_prodChart [B.IsSeparated] {W₁ : X₁.Opens} {W₂ : X₂.Opens}
    (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂) :
    IsAffineOpen (prodChart f₁ f₂ W₁ W₂) := by
  have : IsAffine W₂.toScheme := hW₂
  have := isAffineHom_of_isAffineOpen f₁ hW₁
  exact isAffineOpen_opensRange _

/-- **Section rings of product charts.** Over a separated base, the section ring of a point of
`X₁ ×_B X₂` on the product chart `W₁ ×_B W₂` of affine opens is the compositum of the section
rings of its projections on `W₁` and `W₂`. -/
theorem range_sectionsToField_prodChart [B.IsSeparated] {W₁ : X₁.Opens} {W₂ : X₂.Opens}
    (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂) (ξ : Spec (.of L) ⟶ pullback f₁ f₂)
    (h₁ : (ξ ≫ pullback.fst f₁ f₂) ⁻¹ᵁ W₁ = ⊤) (h₂ : (ξ ≫ pullback.snd f₁ f₂) ⁻¹ᵁ W₂ = ⊤)
    (h : ξ ⁻¹ᵁ prodChart f₁ f₂ W₁ W₂ = ⊤) :
    (sectionsToField ξ _ h).range =
      (sectionsToField _ W₁ h₁).range ⊔ (sectionsToField _ W₂ h₂).range := by
  refine le_antisymm ?_ (sup_le
    (range_sectionsToField_le_of_comp (pullback.fst f₁ f₂) rfl (prodChart_le_fst f₁ f₂) h₁ h)
    (range_sectionsToField_le_of_comp (pullback.snd f₁ f₂) rfl (prodChart_le_snd f₁ f₂) h₂ h))
  set R := (sectionsToField _ W₁ h₁).range ⊔ (sectionsToField _ W₂ h₂).range
  let incl : CommRingCat.of R ⟶ CommRingCat.of L := CommRingCat.ofHom R.subtype
  let γ₁ : Γ(X₁, W₁) ⟶ CommRingCat.of R := CommRingCat.ofHom
    ((sectionsToField _ W₁ h₁).codRestrict R fun a =>
      le_sup_left (a := (sectionsToField _ W₁ h₁).range) ⟨a, rfl⟩)
  let γ₂ : Γ(X₂, W₂) ⟶ CommRingCat.of R := CommRingCat.ofHom
    ((sectionsToField _ W₂ h₂).codRestrict R fun a =>
      le_sup_right (b := (sectionsToField _ W₂ h₂).range) ⟨a, rfl⟩)
  let ψ₁ : Spec (.of R) ⟶ X₁ := Spec.map γ₁ ≫ hW₁.fromSpec
  let ψ₂ : Spec (.of R) ⟶ X₂ := Spec.map γ₂ ≫ hW₂.fromSpec
  have key₁ : Spec.map incl ≫ ψ₁ = ξ ≫ pullback.fst f₁ f₂ := by
    rw [← SpecMap_sectionsToField_fromSpec _ hW₁ h₁, ← Spec.map_comp_assoc]
    rfl
  have key₂ : Spec.map incl ≫ ψ₂ = ξ ≫ pullback.snd f₁ f₂ := by
    rw [← SpecMap_sectionsToField_fromSpec _ hW₂ h₂, ← Spec.map_comp_assoc]
    rfl
  have : IsDominant (Spec.map incl) := isDominant_SpecMap_of_injective incl Subtype.val_injective
  have hc : ψ₁ ≫ f₁ = ψ₂ ≫ f₂ := by
    refine ext_of_isDominant_of_isSeparated (terminal.from B) (terminal.hom_ext _ _)
      (Spec.map incl) ?_
    rw [reassoc_of% key₁, reassoc_of% key₂, pullback.condition]
  let ψ : Spec (.of R) ⟶ pullback f₁ f₂ := pullback.lift ψ₁ ψ₂ hc
  have hψ : Spec.map incl ≫ ψ = ξ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, key₁]
    · rw [Category.assoc, pullback.lift_snd, key₂]
  have hψP : ψ ⁻¹ᵁ prodChart f₁ f₂ W₁ W₂ = ⊤ := by
    refine preimage_prodChart_eq_top f₁ f₂ ψ ?_ ?_
    · rw [pullback.lift_fst, Scheme.Hom.comp_preimage, hW₁.fromSpec_preimage_self]
      rfl
    · rw [pullback.lift_snd, Scheme.Hom.comp_preimage, hW₂.fromSpec_preimage_self]
      rfl
  have hle := range_sectionsToField_le_of_comp ψ hψ (U' := ⊤) hψP.ge h rfl
  refine hle.trans ((range_sectionsToField_SpecMap_top incl rfl).le.trans ?_)
  rintro _ ⟨a, rfl⟩
  exact a.2

end ProdChart

/-! ### Refinements, charts and realisations -/

section Refinement

variable {S : Scheme.{u}} (η : Spec (.of L) ⟶ S)

/-- A *refinement* of `(S, η)` (an `L`-modification of `S` in Temkin's sense, §3.2): a proper
`p : S' → S` with a dominant point `η'` over `η`, `S'` integral, such that every point of `S'` is
the centre of an extension of `η'` to a valuation ring of `L`. -/
structure IsRefinement {S' : Scheme.{u}} (p : S' ⟶ S) (η' : Spec (.of L) ⟶ S') : Prop where
  isProper : IsProper p
  comp_eq : η' ≫ p = η
  isIntegral : IsIntegral S'
  isDominant : IsDominant η'
  exists_extension : ∀ x : S', ∃ (V : RiemannZariskiSpace L)
    (ψ : Spec (.of V.valuationSubring) ⟶ S'),
    toSpecValuationSubring V ≫ ψ = η' ∧ ψ (specClosedPoint V) = x

/-- A refinement *has charts with respect to* `F ⊆ L` if over every affine open `V` of `S`
through which `η` factors there is an affine open `W ⊆ p⁻¹ V` with injective `s_W` and section
ring `s_V(Γ(S, V))[F]`. -/
def HasCharts {S' : Scheme.{u}} (p : S' ⟶ S) (η' : Spec (.of L) ⟶ S') (F : Set L) : Prop :=
  ∀ (V : S.Opens) (_ : IsAffineOpen V) (hηV : η ⁻¹ᵁ V = ⊤),
    ∃ (W : S'.Opens) (_ : IsAffineOpen W) (hη'W : η' ⁻¹ᵁ W = ⊤), W ≤ p ⁻¹ᵁ V ∧
      Function.Injective (sectionsToField η' W hη'W) ∧
      (sectionsToField η' W hη'W).range = (sectionsToField η V hηV).range ⊔ Subring.closure F

/-- `S'` *realises* `g : T → S` (with point `ηT`): there are an open `W ⊆ S'` and a proper
`h : W → T` over `S`, a point of `W` over `η'` mapped to `ηT`, and every valuation ring of
`RZ_L(T)` carries an extension of `η'` centred in `W`. -/
def Realizes {S' T : Scheme.{u}} (p : S' ⟶ S) (η' : Spec (.of L) ⟶ S') (g : T ⟶ S)
    (ηT : Spec (.of L) ⟶ T) : Prop :=
  ∃ (W : S'.Opens) (h : W.toScheme ⟶ T), IsProper h ∧ h ≫ g = W.ι ≫ p ∧
    (∃ e : Spec (.of L) ⟶ W.toScheme, e ≫ W.ι = η' ∧ e ≫ h = ηT) ∧
    ∀ V ∈ ofScheme ηT, ∃ ψ : Spec (.of V.valuationSubring) ⟶ S',
      toSpecValuationSubring V ≫ ψ = η' ∧ ψ (specClosedPoint V) ∈ W

variable {η}

/-- The schematic image of a field point, with any morphism to `S` that is proper, is a
refinement. -/
theorem isRefinement_image {Y : Scheme.{u}} (φ : Spec (.of L) ⟶ Y) (q : Y ⟶ S)
    (hq : IsProper (φ.imageι ≫ q)) (hφ : φ ≫ q = η) :
    IsRefinement η (φ.imageι ≫ q) φ.toImage where
  isProper := hq
  comp_eq := by rw [Scheme.Hom.toImage_imageι_assoc, hφ]
  isIntegral := inferInstance
  isDominant := inferInstance
  exists_extension := image_exists_extension_closedPoint_eq φ

/-- **An affine chart realises an affine piece.** Let `S` be separated, `(S', p, η')` a
refinement, `T` affine with `g : T → S` and `ηT ≫ g = η`. If an affine open `W` of `S'` with
injective `s_W` has the same section ring as `T`, then `S'` realises `g`, by a closed immersion
`W → T`. -/
theorem realizes_of_chart [S.IsSeparated] {S' T : Scheme.{u}} [IsAffine T] {p : S' ⟶ S}
    {η' : Spec (.of L) ⟶ S'} (hp : IsRefinement η p η') (g : T ⟶ S) (ηT : Spec (.of L) ⟶ T)
    (hηT : ηT ≫ g = η) {W : S'.Opens} (hW : IsAffineOpen W) (hη'W : η' ⁻¹ᵁ W = ⊤)
    (hinj : Function.Injective (sectionsToField η' W hη'W))
    (hrange : (sectionsToField η' W hη'W).range = (sectionsToField ηT ⊤ rfl).range) :
    Realizes p η' g ηT := by
  have := hp.isIntegral
  have := hp.isDominant
  set sW := sectionsToField η' W hη'W
  set sT := sectionsToField ηT ⊤ rfl
  let eW : Γ(S', W) ≃+* sW.range :=
    RingEquiv.ofBijective sW.rangeRestrict ⟨fun a b hab => hinj (congrArg Subtype.val hab),
      sW.rangeRestrict_surjective⟩
  let β : Γ(T, ⊤) →+* Γ(S', W) := eW.symm.toRingHom.comp
    (sT.codRestrict sW.range fun b => hrange ▸ ⟨b, rfl⟩)
  have hβ : ∀ b, sW (β b) = sT b := by
    intro b
    have := congrArg Subtype.val (eW.apply_symm_apply
      ⟨sT b, hrange ▸ ⟨b, rfl⟩⟩)
    exact this
  have hβs : Function.Surjective β := by
    intro w
    obtain ⟨b, hb⟩ : sW w ∈ sT.range := hrange ▸ ⟨w, rfl⟩
    exact ⟨b, hinj (by rw [hβ, hb])⟩
  let h : W.toScheme ⟶ T :=
    hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom β) ≫ T.isoSpec.inv
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom β)) :=
    IsClosedImmersion.spec_of_surjective _ hβs
  have hrW : Set.range η' ⊆ Set.range W.ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : t ∈ η' ⁻¹ᵁ W := by rw [hη'W]; trivial
    exact this
  let e : Spec (.of L) ⟶ W.toScheme := IsOpenImmersion.lift W.ι η' hrW
  have he : e ≫ W.ι = η' := IsOpenImmersion.lift_fac _ _ _
  have heS : e ≫ hW.isoSpec.hom = Spec.map (CommRingCat.ofHom sW) := by
    rw [← cancel_mono hW.isoSpec.inv, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← cancel_mono W.ι, he, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
      SpecMap_sectionsToField_fromSpec]
  have heh : e ≫ h = ηT := by
    have h1 : Spec.map (CommRingCat.ofHom sW) ≫ Spec.map (CommRingCat.ofHom β) =
        Spec.map (CommRingCat.ofHom sT) := by
      rw [← Spec.map_comp]
      congr 1
      ext b
      exact hβ b
    rw [reassoc_of% heS, reassoc_of% h1, ← IsAffineOpen.fromSpec_top]
    exact SpecMap_sectionsToField_fromSpec ηT (isAffineOpen_top T) rfl
  have : IsDominant e := by
    have : IsDominant (e ≫ W.ι) := by rw [he]; infer_instance
    exact isDominant_of_comp_isOpenImmersion e W.ι
  refine ⟨W, h, inferInstance, ?_, ⟨e, he, heh⟩, ?_⟩
  · refine ext_of_isDominant e ?_
    rw [reassoc_of% heh, hηT, reassoc_of% he, hp.comp_eq]
  · intro V hV
    rw [ofScheme_eq_ofOpen_top, mem_ofOpen_iff rfl, mem_ofRingHom] at hV
    have hVW : V ∈ ofRingHom sW := by
      rw [mem_ofRingHom]
      intro w
      obtain ⟨b, hb⟩ : sW w ∈ sT.range := hrange ▸ ⟨w, rfl⟩
      rw [← hb]
      exact hV b
    exact ⟨extensionOfMem η' hW hη'W V hVW,
      toSpecValuationSubring_comp_extensionOfMem hW hη'W V hVW,
      extensionOfMem_closedPoint hW hη'W V hVW⟩

end Refinement

/-! ### Graph closures of finitely many elements (Temkin, Lemma 3.2.3) -/

section Graph

open DeJongAlterations.Geometry.ProjectiveIdeal

/-- The range of the evaluation `ℤ[t_i] → L`, `t_i ↦ f_i`, is the subring generated by the
`f_i`. -/
lemma range_eval₂Hom_int {σ : Type*} (f : σ → L) :
    (MvPolynomial.eval₂Hom ((Int.castRingHom L).comp (ULift.ringEquiv (R := ℤ)).toRingHom)
      f).range = Subring.closure (Set.range f) := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C]
      exact intCast_mem _ _
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (Subring.subset_closure ⟨i, rfl⟩)
  · rw [Subring.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ _⟩

/-- The coordinate chart `D₊(x₀)` of `ℙⁿ_ℤ`. -/
noncomputable abbrev chartZero (n : ℕ) : (projectiveSpace (ULift.{u} ℤ) n).Opens :=
  nativeCoordinateOpen (R := ULift.{u} ℤ) (n := n) 0

/-- The chart `D₊(x₀)` is affine. -/
lemma chartZero_isAffineOpen (n : ℕ) : IsAffineOpen (chartZero.{u} n) :=
  nativeCoordinateOpen_isAffine (R := ULift.{u} ℤ) (n := n) 0

/-- The ring map `Γ(ℙⁿ, D₊(x₀)) ≅ ℤ[t₁, …, tₙ] → L` sending `tᵢ = xᵢ/x₀` to `fᵢ`. -/
noncomputable def chartEval (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L) :
    Γ(projectiveSpace (ULift.{u} ℤ) n, chartZero n) ⟶ CommRingCat.of L :=
  (nativeCoordinateSectionsIso (R := ULift.{u} ℤ) (n := n) 0).inv ≫
    CommRingCat.ofHom (MvPolynomial.eval₂Hom
      ((Int.castRingHom L).comp (ULift.ringEquiv (R := ℤ)).toRingHom) f)

/-- The point `(1 : f₁ : … : fₙ)` of `ℙⁿ_ℤ` with values in `L`. -/
noncomputable def chartPoint (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L) :
    Spec (.of L) ⟶ projectiveSpace (ULift.{u} ℤ) n :=
  Spec.map (chartEval n f) ≫ (chartZero_isAffineOpen n).fromSpec

/-- The point `(1 : f₁ : … : fₙ)` lies in `D₊(x₀)`. -/
lemma chartPoint_preimage (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L) :
    (chartPoint n f) ⁻¹ᵁ chartZero n = ⊤ :=
  preimage_SpecMap_fromSpec _ _

/-- The section ring of the point `(1 : f₁ : … : fₙ)` on `D₊(x₀)` is `ℤ[f₁, …, fₙ]`. -/
theorem range_sectionsToField_chartPoint (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L) :
    (sectionsToField (chartPoint n f) (chartZero n) (chartPoint_preimage n f)).range =
      Subring.closure (Set.range f) := by
  rw [show sectionsToField (chartPoint n f) (chartZero n) (chartPoint_preimage n f) =
    (chartEval n f).hom from sectionsToField_SpecMap_fromSpec _ _, ← range_eval₂Hom_int]
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨q, rfl⟩
    refine ⟨(nativeCoordinateSectionsIso (R := ULift.{u} ℤ) (n := n) 0).hom q, ?_⟩
    have := congrArg (fun φ => φ.hom q)
      (nativeCoordinateSectionsIso (R := ULift.{u} ℤ) (n := n) 0).hom_inv_id
    simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply,
      RingHom.id_apply] at this
    show (MvPolynomial.eval₂Hom _ f) ((nativeCoordinateSectionsIso (R := ULift.{u} ℤ) (n := n)
      0).inv.hom ((nativeCoordinateSectionsIso (R := ULift.{u} ℤ) (n := n) 0).hom.hom q)) = _
    rw [this]

variable {S : Scheme.{u}} (η : Spec (.of L) ⟶ S)

/-- The point `(η, (1 : f₁ : … : fₙ))` of `S ×_ℤ ℙⁿ_ℤ`. -/
noncomputable def graphPoint (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L) :
    Spec (.of L) ⟶ pullback (specULiftZIsTerminal.from S)
      (projectiveSpaceStructure (ULift.{u} ℤ) n) :=
  pullback.lift η (chartPoint n f) (specULiftZIsTerminal.hom_ext _ _)

/-- The projection to `S` of the graph closure: the schematic image of `graphPoint` in
`S ×_ℤ ℙⁿ_ℤ`. -/
noncomputable def graphProj (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L) :
    (graphPoint η n f).image ⟶ S :=
  (graphPoint η n f).imageι ≫ pullback.fst _ _

/-- The first projection of the graph point is `η`. -/
@[reassoc (attr := simp)]
lemma graphPoint_fst (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L) :
    graphPoint η n f ≫ pullback.fst (specULiftZIsTerminal.from S)
      (projectiveSpaceStructure (ULift.{u} ℤ) n) = η :=
  pullback.lift_fst _ _ _

/-- The second projection of the graph point is `(1 : f₁ : … : fₙ)`. -/
@[reassoc (attr := simp)]
lemma graphPoint_snd (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L) :
    graphPoint η n f ≫ pullback.snd (specULiftZIsTerminal.from S)
      (projectiveSpaceStructure (ULift.{u} ℤ) n) = chartPoint n f :=
  pullback.lift_snd _ _ _

/-- The graph closure is proper over `S`. -/
instance (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L) : IsProper (graphProj η n f) := by
  unfold graphProj
  infer_instance

/-- The graph closure is a refinement of `(S, η)`. -/
theorem graph_isRefinement (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L) :
    IsRefinement η (graphProj η n f) (graphPoint η n f).toImage :=
  isRefinement_image (graphPoint η n f) (pullback.fst _ _)
    (inferInstanceAs (IsProper (graphProj η n f))) (graphPoint_fst η n f)

/-- **Charts of the graph closure** (the chart over `V ×_ℤ D₊(x₀)`): the graph closure of
`f₁, …, fₙ` has charts with respect to `{f₁, …, fₙ}`. -/
theorem graph_hasCharts (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L) :
    HasCharts η (graphProj η n f) (graphPoint η n f).toImage (Set.range f) := by
  intro V hV hηV
  have hφ₁ : (graphPoint η n f ≫ pullback.fst (specULiftZIsTerminal.from S)
      (projectiveSpaceStructure (ULift.{u} ℤ) n)) ⁻¹ᵁ V = ⊤ := by
    rw [graphPoint_fst]
    exact hηV
  have hφ₂ : (graphPoint η n f ≫ pullback.snd (specULiftZIsTerminal.from S)
      (projectiveSpaceStructure (ULift.{u} ℤ) n)) ⁻¹ᵁ chartZero n = ⊤ := by
    rw [graphPoint_snd]
    exact chartPoint_preimage n f
  have hP := isAffineOpen_prodChart (specULiftZIsTerminal.from S)
    (projectiveSpaceStructure (ULift.{u} ℤ) n) hV (chartZero_isAffineOpen n)
  have hφP := preimage_prodChart_eq_top _ _ (graphPoint η n f) hφ₁ hφ₂
  refine ⟨(graphPoint η n f).imageι ⁻¹ᵁ prodChart _ _ V (chartZero n),
    imageChart_isAffineOpen _ hP, toImage_preimage_imageChart _ hφP, ?_,
    injective_sectionsToField_imageChart _ hP hφP, ?_⟩
  · intro x hx
    have := prodChart_le_fst (specULiftZIsTerminal.from S)
      (projectiveSpaceStructure (ULift.{u} ℤ) n) hx
    rw [graphProj, Scheme.Hom.comp_preimage]
    exact this
  · rw [range_sectionsToField_imageChart _ hP hφP,
      range_sectionsToField_prodChart _ _ hV (chartZero_isAffineOpen n) _ hφ₁ hφ₂ hφP,
      sectionsToField_congr (graphPoint_fst η n f) hφ₁ hηV,
      sectionsToField_congr (graphPoint_snd η n f) hφ₂ (chartPoint_preimage n f),
      range_sectionsToField_chartPoint]

/-- **An affine piece is realised by a graph closure** (proof of Temkin, Proposition 3.2.6, for
one affine piece). Let `S` be separated, `T` affine, `g : T → S` locally of finite type with
image in an affine open `V`, and `ηT` a point of `T` over `η`. For suitable `f₁, …, fₙ ∈ L`
(the images of generators of `Γ(T, ⊤)` over `Γ(S, V)`), the graph closure realises `g`. -/
theorem exists_graph_realizes [S.IsSeparated] {T : Scheme.{u}} [IsAffine T] (g : T ⟶ S)
    [LocallyOfFiniteType g] (ηT : Spec (.of L) ⟶ T) (hηT : ηT ≫ g = η) {V : S.Opens}
    (hV : IsAffineOpen V) (hgV : g ⁻¹ᵁ V = ⊤) :
    ∃ (n : ℕ) (f : ChartIndex (0 : Fin (n + 1)) → L),
      Realizes (graphProj η n f) (graphPoint η n f).toImage g ηT := by
  have hηV : η ⁻¹ᵁ V = ⊤ := by
    rw [← hηT, Scheme.Hom.comp_preimage, hgV]
    rfl
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType g inferInstance ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top T⟩ hgV.ge
  let := (g.appLE V ⊤ hgV.ge).hom.toAlgebra
  obtain ⟨t, ht⟩ := hft.out
  set sT := sectionsToField ηT ⊤ rfl
  let f : ChartIndex (0 : Fin (t.card + 1)) → L :=
    fun i => sT (t.equivFin.symm ((finSuccAboveEquiv 0).symm i))
  refine ⟨t.card, f, ?_⟩
  obtain ⟨W, hW, hη'W, -, hinj, hrange⟩ := graph_hasCharts η t.card f V hV hηV
  refine realizes_of_chart (graph_isRefinement η t.card f) g ηT hηT hW hη'W hinj ?_
  rw [hrange]
  have hcomp := sectionsToField_comp_appLE g hηT hgV.ge rfl hηV
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [← hcomp]
      rintro _ ⟨a, rfl⟩
      exact ⟨_, rfl⟩
    · rw [Subring.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨_, rfl⟩
  · rintro _ ⟨b, rfl⟩
    have hb : b ∈ Algebra.adjoin Γ(S, V) (t : Set Γ(T, ⊤)) := by
      rw [ht]
      trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      refine (le_sup_right : Subring.closure (Set.range f) ≤ _)
        (Subring.subset_closure ⟨(finSuccAboveEquiv 0) (t.equivFin ⟨x, hx⟩), ?_⟩)
      simp only [f, Equiv.symm_apply_apply]
      rfl
    | algebraMap a =>
      refine (le_sup_left : (sectionsToField η V hηV).range ≤ _) ?_
      rw [← hcomp]
      exact ⟨a, rfl⟩
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy

end Graph

/-! ### Domination and the refinement theorem (Temkin, Proposition 3.2.6) -/

section Dominate

variable {S : Scheme.{u}} {η : Spec (.of L) ⟶ S}

/-- **Realisations pass to dominating refinements.** If `q : S₂ → S₁` is proper over `S` and
compatible with the points, every morphism realised by `S₁` is realised by `S₂`. -/
theorem Realizes.of_dominates {S₁ S₂ T : Scheme.{u}} {p₁ : S₁ ⟶ S} {p₂ : S₂ ⟶ S}
    {η₁ : Spec (.of L) ⟶ S₁} {η₂ : Spec (.of L) ⟶ S₂} (q : S₂ ⟶ S₁) [IsProper q]
    (hq : q ≫ p₁ = p₂) (hη : η₂ ≫ q = η₁) {g : T ⟶ S} {ηT : Spec (.of L) ⟶ T}
    (hreal : Realizes p₁ η₁ g ηT) : Realizes p₂ η₂ g ηT := by
  obtain ⟨W, h, hh, hcomm, ⟨e, he, heh⟩, hRZ⟩ := hreal
  have hr : Set.range η₂ ⊆ Set.range (q ⁻¹ᵁ W).ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change q (η₂ t) ∈ W
    rw [← Scheme.Hom.comp_apply, hη, ← he, Scheme.Hom.comp_apply]
    exact (e t).2
  let e₂ : Spec (.of L) ⟶ (q ⁻¹ᵁ W).toScheme := IsOpenImmersion.lift _ η₂ hr
  have he₂ : e₂ ≫ (q ⁻¹ᵁ W).ι = η₂ := IsOpenImmersion.lift_fac _ _ _
  have he₂q : e₂ ≫ q ∣_ W = e := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% he₂, hη, he]
  refine ⟨q ⁻¹ᵁ W, q ∣_ W ≫ h, inferInstance, ?_, ⟨e₂, he₂, by rw [reassoc_of% he₂q, heh]⟩, ?_⟩
  · rw [Category.assoc, hcomm, morphismRestrict_ι_assoc, hq]
  · intro V hV
    obtain ⟨ψ, hψ, hψW⟩ := hRZ V hV
    have hex : ValuativeCriterion.Existence q := by
      have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) q := by
        rw [← UniversallyClosed.eq_valuativeCriterion]
        infer_instance
      exact this.1
    let sq : ValuativeCommSq q :=
      { R := V.valuationSubring, K := L, i₁ := η₂, i₂ := ψ, commSq := ⟨by rw [hη, hψ]⟩ }
    obtain ⟨l⟩ := (hex sq).exists_lift
    refine ⟨l.l, l.fac_left, ?_⟩
    change q (l.l (specClosedPoint V)) ∈ W
    rw [← Scheme.Hom.comp_apply, l.fac_right]
    exact hψW

variable {S₁ S₂ : Scheme.{u}} {p₁ : S₁ ⟶ S} {p₂ : S₂ ⟶ S}
  {η₁ : Spec (.of L) ⟶ S₁} {η₂ : Spec (.of L) ⟶ S₂}

/-- The point `(η₁, η₂)` of `S₁ ×_S S₂`; its schematic image dominates both refinements. -/
noncomputable def dominatePoint (hη : η₁ ≫ p₁ = η₂ ≫ p₂) :
    Spec (.of L) ⟶ pullback p₁ p₂ :=
  pullback.lift η₁ η₂ hη

/-- The first projection of `(η₁, η₂)`. -/
@[reassoc (attr := simp)]
lemma dominatePoint_fst (hη : η₁ ≫ p₁ = η₂ ≫ p₂) :
    dominatePoint hη ≫ pullback.fst p₁ p₂ = η₁ :=
  pullback.lift_fst _ _ _

/-- The second projection of `(η₁, η₂)`. -/
@[reassoc (attr := simp)]
lemma dominatePoint_snd (hη : η₁ ≫ p₁ = η₂ ≫ p₂) :
    dominatePoint hη ≫ pullback.snd p₁ p₂ = η₂ :=
  pullback.lift_snd _ _ _

/-- The schematic image of `(η₁, η₂)` in `S₁ ×_S S₂` is a refinement. -/
theorem dominate_isRefinement (h₁ : IsRefinement η p₁ η₁) (h₂ : IsRefinement η p₂ η₂)
    (hη : η₁ ≫ p₁ = η₂ ≫ p₂) :
    IsRefinement η ((dominatePoint hη).imageι ≫ pullback.fst p₁ p₂ ≫ p₁)
      (dominatePoint hη).toImage := by
  have := h₁.isProper
  have := h₂.isProper
  exact isRefinement_image _ _ inferInstance (by rw [dominatePoint_fst_assoc, h₁.comp_eq])

/-- The dominating refinement has charts with respect to the union of the two sets. -/
theorem dominate_hasCharts [S.IsSeparated] {F₁ F₂ : Set L} (hη : η₁ ≫ p₁ = η₂ ≫ p₂)
    (h₁ : HasCharts η p₁ η₁ F₁) (h₂ : HasCharts η p₂ η₂ F₂) :
    HasCharts η ((dominatePoint hη).imageι ≫ pullback.fst p₁ p₂ ≫ p₁)
      (dominatePoint hη).toImage (F₁ ∪ F₂) := by
  intro V hV hηV
  obtain ⟨W₁, hW₁, hη₁W₁, hW₁V, -, hr₁⟩ := h₁ V hV hηV
  obtain ⟨W₂, hW₂, hη₂W₂, -, -, hr₂⟩ := h₂ V hV hηV
  have hφ₁ : (dominatePoint hη ≫ pullback.fst p₁ p₂) ⁻¹ᵁ W₁ = ⊤ := by
    rw [dominatePoint_fst]
    exact hη₁W₁
  have hφ₂ : (dominatePoint hη ≫ pullback.snd p₁ p₂) ⁻¹ᵁ W₂ = ⊤ := by
    rw [dominatePoint_snd]
    exact hη₂W₂
  have hP := isAffineOpen_prodChart p₁ p₂ hW₁ hW₂
  have hφP := preimage_prodChart_eq_top _ _ (dominatePoint hη) hφ₁ hφ₂
  refine ⟨(dominatePoint hη).imageι ⁻¹ᵁ prodChart p₁ p₂ W₁ W₂, imageChart_isAffineOpen _ hP,
    toImage_preimage_imageChart _ hφP, ?_, injective_sectionsToField_imageChart _ hP hφP, ?_⟩
  · intro x hx
    have h1 := prodChart_le_fst p₁ p₂ hx
    have h2 := hW₁V h1
    change p₁ (pullback.fst p₁ p₂ ((dominatePoint hη).imageι x)) ∈ V at h2
    change ((dominatePoint hη).imageι ≫ pullback.fst p₁ p₂ ≫ p₁) x ∈ V
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact h2
  · rw [range_sectionsToField_imageChart _ hP hφP,
      range_sectionsToField_prodChart _ _ hW₁ hW₂ _ hφ₁ hφ₂ hφP,
      sectionsToField_congr (dominatePoint_fst hη) hφ₁ hη₁W₁,
      sectionsToField_congr (dominatePoint_snd hη) hφ₂ hη₂W₂, hr₁, hr₂,
      Subring.closure_union, ← sup_sup_distrib_left]

/-- Realisations of the first refinement pass to the dominating one. -/
theorem dominate_realizes_left (hη : η₁ ≫ p₁ = η₂ ≫ p₂) (hp₂ : IsProper p₂) {T : Scheme.{u}}
    {g : T ⟶ S} {ηT : Spec (.of L) ⟶ T} (h : Realizes p₁ η₁ g ηT) :
    Realizes ((dominatePoint hη).imageι ≫ pullback.fst p₁ p₂ ≫ p₁)
      (dominatePoint hη).toImage g ηT :=
  Realizes.of_dominates ((dominatePoint hη).imageι ≫ pullback.fst p₁ p₂)
    (by rw [Category.assoc]) (by rw [Scheme.Hom.toImage_imageι_assoc, dominatePoint_fst]) h

/-- Realisations of the second refinement pass to the dominating one. -/
theorem dominate_realizes_right (hη : η₁ ≫ p₁ = η₂ ≫ p₂) (hp₁ : IsProper p₁) {T : Scheme.{u}}
    {g : T ⟶ S} {ηT : Spec (.of L) ⟶ T} (h : Realizes p₂ η₂ g ηT) :
    Realizes ((dominatePoint hη).imageι ≫ pullback.fst p₁ p₂ ≫ p₁)
      (dominatePoint hη).toImage g ηT :=
  Realizes.of_dominates ((dominatePoint hη).imageι ≫ pullback.snd p₁ p₂)
    (by rw [Category.assoc, ← pullback.condition])
    (by rw [Scheme.Hom.toImage_imageι_assoc, dominatePoint_snd]) h

end Dominate

section Main

variable {S : Scheme.{u}} (η : Spec (.of L) ⟶ S)

/-- The schematic image of `η` in `S` is a refinement with charts with respect to `∅`. -/
theorem image_isRefinement_hasCharts :
    IsRefinement η (η.imageι ≫ 𝟙 S) η.toImage ∧ HasCharts η (η.imageι ≫ 𝟙 S) η.toImage ∅ := by
  refine ⟨isRefinement_image η (𝟙 S) inferInstance (Category.comp_id _), ?_⟩
  intro V hV hηV
  refine ⟨η.imageι ⁻¹ᵁ V, imageChart_isAffineOpen η hV, toImage_preimage_imageChart η hηV,
    fun x hx => hx, injective_sectionsToField_imageChart η hV hηV, ?_⟩
  rw [range_sectionsToField_imageChart η hV hηV, Subring.closure_empty, sup_bot_eq]

variable [S.IsSeparated] {ι : Type*} (T : ι → Scheme.{u}) [∀ i, IsAffine (T i)]
  (g : ∀ i, T i ⟶ S) [∀ i, LocallyOfFiniteType (g i)] (ηT : ∀ i, Spec (.of L) ⟶ T i)

/-- **Refinement, finite-set form** (induction step of Temkin, Proposition 3.2.6). -/
theorem exists_refinement_finset (hηT : ∀ i, ηT i ≫ g i = η) (V : ι → S.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hgV : ∀ i, g i ⁻¹ᵁ V i = ⊤) (s : Finset ι) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (η' : Spec (.of L) ⟶ S') (F : Set L),
      IsRefinement η p η' ∧ F.Finite ∧ HasCharts η p η' F ∧
      ∀ i ∈ s, Realizes p η' (g i) (ηT i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := image_isRefinement_hasCharts η
    exact ⟨_, _, _, ∅, h1, Set.finite_empty, h2, by simp⟩
  | insert i s hi ih =>
    obtain ⟨S', p, η', F, hR, hF, hC, hReal⟩ := ih
    obtain ⟨n, f, hfr⟩ := exists_graph_realizes η (g i) (ηT i) (hηT i) (hV i) (hgV i)
    have hη : η' ≫ p = (graphPoint η n f).toImage ≫ graphProj η n f := by
      rw [hR.comp_eq, (graph_isRefinement η n f).comp_eq]
    refine ⟨_, _, _, F ∪ Set.range f,
      dominate_isRefinement hR (graph_isRefinement η n f) hη, hF.union (Set.finite_range f),
      dominate_hasCharts hη hC (graph_hasCharts η n f), ?_⟩
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact dominate_realizes_right hη hR.isProper hfr
    · exact dominate_realizes_left hη (graph_isRefinement η n f).isProper (hReal j hj)

/-- A proper scheme over a separated scheme is separated. -/
lemma isSeparated_of_isProper {S' : Scheme.{u}} (p : S' ⟶ S) [IsProper p] : S'.IsSeparated :=
  ⟨by rw [← terminal.comp_from p]; infer_instance⟩

/-- **Refinement of Riemann–Zariski covers** (Temkin, Proposition 3.2.6 `oetamodprop`, affine
pieces, with the covering addendum used in Proposition 4.5.1). Let `S` be separated,
`η : Spec L → S`, and `gᵢ : Tᵢ → S` (`i` in a finite type) locally of finite type with `Tᵢ`
affine, image in an affine open `Vᵢ`, and points `ηTᵢ` over `η`. There is a refinement
`p : S' → S` (proper, `S'` integral, `η'` dominant, every point a centre) with charts with respect
to a finite set, and opens `Wᵢ ⊆ S'` with proper `hᵢ : Wᵢ → Tᵢ` over `S` and dominant points
`eᵢ` over `η'` and `ηTᵢ` (so `Wᵢ` is an `L`-modification of `Tᵢ`), such that every valuation ring
of `RZ_L(Tᵢ)` has an extension of `η'` centred in `Wᵢ`. If the `RZ_L(Tᵢ)` cover `RZ_L(S)`, the
`Wᵢ` cover `S'`. -/
theorem exists_refinement [Finite ι] (hηT : ∀ i, ηT i ≫ g i = η) (V : ι → S.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hgV : ∀ i, g i ⁻¹ᵁ V i = ⊤) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (η' : Spec (.of L) ⟶ S') (F : Set L)
      (W : ι → S'.Opens) (h : ∀ i, (W i).toScheme ⟶ T i),
      IsRefinement η p η' ∧ F.Finite ∧ HasCharts η p η' F ∧
      (∀ i, IsProper (h i) ∧ h i ≫ g i = (W i).ι ≫ p ∧
        ∃ e : Spec (.of L) ⟶ (W i).toScheme, e ≫ (W i).ι = η' ∧ e ≫ h i = ηT i ∧
          IsDominant e) ∧
      (∀ i, ∀ V' ∈ ofScheme (ηT i), ∃ ψ : Spec (.of V'.valuationSubring) ⟶ S',
        toSpecValuationSubring V' ≫ ψ = η' ∧ ψ (specClosedPoint V') ∈ W i) ∧
      (ofScheme η ⊆ ⋃ i, ofScheme (ηT i) → ⨆ i, W i = ⊤) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨S', p, η', F, hR, hF, hC, hReal⟩ :=
    exists_refinement_finset η T g ηT hηT V hV hgV Finset.univ
  choose W h hh hcomm he hRZ using fun i => hReal i (Finset.mem_univ i)
  have := hR.isDominant
  refine ⟨S', p, η', F, W, h, hR, hF, hC, fun i => ⟨hh i, hcomm i, ?_⟩, hRZ, ?_⟩
  · obtain ⟨e, he1, he2⟩ := he i
    have : IsDominant (e ≫ (W i).ι) := by rw [he1]; infer_instance
    exact ⟨e, he1, he2, isDominant_of_comp_isOpenImmersion e (W i).ι⟩
  · intro hcov
    have := hR.isProper
    have := isSeparated_of_isProper p
    rw [eq_top_iff]
    intro x _
    obtain ⟨V', ψ, hψ, rfl⟩ := hR.exists_extension x
    have hV' : V' ∈ ofScheme η := ⟨ψ ≫ p, by rw [← Category.assoc, hψ, hR.comp_eq]⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hV')
    obtain ⟨ψ', hψ', hψ'W⟩ := hRZ i V' hi
    rw [extension_unique hψ hψ']
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hψ'W⟩

end Main

/-! ### Refinements over a function field are generically étale alterations -/

section GenericallyEtale

open scoped nonZeroDivisors

/-- **Generic étaleness of a separable domain extension.** Let `A` be a Noetherian domain with
fraction field `K`, `L` a separable algebraic extension of `K`, and `B` a domain of finite type
over `A` embedded in `L` over `A`. Then `B_c` is étale over `A` for some `c ≠ 0`. -/
theorem exists_etale_localization_of_separable (A B K L : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.FiniteType A B]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
    [IsScalarTower A B L] (hσ : Function.Injective (algebraMap B L)) :
    ∃ c : B, c ≠ 0 ∧ Algebra.Etale A (Localization.Away c) := by
  let E := FractionRing B
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hAB : Function.Injective (algebraMap A B) := by
    intro a b h
    apply hAL
    rw [IsScalarTower.algebraMap_apply A B L, h, ← IsScalarTower.algebraMap_apply]
  have hu : ∀ a : A⁰, IsUnit (algebraMap A E a) := by
    intro ⟨a, ha⟩
    rw [IsScalarTower.algebraMap_apply A B E]
    refine IsLocalization.map_units E (⟨algebraMap A B a, mem_nonZeroDivisors_of_ne_zero ?_⟩ : B⁰)
    rw [Ne, ← map_zero (algebraMap A B), hAB.eq_iff]
    exact nonZeroDivisors.ne_zero ha
  let : Algebra K E := (IsLocalization.lift (M := A⁰) hu).toAlgebra
  have : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.lift_eq (M := A⁰) hu a).symm
  have hBu : ∀ b : B⁰, IsUnit (algebraMap B L b) := by
    intro ⟨b, hb⟩
    refine IsUnit.mk0 _ fun h0 => nonZeroDivisors.ne_zero hb ?_
    exact hσ (by rw [h0, map_zero])
  let τ : E →+* L := IsLocalization.lift (M := B⁰) hBu
  have hτ : τ.comp (algebraMap K E) = algebraMap K L := by
    refine IsLocalization.ringHom_ext A⁰ ?_
    ext a
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply A K E, IsScalarTower.algebraMap_apply A B E, τ,
      IsLocalization.lift_eq, ← IsScalarTower.algebraMap_apply A B L]
  let τ' : E →ₐ[K] L := { τ with commutes' := fun x => congrArg (fun φ => φ x) hτ }
  have : Algebra.IsSeparable K E := Algebra.IsSeparable.of_algHom K L τ'
  have : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  have : Algebra.FormallyEtale A K := Algebra.FormallyEtale.of_isLocalization A⁰
  have : Algebra.FormallyEtale A E := Algebra.FormallyEtale.comp A K E
  have : IsLocalization B⁰ (Localization.AtPrime (⊥ : Ideal B)) := by
    convert (inferInstance : IsLocalization (⊥ : Ideal B).primeCompl
      (Localization.AtPrime (⊥ : Ideal B))) using 1
    ext b
    simp only [Ideal.mem_primeCompl_iff, Ideal.mem_bot, mem_nonZeroDivisors_iff_ne_zero]
  let e := (IsLocalization.algEquiv B⁰ E (Localization.AtPrime (⊥ : Ideal B))).restrictScalars A
  have : Algebra.IsEtaleAt A (⊥ : Ideal B) := Algebra.FormallyEtale.of_equiv e
  obtain ⟨c, hc, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
  exact ⟨c, by simpa only [Ideal.mem_bot] using hc, he⟩

/-- The generic point `Spec L → Spec K(S) → S` of an integral scheme `S` with values in an
extension `L` of its function field (for instance a separable closure). -/
noncomputable def functionFieldPoint (S : Scheme.{u}) [IsIntegral S] (L : Type u) [Field L]
    [Algebra S.functionField L] : Spec (.of L) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫ S.fromSpecStalk (genericPoint S)

variable {S : Scheme.{u}} [IsIntegral S] [Algebra S.functionField L]

/-- On an affine open containing the generic point, the generic point is `Spec` of the germ. -/
lemma functionFieldPoint_eq {V : S.Opens} (hV : IsAffineOpen V) (hgV : genericPoint S ∈ V) :
    functionFieldPoint S L = Spec.map (CommRingCat.ofHom ((algebraMap S.functionField L).comp
      (S.presheaf.germ V (genericPoint S) hgV).hom)) ≫ hV.fromSpec := by
  rw [functionFieldPoint, ← hV.fromSpecStalk_eq_fromSpecStalk hgV, IsAffineOpen.fromSpecStalk,
    ← Category.assoc]
  congr 1
  exact (Spec.map_comp _ _).symm

/-- The generic point factors through every affine open containing it. -/
lemma functionFieldPoint_preimage {V : S.Opens} (hV : IsAffineOpen V)
    (hgV : genericPoint S ∈ V) : (functionFieldPoint S L) ⁻¹ᵁ V = ⊤ := by
  rw [functionFieldPoint_eq hV hgV]
  exact preimage_SpecMap_fromSpec hV _

/-- The section map of the generic point on an affine open is the germ followed by `K(S) → L`. -/
theorem sectionsToField_functionFieldPoint {V : S.Opens} (hV : IsAffineOpen V)
    (hgV : genericPoint S ∈ V) :
    sectionsToField (functionFieldPoint S L) V (functionFieldPoint_preimage hV hgV) =
      (algebraMap S.functionField L).comp (S.presheaf.germ V (genericPoint S) hgV).hom := by
  rw [sectionsToField_congr (functionFieldPoint_eq hV hgV) (functionFieldPoint_preimage hV hgV)
    (preimage_SpecMap_fromSpec hV _), sectionsToField_SpecMap_fromSpec]
  rfl

/-- The section map of the generic point is injective. -/
lemma injective_sectionsToField_functionFieldPoint {V : S.Opens} (hV : IsAffineOpen V)
    (hgV : genericPoint S ∈ V) :
    Function.Injective (sectionsToField (functionFieldPoint S L) V
      (functionFieldPoint_preimage hV hgV)) := by
  rw [sectionsToField_functionFieldPoint hV hgV]
  exact (algebraMap S.functionField L).injective.comp (germ_injective_of_isIntegral S _ hgV)

/-- The generic point `Spec L → S` hits the generic point of `S`. -/
lemma functionFieldPoint_apply (z : Spec (.of L)) :
    functionFieldPoint S L z = genericPoint S := by
  rw [functionFieldPoint, Scheme.Hom.comp_apply]
  have : Subsingleton (Spec S.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum S.functionField))
  rw [Subsingleton.elim ((Spec.map (CommRingCat.ofHom (algebraMap S.functionField L))) z)
    (IsLocalRing.closedPoint S.functionField)]
  exact Scheme.fromSpecStalk_closedPoint

/-- The generic point is dominant. -/
instance : IsDominant (functionFieldPoint S L) := by
  refine ⟨?_⟩
  have hr : Set.range (functionFieldPoint S L) = {genericPoint S} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact functionFieldPoint_apply z
    · rintro rfl
      obtain ⟨z⟩ : Nonempty (Spec (.of L)) := inferInstance
      exact ⟨z, functionFieldPoint_apply z⟩
  rw [DenseRange, hr, dense_iff_closure_eq]
  exact (genericPoint_spec S).def

/-- Over an integral scheme, choose a nonempty affine open `V` over which a given finite set of
elements of a separable algebraic extension `L` of `K(S)` is integral. -/
theorem exists_affine_isIntegral [Algebra.IsSeparable S.functionField L] {F : Set L}
    (hF : F.Finite) :
    ∃ (V : S.Opens) (hV : IsAffineOpen V) (hgV : genericPoint S ∈ V), ∀ x ∈ F,
      @IsIntegral Γ(S, V) L _ _ (sectionsToField (functionFieldPoint S L) V
        (functionFieldPoint_preimage hV hgV)).toAlgebra x := by
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hg₀, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint S)) isOpen_univ
  have : Nonempty V₀ := ⟨⟨_, hg₀⟩⟩
  set s₀ := sectionsToField (functionFieldPoint S L) V₀ (functionFieldPoint_preimage hV₀ hg₀)
  let _ : Algebra Γ(S, V₀) L := s₀.toAlgebra
  have : IsScalarTower Γ(S, V₀) S.functionField L := IsScalarTower.of_algebraMap_eq fun a => by
    change s₀ a = _
    rw [show s₀ = _ from sectionsToField_functionFieldPoint hV₀ hg₀]
    rfl
  have : IsFractionRing Γ(S, V₀) S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S V₀ hV₀
  have halg : ∀ x : F, IsAlgebraic Γ(S, V₀) (x : L) := fun x =>
    (IsFractionRing.isAlgebraic_iff Γ(S, V₀) S.functionField L).2
      (Algebra.IsSeparable.isIntegral S.functionField (x : L)).isAlgebraic
  choose y hy0 hyint using fun x : F => (halg x).exists_integral_multiple
  have := hF.fintype
  let a : Γ(S, V₀) := ∏ x : F, y x
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => hy0 x
  have hV₁ : IsAffineOpen (S.basicOpen a) := hV₀.basicOpen a
  have hne : (S.basicOpen a : Set S).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ← TopologicalSpace.Opens.coe_bot, Ne,
      TopologicalSpace.Opens.coe_inj, basicOpen_eq_bot_iff]
    exact ha0
  have hg₁ : genericPoint S ∈ S.basicOpen a :=
    ((genericPoint_spec S).mem_open_set_iff (S.basicOpen a).isOpen).2 (by simpa using hne)
  refine ⟨S.basicOpen a, hV₁, hg₁, fun x hx => ?_⟩
  set s₁ := sectionsToField (functionFieldPoint S L) (S.basicOpen a)
    (functionFieldPoint_preimage hV₁ hg₁)
  let ρ := S.presheaf.map (homOfLE (S.basicOpen_le a)).op
  let _ : Algebra Γ(S, S.basicOpen a) L := s₁.toAlgebra
  let _ : Algebra Γ(S, V₀) Γ(S, S.basicOpen a) := ρ.hom.toAlgebra
  have hρ : ∀ b, s₁ (ρ b) = s₀ b := by
    intro b
    rw [show s₁ = _ from sectionsToField_functionFieldPoint hV₁ hg₁,
      show s₀ = _ from sectionsToField_functionFieldPoint hV₀ hg₀, RingHom.comp_apply,
      RingHom.comp_apply]
    congr 1
    exact TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE (S.basicOpen_le a))
      (genericPoint S) hg₁ b
  have : IsScalarTower Γ(S, V₀) Γ(S, S.basicOpen a) L :=
    IsScalarTower.of_algebraMap_eq fun b => (hρ b).symm
  have h1 : IsIntegral Γ(S, S.basicOpen a) (y ⟨x, hx⟩ • x) := (hyint ⟨x, hx⟩).tower_top
  have hunit : IsUnit (ρ (y ⟨x, hx⟩)) := by
    refine isUnit_of_dvd_unit (map_dvd ρ.hom ?_) (S.toRingedSpace.isUnit_res_basicOpen a)
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  obtain ⟨u, hu⟩ := hunit
  have hx' : x = algebraMap Γ(S, S.basicOpen a) L ↑u⁻¹ * (y ⟨x, hx⟩ • x) := by
    rw [Algebra.smul_def, ← mul_assoc, IsScalarTower.algebraMap_apply Γ(S, V₀)
      Γ(S, S.basicOpen a) L, ← map_mul]
    change x = algebraMap _ L (↑u⁻¹ * ρ (y ⟨x, hx⟩)) * x
    rw [← hu, Units.inv_mul, map_one, one_mul]
  rw [hx']
  exact (isIntegral_algebraMap).mul h1

/-- **Refinements are generically étale alterations.** Let `S` be integral, separated and locally
Noetherian, `L` a separable algebraic extension of `K(S)`, and `η` the generic point
`Spec L → S`. A refinement of `(S, η)` with charts with respect to a finite set is a generically
étale alteration. -/
theorem isAlteration_isGenericallyEtale_of_hasCharts [IsLocallyNoetherian S] [S.IsSeparated]
    [Algebra.IsSeparable S.functionField L] {S' : Scheme.{u}} {p : S' ⟶ S}
    {η' : Spec (.of L) ⟶ S'} (hR : IsRefinement (functionFieldPoint S L) p η') {F : Set L}
    (hF : F.Finite) (hC : HasCharts (functionFieldPoint S L) p η' F) :
    IsAlteration p ∧ IsGenericallyEtale p := by
  have := hR.isProper
  have := hR.isIntegral
  have := hR.isDominant
  have := isSeparated_of_isProper p
  obtain ⟨V, hV, hgV, hint⟩ := exists_affine_isIntegral (L := L) (S := S) hF
  have hηV := functionFieldPoint_preimage (L := L) hV hgV
  obtain ⟨W, hW, hη'W, hWV, hinj, hrange⟩ := hC V hV hηV
  set s₁ := sectionsToField (functionFieldPoint S L) V hηV with hs₁
  set sW := sectionsToField η' W hη'W with hsW
  have hcomp : sW.comp (p.appLE V W hWV).hom = s₁ :=
    sectionsToField_comp_appLE p hR.comp_eq hWV hη'W hηV
  -- the chart ring lies in every valuation ring containing `s₁(Γ(S, V))`
  have hFV : ∀ V' : RiemannZariskiSpace L, V' ∈ ofRingHom s₁ →
      ∀ w, sW w ∈ V'.valuationSubring := by
    intro V' hV' w
    have hF' : F ⊆ V'.valuationSubring := by
      intro x hx
      let _ : Algebra Γ(S, V) L := s₁.toAlgebra
      let _ : Algebra Γ(S, V) V'.valuationSubring :=
        (s₁.codRestrict V'.valuationSubring (mem_ofRingHom.1 hV')).toAlgebra
      have : IsScalarTower Γ(S, V) V'.valuationSubring L :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      have hx' : IsIntegral V'.valuationSubring x := (hint x hx).tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
      rw [← hy]
      exact y.2
    have hle : sW.range ≤ V'.valuationSubring.toSubring := by
      rw [hrange]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact mem_ofRingHom.1 hV' a
      · rw [Subring.closure_le]
        exact hF'
    exact hle ⟨w, rfl⟩
  -- the chart is the full preimage of `V`
  have hWeq : p ⁻¹ᵁ V = W := by
    refine le_antisymm (fun x hx => ?_) hWV
    obtain ⟨V', ψ, hψ, rfl⟩ := hR.exists_extension x
    have hψp : toSpecValuationSubring V' ≫ (ψ ≫ p) = functionFieldPoint S L := by
      rw [← Category.assoc, hψ, hR.comp_eq]
    have hmem := mem_ofOpen_of_extension (ψ ≫ p) hψp (U := V) hx
    rw [mem_ofOpen_iff hηV] at hmem
    have hV'W : V' ∈ ofRingHom sW := mem_ofRingHom.2 (hFV V' hmem)
    rw [extension_unique hψ (toSpecValuationSubring_comp_extensionOfMem hW hη'W V' hV'W)]
    exact extensionOfMem_closedPoint hW hη'W V' hV'W
  subst hWeq
  let _ : Algebra Γ(S, V) Γ(S', p ⁻¹ᵁ V) := (p.appLE V (p ⁻¹ᵁ V) hWV).hom.toAlgebra
  let _ : Algebra Γ(S, V) L := s₁.toAlgebra
  let _ : Algebra Γ(S', p ⁻¹ᵁ V) L := sW.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(S', p ⁻¹ᵁ V) L :=
    IsScalarTower.of_algebraMap_eq fun a => (congrArg (fun φ => φ a) hcomp).symm
  -- finite type
  have hG : (sW ⁻¹' F).Finite := hF.preimage hinj.injOn
  have htop : Algebra.adjoin Γ(S, V) (sW ⁻¹' F) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have key : ∀ y ∈ Subring.closure ((s₁.range : Set L) ∪ F),
        ∃ w ∈ Algebra.adjoin Γ(S, V) (sW ⁻¹' F), sW w = y := by
      intro y hy
      induction hy using Subring.closure_induction with
      | mem y hy =>
        rcases hy with ⟨a, rfl⟩ | hy
        · exact ⟨algebraMap _ _ a, Subalgebra.algebraMap_mem _ a,
            (congrArg (fun φ => φ a) hcomp)⟩
        · obtain ⟨w, rfl⟩ : y ∈ sW.range := by
            rw [hrange]
            exact (le_sup_right : Subring.closure F ≤ _) (Subring.subset_closure hy)
          exact ⟨w, Algebra.subset_adjoin hy, rfl⟩
      | zero => exact ⟨0, zero_mem _, map_zero _⟩
      | one => exact ⟨1, one_mem _, map_one _⟩
      | add y z _ _ hy hz =>
        obtain ⟨w₁, h₁, rfl⟩ := hy
        obtain ⟨w₂, h₂, rfl⟩ := hz
        exact ⟨w₁ + w₂, add_mem h₁ h₂, map_add _ _ _⟩
      | neg y _ hy =>
        obtain ⟨w₁, h₁, rfl⟩ := hy
        exact ⟨-w₁, neg_mem h₁, map_neg _ _⟩
      | mul y z _ _ hy hz =>
        obtain ⟨w₁, h₁, rfl⟩ := hy
        obtain ⟨w₂, h₂, rfl⟩ := hz
        exact ⟨w₁ * w₂, mul_mem h₁ h₂, map_mul _ _ _⟩
    obtain ⟨w', hw', he⟩ := key (sW w) (by
      rw [Subring.closure_union, Subring.closure_eq, ← hrange]
      exact ⟨w, rfl⟩)
    rwa [hinj he] at hw'
  have : Algebra.FiniteType Γ(S, V) Γ(S', p ⁻¹ᵁ V) := ⟨⟨hG.toFinset, by simpa using htop⟩⟩
  -- finiteness over `V`
  have : Algebra.IsIntegral Γ(S, V) Γ(S', p ⁻¹ᵁ V) := by
    constructor
    intro w
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom Γ(S, V) Γ(S', p ⁻¹ᵁ V) L) hinj]
    have hle : sW.range ≤ (integralClosure Γ(S, V) L).toSubring := by
      rw [hrange]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact isIntegral_algebraMap
      · rw [Subring.closure_le]
        exact hint
    exact hle ⟨w, rfl⟩
  have hRfin : (p.appLE V (p ⁻¹ᵁ V) hWV).hom.Finite := Algebra.IsIntegral.finite
  have hfac : p ∣_ V = hW.isoSpec.hom ≫ Spec.map (p.appLE V (p ⁻¹ᵁ V) hWV) ≫
      hV.isoSpec.inv := by
    rw [← cancel_mono V.ι, morphismRestrict_ι, Category.assoc, Category.assoc,
      IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec p hV hW hWV,
      ← IsAffineOpen.isoSpec_inv_ι hW, Category.assoc, Iso.hom_inv_id_assoc]
  have : IsFinite (Spec.map (p.appLE V (p ⁻¹ᵁ V) hWV)) := (IsFinite.SpecMap_iff _).2 hRfin
  have hfinite : IsFinite (p ∣_ V) := by
    rw [hfac]
    infer_instance
  have hdom : IsDominant p := by
    have : IsDominant (η' ≫ p) := by rw [hR.comp_eq]; infer_instance
    exact IsDominant.of_comp η' p
  have halt : IsAlteration p :=
    { toIsProper := hR.isProper, toIsDominant := hdom, sourceIntegral := hR.isIntegral,
      targetIntegral := inferInstance, genericallyFinite := ⟨V, ⟨⟨_, hgV⟩⟩, hfinite⟩ }
  -- generic étaleness
  have : Nonempty V := ⟨⟨_, hgV⟩⟩
  have : IsFractionRing Γ(S, V) S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S V hV
  have : IsScalarTower Γ(S, V) S.functionField L := IsScalarTower.of_algebraMap_eq fun a => by
    change s₁ a = _
    rw [show s₁ = _ from sectionsToField_functionFieldPoint hV hgV]
    rfl
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsDomain Γ(S', p ⁻¹ᵁ V) := hinj.isDomain sW
  obtain ⟨c, hc0, hc⟩ := exists_etale_localization_of_separable Γ(S, V) Γ(S', p ⁻¹ᵁ V)
    S.functionField L hinj
  have hU' : IsAffineOpen (S'.basicOpen c) := hW.basicOpen c
  have hdense : Dense (S'.basicOpen c : Set S') := by
    refine (S'.basicOpen c).isOpen.dense ?_
    rw [Set.nonempty_iff_ne_empty, ← TopologicalSpace.Opens.coe_bot, Ne,
      TopologicalSpace.Opens.coe_inj, basicOpen_eq_bot_iff]
    exact hc0
  have hle : S'.basicOpen c ≤ p ⁻¹ᵁ V := S'.basicOpen_le c
  let _ : Algebra Γ(S, V) Γ(S', S'.basicOpen c) := (p.appLE V _ hle).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(S', p ⁻¹ᵁ V) Γ(S', S'.basicOpen c) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change (p.appLE V _ hle).hom a =
        (S'.presheaf.map (homOfLE (S'.basicOpen_le c)).op).hom ((p.appLE V _ hWV).hom a)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have := hW.isLocalization_basicOpen c
  let e := (IsLocalization.algEquiv (Submonoid.powers c) (Localization.Away c)
    Γ(S', S'.basicOpen c)).restrictScalars Γ(S, V)
  have het : Algebra.Etale Γ(S, V) Γ(S', S'.basicOpen c) := Algebra.Etale.of_equiv e
  have : Etale (Spec.map (p.appLE V _ hle)) := HasRingHomProperty.Spec_iff (P := @Etale).2 het
  have hfac' : (S'.basicOpen c).ι ≫ p =
      hU'.isoSpec.hom ≫ Spec.map (p.appLE V _ hle) ≫ hV.fromSpec := by
    rw [IsAffineOpen.SpecMap_appLE_fromSpec p hV hU' hle, ← IsAffineOpen.isoSpec_inv_ι hU',
      Category.assoc, Iso.hom_inv_id_assoc]
  refine ⟨halt, S'.basicOpen c, hdense, ?_⟩
  rw [hfac']
  infer_instance

/-- **Refinement by a generically étale alteration** (Temkin, Proposition 3.2.6 for `K̄ = K^s`,
with Temkin's remark that `K^s`-modifications are generically étale alterations, lines
2310–2312). Let `S` be integral, separated and locally Noetherian, `L` a separable algebraic
extension of `K(S)` (e.g. `K^s`), `η` the generic point `Spec L → S`, and `gᵢ : Tᵢ → S` finitely
many morphisms locally of finite type from affine schemes into affine opens `Vᵢ`, with points
`ηTᵢ` over `η`. There is a generically étale alteration `p : S' → S` with a dominant point `η'`
over `η`, and opens `Wᵢ ⊆ S'` with proper `hᵢ : Wᵢ → Tᵢ` over `S` compatible with dominant points
over `η'` and `ηTᵢ`, such that every valuation ring of `RZ_L(Tᵢ)` has an extension of `η'` centred
in `Wᵢ`; if the `RZ_L(Tᵢ)` cover `RZ_L(S)`, the `Wᵢ` cover `S'`. -/
theorem exists_refinement_genericallyEtale [IsLocallyNoetherian S] [S.IsSeparated]
    [Algebra.IsSeparable S.functionField L] {ι : Type*} [Finite ι] (T : ι → Scheme.{u})
    [∀ i, IsAffine (T i)] (g : ∀ i, T i ⟶ S) [∀ i, LocallyOfFiniteType (g i)]
    (ηT : ∀ i, Spec (.of L) ⟶ T i) (hηT : ∀ i, ηT i ≫ g i = functionFieldPoint S L)
    (V : ι → S.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hgV : ∀ i, g i ⁻¹ᵁ V i = ⊤) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (η' : Spec (.of L) ⟶ S') (W : ι → S'.Opens)
      (h : ∀ i, (W i).toScheme ⟶ T i),
      IsAlteration p ∧ IsGenericallyEtale p ∧ η' ≫ p = functionFieldPoint S L ∧ IsDominant η' ∧
      (∀ i, IsProper (h i) ∧ h i ≫ g i = (W i).ι ≫ p ∧
        ∃ e : Spec (.of L) ⟶ (W i).toScheme, e ≫ (W i).ι = η' ∧ e ≫ h i = ηT i ∧
          IsDominant e) ∧
      (∀ i, ∀ V' ∈ ofScheme (ηT i), ∃ ψ : Spec (.of V'.valuationSubring) ⟶ S',
        toSpecValuationSubring V' ≫ ψ = η' ∧ ψ (specClosedPoint V') ∈ W i) ∧
      (ofScheme (functionFieldPoint S L) ⊆ ⋃ i, ofScheme (ηT i) → ⨆ i, W i = ⊤) := by
  obtain ⟨S', p, η', F, W, h, hR, hF, hC, hh, hRZ, hcov⟩ :=
    exists_refinement (functionFieldPoint S L) T g ηT hηT V hV hgV
  obtain ⟨halt, hge⟩ := isAlteration_isGenericallyEtale_of_hasCharts hR hF hC
  exact ⟨S', p, η', W, h, halt, hge, hR.comp_eq, hR.isDominant, hh, hRZ, hcov⟩

end GenericallyEtale

end RiemannZariskiSpace

end DeJongAlterations.StableModification

