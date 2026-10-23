import DeJongAlterations.StableModification.LocalUniformization.GlobalBase
import DeJongAlterations.StableModification.LocalUniformization.GlobalChart
import DeJongAlterations.StableModification.LocalUniformization.GlobalClosed

/-!
# Transport of chart blow-ups over a localized base, and extension to the whole curve

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1 (T:2970–2983): the blow-ups are built locally at the centre `x` over the
localization `R_𝔭` of the base beneath `x` and then extended "trivially" to `C`. Here
`O ≤ B` are valuation rings of `K` with `Spec O` finite, `X → Spec O` is a separated strictly
semi-stable curve, and `x` is a closed point of `X` lying over `𝔭 = 𝔪_B ∩ O`.

* `baseOpen`, `baseRestrict`: the open `X_B = g⁻¹(Spec B)` and its structure map to `Spec B`;
  `X_B` is separated and strictly semi-stable over `B` (`isStrictlySemistable_baseRestrict`).
* `exists_extension` (`lem:sm-cofinal-extension`): a proper `β' : C'' → X_B` which is an
  isomorphism over an open `W ∌ x` whose complement is finite, contains `x` as its only point over
  `𝔭`, extends by the identity to a strictly semi-stable modification of `X`. The complement of
  `W` is closed in `X` by `isClosed_of_finite_of_unique` (this is where `x` closed in `X` is
  used; over `B` alone it is BND's strict-henselian fix of `ERRATA.md` DJA-T33).
* `exists_nodeBlowup_globalTransport`, `exists_smoothBlowup_globalTransport`
  (`thm:sm-cofinal-transport`): the transport of the chart blow-ups of BL1 along an étale chart of
  `X_B` at `x` (BND's `Blowups.exists_nodeBlowup_transport`, `exists_smoothBlowup_transport` over
  `B`), extended to `X`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing Polynomial

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open Curves Blowups Algebra.NodeBlowupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Base

variable {K : Type u} [Field K] (O B : ValuationSubring K) (hOB : O ≤ B)
  [Finite (PrimeSpectrum O)] {X : Scheme.{u}} (g : X ⟶ Spec (.of O))

/-- The open `X_B = g⁻¹(Spec B)` of a scheme over `Spec O`. -/
def baseOpen : X.Opens := g ⁻¹ᵁ (specInclusion O B hOB).opensRange

/-- `x ∈ X_B` iff `x` lies over a prime contained in `𝔭 = 𝔪_B ∩ O`. -/
theorem mem_baseOpen_iff {x : X} :
    x ∈ baseOpen O B hOB g ↔ (g x).asIdeal ≤ O.idealOfLE B hOB :=
  mem_range_specInclusion_iff O B hOB (g x)

/-- The structure map `X_B → Spec B`. -/
def baseRestrict : (baseOpen O B hOB g).toScheme ⟶ Spec (.of B) :=
  IsOpenImmersion.lift (specInclusion O B hOB) ((baseOpen O B hOB g).ι ≫ g) (by
    rintro _ ⟨y, rfl⟩
    exact y.2)

/-- `X_B → Spec B → Spec O` is the restriction of `g`. -/
@[reassoc]
theorem baseRestrict_comp :
    baseRestrict O B hOB g ≫ specInclusion O B hOB = (baseOpen O B hOB g).ι ≫ g :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restriction of a separated morphism is separated. -/
instance [IsSeparated g] : IsSeparated (baseRestrict O B hOB g) := by
  have : IsSeparated (baseRestrict O B hOB g ≫ specInclusion O B hOB) := by
    rw [baseRestrict_comp]
    infer_instance
  exact IsSeparated.of_comp _ (specInclusion O B hOB)

/-- **Strict semi-stability is local on the base**: `X_B → Spec B` is strictly semi-stable. -/
theorem isStrictlySemistable_baseRestrict (hX : IsStrictlySemistable g ⊤) :
    IsStrictlySemistable (baseRestrict O B hOB g) ⊤ :=
  IsStrictlySemistable.restrictBase hX (specInclusion O B hOB) (baseOpen O B hOB g) rfl
    (baseRestrict O B hOB g) (baseRestrict_comp O B hOB g)

/-- A point of `X_B` lies over the closed point of `Spec B` iff it lies over `𝔭` in `Spec O`. -/
theorem baseRestrict_apply_eq_closedPoint_iff (y : (baseOpen O B hOB g).toScheme) :
    baseRestrict O B hOB g y = closedPoint B ↔
      g ((baseOpen O B hOB g).ι y) = specInclusion O B hOB (closedPoint B) := by
  rw [← Scheme.Hom.comp_apply, ← baseRestrict_comp, Scheme.Hom.comp_apply]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ (specInclusion O B hOB).isOpenEmbedding.injective h⟩

end Base

section Extension

variable {K : Type u} [Field K] (O B : ValuationSubring K) (hOB : O ≤ B)
  [Finite (PrimeSpectrum O)]

/-- **Extension of a blow-up of `X_B` to `X`** (`lem:sm-cofinal-extension`). Let `X → Spec O` be
strictly semi-stable, `x ∈ X_B` a closed point of `X`, and `β' : C'' → X_B` proper with `C''`
integral, an isomorphism over an open `W ∌ x` of `X_B` whose complement lies in a finite set `Z`
and has `x` as its only point over the closed point of `B`, and `(C'', ∅)` strictly semi-stable
over `B`. Then `β'` extends by the identity to a strictly semi-stable modification `β : X₂ → X`
with an open immersion `ι₁ : C'' → X₂` over `X`, and every point of `X₂` over `x` comes from a
point of `C''` over `x`. -/
theorem exists_extension {X : Scheme.{u}} [IsIntegral X] (g : X ⟶ Spec (.of O))
    (hX : IsStrictlySemistable g ⊤) {Z : Set (baseOpen O B hOB g).toScheme} (hZfin : Z.Finite)
    {x : X} (hxU' : x ∈ baseOpen O B hOB g) (hxcl : IsClosed ({x} : Set X))
    (W : (baseOpen O B hOB g).toScheme.Opens) {C'' : Scheme.{u}} [IsIntegral C'']
    (β' : C'' ⟶ (baseOpen O B hOB g).toScheme) [IsProper β'] [IsIso (β' ∣_ W)]
    (hxW : (⟨x, hxU'⟩ : (baseOpen O B hOB g).toScheme) ∉ W) (hWc : (W : Set _)ᶜ ⊆ Z)
    (huniq : ∀ y ∉ W, baseRestrict O B hOB g y = closedPoint B → y = ⟨x, hxU'⟩)
    (hss' : IsStrictlySemistable (β' ≫ baseRestrict O B hOB g) ⊤)
    (hWne : (W : Set (baseOpen O B hOB g).toScheme).Nonempty) :
    ∃ (X₂ : Scheme.{u}) (β : X₂ ⟶ X) (ι₁ : C'' ⟶ X₂), IsOpenImmersion ι₁ ∧
      ι₁ ≫ β = β' ≫ (baseOpen O B hOB g).ι ∧ IsModification β ∧
      IsStrictlySemistable (β ≫ g) ⊤ ∧
      ∀ y : X₂, β y = x → ∃ c : C'', ι₁ c = y ∧ β' c = ⟨x, hxU'⟩ := by
  let T : Set X := (baseOpen O B hOB g).ι '' (W : Set (baseOpen O B hOB g).toScheme)ᶜ
  have hTfin : T.Finite := (hZfin.image (baseOpen O B hOB g).ι).subset (Set.image_mono hWc)
  have hTsub : ∀ z ∈ T, (g z).asIdeal ≤ O.idealOfLE B hOB := by
    rintro _ ⟨z, -, rfl⟩
    exact (mem_baseOpen_iff O B hOB g).mp z.2
  have hTcl : ∀ y ∈ closure T, (g y).asIdeal ≤ O.idealOfLE B hOB → y ∈ T := by
    intro y hy hle
    have hyU : y ∈ baseOpen O B hOB g := (mem_baseOpen_iff O B hOB g).mpr hle
    refine ⟨⟨y, hyU⟩, ?_, rfl⟩
    have hcl : IsClosed ((W : Set (baseOpen O B hOB g).toScheme)ᶜ) := W.isOpen.isClosed_compl
    rw [← hcl.closure_eq,
      (baseOpen O B hOB g).ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]
    exact hy
  have huniq' : ∀ y ∈ T, g y = specInclusion O B hOB (closedPoint B) → y = x := by
    rintro _ ⟨z, hz, rfl⟩ hgz
    have := huniq z hz ((baseRestrict_apply_eq_closedPoint_iff O B hOB g z).mpr hgz)
    rw [this]
    rfl
  have hTclosed : IsClosed T :=
    isClosed_of_finite_of_unique g (specInclusion O B hOB (closedPoint B)) hTfin hTsub hTcl
      hxcl huniq'
  let W₁ : X.Opens := ⟨Tᶜ, hTclosed.isOpen_compl⟩
  have hxT : x ∈ T := ⟨⟨x, hxU'⟩, hxW, rfl⟩
  have hUW : baseOpen O B hOB g ⊔ W₁ = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    by_cases hy : y ∈ T
    · obtain ⟨z, -, rfl⟩ := hy
      exact Or.inl z.2
    · exact Or.inr hy
  have hle : (baseOpen O B hOB g).ι ⁻¹ᵁ W₁ ≤ W := by
    intro y hy
    by_contra hyW
    exact hy ⟨y, hyW, rfl⟩
  have : IsIso (β' ∣_ ((baseOpen O B hOB g).ι ⁻¹ᵁ W₁)) := isIso_morphismRestrict_of_le β' hle
  have hW₁ne : (W₁ : Set X).Nonempty := by
    obtain ⟨w, hw⟩ := hWne
    refine ⟨(baseOpen O B hOB g).ι w, ?_⟩
    rintro ⟨w', hw', hww'⟩
    rw [(baseOpen O B hOB g).ι.isOpenEmbedding.injective hww'] at hw'
    exact hw' hw
  let β := extensionHom W₁ β'
  have hmod : IsModification β := isModification_extensionHom W₁ β' hUW hW₁ne
  refine ⟨extension W₁ β', β, extensionι₁ W₁ β', inferInstance,
    extensionι₁_extensionHom W₁ β', hmod, ?_, fun y hy ↦ ?_⟩
  · refine IsStrictlySemistable.of_isOpenImmersion_pair (extensionι₁ W₁ β') (extensionι₂ W₁ β')
      (extension_jointly_surjective W₁ β') ?_ ?_
    · rw [Scheme.IdealSheafData.comap_top, ← Category.assoc, extensionι₁_extensionHom,
        Category.assoc, ← baseRestrict_comp, ← Category.assoc]
      exact IsStrictlySemistable.comp_isOpenImmersion hss' _
    · rw [Scheme.IdealSheafData.comap_top, ← Category.assoc, extensionι₂_extensionHom]
      have := hX.etale_comp W₁.ι
      rwa [Scheme.IdealSheafData.comap_top] at this
  · rcases extension_jointly_surjective W₁ β' y with ⟨c, rfl⟩ | ⟨w, rfl⟩
    · refine ⟨c, rfl, Subtype.ext ?_⟩
      exact (extensionHom_ι₁_apply W₁ β' c).symm.trans hy
    · exfalso
      rw [extensionHom_ι₂_apply] at hy
      have : W₁.ι w ∈ (W₁ : Set X) := w.2
      rw [hy] at this
      exact this hxT

end Extension


section ChartTransport

variable {K : Type u} [Field K] (O B : ValuationSubring K) (hOB : O ≤ B)
  [Finite (PrimeSpectrum O)]

/-- A flat scheme over a domain has a point over a prime not containing a given `π ≠ 0`. -/
theorem exists_not_mem_of_flat {A : Type u} [CommRing A] [IsDomain A] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of A)) [Flat g] [Nonempty C] {π : A} (hπ : π ≠ 0) :
    ∃ y : C, π ∉ (g y).asIdeal := by
  obtain ⟨y₀⟩ := ‹Nonempty C›
  have hgen : (⊥ : PrimeSpectrum A) ⤳ g y₀ := by
    rw [← PrimeSpectrum.le_iff_specializes]
    exact bot_le
  obtain ⟨y, -, hy⟩ := Flat.generalizingMap g hgen
  refine ⟨y, ?_⟩
  rw [hy]
  exact hπ

/-- **Globalization of a transported chart blow-up** (`thm:sm-cofinal-transport`, common part).
From the output of BND's transport over `B` (`Blowups.exists_transport` for a chart `φ` of `X_B`
restricted to an open `U₁ ≤ U`) one gets a strictly semi-stable modification `β : X₂ → X` and an
open immersion `J : P → X₂` of the pulled-back blow-up `P = M' ×_M U₀`, with étale projection
`p₁ : P → M'` and `p₂ : P → U`, such that every point of `X₂` over `x` lies in `J(P)`. -/
theorem globalize_transport {X : Scheme.{u}} [IsIntegral X] (g : X ⟶ Spec (.of O))
    (hX : IsStrictlySemistable g ⊤) {M M' : Scheme.{u}} (β₀ : M' ⟶ M)
    {U U₁ U₀ : (baseOpen O B hOB g).toScheme.Opens} (hsub : U₁ ≤ U) (hU₀ : U₀ ≤ U₁)
    (φ : U.toScheme ⟶ M) [Etale φ] {Z : Set (baseOpen O B hOB g).toScheme} (hZfin : Z.Finite)
    {x : X} (hxU' : x ∈ baseOpen O B hOB g) (hxcl : IsClosed ({x} : Set X))
    (W : (baseOpen O B hOB g).toScheme.Opens) {C' : Scheme.{u}}
    (β' : C' ⟶ (baseOpen O B hOB g).toScheme)
    (j : pullback β₀ ((baseOpen O B hOB g).toScheme.homOfLE hU₀ ≫
      (baseOpen O B hOB g).toScheme.homOfLE hsub ≫ φ) ⟶ C') (k : W.toScheme ⟶ C')
    (hxW : (⟨x, hxU'⟩ : (baseOpen O B hOB g).toScheme) ∉ W) (hWc : (W : Set _)ᶜ ⊆ Z)
    (huniq : ∀ y ∉ W, baseRestrict O B hOB g y = closedPoint B → y = ⟨x, hxU'⟩)
    (hj : IsOpenImmersion j) (hjβ : j ≫ β' = pullback.snd _ _ ≫ U₀.ι) (hkβ : k ≫ β' = W.ι)
    (hcov : ∀ y : C', y ∈ Set.range j ∨ y ∈ Set.range k) (hprop : IsProper β')
    (hiso : IsIso (β' ∣_ W)) (hss : IsStrictlySemistable (β' ≫ baseRestrict O B hOB g) ⊤)
    (hmod : IsModification β') (hWne : (W : Set (baseOpen O B hOB g).toScheme).Nonempty) :
    ∃ (X₂ : Scheme.{u}) (β : X₂ ⟶ X) (P : Scheme.{u}) (J : P ⟶ X₂) (p₁ : P ⟶ M')
      (p₂ : P ⟶ U.toScheme), IsModification β ∧ IsStrictlySemistable (β ≫ g) ⊤ ∧
      IsOpenImmersion J ∧ Etale p₁ ∧ p₁ ≫ β₀ = p₂ ≫ φ ∧
      J ≫ β = p₂ ≫ U.ι ≫ (baseOpen O B hOB g).ι ∧ ∀ y : X₂, β y = x → y ∈ Set.range J := by
  have : IsIntegral C' := hmod.sourceIntegral
  obtain ⟨X₂, β, ι₁, hι₁, hι₁β, hβ, hssβ, hover⟩ :=
    exists_extension O B hOB g hX hZfin hxU' hxcl W β' hxW hWc huniq hss hWne
  let P := pullback β₀ ((baseOpen O B hOB g).toScheme.homOfLE hU₀ ≫
    (baseOpen O B hOB g).toScheme.homOfLE hsub ≫ φ)
  refine ⟨X₂, β, P, j ≫ ι₁, pullback.fst _ _, pullback.snd _ _ ≫
    (baseOpen O B hOB g).toScheme.homOfLE hU₀ ≫ (baseOpen O B hOB g).toScheme.homOfLE hsub,
    hβ, hssβ, inferInstance, inferInstance, ?_, ?_, fun y hy ↦ ?_⟩
  · rw [pullback.condition]
    simp only [Category.assoc]
  · rw [Category.assoc, hι₁β, ← Category.assoc, hjβ]
    simp only [Category.assoc, Scheme.homOfLE_ι_assoc]
  · obtain ⟨c, rfl, hc⟩ := hover y hy
    rcases hcov c with ⟨p, rfl⟩ | ⟨w, rfl⟩
    · exact ⟨p, rfl⟩
    · exfalso
      have h1 : β' (k w) = W.ι w := by rw [← Scheme.Hom.comp_apply, hkβ]
      rw [hc] at h1
      apply hxW
      rw [h1]
      exact w.2

variable [IsSepClosed K]

/-- An affine open of `U` through a point. -/
theorem exists_affine_le {Y : Scheme.{u}} (U : Y.Opens) {y : Y} (hy : y ∈ U) :
    ∃ U₁ : Y.Opens, IsAffineOpen U₁ ∧ y ∈ U₁ ∧ U₁ ≤ U := by
  obtain ⟨_, ⟨U₁, hU₁, rfl⟩, hyU₁, hsub⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
  exact ⟨U₁, hU₁, hyU₁, hsub⟩

/-- **Global transport of the node chart blow-up** (`thm:sm-cofinal-transport`, node case; Temkin,
Prop 4.3.1, stage 1, T:2976–2990). Let `X → Spec O` be separated, integral and strictly
semi-stable, `x` a closed point of `X` lying over `𝔭 = 𝔪_B ∩ O`, and
`φ : U → Spec B[u,v]/(uv - πb)` an étale chart of `X_B` at `x` with `φ(x) ∈ V(u, v, π)`. Then
there is a strictly semi-stable modification `β : X₂ → X` such that every point of `X₂` over `x`
lies in an open `J(P)`, `P` étale over `Bl_{(u,π)}` via `p₁` and over `U` via `p₂`. -/
theorem exists_nodeBlowup_globalTransport {X : Scheme.{u}} [IsIntegral X] (g : X ⟶ Spec (.of O))
    [IsSeparated g] (hX : IsStrictlySemistable g ⊤) (π b : B) [Fact (π ≠ 0)] [Fact (b ≠ 0)]
    (U : (baseOpen O B hOB g).toScheme.Opens) (φ : U.toScheme ⟶ Spec (.of (Node B (π * b))))
    [Etale φ] (hφ : φ ≫ nodeModel (π * b) = U.ι ≫ baseRestrict O B hOB g)
    {x : X} (hxU' : x ∈ baseOpen O B hOB g) (hxU : (⟨x, hxU'⟩ : (baseOpen O B hOB g).toScheme) ∈ U)
    (hxcl : IsClosed ({x} : Set X))
    (hx : baseRestrict O B hOB g ⟨x, hxU'⟩ = closedPoint B)
    (hxi : φ ⟨⟨x, hxU'⟩, hxU⟩ ∈ Set.range (nodeLocus π b)) :
    ∃ (X₂ : Scheme.{u}) (β : X₂ ⟶ X) (P : Scheme.{u}) (J : P ⟶ X₂)
      (p₁ : P ⟶ affineBlowup (centerIdeal π b)) (p₂ : P ⟶ U.toScheme),
      IsModification β ∧ IsStrictlySemistable (β ≫ g) ⊤ ∧ IsOpenImmersion J ∧ Etale p₁ ∧
      p₁ ≫ affineBlowupStructure (centerIdeal π b) = p₂ ≫ φ ∧
      J ≫ β = p₂ ≫ U.ι ≫ (baseOpen O B hOB g).ι ∧ ∀ y : X₂, β y = x → y ∈ Set.range J := by
  have hC' := isStrictlySemistable_baseRestrict O B hOB g hX
  obtain ⟨U₁, hU₁, hxU₁, hsub⟩ := exists_affine_le U hxU
  have : IsAffine U₁.toScheme := hU₁
  let φ₁ := (baseOpen O B hOB g).toScheme.homOfLE hsub ≫ φ
  have hφ₁ : φ₁ ≫ nodeModel (π * b) = U₁.ι ≫ baseRestrict O B hOB g := by
    rw [Category.assoc, hφ, ← Category.assoc, Scheme.homOfLE_ι]
  have hxi₁ : φ₁ ⟨⟨x, hxU'⟩, hxU₁⟩ ∈ Set.range (nodeLocus π b) := by
    have hh : (baseOpen O B hOB g).toScheme.homOfLE hsub ⟨⟨x, hxU'⟩, hxU₁⟩ = ⟨⟨x, hxU'⟩, hxU⟩ :=
      Subtype.ext (Scheme.homOfLE_apply _ _)
    rw [Scheme.Hom.comp_apply, hh]
    exact hxi
  obtain ⟨U₀, hU₀, W, C', β', j, k, -, hxW, hWc, huniq, hj, -, hjβ, hkβ, hcov, hprop, hiso,
      hss, hmod⟩ :=
    exists_nodeBlowup_transport π b (baseRestrict O B hOB g) hC' U₁ φ₁ hφ₁ ⟨x, hxU'⟩ hxU₁ hx hxi₁
  have : Nonempty (baseOpen O B hOB g).toScheme := ⟨⟨x, hxU'⟩⟩
  have : IsIntegral (baseOpen O B hOB g).toScheme :=
    isIntegral_of_isOpenImmersion (baseOpen O B hOB g).ι
  -- the finite set containing the locus
  have : Finite (PrimeSpectrum B) := finite_primeSpectrum O B hOB
  have hfinĀ : Finite (Spec (.of (Node B (π * b) ⧸ nodeLocusIdeal π b))) :=
    Finite.of_injective _ (PrimeSpectrum.comap_injective_of_surjective _
      (algebraMap_nodeLocus_surjective π b))
  have : QuasiCompact φ₁ :=
    HasAffineProperty.iff_of_isAffine.mpr (inferInstance : CompactSpace U₁.toScheme)
  have hZfin : (U₁.ι '' (φ₁ ⁻¹' Set.range (nodeLocus π b))).Finite :=
    ((Set.finite_range _).preimage' fun _ _ ↦ φ₁.finite_preimage_singleton _).image _
  -- a point off the locus
  have : DeJong.IsNodalCurve (baseRestrict O B hOB g) := hC'.isNodalCurve
  obtain ⟨y, hy⟩ := exists_not_mem_of_flat (baseRestrict O B hOB g) (Fact.out : π ≠ 0)
  have hWne : (W : Set (baseOpen O B hOB g).toScheme).Nonempty := by
    refine ⟨y, by_contra fun hyW ↦ hy ?_⟩
    obtain ⟨w, ⟨a, ha⟩, rfl⟩ := hWc hyW
    have hmem := range_nodeLocus_comp_subset π b ⟨a, rfl⟩
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hmem
    rw [← Scheme.Hom.comp_apply, ← hφ₁, Scheme.Hom.comp_apply, ← ha, ← Scheme.Hom.comp_apply]
    exact hmem
  exact globalize_transport O B hOB g hX _ hsub hU₀ φ hZfin hxU' hxcl W β' j k hxW hWc huniq hj
    hjβ hkβ hcov hprop hiso hss (hmod inferInstance) hWne

/-- **Global transport of the smooth chart blow-up** (`thm:sm-cofinal-transport`, smooth case;
Temkin, Prop 4.3.1, stage 2, T:2992–3016): as `exists_nodeBlowup_globalTransport` for an étale
chart `φ : U → Spec B[T]` of `X_B` at `x` with `φ(x) ∈ V(π, T - a)`. -/
theorem exists_smoothBlowup_globalTransport {X : Scheme.{u}} [IsIntegral X]
    (g : X ⟶ Spec (.of O)) [IsSeparated g] (hX : IsStrictlySemistable g ⊤) (π a : B)
    [Fact (π ≠ 0)] (U : (baseOpen O B hOB g).toScheme.Opens) (φ : U.toScheme ⟶ Spec (.of B[X]))
    [Etale φ] (hφ : φ ≫ smoothModel B = U.ι ≫ baseRestrict O B hOB g)
    {x : X} (hxU' : x ∈ baseOpen O B hOB g) (hxU : (⟨x, hxU'⟩ : (baseOpen O B hOB g).toScheme) ∈ U)
    (hxcl : IsClosed ({x} : Set X))
    (hx : baseRestrict O B hOB g ⟨x, hxU'⟩ = closedPoint B)
    (hxi : φ ⟨⟨x, hxU'⟩, hxU⟩ ∈ Set.range (smoothLocus π a)) :
    ∃ (X₂ : Scheme.{u}) (β : X₂ ⟶ X) (P : Scheme.{u}) (J : P ⟶ X₂)
      (p₁ : P ⟶ affineBlowup (smoothCenter π a)) (p₂ : P ⟶ U.toScheme),
      IsModification β ∧ IsStrictlySemistable (β ≫ g) ⊤ ∧ IsOpenImmersion J ∧ Etale p₁ ∧
      p₁ ≫ affineBlowupStructure (smoothCenter π a) = p₂ ≫ φ ∧
      J ≫ β = p₂ ≫ U.ι ≫ (baseOpen O B hOB g).ι ∧ ∀ y : X₂, β y = x → y ∈ Set.range J := by
  have hC' := isStrictlySemistable_baseRestrict O B hOB g hX
  obtain ⟨U₁, hU₁, hxU₁, hsub⟩ := exists_affine_le U hxU
  have : IsAffine U₁.toScheme := hU₁
  let φ₁ := (baseOpen O B hOB g).toScheme.homOfLE hsub ≫ φ
  have hφ₁ : φ₁ ≫ smoothModel B = U₁.ι ≫ baseRestrict O B hOB g := by
    rw [Category.assoc, hφ, ← Category.assoc, Scheme.homOfLE_ι]
  have hxi₁ : φ₁ ⟨⟨x, hxU'⟩, hxU₁⟩ ∈ Set.range (smoothLocus π a) := by
    have hh : (baseOpen O B hOB g).toScheme.homOfLE hsub ⟨⟨x, hxU'⟩, hxU₁⟩ = ⟨⟨x, hxU'⟩, hxU⟩ :=
      Subtype.ext (Scheme.homOfLE_apply _ _)
    rw [Scheme.Hom.comp_apply, hh]
    exact hxi
  obtain ⟨U₀, hU₀, W, C', β', j, k, -, hxW, hWc, huniq, hj, -, hjβ, hkβ, hcov, hprop, hiso,
      hss, hmod⟩ :=
    exists_smoothBlowup_transport π a (baseRestrict O B hOB g) hC' U₁ φ₁ hφ₁ ⟨x, hxU'⟩ hxU₁ hx
      hxi₁
  have : Nonempty (baseOpen O B hOB g).toScheme := ⟨⟨x, hxU'⟩⟩
  have : IsIntegral (baseOpen O B hOB g).toScheme :=
    isIntegral_of_isOpenImmersion (baseOpen O B hOB g).ι
  have : Finite (PrimeSpectrum B) := finite_primeSpectrum O B hOB
  have hfinĀ : Finite (Spec (.of (B[X] ⧸ smoothCenter π a))) :=
    Finite.of_injective _ (PrimeSpectrum.comap_injective_of_surjective _
      (algebraMap_smoothLocus_surjective π a))
  have : QuasiCompact φ₁ :=
    HasAffineProperty.iff_of_isAffine.mpr (inferInstance : CompactSpace U₁.toScheme)
  have hZfin : (U₁.ι '' (φ₁ ⁻¹' Set.range (smoothLocus π a))).Finite :=
    ((Set.finite_range _).preimage' fun _ _ ↦ φ₁.finite_preimage_singleton _).image _
  have : DeJong.IsNodalCurve (baseRestrict O B hOB g) := hC'.isNodalCurve
  obtain ⟨y, hy⟩ := exists_not_mem_of_flat (baseRestrict O B hOB g) (Fact.out : π ≠ 0)
  have hWne : (W : Set (baseOpen O B hOB g).toScheme).Nonempty := by
    refine ⟨y, by_contra fun hyW ↦ hy ?_⟩
    obtain ⟨w, ⟨a', ha⟩, rfl⟩ := hWc hyW
    have hmem := range_smoothLocus_comp_subset π a ⟨a', rfl⟩
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hmem
    rw [← Scheme.Hom.comp_apply, ← hφ₁, Scheme.Hom.comp_apply, ← ha, ← Scheme.Hom.comp_apply]
    exact hmem
  exact globalize_transport O B hOB g hX _ hsub hU₀ φ hZfin hxU' hxcl W β' j k hxW hWc huniq hj
    hjβ hkβ hcov hprop hiso hss (hmod inferInstance) hWne

end ChartTransport

end DeJongAlterations.StableModification.LocalUniformization
