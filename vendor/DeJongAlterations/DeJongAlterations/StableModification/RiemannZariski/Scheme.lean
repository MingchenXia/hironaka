import DeJongAlterations.StableModification.RiemannZariski.Algebraic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Riemann–Zariski spaces of schemes

Let `S` be a scheme and `η : Spec L → S` a morphism from the spectrum of a field. Following
Temkin, *Stable modification of relative curves* (J. Algebraic Geom. 19 (2010); arXiv v3
numbering), §3.2 (Corollary 3.2.5 `bijcor` and Remark 3.2.8 (i), (iii)), the Riemann–Zariski
space `RZ_L(S)` is described
valuation-theoretically: its points are the valuation rings `V` of `L` such that `η` extends to a
morphism `Spec V → S`. We take this description as the definition, as a subset of the absolute
Riemann–Zariski space of `L` with the subspace topology.

For a separated scheme the extension is unique (valuative criterion), so this set is in natural
bijection with Temkin's `Val_L(S)` (Corollary 3.2.5), and the subspace topology is Temkin's
topology (Lemma 3.2.9). For a non-separated scheme the set of valuation rings forgets
which extension is chosen; all results below that need it assume separatedness.

## Main definitions

* `RiemannZariskiSpace.ofScheme η`: the valuation rings `V` of `L` such that `η` extends to
  `Spec V → S`.
* `RiemannZariskiSpace.sectionsToField η U h`: the ring map `Γ(S, U) → L` induced by `η` when `η`
  factors through the open `U`.
* `RiemannZariskiSpace.ofOpen η U`: the valuation rings containing the image of `Γ(S, U)`.

## Main results

* `RiemannZariskiSpace.mem_ofScheme_iff`: `V ∈ RZ_L(S)` iff `V` contains the image of `Γ(S, U)`
  for some affine open `U` (the closed point of `Spec V` lands in `U`).
* `RiemannZariskiSpace.isCompact_ofScheme`: `RZ_L(S)` is quasi-compact for quasi-compact `S`
  (Temkin, Proposition 3.2.1 `quacomprop`, direct implication, quasi-compactness part).
* `RiemannZariskiSpace.extension_unique`: for separated `S` the extension is unique.
* `RiemannZariskiSpace.isOpen_ofOpen`: for separated quasi-compact `S` and affine open `U`, the set
  `RZ_L(U)` is open in `RZ_L(S)`; equivalently the center map is continuous
  (`RiemannZariskiSpace.ofScheme.continuous_center`).
* `RiemannZariskiSpace.isOpenEmbedding_inclusion_ofScheme`: for `S' → S` locally of finite type,
  `RZ_L(S') → RZ_L(S)` is an open embedding (Temkin, Corollary 3.2.7 `openembcor`).
* `RiemannZariskiSpace.ofScheme_eq_of_universallyClosed`, `RiemannZariskiSpace.ofSchemeHomeomorph`:
  for `S' → S` universally closed (e.g. proper), `RZ_L(S') = RZ_L(S)`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology Set.Notation

universe u

namespace DeJongAlterations.StableModification

namespace RiemannZariskiSpace

variable {S S' : Scheme.{u}} {L : Type u} [Field L]

/-- The morphism `Spec L → Spec V` induced by the inclusion of a valuation ring `V ⊆ L`. -/
noncomputable abbrev toSpecValuationSubring (V : RiemannZariskiSpace L) :
    Spec (.of L) ⟶ Spec (.of V.valuationSubring) :=
  Spec.map (CommRingCat.ofHom (algebraMap V.valuationSubring L))

/-- The closed point of `Spec V` for a valuation ring `V` of `L`. -/
noncomputable def specClosedPoint (V : RiemannZariskiSpace L) : Spec (.of V.valuationSubring) :=
  IsLocalRing.closedPoint V.valuationSubring

variable (η : Spec (.of L) ⟶ S)

/-- The Riemann–Zariski space `RZ_L(S)` of a scheme `S` with respect to `η : Spec L → S`: the
valuation rings `V` of `L` such that `η` extends to a morphism `Spec V → S`
(Temkin 2010, §3.2, `Val_L(S)` before Corollary 3.2.5 `bijcor`). -/
def ofScheme : Set (RiemannZariskiSpace L) :=
  {V | ∃ φ : Spec (.of V.valuationSubring) ⟶ S, toSpecValuationSubring V ≫ φ = η}

/-- The ring homomorphism `Γ(S, U) → L` induced by `η`, when `η` factors through the open `U`. -/
noncomputable def sectionsToField (U : S.Opens) (hU : η ⁻¹ᵁ U = ⊤) : Γ(S, U) →+* L :=
  (η.appLE U ⊤ hU.ge ≫ (Scheme.ΓSpecIso (.of L)).hom).hom

/-- The Riemann–Zariski space of an open `U ⊆ S` through which `η` factors: the valuation rings
containing the image of `Γ(S, U)`. -/
def ofOpen (U : S.Opens) : Set (RiemannZariskiSpace L) :=
  {V | ∃ hU : η ⁻¹ᵁ U = ⊤, V ∈ ofRingHom (sectionsToField η U hU)}

variable {η}

lemma mem_ofOpen_iff {U : S.Opens} (hU : η ⁻¹ᵁ U = ⊤) {V : RiemannZariskiSpace L} :
    V ∈ ofOpen η U ↔ V ∈ ofRingHom (sectionsToField η U hU) :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hU, h⟩⟩

lemma ofOpen_eq_of_not {U : S.Opens} (hU : ¬ η ⁻¹ᵁ U = ⊤) : ofOpen η U = ∅ := by
  ext V
  simp only [ofOpen, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact fun ⟨h, _⟩ => hU h

/-- If `η` is dominant (as in Temkin §3.2), it factors through every nonempty open of `S`. -/
lemma preimage_eq_top_of_isDominant [IsDominant η] {U : S.Opens} (hU : (U : Set S).Nonempty) :
    η ⁻¹ᵁ U = ⊤ := by
  obtain ⟨_, hxU, x, rfl⟩ := η.denseRange.inter_open_nonempty U U.isOpen hU
  have : Subsingleton (Spec (.of L)) := inferInstanceAs (Subsingleton (PrimeSpectrum L))
  ext y
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  rw [Subsingleton.elim y x]
  exact hxU

lemma isPatchClosed_ofOpen (U : S.Opens) : IsPatchClosed (ofOpen η U) := by
  by_cases hU : η ⁻¹ᵁ U = ⊤
  · have : ofOpen η U = ofRingHom (sectionsToField η U hU) := by
      ext V
      exact mem_ofOpen_iff hU
    rw [this]
    exact isPatchClosed_containing _
  · rw [ofOpen_eq_of_not hU]
    exact isPatchClosed_empty

/-- If `φ : Spec V → S` extends `η`, then the ring map `Γ(S, U) → L` factors through `V`. -/
lemma sectionsToField_eq_of_extension {V : RiemannZariskiSpace L}
    (φ : Spec (.of V.valuationSubring) ⟶ S) (hφ : toSpecValuationSubring V ≫ φ = η) {U : S.Opens}
    (hφU : φ ⁻¹ᵁ U = ⊤) (hU : η ⁻¹ᵁ U = ⊤) :
    sectionsToField η U hU = (algebraMap V.valuationSubring L).comp
      (φ.appLE U ⊤ hφU.ge ≫ (Scheme.ΓSpecIso (.of V.valuationSubring)).hom).hom := by
  subst hφ
  have h1 : (toSpecValuationSubring V).appLE ⊤ ⊤ le_rfl ≫ (Scheme.ΓSpecIso (.of L)).hom =
      (Scheme.ΓSpecIso (.of V.valuationSubring)).hom ≫
        CommRingCat.ofHom (algebraMap V.valuationSubring L) := by
    rw [← Scheme.ΓSpecIso_naturality]
    rfl
  have h2 : (toSpecValuationSubring V ≫ φ).appLE U ⊤ hU.ge =
      φ.appLE U ⊤ hφU.ge ≫ (toSpecValuationSubring V).appLE ⊤ ⊤ le_rfl :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [sectionsToField, h2, Category.assoc, h1, ← Category.assoc]
  rfl

/-- **Temkin §3.2, the affine description (one direction).** If `φ : Spec V → S` extends `η` and
the closed point of `Spec V` lands in the open `U`, then `V` contains the image of `Γ(S, U)`. -/
theorem mem_ofOpen_of_extension {V : RiemannZariskiSpace L}
    (φ : Spec (.of V.valuationSubring) ⟶ S) (hφ : toSpecValuationSubring V ≫ φ = η) {U : S.Opens}
    (hU : φ (specClosedPoint V) ∈ U) : V ∈ ofOpen η U := by
  have hφU : φ ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem φ hU
  have hηU : η ⁻¹ᵁ U = ⊤ := by
    rw [← hφ, Scheme.Hom.comp_preimage, hφU]
    rfl
  refine ⟨hηU, ?_⟩
  rw [mem_ofRingHom, sectionsToField_eq_of_extension φ hφ hφU hηU]
  intro a
  exact (SetLike.coe_mem _)

variable (η) in
/-- The extension `Spec V → U ⊆ S` of `η` determined by a valuation ring `V` containing the image
of `Γ(S, U)`, for an affine open `U`. -/
noncomputable def extensionOfMem {U : S.Opens} (hU : IsAffineOpen U) (hηU : η ⁻¹ᵁ U = ⊤)
    (V : RiemannZariskiSpace L) (hV : V ∈ ofRingHom (sectionsToField η U hηU)) :
    Spec (.of V.valuationSubring) ⟶ S :=
  Spec.map (CommRingCat.ofHom ((sectionsToField η U hηU).codRestrict V.valuationSubring
    (mem_ofRingHom.1 hV))) ≫ hU.fromSpec

/-- The morphism `extensionOfMem` extends `η`. -/
lemma toSpecValuationSubring_comp_extensionOfMem {U : S.Opens} (hU : IsAffineOpen U)
    (hηU : η ⁻¹ᵁ U = ⊤) (V : RiemannZariskiSpace L)
    (hV : V ∈ ofRingHom (sectionsToField η U hηU)) :
    toSpecValuationSubring V ≫ extensionOfMem η hU hηU V hV = η := by
  rw [extensionOfMem, ← Spec.map_comp_assoc]
  have h1 : CommRingCat.ofHom ((sectionsToField η U hηU).codRestrict V.valuationSubring
      (mem_ofRingHom.1 hV)) ≫ CommRingCat.ofHom (algebraMap V.valuationSubring L) =
      η.appLE U ⊤ hηU.ge ≫ (Scheme.ΓSpecIso (.of L)).hom := by
    ext x
    rfl
  rw [h1, Spec.map_comp_assoc, IsAffineOpen.SpecMap_appLE_fromSpec η hU (isAffineOpen_top _),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

/-- The closed point of `Spec V` is sent into `U` by `extensionOfMem`. -/
lemma extensionOfMem_closedPoint {U : S.Opens} (hU : IsAffineOpen U) (hηU : η ⁻¹ᵁ U = ⊤)
    (V : RiemannZariskiSpace L) (hV : V ∈ ofRingHom (sectionsToField η U hηU)) :
    extensionOfMem η hU hηU V hV (specClosedPoint V) ∈ U := by
  have : extensionOfMem η hU hηU V hV (specClosedPoint V) ∈ Set.range hU.fromSpec :=
    ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rwa [hU.range_fromSpec] at this

/-- The closed point of the extension determined by `V ⊇ Γ(S, U)` lies in the basic open
`D(g)` of `g ∈ Γ(S, U)` iff the image of `g` is a unit of `V`. -/
lemma extensionOfMem_closedPoint_mem_basicOpen_iff {U : S.Opens} (hU : IsAffineOpen U)
    (hηU : η ⁻¹ᵁ U = ⊤) (V : RiemannZariskiSpace L)
    (hV : V ∈ ofRingHom (sectionsToField η U hηU)) (g : Γ(S, U)) :
    extensionOfMem η hU hηU V hV (specClosedPoint V) ∈ S.basicOpen g ↔
      sectionsToField η U hηU g ∉ V.valuationSubring.nonunits := by
  rw [extensionOfMem, Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage,
    hU.fromSpec_preimage_basicOpen]
  change ¬ (_ ∈ IsLocalRing.maximalIdeal V.valuationSubring) ↔ _
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  rfl

/-- **Temkin §3.2, the affine description (other direction).** If `V` contains the image of
`Γ(S, U)` for an affine open `U`, then `η` extends to `Spec V → S`. -/
theorem ofOpen_subset_ofScheme {U : S.Opens} (hU : IsAffineOpen U) : ofOpen η U ⊆ ofScheme η :=
  fun V ⟨hηU, hV⟩ => ⟨_, toSpecValuationSubring_comp_extensionOfMem hU hηU V hV⟩

/-- **Temkin, Remark 3.2.8 (i), (iii).** A valuation ring `V` of `L` lies in
`RZ_L(S)` iff it contains the image of `Γ(S, U)` for some affine open `U` of `S`. -/
theorem mem_ofScheme_iff {V : RiemannZariskiSpace L} :
    V ∈ ofScheme η ↔ ∃ U : S.affineOpens, V ∈ ofOpen η U := by
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hcU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (φ (specClosedPoint V))) isOpen_univ
    exact ⟨⟨U, hU⟩, mem_ofOpen_of_extension φ hφ hcU⟩
  · rintro ⟨U, hV⟩
    exact ofOpen_subset_ofScheme U.2 hV

/-- `RZ_L(S)` is the union of the `RZ_L(Uᵢ)` for any cover of `S` by affine opens `Uᵢ`. -/
theorem ofScheme_eq_iUnion {ι : Type*} (U : ι → S.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcov : ∀ x : S, ∃ i, x ∈ U i) : ofScheme η = ⋃ i, ofOpen η (U i) := by
  ext V
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨i, hi⟩ := hcov (φ (specClosedPoint V))
    exact ⟨i, mem_ofOpen_of_extension φ hφ hi⟩
  · rintro ⟨i, hV⟩
    exact ofOpen_subset_ofScheme (hU i) hV

/-- **Temkin, Remark 3.2.8 (i).** For an affine scheme `S`, `RZ_L(S)` is the
set of valuation rings of `L` containing the image of `Γ(S, ⊤)`. -/
theorem ofScheme_eq_ofOpen_top [IsAffine S] : ofScheme η = ofOpen η ⊤ := by
  rw [ofScheme_eq_iUnion (fun _ : Unit => (⊤ : S.Opens)) (fun _ => isAffineOpen_top S)
    (fun _ => ⟨(), trivial⟩)]
  exact Set.iUnion_const _

/-- A quasi-compact scheme has a finite affine open cover. -/
lemma exists_finite_affine_cover [CompactSpace S] :
    ∃ t : Finset S.affineOpens, ∀ x : S, ∃ U ∈ t, x ∈ (U : S.Opens) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : S.affineOpens => ((U : S.Opens) : Set S)) (fun U => U.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t, fun x => ?_⟩
  have := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion] at this
  obtain ⟨U, hU, hxU⟩ := this
  exact ⟨U, hU, hxU⟩

/-- For a quasi-compact scheme `S`, `RZ_L(S)` is patch-closed: it is a finite union of the
patch-closed sets `RZ_L(Uᵢ)` over a finite affine open cover. -/
theorem isPatchClosed_ofScheme [CompactSpace S] : IsPatchClosed (ofScheme η) := by
  obtain ⟨t, ht⟩ := exists_finite_affine_cover (S := S)
  rw [ofScheme_eq_iUnion (fun U : t => (U.1 : S.Opens)) (fun U => U.1.2) (fun x => by
    obtain ⟨U, hU, hxU⟩ := ht x
    exact ⟨⟨U, hU⟩, hxU⟩)]
  exact isPatchClosed_iUnion fun U => isPatchClosed_ofOpen _

/-- **Quasi-compactness of `RZ_L(S)`** (Temkin, Proposition 3.2.1 `quacomprop`): for a
quasi-compact scheme `S`, the Riemann–Zariski space `RZ_L(S)` is quasi-compact. -/
theorem isCompact_ofScheme [CompactSpace S] : IsCompact (ofScheme η) :=
  isPatchClosed_ofScheme.isCompact

instance compactSpace_ofScheme [CompactSpace S] : CompactSpace (ofScheme η) :=
  isCompact_iff_compactSpace.1 isCompact_ofScheme

/-! ### Separated schemes: uniqueness of the extension and the topology -/

/-- **Uniqueness of the extension** (valuative criterion of separatedness, Temkin §3.2 before
Corollary 3.2.5 `bijcor`): for a separated scheme `S`, an extension of `η` to `Spec V` is unique. -/
theorem extension_unique [S.IsSeparated] {V : RiemannZariskiSpace L}
    {φ₁ φ₂ : Spec (.of V.valuationSubring) ⟶ S} (h₁ : toSpecValuationSubring V ≫ φ₁ = η)
    (h₂ : toSpecValuationSubring V ≫ φ₂ = η) : φ₁ = φ₂ := by
  let sq : ValuativeCommSq (terminal.from S) :=
    { R := V.valuationSubring, K := L, i₁ := η, i₂ := φ₁ ≫ terminal.from S,
      commSq := ⟨by rw [← h₁, Category.assoc]⟩ }
  have := IsSeparated.valuativeCriterion (terminal.from S) sq
  let l₁ : sq.commSq.LiftStruct := ⟨φ₁, h₁, rfl⟩
  let l₂ : sq.commSq.LiftStruct := ⟨φ₂, h₂, terminal.hom_ext _ _⟩
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)

/-- In a quasi-separated scheme, for affine opens `U` and `W`, finitely many basic opens
`D(g) ⊆ U` with `g ∈ Γ(S, W)` cover `U ∩ W`. -/
lemma exists_finset_basicOpen_cover [QuasiSeparatedSpace S] {U W : S.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) :
    ∃ G : Finset Γ(S, W), (∀ g ∈ G, S.basicOpen g ≤ U) ∧
      ∀ x ∈ U, x ∈ W → ∃ g ∈ G, x ∈ S.basicOpen g := by
  have hc : IsCompact ((U : Set S) ∩ W) :=
    QuasiSeparatedSpace.inter_isCompact _ _ U.isOpen hU.isCompact W.isOpen hW.isCompact
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover
    (fun g : {g : Γ(S, W) // S.basicOpen g ≤ U ⊓ W} => (S.basicOpen g.1 : Set S))
    (fun g => (S.basicOpen g.1).isOpen) (by
      rintro x ⟨hxU, hxW⟩
      obtain ⟨g, hg, hxg⟩ := hW.exists_basicOpen_le (V := U ⊓ W) ⟨x, hxU, hxW⟩ hxW
      exact Set.mem_iUnion.2 ⟨⟨g, hg⟩, hxg⟩)
  classical
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.1 hg
    exact g'.2.trans inf_le_left
  · intro x hxU hxW
    have := ht ⟨hxU, hxW⟩
    simp only [Set.mem_iUnion] at this
    obtain ⟨g, hg, hxg⟩ := this
    exact ⟨g.1, Finset.mem_image_of_mem _ hg, hxg⟩

/-- The local step of the openness of `RZ_L(U)` in `RZ_L(S)`: for affine opens `U`, `W` of a
separated scheme, finitely many elements `F` of the image of `Γ(S, U)` suffice to force a valuation
ring containing `Γ(S, W)` and `F` to contain `Γ(S, U)`. The proof uses the compactness of the patch
topology and the uniqueness of extensions. -/
lemma exists_finset_of_affine_pair [S.IsSeparated] {U W : S.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) (hηU : η ⁻¹ᵁ U = ⊤) :
    ∃ F : Finset L, (F : Set L) ⊆ Set.range (sectionsToField η U hηU) ∧
      ∀ V ∈ ofOpen η W, V ∈ basicOpen F → V ∈ ofOpen η U := by
  by_cases hηW : η ⁻¹ᵁ W = ⊤
  swap
  · refine ⟨∅, by simp, fun V hV => ?_⟩
    rw [ofOpen_eq_of_not hηW] at hV
    exact hV.elim
  obtain ⟨G, hGU, hGcov⟩ := exists_finset_basicOpen_cover hU hW
  set sU := sectionsToField η U hηU
  set sW := sectionsToField η W hηW
  let K : Set (RiemannZariskiSpace L) :=
    ofOpen η W ∩ ⋂ g ∈ G, {V | sW g ∈ V.valuationSubring.nonunits}
  have hK : IsPatchClosed K := (isPatchClosed_ofOpen W).inter
    (isPatchClosed_iInter fun g => isPatchClosed_iInter fun _ => isPatchClosed_mem_nonunits _)
  have hgood : ∀ V (hV : V ∈ ofRingHom sW),
      (∃ g ∈ G, sW g ∉ V.valuationSubring.nonunits) → V ∈ ofOpen η U := by
    rintro V hV ⟨g, hg, hgV⟩
    have hc := (extensionOfMem_closedPoint_mem_basicOpen_iff hW hηW V hV g).2 hgV
    exact mem_ofOpen_of_extension _ (toSpecValuationSubring_comp_extensionOfMem hW hηW V hV)
      (hGU g hg hc)
  have hcov : K ⊆ ⋃ a : Γ(S, U), {V | sU a ∉ V.valuationSubring} := by
    rintro V ⟨⟨_, hVW⟩, hVK⟩
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hcon
    have hVU : V ∈ ofRingHom sU := mem_ofRingHom.2 hcon
    have heq := extension_unique (toSpecValuationSubring_comp_extensionOfMem hW hηW V hVW)
      (toSpecValuationSubring_comp_extensionOfMem hU hηU V hVU)
    have hxW := extensionOfMem_closedPoint hW hηW V hVW
    have hxU := extensionOfMem_closedPoint hU hηU V hVU
    rw [← heq] at hxU
    obtain ⟨g, hg, hxg⟩ := hGcov _ hxU hxW
    rw [extensionOfMem_closedPoint_mem_basicOpen_iff] at hxg
    simp only [Set.mem_iInter] at hVK
    exact hxg (hVK g hg)
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover _ (fun a => isPatchOpen_not_mem (sU a)) hcov
  classical
  refine ⟨T.image sU, by simp, ?_⟩
  rintro V ⟨_, hVW⟩ hVF
  apply hgood V hVW
  by_contra hcon
  push Not at hcon
  have hVK : V ∈ K := ⟨⟨hηW, hVW⟩, by simpa using hcon⟩
  have := hT hVK
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at this
  obtain ⟨a, ha, haV⟩ := this
  exact haV (hVF (Finset.mem_image_of_mem sU ha))

/-- For a separated quasi-compact scheme `S` and an affine open `U`, every point of `RZ_L(U)` has a
basic open neighbourhood whose trace on `RZ_L(S)` lies in `RZ_L(U)`. -/
theorem exists_basicOpen_inter_ofScheme_subset [S.IsSeparated] [CompactSpace S] {U : S.Opens}
    (hU : IsAffineOpen U) {V : RiemannZariskiSpace L} (hV : V ∈ ofOpen η U) :
    ∃ F : Finset L, V ∈ basicOpen F ∧ basicOpen F ∩ ofScheme η ⊆ ofOpen η U := by
  obtain ⟨hηU, hVU⟩ := hV
  obtain ⟨t, ht⟩ := exists_finite_affine_cover (S := S)
  choose F hFU hF using fun W : S.affineOpens => exists_finset_of_affine_pair (η := η) hU W.2 hηU
  classical
  refine ⟨t.biUnion F, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hx
    obtain ⟨W, -, hxW⟩ := hx
    obtain ⟨a, rfl⟩ := hFU W hxW
    exact mem_ofRingHom.1 hVU a
  · rintro V' ⟨hV'F, hV'⟩
    rw [ofScheme_eq_iUnion (fun W : t => (W.1 : S.Opens)) (fun W => W.1.2) (fun x => by
      obtain ⟨U, hU, hxU⟩ := ht x
      exact ⟨⟨U, hU⟩, hxU⟩)] at hV'
    obtain ⟨⟨W, hWt⟩, hV'W⟩ := Set.mem_iUnion.1 hV'
    exact hF W V' hV'W (fun x hx => hV'F (Finset.mem_biUnion.2 ⟨W, hWt, hx⟩))

/-- **Openness of affine pieces** (Temkin, Lemma 3.2.9, for separated `S`): for a separated
quasi-compact scheme `S` and an affine open `U`, `RZ_L(U)` is open in `RZ_L(S)`. -/
theorem isOpen_ofOpen [S.IsSeparated] [CompactSpace S] {U : S.Opens} (hU : IsAffineOpen U) :
    IsOpen (ofScheme η ↓∩ ofOpen η U) := by
  rw [isOpen_iff_forall_mem_open]
  intro V hV
  obtain ⟨F, hVF, hF⟩ := exists_basicOpen_inter_ofScheme_subset hU hV
  exact ⟨ofScheme η ↓∩ basicOpen F, fun W hW => hF ⟨hW, W.2⟩,
    (isOpen_basicOpen F).preimage continuous_subtype_val, hVF⟩

variable (η) in
/-- The center of a point `V ∈ RZ_L(S)`: the image in `S` of the closed point of `Spec V` under a
chosen extension of `η` (unique when `S` is separated). -/
noncomputable def ofScheme.center (V : ofScheme η) : S :=
  V.2.choose (specClosedPoint V.1)

/-- For an affine open `U` of a separated scheme, the center of `V` lies in `U` iff `V` contains
the image of `Γ(S, U)`. -/
lemma ofScheme.center_mem_iff [S.IsSeparated] {U : S.Opens} (hU : IsAffineOpen U)
    (V : ofScheme η) : ofScheme.center η V ∈ U ↔ V.1 ∈ ofOpen η U := by
  constructor
  · intro h
    exact mem_ofOpen_of_extension _ V.2.choose_spec h
  · rintro ⟨hηU, hVU⟩
    rw [ofScheme.center, extension_unique V.2.choose_spec
      (toSpecValuationSubring_comp_extensionOfMem hU hηU _ hVU)]
    exact extensionOfMem_closedPoint hU hηU _ hVU

/-- **Continuity of the center map** `RZ_L(S) → S` for a separated quasi-compact scheme `S`
(Temkin, Lemma 3.2.9: the topology of `RZ_L(S)` is induced from the absolute
Riemann–Zariski space). -/
theorem ofScheme.continuous_center [S.IsSeparated] [CompactSpace S] :
    Continuous (ofScheme.center η) := by
  rw [TopologicalSpace.IsTopologicalBasis.continuous_iff S.isBasis_affineOpens]
  rintro _ ⟨U, hU, rfl⟩
  have : ofScheme.center η ⁻¹' (U : Set S) = ofScheme η ↓∩ ofOpen η U := by
    ext V
    exact ofScheme.center_mem_iff hU V
  rw [this]
  exact isOpen_ofOpen hU

/-! ### Functoriality: quasi-modifications and modifications -/

/-- A factorization `η = η' ≫ f` gives an inclusion `RZ_L(S') ⊆ RZ_L(S)`. -/
lemma ofScheme_subset_of_comp (f : S' ⟶ S) {η' : Spec (.of L) ⟶ S'} (h : η' ≫ f = η) :
    ofScheme η' ⊆ ofScheme η :=
  fun _ ⟨φ, hφ⟩ => ⟨φ ≫ f, by rw [← Category.assoc, hφ, h]⟩

/-- Compatibility of `sectionsToField` with a factorization `η = η' ≫ f`. -/
lemma sectionsToField_comp_appLE (f : S' ⟶ S) {η' : Spec (.of L) ⟶ S'} (h : η' ≫ f = η)
    {U : S.Opens} {U' : S'.Opens} (e : U' ≤ f ⁻¹ᵁ U) (hη'U' : η' ⁻¹ᵁ U' = ⊤)
    (hηU : η ⁻¹ᵁ U = ⊤) :
    (sectionsToField η' U' hη'U').comp (f.appLE U U' e).hom = sectionsToField η U hηU := by
  subst h
  rw [sectionsToField, sectionsToField, ← CommRingCat.hom_comp, ← Category.assoc,
    Scheme.Hom.appLE_comp_appLE]

/-- **Temkin, Corollary 3.2.7 (`openembcor`).** Let `S` be separated and quasi-compact, `f : S' → S`
locally of finite type, and `η = η' ≫ f`. Then `RZ_L(S')` is open in `RZ_L(S)`. -/
theorem isOpen_ofScheme_of_locallyOfFiniteType [S.IsSeparated] [CompactSpace S] (f : S' ⟶ S)
    [LocallyOfFiniteType f] {η' : Spec (.of L) ⟶ S'} (h : η' ≫ f = η) :
    IsOpen (ofScheme η ↓∩ ofScheme η') := by
  rw [isOpen_iff_forall_mem_open]
  rintro V ⟨φ', hφ'⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hcU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (φ' (specClosedPoint V.1)))) isOpen_univ
  obtain ⟨_, ⟨U', hU', rfl⟩, hcU', hU'U⟩ := S'.isBasis_affineOpens.exists_subset_of_mem_open
    (show φ' (specClosedPoint V.1) ∈ f ⁻¹ᵁ U from hcU) (f ⁻¹ᵁ U).isOpen
  obtain ⟨hη'U', hVU'⟩ := mem_ofOpen_of_extension φ' hφ' hcU'
  have hφf : toSpecValuationSubring V.1 ≫ (φ' ≫ f) = η := by rw [← Category.assoc, hφ', h]
  obtain ⟨hηU, hVU⟩ := mem_ofOpen_of_extension (φ' ≫ f) hφf
    (by rw [Scheme.Hom.comp_apply]; exact hcU)
  obtain ⟨G, hVG, hG⟩ := exists_basicOpen_inter_ofScheme_subset hU ⟨hηU, hVU⟩
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨U, hU⟩ ⟨U', hU'⟩ hU'U
  obtain ⟨F, hFr, hF⟩ := exists_finset_ofRingHom_eq _ hft (sectionsToField η' U' hη'U')
  rw [sectionsToField_comp_appLE f h hU'U hη'U' hηU] at hF
  classical
  refine ⟨ofScheme η ↓∩ basicOpen (G ∪ F), ?_,
    (isOpen_basicOpen _).preimage continuous_subtype_val, ?_⟩
  · intro W hW
    rw [Set.mem_preimage, basicOpen_union] at hW
    have hWU := hG ⟨hW.1, W.2⟩
    have hWU' : W.1 ∈ ofRingHom (sectionsToField η' U' hη'U') := by
      rw [hF]
      exact ⟨(mem_ofOpen_iff hηU).1 hWU, hW.2⟩
    exact ofOpen_subset_ofScheme hU' ⟨hη'U', hWU'⟩
  · rw [Set.mem_preimage, basicOpen_union]
    refine ⟨hVG, fun x hx => ?_⟩
    obtain ⟨b, rfl⟩ := hFr hx
    exact mem_ofRingHom.1 hVU' b

/-- **Temkin, Corollary 3.2.7 (`openembcor`).** For a separated quasi-compact scheme `S`, a morphism
`f : S' → S` locally of finite type and `η = η' ≫ f` (e.g. an `L`-quasi-modification), the map
`RZ_L(S') → RZ_L(S)` is an open embedding. -/
theorem isOpenEmbedding_inclusion_ofScheme [S.IsSeparated] [CompactSpace S] (f : S' ⟶ S)
    [LocallyOfFiniteType f] {η' : Spec (.of L) ⟶ S'} (h : η' ≫ f = η) :
    IsOpenEmbedding (Set.inclusion (ofScheme_subset_of_comp f h)) :=
  .inclusion _ (isOpen_ofScheme_of_locallyOfFiniteType f h)

/-- **Modifications** (valuative criterion of universal closedness, Temkin §3.2 before Corollary
3.2.5 `bijcor`): for `f : S' → S` universally closed (e.g. proper, as for an `L`-modification) and
`η = η' ≫ f`, every extension of `η` lifts to `S'`, so `RZ_L(S') = RZ_L(S)`. -/
theorem ofScheme_eq_of_universallyClosed (f : S' ⟶ S) [UniversallyClosed f]
    {η' : Spec (.of L) ⟶ S'} (h : η' ≫ f = η) : ofScheme η' = ofScheme η := by
  refine (ofScheme_subset_of_comp f h).antisymm ?_
  rintro V ⟨φ, hφ⟩
  have hex : ValuativeCriterion.Existence f := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact this.1
  let sq : ValuativeCommSq f :=
    { R := V.valuationSubring, K := L, i₁ := η', i₂ := φ, commSq := ⟨by rw [h, hφ]⟩ }
  obtain ⟨l⟩ := (hex sq).exists_lift
  exact ⟨l.l, l.fac_left⟩

/-- For `f : S' → S` universally closed (e.g. proper) and `η = η' ≫ f`, the Riemann–Zariski spaces
`RZ_L(S')` and `RZ_L(S)` are homeomorphic via the identity of valuation rings. -/
noncomputable def ofSchemeHomeomorph (f : S' ⟶ S) [UniversallyClosed f]
    {η' : Spec (.of L) ⟶ S'} (h : η' ≫ f = η) : ofScheme η' ≃ₜ ofScheme η :=
  Homeomorph.setCongr (ofScheme_eq_of_universallyClosed f h)

@[simp]
lemma coe_ofSchemeHomeomorph (f : S' ⟶ S) [UniversallyClosed f]
    {η' : Spec (.of L) ⟶ S'} (h : η' ≫ f = η) (V : ofScheme η') :
    (ofSchemeHomeomorph f h V : RiemannZariskiSpace L) = V :=
  rfl

end RiemannZariskiSpace

end DeJongAlterations.StableModification
