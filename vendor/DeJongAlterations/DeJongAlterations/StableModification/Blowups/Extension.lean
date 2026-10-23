import DeJongAlterations.StableModification.Blowups.Basic
import DeJongAlterations.StableModification.Curves.Basic

/-!
# Extending a modification of an open by the identity

M. Temkin, *Stable modification of relative curves*, proof of Prop 4.3.1 (T:2970–2975): "We will
build these blow ups so that `x` is the only closed point of the modification locus; this allows
to work locally at `x` since each such blow up extends trivially from a neighborhood of `x` to all
of `C`." This file provides that extension (`lem:sm-modification-extension`).

Let `C` be a scheme, `U, W ⊆ C` opens with `U ∪ W = C` (think: `W = C ∖ Z` for a closed `Z ⊆ U`,
the modification locus), and `f : U' ⟶ U` a morphism which is an isomorphism over `U ∩ W`. Gluing
`U'` and `W` along `f⁻¹(U ∩ W) ≅ U ∩ W` (a colimit of a wide span of open immersions in schemes,
Mathlib's `Scheme.IsLocallyDirected`) gives `extensionHom f : extension f ⟶ C` with

* `U' ≅ (extensionHom f)⁻¹(U)` over `U` (`extensionPreimageIso`, `extensionPreimageIso_hom_comp`),
* `extensionHom f` an isomorphism over `W` (`isIso_extensionHom_restrict`),
* `extensionHom f` proper if `f` is (`isProper_extensionHom`), and a modification of an integral
  `C` if `f` is a modification and `W ≠ ∅` (`isModification_extensionHom`).

We also record that the image of a scheme proper over `S` in a separated `S`-scheme is closed
(`isClosed_range_of_isProper_comp`): this is how the closedness of the modification locus in `C`
is checked when it is finite over the base.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Closed

/-- The image of a morphism `i : T ⟶ C` with `T` proper over `S` and `C` separated over `S` is
closed. -/
theorem isClosed_range_of_isProper_comp {T C S : Scheme.{u}} (i : T ⟶ C) (g : C ⟶ S)
    [IsProper (i ≫ g)] [IsSeparated g] : IsClosed (Set.range i) := by
  have := IsProper.of_comp i g
  exact i.isClosedMap.isClosed_range

end Closed

section Extension

/-- The pieces of the gluing: `U'` and `W`. -/
def extensionObj (U' : Scheme.{u}) {C : Scheme.{u}} (W : C.Opens) : Bool → Scheme.{u}
  | false => U'
  | true => W.toScheme

variable {C U' : Scheme.{u}} {U : C.Opens} (W : C.Opens) (f : U' ⟶ U.toScheme)

/-- The two open immersions out of `f⁻¹(U ∩ W)`: the inclusion into `U'`, and
`f⁻¹(U ∩ W) ≅ U ∩ W ⊆ W`. -/
def extensionArrow [IsIso (f ∣_ (U.ι ⁻¹ᵁ W))] :
    (b : Bool) → (f ⁻¹ᵁ (U.ι ⁻¹ᵁ W)).toScheme ⟶ extensionObj U' W b
  | false => (f ⁻¹ᵁ (U.ι ⁻¹ᵁ W)).ι
  | true => (f ∣_ (U.ι ⁻¹ᵁ W)) ≫ (C.restrictRestrictComm U W).hom ≫ (W.ι ⁻¹ᵁ U).ι

variable [IsIso (f ∣_ (U.ι ⁻¹ᵁ W))]

instance (b : Bool) : IsOpenImmersion (extensionArrow W f b) := by
  cases b <;> dsimp only [extensionArrow] <;> infer_instance

/-- The wide span along which `U'` and `W` are glued. -/
def extensionSpan : WidePushoutShape Bool ⥤ Scheme.{u} :=
  WidePushoutShape.wideSpan _ (extensionObj U' W) (extensionArrow W f)

instance extensionSpan_isOpenImmersion {i j : WidePushoutShape Bool} (g : i ⟶ j) :
    IsOpenImmersion ((extensionSpan W f).map g) := by
  rcases g with _ | b
  · erw [CategoryTheory.Functor.map_id]
    infer_instance
  · change IsOpenImmersion (extensionArrow W f b)
    infer_instance

/-- **The extension of `f` by the identity**: `U'` and `W` glued along `f⁻¹(U ∩ W) ≅ U ∩ W`. -/
def extension : Scheme.{u} := colimit (extensionSpan W f)

/-- The open immersion `U' ⟶ extension f`. -/
def extensionι₁ : U' ⟶ extension W f := colimit.ι (extensionSpan W f) (some false)

/-- The open immersion `W ⟶ extension f`. -/
def extensionι₂ : W.toScheme ⟶ extension W f := colimit.ι (extensionSpan W f) (some true)

instance : IsOpenImmersion (extensionι₁ W f) := by
  dsimp only [extensionι₁]
  infer_instance

instance : IsOpenImmersion (extensionι₂ W f) := by
  dsimp only [extensionι₂]
  infer_instance

/-- The maps of the two pieces to `C`. -/
def extensionToBase : (b : Bool) → extensionObj U' W b ⟶ C
  | false => f ≫ U.ι
  | true => W.ι

theorem restrictRestrictComm_hom_ι_ι :
    (C.restrictRestrictComm U W).hom ≫ (W.ι ⁻¹ᵁ U).ι ≫ W.ι = (U.ι ⁻¹ᵁ W).ι ≫ U.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem extensionArrow_toBase (b : Bool) :
    extensionArrow W f b ≫ extensionToBase W f b = (f ⁻¹ᵁ (U.ι ⁻¹ᵁ W)).ι ≫ f ≫ U.ι := by
  cases b
  · rfl
  · change ((f ∣_ (U.ι ⁻¹ᵁ W)) ≫ (C.restrictRestrictComm U W).hom ≫ (W.ι ⁻¹ᵁ U).ι) ≫ W.ι = _
    rw [Category.assoc, Category.assoc, restrictRestrictComm_hom_ι_ι, ← Category.assoc,
      morphismRestrict_ι, Category.assoc]

/-- **The map from the extension to `C`.** -/
def extensionHom : extension W f ⟶ C :=
  colimit.desc (extensionSpan W f)
    (WidePushoutShape.mkCocone ((f ⁻¹ᵁ (U.ι ⁻¹ᵁ W)).ι ≫ f ≫ U.ι) (extensionToBase W f)
      (extensionArrow_toBase W f))

@[reassoc (attr := simp)]
theorem extensionι₁_extensionHom : extensionι₁ W f ≫ extensionHom W f = f ≫ U.ι := by
  rw [extensionι₁, extensionHom, colimit.ι_desc]
  rfl

@[reassoc (attr := simp)]
theorem extensionι₂_extensionHom : extensionι₂ W f ≫ extensionHom W f = W.ι := by
  rw [extensionι₂, extensionHom, colimit.ι_desc]
  rfl

/-- The gluing relation of the colimit. -/
theorem extensionArrow_ι (b : Bool) :
    extensionArrow W f b ≫ colimit.ι (extensionSpan W f) (some b) =
      colimit.ι (extensionSpan W f) none :=
  colimit.w (extensionSpan W f) (WidePushoutShape.Hom.init b)

/-- The two pieces agree on the overlap. -/
theorem extensionι_glue (x : (f ⁻¹ᵁ (U.ι ⁻¹ᵁ W)).toScheme) :
    extensionι₁ W f ((f ⁻¹ᵁ (U.ι ⁻¹ᵁ W)).ι x) =
      extensionι₂ W f (extensionArrow W f true x) := by
  change (extensionArrow W f false ≫ colimit.ι (extensionSpan W f) (some false)) x =
    (extensionArrow W f true ≫ colimit.ι (extensionSpan W f) (some true)) x
  rw [extensionArrow_ι, extensionArrow_ι]

/-- Every point of the extension comes from `U'` or from `W`. -/
theorem extension_jointly_surjective (y : extension W f) :
    y ∈ Set.range (extensionι₁ W f) ∨ y ∈ Set.range (extensionι₂ W f) := by
  obtain ⟨i, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (extensionSpan W f) y
  rcases i with _ | b
  · left
    refine ⟨(f ⁻¹ᵁ (U.ι ⁻¹ᵁ W)).ι x, ?_⟩
    have h := congrArg (fun g : (extensionSpan W f).obj none ⟶ extension W f => g x)
      (extensionArrow_ι W f false)
    exact h
  · cases b
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨x, rfl⟩

/-- The extension maps onto `C` over `W` via `ι₂`. -/
theorem extensionHom_ι₂_apply (w : W.toScheme) :
    extensionHom W f (extensionι₂ W f w) = W.ι w := by
  rw [← Scheme.Hom.comp_apply, extensionι₂_extensionHom]

theorem extensionHom_ι₁_apply (x : U') :
    extensionHom W f (extensionι₁ W f x) = U.ι (f x) := by
  rw [← Scheme.Hom.comp_apply, extensionι₁_extensionHom, Scheme.Hom.comp_apply]

/-- The inverse image of `W` in the extension is the piece `W`. -/
theorem extensionHom_preimage_W :
    ((extensionHom W f ⁻¹ᵁ W : (extension W f).Opens) : Set (extension W f)) =
      Set.range (extensionι₂ W f) := by
  ext y
  constructor
  · intro hy
    rcases extension_jointly_surjective W f y with ⟨x, rfl⟩ | h
    · have hx : x ∈ f ⁻¹ᵁ (U.ι ⁻¹ᵁ W) := by
        change U.ι (f x) ∈ W
        rw [← extensionHom_ι₁_apply W f]
        exact hy
      exact ⟨extensionArrow W f true ⟨x, hx⟩, (extensionι_glue W f ⟨x, hx⟩).symm⟩
    · exact h
  · rintro ⟨w, rfl⟩
    change extensionHom W f (extensionι₂ W f w) ∈ W
    rw [extensionHom_ι₂_apply]
    exact w.2

/-- The range of the second gluing arrow is `W ∩ U`. -/
theorem range_extensionArrow_true :
    Set.range (extensionArrow W f true) = ((W.ι ⁻¹ᵁ U : W.toScheme.Opens) : Set W.toScheme) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change (W.ι ⁻¹ᵁ U).ι ((C.restrictRestrictComm U W).hom ((f ∣_ (U.ι ⁻¹ᵁ W)) x)) ∈ _
    rw [Scheme.Opens.ι_apply]
    exact Subtype.property _
  · intro w hw
    obtain ⟨v, hv⟩ := (C.restrictRestrictComm U W).hom.surjective ⟨w, hw⟩
    obtain ⟨x, rfl⟩ := (f ∣_ (U.ι ⁻¹ᵁ W)).surjective v
    refine ⟨x, ?_⟩
    change (W.ι ⁻¹ᵁ U).ι ((C.restrictRestrictComm U W).hom ((f ∣_ (U.ι ⁻¹ᵁ W)) x)) = w
    rw [hv, Scheme.Opens.ι_apply]

/-- The inverse image of `U` in the extension is the piece `U'`. -/
theorem extensionHom_preimage_U :
    ((extensionHom W f ⁻¹ᵁ U : (extension W f).Opens) : Set (extension W f)) =
      Set.range (extensionι₁ W f) := by
  ext y
  constructor
  · intro hy
    rcases extension_jointly_surjective W f y with h | ⟨w, rfl⟩
    · exact h
    · have hw : w ∈ ((W.ι ⁻¹ᵁ U : W.toScheme.Opens) : Set W.toScheme) := by
        change W.ι w ∈ U
        rw [← extensionHom_ι₂_apply W f]
        exact hy
      rw [← range_extensionArrow_true W f] at hw
      obtain ⟨x, rfl⟩ := hw
      exact ⟨_, extensionι_glue W f x⟩
  · rintro ⟨x, rfl⟩
    change extensionHom W f (extensionι₁ W f x) ∈ U
    rw [extensionHom_ι₁_apply]
    exact (f x).2

/-- `W ≅ (extensionHom f)⁻¹(W)`. -/
def extensionPreimageWIso : W.toScheme ≅ (extensionHom W f ⁻¹ᵁ W).toScheme :=
  IsOpenImmersion.isoOfRangeEq (extensionι₂ W f) (extensionHom W f ⁻¹ᵁ W).ι (by
    rw [Scheme.Opens.range_ι, extensionHom_preimage_W])

/-- **The extension is an isomorphism over `W`.** -/
instance isIso_extensionHom_restrict : IsIso (extensionHom W f ∣_ W) := by
  have h : (extensionPreimageWIso W f).hom ≫ (extensionHom W f ∣_ W) = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, Category.id_comp]
    rw [← Category.assoc, extensionPreimageWIso, IsOpenImmersion.isoOfRangeEq_hom_fac,
      extensionι₂_extensionHom]
  have : extensionHom W f ∣_ W = (extensionPreimageWIso W f).inv :=
    (Iso.hom_comp_eq_id _).mp h
  rw [this]
  infer_instance

/-- **`U' ≅ (extensionHom f)⁻¹(U)`.** -/
def extensionPreimageIso : U' ≅ (extensionHom W f ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.isoOfRangeEq (extensionι₁ W f) (extensionHom W f ⁻¹ᵁ U).ι (by
    rw [Scheme.Opens.range_ι, extensionHom_preimage_U])

@[reassoc (attr := simp)]
theorem extensionPreimageIso_hom_ι :
    (extensionPreimageIso W f).hom ≫ (extensionHom W f ⁻¹ᵁ U).ι = extensionι₁ W f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Over `U`, the extension is `f`. -/
@[reassoc (attr := simp)]
theorem extensionPreimageIso_hom_comp :
    (extensionPreimageIso W f).hom ≫ (extensionHom W f ∣_ U) = f := by
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, extensionPreimageIso_hom_ι_assoc,
    extensionι₁_extensionHom]

variable (hUW : U ⊔ W = ⊤)
include hUW

/-- **The extension of a proper morphism is proper.** -/
theorem isProper_extensionHom [IsProper f] : IsProper (extensionHom W f) := by
  have hcov : (⨆ b : Bool, if b then U else W) = ⊤ := by
    rw [← hUW]
    apply le_antisymm
    · exact iSup_le fun b => by cases b <;> simp
    · exact sup_le (le_iSup_of_le true (le_of_eq rfl)) (le_iSup_of_le false (le_of_eq rfl))
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) _ hcov fun b => ?_
  cases b
  · change IsProper (extensionHom W f ∣_ W)
    infer_instance
  · change IsProper (extensionHom W f ∣_ U)
    have : extensionHom W f ∣_ U = (extensionPreimageIso W f).inv ≫ f := by
      rw [Iso.eq_inv_comp, extensionPreimageIso_hom_comp]
    rw [this]
    infer_instance

/-- **The extension of a modification is a modification**: for integral `C`, a proper
`f : U' ⟶ U` with `U'` integral which is an isomorphism over `U ∩ W`, with `U ∪ W = C` and
`W ≠ ∅`, extends by the identity to a modification of `C` (in particular this applies to a
modification `f` of `U`). -/
theorem isModification_extensionHom [IsIntegral C] [IsIntegral U']
    [IsProper f] (hW : (W : Set C).Nonempty) :
    IsModification (extensionHom W f) := by
  have hprop := isProper_extensionHom W f hUW
  -- the pieces are integral and meet
  have hWne : Nonempty W.toScheme := hW.to_subtype
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  obtain ⟨x₀⟩ : Nonempty U' := inferInstance
  have hUne : (U : Set C).Nonempty := ⟨_, (f x₀).2⟩
  obtain ⟨c, hcU, hcW⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen hUne hW
  have hV : Nonempty (U.ι ⁻¹ᵁ W).toScheme := ⟨⟨⟨c, hcU⟩, hcW⟩⟩
  have hV' : Nonempty (f ⁻¹ᵁ (U.ι ⁻¹ᵁ W)).toScheme := by
    obtain ⟨v⟩ := hV
    obtain ⟨x, hx⟩ := (f ∣_ (U.ι ⁻¹ᵁ W)).surjective v
    exact ⟨x⟩
  let 𝒰 : (extension W f).OpenCover :=
    Scheme.Cover.mkOfCovers Bool (extensionObj U' W)
      (fun b => colimit.ι (extensionSpan W f) (some b)) (by
        intro y
        rcases extension_jointly_surjective W f y with ⟨x, rfl⟩ | ⟨x, rfl⟩
        · exact ⟨false, x, rfl⟩
        · exact ⟨true, x, rfl⟩)
  have hint : ∀ b, IsIntegral (𝒰.X b) := by
    intro b
    cases b
    · exact inferInstanceAs (IsIntegral U')
    · exact inferInstanceAs (IsIntegral W.toScheme)
  have : IsReduced (extension W f) := by
    have : ∀ b, IsReduced (𝒰.X b) := fun b => by
      have := hint b
      infer_instance
    exact IsReduced.of_openCover (extension W f) 𝒰
  have hpair : Pairwise (fun i j : Bool =>
      ¬ Disjoint (𝒰.f i).opensRange (𝒰.f j).opensRange) := by
    intro i j hij
    obtain ⟨x⟩ := hV'
    have h1 : extensionι₁ W f ((f ⁻¹ᵁ (U.ι ⁻¹ᵁ W)).ι x) ∈ (𝒰.f false).opensRange := ⟨_, rfl⟩
    have h2 : extensionι₁ W f ((f ⁻¹ᵁ (U.ι ⁻¹ᵁ W)).ι x) ∈ (𝒰.f true).opensRange := by
      rw [extensionι_glue]
      exact ⟨_, rfl⟩
    intro hd
    cases i <;> cases j
    · exact hij rfl
    · exact hd.le_bot ⟨h1, h2⟩
    · exact hd.le_bot ⟨h2, h1⟩
    · exact hij rfl
  have hpre (i : Bool) : PreirreducibleSpace (𝒰.f i).opensRange := by
    apply isPreirreducible_iff_preirreducibleSpace.mp
    have := hint i
    have h := (PreirreducibleSpace.isPreirreducible_univ :
      IsPreirreducible (Set.univ : Set (𝒰.X i))).image
      (𝒰.f i) (𝒰.f i).continuous.continuousOn
    simpa only [Set.image_univ, Scheme.Hom.coe_opensRange] using h
  have : PreirreducibleSpace (extension W f) :=
    PreirreducibleSpace.of_isOpenCover hpair 𝒰.isOpenCover_opensRange hpre
  have : Nonempty (extension W f) := ⟨extensionι₁ W f x₀⟩
  have : IrreducibleSpace (extension W f) :=
    { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  have : IsIntegral (extension W f) := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsDominant (extensionHom W f) := by
    refine ⟨(W.isOpen.dense hW).mono ?_⟩
    intro y hy
    exact ⟨extensionι₂ W f ⟨y, hy⟩, extensionHom_ι₂_apply W f ⟨y, hy⟩⟩
  exact { toIsProper := hprop
          sourceIntegral := inferInstance
          targetIntegral := inferInstance
          birational := birationalOver_id_of_isIso_morphismRestrict _ W hW }

end Extension

end DeJongAlterations.StableModification.Blowups
