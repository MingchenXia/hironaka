import DeJongAlterations.StableModification.Curves.Basic
import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Gluing models along an open cover of the base

The last step of the proof of Temkin's Theorem 1.5 (*Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), `semi-stable.tex`, T:3394–3397, node G7 of `PLAN-T5.md` §2.1 step
5) glues stable modifications `X_i ⟶ C ×_S U_i` defined over the members `U_i` of a finite open
cover of the base `S''`, using isomorphisms over `C` on the overlaps. This file provides the two
general ingredients.

* **Rigidity** (`eq_of_comp_eq_of_isIso_fiberMap`): over an integral base `T`, two morphisms
  `f₁, f₂ : X₁ ⟶ X₂` over `P` (`β₂ ∘ f_k = β₁`) agree as soon as `X₁` is flat over `T`, `β₂` is
  separated and an isomorphism on generic fibres. Indeed the generic fibre of `X₁` is
  schematically dense in `X₁` (flat base change of `Spec κ(η) → T`), both maps agree there
  because `β₂` is an isomorphism over `η`, and the equalizer of two maps into a separated
  `P`-scheme is a closed subscheme containing a schematically dense one
  (`ext_of_isSchemeTheoreticallyDominant`). Hence isomorphisms of stable η-modifications over `C`
  are unique (Temkin T:3395: "the isomorphisms are unique, so they glue").
* **Gluing** (`exists_glue`): schemes `X_i` over `P` lying over the members `U_i` of an open
  cover of `T`, with open immersions `φ_ij : X_i|_{U_j} ⟶ X_j` over `P` onto `X_j|_{U_i}`, glue
  to a scheme `X ⟶ P` containing each `X_i` as the preimage of `U_i`, provided morphisms from
  opens of the `X_i` to the `X_j` over `P` (lying over the inclusion into `X_i`) are unique
  (which gives the cocycle condition for free). The proof uses Mathlib's relative gluing
  (`Scheme.Cover.RelativeGluingData`,
  Stacks 01LH) over the locally directed cover of `T` by the opens contained in some `U_i`.
* **Gluing morphisms** (`exists_glueHom`): with rigidity, morphisms over `P` defined locally on
  an open cover of the source glue (the form in which the second refinement of `PLAN-T5.md`
  §2.1 step 4 produces the isomorphisms `φ_ij`).

Blueprint: `sm-global.tex`, `lem:sm-global-rigidity`, `lem:sm-global-glue`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

section Rigidity

/-- **Morphisms into a separated scheme are determined on a schematically dense subscheme.**
If `f, g : X ⟶ Y` agree over a separated `s : Y ⟶ Z` and after composing with a
scheme-theoretically dominant `ι : W ⟶ X`, then `f = g`. (The equalizer is a closed subscheme of
`X` through which `ι` factors, so its ideal sheaf vanishes.) -/
theorem ext_of_isSchemeTheoreticallyDominant {W X Y Z : Scheme.{u}} {f g : X ⟶ Y} (s : Y ⟶ Z)
    [IsSeparated s] (h : f ≫ s = g ≫ s) (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι]
    (hι : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g (by simp [X', Y', h])
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have hl : ι' ≫ f' = ι' ≫ g' := by
    ext1
    exact hι
  have hfac : (equalizer.lift ι' hl).left ≫ (equalizer.ι f' g').left = ι := by
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hle : (equalizer.ι f' g').left.ker ≤ ι.ker := by
    rw [← hfac, Scheme.Hom.ker_comp, ← Scheme.IdealSheafData.map_bot]
    exact Scheme.IdealSheafData.map_mono _ bot_le
  rw [ι.ker_eq_bot, le_bot_iff] at hle
  have : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hle
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

/-- The generic point of an integral scheme, as a morphism from the spectrum of its residue
field, is scheme-theoretically dominant and quasi-compact. -/
theorem isSchemeTheoreticallyDominant_fromSpecResidueField_genericPoint (T : Scheme.{u})
    [IsIntegral T] :
    IsSchemeTheoreticallyDominant (T.fromSpecResidueField (genericPoint T)) ∧
      QuasiCompact (T.fromSpecResidueField (genericPoint T)) := by
  have : Subsingleton (Spec (T.residueField (genericPoint T))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum _))
  have hqc : QuasiCompact (T.fromSpecResidueField (genericPoint T)) :=
    ⟨fun _ _ _ ↦ Set.subsingleton_of_subsingleton.isCompact⟩
  have : IsDominant (T.fromSpecResidueField (genericPoint T)) := by
    refine ⟨?_⟩
    have hr : Set.range (T.fromSpecResidueField (genericPoint T)) = {genericPoint T} := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        rw [Subsingleton.elim z (IsLocalRing.closedPoint _)]
        exact Scheme.fromSpecResidueField_apply _ _
      · rintro rfl
        exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply _ _⟩
    rw [DenseRange, hr, dense_iff_closure_eq]
    exact (genericPoint_spec T).def
  exact ⟨.of_isDominant _, hqc⟩

/-- **Rigidity of η-modifications** (Temkin T:3395). Let `T` be integral, `g : P ⟶ T`, and
`β₁ : X₁ ⟶ P`, `β₂ : X₂ ⟶ P` with `X₁` flat over `T`, `β₂` separated and an isomorphism on the
generic fibres. Two morphisms `f₁, f₂ : X₁ ⟶ X₂` over `P` are equal. -/
theorem eq_of_comp_eq_of_isIso_fiberMap {T P X₁ X₂ : Scheme.{u}} [IsIntegral T] (g : P ⟶ T)
    (β₁ : X₁ ⟶ P) (β₂ : X₂ ⟶ P) [IsSeparated β₂] [Flat (β₁ ≫ g)]
    [IsIso (Curves.fiberMap β₂ g (genericPoint T))] {f₁ f₂ : X₁ ⟶ X₂} (h₁ : f₁ ≫ β₂ = β₁)
    (h₂ : f₂ ≫ β₂ = β₁) : f₁ = f₂ := by
  obtain ⟨_, _⟩ := isSchemeTheoreticallyDominant_fromSpecResidueField_genericPoint T
  set F := T.fromSpecResidueField (genericPoint T)
  have : IsSchemeTheoreticallyDominant (pullback.fst (β₁ ≫ g) F) :=
    IsSchemeTheoreticallyDominant.pullbackFst _ _
  refine ext_of_isSchemeTheoreticallyDominant β₂ (by rw [h₁, h₂]) (pullback.fst (β₁ ≫ g) F) ?_
  have hc : ∀ f : X₁ ⟶ X₂, f ≫ β₂ = β₁ →
      (pullback.fst (β₁ ≫ g) F ≫ f) ≫ β₂ ≫ g = pullback.snd (β₁ ≫ g) F ≫ F := by
    intro f hf
    rw [Category.assoc, reassoc_of% hf, pullback.condition]
  let L : ∀ f : X₁ ⟶ X₂, f ≫ β₂ = β₁ →
      (pullback (C := Scheme.{u}) (β₁ ≫ g) F ⟶ pullback (C := Scheme.{u}) (β₂ ≫ g) F) :=
    fun f hf ↦ pullback.lift _ _ (hc f hf)
  have hL : ∀ (f : X₁ ⟶ X₂) (hf : f ≫ β₂ = β₁),
      L f hf ≫ Curves.pullbackCompMap β₂ g F =
        pullback.lift (pullback.fst (β₁ ≫ g) F ≫ β₁) (pullback.snd (β₁ ≫ g) F)
          (by rw [Category.assoc, pullback.condition]) := by
    intro f hf
    apply pullback.hom_ext
    · simp only [L, Category.assoc, Curves.pullbackCompMap_fst, pullback.lift_fst,
        pullback.lift_fst_assoc, hf]
    · simp only [L, Category.assoc, Curves.pullbackCompMap_snd, pullback.lift_snd]
  have : IsIso (Curves.pullbackCompMap β₂ g F) :=
    inferInstanceAs (IsIso (Curves.fiberMap β₂ g (genericPoint T)))
  have hL12 : L f₁ h₁ = L f₂ h₂ := by
    rw [← cancel_mono (Curves.pullbackCompMap β₂ g F), hL f₁ h₁, hL f₂ h₂]
  have e₁ : pullback.fst (β₁ ≫ g) F ≫ f₁ = L f₁ h₁ ≫ pullback.fst (β₂ ≫ g) F :=
    (pullback.lift_fst _ _ _).symm
  have e₂ : pullback.fst (β₁ ≫ g) F ≫ f₂ = L f₂ h₂ ≫ pullback.fst (β₂ ≫ g) F :=
    (pullback.lift_fst _ _ _).symm
  rw [e₁, e₂, hL12]

end Rigidity

section Glue

variable {T P : Scheme.{u}} (g : P ⟶ T) {ι : Type u} (U : ι → T.Opens)

/-- The index set of the refined directed cover: an open `O` of `T` inside a member `U i`. -/
structure GlueIdx (U : ι → T.Opens) : Type u where
  /-- The member of the cover. -/
  i : ι
  /-- The open. -/
  O : T.Opens
  le : O ≤ U i

instance : Preorder (GlueIdx U) := Preorder.lift GlueIdx.O

theorem GlueIdx.le_def {p q : GlueIdx U} : p ≤ q ↔ p.O ≤ q.O := Iff.rfl

variable {U} in
/-- The opens contained in some member cover `T`. -/
theorem GlueIdx.exists_ι_eq (hU : ⨆ i, U i = ⊤) (x : T) :
    ∃ (p : GlueIdx U) (y : p.O.toScheme), p.O.ι y = x := by
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨⟨i, U i, le_rfl⟩, ⟨x, hi⟩, rfl⟩

/-- The refined cover of `T` by the opens contained in some member of `U`, as an open cover with
index set `GlueIdx U`. -/
abbrev glueCover (hU : ⨆ i, U i = ⊤) : T.OpenCover.{u} where
  I₀ := GlueIdx U
  X p := p.O.toScheme
  f p := p.O.ι
  mem₀ := (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (GlueIdx U) (fun p ↦ p.O.toScheme)
    (fun p ↦ p.O.ι) (GlueIdx.exists_ι_eq hU)).mem₀

theorem opens_ι_mem {Z : Scheme.{u}} {V : Z.Opens} (x : V.toScheme) : V.ι x ∈ V := by
  have : V.ι x ∈ V.ι.opensRange := Scheme.Hom.mem_opensRange.mpr ⟨x, rfl⟩
  rwa [Scheme.Opens.opensRange_ι] at this

variable {U} in
theorem GlueIdx.directed {p q : GlueIdx U}
    (x : (pullback p.O.ι q.O.ι : Scheme.{u})) :
    ∃ (y : (p.O ⊓ q.O).toScheme),
      pullback.lift (T.homOfLE inf_le_left) (T.homOfLE inf_le_right)
        (by simp) y = x := by
  have hx₁ : (pullback.fst p.O.ι q.O.ι ≫ p.O.ι) x ∈ p.O := by
    rw [Scheme.Hom.comp_apply]
    exact opens_ι_mem _
  have hx₂ : (pullback.fst p.O.ι q.O.ι ≫ p.O.ι) x ∈ q.O := by
    rw [pullback.condition, Scheme.Hom.comp_apply]
    exact opens_ι_mem _
  obtain ⟨y, hy⟩ : ∃ y : (p.O ⊓ q.O).toScheme,
      (p.O ⊓ q.O).ι y = (pullback.fst p.O.ι q.O.ι ≫ p.O.ι) x := by
    apply Scheme.Hom.mem_opensRange.mp
    rw [Scheme.Opens.opensRange_ι]
    exact ⟨hx₁, hx₂⟩
  refine ⟨y, ?_⟩
  apply (pullback.fst p.O.ι q.O.ι ≫ p.O.ι).isOpenEmbedding.injective
  rw [← hy, ← Scheme.Hom.comp_apply (pullback.lift _ _ _) (pullback.fst p.O.ι q.O.ι ≫ p.O.ι),
    pullback.lift_fst_assoc, Scheme.homOfLE_ι]

instance glueCover_locallyDirected (hU : ⨆ i, U i = ⊤) : (glueCover U hU).LocallyDirected where
  trans {p q} h := T.homOfLE h.le
  trans_id p := Scheme.homOfLE_rfl _ _
  trans_comp {p q r} h₁ h₂ := (Scheme.homOfLE_homOfLE _ _ _).symm
  w {p q} h := Scheme.homOfLE_ι _ _
  directed {p q} x := by
    obtain ⟨y, hy⟩ := GlueIdx.directed x
    exact ⟨⟨p.i, p.O ⊓ q.O, inf_le_left.trans p.le⟩,
      homOfLE (show p.O ⊓ q.O ≤ p.O from inf_le_left),
      homOfLE (show p.O ⊓ q.O ≤ q.O from inf_le_right), y, hy⟩
  property_trans h := inferInstance

variable (X : ι → Scheme.{u}) (β : ∀ i, X i ⟶ P)
  (φ : ∀ i j, ((β i ≫ g) ⁻¹ᵁ U j).toScheme ⟶ X j)

/-- The piece of the glued scheme over the index `p = (i, O)`: the part of `X i` over `O`. -/
abbrev glueObj (p : GlueIdx U) : Scheme.{u} := ((β p.i ≫ g) ⁻¹ᵁ p.O).toScheme

variable {U X β}

/-- The transition `X_i|_{O_p} ⟶ X_j` for `p ≤ q` (through `φ_ij`). -/
def glueMapAux {p q : GlueIdx U} (h : p ≤ q) : glueObj g U X β p ⟶ X q.i :=
  (X p.i).homOfLE (U := (β p.i ≫ g) ⁻¹ᵁ p.O) (V := (β p.i ≫ g) ⁻¹ᵁ U q.i)
    ((β p.i ≫ g).preimage_mono ((show p.O ≤ q.O from h).trans q.le)) ≫ φ p.i q.i

variable (hφ : ∀ i j, φ i j ≫ β j = ((β i ≫ g) ⁻¹ᵁ U j).ι ≫ β i)

include hφ in
theorem glueMapAux_comp {p q : GlueIdx U} (h : p ≤ q) :
    glueMapAux g φ h ≫ β q.i = ((β p.i ≫ g) ⁻¹ᵁ p.O).ι ≫ β p.i := by
  rw [glueMapAux, Category.assoc, hφ, Scheme.homOfLE_ι_assoc]

include hφ in
theorem range_glueMapAux {p q : GlueIdx U} (h : p ≤ q) :
    Set.range (glueMapAux g φ h) ⊆ Set.range ((β q.i ≫ g) ⁻¹ᵁ q.O).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (β q.i ≫ g) (glueMapAux g φ h x) ∈ q.O
  have := congrArg (fun m ↦ (m ≫ g) x) (glueMapAux_comp g φ hφ h)
  simp only [Scheme.Hom.comp_apply] at this
  rw [Scheme.Hom.comp_apply, this]
  exact (show p.O ≤ q.O from h) x.2

/-- The transition maps of the glued pieces. -/
def glueMap {p q : GlueIdx U} (h : p ≤ q) : glueObj g U X β p ⟶ glueObj g U X β q :=
  IsOpenImmersion.lift _ (glueMapAux g φ h) (range_glueMapAux g φ hφ h)

@[reassoc (attr := simp)]
theorem glueMap_ι {p q : GlueIdx U} (h : p ≤ q) :
    glueMap g φ hφ h ≫ ((β q.i ≫ g) ⁻¹ᵁ q.O).ι = glueMapAux g φ h :=
  IsOpenImmersion.lift_fac _ _ _

variable (rigid : ∀ i j (O : (X i).Opens) (a b : O.toScheme ⟶ X j), a ≫ β j = O.ι ≫ β i →
  b ≫ β j = O.ι ≫ β i → a = b)

include rigid in
theorem glueMap_refl (p : GlueIdx U) : glueMap g φ hφ (le_refl p) = 𝟙 _ := by
  rw [← cancel_mono ((β p.i ≫ g) ⁻¹ᵁ p.O).ι, glueMap_ι, Category.id_comp]
  exact rigid _ _ _ _ _ (glueMapAux_comp g φ hφ _) rfl

include rigid in
theorem glueMap_trans {p q r : GlueIdx U} (h₁ : p ≤ q) (h₂ : q ≤ r) :
    glueMap g φ hφ (h₁.trans h₂) = glueMap g φ hφ h₁ ≫ glueMap g φ hφ h₂ := by
  rw [← cancel_mono ((β r.i ≫ g) ⁻¹ᵁ r.O).ι, glueMap_ι, Category.assoc, glueMap_ι]
  refine rigid _ _ _ _ _ (glueMapAux_comp g φ hφ _) ?_
  rw [Category.assoc, glueMapAux_comp g φ hφ, glueMap_ι_assoc, glueMapAux_comp g φ hφ]

/-- The glued pieces as a functor on the index preorder. -/
def glueFunctor : GlueIdx U ⥤ Scheme.{u} where
  obj p := glueObj g U X β p
  map h := glueMap g φ hφ h.le
  map_id p := glueMap_refl g φ hφ rigid p
  map_comp h₁ h₂ := glueMap_trans g φ hφ rigid h₁.le h₂.le

variable (hU : ⨆ i, U i = ⊤)

/-- The structure maps of the pieces to the members of the refined cover. -/
def glueNatTrans : glueFunctor g φ hφ rigid ⟶ (glueCover U hU).functorOfLocallyDirected where
  app p := (β p.i ≫ g) ∣_ p.O
  naturality {p q} h := by
    change glueMap g φ hφ h.le ≫ (β q.i ≫ g) ∣_ q.O = (β p.i ≫ g) ∣_ p.O ≫ T.homOfLE h.le
    rw [← cancel_mono q.O.ι, Category.assoc, morphismRestrict_ι, glueMap_ι_assoc,
      Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, ← Category.assoc,
      glueMapAux_comp g φ hφ, Category.assoc]

variable [∀ i j, IsOpenImmersion (φ i j)]
  (hφr : ∀ i j, Set.range (φ i j) = ((β j ≫ g) ⁻¹ᵁ U i : Set (X j)))

instance isOpenImmersion_glueMap {p q : GlueIdx U} (h : p ≤ q) :
    IsOpenImmersion (glueMap g φ hφ h) := by
  have : IsOpenImmersion (glueMap g φ hφ h ≫ ((β q.i ≫ g) ⁻¹ᵁ q.O).ι) := by
    rw [glueMap_ι, glueMapAux]
    infer_instance
  exact IsOpenImmersion.of_comp _ ((β q.i ≫ g) ⁻¹ᵁ q.O).ι

/-- A point lies in the range of `f` iff its image under an open immersion `j` lies in the
range of `f ≫ j`. -/
theorem mem_range_iff_mem_range_comp {A B C : Scheme.{u}} (f : A ⟶ B) (j : B ⟶ C)
    [IsOpenImmersion j] (y : B) : y ∈ Set.range f ↔ j y ∈ Set.range (f ≫ j) := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, j.isOpenEmbedding.injective (by rw [← hw, Scheme.Hom.comp_apply])⟩

omit [∀ i j, IsOpenImmersion (φ i j)] in
include hφ hφr in
/-- The image of `X_i|_{O_p}` in `X_j` under `φ_ij` is `X_j|_{O_p}`. -/
theorem mem_range_glueMapAux_iff {p q : GlueIdx U} (h : p ≤ q) (z : X q.i) :
    z ∈ Set.range (glueMapAux g φ h) ↔ (β q.i ≫ g) z ∈ p.O := by
  constructor
  · rintro ⟨w, rfl⟩
    have := congrArg (fun m ↦ (m ≫ g) w) (glueMapAux_comp g φ hφ h)
    simp only [Scheme.Hom.comp_apply] at this
    rw [Scheme.Hom.comp_apply, this]
    exact opens_ι_mem w
  · intro hz
    have hzU : z ∈ ((β q.i ≫ g) ⁻¹ᵁ U p.i : Set (X q.i)) := p.le hz
    rw [← hφr] at hzU
    obtain ⟨v, rfl⟩ := hzU
    have hv : ((β p.i ≫ g) ⁻¹ᵁ U q.i).ι v ∈ ((β p.i ≫ g) ⁻¹ᵁ p.O : Set (X p.i)) := by
      have := congrArg (fun m ↦ (m ≫ g) v) (hφ p.i q.i)
      simp only [Scheme.Hom.comp_apply] at this
      change (β p.i ≫ g) (((β p.i ≫ g) ⁻¹ᵁ U q.i).ι v) ∈ p.O
      rw [Scheme.Hom.comp_apply, ← this, ← Scheme.Hom.comp_apply]
      exact hz
    rw [← Scheme.Opens.range_ι] at hv
    obtain ⟨w, hw⟩ := hv
    refine ⟨w, ?_⟩
    rw [glueMapAux, Scheme.Hom.comp_apply]
    congr 1
    apply ((β p.i ≫ g) ⁻¹ᵁ U q.i).ι.isOpenEmbedding.injective
    rw [← hw, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]

include hφr in
theorem glueNatTrans_equifibered : (glueNatTrans g φ hφ rigid hU).Equifibered := by
  intro p q h
  refine (IsOpenImmersion.isPullback ((β p.i ≫ g) ∣_ p.O) (glueMap g φ hφ h.le)
    (T.homOfLE h.le) ((β q.i ≫ g) ∣_ q.O) ((glueNatTrans g φ hφ rigid hU).naturality h) ?_).flip
  ext y
  change ((β q.i ≫ g) ∣_ q.O) y ∈ Set.range (T.homOfLE h.le) ↔
    y ∈ Set.range (glueMap g φ hφ h.le)
  rw [mem_range_iff_mem_range_comp _ q.O.ι, Scheme.homOfLE_ι, Scheme.Opens.range_ι,
    mem_range_iff_mem_range_comp _ ((β q.i ≫ g) ⁻¹ᵁ q.O).ι, glueMap_ι,
    mem_range_glueMapAux_iff g φ hφ hφr h.le, ← Scheme.Hom.comp_apply, morphismRestrict_ι,
    Scheme.Hom.comp_apply]
  exact Iff.rfl

/-- The relative gluing datum of the pieces (Stacks 01LH). -/
def glueRelData : (glueCover U hU).RelativeGluingData where
  functor := glueFunctor g φ hφ rigid
  natTrans := glueNatTrans g φ hφ rigid hU
  equifibered := glueNatTrans_equifibered g φ hφ rigid hU hφr

/-- The cocone of the pieces over `P`. -/
def glueCoconeP : Cocone (glueFunctor g φ hφ rigid) where
  pt := P
  ι :=
    { app := fun p ↦ ((β p.i ≫ g) ⁻¹ᵁ p.O).ι ≫ β p.i
      naturality := fun p q h ↦ by
        change glueMap g φ hφ h.le ≫ ((β q.i ≫ g) ⁻¹ᵁ q.O).ι ≫ β q.i =
          (((β p.i ≫ g) ⁻¹ᵁ p.O).ι ≫ β p.i) ≫ 𝟙 P
        rw [glueMap_ι_assoc, glueMapAux_comp g φ hφ, Category.comp_id] }

include hφ rigid hU hφr in
/-- **Gluing of schemes over `P` along an open cover of the base** (relative gluing, Stacks 01LH,
used in the proof of Temkin's Thm 1.5, T:3394–3397). Let `g : P ⟶ T`, `U` an open cover of `T`,
and `β i : X i ⟶ P` with `X i` lying over `U i`. Let `φ i j : X_i|_{U_j} ⟶ X_j` be open
immersions over `P` with image `X_j|_{U_i}`, and assume morphisms from opens of the `X_i` to the
`X_j` over `P` are unique. Then the `X i` glue: there are `β : X ⟶ P` and open immersions
`j i : X i ⟶ X` over `P` with image the preimage of `U i`. -/
theorem exists_glue (hβ : ∀ i, (β i ≫ g) ⁻¹ᵁ U i = ⊤) :
    ∃ (Xg : Scheme.{u}) (βg : Xg ⟶ P) (j : ∀ i, X i ⟶ Xg),
      (∀ i, IsOpenImmersion (j i)) ∧ (∀ i, j i ≫ βg = β i) ∧
      (∀ i, Set.range (j i) = ((βg ≫ g) ⁻¹ᵁ U i : Set Xg)) := by
  let d := glueRelData g φ hφ rigid hU hφr
  have : Small.{u} (glueCover U hU).I₀ := small_self _
  have : Quiver.IsThin (glueCover U hU).I₀ := inferInstanceAs (Quiver.IsThin (GlueIdx U))
  have : ((glueCover U hU).functorOfLocallyDirected ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.instIsLocallyDirectedI₀CompFunctorOfLocallyDirectedForget (glueCover U hU)
  have : (d.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective d.natTrans d.equifibered
      (fun hij ↦ (d.functor.map hij).isOpenEmbedding.injective)
  let c : Cocone d.functor := glueCoconeP g φ hφ rigid
  let βg : d.glued ⟶ P := colimit.desc d.functor c
  have hβg : ∀ p, colimit.ι d.functor p ≫ βg = c.ι.app p := fun p ↦ colimit.ι_desc c p
  have hbase : βg ≫ g = d.toBase := by
    refine colimit.hom_ext fun p ↦ ?_
    rw [← Category.assoc, hβg p, Scheme.Cover.RelativeGluingData.ι_toBase]
    change (((β p.i ≫ g) ⁻¹ᵁ p.O).ι ≫ β p.i) ≫ g = ((β p.i ≫ g) ∣_ p.O) ≫ p.O.ι
    rw [morphismRestrict_ι, Category.assoc]
  let p₀ : ι → GlueIdx U := fun i ↦ ⟨i, U i, le_rfl⟩
  have hVι : ∀ i, IsIso ((β i ≫ g) ⁻¹ᵁ U i).ι := by
    intro i
    rw [hβ i]
    exact inferInstanceAs (IsIso (X i).topIso.hom)
  let e : ∀ i, X i ⟶ d.functor.obj (p₀ i) := fun i ↦
    haveI := hVι i
    (inv ((β i ≫ g) ⁻¹ᵁ U i).ι : X i ⟶ ((β i ≫ g) ⁻¹ᵁ U i).toScheme)
  have he : ∀ i, IsIso (e i) := fun i ↦ by
    have := hVι i
    change IsIso (inv ((β i ≫ g) ⁻¹ᵁ U i).ι)
    infer_instance
  let j : ∀ i, X i ⟶ d.glued := fun i ↦ e i ≫ colimit.ι d.functor (p₀ i)
  refine ⟨d.glued, βg, j, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · have := he i
    change IsOpenImmersion (e i ≫ colimit.ι d.functor (p₀ i))
    infer_instance
  · change (e i ≫ colimit.ι d.functor (p₀ i)) ≫ βg = β i
    rw [Category.assoc, hβg (p₀ i)]
    have := hVι i
    change inv ((β i ≫ g) ⁻¹ᵁ U i).ι ≫ ((β i ≫ g) ⁻¹ᵁ U i).ι ≫ β i = β i
    exact IsIso.inv_hom_id_assoc _ _
  · have := he i
    change Set.range (e i ≫ colimit.ι d.functor (p₀ i)) = _
    rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso, hbase,
      ← Scheme.Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι d (p₀ i)]
    change ((d.toBase ⁻¹ᵁ (U i).ι.opensRange : d.glued.Opens) : Set ↥d.glued) = _
    rw [Scheme.Opens.opensRange_ι]

end Glue

section GlueHom

/-- **Gluing of morphisms with rigidity**: morphisms `m k : V_k ⟶ Y` over `P` on an open cover
`V` of `A` glue to a morphism `A ⟶ Y` over `P`, provided morphisms from open subschemes of `A` to
`Y` over `P` are unique (compatibility on the overlaps is then automatic). -/
theorem exists_glueHom {A Y P : Scheme.{u}} (βA : A ⟶ P) (βY : Y ⟶ P) {κ : Type u}
    (V : κ → A.Opens) (hV : ⨆ k, V k = ⊤) (m : ∀ k, (V k).toScheme ⟶ Y)
    (hm : ∀ k, m k ≫ βY = (V k).ι ≫ βA)
    (rigid : ∀ (W : Scheme.{u}) (e : W ⟶ A) [IsOpenImmersion e] (a b : W ⟶ Y),
      a ≫ βY = e ≫ βA → b ≫ βY = e ≫ βA → a = b) :
    ∃ f : A ⟶ Y, f ≫ βY = βA ∧ ∀ k, (V k).ι ≫ f = m k := by
  let 𝒱 : A.OpenCover.{u} :=
    { I₀ := κ
      X k := (V k).toScheme
      f k := (V k).ι
      mem₀ := (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) κ (fun k ↦ (V k).toScheme)
        (fun k ↦ (V k).ι) (fun x ↦ by
          have hx : x ∈ ⨆ k, V k := by rw [hV]; trivial
          obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hx
          exact ⟨k, ⟨x, hk⟩, rfl⟩)).mem₀ }
  have hcompat : ∀ x y, pullback.fst (𝒱.f x) (𝒱.f y) ≫ m x = pullback.snd _ _ ≫ m y := by
    intro x y
    refine rigid _ (pullback.fst (𝒱.f x) (𝒱.f y) ≫ (V x).ι) _ _ ?_ ?_
    · change pullback.fst (V x).ι (V y).ι ≫ m x ≫ βY = (pullback.fst (V x).ι (V y).ι ≫ (V x).ι) ≫ βA
      rw [hm, Category.assoc]
    · change pullback.snd (V x).ι (V y).ι ≫ m y ≫ βY = (pullback.fst (V x).ι (V y).ι ≫ (V x).ι) ≫ βA
      rw [hm, Category.assoc, pullback.condition_assoc]
  refine ⟨𝒱.glueMorphisms m hcompat, ?_, fun k ↦ 𝒱.ι_glueMorphisms m hcompat k⟩
  refine 𝒱.hom_ext _ _ fun k ↦ ?_
  rw [Scheme.Cover.ι_glueMorphisms_assoc]
  exact hm k

end GlueHom


end DeJongAlterations.StableModification.Global
