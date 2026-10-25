import DeJongAlterations.StableModification.Limits.System
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Etale.Basic
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Descent along the approximating system

Let `D : I ⥤ Scheme` be a cofiltered diagram of schemes with affine transition morphisms,
indexed by a thin category (a directed preorder, so that any two parallel arrows agree), and let
`c` be a limit cone with apex `lim D`. This file proves the approximation statements of
EGA IV₃ §8 that Temkin, *Stable modification of relative curves* (arXiv v3), §3.1
(`approxsec`, `T:2262–2298`), collects under the word "approximation", in the form used by our
replacement of Noetherian approximation: the approximating system is the system of finitely
generated subalgebras of a valuation ring (`Limits.System`, Temkin Lemma 3.2.2 `approxlem`,
`T:2342`), so no approximation over `ℤ` is needed.

A *model* at level `i` of a scheme `X → lim D` (`Limits.Model`) is a scheme `Y → D i` with a
cartesian square `X = Y ×_{D i} lim D`; it is *of finite presentation* (`Limits.Model.IsFP`) if
`Y → D i` is locally of finite presentation, quasi-compact and quasi-separated.

## Main results

* `Limits.exists_etale_tensorEquiv`: an étale algebra over a directed union `R = ⋃ F i` of
  subalgebras is `R ⊗_{F i} B` for an étale `F i`-algebra `B`, with finitely many given elements
  in the image of `B` (EGA IV 17.7.8 in the form used for Temkin Prop. 4.3.3, `T:3049–3082`).
* `Limits.isLimitBaseChangeCone`: base change `X ×_{D i} D j` along the system has limit
  `X ×_{D i} lim D`.
* `Limits.exists_hom_of_isPullback`, `Limits.exists_eq_of_isPullback`: descent of morphisms and
  of equalities of morphisms (EGA IV 8.8.2 (i)), from Mathlib's `AffineTransitionLimit`.
* `Limits.exists_isPullback_of_isAffine`: descent of affine schemes of finite presentation, for a
  system of affine schemes.
* `Limits.exists_iso_of_iso`, `Limits.exists_isIso_baseChangeHom`: descent of isomorphisms
  (EGA IV 8.8.2.5, 8.10.5 (iv)).
* `Limits.exists_model_of_sup`: gluing two models along a pushout of open immersions.
* `Limits.exists_model`: every scheme of finite presentation over `lim D` (for `D` a system of
  affine schemes) has a model of finite presentation (EGA IV 8.8.2 (ii)), by induction on the
  number of affine opens of a cover.
* `Limits.exists_isClosedImmersion`: descent of closed immersions (EGA IV 8.10.5 (iv)), and
  `Limits.exists_closedImmersion_model`: descent of closed subschemes.
* `Limits.exists_isSeparated`: descent of separatedness (EGA IV 8.10.5 (v)).
* `Limits.exists_model_fgSubalgebra`: the specialization to the system of finitely generated
  subalgebras of a subalgebra `R ⊆ L`, e.g. a valuation ring.

## Not treated

Descent of flatness (lane FD), and descent of properness, smoothness and étaleness of morphisms
of schemes, are not proved here.

## Implementation notes

The index category is assumed thin, which makes the base change systems indexed by `Over i`
thin as well and removes all coherence conditions on the transition maps. The option
`backward.isDefEq.respectTransparency false` is needed for the `pullback.map` simp lemmas.
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct

universe u

namespace DeJongAlterations.StableModification.Limits

set_option backward.isDefEq.respectTransparency false

/-! ### Directed unions: finitely generated subalgebras and étale algebras -/

section Algebra

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  (F : ι →o Subalgebra A R) (hF : ∀ x : R, ∃ i, x ∈ F i)

include hF in
/-- A finite subset of a directed union of subalgebras lies in one member, above a given index. -/
lemma exists_ge_finset_subset (s : Finset R) (i₀ : ι) :
    ∃ i, i₀ ≤ i ∧ (s : Set R) ⊆ F i := by
  classical
  choose j hj using hF
  obtain ⟨i, hi⟩ := Finset.exists_le (insert i₀ (s.image j))
  exact ⟨i, hi _ (Finset.mem_insert_self _ _), fun x hx =>
    F.monotone (hi _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem j hx))) (hj x)⟩

include hF in
/-- A finitely generated subalgebra of a directed union of subalgebras lies in one member. -/
lemma exists_le_of_fg {A₀ : Subalgebra A R} (h : A₀.FG) (i₀ : ι) :
    ∃ i, i₀ ≤ i ∧ A₀ ≤ F i := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨i, hi, hs⟩ := exists_ge_finset_subset F hF s i₀
  exact ⟨i, hi, Algebra.adjoin_le hs⟩

variable {O : Type u} [CommRing O] [Algebra R O] [Algebra.Etale R O]

include hF in
/-- **Descent of étale algebras along a directed union** (EGA IV 17.7.8, Stacks 00U2 (8)).
Let `R` be the directed union of the subalgebras `F i` and let `O` be an étale `R`-algebra. Then
for some `i` there is an étale `F i`-algebra `B` with `O ≅ R ⊗_{F i} B`, and any given finitely
many elements of `O` lie in the image of `B`. -/
theorem exists_etale_tensorEquiv (s : Finset O) :
    ∃ (i : ι) (B : Type u) (_ : CommRing B) (_ : Algebra (F i) B) (e : O ≃ₐ[R] R ⊗[F i] B),
      Algebra.Etale (F i) B ∧
        ∀ o ∈ s, e o ∈ Set.range (Algebra.TensorProduct.includeRight : B →ₐ[F i] R ⊗[F i] B) := by
  classical
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, ⟨e₀⟩⟩ := Algebra.Etale.exists_subalgebra_fg A R O
  obtain ⟨i₀, -, hi₀⟩ := exists_le_of_fg F hF hA₀ (Classical.arbitrary ι)
  choose T hT using fun o : O => TensorProduct.exists_finset (e₀ o)
  obtain ⟨i, hi, hiT⟩ := exists_ge_finset_subset F hF
    (s.biUnion fun o => (T o).image Prod.fst) i₀
  have hA₀i : A₀ ≤ F i := hi₀.trans (F.monotone hi)
  let : Algebra A₀ (F i) := (Subalgebra.inclusion hA₀i).toRingHom.toAlgebra
  have : IsScalarTower A₀ (F i) R := IsScalarTower.of_algebraMap_eq' rfl
  let c := Algebra.TensorProduct.cancelBaseChange A₀ (F i) R R B₀
  refine ⟨i, F i ⊗[A₀] B₀, inferInstance, inferInstance, e₀.trans c.symm, inferInstance, ?_⟩
  intro o ho
  have hmem : ∀ p ∈ T o, p.1 ∈ F i := fun p hp =>
    hiT (Finset.mem_biUnion.2 ⟨o, ho, Finset.mem_image_of_mem _ hp⟩)
  refine ⟨∑ p ∈ (T o).attach, (⟨p.1.1, hmem _ p.2⟩ : F i) ⊗ₜ p.1.2, ?_⟩
  apply c.injective
  rw [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, hT o,
    Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_sum, map_sum,
    ← Finset.sum_attach (T o) (fun p => p.1 ⊗ₜ[A₀] p.2)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
  rfl

end Algebra

/-! ### Base change systems -/

section BaseChange

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
variable {i : I} {X : Scheme.{u}} (f : X ⟶ D.obj i)

/-- The base change system `j ↦ X ×_{D i} D j` of a morphism `f : X ⟶ D i`, indexed by the
objects `j → i` over `i`. -/
@[simps]
noncomputable def baseChangeDiagram : Over i ⥤ Scheme.{u} where
  obj j := pullback f (D.map j.hom)
  map {j k} g := pullback.map f (D.map j.hom) f (D.map k.hom) (𝟙 _) (D.map g.left) (𝟙 _)
    (by simp) (by rw [Category.comp_id, ← D.map_comp, Over.w g])
  map_id j := by
    apply pullback.hom_ext <;> simp
  map_comp {j k l} g h := by
    apply pullback.hom_ext <;> simp

@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_fst {j k : Over i} (g : j ⟶ k) :
    (baseChangeDiagram D f).map g ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp

@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_snd {j k : Over i} (g : j ⟶ k) :
    (baseChangeDiagram D f).map g ≫ pullback.snd _ _ = pullback.snd _ _ ≫ D.map g.left := by
  simp

/-- The structure maps `X ×_{D i} D j → D j` of the base change system. -/
@[simps]
noncomputable def baseChangeDiagramπ : baseChangeDiagram D f ⟶ Over.forget i ⋙ D where
  app j := pullback.snd _ _
  naturality {j k} g := by simp

/-- The structure maps `X ×_{D i} D j → D i` of the base change system to the fixed base `D i`. -/
@[simps]
noncomputable def baseChangeDiagramToBase :
    baseChangeDiagram D f ⟶ (Functor.const (Over i)).obj (D.obj i) where
  app j := pullback.fst _ _ ≫ f
  naturality {j k} g := by simp

variable {f}

/-- The cone over the base change system given by a pullback square `X' = X ×_{D i} lim D`. -/
@[simps]
noncomputable def baseChangeCone {X' : Scheme.{u}} {g : X' ⟶ X} {f' : X' ⟶ c.pt}
    (h : IsPullback g f' f (c.π.app i)) : Cone (baseChangeDiagram D f) where
  pt := X'
  π.app j := pullback.lift g (f' ≫ c.π.app j.left) (by
    rw [h.w, Category.assoc, ← c.w j.hom])
  π.naturality {j k} g := by
    apply pullback.hom_ext <;> simp

variable (f) in
lemma isPullback_baseChangeDiagram_map {j k : Over i} (g : j ⟶ k) :
    IsPullback ((baseChangeDiagram D f).map g) (pullback.snd _ _) (pullback.snd _ _)
      (D.map g.left) := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback f (D.map k.hom))
  have e1 : (baseChangeDiagram D f).map g ≫ pullback.fst f (D.map k.hom) =
      pullback.fst f (D.map j.hom) := by simp
  have e2 : D.map g.left ≫ D.map k.hom = D.map j.hom := by rw [← D.map_comp, Over.w g]
  rw [e1, e2]
  exact IsPullback.of_hasPullback _ _

lemma isPullback_baseChangeCone_π {X' : Scheme.{u}} {g : X' ⟶ X} {f' : X' ⟶ c.pt}
    (h : IsPullback g f' f (c.π.app i)) (j : Over i) :
    IsPullback ((baseChangeCone D c h).π.app j) f' (pullback.snd _ _) (c.π.app j.left) := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback f (D.map j.hom))
  have e1 : (baseChangeCone D c h).π.app j ≫ pullback.fst f (D.map j.hom) = g := by simp
  have e2 : c.π.app j.left ≫ D.map j.hom = c.π.app i := c.w j.hom
  rw [e1, e2]
  exact h

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

/-- **Base change commutes with cofiltered limits.** For a pullback square
`X' = X ×_{D i} lim D`, the scheme `X'` is the limit of the base change system
`j ↦ X ×_{D i} D j`. -/
noncomputable def isLimitBaseChangeCone [IsCofiltered I] (hc : IsLimit c) {X' : Scheme.{u}}
    {g : X' ⟶ X} {f' : X' ⟶ c.pt} (h : IsPullback g f' f (c.π.app i)) :
    IsLimit (baseChangeCone D c h) :=
  isLimitOfIsPullbackOfIsConnected (baseChangeDiagramπ D f) (baseChangeCone D c h)
    (c.whisker (Over.forget i)) { hom := f' }
    (fun j => isPullback_baseChangeCone_π D c h j)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

variable (f)

instance [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)] {j k : Over i} (g : j ⟶ k) :
    IsAffineHom ((baseChangeDiagram D f).map g) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_baseChangeDiagram_map D f g).flip inferInstance

instance [∀ j, CompactSpace (D.obj j)] [QuasiCompact f] (j : Over i) :
    CompactSpace ((baseChangeDiagram D f).obj j) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (D.map j.hom))

instance [∀ j, QuasiSeparatedSpace (D.obj j)] [QuasiSeparated f] (j : Over i) :
    QuasiSeparatedSpace ((baseChangeDiagram D f).obj j) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (D.map j.hom))

end BaseChange

/-! ### Descent of morphisms and of equalities of morphisms -/

section Morphisms

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  (hc : IsLimit c) [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
  [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]

include hc

/-- **Descent of morphisms** (EGA IV 8.8.2 (i), existence part). Let `X, Y` be schemes over `D i`
with `X` quasi-compact and quasi-separated and `Y` locally of finite presentation, and let
`X' = X ×_{D i} lim D`. Every `D i`-morphism `X' → Y` comes from a `D i`-morphism
`X ×_{D i} D j → Y` for some `j → i`. -/
theorem exists_hom_of_isPullback {i : I} {X Y : Scheme.{u}} (fX : X ⟶ D.obj i)
    (fY : Y ⟶ D.obj i) [QuasiCompact fX] [QuasiSeparated fX] [LocallyOfFinitePresentation fY]
    {X' : Scheme.{u}} {gX : X' ⟶ X} {fX' : X' ⟶ c.pt} (hX : IsPullback gX fX' fX (c.π.app i))
    (a : X' ⟶ Y) (ha : a ≫ fY = gX ≫ fX) :
    ∃ (j : Over i) (b : (baseChangeDiagram D fX).obj j ⟶ Y),
      b ≫ fY = pullback.fst _ _ ≫ fX ∧ (baseChangeCone D c hX).π.app j ≫ b = a := by
  obtain ⟨j, b, hb, hb'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (baseChangeDiagram D fX) (baseChangeDiagramToBase D fX) fY (baseChangeCone D c hX)
    (isLimitBaseChangeCone D c hc hX) a (by ext j; simp [ha])
  exact ⟨j, b, by simpa using hb', hb⟩

omit [∀ j, QuasiSeparatedSpace (D.obj j)] in
/-- **Descent of equalities of morphisms** (EGA IV 8.8.2 (i), injectivity part). Two
`D i`-morphisms `X ×_{D i} D j → Y` to a scheme `Y` locally of finite type over `D i` which agree
after base change to `lim D` agree after base change to some `D k`, `k → j`. -/
theorem exists_eq_of_isPullback {i : I} {X Y : Scheme.{u}} (fX : X ⟶ D.obj i)
    (fY : Y ⟶ D.obj i) [QuasiCompact fX] [LocallyOfFiniteType fY]
    {X' : Scheme.{u}} {gX : X' ⟶ X} {fX' : X' ⟶ c.pt} (hX : IsPullback gX fX' fX (c.π.app i))
    {j : Over i} (a b : (baseChangeDiagram D fX).obj j ⟶ Y)
    (ha : a ≫ fY = pullback.fst _ _ ≫ fX) (hb : b ≫ fY = pullback.fst _ _ ≫ fX)
    (hab : (baseChangeCone D c hX).π.app j ≫ a = (baseChangeCone D c hX).π.app j ≫ b) :
    ∃ (k : Over i) (g : k ⟶ j),
      (baseChangeDiagram D fX).map g ≫ a = (baseChangeDiagram D fX).map g ≫ b := by
  obtain ⟨k, g, h⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (baseChangeDiagram D fX) (baseChangeDiagramToBase D fX) fY (baseChangeCone D c hX)
    (isLimitBaseChangeCone D c hc hX) a b (by simpa using ha.symm) (by simpa using hb.symm) hab
  exact ⟨k, g, h⟩

end Morphisms

/-! ### Descent of affine schemes of finite presentation -/

section Affine

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  (hc : IsLimit c) [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
  [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]

include hc

/-- Finitely many global sections of `lim D` come from global sections of a single `D k`. -/
lemma exists_appTop_eq (s : Finset Γ(c.pt, ⊤)) :
    ∃ k : I, ∀ x ∈ s, ∃ y : Γ(D.obj k, ⊤), (c.π.app k).appTop y = x := by
  classical
  obtain ⟨hΓ⟩ := nonempty_isColimit_Γ_mapCocone D c hc
  have hΓ' := isColimitOfPreserves (forget CommRingCat) hΓ
  choose j y hy using fun x : Γ(c.pt, ⊤) => Types.jointly_surjective_of_isColimit hΓ' x
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (s.image fun x => (j x).unop)
  refine ⟨k, fun x hx => ?_⟩
  obtain ⟨g⟩ := hk (Finset.mem_image_of_mem _ hx)
  refine ⟨(D.map g).appTop (y x), Eq.trans ?_ (hy x)⟩
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, c.w g]
  rfl

variable [∀ j, IsAffine (D.obj j)]

/-- **Descent of affine schemes of finite presentation** (EGA IV 8.8.2 (ii), affine case). An
affine scheme `X` locally of finite presentation over `lim D` (a cofiltered limit of affine
schemes with affine transition maps) is the base change of an affine scheme of finite
presentation over some `D i`. -/
theorem exists_isPullback_of_isAffine {X : Scheme.{u}} [IsAffine X] (f : X ⟶ c.pt)
    [LocallyOfFinitePresentation f] :
    ∃ (i : I) (Y : Scheme.{u}) (fY : Y ⟶ D.obj i) (g : X ⟶ Y),
      IsAffine Y ∧ LocallyOfFinitePresentation fY ∧ IsPullback g f fY (c.π.app i) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let R := Γ(c.pt, ⊤)
  let C := Γ(X, ⊤)
  let : Algebra R C := f.appTop.hom.toAlgebra
  have : Algebra.FinitePresentation R C := RingHom.finitePresentation_algebraMap.1
    ((HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1 ‹_›)
  let P := Algebra.Presentation.ofFinitePresentation R C
  obtain ⟨k, hk⟩ := exists_appTop_eq D c hc P.finite_coeffs.toFinset
  let R₀ := Γ(D.obj k, ⊤)
  let : Algebra R₀ R := (c.π.app k).appTop.hom.toAlgebra
  let : Algebra R₀ C := ((algebraMap R C).comp (algebraMap R₀ R)).toAlgebra
  have : IsScalarTower R₀ R C := IsScalarTower.of_algebraMap_eq' rfl
  have : P.HasCoeffs R₀ := ⟨fun x hx => hk x (by simpa using hx)⟩
  let M := P.ModelOfHasCoeffs R₀
  let e := P.tensorModelOfHasCoeffsEquiv R₀
  let inl : CommRingCat.of R ⟶ CommRingCat.of (R ⊗[R₀] M) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let inr : CommRingCat.of M ⟶ CommRingCat.of (R ⊗[R₀] M) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let eS : Spec (CommRingCat.of C) ≅ Spec (CommRingCat.of (R ⊗[R₀] M)) :=
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e.toRingEquiv).op
  let g : X ⟶ Spec (CommRingCat.of M) := X.isoSpec.hom ≫ eS.hom ≫ Spec.map inr
  refine ⟨k, Spec (CommRingCat.of M),
    Spec.map (CommRingCat.ofHom (algebraMap R₀ M)) ≫ (D.obj k).isoSpec.inv, g, inferInstance,
    ?_, ?_⟩
  · have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R₀ M))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
      exact RingHom.finitePresentation_algebraMap.2 inferInstance
    infer_instance
  · have H := (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R₀ R M)).flip
    have hinl : eS.hom ≫ Spec.map inl = Spec.map f.appTop := by
      change Spec.map (CommRingCat.ofHom (e : R ⊗[R₀] M →+* C)) ≫ Spec.map inl = _
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact e.commutes x
    have hR : CommRingCat.ofHom (algebraMap R₀ R) = (c.π.app k).appTop := rfl
    refine H.of_iso (eS.symm ≪≫ X.isoSpec.symm) (Iso.refl _) c.pt.isoSpec.symm
      (D.obj k).isoSpec.symm ?_ ?_ ?_ ?_
    · simp [g, inr]
    · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rw [Iso.eq_inv_comp, Iso.eq_inv_comp, ← cancel_mono c.pt.isoSpec.hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      erw [hinl, Scheme.isoSpec_hom_naturality]
    · simp
    · simp only [Iso.symm_hom]
      rw [Iso.eq_inv_comp, hR, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]

end Affine

/-! ### Models over the levels of the system -/

section Model

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- A *model* at level `i` of a scheme `X → lim D`: a scheme `Y → D i` together with a pullback
square `X = Y ×_{D i} lim D`. -/
structure Model {X : Scheme.{u}} (f : X ⟶ c.pt) (i : I) where
  /-- The scheme at level `i`. -/
  Y : Scheme.{u}
  /-- Its structure morphism to `D i`. -/
  fY : Y ⟶ D.obj i
  /-- The projection from `X`. -/
  g : X ⟶ Y
  isPullback : IsPullback g f fY (c.π.app i)

variable {D c} {X : Scheme.{u}} {f : X ⟶ c.pt} {i : I}

/-- The base change of a model at level `i` to a level `k → i`. -/
@[simps]
noncomputable def Model.baseChange (m : Model D c f i) {k : I} (h : k ⟶ i) : Model D c f k where
  Y := pullback m.fY (D.map h)
  fY := pullback.snd _ _
  g := (baseChangeCone D c m.isPullback).π.app (Over.mk h)
  isPullback := isPullback_baseChangeCone_π D c m.isPullback (Over.mk h)

/-- The restriction of a model to an open of the level scheme: the preimage `g⁻¹ O ⊆ X` is
modelled by the open subscheme `O`. -/
@[simps]
noncomputable def Model.restrict (m : Model D c f i) (O : m.Y.Opens) :
    Model D c ((m.g ⁻¹ᵁ O).ι ≫ f) i where
  Y := O
  fY := O.ι ≫ m.fY
  g := m.g ∣_ O
  isPullback := (isPullback_morphismRestrict m.g O).paste_vert m.isPullback

lemma Model.isPullback_baseChange_baseChange (m : Model D c f i) {j l : I} (g₁ : j ⟶ i)
    (g₂ : l ⟶ j) :
    IsPullback (pullback.fst _ _ ≫ pullback.fst _ _) ((m.baseChange g₁).baseChange g₂).fY m.fY
      (D.map (g₂ ≫ g₁)) := by
  rw [D.map_comp]
  exact (IsPullback.of_hasPullback (pullback.snd m.fY (D.map g₁)) (D.map g₂)).paste_horiz
    (IsPullback.of_hasPullback m.fY (D.map g₁))

/-- An iterated base change of a model is isomorphic to its base change along the composite. -/
noncomputable def Model.baseChangeCompIso (m : Model D c f i) {j l : I} (g₁ : j ⟶ i)
    (g₂ : l ⟶ j) : ((m.baseChange g₁).baseChange g₂).Y ≅ (m.baseChange (g₂ ≫ g₁)).Y :=
  (m.isPullback_baseChange_baseChange g₁ g₂).isoIsPullback _ _
    (IsPullback.of_hasPullback m.fY (D.map (g₂ ≫ g₁)))

@[reassoc (attr := simp)]
lemma Model.baseChangeCompIso_hom_fY (m : Model D c f i) {j l : I} (g₁ : j ⟶ i) (g₂ : l ⟶ j) :
    (m.baseChangeCompIso g₁ g₂).hom ≫ (m.baseChange (g₂ ≫ g₁)).fY =
      ((m.baseChange g₁).baseChange g₂).fY :=
  (m.isPullback_baseChange_baseChange g₁ g₂).isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback m.fY (D.map (g₂ ≫ g₁)))

@[reassoc (attr := simp)]
lemma Model.g_baseChangeCompIso_hom (m : Model D c f i) {j l : I} (g₁ : j ⟶ i) (g₂ : l ⟶ j) :
    ((m.baseChange g₁).baseChange g₂).g ≫ (m.baseChangeCompIso g₁ g₂).hom =
      (m.baseChange (g₂ ≫ g₁)).g := by
  apply pullback.hom_ext
  · rw [Category.assoc, Model.baseChangeCompIso, IsPullback.isoIsPullback_hom_fst]
    simp [Model.baseChange]
  · rw [Category.assoc]
    change _ ≫ (m.baseChangeCompIso g₁ g₂).hom ≫ (m.baseChange (g₂ ≫ g₁)).fY = _
    rw [Model.baseChangeCompIso_hom_fY]
    simp

end Model

/-! ### Colimits of open covers -/

section OpenCoverColimit

variable {J : Type*} [Category J] (F : J ⥤ Scheme.{u})
  [∀ {i j : J} (f : i ⟶ j), IsOpenImmersion (F.map f)] (s : Cocone F)
  [∀ j, IsOpenImmersion (s.ι.app j)]

/-- **A scheme covered by a locally directed family of opens is their colimit.** Let `s` be a
cocone of open immersions over a diagram of open immersions, whose images cover `s.pt` and such
that every point in the images of `j` and `j'` lies in the image of some `k` mapping to both.
Then `s` is a colimit cocone. -/
noncomputable def isColimitOfOpenCover
    (hcov : ∀ x : s.pt, ∃ j, x ∈ Set.range (s.ι.app j))
    (hdir : ∀ (j j' : J) (x : s.pt), x ∈ Set.range (s.ι.app j) → x ∈ Set.range (s.ι.app j') →
      ∃ (k : J) (_ : k ⟶ j) (_ : k ⟶ j'), x ∈ Set.range (s.ι.app k)) :
    IsColimit s := by
  let 𝒰 : s.pt.OpenCover :=
    { I₀ := J
      X := F.obj
      f := s.ι.app
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hcov, inferInstance⟩ }
  let : Category 𝒰.I₀ := inferInstanceAs (Category J)
  let : Scheme.Cover.LocallyDirected 𝒰 :=
    { trans := fun f => F.map f
      trans_id := fun j => F.map_id j
      trans_comp := fun f g => F.map_comp f g
      w := fun f => s.w f
      directed := by
        intro j j' x
        obtain ⟨k, fk, fk', y, hy⟩ := hdir j j' ((pullback.fst (s.ι.app j) (s.ι.app j') ≫
          s.ι.app j) x) ⟨_, rfl⟩ ⟨(pullback.snd (s.ι.app j) (s.ι.app j')) x, by
            rw [← Scheme.Hom.comp_apply, ← pullback.condition]; rfl⟩
        refine ⟨k, fk, fk', y, ?_⟩
        apply (pullback.fst (s.ι.app j) (s.ι.app j') ≫ s.ι.app j).isOpenEmbedding.injective
        rw [← hy, ← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
        change (F.map fk ≫ s.ι.app j) y = _
        rw [s.w]
        rfl
      property_trans := fun f => inferInstanceAs (IsOpenImmersion (F.map f)) }
  exact Scheme.OpenCover.isColimitCoconeOfLocallyDirected 𝒰

/-- **Pushouts along open immersions.** A commutative square of open immersions
`W → X₁, W → X₂, X₁ → Z, X₂ → Z` whose images cover `Z` and such that the images of `X₁` and
`X₂` meet in the image of `W` is a pushout square. -/
lemma isPushout_of_isOpenImmersion {W X₁ X₂ Z : Scheme.{u}} (a₁ : W ⟶ X₁) (a₂ : W ⟶ X₂)
    (b₁ : X₁ ⟶ Z) (b₂ : X₂ ⟶ Z) [IsOpenImmersion a₁] [IsOpenImmersion a₂]
    [IsOpenImmersion b₁] [IsOpenImmersion b₂] (w : a₁ ≫ b₁ = a₂ ≫ b₂)
    (hcov : ∀ z, z ∈ Set.range b₁ ∨ z ∈ Set.range b₂)
    (hinter : ∀ z, z ∈ Set.range b₁ → z ∈ Set.range b₂ → z ∈ Set.range (a₁ ≫ b₁)) :
    IsPushout a₁ a₂ b₁ b₂ := by
  have : ∀ j, IsOpenImmersion ((PushoutCocone.mk b₁ b₂ w).ι.app j) := by
    rintro (_ | _ | _) <;> dsimp <;> infer_instance
  refine IsPushout.of_isColimit (isColimitOfOpenCover (span a₁ a₂) (PushoutCocone.mk b₁ b₂ w) ?_ ?_)
  · intro z
    rcases hcov z with h | h
    · exact ⟨WalkingSpan.left, h⟩
    · exact ⟨WalkingSpan.right, h⟩
  · have hzero : ∀ (j : WalkingSpan), Nonempty (WalkingSpan.zero ⟶ j) := by
      rintro (_ | _ | _)
      exacts [⟨𝟙 _⟩, ⟨WalkingSpan.Hom.fst⟩, ⟨WalkingSpan.Hom.snd⟩]
    rintro (_ | _ | _) (_ | _ | _) z hz hz'
    all_goals first
      | exact ⟨_, 𝟙 _, (hzero _).some, hz⟩
      | exact ⟨_, (hzero _).some, 𝟙 _, hz'⟩
      | exact ⟨_, 𝟙 _, 𝟙 _, hz⟩
      | exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, hinter z hz hz'⟩
      | exact ⟨WalkingSpan.zero, WalkingSpan.Hom.snd, WalkingSpan.Hom.fst,
          hinter z hz' hz⟩

/-- In a pushout of open immersions, the images of the two pieces meet in the image of the
common open. -/
lemma mem_range_of_pushout {W X₁ X₂ : Scheme.{u}} (a₁ : W ⟶ X₁) (a₂ : W ⟶ X₂)
    [IsOpenImmersion a₁] [IsOpenImmersion a₂] (z : (pushout a₁ a₂ : Scheme.{u}))
    (h₁ : z ∈ Set.range (pushout.inl a₁ a₂)) (h₂ : z ∈ Set.range (pushout.inr a₁ a₂)) :
    z ∈ Set.range (a₁ ≫ pushout.inl a₁ a₂) := by
  obtain ⟨x₁, rfl⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  obtain ⟨k, fi, fj, x, hx, -⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span a₁ a₂)
    (i := WalkingSpan.left) (j := WalkingSpan.right)).1 hx₂.symm
  rcases k with _ | _ | _
  · obtain rfl : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
    refine ⟨x, ?_⟩
    rw [Scheme.Hom.comp_apply, ← hx]
    rfl
  · cases fj
  · cases fi

/-- In a pushout of open immersions, the images of the two pieces meet exactly in the image of
the common open. -/
lemma range_inl_inter_range_inr {W X₁ X₂ : Scheme.{u}} (a₁ : W ⟶ X₁) (a₂ : W ⟶ X₂)
    [IsOpenImmersion a₁] [IsOpenImmersion a₂] :
    Set.range (pushout.inl a₁ a₂) ∩ Set.range (pushout.inr a₁ a₂) =
      Set.range (a₁ ≫ pushout.inl a₁ a₂) := by
  refine subset_antisymm (fun z hz => mem_range_of_pushout a₁ a₂ z hz.1 hz.2) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨a₁ x, rfl⟩, a₂ x, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← pushout.condition]

/-- A pushout of open immersions is covered by the images of its two pieces. -/
lemma mem_range_inl_or_inr {W X₁ X₂ : Scheme.{u}} (a₁ : W ⟶ X₁) (a₂ : W ⟶ X₂)
    [IsOpenImmersion a₁] [IsOpenImmersion a₂] (z : (pushout a₁ a₂ : Scheme.{u})) :
    z ∈ Set.range (pushout.inl a₁ a₂) ∨ z ∈ Set.range (pushout.inr a₁ a₂) := by
  obtain ⟨i, xi, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span a₁ a₂) z
  rcases i with _ | _ | _
  · left
    refine ⟨a₁ xi, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← colimit.w (span a₁ a₂) WalkingSpan.Hom.fst]
    rfl
  · exact Or.inl ⟨xi, rfl⟩
  · exact Or.inr ⟨xi, rfl⟩

/-- The union of two quasi-separated opens with quasi-compact intersection is quasi-separated. -/
lemma quasiSeparatedSpace_of_sup {X : Scheme.{u}} (O₁ O₂ : X.Opens)
    (hcov : ∀ x, x ∈ O₁ ∨ x ∈ O₂) (h₁ : IsQuasiSeparated (O₁ : Set X))
    (h₂ : IsQuasiSeparated (O₂ : Set X)) (h₁₂ : IsCompact ((O₁ : Set X) ∩ O₂)) :
    QuasiSeparatedSpace X := by
  let ι := {U : X.affineOpens // U.1 ≤ O₁ ∨ U.1 ≤ O₂}
  let b : ι → Set X := fun U => U.1.1
  have hb : TopologicalSpace.IsTopologicalBasis (Set.range b) := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨U, rfl⟩
      exact U.1.1.isOpen
    · intro x V hx hV
      have key : ∀ O : X.Opens, x ∈ O → ∃ U : X.affineOpens, x ∈ U.1 ∧ (U.1 : Set X) ⊆ V ∧
          U.1 ≤ O := by
        intro O hxO
        obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
          (show x ∈ (O ⊓ ⟨V, hV⟩ : X.Opens) from ⟨hxO, hx⟩) (O ⊓ ⟨V, hV⟩).isOpen
        exact ⟨⟨U, hU⟩, hxU, fun y hy => (hUV hy).2, fun y hy => (hUV hy).1⟩
      rcases hcov x with hxO | hxO
      · obtain ⟨U, hxU, hUV, hUO⟩ := key O₁ hxO
        exact ⟨_, ⟨⟨U, Or.inl hUO⟩, rfl⟩, hxU, hUV⟩
      · obtain ⟨U, hxU, hUV, hUO⟩ := key O₂ hxO
        exact ⟨_, ⟨⟨U, Or.inr hUO⟩, rfl⟩, hxU, hUV⟩
  have hc : ∀ U : ι, IsCompact (b U) := fun U => U.1.2.isCompact
  have ho : ∀ U : ι, IsOpen (b U) := fun U => U.1.1.isOpen
  have h₁₂o : IsOpen ((O₁ : Set X) ∩ O₂) := O₁.isOpen.inter O₂.isOpen
  have mixed : ∀ U V : ι, b U ⊆ O₁ → b V ⊆ O₂ → IsCompact (b U ∩ b V) := by
    intro U V hU hV
    have e : b U ∩ b V = (b U ∩ ((O₁ : Set X) ∩ O₂)) ∩ (b V ∩ ((O₁ : Set X) ∩ O₂)) := by
      ext y
      constructor
      · rintro ⟨hyU, hyV⟩
        exact ⟨⟨hyU, hU hyU, hV hyV⟩, hyV, hU hyU, hV hyV⟩
      · rintro ⟨⟨hyU, -⟩, hyV, -⟩
        exact ⟨hyU, hyV⟩
    have c₁ : IsCompact (b U ∩ ((O₁ : Set X) ∩ O₂)) :=
      h₁ _ _ hU (ho U) (hc U) Set.inter_subset_left h₁₂o h₁₂
    have c₂ : IsCompact (b V ∩ ((O₁ : Set X) ∩ O₂)) :=
      h₂ _ _ hV (ho V) (hc V) Set.inter_subset_right h₁₂o h₁₂
    rw [e]
    exact h₁ _ _ (Set.inter_subset_right.trans Set.inter_subset_left) ((ho U).inter h₁₂o) c₁
      (Set.inter_subset_right.trans Set.inter_subset_left) ((ho V).inter h₁₂o) c₂
  refine QuasiSeparatedSpace.of_isTopologicalBasis hb fun U V => ?_
  rcases U.2 with hU | hU <;> rcases V.2 with hV | hV
  · exact h₁ _ _ hU (ho U) (hc U) hV (ho V) (hc V)
  · exact mixed U V hU hV
  · rw [Set.inter_comm]
    exact mixed V U hV hU
  · exact h₂ _ _ hU (ho U) (hc U) hV (ho V) (hc V)

/-- Given a pullback square `X = A ×_{D} T` and a morphism `ι : A → Z` over `D`, the induced
morphism `X → Z ×_{D} T` is a base change of `ι`. -/
lemma isPullback_lift_comp {X A Z T S : Scheme.{u}} {g : X ⟶ A} {f' : X ⟶ T} {sA : A ⟶ S}
    {π : T ⟶ S} (h : IsPullback g f' sA π) (ι : A ⟶ Z) (fZ : Z ⟶ S) (hι : ι ≫ fZ = sA) :
    IsPullback (pullback.lift (g ≫ ι) f' (by rw [Category.assoc, hι, h.w]) :
      X ⟶ pullback fZ π) g (pullback.fst fZ π) ι := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback fZ π).flip
  rw [pullback.lift_snd, hι]
  exact h.flip

/-- The image of a base change of an open immersion is the preimage of its image. -/
lemma range_eq_preimage_of_isPullback {X A Z P : Scheme.{u}} {top : X ⟶ P} {left : X ⟶ A}
    {right : P ⟶ Z} {bot : A ⟶ Z} (h : IsPullback top left right bot) :
    Set.range top = right ⁻¹' Set.range bot := by
  rw [← Scheme.Pullback.range_fst right bot, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ]
  exact h.isoPullback.hom.surjective

end OpenCoverColimit

/-! ### Descent of isomorphisms between models -/

section IsoDescent

instance {I : Type*} [Category I] [Quiver.IsThin I] (i : I) : Quiver.IsThin (Over i) :=
  fun _ _ => ⟨fun _ _ => Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
variable {k : I} {X₁ X₂ : Scheme.{u}} {f₁ : X₁ ⟶ c.pt} {f₂ : X₂ ⟶ c.pt}

/-- The base change to level `l` of a morphism `b` from the level-`l₁` model to the level-`k`
scheme `r₂.Y`, as a morphism between the level-`l` base changes. -/
noncomputable def liftAtLevel (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) {l₁ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₁ ⟶ r₂.Y)
    (hb : b ≫ r₂.fY = pullback.fst _ _ ≫ r₁.fY) {l : Over k} (h : l ⟶ l₁) :
    (baseChangeDiagram D r₁.fY).obj l ⟶ (baseChangeDiagram D r₂.fY).obj l :=
  pullback.lift ((baseChangeDiagram D r₁.fY).map h ≫ b) (pullback.snd _ _) (by
    rw [Category.assoc, hb, ← Category.assoc]
    simp [pullback.condition])

variable {D c}

@[reassoc (attr := simp)]
lemma liftAtLevel_fst (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) {l₁ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₁ ⟶ r₂.Y)
    (hb : b ≫ r₂.fY = pullback.fst _ _ ≫ r₁.fY) {l : Over k} (h : l ⟶ l₁) :
    liftAtLevel D c r₁ r₂ b hb h ≫ pullback.fst _ _ = (baseChangeDiagram D r₁.fY).map h ≫ b :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma liftAtLevel_snd (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) {l₁ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₁ ⟶ r₂.Y)
    (hb : b ≫ r₂.fY = pullback.fst _ _ ≫ r₁.fY) {l : Over k} (h : l ⟶ l₁) :
    liftAtLevel D c r₁ r₂ b hb h ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

lemma π_liftAtLevel (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) {l₁ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₁ ⟶ r₂.Y)
    (hb : b ≫ r₂.fY = pullback.fst _ _ ≫ r₁.fY) (a : X₁ ⟶ X₂) (ha : a ≫ f₂ = f₁)
    (hab : (baseChangeCone D c r₁.isPullback).π.app l₁ ≫ b = a ≫ r₂.g)
    {l : Over k} (h : l ⟶ l₁) :
    (baseChangeCone D c r₁.isPullback).π.app l ≫ liftAtLevel D c r₁ r₂ b hb h =
      a ≫ (baseChangeCone D c r₂.isPullback).π.app l := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftAtLevel_fst, ← Category.assoc, (baseChangeCone D c _).w h, hab]
    simp
  · simp [reassoc_of% ha]

lemma map_liftAtLevel (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) {l₁ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₁ ⟶ r₂.Y)
    (hb : b ≫ r₂.fY = pullback.fst _ _ ≫ r₁.fY) {l l' : Over k} (h : l ⟶ l₁) (g : l' ⟶ l) :
    (baseChangeDiagram D r₁.fY).map g ≫ liftAtLevel D c r₁ r₂ b hb h =
      liftAtLevel D c r₁ r₂ b hb (g ≫ h) ≫ (baseChangeDiagram D r₂.fY).map g := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftAtLevel_fst, Category.assoc, baseChangeDiagram_map_fst,
      liftAtLevel_fst, Functor.map_comp, Category.assoc]
  · simp only [Category.assoc, liftAtLevel_snd, baseChangeDiagram_map_snd,
      liftAtLevel_snd_assoc]

/-- The base change to a level `l → l₀` of a morphism between the level-`l₀` base changes of two
models. -/
noncomputable def baseChangeHom (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) {l₀ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₀ ⟶ (baseChangeDiagram D r₂.fY).obj l₀)
    (hb : b ≫ pullback.snd _ _ = pullback.snd _ _) {l : Over k} (g : l ⟶ l₀) :
    (baseChangeDiagram D r₁.fY).obj l ⟶ (baseChangeDiagram D r₂.fY).obj l :=
  liftAtLevel D c r₁ r₂ (b ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, reassoc_of% hb, ← pullback.condition]) g

@[reassoc (attr := simp)]
lemma baseChangeHom_fst (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) {l₀ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₀ ⟶ (baseChangeDiagram D r₂.fY).obj l₀)
    (hb : b ≫ pullback.snd _ _ = pullback.snd _ _) {l : Over k} (g : l ⟶ l₀) :
    baseChangeHom r₁ r₂ b hb g ≫ pullback.fst _ _ =
      (baseChangeDiagram D r₁.fY).map g ≫ b ≫ pullback.fst _ _ :=
  liftAtLevel_fst _ _ _ _ _

@[reassoc (attr := simp)]
lemma baseChangeHom_snd (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) {l₀ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₀ ⟶ (baseChangeDiagram D r₂.fY).obj l₀)
    (hb : b ≫ pullback.snd _ _ = pullback.snd _ _) {l : Over k} (g : l ⟶ l₀) :
    baseChangeHom r₁ r₂ b hb g ≫ pullback.snd _ _ = pullback.snd _ _ :=
  liftAtLevel_snd _ _ _ _ _

@[reassoc]
lemma baseChangeHom_map (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) {l₀ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₀ ⟶ (baseChangeDiagram D r₂.fY).obj l₀)
    (hb : b ≫ pullback.snd _ _ = pullback.snd _ _) {l : Over k} (g : l ⟶ l₀) :
    baseChangeHom r₁ r₂ b hb g ≫ (baseChangeDiagram D r₂.fY).map g =
      (baseChangeDiagram D r₁.fY).map g ≫ b := by
  apply pullback.hom_ext
  · simp
  · simp [hb]

lemma baseChangeHom_congr (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) {l₀ : Over k}
    {b b' : (baseChangeDiagram D r₁.fY).obj l₀ ⟶ (baseChangeDiagram D r₂.fY).obj l₀}
    (hb : b ≫ pullback.snd _ _ = pullback.snd _ _) (hb' : b' ≫ pullback.snd _ _ = pullback.snd _ _)
    (h : b = b') {l : Over k} (g : l ⟶ l₀) :
    baseChangeHom r₁ r₂ b hb g = baseChangeHom r₁ r₂ b' hb' g := by
  subst h
  rfl

@[reassoc]
lemma baseChangeHom_comp (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k)
    {X₃ : Scheme.{u}} {f₃ : X₃ ⟶ c.pt} (r₃ : Model D c f₃ k) {l₀ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₀ ⟶ (baseChangeDiagram D r₂.fY).obj l₀)
    (hb : b ≫ pullback.snd _ _ = pullback.snd _ _)
    (b' : (baseChangeDiagram D r₂.fY).obj l₀ ⟶ (baseChangeDiagram D r₃.fY).obj l₀)
    (hb' : b' ≫ pullback.snd _ _ = pullback.snd _ _) {l : Over k} (g : l ⟶ l₀) :
    baseChangeHom r₁ r₂ b hb g ≫ baseChangeHom r₂ r₃ b' hb' g =
      baseChangeHom r₁ r₃ (b ≫ b') (by rw [Category.assoc, hb', hb]) g := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeHom_fst, baseChangeHom_map_assoc, baseChangeHom_fst,
      Category.assoc]
  · simp

lemma baseChangeHom_id (r₁ : Model D c f₁ k) {l₀ : Over k} {l : Over k} (g : l ⟶ l₀) :
    baseChangeHom r₁ r₁ (𝟙 ((baseChangeDiagram D r₁.fY).obj l₀)) (Category.id_comp _) g = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [baseChangeHom]

lemma π_baseChangeHom (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) {l₀ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₀ ⟶ (baseChangeDiagram D r₂.fY).obj l₀)
    (hb : b ≫ pullback.snd _ _ = pullback.snd _ _) (a : X₁ ⟶ X₂) (ha : a ≫ f₂ = f₁)
    (hab : (baseChangeCone D c r₁.isPullback).π.app l₀ ≫ b =
      a ≫ (baseChangeCone D c r₂.isPullback).π.app l₀) {l : Over k} (g : l ⟶ l₀) :
    (baseChangeCone D c r₁.isPullback).π.app l ≫ baseChangeHom r₁ r₂ b hb g =
      a ≫ (baseChangeCone D c r₂.isPullback).π.app l := by
  refine π_liftAtLevel r₁ r₂ _ _ a ha ?_ g
  rw [← Category.assoc, hab, Category.assoc]
  simp

variable (D c) [IsCofiltered I] [Quiver.IsThin I] (hc : IsLimit c)
  [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
  [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]

include hc in
/-- **Descent of isomorphisms** (EGA IV 8.8.2.5). Let `r₁, r₂` be models at level `k`, of finite
presentation, of two schemes over `lim D`, and let `θ : X₁ ≅ X₂` be an isomorphism over `lim D`.
Then the base changes of the models to some level `l → k` are isomorphic over `D l`, compatibly
with `θ`. -/
theorem exists_iso_of_iso (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k)
    [QuasiCompact r₁.fY] [QuasiSeparated r₁.fY] [LocallyOfFinitePresentation r₁.fY]
    [QuasiCompact r₂.fY] [QuasiSeparated r₂.fY] [LocallyOfFinitePresentation r₂.fY]
    (θ : X₁ ≅ X₂) (hθ : θ.hom ≫ f₂ = f₁) :
    ∃ (l : Over k) (Θ : (baseChangeDiagram D r₁.fY).obj l ≅ (baseChangeDiagram D r₂.fY).obj l),
      Θ.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        (baseChangeCone D c r₁.isPullback).π.app l ≫ Θ.hom =
          θ.hom ≫ (baseChangeCone D c r₂.isPullback).π.app l := by
  have hθ' : θ.inv ≫ f₁ = f₂ := by rw [← hθ, Iso.inv_hom_id_assoc]
  obtain ⟨l₁, b₁, hb₁, hb₁'⟩ := exists_hom_of_isPullback D c hc r₁.fY r₂.fY r₁.isPullback
    (θ.hom ≫ r₂.g) (by rw [Category.assoc, r₂.isPullback.w, reassoc_of% hθ, r₁.isPullback.w])
  obtain ⟨l₂, b₂, hb₂, hb₂'⟩ := exists_hom_of_isPullback D c hc r₂.fY r₁.fY r₂.isPullback
    (θ.inv ≫ r₁.g) (by rw [Category.assoc, r₁.isPullback.w, reassoc_of% hθ', r₂.isPullback.w])
  let l₃ := IsCofiltered.min l₁ l₂
  let h₃₁ : l₃ ⟶ l₁ := IsCofiltered.minToLeft l₁ l₂
  let h₃₂ : l₃ ⟶ l₂ := IsCofiltered.minToRight l₁ l₂
  let Θ₁ := fun {l : Over k} (h : l ⟶ l₁) => liftAtLevel D c r₁ r₂ b₁ hb₁ h
  let Θ₂ := fun {l : Over k} (h : l ⟶ l₂) => liftAtLevel D c r₂ r₁ b₂ hb₂ h
  have hΘ₁ := fun {l : Over k} (h : l ⟶ l₁) =>
    π_liftAtLevel r₁ r₂ b₁ hb₁ θ.hom hθ hb₁' h
  have hΘ₂ := fun {l : Over k} (h : l ⟶ l₂) =>
    π_liftAtLevel r₂ r₁ b₂ hb₂ θ.inv hθ' hb₂' h
  -- the two composites agree with the identity at some levels
  have key₁ := exists_eq_of_isPullback D c hc r₁.fY r₁.fY r₁.isPullback
    (j := l₃) (Θ₁ h₃₁ ≫ Θ₂ h₃₂ ≫ pullback.fst _ _) (pullback.fst _ _)
    (by simp only [Θ₁, Θ₂, Category.assoc]
        rw [pullback.condition, liftAtLevel_snd_assoc, liftAtLevel_snd_assoc,
          ← pullback.condition]) rfl
    (by rw [← Category.assoc, hΘ₁, Category.assoc, reassoc_of% hΘ₂, Iso.hom_inv_id_assoc])
  have key₂ := exists_eq_of_isPullback D c hc r₂.fY r₂.fY r₂.isPullback
    (j := l₃) (Θ₂ h₃₂ ≫ Θ₁ h₃₁ ≫ pullback.fst _ _) (pullback.fst _ _)
    (by simp only [Θ₁, Θ₂, Category.assoc]
        rw [pullback.condition, liftAtLevel_snd_assoc, liftAtLevel_snd_assoc,
          ← pullback.condition]) rfl
    (by rw [← Category.assoc, hΘ₂, Category.assoc, reassoc_of% hΘ₁, Iso.inv_hom_id_assoc])
  obtain ⟨l₄, g₄, e₄⟩ := key₁
  obtain ⟨l₅, g₅, e₅⟩ := key₂
  let l₆ := IsCofiltered.min l₄ l₅
  let m₄ : l₆ ⟶ l₃ := IsCofiltered.minToLeft l₄ l₅ ≫ g₄
  have hm₅ : m₄ = IsCofiltered.minToRight l₄ l₅ ≫ g₅ := Subsingleton.elim _ _
  have comp₁ : Θ₁ (m₄ ≫ h₃₁) ≫ Θ₂ (m₄ ≫ h₃₂) = 𝟙 _ := by
    apply pullback.hom_ext
    · have h1 := map_liftAtLevel r₁ r₂ b₁ hb₁ h₃₁ m₄
      have h2 : Θ₂ (m₄ ≫ h₃₂) ≫ pullback.fst _ _ =
          (baseChangeDiagram D r₂.fY).map m₄ ≫ Θ₂ h₃₂ ≫ pullback.fst _ _ := by
        simp only [Θ₂, liftAtLevel_fst, Functor.map_comp, Category.assoc]
      rw [Category.assoc, h2, ← Category.assoc, ← h1, Category.assoc,
        show m₄ = IsCofiltered.minToLeft l₄ l₅ ≫ g₄ from rfl, Functor.map_comp, Category.assoc,
        e₄]
      simp
    · simp [Θ₁, Θ₂]
  have comp₂ : Θ₂ (m₄ ≫ h₃₂) ≫ Θ₁ (m₄ ≫ h₃₁) = 𝟙 _ := by
    apply pullback.hom_ext
    · have h1 := map_liftAtLevel r₂ r₁ b₂ hb₂ h₃₂ m₄
      have h2 : Θ₁ (m₄ ≫ h₃₁) ≫ pullback.fst _ _ =
          (baseChangeDiagram D r₁.fY).map m₄ ≫ Θ₁ h₃₁ ≫ pullback.fst _ _ := by
        simp only [Θ₁, liftAtLevel_fst, Functor.map_comp, Category.assoc]
      rw [Category.assoc, h2, ← Category.assoc, ← h1, Category.assoc, hm₅, Functor.map_comp,
        Category.assoc, e₅]
      simp
    · simp [Θ₁, Θ₂]
  exact ⟨l₆, ⟨Θ₁ (m₄ ≫ h₃₁), Θ₂ (m₄ ≫ h₃₂), comp₁, comp₂⟩, by simp [Θ₁], hΘ₁ _⟩

end IsoDescent

section IsoDescent'

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  [IsCofiltered I] [Quiver.IsThin I] (hc : IsLimit c)
  [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
  [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
variable {k : I} {X₁ X₂ : Scheme.{u}} {f₁ : X₁ ⟶ c.pt} {f₂ : X₂ ⟶ c.pt}

include hc in
/-- **Descent of isomorphisms of morphisms** (EGA IV 8.10.5 (iv)). Let `b` be a morphism over
`D l₀` between the level-`l₀` base changes of two models of finite presentation, whose base change
to `lim D` is an isomorphism. Then its base change to some level `l → l₀` is an isomorphism. -/
theorem exists_isIso_baseChangeHom (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k)
    [QuasiCompact r₁.fY] [QuasiSeparated r₁.fY] [LocallyOfFinitePresentation r₁.fY]
    [QuasiCompact r₂.fY] [QuasiSeparated r₂.fY] [LocallyOfFinitePresentation r₂.fY]
    {l₀ : Over k}
    (b : (baseChangeDiagram D r₁.fY).obj l₀ ⟶ (baseChangeDiagram D r₂.fY).obj l₀)
    (hb : b ≫ pullback.snd _ _ = pullback.snd _ _) (a : X₁ ⟶ X₂) [IsIso a] (ha : a ≫ f₂ = f₁)
    (hab : (baseChangeCone D c r₁.isPullback).π.app l₀ ≫ b =
      a ≫ (baseChangeCone D c r₂.isPullback).π.app l₀) :
    ∃ (l : Over k) (g : l ⟶ l₀), IsIso (baseChangeHom r₁ r₂ b hb g) := by
  obtain ⟨l₁, Θ, hΘs, hΘπ⟩ := exists_iso_of_iso D c hc r₁ r₂ (asIso a) ha
  let l₂ := IsCofiltered.min l₀ l₁
  let g₀ : l₂ ⟶ l₀ := IsCofiltered.minToLeft l₀ l₁
  let g₁ : l₂ ⟶ l₁ := IsCofiltered.minToRight l₀ l₁
  have hΘs' : Θ.inv ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [← hΘs, Iso.inv_hom_id_assoc]
  -- the base change of `b` and of `Θ` agree at some level
  have e1 := π_baseChangeHom r₁ r₂ b hb a ha hab g₀
  have e2 := π_baseChangeHom r₁ r₂ Θ.hom hΘs a ha hΘπ g₁
  obtain ⟨l₃, g₃, e₃⟩ := exists_eq_of_isPullback D c hc r₁.fY r₂.fY r₁.isPullback (j := l₂)
    (baseChangeHom r₁ r₂ b hb g₀ ≫ pullback.fst _ _)
    (baseChangeHom r₁ r₂ Θ.hom hΘs g₁ ≫ pullback.fst _ _)
    (by rw [Category.assoc, pullback.condition, baseChangeHom_snd_assoc, pullback.condition])
    (by rw [Category.assoc, pullback.condition, baseChangeHom_snd_assoc, pullback.condition])
    (by simp only [← Category.assoc]; rw [e1, e2])
  refine ⟨l₃, g₃ ≫ g₀, ?_⟩
  have key : baseChangeHom r₁ r₂ b hb (g₃ ≫ g₀) = baseChangeHom r₁ r₂ Θ.hom hΘs (g₃ ≫ g₁) := by
    apply pullback.hom_ext
    · simp only [baseChangeHom_fst, Functor.map_comp, Category.assoc] at e₃ ⊢
      exact e₃
    · simp
  rw [key]
  refine ⟨baseChangeHom r₂ r₁ Θ.inv hΘs' (g₃ ≫ g₁), ?_, ?_⟩
  · rw [baseChangeHom_comp, baseChangeHom_congr r₁ r₁ _ (Category.id_comp _) Θ.hom_inv_id,
      baseChangeHom_id]
  · rw [baseChangeHom_comp, baseChangeHom_congr r₂ r₂ _ (Category.id_comp _) Θ.inv_hom_id,
      baseChangeHom_id]

end IsoDescent'

/-! ### Descent of closed immersions -/

section ClosedImmersion

/-- In a pushout square of rings `A → B, A → C, B → P, C → P`, if the images in `P` of a set of
`A`-algebra generators of `B` lie in the image of `C`, then `C → P` is surjective. -/
lemma surjective_inr_of_isPushout {A B C P : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (H : IsPushout f g inl inr) (s : Set B)
    (hs : letI := f.hom.toAlgebra; Algebra.adjoin A s = ⊤)
    (hsP : ∀ x ∈ s, inl x ∈ Set.range inr) : Function.Surjective inr := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  have H' : IsPushout f g (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom) :=
    CommRingCat.isPushout_tensorProduct A B C
  let e := H'.isoIsPushout _ _ H
  have he₁ : ∀ b : B, e.hom (b ⊗ₜ 1) = inl b := fun b =>
    congrArg (fun φ => φ b) (H'.inl_isoIsPushout_hom _ _ H)
  have he₂ : ∀ c' : C, e.hom (1 ⊗ₜ c') = inr c' := fun c' =>
    congrArg (fun φ => φ c') (H'.inr_isoIsPushout_hom _ _ H)
  have hinj : Function.Injective e.hom := (ConcreteCategory.bijective_of_isIso e.hom).1
  let T := (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).range
  have hB : ∀ b : B, b ⊗ₜ[A] (1 : C) ∈ T := by
    intro b
    have hb : b ∈ Algebra.adjoin A s := by rw [hs]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨c', hc'⟩ := hsP x hx
      refine ⟨c', hinj ?_⟩
      change e.hom (1 ⊗ₜ c') = _
      rw [he₂, he₁, hc']
    | algebraMap a =>
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      exact ⟨a • 1, rfl⟩
    | add x y _ _ hx hy =>
      rw [TensorProduct.add_tmul]
      exact T.add_mem hx hy
    | mul x y _ _ hx hy =>
      have : (x * y) ⊗ₜ[A] (1 : C) = (x ⊗ₜ[A] (1 : C)) * (y ⊗ₜ 1) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [this]
      exact T.mul_mem hx hy
  have hsurj : Function.Surjective (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul b c' =>
      have : b ⊗ₜ[A] c' = (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ c') := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact T.mul_mem (hB b) ⟨c', rfl⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
  intro p
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 p
  obtain ⟨c', rfl⟩ := hsurj z
  exact ⟨c', (he₂ c').symm⟩

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}
variable {k : I} {X₁ X₂ : Scheme.{u}} {f₁ : X₁ ⟶ c.pt} {f₂ : X₂ ⟶ c.pt}

/-- The base change to the level `l → k` of a morphism `h` between the schemes of two models at
level `k`. -/
noncomputable def topBaseChange (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) (h : r₁.Y ⟶ r₂.Y)
    (hh : h ≫ r₂.fY = r₁.fY) (l : Over k) :
    (baseChangeDiagram D r₁.fY).obj l ⟶ (baseChangeDiagram D r₂.fY).obj l :=
  pullback.map r₁.fY (D.map l.hom) r₂.fY (D.map l.hom) h (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hh]) (by simp)

variable (r₁ : Model D c f₁ k) (r₂ : Model D c f₂ k) (h : r₁.Y ⟶ r₂.Y) (hh : h ≫ r₂.fY = r₁.fY)

@[reassoc (attr := simp)]
lemma topBaseChange_fst (l : Over k) :
    topBaseChange r₁ r₂ h hh l ≫ pullback.fst _ _ = pullback.fst _ _ ≫ h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma topBaseChange_snd (l : Over k) :
    topBaseChange r₁ r₂ h hh l ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [topBaseChange]

@[reassoc]
lemma topBaseChange_map {l l' : Over k} (g : l' ⟶ l) :
    topBaseChange r₁ r₂ h hh l' ≫ (baseChangeDiagram D r₂.fY).map g =
      (baseChangeDiagram D r₁.fY).map g ≫ topBaseChange r₁ r₂ h hh l := by
  apply pullback.hom_ext <;> simp

lemma isPullback_topBaseChange_map {l l' : Over k} (g : l' ⟶ l) :
    IsPullback ((baseChangeDiagram D r₁.fY).map g) (topBaseChange r₁ r₂ h hh l')
      (topBaseChange r₁ r₂ h hh l) ((baseChangeDiagram D r₂.fY).map g) := by
  refine IsPullback.of_bot ?_ (topBaseChange_map r₁ r₂ h hh g).symm
    (isPullback_baseChangeDiagram_map D r₂.fY g)
  rw [topBaseChange_snd, topBaseChange_snd]
  exact isPullback_baseChangeDiagram_map D r₁.fY g

lemma isPullback_topBaseChange (l : Over k) :
    IsPullback (pullback.fst _ _) (topBaseChange r₁ r₂ h hh l) h (pullback.fst _ _) := by
  refine IsPullback.of_bot ?_ (topBaseChange_fst r₁ r₂ h hh l).symm
    (IsPullback.of_hasPullback r₂.fY (D.map l.hom))
  rw [topBaseChange_snd, hh]
  exact IsPullback.of_hasPullback r₁.fY (D.map l.hom)

lemma π_topBaseChange (a : X₁ ⟶ X₂) (ha : r₁.g ≫ h = a ≫ r₂.g) (ha' : a ≫ f₂ = f₁)
    (l : Over k) :
    (baseChangeCone D c r₁.isPullback).π.app l ≫ topBaseChange r₁ r₂ h hh l =
      a ≫ (baseChangeCone D c r₂.isPullback).π.app l := by
  apply pullback.hom_ext
  · simp [ha]
  · simp [reassoc_of% ha']

/-- The base change of an open subscheme `U ⊆ r.Y` to a level is the preimage of `U`. -/
lemma isPullback_baseChange_restrict {X : Scheme.{u}} {f : X ⟶ c.pt} (r : Model D c f k)
    (U : r.Y.Opens) (l : Over k) :
    IsPullback (pullback.map (U.ι ≫ r.fY) (D.map l.hom) r.fY (D.map l.hom) U.ι (𝟙 _) (𝟙 _)
        (Category.comp_id _) (by simp))
      (pullback.fst (U.ι ≫ r.fY) (D.map l.hom)) (pullback.fst r.fY (D.map l.hom)) U.ι := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback r.fY (D.map l.hom)).flip
  rw [pullback.lift_snd, Category.comp_id]
  exact (IsPullback.of_hasPullback (U.ι ≫ r.fY) (D.map l.hom)).flip

lemma appTop_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (f ≫ g).appTop x = f.appTop (g.appTop x) := by
  rw [Scheme.Hom.comp_appTop]
  rfl

variable [IsCofiltered I] [Quiver.IsThin I] (hc : IsLimit c)
  [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
  [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]

include hc in
/-- **Descent of closed immersions, affine target** (EGA IV 8.10.5 (iv)). Let `h : Y₁ → Y₂` be a
morphism over `D k` between the schemes of two models of finite presentation, with `Y₂` affine,
whose base change to `lim D` is a closed immersion. Then its base change to some level is a
closed immersion. -/
theorem exists_isClosedImmersion_of_isAffine
    [QuasiCompact r₁.fY] [QuasiSeparated r₁.fY] [LocallyOfFinitePresentation r₁.fY]
    [QuasiCompact r₂.fY] [QuasiSeparated r₂.fY] [LocallyOfFinitePresentation r₂.fY]
    [IsAffine r₂.Y] (a : X₁ ⟶ X₂) [IsClosedImmersion a] (ha : r₁.g ≫ h = a ≫ r₂.g)
    (ha' : a ≫ f₂ = f₁) :
    ∃ l : Over k, IsClosedImmersion (topBaseChange r₁ r₂ h hh l) := by
  have hc₁ := isLimitBaseChangeCone D c hc r₁.isPullback
  have hc₂ := isLimitBaseChangeCone D c hc r₂.isPullback
  have : IsAffineHom r₂.g := MorphismProperty.of_isPullback (P := @IsAffineHom)
    r₂.isPullback.flip (isAffineHom_π_app D c hc k)
  have : IsAffine X₂ := isAffine_of_isAffineHom r₂.g
  have : IsAffine X₁ := isAffine_of_isAffineHom a
  have : IsAffine (baseChangeCone D c r₁.isPullback).pt := inferInstanceAs (IsAffine X₁)
  obtain ⟨l₁, hl₁⟩ := Scheme.exists_isAffine_of_isLimit (baseChangeDiagram D r₁.fY)
    (baseChangeCone D c r₁.isPullback) hc₁
  have : LocallyOfFiniteType (h ≫ r₂.fY) := by rw [hh]; infer_instance
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h r₂.fY
  have hbcA : ∀ l : Over k, IsAffine ((baseChangeDiagram D r₂.fY).obj l) := fun l =>
    have : IsAffineHom (pullback.fst r₂.fY (D.map l.hom)) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    isAffine_of_isAffineHom (pullback.fst r₂.fY (D.map l.hom))
  have : LocallyOfFiniteType (topBaseChange r₁ r₂ h hh l₁) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (isPullback_topBaseChange r₁ r₂ h hh l₁) inferInstance
  have hft : (topBaseChange r₁ r₂ h hh l₁).appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 inferInstance
  let := (topBaseChange r₁ r₂ h hh l₁).appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  -- every generator lies in the image at some level
  have hsurjLim : Function.Surjective a.appTop := a.app_surjective ⊤ (isAffineOpen_top X₂)
  have key : ∀ x ∈ s, ∃ (l : Over k) (g : l ⟶ l₁),
      ((baseChangeDiagram D r₁.fY).map g).appTop x ∈
        Set.range (topBaseChange r₁ r₂ h hh l).appTop := by
    intro x _
    obtain ⟨y, hy⟩ := hsurjLim (((baseChangeCone D c r₁.isPullback).π.app l₁).appTop x)
    obtain ⟨l₂, hl₂⟩ := exists_appTop_eq (baseChangeDiagram D r₂.fY)
      (baseChangeCone D c r₂.isPullback) hc₂ {y}
    obtain ⟨y', hy'⟩ := hl₂ y (Finset.mem_singleton_self y)
    let l' := IsCofiltered.min l₁ l₂
    let g₁ : l' ⟶ l₁ := IsCofiltered.minToLeft l₁ l₂
    let g₂ : l' ⟶ l₂ := IsCofiltered.minToRight l₁ l₂
    let z := ((baseChangeDiagram D r₁.fY).map g₁).appTop x -
      (topBaseChange r₁ r₂ h hh l').appTop (((baseChangeDiagram D r₂.fY).map g₂).appTop y')
    have hz : ((baseChangeCone D c r₁.isPullback).π.app l').appTop z = 0 := by
      have m1 := congrArg (fun φ => φ.appTop x) ((baseChangeCone D c r₁.isPullback).w g₁)
      have m2 := congrArg (fun φ => φ.appTop y')
        (show (baseChangeCone D c r₁.isPullback).π.app l' ≫ topBaseChange r₁ r₂ h hh l' ≫
            (baseChangeDiagram D r₂.fY).map g₂ =
            a ≫ (baseChangeCone D c r₂.isPullback).π.app l₂ by
          rw [← Category.assoc, π_topBaseChange r₁ r₂ h hh a ha ha', Category.assoc,
            (baseChangeCone D c r₂.isPullback).w])
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at m1 m2
      simp only [z, map_sub, m2]
      erw [m1, hy', hy, sub_self]
    obtain ⟨l'', g'', hg''⟩ := exists_appTop_map_eq_zero_of_isLimit
      (baseChangeDiagram D r₁.fY) (baseChangeCone D c r₁.isPullback) hc₁ z hz
    refine ⟨l'', g'' ≫ g₁, ((baseChangeDiagram D r₂.fY).map (g'' ≫ g₂)).appTop y', ?_⟩
    simp only [z, map_sub, sub_eq_zero] at hg''
    have m3 := congrArg (fun φ => φ.appTop y')
      (show topBaseChange r₁ r₂ h hh l'' ≫ (baseChangeDiagram D r₂.fY).map (g'' ≫ g₂) =
          (baseChangeDiagram D r₁.fY).map g'' ≫ topBaseChange r₁ r₂ h hh l' ≫
            (baseChangeDiagram D r₂.fY).map g₂ by
        rw [Functor.map_comp, ← Category.assoc, topBaseChange_map, Category.assoc])
    have m4 := congrArg (fun φ => φ.appTop x)
      ((baseChangeDiagram D r₁.fY).map_comp g'' g₁)
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at m3 m4
    rw [m3, m4, hg'']
  choose L G hLG using key
  classical
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists
    (insert l₁ (s.attach.image fun x : {x // x ∈ s} => L x.1 x.2))
  obtain ⟨gl⟩ := hl (Finset.mem_insert_self _ _)
  refine ⟨l, ?_⟩
  have : IsAffine ((baseChangeDiagram D r₁.fY).obj l) :=
    isAffine_of_isAffineHom ((baseChangeDiagram D r₁.fY).map gl)
  refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
  have : IsAffine ((baseChangeDiagram D r₂.fY).obj l) := hbcA l
  have : IsAffine ((baseChangeDiagram D r₂.fY).obj l₁) := hbcA l₁
  have hpo : IsPushout (topBaseChange r₁ r₂ h hh l₁).appTop
      ((baseChangeDiagram D r₂.fY).map gl).appTop ((baseChangeDiagram D r₁.fY).map gl).appTop
      (topBaseChange r₁ r₂ h hh l).appTop :=
    isPushout_appTop_of_isPullback (isPullback_topBaseChange_map r₁ r₂ h hh gl)
  have hs' : letI := (topBaseChange r₁ r₂ h hh l₁).appTop.hom.toAlgebra
      Algebra.adjoin Γ((baseChangeDiagram D r₂.fY).obj l₁, ⊤)
        (s : Set Γ((baseChangeDiagram D r₁.fY).obj l₁, ⊤)) = ⊤ := hs
  refine surjective_inr_of_isPushout hpo (s : Set Γ((baseChangeDiagram D r₁.fY).obj l₁, ⊤)) hs'
    fun x hx => ?_
  obtain ⟨gx⟩ := hl (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem (fun x : {x // x ∈ s} => L x.1 x.2)
      (Finset.mem_attach s ⟨x, hx⟩)))
  obtain ⟨y, hy⟩ := hLG x hx
  refine ⟨((baseChangeDiagram D r₂.fY).map gx).appTop y, ?_⟩
  have hg : gl = gx ≫ G x hx := Subsingleton.elim _ _
  have m5 := congrArg (fun φ => φ.appTop y)
    (show topBaseChange r₁ r₂ h hh l ≫ (baseChangeDiagram D r₂.fY).map gx =
        (baseChangeDiagram D r₁.fY).map gx ≫ topBaseChange r₁ r₂ h hh (L x hx) from
      topBaseChange_map r₁ r₂ h hh gx)
  have m6 := congrArg (fun φ => φ.appTop x)
    ((baseChangeDiagram D r₁.fY).map_comp gx (G x hx))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at m5 m6
  rw [m5, hy, hg, m6]

include hc in
/-- **Descent of closed immersions** (EGA IV 8.10.5 (iv)). Let `h : Y₁ → Y₂` be a morphism over
`D k` between the schemes of two models of finite presentation, whose base change to `lim D` is a
closed immersion. Then its base change to some level is a closed immersion. -/
theorem exists_isClosedImmersion
    [QuasiCompact r₁.fY] [QuasiSeparated r₁.fY] [LocallyOfFinitePresentation r₁.fY]
    [QuasiCompact r₂.fY] [QuasiSeparated r₂.fY] [LocallyOfFinitePresentation r₂.fY]
    (a : X₁ ⟶ X₂) [IsClosedImmersion a] (ha : r₁.g ≫ h = a ≫ r₂.g) (ha' : a ≫ f₂ = f₁) :
    ∃ l : Over k, IsClosedImmersion (topBaseChange r₁ r₂ h hh l) := by
  classical
  have : CompactSpace r₂.Y := QuasiCompact.compactSpace_of_compactSpace r₂.fY
  have : QuasiSeparatedSpace r₁.Y := quasiSeparatedSpace_of_quasiSeparated r₁.fY
  have : QuasiSeparatedSpace r₂.Y := quasiSeparatedSpace_of_quasiSeparated r₂.fY
  have : QuasiCompact (h ≫ r₂.fY) := by rw [hh]; infer_instance
  have : QuasiCompact h := QuasiCompact.of_comp h r₂.fY
  obtain ⟨t, ht⟩ := RiemannZariskiSpace.exists_finite_affine_cover (S := r₂.Y)
  -- the restricted problems over the affine opens of the cover
  have key : ∀ V : t, ∃ l : Over k, IsClosedImmersion
      (topBaseChange (r₁.restrict (h ⁻¹ᵁ V.1.1)) (r₂.restrict V.1.1) (h ∣_ V.1.1)
        (by simp [Model.restrict, morphismRestrict_ι_assoc, hh]) l) := by
    intro V
    let U := (V.1 : r₂.Y.Opens)
    have : IsAffine U := V.1.2
    have : CompactSpace (h ⁻¹ᵁ U) :=
      isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.isOpen V.1.2.isCompact)
    have : QuasiCompact (r₁.restrict (h ⁻¹ᵁ U)).fY :=
      inferInstanceAs (QuasiCompact ((h ⁻¹ᵁ U).ι ≫ r₁.fY))
    have : QuasiSeparated (r₁.restrict (h ⁻¹ᵁ U)).fY :=
      inferInstanceAs (QuasiSeparated ((h ⁻¹ᵁ U).ι ≫ r₁.fY))
    have : LocallyOfFinitePresentation (r₁.restrict (h ⁻¹ᵁ U)).fY :=
      inferInstanceAs (LocallyOfFinitePresentation ((h ⁻¹ᵁ U).ι ≫ r₁.fY))
    have : CompactSpace U := isCompact_iff_compactSpace.mp V.1.2.isCompact
    have : QuasiCompact (r₂.restrict U).fY := inferInstanceAs (QuasiCompact (U.ι ≫ r₂.fY))
    have : QuasiSeparated (r₂.restrict U).fY := inferInstanceAs (QuasiSeparated (U.ι ≫ r₂.fY))
    have : LocallyOfFinitePresentation (r₂.restrict U).fY :=
      inferInstanceAs (LocallyOfFinitePresentation (U.ι ≫ r₂.fY))
    have : IsAffine (r₂.restrict U).Y := inferInstanceAs (IsAffine U)
    have hpre : r₁.g ⁻¹ᵁ h ⁻¹ᵁ U = a ⁻¹ᵁ r₂.g ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ha]
    let aU := a.resLE (r₂.g ⁻¹ᵁ U) (r₁.g ⁻¹ᵁ h ⁻¹ᵁ U) hpre.le
    have : IsClosedImmersion aU := by
      have e : aU = (Scheme.isoOfEq _ hpre).hom ≫ a ∣_ (r₂.g ⁻¹ᵁ U) := by
        rw [Scheme.isoOfEq_hom]
        rfl
      rw [e]
      infer_instance
    exact exists_isClosedImmersion_of_isAffine (r₁.restrict (h ⁻¹ᵁ U)) (r₂.restrict U) (h ∣_ U)
      _ hc aU (by
        simp only [Model.restrict, aU]
        rw [← cancel_mono U.ι]
        simp [morphismRestrict_ι, ha]) (by simp [aU, ha'])
  choose L hL using key
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (t.attach.image L)
  refine ⟨l, ?_⟩
  have hV : ∀ V : t, IsClosedImmersion
      (topBaseChange (r₁.restrict (h ⁻¹ᵁ V.1.1)) (r₂.restrict V.1.1) (h ∣_ V.1.1)
        (by simp [Model.restrict, morphismRestrict_ι_assoc, hh]) l) := by
    intro V
    obtain ⟨g⟩ := hl (Finset.mem_image_of_mem L (Finset.mem_attach t V))
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (isPullback_topBaseChange_map _ _ _ _ g) (hL V)
  -- the open cover of the level-`l` target by the base changes of the affine opens
  have hsqV := fun V : t => isPullback_baseChange_restrict r₂ V.1.1 l
  let ιV : ∀ V : t, pullback (V.1.1.ι ≫ r₂.fY) (D.map l.hom) ⟶
      (baseChangeDiagram D r₂.fY).obj l := fun V =>
    pullback.map (V.1.1.ι ≫ r₂.fY) (D.map l.hom) r₂.fY (D.map l.hom)
      V.1.1.ι (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp)
  have hιV : ∀ V : t, IsOpenImmersion (ιV V) := fun V =>
    Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  let 𝒰 : ((baseChangeDiagram D r₂.fY).obj l).OpenCover :=
    { I₀ := t
      X := fun V => pullback (V.1.1.ι ≫ r₂.fY) (D.map l.hom)
      f := ιV
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun z => ?_, hιV⟩
        obtain ⟨V, hVt, hzV⟩ := ht (pullback.fst r₂.fY (D.map l.hom) z)
        refine ⟨⟨V, hVt⟩, ?_⟩
        have hr : Set.range (ιV ⟨V, hVt⟩) = _ := range_eq_preimage_of_isPullback (hsqV ⟨V, hVt⟩)
        change z ∈ Set.range (ιV ⟨V, hVt⟩)
        rw [hr, Scheme.Opens.range_ι]
        exact hzV }
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun V => ?_
  have e1 : topBaseChange (r₁.restrict (h ⁻¹ᵁ V.1.1)) (r₂.restrict V.1.1) (h ∣_ V.1.1)
      (by simp [Model.restrict, morphismRestrict_ι_assoc, hh]) l ≫
        pullback.fst (V.1.1.ι ≫ r₂.fY) (D.map l.hom) =
      pullback.fst ((h ⁻¹ᵁ V.1.1).ι ≫ r₁.fY) (D.map l.hom) ≫ (h ∣_ V.1.1) :=
    topBaseChange_fst _ _ _ _ l
  have e2 : topBaseChange (r₁.restrict (h ⁻¹ᵁ V.1.1)) (r₂.restrict V.1.1) (h ∣_ V.1.1)
      (by simp [Model.restrict, morphismRestrict_ι_assoc, hh]) l ≫
        pullback.snd (V.1.1.ι ≫ r₂.fY) (D.map l.hom) =
      pullback.snd ((h ⁻¹ᵁ V.1.1).ι ≫ r₁.fY) (D.map l.hom) :=
    topBaseChange_snd _ _ _ _ l
  have hsq : IsPullback
      (pullback.map ((h ⁻¹ᵁ V.1.1).ι ≫ r₁.fY) (D.map l.hom) r₁.fY (D.map l.hom) (h ⁻¹ᵁ V.1.1).ι
        (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp))
      (topBaseChange (r₁.restrict (h ⁻¹ᵁ V.1.1)) (r₂.restrict V.1.1) (h ∣_ V.1.1)
        (by simp [Model.restrict, morphismRestrict_ι_assoc, hh]) l)
      (topBaseChange r₁ r₂ h hh l) (𝒰.f V) := by
    refine IsPullback.of_bot ?_ ?_ (hsqV V)
    · rw [e1, topBaseChange_fst]
      exact (isPullback_baseChange_restrict r₁ (h ⁻¹ᵁ V.1.1) l).paste_vert
        (isPullback_morphismRestrict h V.1.1).flip
    · apply pullback.hom_ext
      · simp only [𝒰, ιV, Category.assoc, topBaseChange_fst, pullback.lift_fst]
        rw [reassoc_of% e1, morphismRestrict_ι]
        simp
      · simp only [𝒰, ιV, Category.assoc, topBaseChange_snd, pullback.lift_snd]
        rw [reassoc_of% e2]
  have e : 𝒰.pullbackHom (topBaseChange r₁ r₂ h hh l) V = hsq.isoPullback.inv ≫
      topBaseChange (r₁.restrict (h ⁻¹ᵁ V.1.1)) (r₂.restrict V.1.1) (h ∣_ V.1.1)
        (by simp [Model.restrict, morphismRestrict_ι_assoc, hh]) l :=
    (Iso.eq_inv_comp _).2 hsq.isoPullback_hom_snd
  rw [e]
  have := hV V
  infer_instance

end ClosedImmersion

/-! ### Gluing models along an open -/

section Glue

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- A model is *of finite presentation* if its structure morphism is locally of finite
presentation, quasi-compact and quasi-separated. -/
def Model.IsFP {X : Scheme.{u}} {f : X ⟶ c.pt} {i : I} (m : Model D c f i) : Prop :=
  LocallyOfFinitePresentation m.fY ∧ QuasiCompact m.fY ∧ QuasiSeparated m.fY

variable {D c}

lemma Model.IsFP.baseChange {X : Scheme.{u}} {f : X ⟶ c.pt} {i : I} {m : Model D c f i}
    (hm : m.IsFP) {k : I} (h : k ⟶ i) : (m.baseChange h).IsFP := by
  obtain ⟨_, _, _⟩ := hm
  exact ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _)),
    inferInstanceAs (QuasiCompact (pullback.snd _ _)),
    inferInstanceAs (QuasiSeparated (pullback.snd _ _))⟩

/-- The image of `V ↪ U ↪ X` for an open `V = U ∩ W` of `U`. -/
lemma range_ι_comp_ι {X : Scheme.{u}} (U W : X.Opens) (V : U.toScheme.Opens)
    (hV : V = U.ι ⁻¹ᵁ W) : Set.range (V.ι ≫ U.ι) = (U : Set X) ∩ W := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, hV]
  change U.ι '' (U.ι ⁻¹' W) = _
  rw [Set.image_preimage_eq_range_inter, Scheme.Opens.range_ι]

variable [IsCofiltered I] [Quiver.IsThin I] (hc : IsLimit c)
  [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
  [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]

include hc in
/-- **Gluing of models** (the gluing step of EGA IV 8.8.2 (ii)). Let `X = X₁ ∪ X₂` be the union
of two opens with quasi-compact intersection, and suppose both opens have models of finite
presentation. Then `X` has a model of finite presentation. -/
theorem exists_model_of_sup {X : Scheme.{u}} (f : X ⟶ c.pt) (X₁ X₂ : X.Opens)
    (hX : ∀ x, x ∈ X₁ ∨ x ∈ X₂) (h₁₂ : IsCompact ((X₁ : Set X) ∩ X₂)) {i₁ i₂ : I}
    (m₁ : Model D c (X₁.ι ≫ f) i₁) (m₂ : Model D c (X₂.ι ≫ f) i₂) (hm₁ : m₁.IsFP)
    (hm₂ : m₂.IsFP) :
    ∃ (i : I) (m : Model D c f i), m.IsFP := by
  -- common level
  let n₁ := m₁.baseChange (IsCofiltered.minToLeft i₁ i₂)
  let n₂ := m₂.baseChange (IsCofiltered.minToRight i₁ i₂)
  obtain ⟨_, _, _⟩ := hm₁.baseChange (IsCofiltered.minToLeft i₁ i₂)
  obtain ⟨_, _, _⟩ := hm₂.baseChange (IsCofiltered.minToRight i₁ i₂)
  -- the intersection, as an open of each piece
  let W₁ : X₁.toScheme.Opens := X₁.ι ⁻¹ᵁ X₂
  let W₂ : X₂.toScheme.Opens := X₂.ι ⁻¹ᵁ X₁
  have hW₁ : IsCompact (W₁ : Set X₁.toScheme) := by
    have : (W₁ : Set X₁.toScheme) = X₁.ι ⁻¹' ((X₁ : Set X) ∩ X₂) := by
      ext x
      simp [W₁]
    rw [this, X₁.ι.isOpenEmbedding.isInducing.isCompact_preimage_iff
      (by rw [Scheme.Opens.range_ι]; exact Set.inter_subset_left)]
    exact h₁₂
  have hW₂ : IsCompact (W₂ : Set X₂.toScheme) := by
    have : (W₂ : Set X₂.toScheme) = X₂.ι ⁻¹' ((X₁ : Set X) ∩ X₂) := by
      ext x
      simp [W₂]
    rw [this, X₂.ι.isOpenEmbedding.isInducing.isCompact_preimage_iff
      (by rw [Scheme.Opens.range_ι]; exact Set.inter_subset_right)]
    exact h₁₂
  -- descend the two opens
  obtain ⟨j₁, V₁, hV₁c, hV₁⟩ := exists_preimage_eq (baseChangeDiagram D n₁.fY)
    (baseChangeCone D c n₁.isPullback) (isLimitBaseChangeCone D c hc n₁.isPullback) W₁ hW₁
  obtain ⟨j₂, V₂, hV₂c, hV₂⟩ := exists_preimage_eq (baseChangeDiagram D n₂.fY)
    (baseChangeCone D c n₂.isPullback) (isLimitBaseChangeCone D c hc n₂.isPullback) W₂ hW₂
  let j := IsCofiltered.min j₁ j₂
  let O₁ := (baseChangeDiagram D n₁.fY).map (IsCofiltered.minToLeft j₁ j₂) ⁻¹ᵁ V₁
  let O₂ := (baseChangeDiagram D n₂.fY).map (IsCofiltered.minToRight j₁ j₂) ⁻¹ᵁ V₂
  have hO₁ : (baseChangeCone D c n₁.isPullback).π.app j ⁻¹ᵁ O₁ = W₁ := by
    rw [← Scheme.Hom.comp_preimage, (baseChangeCone D c _).w]
    exact hV₁
  have hO₂ : (baseChangeCone D c n₂.isPullback).π.app j ⁻¹ᵁ O₂ = W₂ := by
    rw [← Scheme.Hom.comp_preimage, (baseChangeCone D c _).w]
    exact hV₂
  -- models at the level `k = j.left` and their restrictions to the descended opens
  let p₁ : Model D c (X₁.ι ≫ f) j.left := ⟨(baseChangeDiagram D n₁.fY).obj j, pullback.snd _ _,
    (baseChangeCone D c n₁.isPullback).π.app j, isPullback_baseChangeCone_π D c n₁.isPullback j⟩
  let p₂ : Model D c (X₂.ι ≫ f) j.left := ⟨(baseChangeDiagram D n₂.fY).obj j, pullback.snd _ _,
    (baseChangeCone D c n₂.isPullback).π.app j, isPullback_baseChangeCone_π D c n₂.isPullback j⟩
  have : QuasiSeparatedSpace p₁.Y := quasiSeparatedSpace_of_quasiSeparated p₁.fY
  have : QuasiSeparatedSpace p₂.Y := quasiSeparatedSpace_of_quasiSeparated p₂.fY
  have hO₁c : IsCompact (O₁ : Set p₁.Y) :=
    QuasiCompact.isCompact_preimage (f := (baseChangeDiagram D n₁.fY).map _) _ V₁.isOpen hV₁c
  have hO₂c : IsCompact (O₂ : Set p₂.Y) :=
    QuasiCompact.isCompact_preimage (f := (baseChangeDiagram D n₂.fY).map _) _ V₂.isOpen hV₂c
  have : CompactSpace O₁ := isCompact_iff_compactSpace.mp hO₁c
  have : CompactSpace O₂ := isCompact_iff_compactSpace.mp hO₂c
  let r₁ := p₁.restrict O₁
  let r₂ := p₂.restrict O₂
  have : LocallyOfFinitePresentation r₁.fY :=
    inferInstanceAs (LocallyOfFinitePresentation (O₁.ι ≫ p₁.fY))
  have : QuasiCompact r₁.fY := inferInstanceAs (QuasiCompact (O₁.ι ≫ p₁.fY))
  have : QuasiSeparated r₁.fY := inferInstanceAs (QuasiSeparated (O₁.ι ≫ p₁.fY))
  have : LocallyOfFinitePresentation r₂.fY :=
    inferInstanceAs (LocallyOfFinitePresentation (O₂.ι ≫ p₂.fY))
  have : QuasiCompact r₂.fY := inferInstanceAs (QuasiCompact (O₂.ι ≫ p₂.fY))
  have : QuasiSeparated r₂.fY := inferInstanceAs (QuasiSeparated (O₂.ι ≫ p₂.fY))
  -- the isomorphism between the two descriptions of `X₁ ∩ X₂`
  let E₁ := p₁.g ⁻¹ᵁ O₁
  let E₂ := p₂.g ⁻¹ᵁ O₂
  have hE₁ : Set.range (E₁.ι ≫ X₁.ι) = (X₁ : Set X) ∩ X₂ := range_ι_comp_ι X₁ X₂ E₁ hO₁
  have hE₂ : Set.range (E₂.ι ≫ X₂.ι) = (X₁ : Set X) ∩ X₂ := by
    rw [range_ι_comp_ι X₂ X₁ E₂ hO₂, Set.inter_comm]
  let θ : E₁.toScheme ⟶ E₂.toScheme :=
    IsOpenImmersion.lift (E₂.ι ≫ X₂.ι) (E₁.ι ≫ X₁.ι) (by rw [hE₁, hE₂])
  let θ' : E₂.toScheme ⟶ E₁.toScheme :=
    IsOpenImmersion.lift (E₁.ι ≫ X₁.ι) (E₂.ι ≫ X₂.ι) (by rw [hE₁, hE₂])
  have hθ : θ ≫ E₂.ι ≫ X₂.ι = E₁.ι ≫ X₁.ι := IsOpenImmersion.lift_fac _ _ _
  have hθ' : θ' ≫ E₁.ι ≫ X₁.ι = E₂.ι ≫ X₂.ι := IsOpenImmersion.lift_fac _ _ _
  let θiso : E₁.toScheme ≅ E₂.toScheme :=
    ⟨θ, θ', by rw [← cancel_mono (E₁.ι ≫ X₁.ι), Category.assoc, hθ', hθ, Category.id_comp],
      by rw [← cancel_mono (E₂.ι ≫ X₂.ι), Category.assoc, hθ, hθ', Category.id_comp]⟩
  obtain ⟨l, Θ, hΘs, hΘπ⟩ := exists_iso_of_iso D c hc r₁ r₂ θiso ((reassoc_of% hθ) f)
  -- the span at level `l`
  let ιC : (baseChangeDiagram D r₁.fY).obj l ⟶ pullback p₁.fY (D.map l.hom) :=
    pullback.map r₁.fY (D.map l.hom) p₁.fY (D.map l.hom) O₁.ι (𝟙 _) (𝟙 _)
      (Category.comp_id _) (by simp)
  let ιC' : (baseChangeDiagram D r₂.fY).obj l ⟶ pullback p₂.fY (D.map l.hom) :=
    pullback.map r₂.fY (D.map l.hom) p₂.fY (D.map l.hom) O₂.ι (𝟙 _) (𝟙 _)
      (Category.comp_id _) (by simp)
  let legR := Θ.hom ≫ ιC'
  have hιC : ιC ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [ιC]
  have hιC' : ιC' ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [ιC']
  have hlegR : legR ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [Category.assoc, hιC', hΘs]
  let Z := pushout ιC legR
  let fZ : Z ⟶ D.obj l.left := pushout.desc (pullback.snd _ _) (pullback.snd _ _)
    (by rw [hιC, hlegR])
  have hinlZ : pushout.inl ιC legR ≫ fZ = pullback.snd _ _ := pushout.inl_desc _ _ _
  have hinrZ : pushout.inr ιC legR ≫ fZ = pullback.snd _ _ := pushout.inr_desc _ _ _
  -- the model maps at level `l`
  let gA := (baseChangeCone D c p₁.isPullback).π.app l
  let gB := (baseChangeCone D c p₂.isPullback).π.app l
  let gC := (baseChangeCone D c r₁.isPullback).π.app l
  let gC' := (baseChangeCone D c r₂.isPullback).π.app l
  have R₁ : gC ≫ ιC = E₁.ι ≫ gA := by
    apply pullback.hom_ext
    · simp [gC, gA, ιC, r₁, E₁]
    · simp [gC, gA, ιC, r₁, E₁]
  have R₃ : gC' ≫ ιC' = E₂.ι ≫ gB := by
    apply pullback.hom_ext
    · simp [gC', gB, ιC', r₂, E₂]
    · simp [gC', gB, ιC', r₂, E₂]
  -- the limit `X` is the pushout of `X₁ ⊇ X₁ ∩ X₂ ⊆ X₂`
  have hwX : E₁.ι ≫ X₁.ι = (θ ≫ E₂.ι) ≫ X₂.ι := by rw [Category.assoc, hθ]
  have hXpush : IsPushout E₁.ι (θ ≫ E₂.ι) X₁.ι X₂.ι := by
    refine isPushout_of_isOpenImmersion _ _ _ _ hwX (fun z => ?_) (fun z h₁ h₂ => ?_)
    · rcases hX z with h | h
      · exact Or.inl (by rwa [Scheme.Opens.range_ι])
      · exact Or.inr (by rwa [Scheme.Opens.range_ι])
    · rw [Scheme.Opens.range_ι] at h₁ h₂
      rw [hE₁]
      exact ⟨h₁, h₂⟩
  -- the base change `P = Z ×_{D l} lim D` is the pushout of the base changes
  let P := pullback fZ (c.π.app l.left)
  have hA := isPullback_lift_comp (isPullback_baseChangeCone_π D c p₁.isPullback l)
    (pushout.inl ιC legR) fZ hinlZ
  have hB := isPullback_lift_comp (isPullback_baseChangeCone_π D c p₂.isPullback l)
    (pushout.inr ιC legR) fZ hinrZ
  have hC := isPullback_lift_comp (isPullback_baseChangeCone_π D c r₁.isPullback l)
    (ιC ≫ pushout.inl ιC legR) fZ (by rw [Category.assoc, hinlZ, hιC])
  let inl' : X₁.toScheme ⟶ P := pullback.lift (gA ≫ pushout.inl ιC legR) (X₁.ι ≫ f)
    (by rw [Category.assoc, hinlZ, (isPullback_baseChangeCone_π D c p₁.isPullback l).w])
  let inr' : X₂.toScheme ⟶ P := pullback.lift (gB ≫ pushout.inr ιC legR) (X₂.ι ≫ f)
    (by rw [Category.assoc, hinrZ, (isPullback_baseChangeCone_π D c p₂.isPullback l).w])
  have : IsOpenImmersion inl' :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hA.flip inferInstance
  have : IsOpenImmersion inr' :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hB.flip inferInstance
  have hcenter : E₁.ι ≫ inl' = pullback.lift (gC ≫ ιC ≫ pushout.inl ιC legR)
      ((E₁.ι ≫ X₁.ι) ≫ f) (by rw [Category.assoc, Category.assoc, hinlZ, hιC,
        (isPullback_baseChangeCone_π D c r₁.isPullback l).w]; rfl) := by
    apply pullback.hom_ext
    · simp [inl', reassoc_of% R₁]
    · simp [inl']
  have hwP : E₁.ι ≫ inl' = (θ ≫ E₂.ι) ≫ inr' := by
    apply pullback.hom_ext
    · simp only [Category.assoc, inl', inr', pullback.lift_fst]
      rw [← reassoc_of% R₁, ← reassoc_of% R₃, ← reassoc_of% hΘπ, pushout.condition]
      rfl
    · simp only [Category.assoc, inl', inr', pullback.lift_snd]
      rw [reassoc_of% hθ]
  have hZcov := mem_range_inl_or_inr ιC legR
  have hrA : Set.range inl' = pullback.fst fZ (c.π.app l.left) ⁻¹'
      Set.range (pushout.inl ιC legR) := range_eq_preimage_of_isPullback hA
  have hrB : Set.range inr' = pullback.fst fZ (c.π.app l.left) ⁻¹'
      Set.range (pushout.inr ιC legR) := range_eq_preimage_of_isPullback hB
  have hrC : Set.range (E₁.ι ≫ inl') = pullback.fst fZ (c.π.app l.left) ⁻¹'
      Set.range (ιC ≫ pushout.inl ιC legR) := by
    rw [hcenter]
    exact range_eq_preimage_of_isPullback hC
  have hPpush : IsPushout E₁.ι (θ ≫ E₂.ι) inl' inr' := by
    refine isPushout_of_isOpenImmersion _ _ _ _ hwP (fun z => ?_) (fun z h₁ h₂ => ?_)
    · rw [hrA, hrB]
      exact hZcov _
    · rw [hrA] at h₁
      rw [hrB] at h₂
      rw [hrC]
      exact mem_range_of_pushout ιC legR _ h₁ h₂
  -- the comparison isomorphism `X ≅ P`
  let e := IsPushout.isoIsPushout _ _ hXpush hPpush
  have hes : e.hom ≫ pullback.snd fZ (c.π.app l.left) = f := by
    refine hXpush.hom_ext ?_ ?_
    · rw [IsPushout.inl_isoIsPushout_hom_assoc]
      simp [inl']
    · rw [IsPushout.inr_isoIsPushout_hom_assoc]
      simp [inr']
  have hpb : IsPullback (e.hom ≫ pullback.fst fZ (c.π.app l.left)) f fZ (c.π.app l.left) := by
    refine (IsPullback.of_hasPullback fZ (c.π.app l.left)).of_iso e.symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [← hes]
    · simp
    · simp
  -- finiteness properties of the glued scheme
  have : CompactSpace ↥(pullback p₁.fY (D.map l.hom) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p₁.fY (D.map l.hom))
  have : CompactSpace ↥(pullback p₂.fY (D.map l.hom) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p₂.fY (D.map l.hom))
  have : CompactSpace ((baseChangeDiagram D r₁.fY).obj l) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd r₁.fY (D.map l.hom))
  have : QuasiSeparatedSpace ↥(pullback p₁.fY (D.map l.hom) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p₁.fY (D.map l.hom))
  have : QuasiSeparatedSpace ↥(pullback p₂.fY (D.map l.hom) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p₂.fY (D.map l.hom))
  have hZuniv : (Set.univ : Set Z) =
      Set.range (pushout.inl ιC legR) ∪ Set.range (pushout.inr ιC legR) := by
    ext z
    simpa using hZcov z
  have : CompactSpace Z := ⟨by
    rw [hZuniv]
    exact (isCompact_range (pushout.inl ιC legR).continuous).union
      (isCompact_range (pushout.inr ιC legR).continuous)⟩
  have hinter := range_inl_inter_range_inr ιC legR
  have : QuasiSeparatedSpace Z := by
    refine quasiSeparatedSpace_of_sup (pushout.inl ιC legR).opensRange
      (pushout.inr ιC legR).opensRange (fun z => ?_) ?_ ?_ ?_
    · simpa using hZcov z
    · rw [Scheme.Hom.coe_opensRange, ← Set.image_univ]
      exact (pushout.inl ιC legR).isOpenEmbedding.isQuasiSeparated_iff.mp isQuasiSeparated_univ
    · rw [Scheme.Hom.coe_opensRange, ← Set.image_univ]
      exact (pushout.inr ιC legR).isOpenEmbedding.isQuasiSeparated_iff.mp isQuasiSeparated_univ
    · rw [Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange, hinter]
      exact isCompact_range (ιC ≫ pushout.inl ιC legR).continuous
  refine ⟨l.left, ⟨Z, fZ, e.hom ≫ pullback.fst _ _, hpb⟩, ?_, inferInstance, inferInstance⟩
  change LocallyOfFinitePresentation fZ
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation)
    (Scheme.IsLocallyDirected.openCover (span ιC legR))]
  rintro (_ | _ | _)
  · change LocallyOfFinitePresentation (colimit.ι (span ιC legR) WalkingSpan.zero ≫ fZ)
    rw [← colimit.w (span ιC legR) WalkingSpan.Hom.fst, Category.assoc]
    change LocallyOfFinitePresentation (ιC ≫ pushout.inl ιC legR ≫ fZ)
    rw [hinlZ, hιC]
    infer_instance
  · change LocallyOfFinitePresentation (pushout.inl ιC legR ≫ fZ)
    rw [hinlZ]
    infer_instance
  · change LocallyOfFinitePresentation (pushout.inr ιC legR ≫ fZ)
    rw [hinrZ]
    infer_instance

end Glue

/-! ### Descent of schemes of finite presentation -/

section Objects

variable {I : Type u} [Category.{u} I] [IsCofiltered I] [Quiver.IsThin I] {D : I ⥤ Scheme.{u}}
  {c : Cone D} (hc : IsLimit c) [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
  [∀ j, IsAffine (D.obj j)]

omit [Quiver.IsThin I] in
include hc in
/-- An affine scheme locally of finite presentation over `lim D` has a model of finite
presentation. -/
lemma exists_model_of_isAffine {X : Scheme.{u}} [IsAffine X] (f : X ⟶ c.pt)
    [LocallyOfFinitePresentation f] : ∃ (i : I) (m : Model D c f i), m.IsFP := by
  obtain ⟨i, Y, fY, g, hY, hfY, h⟩ := exists_isPullback_of_isAffine D c hc f
  exact ⟨i, ⟨Y, fY, g, h⟩, hfY, inferInstance, inferInstance⟩

include hc in
private lemma exists_model_of_card_le (n : ℕ) : ∀ {X : Scheme.{u}} (f : X ⟶ c.pt)
    [LocallyOfFinitePresentation f] [QuasiSeparatedSpace X] (s : Finset X.affineOpens),
    s.card ≤ n → (∀ x : X, ∃ U ∈ s, x ∈ (U : X.Opens)) →
      ∃ (i : I) (m : Model D c f i), m.IsFP := by
  induction n with
  | zero =>
    intro X f _ _ s hs hcov
    have : IsEmpty X := ⟨fun x => by
      obtain ⟨U, hU, -⟩ := hcov x
      simp_all⟩
    exact exists_model_of_isAffine hc f
  | succ n ih =>
    intro X f _ _ s hs hcov
    rcases s.eq_empty_or_nonempty with rfl | ⟨U, hU⟩
    · have : IsEmpty X := ⟨fun x => by
        obtain ⟨U, hU, -⟩ := hcov x
        simp at hU⟩
      exact exists_model_of_isAffine hc f
    classical
    let s' := s.erase U
    let X₁ : X.Opens := ⨆ V ∈ s', (V : X.Opens)
    let X₂ : X.Opens := U
    -- the first piece is covered by fewer affine opens
    have hV : ∀ V ∈ s', IsAffineOpen (X₁.ι ⁻¹ᵁ (V : X.Opens)) := fun V hV' =>
      V.2.preimage_of_isOpenImmersion X₁.ι (by
        rw [Scheme.Opens.opensRange_ι]
        exact le_biSup (fun V : X.affineOpens => (V : X.Opens)) hV')
    let s₁ : Finset X₁.toScheme.affineOpens :=
      s'.attach.image fun V : {V // V ∈ s'} =>
        (⟨X₁.ι ⁻¹ᵁ (V.1 : X.Opens), hV V.1 V.2⟩ : X₁.toScheme.affineOpens)
    have hs₁ : s₁.card ≤ n := by
      refine (Finset.card_image_le).trans ?_
      rw [Finset.card_attach, Finset.card_erase_of_mem hU]
      omega
    have hcov₁ : ∀ x : X₁.toScheme, ∃ V ∈ s₁, x ∈ (V : X₁.toScheme.Opens) := by
      intro x
      have hx : X₁.ι x ∈ (X₁ : Set X) := by
        rw [← Scheme.Opens.range_ι X₁]
        exact ⟨x, rfl⟩
      obtain ⟨V, hV', hxV⟩ : ∃ V ∈ s', X₁.ι x ∈ (V : X.Opens) := by
        simpa [X₁, TopologicalSpace.Opens.mem_iSup] using hx
      exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨V, hV'⟩), hxV⟩
    have : QuasiSeparatedSpace X₁.toScheme := X₁.ι.isOpenEmbedding.quasiSeparatedSpace
    obtain ⟨i₁, m₁, hm₁⟩ := ih (X₁.ι ≫ f) s₁ hs₁ hcov₁
    -- the second piece is affine
    have : IsAffine X₂.toScheme := U.2
    obtain ⟨i₂, m₂, hm₂⟩ := exists_model_of_isAffine hc (X₂.ι ≫ f)
    -- glue
    have hX : ∀ x, x ∈ X₁ ∨ x ∈ X₂ := by
      intro x
      obtain ⟨V, hV', hxV⟩ := hcov x
      by_cases hVU : V = U
      · subst hVU
        exact Or.inr hxV
      · left
        simp only [X₁, TopologicalSpace.Opens.mem_iSup]
        exact ⟨V, Finset.mem_erase.2 ⟨hVU, hV'⟩, hxV⟩
    have hX₁c : IsCompact (X₁ : Set X) := by
      simp only [X₁, TopologicalSpace.Opens.coe_iSup]
      exact s'.isCompact_biUnion fun V _ => V.2.isCompact
    have h₁₂ : IsCompact ((X₁ : Set X) ∩ X₂) :=
      QuasiSeparatedSpace.inter_isCompact _ _ X₁.isOpen hX₁c X₂.isOpen U.2.isCompact
    exact exists_model_of_sup hc f X₁ X₂ hX h₁₂ m₁ m₂ hm₁ hm₂

include hc in
/-- **Descent of schemes of finite presentation** (EGA IV 8.8.2 (ii); Stacks 01ZM). Let `D` be a
cofiltered diagram of affine schemes with affine transition maps, indexed by a cofiltered
preorder, with limit `lim D`. Every scheme of finite presentation over `lim D` is the base change
of a scheme of finite presentation over some `D i`. -/
theorem exists_model {X : Scheme.{u}} (f : X ⟶ c.pt) [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] : ∃ (i : I) (m : Model D c f i), m.IsFP := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨s, hs⟩ := RiemannZariskiSpace.exists_finite_affine_cover (S := X)
  exact exists_model_of_card_le hc s.card f s le_rfl hs

include hc in
/-- **Descent of closed subschemes.** Let `r` be a model of finite presentation of `X → lim D`
at level `k`, and let `Z ⊆ X` be a closed subscheme of finite presentation over `lim D`. Then for
some `l → k` there is a model of finite presentation of `Z` at level `l` which is a closed
subscheme of the base change of `r` to `l`, compatibly with the inclusion `Z ⊆ X`. -/
theorem exists_closedImmersion_model {k : I} {X : Scheme.{u}} {fX : X ⟶ c.pt}
    (r : Model D c fX k) (hr : r.IsFP) {Z : Scheme.{u}} (fZ : Z ⟶ c.pt)
    [LocallyOfFinitePresentation fZ] [QuasiCompact fZ] [QuasiSeparated fZ] (a : Z ⟶ X)
    [IsClosedImmersion a] (ha : a ≫ fX = fZ) :
    ∃ (l : I) (g : l ⟶ k) (m : Model D c fZ l) (ι : m.Y ⟶ (r.baseChange g).Y),
      m.IsFP ∧ IsClosedImmersion ι ∧ ι ≫ (r.baseChange g).fY = m.fY ∧
        m.g ≫ ι = a ≫ (r.baseChange g).g := by
  obtain ⟨i, m₀, hm₀⟩ := exists_model hc fZ
  let j := IsCofiltered.min k i
  let gk : j ⟶ k := IsCofiltered.minToLeft k i
  let gi : j ⟶ i := IsCofiltered.minToRight k i
  let r₁ := m₀.baseChange gi
  let r₂ := r.baseChange gk
  obtain ⟨_, _, _⟩ := hm₀.baseChange gi
  obtain ⟨_, _, _⟩ := hr.baseChange gk
  obtain ⟨l₁, b, hb, hb'⟩ := exists_hom_of_isPullback D c hc r₁.fY r₂.fY r₁.isPullback
    (a ≫ r₂.g) (by rw [Category.assoc, r₂.isPullback.w, reassoc_of% ha, r₁.isPullback.w])
  let s₁ := r₁.baseChange l₁.hom
  let s₂ := r₂.baseChange l₁.hom
  obtain ⟨_, _, _⟩ := (hm₀.baseChange gi).baseChange l₁.hom
  obtain ⟨_, _, _⟩ := (hr.baseChange gk).baseChange l₁.hom
  let h : s₁.Y ⟶ s₂.Y := pullback.lift b (pullback.snd _ _) (by
    rw [hb, pullback.condition])
  have hh : h ≫ s₂.fY = s₁.fY := pullback.lift_snd _ _ _
  have hgh : s₁.g ≫ h = a ≫ s₂.g := by
    apply pullback.hom_ext
    · simp only [Category.assoc, h, pullback.lift_fst]
      exact hb'.trans (by simp [s₂, Model.baseChange])
    · simp [h, s₁, s₂, Model.baseChange, reassoc_of% ha]
  obtain ⟨l₂, hl₂⟩ := exists_isClosedImmersion s₁ s₂ h hh hc a hgh ha
  let e := r.baseChangeCompIso gk l₁.hom
  let e' := r.baseChangeCompIso (l₁.hom ≫ gk) l₂.hom
  have hm := (hm₀.baseChange gi).baseChange l₁.hom |>.baseChange l₂.hom
  refine ⟨l₂.left, l₂.hom ≫ l₁.hom ≫ gk, s₁.baseChange l₂.hom,
    topBaseChange s₁ s₂ h hh l₂ ≫
      pullback.map s₂.fY (D.map l₂.hom) (r.baseChange (l₁.hom ≫ gk)).fY (D.map l₂.hom) e.hom
        (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Model.baseChangeCompIso_hom_fY]) (by simp) ≫
        e'.hom,
    hm, inferInstance, ?_, ?_⟩
  · simp only [Category.assoc, e', Model.baseChangeCompIso_hom_fY]
    simp [Model.baseChange]
  · have step1 : (s₁.baseChange l₂.hom).g ≫ topBaseChange s₁ s₂ h hh l₂ =
        a ≫ (s₂.baseChange l₂.hom).g := π_topBaseChange s₁ s₂ h hh a hgh ha l₂
    have step2 : (s₂.baseChange l₂.hom).g ≫
        pullback.map s₂.fY (D.map l₂.hom) (r.baseChange (l₁.hom ≫ gk)).fY (D.map l₂.hom) e.hom
          (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Model.baseChangeCompIso_hom_fY]) (by simp) =
        ((r.baseChange (l₁.hom ≫ gk)).baseChange l₂.hom).g := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst]
        erw [pullback.lift_fst_assoc, pullback.lift_fst]
        exact r.g_baseChangeCompIso_hom gk l₁.hom
      · simp [Model.baseChange]
    rw [reassoc_of% step1, reassoc_of% step2, Model.g_baseChangeCompIso_hom]

end Objects

/-! ### Descent of separatedness -/

section Separated

/-- The comparison `Y_l ×_{D_l} Y_l → (Y ×_{D_k} Y) ×_{D_k} D_l` for a base change
`Y_l = Y ×_{D_k} D_l`. -/
noncomputable def diagonalObjBaseChangeHom {Y S T : Scheme.{u}} (fY : Y ⟶ S) (g : T ⟶ S) :
    pullback (pullback.snd fY g) (pullback.snd fY g) ⟶
      pullback (pullback.fst fY fY ≫ fY) g :=
  pullback.lift
    (pullback.map _ _ _ _ (pullback.fst fY g) (pullback.fst fY g) g pullback.condition.symm
      pullback.condition.symm)
    (pullback.fst _ _ ≫ pullback.snd _ _)
    (by simp [pullback.condition])

/-- The inverse of `diagonalObjBaseChangeHom`. -/
noncomputable def diagonalObjBaseChangeInv {Y S T : Scheme.{u}} (fY : Y ⟶ S) (g : T ⟶ S) :
    pullback (pullback.fst fY fY ≫ fY) g ⟶
      pullback (pullback.snd fY g) (pullback.snd fY g) :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition))
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
      (by rw [Category.assoc, ← pullback.condition (f := fY) (g := fY)]
          exact pullback.condition))
    (by simp)

instance {Y S T : Scheme.{u}} (fY : Y ⟶ S) (g : T ⟶ S) :
    IsIso (diagonalObjBaseChangeHom fY g) :=
  ⟨diagonalObjBaseChangeInv fY g, by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [diagonalObjBaseChangeHom, diagonalObjBaseChangeInv]
    exact pullback.condition,
    by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [diagonalObjBaseChangeHom, diagonalObjBaseChangeInv]
    · simp [diagonalObjBaseChangeHom, diagonalObjBaseChangeInv]⟩

lemma diagonal_comp_diagonalObjBaseChangeHom {Y S T : Scheme.{u}} (fY : Y ⟶ S) (g : T ⟶ S) :
    pullback.diagonal (pullback.snd fY g) ≫ diagonalObjBaseChangeHom fY g =
      pullback.map fY g (pullback.fst fY fY ≫ fY) g (pullback.diagonal fY) (𝟙 _) (𝟙 _)
        (by simp) (by simp) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [diagonalObjBaseChangeHom]
  · simp [diagonalObjBaseChangeHom]

/-- A base change `Y ×_S T → T` is separated as soon as the base change of the diagonal of
`Y → S` along `(Y ×_S Y) ×_S T → Y ×_S Y` is a closed immersion. -/
lemma isSeparated_snd_of_isClosedImmersion {Y S T : Scheme.{u}} (fY : Y ⟶ S) (g : T ⟶ S)
    (h : IsClosedImmersion (pullback.map fY g (pullback.fst fY fY ≫ fY) g (pullback.diagonal fY)
      (𝟙 _) (𝟙 _) (by simp) (by simp))) :
    IsSeparated (pullback.snd fY g) := by
  rw [isSeparated_iff, ← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (diagonalObjBaseChangeHom fY g), diagonal_comp_diagonalObjBaseChangeHom]
  exact h

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

/-- The model `Y ×_{D k} Y` of `X ×_{lim D} X` given by a model `Y` of `X`. -/
noncomputable def Model.pullbackSelf {X : Scheme.{u}} {f : X ⟶ c.pt} {k : I}
    (r : Model D c f k) : Model D c (pullback.fst f f ≫ f) k where
  Y := pullback r.fY r.fY
  fY := pullback.fst _ _ ≫ r.fY
  g := pullback.map f f r.fY r.fY r.g r.g (c.π.app k) r.isPullback.w.symm r.isPullback.w.symm
  isPullback := by
    have h1 : IsPullback (pullback.map f f r.fY r.fY r.g r.g (c.π.app k) r.isPullback.w.symm
        r.isPullback.w.symm ≫ pullback.snd _ _) (pullback.fst f f) r.fY (r.g ≫ r.fY) := by
      rw [pullback.lift_snd, r.isPullback.w]
      exact (IsPullback.of_hasPullback f f).flip.paste_horiz r.isPullback
    exact (IsPullback.of_right h1 (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback r.fY r.fY).flip).paste_vert r.isPullback

lemma Model.IsFP.pullbackSelf {X : Scheme.{u}} {f : X ⟶ c.pt} {k : I} {r : Model D c f k}
    (hr : r.IsFP) : r.pullbackSelf.IsFP := by
  obtain ⟨_, _, _⟩ := hr
  exact ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.fst r.fY r.fY ≫ r.fY)),
    inferInstanceAs (QuasiCompact (pullback.fst r.fY r.fY ≫ r.fY)),
    inferInstanceAs (QuasiSeparated (pullback.fst r.fY r.fY ≫ r.fY))⟩

variable [IsCofiltered I] [Quiver.IsThin I] (hc : IsLimit c)
  [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
  [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]

include hc in
/-- **Descent of separatedness** (EGA IV 8.10.5 (v)). If `X → lim D` is separated and `r` is a
model of finite presentation of `X` at level `k`, then the base change of `r` to some level
`l → k` is separated over `D l`. -/
theorem exists_isSeparated {X : Scheme.{u}} {f : X ⟶ c.pt} [IsSeparated f] {k : I}
    (r : Model D c f k) (hr : r.IsFP) :
    ∃ (l : I) (g : l ⟶ k), IsSeparated (r.baseChange g).fY := by
  have h₂ := hr.pullbackSelf
  obtain ⟨_, _, _⟩ := hr
  obtain ⟨_, _, _⟩ := h₂
  obtain ⟨l, hl⟩ := exists_isClosedImmersion r r.pullbackSelf (pullback.diagonal r.fY)
    (by simp [Model.pullbackSelf]) hc (pullback.diagonal f)
    (by apply pullback.hom_ext <;> simp [Model.pullbackSelf]) (by simp)
  exact ⟨l.left, l.hom, isSeparated_snd_of_isClosedImmersion r.fY (D.map l.hom) hl⟩

end Separated

/-! ### The approximating system of a valuation ring -/

section QASystem

variable {A L : Type u} [CommRing A] [CommRing L] [Algebra A L] (R : Subalgebra A L)

instance : Quiver.IsThin (FGSubalgebra A R)ᵒᵖ := fun _ _ =>
  ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

/-- **Descent of schemes along the system of finitely generated subalgebras.** Every scheme of
finite presentation over `Spec R` is the base change of a scheme of finite presentation over
`Spec B` for a finitely generated `A`-subalgebra `B ⊆ R`. For `R` a valuation ring `V` of
`L = K^s` containing `A = Γ(S, U)`, the `Spec B` are affine quasi-alterations of `S` containing
the center of `V` (`Limits.fgSpecCone_π_app_comp_fromSpec`). -/
theorem exists_model_fgSubalgebra {X : Scheme.{u}} (f : X ⟶ (fgSpecCone R).pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (B : (FGSubalgebra A R)ᵒᵖ) (m : Model _ (fgSpecCone R) f B), m.IsFP :=
  exists_model (isLimitFGSpecCone R) f

end QASystem

end DeJongAlterations.StableModification.Limits
