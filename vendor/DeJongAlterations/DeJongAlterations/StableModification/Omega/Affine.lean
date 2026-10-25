import DeJongAlterations.StableModification.Omega.Basic
import DeJongAlterations.StableModification.Omega.SpecDerivation

/-!
# `Ω¹_{X/S}` on affine opens

Let `f : X ⟶ S`, let `V ⊆ S` and `W ⊆ X` be affine opens with `W ≤ f⁻¹ V`, and write
`A = Γ(X, W)`, `R = Γ(S, V)` (an `R`-algebra through `f.appLE`). This file identifies the sections
of `Ω¹_{X/S}` over `W` with the Kähler differentials `Ω_{A/R}`.

* `exists_eq_of_mem_baseSubring`: a section in the base subring is, near every point, a fraction
  `r / g` of pullbacks of sections `r, g ∈ R` with `g` invertible there.
* `PreDerivation`, `PreDerivation.d_eq_zero_of_mem_baseSubring`: a family of derivations
  `Γ(X, U) → Γ(N, U)` (`U ≤ W`) which kills the pullbacks of `R` kills the base subrings.
* `affineDerivation`: the relative derivation `𝒪_X → ι_* (Ω_{A/R})^~` (`ι = hW.fromSpec`)
  given pointwise by `specDerivation`.
* `sectionsLinearMap`: the `A`-linear map `Ω_{A/R} → Γ(Ω¹_{X/S}, W)`, `da ↦ d a`;
  `sectionsLinearMap_bijective`: it is bijective (blueprint `prop:sm-omega-affine`). Injectivity
  comes from `affineDerivation`; surjectivity from the locality of derivations
  (`RelDerivation.ext_of_le_affine`) through the adjunctions
  `restrictFunctor ι ⊣ pushforward ι` and `tilde ⊣ Γ`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Omega

variable {X S : Scheme.{u}} {f : X ⟶ S}

section BaseFraction

/-- Near every point, a section in the base subring is a fraction `r / g` of pullbacks of
sections over an affine open `V` of `S`, with `g` invertible there. -/
theorem exists_eq_of_mem_baseSubring {V : S.Opens} (hV : IsAffineOpen V) {U : X.Opens}
    (hU : U ≤ f ⁻¹ᵁ V) {t : Γ(X, U)} (ht : t ∈ baseSubring f U) (x : X) (hx : x ∈ U) :
    ∃ (r g : Γ(S, V)) (U' : X.Opens) (hU' : U' ≤ U), x ∈ U' ∧
      U' ≤ X.basicOpen (f.appLE V U hU g) ∧
      X.presheaf.map (homOfLE hU').op (t * f.appLE V U hU g) =
        X.presheaf.map (homOfLE hU').op (f.appLE V U hU r) := by
  obtain ⟨σ, hσ⟩ := ht x hx
  let := S.presheaf.algebra_section_stalk ⟨f x, hU hx⟩
  have := hV.isLocalization_stalk ⟨f x, hU hx⟩
  obtain ⟨⟨r, g⟩, h⟩ := IsLocalization.surj (hV.primeIdealOf ⟨f x, hU hx⟩).asIdeal.primeCompl σ
  have hunit : IsUnit (algebraMap Γ(S, V) (S.presheaf.stalk (f x)) g) :=
    IsLocalization.map_units _ g
  have hgerm : ∀ b : Γ(S, V), f.stalkMap x (algebraMap Γ(S, V) (S.presheaf.stalk (f x)) b) =
      X.presheaf.germ U x hx (f.appLE V U hU b) := by
    intro b
    have h1 := Scheme.Hom.germ_stalkMap_apply f V x (hU hx) b
    change f.stalkMap x (S.presheaf.germ V (f x) (hU hx) b) = _
    rw [h1, Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  have e := congrArg (f.stalkMap x) h
  simp only [map_mul, hσ, hgerm] at e
  rw [← map_mul] at e
  obtain ⟨U'', hxU'', iU, iV, heq⟩ := X.presheaf.germ_eq x hx hx _ _ e
  have hxg : x ∈ X.basicOpen (f.appLE V U hU g) := by
    rw [Scheme.mem_basicOpen X _ x hx, ← hgerm]
    exact hunit.map _
  refine ⟨r, g, U'' ⊓ X.basicOpen (f.appLE V U hU g), inf_le_left.trans iU.le, ⟨hxU'', hxg⟩,
    inf_le_right, ?_⟩
  have h1 : homOfLE (inf_le_left.trans iU.le : U'' ⊓ X.basicOpen (f.appLE V U hU g) ≤ U) =
      homOfLE inf_le_left ≫ iU := rfl
  rw [h1, op_comp, Functor.map_comp, CommRingCat.comp_apply, CommRingCat.comp_apply, heq,
    Subsingleton.elim iV iU]

end BaseFraction

section PreDerivation

/-- A section restricted to an open contained in its basic open is a unit. -/
theorem isUnit_map_of_le_basicOpen {U U' : X.Opens} (s : Γ(X, U)) (h : U' ≤ X.basicOpen s)
    (hU : U' ≤ U) : IsUnit (X.presheaf.map (homOfLE hU).op s) := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply]
  exact (X.mem_basicOpen s x (hU hx)).mp (h hx)

/-- A family of derivations `Γ(X, U) → Γ(N, U)` compatible with restrictions (no condition on
the base). -/
structure PreDerivation (N : X.Modules) where
  /-- The additive maps. -/
  d : ∀ (U : X.Opens), Γ(X, U) →+ Γ(N, U)
  d_mul : ∀ (U : X.Opens) (s t : Γ(X, U)), d U (s * t) = s • d U t + t • d U s
  d_map : ∀ {U U' : X.Opens} (i : U' ⟶ U) (s : Γ(X, U)),
    d U' (X.presheaf.map i.op s) = N.presheaf.map i.op (d U s)

namespace PreDerivation

variable {N : X.Modules} (D : PreDerivation N)

/-- A pre-derivation which kills the pullbacks of the sections over an affine open `V` kills the
base subrings over every open `U ≤ f⁻¹ V`. -/
theorem d_eq_zero_of_mem_baseSubring {V : S.Opens} (hV : IsAffineOpen V)
    {U : X.Opens} (hU : U ≤ f ⁻¹ᵁ V)
    (hD : ∀ (U' : X.Opens) (hU' : U' ≤ U) (r : Γ(S, V)),
      D.d U' (f.appLE V U' (hU'.trans hU) r) = 0)
    {t : Γ(X, U)} (ht : t ∈ baseSubring f U) :
    D.d U t = 0 := by
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  choose r g U' hU' hxU' hU'g heq using
    fun x : U => exists_eq_of_mem_baseSubring hV hU ht x.1 x.2
  refine F.eq_of_locally_eq' U' U (fun x => homOfLE (hU' x)) ?_ (D.d U t) 0 ?_
  · intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU' ⟨x, hx⟩⟩
  · intro x
    change N.presheaf.map (homOfLE (hU' x)).op (D.d U t) = N.presheaf.map (homOfLE (hU' x)).op 0
    rw [map_zero, ← D.d_map]
    set i := homOfLE (hU' x)
    set G := X.presheaf.map i.op (f.appLE V U hU (g x))
    have hG : IsUnit G := isUnit_map_of_le_basicOpen _ (hU'g x) _
    have hres : ∀ b : Γ(S, V), X.presheaf.map i.op (f.appLE V U hU b) =
        f.appLE V (U' x) ((hU' x).trans hU) b := by
      intro b
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    have key := congrArg (D.d (U' x)) (heq x)
    rw [map_mul, D.d_mul, hres, hres, hD _ (hU' x), hD _ (hU' x), smul_zero, zero_add] at key
    rw [← hres] at key
    exact (hG.smul_left_cancel).mp (key.trans (smul_zero _).symm)

/-- A pre-derivation which kills the base subrings is a relative derivation. -/
def toRelDerivation (hD : ∀ (U : X.Opens) (t : Γ(X, U)), t ∈ baseSubring f U → D.d U t = 0) :
    RelDerivation f N :=
  { d := fun {U} => D.d U.unop
    d_mul := fun {U} s t => D.d_mul U.unop s t
    d_map := fun i s => D.d_map i.unop s
    d_app := fun {U} t => hD U.unop t.1 t.2 }

@[simp]
theorem toRelDerivation_d
    (hD : ∀ (U : X.Opens) (t : Γ(X, U)), t ∈ baseSubring f U → D.d U t = 0) {U : X.Opens}
    (s : Γ(X, U)) :
    (D.toRelDerivation hD).d s = D.d U s :=
  rfl

end PreDerivation

end PreDerivation

section Support

/-- An `𝒪_X`-module `N` is *supported in* `W` if restriction from any open `U` to `U ⊓ W` is
injective on sections (for instance, a pushforward from an open subscheme contained in `W`). -/
def IsSupportedIn (N : X.Modules) (W : X.Opens) : Prop :=
  ∀ U : X.Opens, Function.Injective (N.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op)

/-- Restriction between equal opens is injective. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.map_injective_of_le {Y : Scheme.{u}}
    (M : Y.Modules) {U U' : Y.Opens} (i : U' ⟶ U) (h : U ≤ U') :
    Function.Injective (M.presheaf.map i.op) := by
  intro a b hab
  have key := congrArg (M.presheaf.map (homOfLE h).op) hab
  rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, Subsingleton.elim (homOfLE h ≫ i) (𝟙 _), op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply, ConcreteCategory.id_apply] at key

/-- Modules pushed forward from `Spec Γ(X, W)` are supported in `W`. -/
theorem isSupportedIn_pushforward_fromSpec {W : X.Opens} (hW : IsAffineOpen W)
    (M : (Spec Γ(X, W)).Modules) :
    IsSupportedIn ((Scheme.Modules.pushforward hW.fromSpec).obj M) W := by
  intro U
  have h : hW.fromSpec ⁻¹ᵁ U ≤ hW.fromSpec ⁻¹ᵁ (U ⊓ W) := by
    rw [Scheme.Hom.preimage_inf, hW.fromSpec_preimage_self, inf_top_eq]
  exact M.map_injective_of_le _ h

/-- Relative derivations into a module supported in an affine open `W` are determined by their
values on `Γ(X, W)`. -/
theorem RelDerivation.ext_of_isSupportedIn {N : X.Modules} {W : X.Opens} (hW : IsAffineOpen W)
    (hN : IsSupportedIn N W) {d d' : RelDerivation f N}
    (h : ∀ a : Γ(X, W), (d.d a : Γ(N, W)) = d'.d a) : d = d' := by
  ext U s
  apply hN U
  rw [← RelDerivation.d_map, ← RelDerivation.d_map]
  exact RelDerivation.ext_of_le_affine d d' hW h inf_le_right _

/-- A pre-derivation into a module supported in `W ≤ f⁻¹ V` (`V` affine) which kills the
pullbacks of `Γ(S, V)` on the opens contained in `W` kills all base subrings. -/
theorem PreDerivation.d_eq_zero_of_isSupportedIn {N : X.Modules} (D : PreDerivation N)
    {W : X.Opens} (hN : IsSupportedIn N W) {V : S.Opens} (hV : IsAffineOpen V)
    (hWV : W ≤ f ⁻¹ᵁ V)
    (hD : ∀ (U : X.Opens) (hU : U ≤ W) (r : Γ(S, V)),
      D.d U (f.appLE V U (hU.trans hWV) r) = 0)
    (U : X.Opens) (t : Γ(X, U)) (ht : t ∈ baseSubring f U) : D.d U t = 0 := by
  apply hN U
  rw [← D.d_map, map_zero]
  exact D.d_eq_zero_of_mem_baseSubring hV (inf_le_right.trans hWV)
    (fun U' hU' r => hD U' (hU'.trans inf_le_right) r) (map_mem_baseSubring f _ ht)

end Support

section AffineDerivation

variable {W : X.Opens} (hW : IsAffineOpen W)

/-- On an open `U ≤ W`, `hW.fromSpec` sends restrictions of sections over `W` to the constant
sections of `Spec Γ(X, W)`. -/
theorem fromSpec_app_map (a : Γ(X, W)) {U : X.Opens} (hU : U ≤ W) :
    hW.fromSpec.app U (X.presheaf.map (homOfLE hU).op a) =
      algebraMap Γ(X, W) Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ U) a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply,
    IsAffineOpen.fromSpec_app_self_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    IsAffineOpen.algebraMap_Spec_obj]
  rfl

theorem fromSpec_app_self_eq (a : Γ(X, W)) :
    hW.fromSpec.app W a = algebraMap Γ(X, W) Γ(Spec Γ(X, W), hW.fromSpec ⁻¹ᵁ W) a := by
  simpa using fromSpec_app_map hW a le_rfl

variable (f) {V : S.Opens} (hWV : W ≤ f ⁻¹ᵁ V)

/-- `(Ω_{A/R})^~` on `Spec A`, for `A = Γ(X, W)`, `R = Γ(S, V)` and `R → A` the map `f.appLE`. -/
abbrev affineTilde : (Spec Γ(X, W)).Modules :=
  tilde (CommRingCat.KaehlerDifferential (f.appLE V W hWV))

/-- The module `ι_* (Ω_{A/R})^~` on `X`, for `ι = hW.fromSpec : Spec A → X`. -/
abbrev affineKaehler : X.Modules :=
  (Scheme.Modules.pushforward hW.fromSpec).obj (affineTilde f hWV)

/-- The pre-derivation `𝒪_X → ι_* (Ω_{A/R})^~`, `s ↦ specDerivation (ι^* s)`. -/
def affinePreDerivation : PreDerivation (affineKaehler f hW hWV) :=
  letI := (f.appLE V W hWV).hom.toAlgebra
  { d := fun U => (specDerivationHom Γ(S, V) (hW.fromSpec ⁻¹ᵁ U)).comp
      (hW.fromSpec.app U).hom.toAddMonoidHom
    d_mul := fun U s t => by
      change specDerivation _ _ (hW.fromSpec.app U (s * t)) = _
      rw [map_mul, specDerivation_mul]
      rfl
    d_map := fun {U U'} i s => by
      change specDerivation _ _ (hW.fromSpec.app U' (X.presheaf.map i.op s)) = _
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply,
        specDerivation_map]
      rfl }

/-- On restrictions of sections over `W`, the affine pre-derivation is `d`. -/
theorem affinePreDerivation_d_map (a : Γ(X, W)) {U : X.Opens} (hU : U ≤ W) :
    (affinePreDerivation f hW hWV).d U (X.presheaf.map (homOfLE hU).op a) =
      (tilde.toOpen (CommRingCat.KaehlerDifferential (f.appLE V W hWV)) (hW.fromSpec ⁻¹ᵁ U)).hom
        (CommRingCat.KaehlerDifferential.d a) := by
  let := (f.appLE V W hWV).hom.toAlgebra
  change specDerivation Γ(S, V) _ (hW.fromSpec.app U (X.presheaf.map (homOfLE hU).op a)) = _
  rw [fromSpec_app_map hW a hU, specDerivation_algebraMap]
  rfl

/-- The affine pre-derivation kills the base subrings. -/
theorem affinePreDerivation_base (hV : IsAffineOpen V) (U : X.Opens) (t : Γ(X, U))
    (ht : t ∈ baseSubring f U) : (affinePreDerivation f hW hWV).d U t = 0 := by
  let := (f.appLE V W hWV).hom.toAlgebra
  refine (affinePreDerivation f hW hWV).d_eq_zero_of_isSupportedIn
    (isSupportedIn_pushforward_fromSpec hW _) hV hWV ?_ U t ht
  intro U hU r
  change specDerivation Γ(S, V) _ (hW.fromSpec.app U (f.appLE V U (hU.trans hWV) r)) = 0
  rw [← Scheme.Hom.appLE_map (e := hWV) (i := (homOfLE hU).op), CommRingCat.comp_apply,
    fromSpec_app_map hW _ hU]
  exact specDerivation_algebraMap_base Γ(S, V) _ r

/-- The relative derivation `𝒪_X → ι_* (Ω_{A/R})^~`. -/
def affineDerivation (hV : IsAffineOpen V) : RelDerivation f (affineKaehler f hW hWV) :=
  (affinePreDerivation f hW hWV).toRelDerivation (affinePreDerivation_base f hW hWV hV)

theorem affineDerivation_d_map (hV : IsAffineOpen V) (a : Γ(X, W)) {U : X.Opens} (hU : U ≤ W) :
    (affineDerivation f hW hWV hV).d (X.presheaf.map (homOfLE hU).op a) =
      (tilde.toOpen (CommRingCat.KaehlerDifferential (f.appLE V W hWV)) (hW.fromSpec ⁻¹ᵁ U)).hom
        (CommRingCat.KaehlerDifferential.d a) :=
  affinePreDerivation_d_map f hW hWV a hU

end AffineDerivation

section Comparison

variable (f) {W : X.Opens} (hW : IsAffineOpen W) {V : S.Opens} (hV : IsAffineOpen V)
  (hWV : W ≤ f ⁻¹ᵁ V)

theorem fromSpec_image_top_le : hW.fromSpec ''ᵁ ⊤ ≤ W := by
  rw [Scheme.Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]

theorem le_fromSpec_image_top : W ≤ hW.fromSpec ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]

/-- On `Spec Γ(X, W) → X`, a constant section `b` corresponds on the image of `U` to the
restriction of `b` (as in lane COH1's `Cohomology.fromSpec_appIso_inv_algebraMap`). -/
theorem fromSpec_appIso_inv_algebraMap' (U : (Spec Γ(X, W)).Opens) (b : Γ(X, W)) :
    (hW.fromSpec.appIso U).inv (algebraMap Γ(X, W) Γ(Spec Γ(X, W), U) b) =
      X.presheaf.map (homOfLE ((hW.fromSpec.image_mono le_top).trans
        (fromSpec_image_top_le hW))).op b := by
  apply (ConcreteCategory.bijective_of_isIso (hW.fromSpec.appIso U).hom).1
  rw [Iso.inv_hom_id_apply, Scheme.Hom.appIso_hom', ← ConcreteCategory.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.appLE, ConcreteCategory.comp_apply,
    IsAffineOpen.fromSpec_app_self, IsAffineOpen.algebraMap_Spec_obj]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← ConcreteCategory.comp_apply ((Spec Γ(X, W)).presheaf.map _),
    ← Functor.map_comp]
  rfl

/-- The morphism `Ω¹_{X/S} ⟶ ι_* (Ω_{A/R})^~` classifying `affineDerivation`. -/
def toAffineKaehler : relativeDifferentials f ⟶ affineKaehler f hW hWV :=
  (homEquiv f _).symm (affineDerivation f hW hWV hV)

theorem toAffineKaehler_app_d (a : Γ(X, W)) {U : X.Opens} (hU : U ≤ W) :
    (toAffineKaehler f hW hV hWV).app U
        ((universalDerivation f).d (X.presheaf.map (homOfLE hU).op a)) =
      (tilde.toOpen (CommRingCat.KaehlerDifferential (f.appLE V W hWV)) (hW.fromSpec ⁻¹ᵁ U)).hom
        (CommRingCat.KaehlerDifferential.d a) := by
  rw [← homEquiv_apply_d, toAffineKaehler, Equiv.apply_symm_apply]
  exact affineDerivation_d_map f hW hWV hV a hU

/-- The morphism `ι^* Ω¹_{X/S} ⟶ (Ω_{A/R})^~` on `Spec A`. -/
def restrictToKaehler :
    (relativeDifferentials f).restrict hW.fromSpec ⟶ affineTilde f hWV :=
  ((Scheme.Modules.restrictAdjunction hW.fromSpec).homEquiv _ _).symm
    (toAffineKaehler f hW hV hWV)

/-- The derivation `Γ(X, W) → Γ(Ω¹_{X/S}, W)`, `a ↦ d a`, relative to `f.appLE`. -/
def sectionsDerivation :
    (ModuleCat.of Γ(X, W) Γ(relativeDifferentials f, W)).Derivation (f.appLE V W hWV) :=
  ModuleCat.Derivation.mk (fun a => (universalDerivation f).d a)
    (fun a b => map_add _ a b) (fun a b => RelDerivation.d_mul _ a b)
    (fun r => RelDerivation.d_appLE _ hWV r)

/-- The `Γ(X, W)`-linear map `Ω_{Γ(X, W)/Γ(S, V)} → Γ(Ω¹_{X/S}, W)`, `da ↦ d a`. -/
def sectionsLinearMap :
    CommRingCat.KaehlerDifferential (f.appLE V W hWV) ⟶
      ModuleCat.of Γ(X, W) Γ(relativeDifferentials f, W) :=
  (sectionsDerivation f hWV).desc

theorem sectionsLinearMap_d (a : Γ(X, W)) :
    sectionsLinearMap f hWV (CommRingCat.KaehlerDifferential.d a) =
      (universalDerivation f).d a :=
  (sectionsDerivation f hWV).desc_d a

/-- The identification `Γ(Ω¹_{X/S}, W) = Γ(ι^* Ω¹_{X/S}, ⊤)` (restriction along the equality
`ι(Spec A) = W`), as a map of `Γ(X, W)`-modules. -/
def sectionsTransport :
    ModuleCat.of Γ(X, W) Γ(relativeDifferentials f, W) ⟶
      moduleSpecΓFunctor.obj ((relativeDifferentials f).restrict hW.fromSpec) :=
  ModuleCat.ofHom (Y := moduleSpecΓFunctor.obj ((relativeDifferentials f).restrict hW.fromSpec))
    { toFun := fun σ =>
        (relativeDifferentials f).presheaf.map (homOfLE (fromSpec_image_top_le hW)).op σ
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun a σ => by
        change _ = (hW.fromSpec.appIso ⊤).inv (algebraMap Γ(X, W) Γ(Spec Γ(X, W), ⊤) a) •
          (relativeDifferentials f).presheaf.map (homOfLE (fromSpec_image_top_le hW)).op σ
        rw [Scheme.Modules.map_smul, fromSpec_appIso_inv_algebraMap'] }

theorem sectionsTransport_apply (σ : Γ(relativeDifferentials f, W)) :
    sectionsTransport f hW σ =
      (relativeDifferentials f).presheaf.map (homOfLE (fromSpec_image_top_le hW)).op σ :=
  rfl

/-- The morphism `(Ω_{A/R})^~ ⟶ ι^* Ω¹_{X/S}` adjoint to `da ↦ d a`. -/
def kaehlerToRestrict : affineTilde f hWV ⟶ (relativeDifferentials f).restrict hW.fromSpec :=
  (tilde.adjunction.homEquiv _ _).symm (sectionsLinearMap f hWV ≫ sectionsTransport f hW)

/-- Morphisms out of `M^~` are determined by their values on the constant global sections. -/
theorem tilde_hom_ext {A : CommRingCat.{u}} {M : ModuleCat.{u} A} {N : (Spec A).Modules}
    {g₁ g₂ : tilde M ⟶ N}
    (h : ∀ m : M, g₁.app ⊤ ((tilde.toOpen M ⊤).hom m) = g₂.app ⊤ ((tilde.toOpen M ⊤).hom m)) :
    g₁ = g₂ := by
  apply (tilde.adjunction.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext m
  exact h m

/-- Morphisms out of `(Ω_{A/R})^~` are determined by their values on the global sections `da`. -/
theorem tilde_kaehler_hom_ext {A B : CommRingCat.{u}} {φ : B ⟶ A} {N : (Spec A).Modules}
    {g₁ g₂ : tilde (CommRingCat.KaehlerDifferential φ) ⟶ N}
    (h : ∀ a : A, g₁.app ⊤ ((tilde.toOpen _ ⊤).hom (CommRingCat.KaehlerDifferential.d a)) =
      g₂.app ⊤ ((tilde.toOpen _ ⊤).hom (CommRingCat.KaehlerDifferential.d a))) :
    g₁ = g₂ := by
  apply (tilde.adjunction.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply CommRingCat.KaehlerDifferential.ext
  intro a
  exact h a

/-- The tilde-adjunct of `ψ : M → Γ(N, ⊤)` sends the constant section `m` to `ψ m`. -/
theorem tilde_homEquiv_symm_app_top {A : CommRingCat.{u}} {M : ModuleCat.{u} A}
    {N : (Spec A).Modules} (ψ : M ⟶ moduleSpecΓFunctor.obj N) (m : M) :
    ((tilde.adjunction.homEquiv M N).symm ψ).app ⊤ ((tilde.toOpen M ⊤).hom m) = ψ m := by
  have h := (tilde.adjunction.homEquiv M N).apply_symm_apply ψ
  erw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun g => g.hom m) h

theorem restrictToKaehler_app_top (x : Γ(relativeDifferentials f, hW.fromSpec ''ᵁ ⊤)) :
    (restrictToKaehler f hW hV hWV).app ⊤ x =
      (affineTilde f hWV).presheaf.map (eqToHom (hW.fromSpec.preimage_image_eq ⊤).symm).op
        ((toAffineKaehler f hW hV hWV).app (hW.fromSpec ''ᵁ ⊤) x) := by
  rw [restrictToKaehler, Adjunction.homEquiv_counit]
  rfl

theorem sectionsTransport_sectionsLinearMap_d (a : Γ(X, W)) :
    sectionsTransport f hW (sectionsLinearMap f hWV (CommRingCat.KaehlerDifferential.d a)) =
      (universalDerivation f).d (X.presheaf.map (homOfLE (fromSpec_image_top_le hW)).op a) := by
  rw [sectionsLinearMap_d]
  exact ((universalDerivation f).d_map _ a).symm

theorem kaehlerToRestrict_app_top (m : CommRingCat.KaehlerDifferential (f.appLE V W hWV)) :
    (kaehlerToRestrict f hW hWV).app ⊤ ((tilde.toOpen _ ⊤).hom m) =
      sectionsTransport f hW (sectionsLinearMap f hWV m) :=
  tilde_homEquiv_symm_app_top _ m

theorem kaehlerToRestrict_restrictToKaehler :
    kaehlerToRestrict f hW hWV ≫ restrictToKaehler f hW hV hWV = 𝟙 _ := by
  apply tilde_kaehler_hom_ext
  intro a
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app]
  change (restrictToKaehler f hW hV hWV).app ⊤
    ((kaehlerToRestrict f hW hWV).app ⊤ ((tilde.toOpen _ ⊤).hom _)) = _
  rw [kaehlerToRestrict_app_top, sectionsTransport_sectionsLinearMap_d]
  refine (restrictToKaehler_app_top f hW hV hWV _).trans ?_
  rw [toAffineKaehler_app_d]
  rfl

theorem toAffineKaehler_app_d_self (a : Γ(X, W)) :
    (toAffineKaehler f hW hV hWV).app W ((universalDerivation f).d a) =
      (tilde.toOpen (CommRingCat.KaehlerDifferential (f.appLE V W hWV)) (hW.fromSpec ⁻¹ᵁ W)).hom
        (CommRingCat.KaehlerDifferential.d a) := by
  have h := toAffineKaehler_app_d f hW hV hWV a le_rfl
  have e : X.presheaf.map (homOfLE (le_refl W)).op a = a := by
    rw [Subsingleton.elim (homOfLE (le_refl W)) (𝟙 W), op_id, CategoryTheory.Functor.map_id,
      ConcreteCategory.id_apply]
  rwa [e] at h

theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.app_map {Y : Scheme.{u}} {M N : Y.Modules}
    (φ : M ⟶ N) {U V : Y.Opens} (i : V ⟶ U) (m : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op m) = N.presheaf.map i.op (φ.app U m) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) m

theorem kaehlerToRestrict_app_toOpen (U : (Spec Γ(X, W)).Opens)
    (m : CommRingCat.KaehlerDifferential (f.appLE V W hWV)) :
    (kaehlerToRestrict f hW hWV).app U ((tilde.toOpen _ U).hom m) =
      ((relativeDifferentials f).restrict hW.fromSpec).presheaf.map (homOfLE le_top).op
        (sectionsTransport f hW (sectionsLinearMap f hWV m)) := by
  have h : (tilde.toOpen (CommRingCat.KaehlerDifferential (f.appLE V W hWV)) U).hom m =
      (affineTilde f hWV).presheaf.map (homOfLE le_top).op ((tilde.toOpen _ ⊤).hom m) := rfl
  rw [h]
  exact (Scheme.Modules.Hom.app_map (kaehlerToRestrict f hW hWV) (homOfLE le_top) _).trans
    (congrArg _ (kaehlerToRestrict_app_top f hW hWV m))

theorem restrictToKaehler_kaehlerToRestrict :
    restrictToKaehler f hW hV hWV ≫ kaehlerToRestrict f hW hWV = 𝟙 _ := by
  apply ((Scheme.Modules.restrictAdjunction hW.fromSpec).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, restrictToKaehler, Equiv.apply_symm_apply,
    Adjunction.homEquiv_id]
  apply (homEquiv f _).injective
  apply RelDerivation.ext_of_isSupportedIn hW (isSupportedIn_pushforward_fromSpec hW _)
  intro a
  rw [homEquiv_apply_d, homEquiv_apply_d, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  change (kaehlerToRestrict f hW hWV).app (hW.fromSpec ⁻¹ᵁ W)
    ((toAffineKaehler f hW hV hWV).app W ((universalDerivation f).d a)) = _
  rw [toAffineKaehler_app_d_self, kaehlerToRestrict_app_toOpen,
    sectionsTransport_sectionsLinearMap_d]
  have h1 := (universalDerivation f).d_map
    (homOfLE (hW.fromSpec.image_mono (le_top : hW.fromSpec ⁻¹ᵁ W ≤ ⊤)))
    (X.presheaf.map (homOfLE (fromSpec_image_top_le hW)).op a)
  have h2 := (universalDerivation f).d_map (homOfLE (hW.fromSpec.image_preimage_le W)) a
  refine h1.symm.trans (Eq.trans ?_ h2)
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **`Ω¹_{X/S}` on an affine open.** For affine opens `W ⊆ X`, `V ⊆ S` with `W ≤ f⁻¹ V`, the
restriction of `Ω¹_{X/S}` to `Spec Γ(X, W)` is the quasi-coherent module `(Ω_{Γ(X,W)/Γ(S,V)})^~`
(blueprint `prop:sm-omega-affine`). -/
def restrictIso : (relativeDifferentials f).restrict hW.fromSpec ≅ affineTilde f hWV where
  hom := restrictToKaehler f hW hV hWV
  inv := kaehlerToRestrict f hW hWV
  hom_inv_id := restrictToKaehler_kaehlerToRestrict f hW hV hWV
  inv_hom_id := kaehlerToRestrict_restrictToKaehler f hW hV hWV

include hV hWV in
theorem isQuasicoherent_restrict_fromSpec :
    ((relativeDifferentials f).restrict hW.fromSpec).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec Γ(X, W)).ringCatSheaf).prop_of_iso
    (restrictIso f hW hV hWV).symm
    (inferInstance : (tilde (CommRingCat.KaehlerDifferential (f.appLE V W hWV))).IsQuasicoherent)

/-- Restriction between equal opens is bijective. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.map_bijective_of_le {Y : Scheme.{u}}
    (M : Y.Modules) {U U' : Y.Opens} (i : U' ⟶ U) (h : U ≤ U') :
    Function.Bijective (M.presheaf.map i.op) := by
  refine ⟨M.map_injective_of_le i h, fun y => ⟨M.presheaf.map (homOfLE h).op y, ?_⟩⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (i ≫ homOfLE h) (𝟙 _), op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]

include hW hV in
/-- **Sections of `Ω¹_{X/S}` over an affine open.** The map
`Ω_{Γ(X, W)/Γ(S, V)} → Γ(Ω¹_{X/S}, W)`, `da ↦ d a`, is bijective (blueprint
`prop:sm-omega-affine`). -/
theorem sectionsLinearMap_bijective : Function.Bijective (sectionsLinearMap f hWV) := by
  have h1 : Function.Bijective
      (tilde.toOpen (CommRingCat.KaehlerDifferential (f.appLE V W hWV)) ⊤).hom :=
    ConcreteCategory.bijective_of_isIso _
  have : IsIso (kaehlerToRestrict f hW hWV) := (restrictIso f hW hV hWV).isIso_inv
  have h2 : Function.Bijective ((kaehlerToRestrict f hW hWV).app ⊤) :=
    ConcreteCategory.bijective_of_isIso _
  have h3 : Function.Bijective (sectionsTransport f hW) :=
    (relativeDifferentials f).map_bijective_of_le _ (le_fromSpec_image_top hW)
  have hcomp : (sectionsTransport f hW) ∘ (sectionsLinearMap f hWV) =
      (kaehlerToRestrict f hW hWV).app ⊤ ∘ (tilde.toOpen _ ⊤).hom := by
    funext m
    exact (kaehlerToRestrict_app_top f hW hWV m).symm
  have h4 : Function.Bijective ((sectionsTransport f hW) ∘ (sectionsLinearMap f hWV)) := by
    rw [hcomp]
    exact h2.comp h1
  exact (Function.Bijective.of_comp_iff' h3 _).mp h4

/-- The isomorphism `Ω_{Γ(X, W)/Γ(S, V)} ≅ Γ(Ω¹_{X/S}, W)` of `Γ(X, W)`-modules. -/
def sectionsEquiv :
    CommRingCat.KaehlerDifferential (f.appLE V W hWV) ≃ₗ[Γ(X, W)]
      Γ(relativeDifferentials f, W) :=
  LinearEquiv.ofBijective (sectionsLinearMap f hWV).hom (sectionsLinearMap_bijective f hW hV hWV)

theorem sectionsEquiv_d (a : Γ(X, W)) :
    sectionsEquiv f hW hV hWV (CommRingCat.KaehlerDifferential.d a) =
      (universalDerivation f).d a :=
  sectionsLinearMap_d f hWV a

end Comparison

section Naturality

variable (f) {W W' : X.Opens} {V : S.Opens} (hWV : W ≤ f ⁻¹ᵁ V) (h : W' ≤ W)

/-- The identification with Kähler differentials is compatible with restriction. -/
theorem map_sectionsLinearMap_d (a : Γ(X, W)) :
    (relativeDifferentials f).presheaf.map (homOfLE h).op
        (sectionsLinearMap f hWV (CommRingCat.KaehlerDifferential.d a)) =
      sectionsLinearMap f (h.trans hWV)
        (CommRingCat.KaehlerDifferential.d (X.presheaf.map (homOfLE h).op a)) := by
  rw [sectionsLinearMap_d, sectionsLinearMap_d]
  exact ((universalDerivation f).d_map _ a).symm

end Naturality
