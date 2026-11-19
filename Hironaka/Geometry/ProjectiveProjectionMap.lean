/-
Copyright (c) 2026. Adapted from Mathlib's ProjectiveSpectrum/Functor.lean
by Kenny Lau (Apache 2.0), retaining its actual native structure-sheaf
and homogeneous localization maps. The relevance hypothesis is weakened
to the true prime-relevance condition required by projective projection.
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

noncomputable section

universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj

namespace Hironaka.Geometry.ProjectiveProjection.General

section universe_polymorphic

variable {A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : ∀ p : ProjectiveSpectrum ℬ, ¬ 𝒜₊ ≤ p.asHomogeneousIdeal.comap f)

namespace Point

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
@[simps] def comapFun (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le := hf p

/-- The underlying continuous function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
def comap : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := comapFun f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by ext; simp⟩

end Point

namespace Morph

open StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 ⊆ Point.comap f hf ⁻¹' U.1)

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def comapStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtPrime ℬ y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl <| s ⟨(Point.comap f hf y.1), hUV y.2⟩

set_option backward.isDefEq.respectTransparency false in
lemma isLocallyFraction_comapStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (comapStructureSheafFun f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨(Point.comap f hf p), hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (Point.comap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [comapStructureSheafFun]

set_option backward.isDefEq.respectTransparency false in
/-- The underlying ring hom of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def comapStructureSheaf :
    (Proj.structureSheaf 𝒜).1.obj (.op U) →+* (Proj.structureSheaf ℬ).1.obj (.op V) where
  toFun s := ⟨comapStructureSheafFun _ _ _ _ hUV s.1,
      isLocallyFraction_comapStructureSheafFun _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [comapStructureSheafFun]
  map_zero' := by ext; simp [comapStructureSheafFun]
  map_add' x y := by ext; simp [comapStructureSheafFun]
  map_mul' x y := by ext; simp [comapStructureSheafFun]

end Morph

end universe_polymorphic

section universe_monomorphic

namespace Morph

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : ∀ p : ProjectiveSpectrum ℬ, ¬ 𝒜₊ ≤ p.asHomogeneousIdeal.comap f)

set_option backward.isDefEq.respectTransparency.types false in
/-- The underlying map of `Proj ℬ ⟶ Proj 𝒜` on the level of sheafed spaces. -/
@[simps! (isSimp := false)] noncomputable def sheafedSpaceMap :
    Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom <| Point.comap f hf
      c := { app U := CommRingCat.ofHom <| comapStructureSheaf f hf _ _ Set.Subset.rfl } }

set_option backward.isDefEq.respectTransparency.types false in
lemma germ_map_sectionInBasicOpen {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (Point.comap f hf p).1.toIdeal.primeCompl) :
    (toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (sheafedSpaceMap f hf).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap f hf).hom.c.app _ (sectionInBasicOpen 𝒜 _ c)) =
    (toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen ℬ p (c.map _ le_rfl)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp] lemma val_sectionInBasicOpen_apply (p : ProjectiveSpectrum.top 𝒜)
    (c : NumDenSameDeg 𝒜 p.1.toIdeal.primeCompl)
    (q : ProjectiveSpectrum.basicOpen 𝒜 c.den) :
    ((sectionInBasicOpen 𝒜 p c).val q).val = .mk c.num ⟨c.den, q.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[elementwise] theorem localRingHom_comp_stalkIso (p : ProjectiveSpectrum ℬ) :
    (stalkIso 𝒜 (Point.comap f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (stalkIso ℬ p).inv =
      (sheafedSpaceMap f hf).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply]
  simp only [GradedRingHom.toRingHom_eq_toRingHom, Localization.localRingHom_mk,
    GradedRingHom.coe_toRingHom]
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_map_sectionInBasicOpen]
  erw [stalkIso'_germ]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality of `Proj`. -/
noncomputable def map : Proj ℬ ⟶ Proj 𝒜 where
  __ := (sheafedSpaceMap f hf).hom
  prop p := .mk fun x hx ↦ by
    rw [← localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (stalkIso 𝒜 (Point.comap f hf p)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

@[simp] theorem map_preimage_basicOpen (s : A) :
    map f hf ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 s = AlgebraicGeometry.Proj.basicOpen ℬ (f s) := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem ι_comp_map (s : A) : (AlgebraicGeometry.Proj.basicOpen ℬ (f s)).ι ≫ map f hf =
    (map f hf).resLE _ _ le_rfl ≫ (AlgebraicGeometry.Proj.basicOpen 𝒜 s).ι := by simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] lemma awayToSection_comp_appLE {i : ℕ} {s : A} (hs : s ∈ 𝒜 i) :
    AlgebraicGeometry.Proj.awayToSection 𝒜 s ≫
      Scheme.Hom.appLE (map f hf) (AlgebraicGeometry.Proj.basicOpen 𝒜 s) (AlgebraicGeometry.Proj.basicOpen ℬ (f s)) (by rfl) =
    CommRingCat.ofHom (Away.map f s : Away 𝒜 s →+* Away ℬ (f s)) ≫
      AlgebraicGeometry.Proj.awayToSection ℬ (f s) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hs
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/--
The following square commutes:
```
Proj ℬ         ⟶ Proj 𝒜₁
    ^                   ^
    |                   |
Spec A₂[f(s)⁻¹]₀ ⟶ Spec A₁[s⁻¹]₀
```
-/
@[reassoc] theorem awayι_comp_map {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    AlgebraicGeometry.Proj.awayι ℬ (f s) (f.2 hs) hi ≫ map f hf =
    Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ AlgebraicGeometry.Proj.awayι 𝒜 s hs hi := by
  rw [AlgebraicGeometry.Proj.awayι, AlgebraicGeometry.Proj.awayι, Category.assoc, ι_comp_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (AlgebraicGeometry.Proj.basicOpen ℬ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, awayToSection_comp_appLE _ _ hs]


end Morph

end universe_monomorphic

end Hironaka.Geometry.ProjectiveProjection.General
