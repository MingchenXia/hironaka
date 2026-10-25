import DeJongAlterations.StableModification.Limits.Descent
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth and étale models of affine schemes over the approximating system

Let `R ⊆ L` be an `A`-subalgebra and consider lane LIM1's system `Spec B`, `B ⊆ R` finitely
generated over `A`, with limit `Spec R` (`Limits.System`). Mathlib's noetherian descent of smooth
and étale algebras (`Algebra.Smooth.exists_subalgebra_fg`, `Algebra.Etale.exists_subalgebra_fg`,
Stacks 00TP, 00U2) writes a smooth (étale) `R`-algebra `E` as `R ⊗_{A₀} B₀` for a finitely
generated `A`-subalgebra `A₀ ⊆ R` and a smooth (étale) `A₀`-algebra `B₀`. Translated into a
`Limits.Model` at the level `B = A₀` (`exists_model_spec_of_tensorEquiv`), this gives
**smooth (étale) models of finite presentation of affine smooth (étale) schemes over `Spec R`**
(`exists_smooth_model_of_isAffine`, `exists_etale_model_of_isAffine`), the hypothesis of the
descent of properties local on the source (`Spread.exists_baseChange_of_forall_isAffineOpen`).

This is the descent of smoothness and étaleness of EGA IV 17.7.8 used by Temkin, *Stable
modification of relative curves*, §3.1 (T:2262–2298) and Rem. 3.1.1 (T:2283–2300).
Blueprint: `sm-spread.tex`, `lem:sm-spread-affine-models`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct Opposite

namespace DeJongAlterations.StableModification.Limits.Spread

universe u

set_option backward.isDefEq.respectTransparency false

variable {A L : Type u} [CommRing A] [CommRing L] [Algebra A L] {R : Subalgebra A L}

/-- **Models from tensor decompositions.** Let `E` be an `R`-algebra with `E ≅ R ⊗_{A₀} B₀`, where
`A₀ ⊆ R` is a finitely generated `A`-subalgebra and `B₀` a finitely presented `A₀`-algebra. Then
`Spec E ⟶ Spec R` has a model of finite presentation at the level `A₀` (as a subalgebra of `L`),
whose structure morphism is `Spec B₀ ⟶ Spec A₀` up to an isomorphism of the base. -/
theorem exists_model_spec_of_tensorEquiv (E : Type u) [CommRing E] [Algebra R E]
    (A₀ : Subalgebra A R) (hA₀ : A₀.FG) (B₀ : Type u) [CommRing B₀] [Algebra A₀ B₀]
    [Algebra.FinitePresentation A₀ B₀] (e : E ≃ₐ[R] R ⊗[A₀] B₀) :
    ∃ (B : FGSubalgebra A R)
      (M : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R)
        (Spec.map (CommRingCat.ofHom (algebraMap R E))) (op B)),
      M.IsFP ∧ ∀ (P : MorphismProperty Scheme.{u}) [P.RespectsIso],
        P (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))) → P M.fY := by
  let B : FGSubalgebra A R := ⟨A₀.map R.val, hA₀.map _, by
    rintro _ ⟨x, -, rfl⟩
    exact x.2⟩
  let ε : A₀ ≃ₐ[A] B.1 := Subalgebra.equivMapOfInjective A₀ R.val Subtype.val_injective
  -- the isomorphisms of the corners
  let e₁ : Spec (.of (R ⊗[A₀] B₀)) ≅ Spec (.of E) :=
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e.toRingEquiv).op
  let e₄ : Spec (.of A₀) ≅ Spec (.of B.1) :=
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso ε.symm.toRingEquiv).op
  let fY : Spec (.of B₀) ⟶ Spec (.of B.1) :=
    Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀)) ≫ e₄.hom
  let g : Spec (.of E) ⟶ Spec (.of B₀) :=
    Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := A₀) (A := R)).toRingHom))
  have H := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A₀ R B₀)).flip
  have hsq : IsPullback g (Spec.map (CommRingCat.ofHom (algebraMap R E))) fY
      ((fgSpecCone R).π.app (op B)) := by
    refine H.of_iso e₁ (Iso.refl _) (Iso.refl _) e₄ ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id]
      change _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp
    · rw [Iso.refl_hom, Category.comp_id]
      change _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp
    · simp [fY]
    · rw [Iso.refl_hom, Category.id_comp]
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext x
      have h := congrArg Subtype.val (ε.apply_symm_apply x)
      rw [Subalgebra.coe_equivMapOfInjective_apply] at h
      exact h
  refine ⟨B, ⟨Spec (.of B₀), fY, g, hsq⟩, ?_, fun P _ hP ↦ ?_⟩
  · have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
      exact RingHom.finitePresentation_algebraMap.2 inferInstance
    refine ⟨inferInstanceAs (LocallyOfFinitePresentation (_ ≫ _)), ?_, ?_⟩
    · exact HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := fY) |>.mpr inferInstance
    · exact HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated) (f := fY) |>.mpr
        inferInstance
  · exact (MorphismProperty.cancel_right_of_respectsIso P _ e₄.hom).mpr hP

/-- Transport of a model along an isomorphism of the source. -/
def modelOfIso {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}
    {X X' : Scheme.{u}} {f : X ⟶ c.pt} {i : I} (m : Model D c f i) (e : X' ≅ X)
    (f' : X' ⟶ c.pt) (hf' : e.hom ≫ f = f') : Model D c f' i where
  Y := m.Y
  fY := m.fY
  g := e.hom ≫ m.g
  isPullback := by
    subst hf'
    exact m.isPullback.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)

lemma isFP_modelOfIso {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}
    {X X' : Scheme.{u}} {f : X ⟶ c.pt} {i : I} {m : Model D c f i} (hm : m.IsFP) (e : X' ≅ X)
    (f' : X' ⟶ c.pt) (hf' : e.hom ≫ f = f') : (modelOfIso m e f' hf').IsFP := hm

/-- The `R`-algebra structure on the global sections of an affine scheme over `Spec R`. -/
abbrev sectionsAlgebra {W : Scheme.{u}} [IsAffine W] (fW : W ⟶ (fgSpecCone R).pt) :
    Algebra R Γ(W, ⊤) :=
  (Spec.preimage (W.isoSpec.inv ≫ fW)).hom.toAlgebra

lemma isoSpec_hom_comp_specMap {W : Scheme.{u}} [IsAffine W] (fW : W ⟶ (fgSpecCone R).pt) :
    letI := sectionsAlgebra fW
    W.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(W, ⊤))) = fW := by
  let _ := sectionsAlgebra fW
  have : CommRingCat.ofHom (algebraMap R Γ(W, ⊤)) = Spec.preimage (W.isoSpec.inv ≫ fW) := rfl
  rw [this, Spec.map_preimage, Iso.hom_inv_id_assoc]

/-- **Smooth models of affine smooth schemes.** -/
theorem exists_smooth_model_of_isAffine {W : Scheme.{u}} [IsAffine W]
    (fW : W ⟶ (fgSpecCone R).pt) [Smooth fW] :
    ∃ (B : FGSubalgebra A R)
      (M : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) fW (op B)),
      M.IsFP ∧ Smooth M.fY := by
  let _ := sectionsAlgebra fW
  have hW := isoSpec_hom_comp_specMap fW
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R Γ(W, ⊤)))) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) W.isoSpec.hom, hW]
    infer_instance
  have : Algebra.Smooth R Γ(W, ⊤) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom,
      RingHom.smooth_algebraMap] at this
    exact this
  obtain ⟨A₀, B₀, _, _, hA₀, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg A R Γ(W, ⊤)
  obtain ⟨B, M, hM, hP⟩ := exists_model_spec_of_tensorEquiv Γ(W, ⊤) A₀ hA₀ B₀ e
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom,
      RingHom.smooth_algebraMap]
    exact hsm
  exact ⟨B, modelOfIso M W.isoSpec fW hW, isFP_modelOfIso hM W.isoSpec fW hW, hP @Smooth hs⟩

/-- **Étale models of affine étale schemes.** -/
theorem exists_etale_model_of_isAffine {W : Scheme.{u}} [IsAffine W]
    (fW : W ⟶ (fgSpecCone R).pt) [Etale fW] :
    ∃ (B : FGSubalgebra A R)
      (M : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) fW (op B)),
      M.IsFP ∧ Etale M.fY := by
  let _ := sectionsAlgebra fW
  have hW := isoSpec_hom_comp_specMap fW
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R Γ(W, ⊤)))) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Etale) W.isoSpec.hom, hW]
    infer_instance
  have : Algebra.Etale R Γ(W, ⊤) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom,
      RingHom.etale_algebraMap] at this
    exact this
  obtain ⟨A₀, B₀, _, _, hA₀, het, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg A R Γ(W, ⊤)
  obtain ⟨B, M, hM, hP⟩ := exists_model_spec_of_tensorEquiv Γ(W, ⊤) A₀ hA₀ B₀ e
  have hs : Etale (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom,
      RingHom.etale_algebraMap]
    exact het
  exact ⟨B, modelOfIso M W.isoSpec fW hW, isFP_modelOfIso hM W.isoSpec fW hW, hP @Etale hs⟩

end DeJongAlterations.StableModification.Limits.Spread
