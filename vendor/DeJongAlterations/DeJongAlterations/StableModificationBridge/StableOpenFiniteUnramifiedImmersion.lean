import DeJongAlterations.StableModificationBridge.StableOpenUnramifiedClosedPoints
import DeJongAlterations.StableModification.Curves.Basic

/-! Native finite unramified closed immersions from original closed-point injectivity. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenFiniteUnramifiedImmersion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original affine map becomes a closed immersion from original closed points. -/
theorem closedImmersion_affine_of_closedPoint_injective {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] [FormallyUnramified f]
    {k : Type u} [Field k] [IsAlgClosed k]
    (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    (hclosed : ∀ x y : X, IsClosed ({x} : Set X) → IsClosed ({y} : Set X) →
      f x = f y → x = y) : IsClosedImmersion f := by
  let : IsAffine X := isAffine_of_isAffineHom f
  let κ : k →+* Γ(Y, ⊤) :=
    (q.appLE ⊤ ⊤ (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let : Algebra k Γ(Y, ⊤) := κ.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra k Γ(X, ⊤) := (f.appTop.hom.comp κ).toAlgebra
  have : IsScalarTower k Γ(Y, ⊤) Γ(X, ⊤) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType k Γ(Y, ⊤) := by
    apply (q.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)).comp
    exact RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2
  have : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  have : Algebra.FormallyUnramified Γ(Y, ⊤) Γ(X, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)).mp inferInstance
  have hmax : ∀ m m' : Ideal Γ(X, ⊤), m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap Γ(Y, ⊤) Γ(X, ⊤)) =
        m'.comap (algebraMap Γ(Y, ⊤) Γ(X, ⊤)) → m = m' := by
    intro m m' hm hm' heq
    let x : Spec Γ(X, ⊤) := ⟨m, hm.isPrime⟩
    let y : Spec Γ(X, ⊤) := ⟨m', hm'.isPrime⟩
    have hx : IsClosed ({x} : Set (Spec Γ(X, ⊤))) := x.isClosed_singleton_iff_isMaximal.mpr hm
    have hy : IsClosed ({y} : Set (Spec Γ(X, ⊤))) := y.isClosed_singleton_iff_isMaximal.mpr hm'
    have hcx : IsClosed ({X.isoSpec.inv x} : Set X) := by
      simpa only [Set.image_singleton] using X.isoSpec.inv.isClosedEmbedding.isClosedMap _ hx
    have hcy : IsClosed ({X.isoSpec.inv y} : Set X) := by
      simpa only [Set.image_singleton] using X.isoSpec.inv.isClosedEmbedding.isClosedMap _ hy
    have hspec : Spec.map f.appTop x = Spec.map f.appTop y := PrimeSpectrum.ext heq
    have hfx : f (X.isoSpec.inv x) = f (X.isoSpec.inv y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.isoSpec_inv_naturality,
        Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hspec]
    have hxy := X.isoSpec.inv.isOpenEmbedding.injective (hclosed _ _ hcx hcy hfx)
    exact congrArg PrimeSpectrum.asIdeal hxy
  have hs := StableOpenUnramifiedClosedPoints.closedImmersion_spec_of_maximal_injective
    (k := k) hmax
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (arrowIsoSpecΓOfIsAffine f)).mpr hs

/-- Original closed points suffice globally: all open restrictions and comparisons are internal. -/
theorem closedImmersion_of_closedPoint_injective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [FormallyUnramified f]
    {k : Type u} [Field k] [IsAlgClosed k]
    (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    (hclosed : ∀ x y : X, IsClosed ({x} : Set X) → IsClosed ({y} : Set X) →
      f x = f y → x = y) : IsClosedImmersion f := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Y.affineCover]
  intro i
  change IsClosedImmersion (pullback.snd f (Y.affineCover.f i))
  have : FormallyUnramified (pullback.snd f (Y.affineCover.f i)) :=
    MorphismProperty.pullback_snd (P := @FormallyUnramified) _ _ inferInstance
  apply closedImmersion_affine_of_closedPoint_injective _ (Y.affineCover.f i ≫ q)
  intro x y hx hy hxy
  apply (pullback.fst f (Y.affineCover.f i)).isOpenEmbedding.injective
  apply hclosed
  · exact StableModification.Curves.isClosed_image_of_isClosed
      (q := pullback.fst f (Y.affineCover.f i) ≫ f ≫ q) (q' := f ≫ q)
      (pullback.fst f (Y.affineCover.f i)) rfl hx
  · exact StableModification.Curves.isClosed_image_of_isClosed
      (q := pullback.fst f (Y.affineCover.f i) ≫ f ≫ q) (q' := f ≫ q)
      (pullback.fst f (Y.affineCover.f i)) rfl hy
  · have h := congrArg (Y.affineCover.f i) hxy
    simpa only [← Scheme.Hom.comp_apply, ← pullback.condition] using h

end DeJongAlterations.StableModificationBridge.StableOpenFiniteUnramifiedImmersion
