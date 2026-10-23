import DeJongAlterations.Geometry.LineBundleNativePullback
import DeJongAlterations.StableModification.Omega.ComponentDegree
import DeJongAlterations.StableModification.Gluing.RefinementProjective
import DeJongAlterations.StableModification.Global.Pairwise

/-! Actual original polarization comparisons and affine native normalized open lifts. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenPolarizationPullback

open StableModification Projectivity Cohomology CurvesField.Genus
open Omega.ComponentNormalization Omega.ComponentDegree

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The WHOLE native original module comparison on N is constructed, not a caller certificate. -/
def originalPullbackPowerIso {X N P : Scheme.{u}} (L : LineBundleData X)
    (H : LineBundleData P) (U : X.Opens) (b : N ⟶ U.toScheme) (ν : N ⟶ X)
    (fac : b ≫ U.ι = ν) (h : U.toScheme ⟶ P) (m : ℤ)
    (e : (L.pullback U.ι).twist (unitModule U.toScheme) m ≅
      (H.pullback h).twist (unitModule U.toScheme) 1) :
    (L.pullback ν).twist (unitModule N) m ≅
      (H.pullback (b ≫ h)).twist (unitModule N) 1 :=
  (L.nativePullbackTwistIso m ν).symm ≪≫
    (Scheme.Modules.pullbackCongr fac.symm).app (L.twist (unitModule X) m) ≪≫
    ((Scheme.Modules.pullbackComp b U.ι).app (L.twist (unitModule X) m)).symm ≪≫
    (Scheme.Modules.pullback b).mapIso (L.nativePullbackTwistIso m U.ι) ≪≫
    (Scheme.Modules.pullback b).mapIso e ≪≫
    (Scheme.Modules.pullback b).mapIso ((H.nativePullbackTwistIso 1 h).symm) ≪≫
    (Scheme.Modules.pullbackComp b h).app (H.twist (unitModule P) 1) ≪≫
    H.nativePullbackTwistIso 1 (b ≫ h)

/-- The SAME native normalized component lifts into the ORIGINAL open, affinely and with the
ENTIRE original map; no point factor, affine-lift or coefficient certificate is supplied. -/
theorem exists_affine_normalization_lift {X C V : Scheme.{u}} [V.IsSeparated]
    (β : X ⟶ C) (q : C ⟶ V) [LocallyOfFiniteType (β ≫ q)]
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ V)
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) (β ≫ q) a)))]
    (v : pullback (C := Scheme.{u}) (β ≫ q) a)
    (hcon : (Curves.pullbackCompMap β q a '' closure {v}).Subsingleton)
    (W : C.Opens) (hW : β (pullback.fst (β ≫ q) a v) ∈ W) :
    ∃ b : componentNormalization (β ≫ q) a v ⟶ (β ⁻¹ᵁ W).toScheme,
      b ≫ (β ⁻¹ᵁ W).ι = componentMap (β ≫ q) a v ∧ IsAffineHom b := by
  let π := normalizationPointsMap ({v} : Set (pullback (C := Scheme.{u}) (β ≫ q) a))
  let ν := componentMap (β ≫ q) a v
  have hpt (z : pullback (C := Scheme.{u}) (β ≫ q) a) :
      pullback.fst q a (Curves.pullbackCompMap β q a z) = β (pullback.fst (β ≫ q) a z) :=
    congrArg (fun h => h z) (Curves.pullbackCompMap_fst β q a)
  have hrange : Set.range ν ⊆ Set.range (β ⁻¹ᵁ W).ι := by
    rintro x ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have he := hcon ⟨π z, normalizationPointsMap_mem_closure v z, rfl⟩
      ⟨v, subset_closure rfl, rfl⟩
    have hβ : β (ν z) = β (pullback.fst (β ≫ q) a v) := by
      change β (pullback.fst (β ≫ q) a (π z)) = _
      rw [← hpt (π z), he, hpt v]
    change β (ν z) ∈ W
    rw [hβ]
    exact hW
  let b := IsOpenImmersion.lift (β ⁻¹ᵁ W).ι ν hrange
  have hb : b ≫ (β ⁻¹ᵁ W).ι = ν := IsOpenImmersion.lift_fac _ _ _
  have : IsAffineHom a := Global.isAffineHom_of_isAffine_of_isSeparated a
  have : IsFinite π := isFinite_normalizationPointsMap_singleton v (pullback.snd (β ≫ q) a)
  have : IsAffineHom (pullback.fst (β ≫ q) a) :=
    MorphismProperty.pullback_fst _ _ (inferInstanceAs (IsAffineHom a))
  have : IsAffineHom ν := inferInstanceAs (IsAffineHom (π ≫ pullback.fst (β ≫ q) a))
  have : IsAffineHom (b ≫ (β ⁻¹ᵁ W).ι) := hb.symm ▸ inferInstance
  exact ⟨b, hb, IsAffineHom.of_comp b (β ⁻¹ᵁ W).ι⟩

/-- Relative projectivity internally gives the SAME actual geometric-field projective embedding. -/
theorem isProjectiveOver_geometric_fibre {R K : Type u} [CommRing R] [Field K]
    {X V : Scheme.{u}} (pV : V ⟶ Spec (.of R)) (f : X ⟶ V)
    (hf : DeJong.IsRelativelyProjective pV f) (a : Spec (.of K) ⟶ V) :
    IsProjectiveOver (pullback.snd f a) := by
  let φ : R →+* K := (Spec.preimage (a ≫ pV)).hom
  have he : Spec.map (CommRingCat.ofHom φ) = a ≫ pV := Spec.map_preimage _
  have hh := hf.pullback_snd a
  have hh' : DeJong.IsRelativelyProjective (𝟙 _ ≫ Spec.map (CommRingCat.ofHom φ)) (pullback.snd f a) := by
    simpa only [Category.id_comp, he] using hh
  exact (DeJong.isRelativelyProjective_id_iff (pullback.snd f a)).mp
    ((isRelativelyProjective_comp_specMap_iff φ (𝟙 _) _).mp hh')

end DeJongAlterations.StableModificationBridge.StableOpenPolarizationPullback
