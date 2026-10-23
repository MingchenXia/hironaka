import DeJongAlterations.StableModificationBridge.NilradicalCoverEngine
import DeJongAlterations.StableModification.Projectivity.RelativeFibre

/-! Actual affine closed-subscheme pullback internally lifts all line-bundle sections and reduced frames. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.AffineClosedSectionLifting

open CategoryTheory Opposite AlgebraicGeometry
open StableModification StableModification.Projectivity StableModification.Cohomology
open Projectivity.LineBundleData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData) (L : LineBundleData X) (m : ℤ)

/-- The WHOLE original section pullback along the SAME actual closed-subscheme morphism. -/
def sectionsMap {U V : X.Opens} (hV : V ≤ U) :
    sectionsModuleCat (L.twist (unitModule X) m) (RingHom.id Γ(X, U)) V hV →ₗ[Γ(X, U)]
      sectionsModuleCat ((L.pullback I.subschemeι).twist (unitModule I.subscheme) m)
        (I.subschemeι.app U).hom (I.subschemeι ⁻¹ᵁ V) (I.subschemeι.preimage_mono hV) where
  toFun s := Sections.pullback I.subschemeι (L := L) (m := m) s
  map_add' s t := Sections.pullback_add L m _ s t
  map_smul' r s := by
    change Sections.pullback I.subschemeι ((res hV r) • (show L.Sections m V from s)) =
      res (I.subschemeι.preimage_mono hV) (I.subschemeι.app U r) •
        Sections.pullback I.subschemeι (show L.Sections m V from s)
    rw [Sections.pullback_smul, LineBundleData.app_res]

/-- EVERY original restriction square follows the SAME whole original pullback. -/
theorem sectionsMap_restrict {U V V' : X.Opens} (hV : V ≤ U) (hV' : V' ≤ U)
    (h : V' ≤ V) (s : L.Sections m V) :
    sectionsMap I L m hV' (sectionsRestrict (L.twist (unitModule X) m)
      (RingHom.id Γ(X, U)) hV hV' h s) =
      sectionsRestrict ((L.pullback I.subschemeι).twist (unitModule I.subscheme) m)
        (I.subschemeι.app U).hom (I.subschemeι.preimage_mono hV)
        (I.subschemeι.preimage_mono hV') (I.subschemeι.preimage_mono h)
        (sectionsMap I L m hV s) :=
  Sections.pullback_restrict L m I.subschemeι h s

variable {U : X.Opens} (hU : IsAffineOpen U)

include hU in
private theorem basicOpen_surjective {g : Γ(X, U)} (hg : g ∈ L.chartBasicSet U) :
    Function.Surjective (sectionsMap I L m (X.basicOpen_le g)) := by
  obtain ⟨j, hj⟩ := hg
  intro t
  have hle : I.subschemeι ⁻¹ᵁ X.basicOpen g ≤ (L.pullback I.subschemeι).U j :=
    I.subschemeι.preimage_mono hj
  let b := toLocal (unitModule I.subscheme) m (L := L.pullback I.subschemeι) hle
    (show (L.pullback I.subschemeι).Sections m (I.subschemeι ⁻¹ᵁ X.basicOpen g) from t).toTwist
  obtain ⟨a, ha⟩ := I.subschemeι_app_surjective ⟨X.basicOpen g, hU.basicOpen g⟩ b
  refine ⟨Sections.ofTwist (ofLocal (unitModule X) m hj a), ?_⟩
  change Sections.pullback I.subschemeι (Sections.ofTwist (ofLocal (unitModule X) m hj a)) = t
  apply (localEquiv (unitModule I.subscheme) m (L := L.pullback I.subschemeι) hle).injective
  rw [localEquiv_apply, localEquiv_apply]
  change toLocal _ m hle (Sections.pullback I.subschemeι
    (Sections.ofTwist (ofLocal (unitModule X) m hj a))).toTwist = b
  rw [toLocal_pullback]
  change I.subschemeι.app _ (toLocal (unitModule X) m hj (ofLocal (unitModule X) m hj a)) = b
  rw [toLocal_ofLocal]
  exact ha

include hU in
private theorem target_localized (g : Γ(X, U)) :
    IsLocalizedModule (Submonoid.powers g)
      (sectionsRestrict ((L.pullback I.subschemeι).twist (unitModule I.subscheme) m)
        (I.subschemeι.app U).hom le_rfl (I.subschemeι.preimage_mono (X.basicOpen_le g))
        (I.subschemeι.preimage_mono (X.basicOpen_le g))).hom :=
  isLocalizedModule_sectionsRestrict _ (I.subschemeι.app U).hom
    (hU.preimage I.subschemeι) le_rfl g (by
      rw [Scheme.preimage_basicOpen]
      exact (inf_eq_left.mpr (Scheme.basicOpen_le _ _)).symm)

include hU in
/-- Actual localization on the original trivializing basic opens proves WHOLE affine section surjectivity. -/
theorem sectionsMap_surjective : Function.Surjective (sectionsMap I L m (le_refl U)) := by
  let S := L.chartBasicSet U
  let : ∀ r : S, IsLocalizedModule.Away r.1
      (sectionsRestrict (L.twist (unitModule X) m) (RingHom.id Γ(X, U)) le_rfl
        (X.basicOpen_le r.1) (X.basicOpen_le r.1)).hom :=
    fun r => L.isLocalizedModule_restrict_basicOpen m hU r.1
  let : ∀ r : S, IsLocalizedModule.Away r.1
      (sectionsRestrict ((L.pullback I.subschemeι).twist (unitModule I.subscheme) m)
        (I.subschemeι.app U).hom le_rfl (I.subschemeι.preimage_mono (X.basicOpen_le r.1))
        (I.subschemeι.preimage_mono (X.basicOpen_le r.1))).hom :=
    fun r => target_localized I L m hU r.1
  refine surjective_of_isLocalized_span S (L.span_chartBasicSet hU) _
    (fun r => (sectionsRestrict (L.twist (unitModule X) m) (RingHom.id Γ(X, U)) le_rfl
      (X.basicOpen_le r.1) (X.basicOpen_le r.1)).hom) _
    (fun r => (sectionsRestrict ((L.pullback I.subschemeι).twist (unitModule I.subscheme) m)
      (I.subschemeι.app U).hom le_rfl (I.subschemeι.preimage_mono (X.basicOpen_le r.1))
      (I.subschemeι.preimage_mono (X.basicOpen_le r.1))).hom) _ (fun r => ?_)
  have heq : IsLocalizedModule.map (Submonoid.powers r.1)
      (sectionsRestrict (L.twist (unitModule X) m) (RingHom.id Γ(X, U)) le_rfl
        (X.basicOpen_le r.1) (X.basicOpen_le r.1)).hom
      (sectionsRestrict ((L.pullback I.subschemeι).twist (unitModule I.subscheme) m)
        (I.subschemeι.app U).hom le_rfl (I.subschemeι.preimage_mono (X.basicOpen_le r.1))
        (I.subschemeι.preimage_mono (X.basicOpen_le r.1))).hom
      (sectionsMap I L m (le_refl U)) = sectionsMap I L m (X.basicOpen_le r.1) := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r.1)
      (sectionsRestrict (L.twist (unitModule X) m) (RingHom.id Γ(X, U)) le_rfl
        (X.basicOpen_le r.1) (X.basicOpen_le r.1)).hom
      (sectionsRestrict ((L.pullback I.subschemeι).twist (unitModule I.subscheme) m)
        (I.subschemeι.app U).hom le_rfl (I.subschemeι.preimage_mono (X.basicOpen_le r.1))
        (I.subschemeι.preimage_mono (X.basicOpen_le r.1))).hom
    rw [IsLocalizedModule.map_comp]
    ext s
    exact (sectionsMap_restrict I L m le_rfl (X.basicOpen_le r.1) _ s).symm
  rw [heq]
  exact basicOpen_surjective I L m hU r.2

include hU in
/-- EVERY actual affine closed-subscheme section lifts with its WHOLE pullback equality. -/
theorem surjective_pullback_subscheme :
    Function.Surjective (fun s : L.Sections m U => s.pullback I.subschemeι) :=
  sectionsMap_surjective I L m hU

include hU in
/-- An actual reduced generator INTERNALLY supplies its SAME original affine frame and whole pullback. -/
theorem exists_nilradical_frame
    (s : (L.pullback X.nilradical.subschemeι).Sections m (X.nilradical.subschemeι ⁻¹ᵁ U))
    (hs : s.nonvanishingLocus = X.nilradical.subschemeι ⁻¹ᵁ U) :
    ∃ τ : L.Sections m U, τ.pullback X.nilradical.subschemeι = s ∧ τ.nonvanishingLocus = U := by
  obtain ⟨τ, hτ⟩ := surjective_pullback_subscheme X.nilradical L m hU s
  change τ.pullback X.nilradical.subschemeι = s at hτ
  refine ⟨τ, hτ, ?_⟩
  have hpre : X.nilradical.subschemeι ⁻¹ᵁ τ.nonvanishingLocus =
      X.nilradical.subschemeι ⁻¹ᵁ U := by
    rw [← Sections.nonvanishingLocus_pullback, hτ, hs]
  ext x
  obtain ⟨z, rfl⟩ := NilradicalCoverEngine.reduction_surjective X x
  change z ∈ X.nilradical.subschemeι ⁻¹ᵁ τ.nonvanishingLocus ↔
    z ∈ X.nilradical.subschemeι ⁻¹ᵁ U
  rw [hpre]

end DeJongAlterations.StableModificationBridge.AffineClosedSectionLifting
