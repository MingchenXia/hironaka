import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Actual QCQS flat base change of the ORIGINAL global-section ring

Adapted from EnvelopeProperty/EnvelopeProperty/FlatGlobalSections.lean
in the same workspace, SHA256: 312240678dab9c99f64858566af12bc64c530cf06cee7aac45244273e9b530a7.
The proof uses only native Mathlib. Both original coefficient maps and
original whole projection maps are retained; no external project is imported.
-/

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped TensorProduct
noncomputable section
namespace Hironaka.Geometry.ProperGeometricGlobalFunctions
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The ORIGINAL coefficient homomorphism on the ACTUAL whole original section ring. -/
def coefficientMap : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom

abbrev baseChange := pullback f (Spec.map (CommRingCat.ofHom (algebraMap A S)))
abbrev firstProjection : baseChange (S := S) f ⟶ X := pullback.fst _ _
abbrev structureMap : baseChange (S := S) f ⟶ Spec (.of S) := pullback.snd _ _

private theorem sectionSquare [Module.Flat A S] [QuasiCompact f] [QuasiSeparated f] :
    IsPushout f.appTop (Spec.map (CommRingCat.ofHom (algebraMap A S))).appTop
      (firstProjection (S := S) f).appTop (structureMap (S := S) f).appTop := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap A S))
  let : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hc : IsCompact (X := X) (⊤ : X.Opens) := by
    simpa using f.isCompact_preimage (isAffineOpen_top (Spec (.of A))).isCompact
  have hq : IsQuasiSeparated (α := X) (⊤ : X.Opens) := by
    simpa using f.isQuasiSeparated_preimage (isAffineOpen_top (Spec (.of A))).isQuasiSeparated
  have hi := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f g) (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp) (isAffineOpen_top _) (isAffineOpen_top _) hc hq
  have hp := (isIso_pushoutSection_iff (IsPullback.of_hasPullback f g)
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (by simp) (by simp) (by simp)).mp hi
  simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using hp

/-- The original A/S coefficient square and BOTH whole projection section maps form an actual pushout. -/
theorem originalSectionSquare [Module.Flat A S] [QuasiCompact f] [QuasiSeparated f] :
    IsPushout (CommRingCat.ofHom (coefficientMap f))
      (CommRingCat.ofHom (algebraMap A S)) (firstProjection (S := S) f).appTop
      (CommRingCat.ofHom (coefficientMap (structureMap (S := S) f))) := by
  apply (sectionSquare (S := S) f).of_iso
    (Scheme.ΓSpecIso (.of A)) (Iso.refl _) (Scheme.ΓSpecIso (.of S)) (Iso.refl _)
  · simp [coefficientMap]
  · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A S))
  · simp
  · simp [coefficientMap]

/-- The section algebra carries precisely the ORIGINAL coefficient homomorphism. -/
abbrev sectionsAlgebra : Algebra A Γ(X, ⊤) :=
  (coefficientMap f).toAlgebra

/-- The true original flat base-change tensor algebra equivalence. -/
def tensorEquiv [Module.Flat A S] [QuasiCompact f] [QuasiSeparated f] :
    let : Algebra A Γ(X, ⊤) := sectionsAlgebra f
    let : Algebra S Γ(baseChange (S := S) f, ⊤) := sectionsAlgebra (structureMap (S := S) f)
    S ⊗[A] Γ(X, ⊤) ≃ₐ[S] Γ(baseChange (S := S) f, ⊤) := by
  let : Algebra A Γ(X, ⊤) := sectionsAlgebra f
  let : Algebra S Γ(baseChange (S := S) f, ⊤) := sectionsAlgebra (structureMap (S := S) f)
  let e₀ : CommRingCat.of (S ⊗[A] Γ(X, ⊤)) ≅ Γ(baseChange (S := S) f, ⊤) :=
    (CommRingCat.isPushout_tensorProduct A S Γ(X, ⊤)).isoPushout ≪≫
      (originalSectionSquare (S := S) f).flip.isoPushout.symm
  let e := e₀.commRingCatIsoToRingEquiv
  refine { toRingEquiv := e, commutes' := ?_ }
  intro s
  change ((CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
    ((CommRingCat.isPushout_tensorProduct A S Γ(X, ⊤)).isoPushout ≪≫
      (originalSectionSquare (S := S) f).flip.isoPushout.symm).hom) s = _
  simp only [Iso.trans_hom, Iso.symm_hom, IsPushout.inl_isoPushout_hom_assoc,
    IsPushout.inl_isoPushout_inv]
  rfl

/-- The entire original coefficient inclusion agrees with the literal second projection. -/
theorem tensorEquiv_includeLeft [Module.Flat A S] [QuasiCompact f] [QuasiSeparated f] (s : S) :
    let : Algebra A Γ(X, ⊤) := sectionsAlgebra f
    tensorEquiv (S := S) f (Algebra.TensorProduct.includeLeftRingHom s) =
      coefficientMap (structureMap (S := S) f) s := by
  let : Algebra A Γ(X, ⊤) := sectionsAlgebra f
  let : Algebra S Γ(baseChange (S := S) f, ⊤) := sectionsAlgebra (structureMap (S := S) f)
  exact (tensorEquiv (S := S) f).commutes s

/-- The entire original section inclusion agrees with the literal first projection. -/
theorem tensorEquiv_includeRight [Module.Flat A S] [QuasiCompact f] [QuasiSeparated f]
    (b : Γ(X, ⊤)) :
    let : Algebra A Γ(X, ⊤) := sectionsAlgebra f
    tensorEquiv (S := S) f (Algebra.TensorProduct.includeRight b) =
      (firstProjection (S := S) f).appTop b := by
  let : Algebra A Γ(X, ⊤) := sectionsAlgebra f
  change ((CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
    ((CommRingCat.isPushout_tensorProduct A S Γ(X, ⊤)).isoPushout ≪≫
      (originalSectionSquare (S := S) f).flip.isoPushout.symm).hom) b = _
  simp only [Iso.trans_hom, Iso.symm_hom, IsPushout.inr_isoPushout_hom_assoc,
    IsPushout.inr_isoPushout_inv]


/-- Every original pure tensor retains BOTH complete coefficient/section maps. -/
theorem tensorEquiv_tmul [Module.Flat A S] [QuasiCompact f] [QuasiSeparated f]
    (s : S) (b : Γ(X, ⊤)) :
    let : Algebra A Γ(X, ⊤) := sectionsAlgebra f
    tensorEquiv (S := S) f (s ⊗ₜ[A] b) =
      coefficientMap (structureMap (S := S) f) s *
        (firstProjection (S := S) f).appTop b := by
  let : Algebra A Γ(X, ⊤) := sectionsAlgebra f
  rw [show s ⊗ₜ[A] b = Algebra.TensorProduct.includeLeftRingHom s *
    Algebra.TensorProduct.includeRight b by simp, map_mul,
    tensorEquiv_includeLeft, tensorEquiv_includeRight]

/-- For an ACTUAL field extension, flatness is derived and the SAME original tensor map is an equivalence. -/
def fieldTensorEquiv {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K)) [QuasiCompact g] [QuasiSeparated g] :
    let : Algebra K Γ(Y, ⊤) := sectionsAlgebra g
    let : Algebra L Γ(baseChange (S := L) g, ⊤) := sectionsAlgebra (structureMap (S := L) g)
    L ⊗[K] Γ(Y, ⊤) ≃ₐ[L] Γ(baseChange (S := L) g, ⊤) := tensorEquiv g

end Hironaka.Geometry.ProperGeometricGlobalFunctions
