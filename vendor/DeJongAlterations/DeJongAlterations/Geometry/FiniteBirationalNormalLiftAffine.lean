import DeJongAlterations.Geometry.FiniteBirationalNormalFunctionField

/-!
# Actual affine lifts from common-field normalization

A finite dominant component morphism and a compatible function-field
embedding give actual coordinate maps into the integral closures.  No
scheme map, section, or desired commutative square is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T S : Scheme.{u}} [IsIntegral T] [IsIntegral S]
  (f : T ⟶ S) [IsDominant f] [IsFinite f]
  (L : Type u) [Field L] [Algebra S.functionField L]

attribute [local instance] NormalizationInExtension.sectionsAlgebra

/-- Dominance gives a genuinely nonempty inverse image of every nonempty affine open. -/
instance liftPreimage_nonempty (U : NormalizationInExtension.NonemptyAffineOpen S) :
    Nonempty (f ⁻¹ᵁ U.1.1) := by
  refine ⟨⟨genericPoint T, ?_⟩⟩
  change f (genericPoint T) ∈ U.1.1
  rw [genericPoint_map_of_isDominant f]
  exact ((genericPoint_spec S).mem_open_set_iff U.1.1.isOpen).mpr (by simpa using U.2)

variable (e : letI := functionFieldAlgebra f; T.functionField →ₐ[S.functionField] L)

/-- The original finite component's sections embed into the specified common field. -/
def affineLiftFieldMap (U : NormalizationInExtension.NonemptyAffineOpen S) :
    Γ(T, f ⁻¹ᵁ U.1.1) →+* L := by
  let := functionFieldAlgebra f
  exact e.toRingHom.comp (T.germToFunctionField (f ⁻¹ᵁ U.1.1)).hom

omit [IsFinite f] in
/-- The actual field map preserves the original affine coefficients. -/
theorem affineLiftFieldMap_coeff (U : NormalizationInExtension.NonemptyAffineOpen S) :
    (affineLiftFieldMap f L e U).comp (f.app U.1.1).hom =
      algebraMap Γ(S, U.1.1) L := by
  let := functionFieldAlgebra f
  ext r
  have h := congrArg (fun q : Γ(S, U.1.1) ⟶ T.functionField => e (q r))
    (NormalizationInExtension.functionFieldMap_sections f U.1.1)
  change e (NormalizationInExtension.functionFieldMap f (S.germToFunctionField U.1.1 r)) =
    e (T.germToFunctionField (f ⁻¹ᵁ U.1.1) (f.app U.1.1 r)) at h
  change e (T.germToFunctionField (f ⁻¹ᵁ U.1.1) (f.app U.1.1 r)) =
    algebraMap S.functionField L (S.germToFunctionField U.1.1 r)
  exact h.symm.trans (e.commutes _)

/-- Finiteness forces every actual affine component section into the actual closure. -/
def affineLiftMap (U : NormalizationInExtension.NonemptyAffineOpen S) :
    Γ(T, f ⁻¹ᵁ U.1.1) →+* NormalizationInExtension.closureRing L U := by
  let := (f.app U.1.1).hom.toAlgebra
  let : Module.Finite Γ(S, U.1.1) Γ(T, f ⁻¹ᵁ U.1.1) := f.finite_app U.1.1 U.1.2
  let q : Γ(T, f ⁻¹ᵁ U.1.1) →ₐ[Γ(S, U.1.1)] L :=
    { affineLiftFieldMap f L e U with
      commutes' := fun r => RingHom.congr_fun (affineLiftFieldMap_coeff f L e U) r }
  exact (affineLiftFieldMap f L e U).codRestrict _
    (fun a => (Algebra.IsIntegral.isIntegral a).map q)

@[simp]
theorem affineLiftMap_coe (U : NormalizationInExtension.NonemptyAffineOpen S)
    (a : Γ(T, f ⁻¹ᵁ U.1.1)) :
    (affineLiftMap f L e U a : L) = affineLiftFieldMap f L e U a := rfl

/-- The literal ring lift retains the original affine structure map. -/
theorem affineLiftMap_coeff (U : NormalizationInExtension.NonemptyAffineOpen S) :
    (affineLiftMap f L e U).comp (f.app U.1.1).hom =
      algebraMap Γ(S, U.1.1) (NormalizationInExtension.closureRing L U) := by
  ext r
  exact RingHom.congr_fun (affineLiftFieldMap_coeff f L e U) r

/-- The actual morphism from a common-field affine normalization to the component. -/
def affineLift (U : NormalizationInExtension.NonemptyAffineOpen S) :
    Spec (.of (NormalizationInExtension.closureRing L U)) ⟶ T :=
  Spec.map (CommRingCat.ofHom (affineLiftMap f L e U)) ≫ (U.1.2.preimage f).fromSpec

/-- The original morphism and its original affine normalization structure agree. -/
@[reassoc]
theorem affineLift_structure (U : NormalizationInExtension.NonemptyAffineOpen S) :
    affineLift f L e U ≫ f =
      NormalizationInExtension.affineStructure L U ≫ U.1.2.fromSpec := by
  rw [affineLift, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec f U.1.2 (U.1.2.preimage f) le_rfl,
    ← Scheme.Hom.app_eq_appLE, ← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext (affineLiftMap_coeff f L e U)

/-- The actual restriction on the inverse images of two base affine opens. -/
def liftRestriction {U V : NormalizationInExtension.NonemptyAffineOpen S} (h : U ⟶ V) :
    Γ(T, f ⁻¹ᵁ V.1.1) →+* Γ(T, f ⁻¹ᵁ U.1.1) :=
  (T.presheaf.map (homOfLE (f.preimage_mono
    (Scheme.AffineZariskiSite.toOpens_mono h.le))).op).hom

omit [IsFinite f] in
/-- The original coordinate restriction commutes with the actual generic germs. -/
theorem liftRestriction_functionField
    {U V : NormalizationInExtension.NonemptyAffineOpen S} (h : U ⟶ V) :
    (T.germToFunctionField (f ⁻¹ᵁ U.1.1)).hom.comp (liftRestriction f h) =
      (T.germToFunctionField (f ⁻¹ᵁ V.1.1)).hom := by
  change (T.presheaf.map _ ≫ T.germToFunctionField (f ⁻¹ᵁ U.1.1)).hom = _
  exact congrArg CommRingCat.Hom.hom (T.presheaf.germ_res
    (homOfLE (f.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono h.le)))
    (genericPoint T) _)

/-- Actual section restrictions and closure restrictions give the same literal ring map. -/
theorem affineLiftMap_naturality
    {U V : NormalizationInExtension.NonemptyAffineOpen S} (h : U ⟶ V) :
    (NormalizationInExtension.closureMap L h).comp (affineLiftMap f L e V) =
      (affineLiftMap f L e U).comp (liftRestriction f h) := by
  let := functionFieldAlgebra f
  ext a
  change e (T.germToFunctionField (f ⁻¹ᵁ V.1.1) a) =
    e (T.germToFunctionField (f ⁻¹ᵁ U.1.1) (liftRestriction f h a))
  exact congrArg e (RingHom.congr_fun (liftRestriction_functionField f h) a).symm

/-- The actual affine normalization maps glue over the entire original affine site. -/
theorem affineLift_naturality
    {U V : NormalizationInExtension.NonemptyAffineOpen S} (h : U ⟶ V) :
    Spec.map (CommRingCat.ofHom (NormalizationInExtension.closureMap L h)) ≫
      affineLift f L e V = affineLift f L e U := by
  unfold affineLift
  rw [← Spec.map_comp_assoc]
  have H : CommRingCat.ofHom (affineLiftMap f L e V) ≫
      CommRingCat.ofHom (NormalizationInExtension.closureMap L h) =
      CommRingCat.ofHom (liftRestriction f h) ≫
        CommRingCat.ofHom (affineLiftMap f L e U) :=
    CommRingCat.hom_ext (affineLiftMap_naturality f L e h)
  rw [H, Spec.map_comp, Category.assoc]
  exact congrArg (fun q => Spec.map (CommRingCat.ofHom (affineLiftMap f L e U)) ≫ q)
    ((V.1.2.preimage f).map_fromSpec (U.1.2.preimage f)
      (homOfLE (f.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono h.le))).op)

end DeJongAlterations.Geometry.FiniteBirationalNormal
