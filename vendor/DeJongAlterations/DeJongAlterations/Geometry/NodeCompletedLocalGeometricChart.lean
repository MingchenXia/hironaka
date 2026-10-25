import DeJongAlterations.Geometry.NodeCompletedLocalActualAffineUV
import DeJongAlterations.Algebra.NodeFittingOmegaCharts
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! The actual geometric pullback of an ORIGINAL affine source/base chart.
The scalar field map is produced from the ORIGINAL base germ, its ORIGINAL residue map,
and the actual field extension, with no point-residue-separability or model assumption. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace DeJongAlterations.Geometry.NodeCompletedLocalGeometricChart

open Algebra.NodeFittingOmegaCharts NodeCompletedLocalAffineBaseChangeUV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (C : Chart f)
  (s : S) (hs : s ∈ C.base.1) (K : Type u) [Field K] [Algebra (S.residueField s) K]

/-- The ENTIRE actual original-chart coefficient map to the geometric residue extension. -/
def chartCoefficient : Γ(S, C.base.1) ⟶ CommRingCat.of K :=
  S.presheaf.germ C.base.1 s hs ≫ S.residue s ≫
    CommRingCat.ofHom (algebraMap (S.residueField s) K)

/-- The actual field action of the original affine base chart, retaining the original base point. -/
@[instance_reducible]
def chartFieldAlgebra : Algebra Γ(S, C.base.1) K := (chartCoefficient f C s hs K).hom.toAlgebra

/-- The ORIGINAL geometric residue-extension morphism, prior to any affine chart choice. -/
def originalFieldMap : Spec (.of K) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫ S.fromSpecResidueField s

/-- Its ACTUAL factor through this original affine base, with the WHOLE original coefficients. -/
theorem chartFieldMap_source :
    Spec.map (chartCoefficient f C s hs K) ≫ C.base.2.fromSpec = originalFieldMap s K := by
  simp only [chartCoefficient, originalFieldMap, Scheme.fromSpecResidueField,
    Spec.map_comp, Category.assoc]
  rw [← C.base.2.fromSpecStalk_eq_fromSpecStalk hs]
  rfl

/-- The literal ACTUAL original geometric scheme pullback, independent of a chart. -/
abbrev OriginalGeometricScheme : Scheme.{u} := pullback f (originalFieldMap s K)

/-- The actual original affine chart-ring family map retains the original scheme square. -/
theorem chartRingFamily_source :
    letI := C.algebra f
    originalFamily Γ(S, C.base.1) Γ(X, C.source.1) ≫ C.base.2.fromSpec =
      C.source.2.fromSpec ≫ f :=
  IsAffineOpen.SpecMap_appLE_fromSpec f C.base.2 C.source.2 C.le_preimage

/-- The actual chart field-pullback has the exact source/field square over the original base. -/
theorem chartPullback_condition :
    letI := C.algebra f
    letI := chartFieldAlgebra f C s hs K
    pullback.fst (originalFamily Γ(S, C.base.1) Γ(X, C.source.1))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, C.base.1) K))) ≫
        C.source.2.fromSpec ≫ f =
      pullback.snd (originalFamily Γ(S, C.base.1) Γ(X, C.source.1))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, C.base.1) K))) ≫ originalFieldMap s K := by
  let := C.algebra f
  let := chartFieldAlgebra f C s hs K
  rw [← chartRingFamily_source f C]
  erw [pullback.condition_assoc]
  exact congrArg (fun p => pullback.snd
    (originalFamily Γ(S, C.base.1) Γ(X, C.source.1))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, C.base.1) K))) ≫ p)
    (chartFieldMap_source f C s hs K)

/-- The ACTUAL native map from the original affine geometric chart to the original
geometric scheme pullback; no supplied scheme or stalk comparison is input. -/
def chartMap :
    letI := C.algebra f
    letI := chartFieldAlgebra f C s hs K
    ActualBaseChange Γ(S, C.base.1) Γ(X, C.source.1) K ⟶ OriginalGeometricScheme f s K := by
  letI := C.algebra f
  letI := chartFieldAlgebra f C s hs K
  exact pullback.lift (pullback.fst _ _ ≫ C.source.2.fromSpec) (pullback.snd _ _)
    (chartPullback_condition f C s hs K)

/-- The ENTIRE actual original-source projection is retained. -/
theorem chartMap_source :
    letI := C.algebra f
    letI := chartFieldAlgebra f C s hs K
    chartMap f C s hs K ≫ pullback.fst f (originalFieldMap s K) =
      pullback.fst _ _ ≫ C.source.2.fromSpec := by
  exact pullback.lift_fst _ _ _

/-- The ENTIRE actual geometric-field projection is retained. -/
theorem chartMap_field :
    letI := C.algebra f
    letI := chartFieldAlgebra f C s hs K
    chartMap f C s hs K ≫ pullback.snd f (originalFieldMap s K) = pullback.snd _ _ := by
  exact pullback.lift_snd _ _ _

/-- This ACTUAL geometric affine-chart map is the literal base change of the ORIGINAL
source affine-open embedding, as a proved native pullback square. -/
theorem chartMap_isPullback :
    letI := C.algebra f
    letI := chartFieldAlgebra f C s hs K
    IsPullback (chartMap f C s hs K) (pullback.fst _ _)
      (pullback.fst f (originalFieldMap s K)) C.source.2.fromSpec := by
  let := C.algebra f
  let := chartFieldAlgebra f C s hs K
  let β := originalFamily Γ(S, C.base.1) Γ(X, C.source.1)
  let g := Spec.map (chartCoefficient f C s hs K)
  have hr : IsPullback (𝟙 (Spec Γ(X, C.source.1))) β (C.source.2.fromSpec ≫ f)
      C.base.2.fromSpec :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa using (chartRingFamily_source f C).symm⟩
  have hb : IsPullback (pullback.fst β g) (pullback.snd β g)
      (C.source.2.fromSpec ≫ f) (originalFieldMap s K) := by
    have h := (IsPullback.of_hasPullback β g).paste_horiz hr
    have hgp : g ≫ C.base.2.fromSpec = originalFieldMap s K := chartFieldMap_source f C s hs K
    erw [Category.comp_id, hgp] at h
    exact h
  have ho : IsPullback (pullback.fst β g)
      (chartMap f C s hs K ≫ pullback.snd f (originalFieldMap s K))
      (C.source.2.fromSpec ≫ f) (originalFieldMap s K) := by
    rw [chartMap_field]
    exact hb
  exact (IsPullback.of_bot ho (chartMap_source f C s hs K).symm
    (IsPullback.of_hasPullback f (originalFieldMap s K))).flip

/-- It is therefore an actual OPEN immersion, internally, with no target model assumption. -/
theorem chartMap_isOpenImmersion :
    letI := C.algebra f
    letI := chartFieldAlgebra f C s hs K
    IsOpenImmersion (chartMap f C s hs K) := by
  let := C.algebra f
  let := chartFieldAlgebra f C s hs K
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (chartMap_isPullback f C s hs K).flip inferInstance

/-- The exact range is the preimage of the ORIGINAL affine source open, internally. -/
theorem chartMap_range :
    letI := C.algebra f
    letI := chartFieldAlgebra f C s hs K
    Set.range (chartMap f C s hs K) =
      (pullback.fst f (originalFieldMap s K)) ⁻¹' (C.source.1 : Set X) := by
  let := C.algebra f
  let := chartFieldAlgebra f C s hs K
  let H := chartMap_isPullback f C s hs K
  calc
    Set.range (chartMap f C s hs K) =
        Set.range (pullback.fst (pullback.fst f (originalFieldMap s K)) C.source.2.fromSpec) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        refine ⟨H.isoPullback.hom z, ?_⟩
        change (H.isoPullback.hom ≫ pullback.fst _ _) z = _
        rw [H.isoPullback_hom_fst]
      · rintro ⟨p, hp⟩
        refine ⟨H.isoPullback.inv p, ?_⟩
        change (H.isoPullback.inv ≫ chartMap f C s hs K) p = _
        rw [H.isoPullback_inv_fst]
        exact hp
    _ = _ := by rw [Scheme.Pullback.range_fst, IsAffineOpen.range_fromSpec]

/-- Every ACTUAL geometric point over this ORIGINAL chart lifts uniquely to its ACTUAL
affine geometric chart; this is constructed from the proved range and open immersion. -/
theorem existsUnique_chartPoint (y : OriginalGeometricScheme f s K)
    (hx : pullback.fst f (originalFieldMap s K) y ∈ C.source.1) :
    letI := C.algebra f
    letI := chartFieldAlgebra f C s hs K
    ∃! z : ActualBaseChange Γ(S, C.base.1) Γ(X, C.source.1) K,
      chartMap f C s hs K z = y := by
  let := C.algebra f
  let := chartFieldAlgebra f C s hs K
  let : IsOpenImmersion (chartMap f C s hs K) := chartMap_isOpenImmersion f C s hs K
  have hy : y ∈ Set.range (chartMap f C s hs K) := by
    rw [chartMap_range]
    exact hx
  obtain ⟨z, hz⟩ := hy
  exact ⟨z, hz, fun z' hz' => (chartMap f C s hs K).isOpenEmbedding.injective (hz'.trans hz.symm)⟩

/-- Original locally finite type gives finite type of this SAME ORIGINAL chart algebra. -/
theorem chartAlgebra_finiteType [LocallyOfFiniteType f] :
    letI := C.algebra f
    Algebra.FiniteType Γ(S, C.base.1) Γ(X, C.source.1) :=
  f.finiteType_appLE C.base.2 C.source.2 C.le_preimage

end DeJongAlterations.Geometry.NodeCompletedLocalGeometricChart
