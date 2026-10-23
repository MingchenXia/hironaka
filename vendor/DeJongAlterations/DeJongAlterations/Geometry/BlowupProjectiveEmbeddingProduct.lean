import DeJongAlterations.Geometry.BlowupProjectiveEmbedding
import DeJongAlterations.Geometry.ProjectiveSpaceBaseChange

/-!
# The actual closed embedding of the native global blowup into a projective product

Native projective-space base change identifies each local product with actual
projective space over the original affine section ring. The specified Rees
presentation is therefore the actual local closed embedding. Pullback pasting
and the native target open cover prove the global closed immersion.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

noncomputable section

namespace DeJongAlterations.Geometry.BlowupProjectiveEmbedding

open ProjectiveIdeal BlowupGluing ProjectiveSpaceBaseChange

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {n m : ℕ}

/-- The actual original affine spectrum opens subordinate to projective coordinates cover X. -/
def subordinateBaseCover (j : X ⟶ projectiveSpace R n) : X.OpenCover :=
  Scheme.Cover.mkOfCovers (SubordinateAffineSite j)
    (fun U => Spec Γ(X, U.1.1)) (fun U => U.1.2.fromSpec) (by
      intro x
      have hx : j x ∈ ⨆ i : Fin (n + 1), nativeCoordinateOpen (R := R) i := by
        rw [iSup_nativeCoordinateOpen_eq_top]
        trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      obtain ⟨U, hU, hxU, hUi⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ j ⁻¹ᵁ nativeCoordinateOpen i from hi)
      have hxr : x ∈ hU.fromSpec.opensRange := by
        rw [hU.opensRange_fromSpec]
        exact hxU
      obtain ⟨y, hy⟩ := hxr
      exact ⟨⟨⟨U, hU⟩, i, hUi⟩, y, hy⟩)

variable (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) {d : ℕ} (hF : ∀ a, (F a).IsHomogeneous d)

local notation "D" => Scheme.IdealSheafData.comap
  (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J) j
local notation "T" => pullback p (projectiveSpaceStructure R m)
local notation "q" => projectiveBlowupMapOfForms p j J F hspan hF

/-- The pair of the actual native blowup map and the actual glued projective morphism. -/
def formsProductMap : blowup D ⟶ T :=
  pullback.lift (blowupStructure D) q (projectiveBlowupMapOfForms_structure p j J F hspan hF).symm

@[reassoc (attr := simp)]
theorem formsProductMap_fst : formsProductMap p j J F hspan hF ≫ pullback.fst _ _ =
    blowupStructure D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem formsProductMap_snd : formsProductMap p j J F hspan hF ≫ pullback.snd _ _ = q :=
  pullback.lift_snd _ _ _

/-- The actual target product chart over the original affine spectrum open. -/
abbrev ProductChart (U : SubordinateAffineSite j) :=
  pullback (pullback.fst p (projectiveSpaceStructure R m)) U.1.2.fromSpec

/-- On this target chart the original native projective-space coefficient square is Cartesian. -/
theorem productChart_isPullback (U : SubordinateAffineSite j) :
    IsPullback
      (pullback.fst (pullback.fst p (projectiveSpaceStructure R m)) U.1.2.fromSpec ≫
        pullback.snd p (projectiveSpaceStructure R m))
      (pullback.snd (pullback.fst p (projectiveSpaceStructure R m)) U.1.2.fromSpec)
      (projectiveSpaceStructure R m)
      (Spec.map (CommRingCat.ofHom (affineBaseCoefficients p ⟨U.1.1, U.1.2⟩))) := by
  have H := (IsPullback.of_hasPullback (pullback.fst p (projectiveSpaceStructure R m)) U.1.2.fromSpec).paste_horiz (IsPullback.of_hasPullback p (projectiveSpaceStructure R m)).flip
  rw [affineBaseCoefficients_structure]
  exact H

/-- The genuine target product chart is actual projective space over its affine section ring. -/
def productChartProjectiveIso (U : SubordinateAffineSite j) :
    ProductChart p j (m := m) U ≅ projectiveSpace Γ(X, U.1.1) m :=
  (productChart_isPullback p j U).isoIsPullback _ _
    (isPullback_projectiveCoefficientMap (affineBaseCoefficients p ⟨U.1.1, U.1.2⟩) m)

@[reassoc]
theorem productChartProjectiveIso_hom_coeff (U : SubordinateAffineSite j) :
    (productChartProjectiveIso p j (m := m) U).hom ≫
      projectiveCoefficientMap (affineBaseCoefficients p ⟨U.1.1, U.1.2⟩) m =
    pullback.fst (pullback.fst p (projectiveSpaceStructure R m)) U.1.2.fromSpec ≫
      pullback.snd p (projectiveSpaceStructure R m) :=
  (productChart_isPullback p j U).isoIsPullback_hom_fst _ _ _

@[reassoc]
theorem productChartProjectiveIso_hom_structure (U : SubordinateAffineSite j) :
    (productChartProjectiveIso p j (m := m) U).hom ≫ projectiveSpaceStructure Γ(X, U.1.1) m =
    pullback.snd (pullback.fst p (projectiveSpaceStructure R m)) U.1.2.fromSpec :=
  (productChart_isPullback p j U).isoIsPullback_hom_snd _ _ _

/-- The original local blowup maps into the actual target product chart. -/
def formsProductChartMap (U : SubordinateAffineSite j) :
    affineBlowup ((D).ideal ⟨U.1.1, U.1.2⟩) ⟶ ProductChart p j (m := m) U :=
  pullback.lift (chartInclusion D U.1 ≫ formsProductMap p j J F hspan hF)
    (affineBlowupStructure ((D).ideal ⟨U.1.1, U.1.2⟩)) (by
      rw [Category.assoc, formsProductMap_fst, chartInclusion_structure])

/-- Under the native product identification, the actual local map is the original Rees embedding. -/
theorem formsProductChartMap_eq_embedding (U : SubordinateAffineSite j) :
    formsProductChartMap p j J F hspan hF U ≫ (productChartProjectiveIso p j (m := m) U).hom =
      affineGeneratorEmbedding ((D).ideal ⟨U.1.1, U.1.2⟩)
        (fun a => pulledForm j ⟨U.1.1, U.1.2⟩ (subordinateCoordinate j U)
          (subordinateCoordinate_le j U) (F a))
        (pulledForm_span_fin j ⟨U.1.1, U.1.2⟩ J F hspan
          (subordinateCoordinate j U) (subordinateCoordinate_le j U)) := by
  apply (isPullback_projectiveCoefficientMap (affineBaseCoefficients p ⟨U.1.1, U.1.2⟩) m).hom_ext
  · rw [Category.assoc, productChartProjectiveIso_hom_coeff,
      ← Category.assoc, formsProductChartMap, pullback.lift_fst,
      Category.assoc, formsProductMap_snd, projectiveBlowupMapOfForms_restrict]
    rfl
  · rw [Category.assoc, productChartProjectiveIso_hom_structure,
      formsProductChartMap, pullback.lift_snd, affineGeneratorEmbedding_structure]

/-- Each native local map to the original product chart is a genuine closed immersion. -/
instance formsProductChartMap_isClosedImmersion (U : SubordinateAffineSite j) :
    IsClosedImmersion (formsProductChartMap p j J F hspan hF U) := by
  have : IsClosedImmersion (formsProductChartMap p j J F hspan hF U ≫
      (productChartProjectiveIso p j (m := m) U).hom) := by
    rw [formsProductChartMap_eq_embedding]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (productChartProjectiveIso p j (m := m) U).hom

/-- This actual chart of the global product map is its native pullback square. -/
theorem formsProductChartMap_isPullback (U : SubordinateAffineSite j) :
    IsPullback (formsProductChartMap p j J F hspan hF U) (chartInclusion D U.1)
      (pullback.fst (pullback.fst p (projectiveSpaceStructure R m)) U.1.2.fromSpec)
      (formsProductMap p j J F hspan hF) := by
  have H : IsPullback
      (formsProductChartMap p j J F hspan hF U ≫
        pullback.snd (pullback.fst p (projectiveSpaceStructure R m)) U.1.2.fromSpec)
      (chartInclusion D U.1) U.1.2.fromSpec
      (formsProductMap p j J F hspan hF ≫ pullback.fst p (projectiveSpaceStructure R m)) := by
    simpa only [formsProductChartMap, pullback.lift_snd, formsProductMap_fst] using isPullback_chart D U.1
  exact H.of_right (by simp only [formsProductChartMap, pullback.lift_fst])
    (IsPullback.of_hasPullback (pullback.fst p (projectiveSpaceStructure R m)) U.1.2.fromSpec).flip

/-- The pair to the actual product is globally a closed immersion by its native affine charts. -/
instance formsProductMap_isClosedImmersion : IsClosedImmersion (formsProductMap p j J F hspan hF) := by
  let C : (T).OpenCover := (subordinateBaseCover j).pullback₁ (pullback.fst p (projectiveSpaceStructure R m))
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) C
  intro U
  let e := (formsProductChartMap_isPullback p j J F hspan hF U).flip.isoPullback
  have heq : C.pullbackHom (formsProductMap p j J F hspan hF) U =
      e.inv ≫ formsProductChartMap p j J F hspan hF U := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (formsProductChartMap_isPullback p j J F hspan hF U).flip.isoPullback_hom_snd
  rw [heq]
  infer_instance

/-- Actual projective embeddings over a Noetherian ring produce an actual closed product embedding
of the original native ideal-sheaf blowup, with both original structure projections. -/
theorem exists_closedProductEmbedding [IsNoetherianRing R] (D₀ : X.IdealSheafData)
    [IsClosedImmersion j] :
    ∃ (m : ℕ) (q₀ : blowup D₀ ⟶ projectiveSpace R m)
      (e : blowup D₀ ⟶ pullback p (projectiveSpaceStructure R m)),
      IsClosedImmersion e ∧ e ≫ pullback.fst _ _ = blowupStructure D₀ ∧
        e ≫ pullback.snd _ _ = q₀ := by
  obtain ⟨m, d, F, J, hF, hs, hD⟩ := exists_fin_sameDegree_representation D₀ j
  subst D₀
  exact ⟨m, projectiveBlowupMapOfForms p j J F hs hF,
    formsProductMap p j J F hs hF, inferInstance, formsProductMap_fst p j J F hs hF,
    formsProductMap_snd p j J F hs hF⟩

end DeJongAlterations.Geometry.BlowupProjectiveEmbedding
