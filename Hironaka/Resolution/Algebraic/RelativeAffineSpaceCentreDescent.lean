import Hironaka.Resolution.Algebraic.ActualPaddedEnvelopeNativeTranslations
import Hironaka.Resolution.Algebraic.MvPolynomialCoordinateTranslationDescent
import Hironaka.Resolution.Algebraic.ActualNativeTailTranslationTransport
import Hironaka.Scheme.BlowUp.Composite.ChartIdeal
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InverseImage

/-!
# Current relative-affine centre descent over arbitrary actual k-schemes

Source-first proof: `relative-affine-space-centre-descent-20261102.tex`.
The current base need not be an affine dimension-separation blowup.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace Hironaka.Resolution.Algebraic.RelativeAffineSpaceCentreDescent

noncomputable section
open ActualPaddedEnvelopeNativeTranslations MvPolynomialCoordinateTranslationDescent
open MvPolynomial
open scoped Classical

section Spectrum
variable {A B : Type u} [CommRing A] [CommRing B]

private theorem appTop_specMap_gamma_inv (φ : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (Scheme.ΓSpecIso (.of B)).inv (φ a) := by
  rw [Scheme.IdealSheafData.appTop_Spec_map]
  change (Scheme.ΓSpecIso (.of B)).inv
      (φ ((Scheme.ΓSpecIso (.of A)).hom ((Scheme.ΓSpecIso (.of A)).inv a))) = _
  have ha : (Scheme.ΓSpecIso (.of A)).hom ((Scheme.ΓSpecIso (.of A)).inv a) = a :=
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.apply_symm_apply a
  rw [ha]

private def spectrumIdeal (D : (Spec (.of A)).IdealSheafData) : Ideal A :=
  (D.ideal ⟨⊤, isAffineOpen_top _⟩).comap (Scheme.ΓSpecIso (.of A)).inv.hom

private theorem specIdealSheaf_spectrumIdeal (D : (Spec (.of A)).IdealSheafData) :
    specIdealSheaf (spectrumIdeal D) = D := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [specIdealSheaf_ideal_top]
  exact Ideal.map_comap_of_surjective _
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.surjective _

private theorem specIdealSheaf_comap_specMap (J : Ideal A) (φ : A →+* B) :
    (specIdealSheaf J).comap (Spec.map (CommRingCat.ofHom φ)) = specIdealSheaf (J.map φ) :=
  Scheme.IdealSheafData.comap_ofIdealTop_Spec_map _ _

private theorem polynomial_spectrum_zero_section_descent (K : Type u)
    [Field K] [CharZero K] [Algebra K A] (σ : Type u) [Finite σ]
    (D : (Spec (.of (MvPolynomial σ A))).IdealSheafData)
    (hshift : ∀ j, D.comap (Spec.map (CommRingCat.ofHom (coordinateShift j))) = D) :
    D = (D.comap (Spec.map (CommRingCat.ofHom
      (eval (fun _ : σ => (0 : A)))))).comap
        (Spec.map (CommRingCat.ofHom (C : A →+* MvPolynomial σ A))) := by
  let J := spectrumIdeal D
  have hJ : specIdealSheaf J = D := specIdealSheaf_spectrumIdeal D
  have hj : ∀ j, J.map (coordinateShift j) = J := by
    intro j
    apply specIdealSheaf_inj
    rw [← specIdealSheaf_comap_specMap, hJ, hshift j]
  have hs : ∀ j, ∀ f ∈ J, coordinateShift j f ∈ J := by
    intro j f hf
    rw [← hj j]
    exact Ideal.mem_map_of_mem _ hf
  have hd := ideal_eq_extension_of_zero_section_of_coordinate_shift_stable K σ J hs
  rw [← hJ, specIdealSheaf_comap_specMap, specIdealSheaf_comap_specMap, ← hd]
end Spectrum

section CoordinateGeometry
variable (σ : Type u) (X Y : Scheme.{u})

private theorem translation_coord (v : σ → ℤ) (i : σ) :
    (affineTranslation σ X v).hom.appTop (AffineSpace.coord X i) =
      AffineSpace.coord X i + (v i : Γ(AffineSpace σ X, ⊤)) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

private theorem translation_natural (f : X ⟶ Y) (v : σ → ℤ) :
    (affineTranslation σ X v).hom ≫ AffineSpace.map σ f =
      AffineSpace.map σ f ≫ (affineTranslation σ Y v).hom := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, AffineSpace.map_over, affineTranslation_projection]
    rw [← Category.assoc, affineTranslation_projection]
  · intro i
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.map_appTop_coord, translation_coord, map_add, map_intCast]

private def polynomialIntegerTranslation {A : Type u} [CommRing A] (v : σ → ℤ) :
    MvPolynomial σ A →+* MvPolynomial σ A :=
  eval₂Hom C (fun i => MvPolynomial.X i + (v i : MvPolynomial σ A))

private theorem specIso_translation {A : Type u} [CommRing A] (v : σ → ℤ) :
    Spec.map (CommRingCat.ofHom (polynomialIntegerTranslation σ v (A := A))) ≫
        (AffineSpace.SpecIso σ (.of A)).inv =
      (AffineSpace.SpecIso σ (.of A)).inv ≫ (affineTranslation σ (Spec (.of A)) v).hom := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, affineTranslation_projection, AffineSpace.SpecIso_inv_over]
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp [polynomialIntegerTranslation]
  · intro i
    change (Spec.map (CommRingCat.ofHom (polynomialIntegerTranslation σ v (A := A)))).appTop
        ((AffineSpace.SpecIso σ (.of A)).inv.appTop (AffineSpace.coord (Spec (.of A)) i)) =
      (AffineSpace.SpecIso σ (.of A)).inv.appTop
        ((affineTranslation σ (Spec (.of A)) v).hom.appTop (AffineSpace.coord (Spec (.of A)) i))
    rw [AffineSpace.SpecIso_inv_appTop_coord, translation_coord, map_add, map_intCast,
      AffineSpace.SpecIso_inv_appTop_coord, appTop_specMap_gamma_inv]
    simp [polynomialIntegerTranslation]

private theorem specIso_zero_section {A : Type u} [CommRing A] :
    Spec.map (CommRingCat.ofHom (eval (fun _ : σ => (0 : A)))) ≫
        (AffineSpace.SpecIso σ (.of A)).inv =
      AffineSpace.homOfVector (𝟙 (Spec (.of A))) (fun _ : σ => 0) := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, AffineSpace.SpecIso_inv_over, AffineSpace.homOfVector_over]
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom (C : A →+* MvPolynomial σ A) ≫
        CommRingCat.ofHom (eval (fun _ : σ => (0 : A))) = 𝟙 (CommRingCat.of A) := by
      ext a
      simp
    rw [h]
    simp
  · intro i
    change (Spec.map (CommRingCat.ofHom (eval (fun _ : σ => (0 : A))))).appTop
        ((AffineSpace.SpecIso σ (.of A)).inv.appTop (AffineSpace.coord (Spec (.of A)) i)) = _
    rw [AffineSpace.SpecIso_inv_appTop_coord, appTop_specMap_gamma_inv,
      AffineSpace.homOfVector_appTop_coord]
    simp

private theorem zero_section_natural (f : X ⟶ Y) :
    AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0) ≫ AffineSpace.map σ f =
      f ≫ AffineSpace.homOfVector (𝟙 Y) (fun _ : σ => 0) := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, AffineSpace.map_over, AffineSpace.homOfVector_over,
      Category.comp_id]
    rw [← Category.assoc, AffineSpace.homOfVector_over, Category.id_comp]
  · intro i
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.map_appTop_coord, AffineSpace.homOfVector_appTop_coord, map_zero]
end CoordinateGeometry

section CurrentBase
variable {X : Scheme.{u}} (σ : Type u) (C₀ : X.AffineOpenCover)

private def relativeChart (i : C₀.I₀) :
    Spec (.of (MvPolynomial σ (C₀.X i))) ⟶ AffineSpace σ X :=
  (AffineSpace.SpecIso σ (C₀.X i)).inv ≫ AffineSpace.map σ (C₀.f i)

private instance affineMap_cover_isOpenImmersion (i : C₀.I₀) :
    IsOpenImmersion (AffineSpace.map σ (C₀.f i)) :=
  property_of_isPullback _ (AffineSpace.isPullback_map (n := σ) (C₀.f i)) inferInstance

private instance relativeChart_isOpenImmersion (i : C₀.I₀) :
    IsOpenImmersion (relativeChart σ C₀ i) := by
  dsimp only [relativeChart]
  infer_instance

private theorem relativeChart_range (i : C₀.I₀) :
    Set.range (relativeChart σ C₀ i) =
      (AffineSpace σ X ↘ X) ⁻¹' Set.range (C₀.f i) := by
  change ((relativeChart σ C₀ i).opensRange : Set (AffineSpace σ X)) = _
  dsimp only [relativeChart]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact range_fst_of_isPullback (AffineSpace.isPullback_map (n := σ) (C₀.f i))

/-- The actual relative polynomial affine open cover over an arbitrary current
scheme base. No dimension-separation origin is required. -/
def relativeAffineOpenCover : (AffineSpace σ X).AffineOpenCover where
  I₀ := C₀.I₀
  X i := .of (MvPolynomial σ (C₀.X i))
  f i := relativeChart σ C₀ i
  idx x := C₀.idx ((AffineSpace σ X ↘ X) x)
  covers x := by
    rw [relativeChart_range]
    exact C₀.covers ((AffineSpace σ X ↘ X) x)

private theorem relativeChart_projection (i : C₀.I₀) :
    relativeChart σ C₀ i ≫ (AffineSpace σ X ↘ X) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : C₀.X i →+* MvPolynomial σ (C₀.X i))) ≫
        C₀.f i := by
  rw [relativeChart, Category.assoc, AffineSpace.map_over,
    ← Category.assoc, AffineSpace.SpecIso_inv_over]

private theorem relativeChart_zero_section (i : C₀.I₀) :
    C₀.f i ≫ AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0) =
      Spec.map (CommRingCat.ofHom (eval (fun _ : σ => (0 : C₀.X i)))) ≫ relativeChart σ C₀ i := by
  have hz : Spec.map (CommRingCat.ofHom (eval (fun _ : σ => (0 : C₀.X i)))) ≫
      (AffineSpace.SpecIso σ (C₀.X i)).inv =
        AffineSpace.homOfVector (𝟙 (Spec (C₀.X i))) (fun _ : σ => 0) :=
    specIso_zero_section σ (A := C₀.X i)
  rw [relativeChart, ← Category.assoc, hz]
  exact (zero_section_natural σ (Spec (C₀.X i)) X (C₀.f i)).symm

private theorem relativeChart_translation (i : C₀.I₀) (v : σ → ℤ) :
    Spec.map (CommRingCat.ofHom (polynomialIntegerTranslation σ v (A := C₀.X i))) ≫
        relativeChart σ C₀ i =
      relativeChart σ C₀ i ≫ (affineTranslation σ X v).hom := by
  have ht : Spec.map (CommRingCat.ofHom (polynomialIntegerTranslation σ v (A := C₀.X i))) ≫
      (AffineSpace.SpecIso σ (C₀.X i)).inv =
        (AffineSpace.SpecIso σ (C₀.X i)).inv ≫ (affineTranslation σ (Spec (C₀.X i)) v).hom :=
    specIso_translation σ v
  rw [relativeChart, ← Category.assoc, ht]
  simp only [Category.assoc, translation_natural]

private theorem polynomialIntegerTranslation_coordinate {A : Type u} [CommRing A] (j : σ) :
    polynomialIntegerTranslation σ (fun i => if i = j then 1 else 0) (A := A) = coordinateShift j := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [polynomialIntegerTranslation, coordinateShift]
  · intro i
    by_cases hij : i = j <;> simp [polynomialIntegerTranslation, coordinateShift, hij]

private theorem chart_centre_descends (k : Type u) [Field k] [CharZero k] (f : X ⟶ Spec (.of k))
    [Finite σ] (D : (AffineSpace σ X).IdealSheafData)
    (hD : ∀ v : σ → ℤ, D.comap (affineTranslation σ X v).hom = D) (i : C₀.I₀) :
    D.comap (relativeChart σ C₀ i) =
      ((D.comap (AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0))).comap
        (AffineSpace σ X ↘ X)).comap (relativeChart σ C₀ i) := by
  let φ : k →+* C₀.X i := (Scheme.ΓSpecIso (C₀.X i)).hom.hom.comp
    ((C₀.f i ≫ f).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  let : Algebra k (C₀.X i) := φ.toAlgebra
  have hs : ∀ j, (D.comap (relativeChart σ C₀ i)).comap
      (Spec.map (CommRingCat.ofHom (coordinateShift j))) = D.comap (relativeChart σ C₀ i) := by
    intro j
    have h := relativeChart_translation σ C₀ i (fun a => if a = j then 1 else 0)
    rw [polynomialIntegerTranslation_coordinate] at h
    rw [← Scheme.IdealSheafData.comap_comp, h, Scheme.IdealSheafData.comap_comp, hD]
  have hl := polynomial_spectrum_zero_section_descent k σ (D.comap (relativeChart σ C₀ i)) hs
  have hp : relativeChart σ C₀ i ≫ (AffineSpace σ X ↘ X) ≫
      AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : C₀.X i →+* MvPolynomial σ (C₀.X i))) ≫
          Spec.map (CommRingCat.ofHom (eval (fun _ : σ => (0 : C₀.X i)))) ≫ relativeChart σ C₀ i := by
    rw [← Category.assoc, relativeChart_projection, Category.assoc, relativeChart_zero_section]
  calc
    D.comap (relativeChart σ C₀ i) = _ := hl
    _ = D.comap (relativeChart σ C₀ i ≫ (AffineSpace σ X ↘ X) ≫
        AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0)) := by
      rw [hp]
      simp only [Scheme.IdealSheafData.comap_comp]
    _ = _ := by simp only [Scheme.IdealSheafData.comap_comp]

/-- The actual invariant current centre descends over ANY current k-scheme.
Its base ideal is its OWN actual zero-section pullback. -/
theorem relativeAffineSpace_centre_descends (k : Type u) [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [Finite σ] (D : (AffineSpace σ X).IdealSheafData)
    (hD : ∀ v : σ → ℤ, D.comap (affineTranslation σ X v).hom = D) :
    D = (D.comap (AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0))).comap (AffineSpace σ X ↘ X) := by
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro x
  let C₀ := X.affineOpenCover
  obtain ⟨i,y,rfl⟩ := (relativeAffineOpenCover σ C₀).openCover.exists_eq x
  have h := chart_centre_descends σ C₀ k f D hD i
  have hs := congrArg (fun J => J.stalkIdeal y) h
  rw [Scheme.IdealSheafData.stalkIdeal_comap, Scheme.IdealSheafData.stalkIdeal_comap] at hs
  have hc := congrArg (fun I => I.comap ((relativeChart σ C₀ i).stalkMap y).hom) hs
  have hp : ((relativeAffineOpenCover σ C₀).openCover.f i) y = relativeChart σ C₀ i y := rfl
  rw [hp]
  simpa only [Scheme.Hom.comap_stalkMap_map_eq_self] using hc
end CurrentBase

section ProductStep
variable {X : Scheme.{u}} (σ : Type u) [Finite σ]

instance relativeProjection_smooth : Smooth (AffineSpace σ X ↘ X) := by
  have ht : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  have hp : SmoothOfRelativeDimension (Nat.card σ) (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (MvPolynomial σ (ULift.{u} ℤ))))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card σ))).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).mpr inferInstance))
  have : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (MvPolynomial σ (ULift.{u} ℤ))))) :=
    SmoothOfRelativeDimension.smooth (Nat.card σ) _
  have hm : Smooth (terminal.from (Spec (.of (MvPolynomial σ (ULift.{u} ℤ))))) := by
    rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (MvPolynomial σ (ULift.{u} ℤ)))))]
    infer_instance
  have : MorphismProperty.IsStableUnderBaseChange (@Smooth.{u}) := smooth_isStableUnderBaseChange
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Smooth.{u}) (IsPullback.of_hasPullback (terminal.from X)
      (terminal.from (Spec (.of (MvPolynomial σ (ULift.{u} ℤ)))))).flip hm

/-- The actual blowup product comparison is constructed from TWO genuine
cartesian squares; no product isomorphism is supplied. -/
def relativeBlowupProductIso (J : X.IdealSheafData) :
    (J.comap (AffineSpace σ X ↘ X)).blowUp ≅ AffineSpace σ J.blowUp :=
  (isPullback_blowUpMap (AffineSpace σ X ↘ X) J).isoPullback ≪≫
    (AffineSpace.isPullback_map (n := σ) J.blowUpπ).flip.isoPullback.symm

theorem relativeBlowupProductIso_projection (J : X.IdealSheafData) :
    (relativeBlowupProductIso σ J).hom ≫ (AffineSpace σ J.blowUp ↘ J.blowUp) =
      Scheme.Hom.blowUpMap (AffineSpace σ X ↘ X) J := by
  simp only [relativeBlowupProductIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]

theorem relativeBlowupProductIso_blowup (J : X.IdealSheafData) :
    (relativeBlowupProductIso σ J).hom ≫ AffineSpace.map σ J.blowUpπ =
      (J.comap (AffineSpace σ X ↘ X)).blowUpπ := by
  simp only [relativeBlowupProductIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_snd, IsPullback.isoPullback_hom_snd]

/-- The current product is produced from the current ACTUAL centre and its
derived zero-section identity over an arbitrary current base. -/
def currentCentreProductIso (k : Type u) [Field k] [CharZero k] (f : X ⟶ Spec (.of k))
    (D : (AffineSpace σ X).IdealSheafData)
    (hD : ∀ v : σ → ℤ, D.comap (affineTranslation σ X v).hom = D) :
    D.blowUp ≅ AffineSpace σ (D.comap (AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0))).blowUp :=
  eqToIso (congrArg Scheme.IdealSheafData.blowUp
    (relativeAffineSpace_centre_descends σ k f D hD)) ≪≫
      relativeBlowupProductIso σ (D.comap (AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0)))

theorem currentCentreProductIso_blowup (k : Type u) [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) (D : (AffineSpace σ X).IdealSheafData)
    (hD : ∀ v : σ → ℤ, D.comap (affineTranslation σ X v).hom = D) :
    (currentCentreProductIso σ k f D hD).hom ≫
      AffineSpace.map σ (D.comap (AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0))).blowUpπ =
        D.blowUpπ := by
  simp only [currentCentreProductIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    relativeBlowupProductIso_blowup]
  exact eqToHom_comp_blowUpπ (relativeAffineSpace_centre_descends σ k f D hD)

/-- The SAME remaining tail acquires its actual new product presentation and
translation law by blowup uniqueness, without a new resolution run. -/
theorem current_relative_product_tail_step (k : Type u) [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) (D : (AffineSpace σ X).IdealSheafData)
    (T : D.blowUp.BlowUpSequence)
    (h : ∀ v : σ → ℤ, Scheme.BlowUpSequence.cons (AffineSpace σ X) D T =
      (Scheme.BlowUpSequence.cons (AffineSpace σ X) D T).pullback (affineTranslation σ X v).hom) :
    let J := D.comap (AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0))
    ∃ e : D.blowUp ≅ AffineSpace σ J.blowUp,
      e.hom ≫ AffineSpace.map σ J.blowUpπ = D.blowUpπ ∧
      ∀ v : σ → ℤ, T.pullback e.inv =
        (T.pullback e.inv).pullback (affineTranslation σ J.blowUp v).hom := by
  let J := D.comap (AffineSpace.homOfVector (𝟙 X) (fun _ : σ => 0))
  have hD : ∀ v : σ → ℤ, D.comap (affineTranslation σ X v).hom = D :=
    fun v => (Scheme.BlowUpSequence.cons.inj (h v)).1.symm
  let e := currentCentreProductIso σ k f D hD
  have he : e.hom ≫ AffineSpace.map σ J.blowUpπ = D.blowUpπ :=
    currentCentreProductIso_blowup σ k f D hD
  refine ⟨e,he,?_⟩
  intro v
  have hei : e.inv ≫ D.blowUpπ = AffineSpace.map σ J.blowUpπ := by
    rw [← he, Iso.inv_hom_id_assoc]
  let t := e.hom ≫ (affineTranslation σ J.blowUp v).hom ≫ e.inv
  have ht : t ≫ D.blowUpπ = D.blowUpπ ≫ (affineTranslation σ X v).hom := by
    dsimp only [t]
    rw [Category.assoc, Category.assoc, hei, translation_natural, ← Category.assoc, he]
  have hT := ActualNativeTailTranslationTransport.same_tail_eq_pullback_of_geometric_lift D T
    (affineTranslation σ X v).hom (h v) t ht
  have hc := congrArg (fun S => S.pullback e.inv) hT
  simpa only [← pullback_comp, t, Category.assoc, Iso.inv_hom_id_assoc] using hc
end ProductStep

end
end Hironaka.Resolution.Algebraic.RelativeAffineSpaceCentreDescent

