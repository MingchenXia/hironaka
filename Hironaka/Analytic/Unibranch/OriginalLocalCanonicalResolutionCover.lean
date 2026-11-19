import Hironaka.Analytic.Unibranch.OriginalLocalCanonicalStrictResolution

/-!
# Actual canonical strict-resolution windows at every original point

The regular branch has a literal empty ambient blowup history and a full
native strict-space isomorphism. The singular branch retains the SAME actual
recipe and smooth-source fields supplied by the ordinary singular-point
producer. Different original embeddings are not compared here.

Blueprint FIRST: `original-local-canonical-resolution-cover.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalLocalCanonicalResolutionCover

noncomputable section

open Hironaka Hironaka.BlowupSequences
  Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceManifoldCharts HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaResolutionSpace
  HironakaResolutionSpaceComplex HironakaEmbeddedAnalytic
  HironakaOriginalIntrinsicNonpureRecipe HironakaOriginalLocalNonpureCanonicalResolution
  HironakaOriginalNonpureCanonicalSpecializations SourceReducedComplexSpace BlowupTowers
  OriginalLocalCanonicalStrictResolution

/-- Original regularity internally produces a literal whole-carrier local
embedding, restricted inside the prescribed original open. -/
theorem exists_whole_localEmbedding_of_regular (X : SourceReducedComplexSpace)
    (x : X.obj.left) (hx : x ∈ intrinsicRegularLocus X.obj)
    (O : Opens X.obj.left) (hxO : x ∈ O) :
    ∃ (e : LocalEmbedding X) (c : e.carrier),
      e.toPoint c = x ∧ range e.toPoint ⊆ (O : Set X.obj.left) ∧ e.carrier = univ := by
  obtain ⟨d, Ω, i, hi, hip, v, hv⟩ := hx
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let e₀ : LocalEmbedding X :=
    { dim := d
      ambient := Ω
      carrier := univ
      analytic := isComplexAnalyticSubset_univ
      map := (actualSubspaceUnivIso (n := d) (M := Ω)).hom ≫ i
      isOpenImmersion := by infer_instance
      overPoint := by
        rw [Category.assoc, hip]
        rfl }
  let P : Opens Ω := ⟨i.base ⁻¹' (O : Set X.obj.left),
    O.isOpen.preimage i.base.hom.continuous⟩
  have hvP : v ∈ P := by
    change i.base v ∈ O
    rw [hv]
    exact hxO
  let A : Opens (ComplexModel d) :=
    ⟨(Subtype.val : Ω → ComplexModel d) '' (P : Set Ω),
      Ω.isOpen.isOpenMap_subtype_val _ P.isOpen⟩
  have hA : A ≤ e₀.ambient := by
    rintro _ ⟨w, _hw, rfl⟩
    exact w.property
  have hC : ∀ z : A, z ∈ (univ : Set A) ↔ Opens.inclusion hA z ∈ e₀.carrier :=
    fun _ => Iff.rfl
  let e := e₀.restrictWith A hA univ hC
  have hvA : v.val ∈ A := ⟨v, hvP, rfl⟩
  let c : e.carrier := ⟨⟨v.val, hvA⟩, mem_univ _⟩
  refine ⟨e, c, ?_, ?_, rfl⟩
  · change e₀.toPoint ⟨Opens.inclusion hA c.val, _⟩ = x
    change i.base (Opens.inclusion hA c.val) = x
    exact hv
  · rintro _ ⟨z, rfl⟩
    change i.base (Opens.inclusion hA z.val) ∈ O
    obtain ⟨w, hwP, hwz⟩ := z.val.property
    have heq : w = Opens.inclusion hA z.val := Subtype.ext hwz
    exact heq ▸ hwP

/-- The literal empty ambient history, with no inserted blowup, resolves the
whole manifold by its actual strict transform. -/
theorem whole_refl_strictResolution {n : ℕ} (A : CMfd.{0} n) :
    IsStrictTransformResolution n (univ : Set A)
      (BlowupTower.refl : BlowupTower A A).proj [] := by
  have hSing : singularSet (n := n) (univ : Set A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact ha.2 (mem_iUnion.mpr ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ a⟩)
  have hStrict : strictTransform n (id : A → A) (univ : Set A) = univ := by
    simp [strictTransform]
  have hSM : IsClosedSubmanifold n (strictTransform n (id : A → A) (univ : Set A)) := by
    rw [hStrict]
    exact ⟨isClosed_univ, fun a _ => ⟨n, AnalyticIrreducibleComponents.regularAtDim_univ a⟩⟩
  have hAdm : HironakaAdmissibleSequence.IsAdmissibleBlowupSequence
      n A [] (singularSet (n := n) (univ : Set A)) A id [] := .refl
  exact isStrictTransformResolution_of_data isComplexAnalyticSubset_univ
    hAdm NormalCrossings.isSNCDivisor_nil
    (by simp) (by simp [hSing])
    (HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hAdm)
    hSM (by intro S hS; simpa using hS)

/-- For the SAME empty tower, the actual quotient projection is a full
native isomorphism induced by the ambient identity. -/
theorem resolutionMorphism_isIso_of_refl_whole
    {X : SourceReducedComplexSpace} (e : LocalEmbedding X) (U : Opens e.ambient)
    (hWhole : windowCarrier e U = univ)
    (h : IsStrictTransformResolution e.dim (windowCarrier e U)
      (BlowupTower.refl : BlowupTower (CMfd.of (n := e.dim) U) (CMfd.of (n := e.dim) U)).proj []) :
    IsIso (resolutionMorphism (windowCarrier_analytic e U) h) := by
  have hStrict : strictTransform e.dim (id : U → U) (windowCarrier e U) = windowCarrier e U := by
    simp [strictTransform, hWhole]
  let E := actualSubspaceBiholomorphicIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel e.dim) U ∞)
    (strictTransform e.dim (id : U → U) (windowCarrier e U)) (windowCarrier e U)
    (fun z => by rw [hStrict]; rfl)
  have hLeft : (resolutionMorphism (windowCarrier_analytic e U) h).hom.left = E.hom := rfl
  have hLeftIso : IsIso (resolutionMorphism (windowCarrier_analytic e U) h).hom.left := by
    rw [hLeft]
    infer_instance
  have : IsIso ((Over.forget complexPoint).map
      (resolutionMorphism (windowCarrier_analytic e U) h).hom) := hLeftIso
  have hOver : IsIso (resolutionMorphism (windowCarrier_analytic e U) h).hom :=
    isIso_of_reflects_iso _ (Over.forget complexPoint)
  have : IsIso ((ObjectProperty.ι _).map
      (resolutionMorphism (windowCarrier_analytic e U) h)) := hOver
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

/-- EVERY original point internally acquires a genuine strict-resolution
window: literal empty history at regular points, unchanged actual canonical
recipe and entire smooth-source data at singular points. -/
theorem exists_original_point_canonical_strict_window
    (X : SourceReducedComplexSpace) (x : X.obj.left)
    (O : Opens X.obj.left) (hxO : x ∈ O) :
    ∃ (e : LocalEmbedding X) (U : Opens e.ambient)
      (D : CMfd.{0} e.dim) (T : BlowupTower (CMfd.of (n := e.dim) U) D)
      (Ef : List (Set D))
      (h : IsStrictTransformResolution e.dim (windowCarrier e U) T.proj Ef),
      x ∈ range (windowMorphism e U).hom.left.base ∧
      range (windowMorphism e U).hom.left.base ⊆ (O : Set X.obj.left) ∧
      IsResolution (resolutionMorphism (windowCarrier_analytic e U) h) ∧
      Function.Surjective (resolutionMorphism (windowCarrier_analytic e U) h).hom.left.base ∧
      IsProperMap (resolutionMorphism (windowCarrier_analytic e U) h).hom.left.base ∧
      IsIsoOver (resolutionMorphism (windowCarrier_analytic e U) h)
        ((windowMorphism e U).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) ∧
      (∀ y : strictTransform e.dim T.proj (windowCarrier e U),
        ((resolutionMorphism (windowCarrier_analytic e U) h).hom.left.base y).val = T.proj y.val) ∧
      ((x ∈ intrinsicRegularLocus X.obj ∧ windowCarrier e U = univ ∧ T.length = 0 ∧ Ef = [] ∧
          IsIso (resolutionMorphism (windowCarrier_analytic e U) h)) ∨
        (x ∈ intrinsicSingularLocus X.obj ∧ IntrinsicOrderedRecipe (windowCarrier e U) [] T Ef ∧
          HasElementaryGeometry (windowCarrier e U) [] T Ef ∧
          RestrictEmptyTower.CentresOver (singularSet (n := e.dim) (windowCarrier e U)) T ∧
          HasIntrinsicSmoothSources (windowCarrier e U) [] T Ef ∧
          HasExactEmptyBoundarySmoothSources (windowCarrier e U) T Ef)) := by
  by_cases hx : x ∈ intrinsicRegularLocus X.obj
  · obtain ⟨e, c, hcx, heO, heWhole⟩ := exists_whole_localEmbedding_of_regular X x hx O hxO
    let U : Opens e.ambient := ⊤
    let A : CMfd.{0} e.dim := CMfd.of (n := e.dim) U
    let T : BlowupTower A A := .refl
    have hWhole : windowCarrier e U = univ := by
      ext z
      simp [windowCarrier, heWhole]
    let h : IsStrictTransformResolution e.dim (windowCarrier e U) T.proj [] := by
      rw [hWhole]
      exact whole_refl_strictResolution A
    have hProper : IsProperMap T.proj := HironakaLocalPrincipalization.isProperMap_proj T
    refine ⟨e, U, A, T, [], h, ?_, ?_,
      isResolution_resolutionMorphism_of_isProperMap (windowCarrier_analytic e U) h hProper,
      resolutionMap_surjective h,
      HironakaResolutionSpaceLocal.resolutionMap_isProperMap_of_isProperMap h hProper,
      resolutionMorphism_isIsoOver_originalRegularLocus e U h, fun _ => rfl,
      Or.inl ⟨hx, hWhole, rfl, rfl, resolutionMorphism_isIso_of_refl_whole e U hWhole h⟩⟩
    · refine ⟨⟨⟨c.val, mem_univ _⟩, c.property⟩, ?_⟩
      exact hcx
    · rintro _ ⟨z, rfl⟩
      exact heO ⟨⟨z.val.val, z.property⟩, rfl⟩
  · have hxSing : x ∈ intrinsicSingularLocus X.obj := hx
    obtain ⟨e, U, D, T, Ef, h, hxj, hjO, hRecipe, hGeom, hOver, hSources, hExact,
      hResolution, hSurj, hProper, hReg, hPoint⟩ :=
      exists_original_local_canonical_strict_resolution X x hxSing O hxO
    exact ⟨e, U, D, T, Ef, h, hxj, hjO, hResolution, hSurj, hProper, hReg, hPoint,
      Or.inr ⟨hxSing, hRecipe, hGeom, hOver, hSources, hExact⟩⟩

end
end Hironaka.Analytic.Unibranch.OriginalLocalCanonicalResolutionCover
