import DeJongAlterations.Geometry.AlgebraicFieldFiniteModelRefinement
import DeJongAlterations.Geometry.ProjectiveSpaceBaseChange
import DeJongAlterations.Geometry.FiniteProjectivePreservation
import DeJongAlterations.StableModification.Limits.SpreadModificationProjective

/-! Actual original projectivity INTERNALLY produces projectivity on the SAME finite field model. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlgebraicFieldFiniteProjectiveModel

open StableModification.Limits AlgebraicFieldFiniteModel AlgebraicFieldFiniteModelRefinement
  ProjectiveSpaceBaseChange BlowupProjectiveEmbedding

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]

/-- Actual projective space has its SAME canonical model at EVERY finite field level. -/
def projectiveModel (n : ℕ) (i : Index k L) :
    Model (diagram k L) (scalarCone k L) (projectiveSpaceStructure L n) i where
  Y := projectiveSpace (levelField k L i) n
  fY := projectiveSpaceStructure (levelField k L i) n
  g := projectiveCoefficientMap (levelField k L i).val.toRingHom n
  isPullback := by
    rw [scalarCone_π]
    exact isPullback_projectiveCoefficientMap _ _

/-- Original finite-level projective-space geometry proves actual finite presentation. -/
theorem projectiveModel_isFP (n : ℕ) (i : Index k L) : (projectiveModel k L n i).IsFP := by
  let : LocallyOfFinitePresentation (projectiveSpaceStructure (levelField k L i) n) :=
    SpreadModification.locallyOfFinitePresentation_of_locallyOfFiniteType _
  dsimp only [Model.IsFP, projectiveModel]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Original actual projectivity INTERNALLY produces an ACTUAL projective embedding on a further
base change of the SAME model. No finite-model embedding or projectivity certificate is assumed. -/
theorem exists_projective_refinement {Y : Scheme.{u}} {p : Y ⟶ Spec (.of L)}
    (hp : IsProjectiveOver p) {i : Index k L}
    (m : Model (diagram k L) (scalarCone k L) p i) (hm : m.IsFP) :
    ∃ (j : Index k L) (h : j ⟶ i),
      IsProjectiveOver (k := levelField k L j) (m.baseChange h).fY := by
  obtain ⟨n, a, ha, hpa⟩ := hp
  let : IsClosedImmersion a := ha
  let P := projectiveModel k L n i
  have hP : P.IsFP := projectiveModel_isFP k L n i
  obtain ⟨j₁, h₁, b, hb, hgb, _⟩ := exists_arrow_refinement k L m P hm hP a hpa
  let s := m.baseChange h₁
  let Q := P.baseChange h₁
  obtain ⟨_, _, _⟩ := hm.baseChange h₁
  obtain ⟨_, _, _⟩ := hP.baseChange h₁
  obtain ⟨l, hl⟩ := exists_isClosedImmersion s Q b hb (isLimitScalarCone k L) a hgb hpa
  let t := s.baseChange l.hom
  let R := Q.baseChange l.hom
  let c := topBaseChange s Q b hb l
  let : IsClosedImmersion c := hl
  have hc : c ≫ R.fY = t.fY := topBaseChange_snd _ _ _ _ _
  let h := l.hom ≫ h₁
  let φ : levelField k L i →+* levelField k L l.left :=
    (Subalgebra.inclusion h.unop.le).toRingHom
  let π : R.Y ⟶ P.Y := pullback.fst Q.fY ((diagram k L).map l.hom) ≫
    pullback.fst P.fY ((diagram k L).map h₁)
  have H : IsPullback π R.fY (projectiveSpaceStructure (levelField k L i) n)
      (Spec.map (CommRingCat.ofHom φ)) := by
    have H₀ := (IsPullback.of_hasPullback Q.fY ((diagram k L).map l.hom)).paste_horiz
      (IsPullback.of_hasPullback P.fY ((diagram k L).map h₁))
    change IsPullback π R.fY P.fY ((diagram k L).map h)
    simpa only [π, R, Model.baseChange, h, Functor.map_comp] using H₀
  let e := H.isoIsPullback _ _ (isPullback_projectiveCoefficientMap φ n)
  have hce : (c ≫ e.hom) ≫ projectiveSpaceStructure (levelField k L l.left) n = t.fY := by
    have he : e.hom ≫ projectiveSpaceStructure (levelField k L l.left) n = R.fY :=
      H.isoIsPullback_hom_snd _ _ (isPullback_projectiveCoefficientMap φ n)
    rw [Category.assoc, he]
    exact hc
  let eM := m.baseChangeCompIso h₁ l.hom
  refine ⟨l.left, h, n, eM.inv ≫ c ≫ e.hom, inferInstance, ?_⟩
  rw [Category.assoc, hce, ← m.baseChangeCompIso_hom_fY h₁ l.hom]
  simp [eM, h]

/-- An actual projective finite-field model has its OWN internally produced native projective
embedding over the ORIGINAL field k, retaining the entire original coefficient structure. -/
theorem projective_over_original_field {k E : Type u} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of E))
    (hq : IsProjectiveOver q) :
    IsProjectiveOver (q ≫ Spec.map (CommRingCat.ofHom (algebraMap k E))) := by
  obtain ⟨n, a, ha, hqa⟩ := hq
  let : IsClosedImmersion a := ha
  let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have H := isPullback_projectiveCoefficientMap (algebraMap k E) n
  let : IsFinite (projectiveCoefficientMap (algebraMap k E) n) :=
    MorphismProperty.of_isPullback H.flip inferInstance
  have hproj := FiniteProjective.isProjectiveOver_comp_of_isFinite
    (projectiveSpaceStructure k n) (isProjectiveOver_projectiveSpaceStructure k n)
    (a ≫ projectiveCoefficientMap (algebraMap k E) n)
  rw [Category.assoc, H.w, ← Category.assoc, hqa] at hproj
  exact hproj

end DeJongAlterations.Geometry.AlgebraicFieldFiniteProjectiveModel
