import DeJongAlterations.Geometry.AlgebraicFieldFiniteSmoothModel

/-! Actual scalar arrows and smoothness are produced on the SAME internally chosen models. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlgebraicFieldFiniteModelRefinement

open StableModification.Limits AlgebraicFieldFiniteModel

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]

omit [Algebra.IsAlgebraic k L] in
/-- The WHOLE original arrow is INTERNALLY produced between base changes of the SAME models. -/
theorem exists_arrow_refinement {Y Z : Scheme.{u}}
    {p : Y ⟶ Spec (.of L)} {q : Z ⟶ Spec (.of L)} {i : Index k L}
    (r : Model (diagram k L) (scalarCone k L) p i)
    (s : Model (diagram k L) (scalarCone k L) q i) (hr : r.IsFP) (hs : s.IsFP)
    (a : Y ⟶ Z) (ha : a ≫ q = p) :
    ∃ (j : Index k L) (h : j ⟶ i)
      (b : (r.baseChange h).Y ⟶ (s.baseChange h).Y),
      b ≫ (s.baseChange h).fY = (r.baseChange h).fY ∧
      (r.baseChange h).g ≫ b = a ≫ (s.baseChange h).g ∧
      IsPullback (r.baseChange h).g a b (s.baseChange h).g := by
  let : QuasiCompact r.fY := hr.2.1
  let : QuasiSeparated r.fY := hr.2.2
  let : LocallyOfFinitePresentation s.fY := hs.1
  obtain ⟨l, b, hb, hb'⟩ := exists_hom_of_isPullback (diagram k L) (scalarCone k L)
    (isLimitScalarCone k L) r.fY s.fY r.isPullback (a ≫ s.g) (by
      rw [Category.assoc, s.isPullback.w, ← Category.assoc, ha, r.isPullback.w])
  let b₀ := pullback.lift b (pullback.snd _ _) (by rw [hb, pullback.condition])
  have hb₀ : b₀ ≫ (s.baseChange l.hom).fY = (r.baseChange l.hom).fY :=
    pullback.lift_snd _ _ _
  have hg : (r.baseChange l.hom).g ≫ b₀ = a ≫ (s.baseChange l.hom).g := by
    apply pullback.hom_ext
    · simp only [Category.assoc, b₀, pullback.lift_fst]
      exact hb'.trans (by simp [Model.baseChange])
    · simp [b₀, Model.baseChange, reassoc_of% ha]
  refine ⟨l.left, l.hom, b₀, hb₀, hg, ?_⟩
  refine IsPullback.of_bot ?_ hg (s.baseChange l.hom).isPullback
  simpa only [ha, hb₀] using (r.baseChange l.hom).isPullback

/-- Actual scalar smoothness INTERNALLY proves smoothness/regularity on a further base change
of ANY SAME actual model, retaining all previously constructed maps by native base change. -/
theorem exists_smooth_refinement {Y : Scheme.{u}} {p : Y ⟶ Spec (.of L)} [Smooth p]
    {i : Index k L} (m : Model (diagram k L) (scalarCone k L) p i) (hm : m.IsFP) :
    ∃ (j : Index k L) (h : j ⟶ i),
      Smooth (m.baseChange h).fY ∧ IsRegularScheme (m.baseChange h).Y := by
  let f := p ≫ (topScalarIso k L).hom
  let : Smooth f := inferInstance
  have Hleft : IsPullback (𝟙 Y) f p (topScalarIso k L).inv :=
    IsPullback.of_horiz_isIso ⟨by simp [f]⟩
  let m' : Model (diagram k L) (fgSpecCone (⊤ : Subalgebra k L)) f i :=
    { Y := m.Y, fY := m.fY, g := m.g, isPullback := by
        simpa [scalarCone, ← Category.assoc] using Hleft.paste_horiz m.isPullback }
  obtain ⟨j, h, hsm⟩ := Spread.exists_baseChange_of_forall_isAffineOpen @Smooth m'
    (isLimitFGSpecCone (⊤ : Subalgebra k L)) hm (fun W hW => by
      let : IsAffine W := hW
      obtain ⟨B, M, hM, hs⟩ := Spread.exists_smooth_model_of_isAffine (W.ι ≫ f)
      exact ⟨Opposite.op B, M, hM, hs⟩)
  let : Smooth (m.baseChange h).fY := hsm
  exact ⟨j, h, hsm, RegularSmooth.isRegularScheme_of_smooth
    (K := levelField k L j) (m.baseChange h).fY⟩

/-- Actual regularity over perfect L produces smooth/regular geometry on the SAME model;
no perfectness of the ORIGINAL k and no finite-model regularity certificate are assumed. -/
theorem exists_regular_refinement [PerfectField L] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (.of L)} [LocallyOfFiniteType p] (hY : IsRegularScheme Y)
    {i : Index k L} (m : Model (diagram k L) (scalarCone k L) p i) (hm : m.IsFP) :
    ∃ (j : Index k L) (h : j ⟶ i),
      Smooth (m.baseChange h).fY ∧ IsRegularScheme (m.baseChange h).Y := by
  let : Smooth p := RegularSmoothConverse.smooth_of_isRegularScheme p hY
  exact exists_smooth_refinement k L m hm

end DeJongAlterations.Geometry.AlgebraicFieldFiniteModelRefinement
