import DeJongAlterations.Geometry.AlgebraicFieldFiniteModel
import DeJongAlterations.Geometry.RegularSmoothConverse
import DeJongAlterations.StableModification.Limits.SpreadAffine
import DeJongAlterations.StableModification.Limits.SpreadProperty

/-! Actual smooth/regular models over finite fields, INTERNALLY constructed from scalar geometry. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.AlgebraicFieldFiniteSmoothModel

open StableModification.Limits AlgebraicFieldFiniteModel

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]

/-- Original smooth scalar geometry INTERNALLY gives a SAME actual finite-field smooth/regular
model and both entire original coefficient triangles, with no supplied descent data. -/
theorem exists_smooth_finite_field_model {Y : Scheme.{u}} (p : Y ⟶ Spec (.of L))
    [Smooth p] [QuasiCompact p] [QuasiSeparated p] :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      ∃ (Y₀ : Scheme.{u}) (p₀ : Y₀ ⟶ Spec (.of E)) (g : Y ⟶ Y₀),
        LocallyOfFinitePresentation p₀ ∧ QuasiCompact p₀ ∧ QuasiSeparated p₀ ∧
        Smooth p₀ ∧ IsRegularScheme Y₀ ∧
        IsPullback g p p₀ (Spec.map (CommRingCat.ofHom E.val.toRingHom)) ∧
        g ≫ p₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) =
          p ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  let f := p ≫ (topScalarIso k L).hom
  let : Smooth f := inferInstance
  obtain ⟨i, m, hm⟩ := exists_model_fgSubalgebra (⊤ : Subalgebra k L) f
  obtain ⟨j, h, hsmooth⟩ := Spread.exists_baseChange_of_forall_isAffineOpen @Smooth m
    (isLimitFGSpecCone (⊤ : Subalgebra k L)) hm (fun W hW => by
      let : IsAffine W := hW
      obtain ⟨B, M, hM, hs⟩ := Spread.exists_smooth_model_of_isAffine (W.ι ≫ f)
      exact ⟨Opposite.op B, M, hM, hs⟩)
  let n := m.baseChange h
  have hn : n.IsFP := hm.baseChange h
  let : Smooth n.fY := hsmooth
  have Hleft : IsPullback (𝟙 Y) p f (topScalarIso k L).hom :=
    IsPullback.of_horiz_isIso ⟨by simp [f]⟩
  have H : IsPullback n.g p n.fY ((scalarCone k L).π.app j) := by
    change IsPullback n.g p n.fY
      ((topScalarIso k L).hom ≫ (fgSpecCone (⊤ : Subalgebra k L)).π.app j)
    simpa only [Category.id_comp] using Hleft.paste_horiz n.isPullback
  rw [scalarCone_π] at H
  refine ⟨levelField k L j, levelField_finiteDimensional k L j, n.Y, n.fY, n.g,
    hn.1, hn.2.1, hn.2.2, hsmooth,
    RegularSmooth.isRegularScheme_of_smooth (K := levelField k L j) n.fY, H, ?_⟩
  rw [H.w_assoc, levelField_coefficient_triangle]

/-- Actual regularity over the ORIGINAL perfect scalar field INTERNALLY constructs a finite
field model which is smooth and regular; the ORIGINAL ground field may be imperfect. -/
theorem exists_regular_finite_field_model [PerfectField L] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of L)) [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (hY : IsRegularScheme Y) :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      ∃ (Y₀ : Scheme.{u}) (p₀ : Y₀ ⟶ Spec (.of E)) (g : Y ⟶ Y₀),
        LocallyOfFinitePresentation p₀ ∧ QuasiCompact p₀ ∧ QuasiSeparated p₀ ∧
        Smooth p₀ ∧ IsRegularScheme Y₀ ∧
        IsPullback g p p₀ (Spec.map (CommRingCat.ofHom E.val.toRingHom)) ∧
        g ≫ p₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) =
          p ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  let : Smooth p := RegularSmoothConverse.smooth_of_isRegularScheme p hY
  exact exists_smooth_finite_field_model k L p

end DeJongAlterations.Geometry.AlgebraicFieldFiniteSmoothModel
