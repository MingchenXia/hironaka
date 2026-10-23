import DeJongAlterations.Algebra.ReesPresentation
import DeJongAlterations.Geometry.AffineBlowupChart

/-!
# A genuine fraction-chart open cover of the native affine blowup

All degree-one elements of the ideal generate its actual Rees algebra. Their
basic opens cover its native Proj; the zero generators have empty opens.
The nonzero charts, identified with Spec R[I/g], therefore form an actual
scheme open cover. No finite-generation or nonzero-ideal hypothesis is used.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

private theorem adjoin_eq_top_of_coeff_mem {Q A : Type u} [CommRing Q] [CommRing A]
    [Algebra R A] [Algebra Q A] (s : Set A)
    (hgen : Algebra.adjoin R s = ⊤)
    (hcoeff : ∀ r : R, algebraMap R A r ∈ Algebra.adjoin Q s) :
    Algebra.adjoin Q s = ⊤ := by
  apply top_unique
  intro a htop
  clear htop
  have ha : a ∈ Algebra.adjoin R s := by rw [hgen]; trivial
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r => exact hcoeff r
  | add x y _ _ hx hy => exact (Algebra.adjoin Q s).add_mem hx hy
  | mul x y _ _ hx hy => exact (Algebra.adjoin Q s).mul_mem hx hy

/-- All degree-one ideal elements generate the actual Rees algebra over R. -/
theorem reesDegreeOne_adjoin_eq_top :
    Algebra.adjoin R (Set.range fun a : I => reesDegreeOne I a a.property) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  change (Algebra.ReesPresentation.reesPolynomialEval I
    (fun a : I => (a : R)) (fun a => a.property)).range = ⊤
  rw [AlgHom.range_eq_top]
  exact Algebra.ReesPresentation.reesPolynomialMap_surjective I
    (fun a : I => (a : R)) (fun a => a.property) (by
      have hrange : Set.range (fun a : I => (a : R)) = (I : Set R) := by
        ext a
        exact ⟨fun ⟨b, hb⟩ => hb ▸ b.property, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
      rw [hrange, Ideal.span_eq])

/-- The same degree-one family generates over the actual degree-zero ring. -/
theorem reesDegreeOne_adjoin_zero_eq_top :
    Algebra.adjoin (reesGrading I 0)
      (Set.range fun a : I => reesDegreeOne I a a.property) = ⊤ := by
  exact adjoin_eq_top_of_coeff_mem (R := R) (Q := reesGrading I 0) (A := reesAlgebra I)
    (Set.range fun a : I => reesDegreeOne I a a.property) (reesDegreeOne_adjoin_eq_top I)
    (fun r => (Algebra.adjoin (reesGrading I 0)
      (Set.range fun a : I => reesDegreeOne I a a.property)).algebraMap_mem (reesConstants I r))

/-- The actual degree-one basic opens cover the native blowup. -/
theorem iSup_affineBlowupChartOpen :
    (⨆ a : I, affineBlowupChartOpen I a a.property) = ⊤ := by
  exact Proj.iSup_basicOpen_eq_top' (reesGrading I)
    (fun a : I => reesDegreeOne I a a.property)
    (fun a => ⟨1, reesDegreeOne_mem I a a.property⟩)
    (reesDegreeOne_adjoin_zero_eq_top I)

/-- Zero degree-one generators have empty opens, so all nonzero charts still cover. -/
theorem iSup_affineBlowupNonzeroChartOpen :
    (⨆ a : {a : I // (a : R) ≠ 0}, affineBlowupChartOpen I a.val a.val.property) = ⊤ := by
  apply top_le_iff.mp
  intro x hx
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp ((iSup_affineBlowupChartOpen I).ge hx)
  have ha0 : (a : R) ≠ 0 := by
    intro h
    have hz : reesDegreeOne I a a.property = 0 := by
      apply Subtype.ext
      simp [reesDegreeOne, h]
    change x ∈ Proj.basicOpen (reesGrading I) (reesDegreeOne I a a.property) at ha
    rw [hz, Proj.basicOpen_zero] at ha
    exact ha
  exact Opens.mem_iSup.mpr ⟨⟨a, ha0⟩, ha⟩

variable [IsDomain R]

/-- The actual fraction-chart immersion has the expected native basic-open range. -/
theorem affineBlowupFractionChartInclusion_opensRange (g : R) (hg : g ∈ I) (hg0 : g ≠ 0) :
    (affineBlowupChartInclusion I g hg hg0).opensRange = affineBlowupChartOpen I g hg := by
  dsimp only [affineBlowupChartInclusion, affineBlowupChartOpen]
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

/-- The actual spectra of the fraction charts form an open cover of the native blowup. -/
@[simps! I₀ X f]
def affineBlowupFractionOpenCover : (affineBlowup I).OpenCover.{u} :=
  Scheme.Cover.mkOfCovers
    {a : I // (a : R) ≠ 0}
    (fun a => Spec (CommRingCat.of (affineBlowupFractionChart I a.val)))
    (fun a => affineBlowupChartInclusion I a.val a.val.property a.property)
    (by
      intro x
      have hx : x ∈ (⊤ : (affineBlowup I).Opens) := trivial
      rw [← iSup_affineBlowupNonzeroChartOpen I] at hx
      obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
      rw [← affineBlowupFractionChartInclusion_opensRange I a.val a.val.property a.property] at ha
      exact ⟨a, ha⟩)


end DeJongAlterations
