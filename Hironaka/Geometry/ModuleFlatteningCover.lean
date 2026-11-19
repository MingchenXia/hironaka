import Hironaka.Algebra.ModuleFlatteningMinorsExistence
import Hironaka.Geometry.AffineBlowupCover

/-!
# The original maximal-minor fraction charts cover the actual native blowup

The original column-minor family generates its literal ideal and hence the
actual Rees algebra. Its nonzero original minors therefore give a native
fraction-spectrum open cover, without a supplied cover certificate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ModuleFlattening

open Algebra.ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {n r : ℕ}

/-- The actual original minor Rees elements generate the original Rees algebra. -/
theorem minorRees_adjoin_eq_top (A : Matrix (Fin r) (Fin n) R) :
    Algebra.adjoin R (Set.range fun s : Fin r → Fin n ↦
      reesDegreeOne (minorIdeal A) (columnMinor A s) (columnMinor_mem_minorIdeal A s)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  change (Algebra.ReesPresentation.reesPolynomialEval (minorIdeal A)
    (columnMinor A) (columnMinor_mem_minorIdeal A)).range = ⊤
  rw [AlgHom.range_eq_top]
  exact Algebra.ReesPresentation.reesPolynomialMap_surjective (minorIdeal A)
    (columnMinor A) (columnMinor_mem_minorIdeal A) rfl

/-- The same actual original minor family generates over the native degree-zero ring. -/
theorem minorRees_adjoin_zero_eq_top (A : Matrix (Fin r) (Fin n) R) :
    Algebra.adjoin (reesGrading (minorIdeal A) 0)
      (Set.range fun s : Fin r → Fin n ↦ reesDegreeOne (minorIdeal A)
        (columnMinor A s) (columnMinor_mem_minorIdeal A s)) = ⊤ := by
  apply top_unique
  intro a htop
  clear htop
  have ha : a ∈ Algebra.adjoin R (Set.range fun s : Fin r → Fin n ↦
      reesDegreeOne (minorIdeal A) (columnMinor A s) (columnMinor_mem_minorIdeal A s)) := by
    rw [minorRees_adjoin_eq_top]
    trivial
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap c => exact (Algebra.adjoin (reesGrading (minorIdeal A) 0)
      (Set.range fun s : Fin r → Fin n ↦ reesDegreeOne (minorIdeal A)
        (columnMinor A s) (columnMinor_mem_minorIdeal A s))).algebraMap_mem (reesConstants (minorIdeal A) c)
  | add x y _ _ hx hy => exact (Algebra.adjoin _ _).add_mem hx hy
  | mul x y _ _ hx hy => exact (Algebra.adjoin _ _).mul_mem hx hy

/-- The original actual minor basic opens cover the whole native blowup. -/
theorem iSup_minorChartOpen (A : Matrix (Fin r) (Fin n) R) :
    (⨆ s : Fin r → Fin n, affineBlowupChartOpen (minorIdeal A)
      (columnMinor A s) (columnMinor_mem_minorIdeal A s)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (reesGrading (minorIdeal A))
    (fun s : Fin r → Fin n ↦ reesDegreeOne (minorIdeal A)
      (columnMinor A s) (columnMinor_mem_minorIdeal A s))
    (fun _s ↦ ⟨1, reesDegreeOne_mem _ _ _⟩) (minorRees_adjoin_zero_eq_top A)

/-- Zero original minors have empty native opens; the nonzero original minor opens still cover. -/
theorem iSup_nonzeroMinorChartOpen (A : Matrix (Fin r) (Fin n) R) :
    (⨆ s : {s : Fin r → Fin n // columnMinor A s ≠ 0},
      affineBlowupChartOpen (minorIdeal A) (columnMinor A s.val)
        (columnMinor_mem_minorIdeal A s.val)) = ⊤ := by
  apply top_le_iff.mp
  intro x hx
  obtain ⟨s, hs⟩ := Opens.mem_iSup.mp ((iSup_minorChartOpen A).ge hx)
  have hs0 : columnMinor A s ≠ 0 := by
    intro hzero
    have hz : reesDegreeOne (minorIdeal A) (columnMinor A s)
        (columnMinor_mem_minorIdeal A s) = 0 := by
      apply Subtype.ext
      simp [reesDegreeOne, hzero]
    change x ∈ Proj.basicOpen (reesGrading (minorIdeal A))
      (reesDegreeOne (minorIdeal A) (columnMinor A s) (columnMinor_mem_minorIdeal A s)) at hs
    rw [hz, Proj.basicOpen_zero] at hs
    exact hs
  exact Opens.mem_iSup.mpr ⟨⟨s, hs0⟩, hs⟩

variable [IsDomain R]

/-- An actual native finite open cover by the fraction spectra of the original nonzero minors. -/
@[simps! I₀ X f]
def minorFractionOpenCover (A : Matrix (Fin r) (Fin n) R) :
    (affineBlowup (minorIdeal A)).OpenCover.{0} :=
  Scheme.Cover.mkOfCovers {s : Fin r → Fin n // columnMinor A s ≠ 0}
    (fun s ↦ Spec (.of (affineBlowupFractionChart (minorIdeal A) (columnMinor A s.val))))
    (fun s ↦ affineBlowupChartInclusion (minorIdeal A) (columnMinor A s.val)
      (columnMinor_mem_minorIdeal A s.val) s.property)
    (by
      intro x
      have hx : x ∈ (⊤ : (affineBlowup (minorIdeal A)).Opens) := trivial
      rw [← iSup_nonzeroMinorChartOpen A] at hx
      obtain ⟨s, hs⟩ := Opens.mem_iSup.mp hx
      rw [← affineBlowupFractionChartInclusion_opensRange (minorIdeal A) (columnMinor A s.val)
        (columnMinor_mem_minorIdeal A s.val) s.property] at hs
      exact ⟨s, hs⟩)

/-- The original nonzero minor selector set is finite. -/
instance minorFractionOpenCover_finite (A : Matrix (Fin r) (Fin n) R) :
    Finite (minorFractionOpenCover A).I₀ := by
  change Finite {s : Fin r → Fin n // columnMinor A s ≠ 0}
  infer_instance

/-- Every actual minor chart preserves the literal original coefficient structure map. -/
@[reassoc (attr := simp)]
theorem minorFractionOpenCover_structure (A : Matrix (Fin r) (Fin n) R)
    (s : (minorFractionOpenCover A).I₀) :
    (minorFractionOpenCover A).f s ≫ affineBlowupStructure (minorIdeal A) =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (affineBlowupFractionChart (minorIdeal A) (columnMinor A s.val)))) :=
  affineBlowupChartInclusion_structure _ _ _ _

end Hironaka.Geometry.ModuleFlattening
