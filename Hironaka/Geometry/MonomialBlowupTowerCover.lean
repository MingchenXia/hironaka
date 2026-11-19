import Hironaka.Geometry.BlowupOpenChart

/-!
# Actual global blowup covers from actual spectrum charts

The full ideal comap identifies each actual native affine Rees blowup with
the corresponding inverse-image open of the genuine global blowup.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupTowerCover

open BlowupGluing

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} {ι : Type v} (D : X.IdealSheafData)
    (R : ι → CommRingCat.{u}) (f : ∀ i, Spec (R i) ⟶ X)
    [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ (f i).opensRange)
    (I : ∀ i, Ideal (R i))
    (hI : ∀ i, D.comap (f i) = SpecIdealSheaf.specIdealSheaf (R i) (I i))

/-- Actual affine Rees blowups cover the actual global blowup over the specified spectrum cover. -/
def spectrumBlowupCover : (blowup D).OpenCover.{v} :=
  Scheme.Cover.mkOfCovers ι (fun i ↦ affineBlowup (I i))
    (fun i ↦ BlowupOpenChart.chartMap (f i) D (I i) (hI i)) (by
      intro x
      obtain ⟨i, hi⟩ := hcover (blowupStructure D x)
      refine ⟨i, ?_⟩
      change x ∈ (BlowupOpenChart.chartMap (f i) D (I i) (hI i)).opensRange
      rw [BlowupOpenChart.chartMap_opensRange]
      exact hi)

@[simp]
theorem spectrumBlowupCover_source (i : ι) :
    (spectrumBlowupCover D R f hcover I hI).X i = affineBlowup (I i) := rfl

@[simp]
theorem spectrumBlowupCover_map (i : ι) :
    (spectrumBlowupCover D R f hcover I hI).f i =
      BlowupOpenChart.chartMap (f i) D (I i) (hI i) := rfl

@[reassoc]
theorem spectrumBlowupCover_structure (i : ι) :
    (spectrumBlowupCover D R f hcover I hI).f i ≫ blowupStructure D =
      affineBlowupStructure (I i) ≫ f i :=
  BlowupOpenChart.chartMap_structure (f i) D (I i) (hI i)

/-- Native binding constructs the actual refined global cover from all actual local covers. -/
def refinedSpectrumBlowupCover (C : ∀ i, (affineBlowup (I i)).OpenCover.{w}) :
    (blowup D).OpenCover.{max v w} :=
  (spectrumBlowupCover D R f hcover I hI).bind C

@[simp]
theorem refinedSpectrumBlowupCover_source
    (C : ∀ i, (affineBlowup (I i)).OpenCover.{w}) (i : ι) (j : (C i).I₀) :
    (refinedSpectrumBlowupCover D R f hcover I hI C).X ⟨i, j⟩ = (C i).X j := rfl

@[simp]
theorem refinedSpectrumBlowupCover_map
    (C : ∀ i, (affineBlowup (I i)).OpenCover.{w}) (i : ι) (j : (C i).I₀) :
    (refinedSpectrumBlowupCover D R f hcover I hI C).f ⟨i, j⟩ =
      (C i).f j ≫ BlowupOpenChart.chartMap (f i) D (I i) (hI i) := rfl

end Hironaka.Geometry.MonomialBlowupTowerCover
