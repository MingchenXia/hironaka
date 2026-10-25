import DeJongAlterations.Algebra.NodeFittingSmooth
import DeJongAlterations.Algebra.NodeFittingOmegaGluing
import DeJongAlterations.Algebra.NodeFittingOmegaAffineBase
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # The ACTUAL global Fitting closed subscheme avoids native smooth points of a field curve -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Algebra.NodeFittingSmoothScheme

open NodeFittingModule NodeFittingOmegaCharts

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}}

/-- The actual affine spectrum open embedding bounds the SAME original section-ring dimension. -/
theorem affine_dimension_le (U : X.affineOpens) :
    ringKrullDim Γ(X, U) ≤ topologicalKrullDim X := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact U.2.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le

variable (f : X ⟶ Y) [IsAffine Y] [LocallyOfFinitePresentation f]

/-- EVERY native smooth point avoids the support of the ACTUAL entire globally glued ideal. -/
theorem not_mem_support_of_mem_smoothLocus (hField : IsField Γ(Y, ⊤))
    (hPerfect : letI : Field Γ(Y, ⊤) := hField.toField; PerfectField Γ(Y, ⊤))
    (hdim : topologicalKrullDim X ≤ 1)
    (x : X) (hx : x ∈ f.smoothLocus) :
    x ∉ (NodeFittingOmegaGluing.idealSheaf f 1).support := by
  let : Field Γ(Y, ⊤) := hField.toField
  let : PerfectField Γ(Y, ⊤) := hPerfect
  obtain ⟨D, hxD⟩ := NodeFittingOmegaStalk.exists_chart_mem f x
  let U := D.source
  let C : Chart f := ⟨U, ⟨⊤, isAffineOpen_top Y⟩, le_top⟩
  let := NodeFittingOmegaAffine.sectionsAlgebra f U.1
  let := NodeFittingOmegaAffine.sections_finitePresentation f U
  let := NodeFittingOmegaAffine.differential_finitePresentation f U
  let q := U.2.primeIdealOf ⟨x, hxD⟩
  let : q.asIdeal.IsPrime := q.isPrime
  let : Algebra.IsSmoothAt Γ(Y, ⊤) q.asIdeal :=
    (formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top Y) U.1 U.2 le_top hxD).mp hx
  have hnot := NodeFittingSmooth.fitting_not_le_of_isSmoothAt Γ(Y, ⊤) Γ(X, U) q.asIdeal
    ((affine_dimension_le U).trans hdim)
  have heq : (NodeFittingOmegaGluing.idealSheaf f 1).ideal U =
      fittingIdeal (R := Γ(X, U)) (M := KaehlerDifferential Γ(Y, ⊤) Γ(X, U)) 1 :=
    NodeFittingOmegaGluing.idealSheaf_chart_ideal f 1 C
  rw [← heq] at hnot
  intro hs
  have hz := ((NodeFittingOmegaGluing.idealSheaf f 1).mem_support_iff_of_mem hxD).mp hs
  have hq : q ∈ PrimeSpectrum.zeroLocus
      ((NodeFittingOmegaGluing.idealSheaf f 1).ideal U : Set Γ(X, U)) := by
    rw [← U.2.fromSpec_preimage_zeroLocus]
    change U.2.fromSpec q ∈ X.zeroLocus _
    simpa only [q, IsAffineOpen.fromSpec_primeIdealOf] using hz
  exact hnot hq

/-- The ACTUAL original closed-subscheme inclusion has no image in the native smooth locus. -/
theorem subscheme_image_not_mem_smoothLocus (hField : IsField Γ(Y, ⊤))
    (hPerfect : letI : Field Γ(Y, ⊤) := hField.toField; PerfectField Γ(Y, ⊤))
    (hdim : topologicalKrullDim X ≤ 1)
    (z : (NodeFittingOmegaGluing.idealSheaf f 1).subscheme) :
    (NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z ∉ f.smoothLocus := by
  intro hz
  apply not_mem_support_of_mem_smoothLocus f hField hPerfect hdim _ hz
  have hmem : (NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z ∈
      Set.range (NodeFittingOmegaGluing.idealSheaf f 1).subschemeι := ⟨z, rfl⟩
  rw [(NodeFittingOmegaGluing.idealSheaf f 1).range_subschemeι] at hmem
  exact hmem

/-- On the SAME actual structural map to Spec K, the original intrinsic Fitting subscheme avoids smooth points. -/
theorem fieldCurve_subscheme_image_not_mem_smoothLocus {K : Type u} [Field K] [PerfectField K]
    (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFinitePresentation p]
    (hdim : topologicalKrullDim X ≤ 1)
    (z : (NodeFittingOmegaGluing.idealSheaf p 1).subscheme) :
    (NodeFittingOmegaGluing.idealSheaf p 1).subschemeι z ∉ p.smoothLocus := by
  let B := Γ(Spec (CommRingCat.of K), ⊤)
  let e : B ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hField : IsField B := e.toMulEquiv.isField (Field.toIsField K)
  let : Field B := hField.toField
  let : PerfectField B := PerfectField.of_ringEquiv e.symm
  exact subscheme_image_not_mem_smoothLocus p hField inferInstance hdim z

end DeJongAlterations.Algebra.NodeFittingSmoothScheme
