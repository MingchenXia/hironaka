/-
The actual closed-residue calculation adapts the minimal proved core of
EnvelopeProperty/EnvelopeProperty/SmoothMaximalLocalizations.lean, SHA256
c32c81393b2915194037980fbf1d32635d0e45c1aaa7ef047ba18937e5279a8b. No EnvelopeProperty imports.
The actual original rings, coefficient actions and maximal ideal are retained.
-/
import DeJongAlterations.Algebra.NodeFittingModuleLocalRank
import DeJongAlterations.Algebra.NodeFittingOmegaLocalization
import DeJongAlterations.Algebra.ProjectiveSecantTangentDimension
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.FiniteType

/-! # Genuine closed regular affine curve points avoid the ORIGINAL full first Fitting ideal -/

noncomputable section

open IsLocalRing KaehlerDifferential
open scoped TensorProduct

namespace DeJongAlterations.Algebra.NodeFittingClosedRegular

open NodeFittingModule

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K A : Type*) [Field K] [PerfectField K] [CommRing A] [Algebra K A]
  [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal]

omit [PerfectField K] in
/-- Finiteness of the SAME actual closed residue follows internally from actual finite type. -/
theorem maximalResidue_finite : Module.Finite K m.ResidueField := by
  let : Algebra.FiniteType A m.ResidueField := inferInstance
  let : Algebra.FiniteType K m.ResidueField :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K A) inferInstance
  exact finite_of_finite_type_of_isJacobsonRing K m.ResidueField

/-- Perfectness makes THIS internally produced actual closed residue formally etale. -/
theorem maximalResidue_formallyEtale : Algebra.FormallyEtale K m.ResidueField := by
  let := maximalResidue_finite K A m
  exact Algebra.FormallyEtale.of_isSeparable K m.ResidueField

omit [PerfectField K] in
/-- Native finite presentation of the ORIGINAL affine differential module is internally derived. -/
theorem affineOmega_finitePresentation : Module.FinitePresentation A (KaehlerDifferential K A) := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  exact Module.finitePresentation_of_finite A (KaehlerDifferential K A)

variable [IsRegularLocalRing (Localization.AtPrime m)]

omit [PerfectField K] in
/-- The actual ORIGINAL maximal-localization differentials are internally finitely presented. -/
theorem maximalOmega_finitePresentation :
    Module.FinitePresentation (Localization.AtPrime m)
      (KaehlerDifferential K (Localization.AtPrime m)) := by
  let : Algebra.EssFiniteType A (Localization.AtPrime m) :=
    Algebra.EssFiniteType.of_isLocalization _ m.primeCompl
  let : Algebra.EssFiniteType K (Localization.AtPrime m) :=
    Algebra.EssFiniteType.comp K A (Localization.AtPrime m)
  exact Module.finitePresentation_of_finite _ _

/-- Original regularity and curve dimension produce the actual closed residue differential rank bound. -/
theorem maximalOmega_residue_finrank_le_one (hdim : ringKrullDim A ≤ 1) :
    Module.finrank (ResidueField (Localization.AtPrime m))
      ((ResidueField (Localization.AtPrime m)) ⊗[Localization.AtPrime m]
        (KaehlerDifferential K (Localization.AtPrime m))) ≤ 1 := by
  let P := Localization.AtPrime m
  let : Algebra.FormallyEtale K (ResidueField P) := maximalResidue_formallyEtale K A m
  have hs := ProjectiveSecant.residueCotangentMap_surjective_of_formallyEtale (k := K) (P := P)
  have hle := LinearMap.finrank_le_finrank_of_surjective hs
  have hd : ringKrullDim P ≤ 1 :=
    (le_of_eq (IsLocalization.AtPrime.ringKrullDim_eq_height m P)).trans
      (m.height_le_ringKrullDim_of_isPrime.trans hdim)
  rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace P).mp inferInstance] at hd
  have hc : Module.finrank (ResidueField P) (CotangentSpace P) ≤ 1 := by
    exact_mod_cast hd
  exact hle.trans hc

/-- The ENTIRE original local differential first Fitting ideal is the unit ideal at that ACTUAL closed point. -/
theorem maximalOmega_fitting_one_eq_top (hdim : ringKrullDim A ≤ 1) :
    letI := maximalOmega_finitePresentation K A m
    fittingIdeal (R := Localization.AtPrime m)
      (M := KaehlerDifferential K (Localization.AtPrime m)) 1 = ⊤ := by
  let := maximalOmega_finitePresentation K A m
  exact fittingIdeal_one_eq_top_of_residue_finrank_le_one
    (maximalOmega_residue_finrank_le_one K A m hdim)

/-- The SAME actual affine differential Fitting ideal excludes the SAME actual original maximal point. -/
theorem affineOmega_fitting_not_le_maximal (hdim : ringKrullDim A ≤ 1) :
    letI := affineOmega_finitePresentation K A
    ¬ fittingIdeal (R := A) (M := KaehlerDifferential K A) 1 ≤ m := by
  let := affineOmega_finitePresentation K A
  let := maximalOmega_finitePresentation K A m
  have hmap := NodeFittingOmega.fittingIdeal_localization K A (Localization.AtPrime m) m.primeCompl 1
  rw [maximalOmega_fitting_one_eq_top K A m hdim] at hmap
  intro hm
  have hle := Ideal.map_mono (f := algebraMap A (Localization.AtPrime m)) hm
  rw [hmap, Localization.AtPrime.map_eq_maximalIdeal] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime m)).ne_top (top_le_iff.mp hle)

end DeJongAlterations.Algebra.NodeFittingClosedRegular
