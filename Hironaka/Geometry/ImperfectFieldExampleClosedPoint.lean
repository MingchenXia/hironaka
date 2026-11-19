/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Geometry.ImperfectFieldExampleCurve

/-!
# An actual closed nonsmooth point on the explicit regular curve
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Hironaka.Algebra.ImperfectFieldExample
open Hironaka.Geometry.ImperfectFieldExampleCurve

namespace Hironaka.Geometry.ImperfectFieldExampleClosedPoint

instance curveStructure_locallyOfFinitePresentation : LocallyOfFinitePresentation curveStructure :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

theorem exists_closed_nonsmooth_point : ∃ z : Spec (.of CurveRing),
    IsClosed ({z} : Set (Spec (.of CurveRing))) ∧ z ∉ curveStructure.smoothLocus := by
  by_contra! h
  apply curveStructure_not_smooth
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro x _
  let p : PrimeSpectrum CurveRing := x
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  let z : PrimeSpectrum CurveRing := ⟨m, hm.isPrime⟩
  have hz : IsClosed ({z} : Set (Spec (.of CurveRing))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal z).mpr hm
  have hspec : p ⤳ z := (PrimeSpectrum.le_iff_specializes p z).mp hpm
  exact hspec.mem_open curveStructure.smoothLocus.isOpen (h z hz)

end Hironaka.Geometry.ImperfectFieldExampleClosedPoint
