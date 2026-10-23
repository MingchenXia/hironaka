import DeJongAlterations.StableModificationBridge.StableOpenPolarizedFamily
import DeJongAlterations.StableModificationBridge.StableOpenAffinePolarization
import DeJongAlterations.StableModificationBridge.StableOpenRationalFibreSections
import DeJongAlterations.StableModificationBridge.StableOpenGenericSmoothReduction

/-! The actual normal rational stable-open producer, with every section and
polarization input discharged. Blueprint: `sm-bridge-stable-open-normal-rational.tex`. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenNormalRational

open StableModification Projectivity Cohomology CurvesField

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual stability openness for the normal rational generic-smooth route;
there are no section, positivity, comparison or stable-open producer inputs. -/
theorem stableOpenNbhdRationalGenericSmooth (K : Type u) [Field K] [IsAlgClosed K] :
    Global.StableOpenNbhdRationalGenericSmooth K := by
  intro V pV hVar hNorm C q hq X β hβ D' hss hsm a ha hnum hno
  let : IsVariety pV := hVar
  let : DeJong.IsNodalCurve (β ≫ q) := hss.nodal
  let : IsProper q := hq.isProper
  let : IsProper β := hβ.isProper
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (q ≫ pV)
  obtain ⟨E, hEi, hEs, L, ⟨e⟩, hsec⟩ :=
    StableOpenRationalFibreSections.exists_markedLineBundle_fibreSections
      pV hNorm q hq β hβ D' hss hsm a ha hnum hno
  have hEi' : ∀ i, ∃ h : IsAffineOpen (E.U i),
      D'.ideal ⟨E.U i, h⟩ = Ideal.span {E.f i} := by
    intro i
    obtain ⟨h, _, hi⟩ := hEi i
    exact ⟨h, hi⟩
  have hzc : IsClosed ({a (IsLocalRing.closedPoint K)} : Set V) :=
    ((pointEquivClosedPoint pV) ⟨a, ha⟩).2
  apply StableOpenPolarizedFamily.exists_open_of_original_affine_polarizations
    pV hNorm q hq β hβ D' hss hsm E hEi' hEs L e
    (a (IsLocalRing.closedPoint K)) hzc
  intro y hy hya
  let : IsAlgClosed (C.residueField y) :=
    StableProjectivityClosedFibres.isAlgClosed_residueField_of_isClosed (q ≫ pV) y hy
  exact StableOpenAffinePolarization.exists_affine_polarization β (q ≫ pV)
    (locallyRelativelyProjective_of_isRelativelyProjective hβ) L hy
    (topologicalKrullDim_fiber_le_one β q y) (hsec y hy hya)

/-- The precise generic-smooth stable-open input consumed by the actual main
proof holds over every field, with no remaining mathematical producer input. -/
theorem stableOpenNbhdConnGenericSmooth (k : Type u) [Field k] :
    Global.StableOpenNbhdConnGenericSmooth k :=
  Global.stableOpenNbhdConnGenericSmooth_of_rational k
    (fun K _ _ => stableOpenNbhdRationalGenericSmooth K)

end DeJongAlterations.StableModificationBridge.StableOpenNormalRational
