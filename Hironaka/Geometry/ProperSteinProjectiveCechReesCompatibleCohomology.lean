/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesFixedTarget
import Hironaka.Geometry.ProperSteinProjectiveCechStableFiltration

/-! # Actual compatible ORIGINAL ideal-power native cohomology vanishes

Closed native intersection proof adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/FormalFunctionsCompatibleCohomology.lean`,
SHA256 490879b62e3810a79511404a183b09562320cc2f4a3939cec87fcfe9a4b6a236.
Only OWN internally derived original projective finiteness and actual original
image stability are used. No prozero, vanishing or formal-functions certificate.
-/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesCompatibleCohomology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
section OriginalFamily
variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The ENTIRE genuine compatible original power-cohomology module, with SAME original transitions and R action. -/
def compatibleCohomology (q : ℕ) :
    Submodule R (∀ n : ℕ, (ReesPowerDiagram.powerComplex I f U n).homology q) where
  carrier := {y | ∀ n m (h : n≤m), (ReesDegreeTransitions.homologyLower I f U h q).hom (y m)=y n}
  zero_mem' := by intro n m h; exact map_zero _
  add_mem' := by
    intro y z hy hz n m h
    change (ReesDegreeTransitions.homologyLower I f U h q).hom (y m+z m)=y n+z n
    rw [map_add, hy n m h, hz n m h]
  smul_mem' := by
    intro a y hy n m h
    change (ReesDegreeTransitions.homologyLower I f U h q).hom (a • y m)=a • y n
    exact ((ReesDegreeTransitions.homologyLower I f U h q).hom.map_smul a (y m)).trans
      (congrArg (fun z => a • z) (hy n m h))
end OriginalFamily

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} {r : ℕ} (i : X ⟶ projectiveSpace R r) [IsClosedImmersion i]

/-- ONLY complete original Noetherian projective geometry separates EVERY actual original fixed-target image filtration. -/
theorem projective_fixedTarget_iInf_eq_bot [IsNoetherianRing R] [IsAdicComplete I R] (n q : ℕ) :
    (⨅ d : ℕ, (ReesFixedTarget.imageFiltration I (i ≫ projectiveSpaceStructure R r)
      (originalClosedCoordinateOpens i) n q).N d)=⊥ := by
  let : Module.Finite R ((ReesPowerDiagram.powerComplex I (i ≫ projectiveSpaceStructure R r)
    (originalClosedCoordinateOpens i) n).homology q) :=
    ReesPowerCohomologyFinite.projective_powerCech_finite I i n q
  exact StableFiltration.iInf_eq_bot_of_le_jacobson I
    (ReesFixedTarget.imageFiltration I (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i) n q)
    (ReesFixedTarget.projective_imageFiltration_stable I i n q)
    (IsAdicComplete.le_jacobson_bot I)

/-- EVERY actual compatible original cohomology family vanishes from ORIGINAL complete projective geometry alone. -/
theorem projective_compatible_eq_zero [IsNoetherianRing R] [IsAdicComplete I R] (q : ℕ)
    (y : ∀ n : ℕ, (ReesPowerDiagram.powerComplex I (i ≫ projectiveSpaceStructure R r)
      (originalClosedCoordinateOpens i) n).homology q)
    (hy : ∀ n m (h : n≤m), (ReesDegreeTransitions.homologyLower I
      (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i) h q).hom (y m)=y n) :
    y=0 := by
  funext n
  have hmem : y n ∈ ⨅ d : ℕ,
      (ReesFixedTarget.imageFiltration I (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i) n q).N d := by
    apply (Submodule.mem_iInf _).mpr
    intro d
    exact ⟨y (n+d), hy n (n+d) (Nat.le_add_right n d)⟩
  rw [projective_fixedTarget_iInf_eq_bot I i n q] at hmem
  exact hmem

/-- The ENTIRE genuine original compatible native cohomology module is zero; no finite-level vanishing is assumed. -/
theorem projective_compatibleCohomology_eq_bot [IsNoetherianRing R] [IsAdicComplete I R] (q : ℕ) :
    compatibleCohomology I (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i) q=⊥ := by
  apply bot_unique
  intro y hy
  exact projective_compatible_eq_zero I i q y hy

/-- The SAME original vanishing for literal positive infinitesimal orders n+1 and EVERY actual original class. -/
theorem projective_compatible_positive_eq_zero [IsNoetherianRing R] [IsAdicComplete I R] (q : ℕ)
    (y : ∀ n : ℕ, (ReesPowerDiagram.powerComplex I (i ≫ projectiveSpaceStructure R r)
      (originalClosedCoordinateOpens i) (n+1)).homology q)
    (hy : ∀ n m (h : n≤m), (ReesDegreeTransitions.homologyLower I
      (i ≫ projectiveSpaceStructure R r) (originalClosedCoordinateOpens i) (Nat.succ_le_succ h) q).hom (y m)=y n) :
    y=0 := by
  funext n
  let f := i ≫ projectiveSpaceStructure R r
  let U := originalClosedCoordinateOpens i
  have hmem : y n ∈ ⨅ d : ℕ, (ReesFixedTarget.imageFiltration I f U (n+1) q).N d := by
    apply (Submodule.mem_iInf _).mpr
    intro d
    let P : {j : ℕ // n+1≤j} → Prop := fun j =>
      y n ∈ LinearMap.range (ReesDegreeTransitions.homologyLower I f U j.property q).hom
    let j₁ : {j : ℕ // n+1≤j} := ⟨(n+d)+1, Nat.succ_le_succ (Nat.le_add_right n d)⟩
    let j₂ : {j : ℕ // n+1≤j} := ⟨(n+1)+d, Nat.le_add_right (n+1) d⟩
    have he : j₁=j₂ := Subtype.ext (by change (n+d)+1=(n+1)+d; omega)
    have hm : P j₁ := ⟨y (n+d), hy n (n+d) (Nat.le_add_right n d)⟩
    exact (congrArg P he).mp hm
  rw [projective_fixedTarget_iInf_eq_bot I i (n+1) q] at hmem
  exact hmem

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesCompatibleCohomology
