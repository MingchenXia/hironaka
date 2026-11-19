import Hironaka.Analytic.Unibranch.HironakaG10ActualSchurScalarSections
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-! Finite actual scalar equations detect the whole operator zero locus. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka Hironaka
  HironakaG10PNIdealFamily HironakaG10LocSectionNoether HironakaG10PNIdealNoetherOpen
  HironakaSmoothCentreRealDomainActualSheafStalk
  Hironaka.Analytic.Unibranch.HironakaG10ActualSchurScalarSections
namespace Hironaka.Analytic.Unibranch.HironakaG10SchurScalarZeroLocus
noncomputable section

variable {E₁ E₀ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]

/-- The literal scalar values of all obstruction sections vanish at a point
exactly when the entire actual operator vanishes there. -/
theorem scalarSections_zero_iff_operator_zero (d : ℕ) (U : Opens (ComplexModel d))
    (S : ComplexModel d → (E₁ →L[ℂ] E₀)) (hS : DifferentiableOn ℂ S U) (p : U) :
    (∀ (v : E₁) (ell : E₀ →L[ℂ] ℂ),
      operatorScalarSection d U S hS v ell ⟨p, trivial⟩ = 0) ↔ S p = 0 := by
  constructor
  · intro h
    ext v
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
    intro ell
    simpa only [zero_apply, operatorScalarSection_apply] using h v ell
  · intro h v ell
    rw [operatorScalarSection_apply, h, zero_apply, map_zero]

/-- If a finite subfamily generates all obstruction germs at this point,
its literal scalar zero equations detect the whole operator. -/
theorem finiteScalarSections_zero_iff_operator_zero (d : ℕ) (U : Opens (ComplexModel d))
    (S : ComplexModel d → (E₁ →L[ℂ] E₀)) (hS : DifferentiableOn ℂ S U) (p : U)
    (F : Finset (E₁ × (E₀ →L[ℂ] ℂ))) :
    let X := ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) U
    let s : E₁ × (E₀ →L[ℂ] ℂ) → X.presheaf.obj (op ⊤) :=
      fun q => operatorScalarSection d U S hS q.1 q.2
    spanFamily s univ p = spanFamily s (F : Set _) p →
      ((∀ q ∈ F, operatorScalarSection d U S hS q.1 q.2 ⟨p, trivial⟩ = 0) ↔ S p = 0) := by
  let X := ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) U
  let s : E₁ × (E₀ →L[ℂ] ℂ) → X.presheaf.obj (op ⊤) :=
    fun q => operatorScalarSection d U S hS q.1 q.2
  let eval := smoothSheafCommRing.eval 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ℂ) U ℂ p
  change spanFamily s univ p = spanFamily s (F : Set _) p →
    ((∀ q ∈ F, operatorScalarSection d U S hS q.1 q.2 ⟨p, trivial⟩ = 0) ↔ S p = 0)
  intro hgen
  constructor
  · intro hfin
    apply (scalarSections_zero_iff_operator_zero d U S hS p).mp
    intro v ell
    have hker : spanFamily s (F : Set _) p ≤ RingHom.ker eval := by
      apply Ideal.span_le.mpr
      rintro _ ⟨q,hq,rfl⟩
      change eval (X.presheaf.germ ⊤ p trivial (s q)) = 0
      change smoothSheafCommRing.evalHom 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ℂ) U ℂ p
        ((smoothSheafCommRing 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ℂ) U ℂ).presheaf.germ ⊤ p (by trivial) (s q)) = 0
      rw [smoothSheafCommRing.evalHom_germ]
      exact hfin q hq
    have hm := germ_mem_spanFamily s (F := univ) (show (v,ell) ∈ (univ : Set _) from trivial) p
    rw [hgen] at hm
    have hz := hker hm
    change eval (X.presheaf.germ ⊤ p trivial (s (v,ell))) = 0 at hz
    change smoothSheafCommRing.evalHom 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ℂ) U ℂ p
      ((smoothSheafCommRing 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ℂ) U ℂ).presheaf.germ ⊤ p (by trivial) (s (v,ell))) = 0 at hz
    rw [smoothSheafCommRing.evalHom_germ] at hz
    exact hz
  · intro h q hq
    exact (scalarSections_zero_iff_operator_zero d U S hS p).mpr h q.1 q.2
end
end Hironaka.Analytic.Unibranch.HironakaG10SchurScalarZeroLocus
