import Hironaka.Analytic.Unibranch.HironakaG10ActualSchurHolomorphic
import Hironaka.Resolution.HironakaG10LocSectionNoether
import Hironaka.Resolution.HironakaG10PNIdealNoetherOpen
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualSheafStalk

/-! A single family of actual scalar Schur obstruction sections and local
finite generation on one open parameter manifold. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka Hironaka
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  HironakaG10PNIdealFamily HironakaG10LocSectionNoether HironakaG10PNIdealNoetherOpen
  HironakaSmoothCentreRealDomainActualSheafStalk
  Hironaka.Analytic.Unibranch.HironakaG10ActualSchurHolomorphic
namespace Hironaka.Analytic.Unibranch.HironakaG10ActualSchurScalarSections
noncomputable section

variable {E₁ E₀ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]

/-- The actual scalar functional of the actual operator applied to one input. -/
def operatorScalarFunction (d : ℕ) (S : ComplexModel d → (E₁ →L[ℂ] E₀))
    (v : E₁) (ell : E₀ →L[ℂ] ℂ) : ComplexModel d → ℂ := fun z => ell (S z v)

/-- Every actual scalar functional of a holomorphic operator family is
holomorphic on the same open parameter set. -/
theorem differentiableOn_operatorScalarFunction (d : ℕ) (U : Opens (ComplexModel d))
    (S : ComplexModel d → (E₁ →L[ℂ] E₀)) (hS : DifferentiableOn ℂ S U)
    (v : E₁) (ell : E₀ →L[ℂ] ℂ) :
    DifferentiableOn ℂ (operatorScalarFunction d S v ell) U := by
  intro z hz
  have hsz : DifferentiableAt ℂ S z := (hS z hz).differentiableAt (U.isOpen.mem_nhds hz)
  exact (ell.differentiableAt.comp z ((ContinuousLinearMap.apply ℂ E₀ v).differentiableAt.comp z hsz)).differentiableWithinAt

/-- Each scalar obstruction is an actual global section on the common open
parameter manifold, with its literal scalar values. -/
def operatorScalarSection (d : ℕ) (U : Opens (ComplexModel d))
    (S : ComplexModel d → (E₁ →L[ℂ] E₀)) (hS : DifferentiableOn ℂ S U)
    (v : E₁) (ell : E₀ →L[ℂ] ℂ) :
    actualComplexSection (n := d) (⊤ : Opens U) := by
  have hd := differentiableOn_operatorScalarFunction d U S hS v ell
  have hc : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ℂ) ∞ (fun z : U => operatorScalarFunction d S v ell z) :=
    (contDiffOn_of_differentiableOn_complex hd U.isOpen).contMDiffOn.comp_contMDiff
      contMDiff_subtype_val (fun z => z.property)
  change C^∞⟮𝓘(ℂ, ComplexModel d), (⊤ : Opens U); 𝓘(ℂ, ℂ), ℂ⟯
  exact ⟨fun z => operatorScalarFunction d S v ell z.val.val, hc.comp contMDiff_subtype_val⟩

theorem operatorScalarSection_apply (d : ℕ) (U : Opens (ComplexModel d))
    (S : ComplexModel d → (E₁ →L[ℂ] E₀)) (hS : DifferentiableOn ℂ S U)
    (v : E₁) (ell : E₀ →L[ℂ] ℂ) (z : (⊤ : Opens U)) :
    operatorScalarSection d U S hS v ell z = ell (S z.val.val v) := rfl

/-- The SINGLE family of all scalar operator obstructions has one finite
subfamily spanning it throughout a neighborhood of every parameter point. -/
theorem scalarOperatorSections_finite_near (d : ℕ) (U : Opens (ComplexModel d))
    (S : ComplexModel d → (E₁ →L[ℂ] E₀)) (hS : DifferentiableOn ℂ S U) (p : U) :
    let X := ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) U
    let s : E₁ × (E₀ →L[ℂ] ℂ) → X.presheaf.obj (op ⊤) :=
      fun q => operatorScalarSection d U S hS q.1 q.2
    ∃ F : Finset (E₁ × (E₀ →L[ℂ] ℂ)),
      ∀ᶠ y in 𝓝 p, spanFamily s univ y = spanFamily s (F : Set _) y := by
  let X := ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) U
  let s : E₁ × (E₀ →L[ℂ] ℂ) → X.presheaf.obj (op ⊤) :=
    fun q => operatorScalarSection d U S hS q.1 q.2
  have : FirstCountableTopology X := inferInstanceAs (FirstCountableTopology U)
  exact exists_finset_eventually_eq (hasLocalNoetherProperty_manifoldOpen U) s p

/-- The actual scalar operator family can be made into one locally finite
ideal-section family on a single open neighborhood. -/
theorem exists_scalarOperatorSections_near (d : ℕ)
    (S : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hS : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ S z) :
    ∃ (U : Opens (ComplexModel d)) (_h0 : (0 : ComplexModel d) ∈ U)
      (hSU : DifferentiableOn ℂ S U),
      let X := ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) U
      let s : E₁ × (E₀ →L[ℂ] ℂ) → X.presheaf.obj (op ⊤) :=
        fun q => operatorScalarSection d U S hSU q.1 q.2
      ∀ p : U, ∃ F : Finset (E₁ × (E₀ →L[ℂ] ℂ)),
        ∀ᶠ y in 𝓝 p, spanFamily s univ y = spanFamily s (F : Set _) y := by
  obtain ⟨V,hV,hVo,h0⟩ := eventually_nhds_iff.mp hS
  let U : Opens (ComplexModel d) := ⟨V,hVo⟩
  have hSU : DifferentiableOn ℂ S U := fun z hz => (hV z hz).differentiableWithinAt
  exact ⟨U,h0,hSU,fun p => scalarOperatorSections_finite_near d U S hSU p⟩

/-- The actual analytic Frisch Schur operator produces the same concrete
scalar obstruction family, locally finitely generated at all nearby points. -/
theorem exists_schurScalarSections_near [CompleteSpace E₁] [CompleteSpace E₀]
    (d : ℕ) (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hC0 : opC P Q S₀ (f 0) = ContinuousLinearMap.id ℂ E₀) :
    ∃ (U : Opens (ComplexModel d)) (_h0 : (0 : ComplexModel d) ∈ U)
      (hSU : DifferentiableOn ℂ (fun z => schurOp P Q S₀ (f z)) U),
      let X := ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) U
      let s : E₁ × (E₀ →L[ℂ] ℂ) → X.presheaf.obj (op ⊤) :=
        fun q => operatorScalarSection d U (fun z => schurOp P Q S₀ (f z)) hSU q.1 q.2
      ∀ p : U, ∃ F : Finset (E₁ × (E₀ →L[ℂ] ℂ)),
        ∀ᶠ y in 𝓝 p, spanFamily s univ y = spanFamily s (F : Set _) y :=
  exists_scalarOperatorSections_near d _ (actual_schur_holomorphic d P Q S₀ f hf hC0)

end
end Hironaka.Analytic.Unibranch.HironakaG10ActualSchurScalarSections
