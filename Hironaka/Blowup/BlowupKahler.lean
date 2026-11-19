import Hironaka.Blowup.BlanchardForm
import Hironaka.Analytic.KahlerPerturbation
import Hironaka.Analytic.KahlerPullbackKernel
import Hironaka.Blowup.BlowupCompact

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A blowup of a compact Kähler manifold along a smooth centre is compact Kähler

Source: Blanchard; Voisin, *Hodge theory and complex algebraic geometry* I, Prop. 3.24.

Let `π : Z → M` be the blowup (`IsBlowupAlong`) of a compact Kähler manifold `(M, ω)` along a
closed submanifold `C`.

* `exists_blanchardForm`: there is a closed real `(1,1)`-form `Θ` on `Z` (`ddᶜ log U` for the
  Blanchard weight `U` of `C`, extended across `π⁻¹ C`) which is strictly positive on every
  nonzero kernel vector of `dπ`;
* `compactSpace_and_kahler_of_isBlowupAlong`: `Z` is compact and `π^* ω + ε Θ` is Kähler for
  small `ε > 0`.  Indeed `π^* ω ≥ 0` with null directions exactly `ker dπ`
  (`KahlerPullbackKernel`), so at each point `π^* ω + ε₀ Θ > 0` for small `ε₀`
  (`PositivityPerturbation`), and compactness gives one `ε` (`KahlerPerturbation`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupKahler

open Hironaka.PositiveClasses Hironaka.BlowupSequences BlanchardWeight BlanchardForm
  FactorizedWeightForm

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  {C : Set M} {π : Z → M}

/-- **The Blanchard factorization** of a blowup: its glued form is positive on the kernel of
`dπ`. -/
theorem exists_blanchardFactorization_of_flat (hπ : IsBlowupAlong n C π) {C' : Set M}
    (D : BlanchardData n C')
    (hflatC : ∀ (q : C') {y : M}, y ∈ (chartAt (ComplexModel n) q.1).source →
      chartAt (ComplexModel n) q.1 y ∈ (D.flat q).source →
        (y ∈ C ↔ (D.flat q).toFun (chartAt (ComplexModel n) q.1 y) ∈
          complexCoordinatePlane n (D.kdim q)))
    (hC' : IsClosed C') (hC'C : C' ⊆ C) (hexc : ∀ z, π z ∉ C' → z ∉ exceptionalLocus n π) :
    ∃ F : WeightFactorization n (fun y => D.weight (π y)), ∀ (z : Z) (v : ComplexModel n),
      v ≠ 0 → mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z v = 0 →
        0 < F.closedForm.val.coeff (complexChartAt (n := n) z) (chartAt (ComplexModel n) z z)
          ![v, Complex.I • v] := by
  choose S h U' hS hzS hh hsm hpos hfac hposv using
    exists_localFactor_of_flat hπ D hflatC hC' hexc
  let F : WeightFactorization n (fun y => D.weight (π y)) :=
    { domain := S, isOpen_domain := hS, mem_domain := hzS, gen := h, smoothPart := U',
      gen_mdifferentiable := hh, smooth := hsm, pos := hpos, factor := hfac,
      nowhereZero := fun W hW hne => by
        obtain ⟨z, hz, hzC⟩ := exists_notMem_of_isOpen hπ hW hne
        exact ⟨z, hz, (D.weight_pos_of_notMem fun h => hzC (hC'C h)).ne'⟩ }
  refine ⟨F, fun z v hv hdv => ?_⟩
  have hu : chartAt (ComplexModel n) z z ∈ (complexChartAt (n := n) z).val.target :=
    (chartAt (ComplexModel n) z).map_source (mem_chart_source _ z)
  have hx : (complexChartAt (n := n) z).val.symm (chartAt (ComplexModel n) z z) ∈ F.domain z := by
    show (chartAt (ComplexModel n) z).symm (chartAt (ComplexModel n) z z) ∈ S z
    rw [(chartAt (ComplexModel n) z).left_inv (mem_chart_source _ z)]
    exact hzS z
  rw [(F.closedForm_coeff_eventuallyEq z (complexChartAt (n := n) z) hu hx).self_of_nhds]
  exact hposv z v hv hdv

/-- **The Blanchard factorization** of a blowup: its glued form is positive on the kernel of
`dπ`. -/
theorem exists_blanchardFactorization (hπ : IsBlowupAlong n C π) (D : BlanchardData n C) :
    ∃ F : WeightFactorization n (fun y => D.weight (π y)), ∀ (z : Z) (v : ComplexModel n),
      v ≠ 0 → mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z v = 0 →
        0 < F.closedForm.val.coeff (complexChartAt (n := n) z) (chartAt (ComplexModel n) z z)
          ![v, Complex.I • v] :=
  exists_blanchardFactorization_of_flat hπ D (fun q => D.flat_eq q) hπ.1.1 subset_rfl
    fun _ hz h => hz (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)

/-- **The Blanchard form** of a blowup: positive on the kernel of `dπ`. -/
theorem exists_blanchardForm (hπ : IsBlowupAlong n C π) (D : BlanchardData n C) :
    ∃ Θ : ClosedRealOneOneForm n Z, ∀ (z : Z) (v : ComplexModel n), v ≠ 0 →
      mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π z v = 0 →
        0 < Θ.val.coeff (complexChartAt (n := n) z) (chartAt (ComplexModel n) z z)
          ![v, Complex.I • v] := by
  obtain ⟨F, hF⟩ := exists_blanchardFactorization hπ D
  exact ⟨F.closedForm, hF⟩

/-- For every Kähler form `ω` on `M`, `π^* ω + ε Θ` is Kähler for some `ε > 0`, where `Θ` is the
Blanchard form. -/
theorem exists_isKahler_pullback_add_of_flat [CompactSpace Z] (omega : KahlerBackground n M)
    (hπ : IsBlowupAlong n C π) {C' : Set M} (D : BlanchardData n C')
    (hflatC : ∀ (q : C') {y : M}, y ∈ (chartAt (ComplexModel n) q.1).source →
      chartAt (ComplexModel n) q.1 y ∈ (D.flat q).source →
        (y ∈ C ↔ (D.flat q).toFun (chartAt (ComplexModel n) q.1 y) ∈
          complexCoordinatePlane n (D.kdim q)))
    (hC' : IsClosed C') (hC'C : C' ⊆ C) (hexc : ∀ z, π z ∉ C' → z ∉ exceptionalLocus n π) :
    ∃ F : WeightFactorization n (fun y => D.weight (π y)), ∃ ε : ℝ, 0 < ε ∧
      (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form + ε • F.closedForm).val.IsKahler := by
  obtain ⟨F, hΘ⟩ := exists_blanchardFactorization_of_flat hπ D hflatC hC' hC'C hexc
  set Θ := F.closedForm
  set A := ClosedRealOneOneForm.pullback hπ.contMDiff omega.form
  have hA : A.val.IsSemipositive :=
    ClosedRealOneOneForm.pullback_isSemipositive hπ.contMDiff omega.isSemipositive
  obtain ⟨ε, hε, hK⟩ := KahlerPerturbation.exists_isKahler_add_smul A Θ hA fun y => by
    set e := complexChartAt (n := n) y
    have hyt : chartAt (ComplexModel n) y y ∈ e.val.target :=
      (chartAt (ComplexModel n) y).map_source (mem_chart_source _ y)
    obtain ⟨ε₀, hε₀, hpos⟩ := PositivityPerturbation.exists_isStrictlyPositive_add_smul
      (a := A.val.coeff e (chartAt (ComplexModel n) y y))
      (b := Θ.val.coeff e (chartAt (ComplexModel n) y y))
      (fun v => hA e _ hyt v)
      (fun v hv h0 => hΘ y v hv
        ((KahlerPullbackKernel.quad_pullback_eq_zero_iff hπ.contMDiff omega.isKahler.1 y v).mp h0))
    refine ⟨ε₀, hε₀, ?_⟩
    have h := hpos ε₀ hε₀ le_rfl
    show IsStrictlyPositive ((A + ε₀ • Θ).val.coeff e (chartAt (ComplexModel n) y y))
    simpa [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul] using h
  exact ⟨F, ε, hε, hK⟩

/-- For every Kähler form `ω` on `M`, `π^* ω + ε Θ` is Kähler for some `ε > 0`, where `Θ` is the
Blanchard form. -/
theorem exists_isKahler_pullback_add [CompactSpace Z] (omega : KahlerBackground n M)
    (hπ : IsBlowupAlong n C π) (D : BlanchardData n C) :
    ∃ F : WeightFactorization n (fun y => D.weight (π y)), ∃ ε : ℝ, 0 < ε ∧
      (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form + ε • F.closedForm).val.IsKahler :=
  exists_isKahler_pullback_add_of_flat omega hπ D (fun q => D.flat_eq q) hπ.1.1 subset_rfl
    fun _ hz h => hz (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)

/-- **Blanchard.**  The blowup of a compact Kähler manifold along a closed complex submanifold
is compact Kähler. -/
theorem compactSpace_and_kahler_of_isBlowupAlong [CompactSpace M]
    (hKahler : Nonempty (KahlerBackground n M)) (hπ : IsBlowupAlong n C π) :
    CompactSpace Z ∧ Nonempty (KahlerBackground n Z) := by
  have := BlowupCompact.compactSpace_of_isBlowupAlong hπ
  refine ⟨inferInstance, ?_⟩
  obtain ⟨omega⟩ := hKahler
  obtain ⟨D⟩ := exists_blanchardData hπ.1
  obtain ⟨F, ε, -, hK⟩ := exists_isKahler_pullback_add omega hπ D
  exact ⟨⟨_, hK⟩⟩

end

end Hironaka.BlowupKahler
