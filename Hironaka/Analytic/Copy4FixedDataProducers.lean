import Hironaka.Analytic.Copy4FixedDataAssembly
import Hironaka.Analytic.AmbientUMWeightLowerBound
import Hironaka.Analytic.MultiplierIdealBergmanNadelManifold
import Hironaka.Analytic.IdealFunctionMaxGluing

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Producers for fields of `Copy4FixedData`: `U_M` (with Nadel coherence), `Ψ_m` and `x₀`

Source: Copy-4, `sec:ambient` (`eq:def-TM`), `sec:fixed-principalization` (`eq:def-Psi`) and
`prop:principalization` Step 5 (`references/transcendental-nakamaye-copy4-20260911/source/
main-Nulllocus.tex:1598-1630, 1719-1730, 1907-1916`).

* `exists_regularization_UM` — **`eq:def-TM` with `𝔅_M = 𝓘(M V_θ)` coherent.**  The constant
  `c₀` of `lem:regularization` comes first and depends only on `(X, ω)`; then for every
  `θ`-psh potential `φ` (Copy-4: `V_θ`) and every level `M ≥ 1` there are a weight `ψ_{𝔅_M}` of
  `𝓘(Mφ)` at coefficient `1` and `U_M` with `θ + (c₀/M) ω + ddᶜU_M ≥ 0` and
  `M⁻¹ ψ_{𝔅_M} ≤ U_M + O(1)` — the fields `hpsiBM`, `hUM`, `hUMlower` of `Copy4FixedData` with
  `levQ = M`.  Coherence of `𝓘(Mφ)` is Nadel's theorem
  (`MultiplierIdealBergmanNadelManifold.isCoherent_multiplierIdeal_of_pos`, TN23 879df559).
* `exists_mem_notMem_zeroLocus₂` — an irreducible `V` contained in neither of two zero loci of
  coherent ideals has a point outside both (identity principle on `V`).
* `exists_idealFunction_of_not_subset` — **`eq:def-Psi` with its point `x₀`**: for coherent `𝔧`,
  `𝔅_m` with `V ⊄ Z(𝔧)`, `V ⊄ Z(𝔅_m)`, a point `x₀ ∈ V` and a `c_Ψ ω`-psh `Ψ` of type
  `(1, 𝔧 𝔅_m)` smooth near `x₀` (`IdealFunctionMaxGluing.exists_idealFunction`).

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.Copy4FixedDataProducers

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.NonKahlerLocus

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **`eq:def-TM` with `𝔅_M = 𝓘(Mφ)` coherent** (Nadel); `c₀` before everything else. -/
theorem exists_regularization_UM [CompactSpace X] [ConnectedSpace X] (hn : 0 < n)
    (omega : KahlerBackground n X) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (θ : ClosedRealOneOneForm n X) (φ : X → EReal), IsThetaPshPotential θ.val φ →
        ∀ M : ℕ, 1 ≤ M →
          ∃ psiBM UM : X → EReal,
            HasAnalyticSingularitiesOfType (n := n) psiBM 1
              (multiplierIdeal (n := n) (M : ℝ) φ) ∧
            IsThetaPshPotential (θ + (c₀ / ((M : ℚ) : ℝ)) • omega.form).val UM ∧
            MoreSingularOn (fun x => ((1 / ((M : ℚ) : ℝ) : ℝ) : EReal) * psiBM x) UM univ := by
  obtain ⟨c₀, hc₀, hreg⟩ :=
    AmbientUMWeightLowerBound.exists_regularization_moreSingularOn_multiplierIdealWeight omega
  refine ⟨c₀, hc₀, fun θ φ hφ M hM => ?_⟩
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcoh : (multiplierIdeal (n := n) (M : ℝ) φ).IsCoherent :=
    MultiplierIdealBergmanNadelManifold.isCoherent_multiplierIdeal_of_pos hn hφ.1 hMpos
  obtain ⟨psi, hpsi⟩ := CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent hcoh
  obtain ⟨UM, hUM, hlow⟩ := hreg θ φ hφ M hM psi hpsi
  refine ⟨psi, UM, hpsi, ?_, ?_⟩
  · simpa only [Rat.cast_natCast] using hUM
  · simpa only [Rat.cast_natCast, one_div] using hlow

/-- **An irreducible `V` contained in neither of two zero loci has a point outside both.** -/
theorem exists_mem_notMem_zeroLocus₂ (V : ClosedIrreducibleAnalyticSubvariety n X)
    {𝔞 𝔟 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent)
    (hV𝔞 : ¬ V.carrier ⊆ 𝔞.zeroLocus) (hV𝔟 : ¬ V.carrier ⊆ 𝔟.zeroLocus) :
    ∃ x ∈ V.carrier, x ∉ 𝔞.zeroLocus ∧ x ∉ 𝔟.zeroLocus := by
  have hZ𝔞 := StepFourNoComponentContainsW.isComplexAnalyticSubset_zeroLocus h𝔞
  have hZ𝔟 := StepFourNoComponentContainsW.isComplexAnalyticSubset_zeroLocus h𝔟
  obtain ⟨x, hxV, hx𝔞⟩ := not_subset.mp hV𝔞
  by_contra hcon
  push Not at hcon
  apply hV𝔟
  refine StrictTransformLocus.subset_of_inter_isOpen_subset V hZ𝔟 hZ𝔞.isClosed.isOpen_compl
    ⟨x, hxV, hx𝔞⟩ fun y ⟨hyV, hy𝔞⟩ => hcon y hyV hy𝔞

/-- **`eq:def-Psi` with its point `x₀`.**  For coherent `𝔧`, `𝔅_m` with `V ⊄ Z(𝔧)` and
`V ⊄ Z(𝔅_m)`: a point `x₀ ∈ V` and a `c_Ψ ω`-psh `Ψ` with analytic singularities of type
`(1, 𝔧 𝔅_m)`, smooth near `x₀`. -/
theorem exists_idealFunction_of_not_subset [CompactSpace X] (omega : KahlerBackground n X)
    (V : ClosedIrreducibleAnalyticSubvariety n X) {𝔧 𝔟 : GermIdeal n X}
    (h𝔧 : 𝔧.IsCoherent) (h𝔟 : 𝔟.IsCoherent) (hV𝔧 : ¬ V.carrier ⊆ 𝔧.zeroLocus)
    (hV𝔟 : ¬ V.carrier ⊆ 𝔟.zeroLocus) :
    ∃ x₀ ∈ V.carrier, ∃ (Ψ : X → EReal) (cΨ : ℝ), 0 < cΨ ∧
      ThetaPlurisubharmonic (cΨ • omega.form).val Ψ ∧
      HasAnalyticSingularitiesOfType (n := n) Ψ 1 (𝔧.mul 𝔟) ∧
      IsSmoothNear (n := n) Ψ x₀ := by
  obtain ⟨x₀, hx₀V, hx₀𝔧, hx₀𝔟⟩ := exists_mem_notMem_zeroLocus₂ V h𝔧 h𝔟 hV𝔧 hV𝔟
  obtain ⟨Ψ, c, hc, hpsh, htype, hsmooth⟩ :=
    IdealFunctionMaxGluing.exists_idealFunction omega (IdealWeightPowers.isCoherent_mul h𝔧 h𝔟) x₀
  exact ⟨x₀, hx₀V, Ψ, c, hc, hpsh, htype,
    (hsmooth (RestrictLeCalculus.notMem_zeroLocus_mul h𝔧 h𝔟 hx₀𝔧 hx₀𝔟)).1⟩

end

end Hironaka.Copy4FixedDataProducers
