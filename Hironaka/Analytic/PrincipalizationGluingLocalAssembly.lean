import Hironaka.Analytic.SmoothPotentialDomination
import Hironaka.Analytic.KahlerCurrentMax
import Hironaka.Analytic.AnalyticGluingData

set_option autoImplicit false

/-!
# The formal Step-6 assembly for local principalization data

This is the source-free algebraic/PSH assembly at the end of Copy-4's
`prop:principalization`.  It takes the strict-positive smooth part, the
positive divisor/correction part, and the compact collar comparison as data,
and produces `PrincipalizationGluingConclusions`.  It does not construct any
of that data and has no resolution input.
-/

open Set
open scoped Topology Manifold ContDiff

namespace Hironaka.PrincipalizationGluingLocalAssembly

open Hironaka.PositiveClasses Hironaka.AnalyticGluingData
  Hironaka.LocalPotentials Hironaka.NonKahlerLocus

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Addition of theta-PSH potentials, localized to a set. -/
theorem thetaPlurisubharmonicOn_add {a b : ClosedRealOneOneForm n M}
    {u v : M → EReal} {Ω : Set M}
    (hu : ThetaPlurisubharmonicOn a.val u Ω) (hv : ThetaPlurisubharmonicOn b.val v Ω) :
    ThetaPlurisubharmonicOn (a + b).val (fun x => u x + v x) Ω := by
  intro e z hz hzΩ
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz hzΩ
  obtain ⟨V, σ, hzV, hσ, hq⟩ := hv e z hz hzΩ
  have hWV : IsOpen (W ∩ V) := hρ.1.inter hσ.1
  refine ⟨W ∩ V, fun y => ρ y + σ y, ⟨hzW, hzV⟩,
    localPotential_add (hρ.mono hWV inter_subset_left) (hσ.mono hWV inter_subset_right), ?_⟩
  have hfun :
      (fun y => chartFunction (fun x => u x + v x) e y + ((ρ y + σ y : ℝ) : EReal)) =
      (fun y => (chartFunction u e y + (ρ y : EReal)) +
        (chartFunction v e y + (σ y : EReal))) := by
    funext y
    simp only [chartFunction, EReal.coe_add]
    ac_rfl
  rw [hfun]
  exact (hp.mono inter_subset_left).add (hq.mono inter_subset_right)

/-- A real smooth summand preserves local nondegeneracy of a theta-PSH potential. -/
theorem isThetaPshPotentialOn_coe_add {a b : ClosedRealOneOneForm n M}
    {σ : M → ℝ} {v : M → EReal} {Ω : Set M}
    (hu : ThetaPlurisubharmonicOn a.val (fun x => (σ x : EReal)) Ω)
    (hv : IsThetaPshPotentialOn b.val v Ω) :
    IsThetaPshPotentialOn (a + b).val (fun x => (σ x : EReal) + v x) Ω := by
  refine ⟨thetaPlurisubharmonicOn_add hu hv.1, ?_⟩
  intro x hx U hU hxU
  obtain ⟨y, hyU, hy⟩ := hv.2 x hx U hU hxU
  refine ⟨y, hyU, ?_⟩
  show ((σ y : ℝ) : EReal) + v y ≠ ⊥
  exact fun h => (EReal.add_eq_bot_iff.mp h).elim (fun h' => EReal.coe_ne_bot _ h') hy

/-- A smooth strictly positive part plus a positive correction preserves Kähler domination. -/
theorem dominatesKahlerFormOn_coe_add {β η : ClosedRealOneOneForm n M}
    {σ : M → ℝ} {ρ : M → EReal} {Ω : Set M}
    (hβ : DominatesKahlerFormOn β (fun x => (σ x : EReal)) Ω)
    (hη : IsThetaPshPotentialOn η.val ρ Ω) :
    DominatesKahlerFormOn (β + η) (fun x => (σ x : EReal) + ρ x) Ω := by
  obtain ⟨omega', homega'⟩ := hβ
  refine ⟨omega', ?_⟩
  have hform : ((β - omega'.form) + η) = ((β + η) - omega'.form) := by
    abel
  have h := isThetaPshPotentialOn_coe_add (a := β - omega'.form) (b := η) homega'.1 hη
  rwa [hform] at h

/-- A globally chart-smooth real summand preserves smoothness near a point. -/
theorem isSmoothNear_coe_add {v : M → EReal} {p : M} {σ : M → ℝ}
    (hσ : ChartSmooth (n := n) σ) (hv : IsSmoothNear (n := n) v p) :
    IsSmoothNear (n := n) (fun x => (σ x : EReal) + v x) p := by
  obtain ⟨U, hU, hp, g, hg, hvg⟩ := hv
  refine ⟨U, hU, hp, fun x => σ x + g x, ?_, ?_⟩
  · intro e
    exact ((hσ e).mono inter_subset_left).add (hg e)
  · intro y hy
    show (σ y : EReal) + v y = ((σ y + g y : ℝ) : EReal)
    rw [hvg y hy, ← EReal.coe_add]

/-- A continuous real function has an upper bound on a compact set. -/
theorem exists_le_of_isCompact {σ : M → ℝ} (hσ : Continuous σ)
    {Λ : Set M} (hΛ : IsCompact Λ) : ∃ C : ℝ, ∀ z ∈ Λ, σ z ≤ C := by
  rcases Λ.eq_empty_or_nonempty with hempty | hne
  · exact ⟨0, fun z hz => absurd hz (by simp [hempty])⟩
  · obtain ⟨z₀, -, hz₀⟩ := hΛ.exists_isMaxOn hne hσ.continuousOn
    exact ⟨σ z₀, fun z hz => hz₀ hz⟩

/-- The source-free Step-6 assembly. -/
theorem principalizationGluingConclusions_coe_add
    {θ β η : ClosedRealOneOneForm n M} (hθ : θ = β + η)
    {W U : Set M} {y : M} {σ : M → ℝ} {ρ φG : M → EReal}
    (hσ : ChartSmooth (n := n) σ)
    (hdom : DominatesKahlerFormOn β (fun x => (σ x : EReal)) U)
    (hρ : IsThetaPshPotentialOn η.val ρ U)
    (hφG : IsKahlerCurrentPotential θ φG) (hpole : ∀ w ∈ W, φG w = ⊥)
    (hsmooth : IsSmoothNear (n := n) ρ y)
    (hcollar : ∀ Λ : Set M, IsCompact Λ → Λ ⊆ U \ W →
      ∃ C : ℝ, ∀ z ∈ Λ, ρ z ≤ φG z + (C : EReal)) :
    PrincipalizationGluingConclusions θ W y U φG (fun x => (σ x : EReal) + ρ x) := by
  refine ⟨⟨hφG, hpole⟩, ⟨?_, isSmoothNear_coe_add hσ hsmooth⟩, ?_⟩
  · rw [hθ]
    exact dominatesKahlerFormOn_coe_add hdom hρ
  · intro Λ hΛ hΛU
    obtain ⟨C, hC⟩ := hcollar Λ hΛ hΛU
    obtain ⟨C', hC'⟩ := exists_le_of_isCompact
      (KahlerCurrentMax.continuous_of_chartSmooth hσ) hΛ
    refine ⟨C + C', fun z hz => ?_⟩
    calc (σ z : EReal) + ρ z
        ≤ (σ z : EReal) + (φG z + (C : EReal)) := by
          gcongr
          exact hC z hz
      _ ≤ (C' : EReal) + (φG z + (C : EReal)) := by
          gcongr
          exact hC' z hz
      _ = φG z + ((C + C' : ℝ) : EReal) := by
          rw [EReal.coe_add]
          abel

end

end Hironaka.PrincipalizationGluingLocalAssembly
