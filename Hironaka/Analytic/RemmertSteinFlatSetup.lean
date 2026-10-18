/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.RemmertSteinCoordinates
import Hironaka.Analytic.CompactAnalyticFinite
import Hironaka.Analytic.AnalyticIrreducibleComponents

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The flat case of Remmert--Stein: radii, properness and finite fibres

Blueprint `rem:remmert-stein-flat`, end of the paragraph "Coordinates" (Demailly, *Complex analytic
and differential geometry*, II.8.7).  In linear coordinates `Λ = (π, κ) : ℂⁿ ≃ ℂˢ × ℂᵈ` for which
`π` is injective on `L` (through `a`) and the central fibre `E ∩ π⁻¹(π a)` is countable, we choose
radii `δ, ρ > 0` such that the closed polydisc `{‖π z - π a‖ ≤ δ, ‖κ z - κ a‖ ≤ ρ}` lies in `Ω` and its
"vertical boundary" `{‖π z - π a‖ ≤ δ, ‖κ z - κ a‖ = ρ}` misses `E ∪ L` (`exists_radii`: a radius `ρ`
missing the countably many values `‖κ z - κ a‖` on the central fibre, then the tube lemma).
Over a compact set `K` of the ball `B'` missing `π(L)`, `E ∩ Q ∩ π⁻¹ K` is compact
(`isCompact_inter_preimage`, `Q` the open polydisc), and the fibres of `π` on `E ∩ Q` are finite
(`finite_fibre`: compact analytic subsets of `ℂᵈ` are finite).

Helpers: presentations from equations on an open subset of `ℂⁿ`; finite sets have no accumulation
points; a set containing a neighbourhood of a point is regular of full dimension there.

Sorry-free.
-/

open Set Filter Topology Metric TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.RemmertSteinFlat

open AnalyticDimensionBasics RemmertStatements

section Helpers

/-- A presentation at `x` from finitely many equations holomorphic on an open set `O ∋ x` of `ℂⁿ`
which cut out `S` in `O`. -/
theorem nonempty_presentation_of_eqOn {n : ℕ} {S O : Set (ComplexModel n)} (hO : IsOpen O)
    {x : ComplexModel n} (hx : x ∈ O) {r : ℕ} (f : Fin r → ComplexModel n → ℂ)
    (hf : ∀ i, DifferentiableOn ℂ (f i) O) (hS : ∀ y ∈ O, y ∈ S ↔ ∀ i, f i y = 0) :
    Nonempty (ComplexAnalyticPresentationAt (n := n) (M := ComplexModel n) S x) := by
  have hchart : (complexChartAt (n := n) x).val = OpenPartialHomeomorph.refl (ComplexModel n) := by
    simp [complexChartAt, chartAt_self_eq]
  exact ⟨{ generatorCount := r
           generator := f
           coordinateNeighborhood := O
           isOpen_coordinateNeighborhood := hO
           center_mem_coordinateNeighborhood := by rw [hchart]; exact hx
           coordinateNeighborhood_subset_target := by rw [hchart]; exact subset_univ _
           generator_holomorphic := hf
           zeroLocus := by
             intro y _ hy
             rw [hchart] at hy ⊢
             exact hS y hy }⟩

/-- A finite set has no accumulation points. -/
theorem not_accPt_of_finite {X : Type*} [TopologicalSpace X] [T1Space X] {S : Set X}
    (hS : S.Finite) (x : X) : ¬ AccPt x (𝓟 S) := by
  rw [accPt_iff_nhds]
  intro h
  obtain ⟨y, ⟨hyU, hyS⟩, hyx⟩ := h (S \ {x})ᶜ ((hS.sdiff).isClosed.isOpen_compl.mem_nhds
    fun hx => hx.2 rfl)
  exact hyU ⟨hyS, hyx⟩

/-- A set containing a neighbourhood of `x` is regular of full dimension at `x`. -/
theorem regularAtDim_of_mem_nhds {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {S : Set M} {x : M}
    (hS : S ∈ 𝓝 x) : RegularAtDim (n := n) S x n := by
  obtain ⟨O, hOS, hOo, hxO⟩ := mem_nhds_iff.mp hS
  refine RegularPointDimension.regularAtDim_of_inter_eq hOo hxO ?_
    (AnalyticIrreducibleComponents.regularAtDim_univ x)
  rw [univ_inter, inter_eq_right.mpr hOS]

end Helpers

section Radii

variable {n s d : ℕ}

/-- **Choice of the radii.** -/
theorem exists_radii {Ω E L : Set (ComplexModel n)} (hΩ : IsOpen Ω) (hL : IsClosed L)
    (Λ : ComplexModel n ≃L[ℂ] ComplexModel s × ComplexModel d) {a : ComplexModel n}
    (haΩ : a ∈ Ω) (hcl : closure E ∩ Ω ⊆ E ∪ L)
    (hLinj : ∀ l ∈ L, (Λ l).1 = (Λ a).1 → l = a)
    (hD : (E ∩ {z | (Λ z).1 = (Λ a).1}).Countable) :
    ∃ δ > 0, ∃ ρ > 0,
      (∀ z, ‖(Λ z).1 - (Λ a).1‖ ≤ δ → ‖(Λ z).2 - (Λ a).2‖ ≤ ρ → z ∈ Ω) ∧
      (∀ z, ‖(Λ z).1 - (Λ a).1‖ ≤ δ → ‖(Λ z).2 - (Λ a).2‖ = ρ → z ∉ E ∧ z ∉ L) := by
  have hΩ' : IsOpen (Λ.symm ⁻¹' Ω) := hΩ.preimage Λ.symm.continuous
  have haΩ' : Λ a ∈ Λ.symm ⁻¹' Ω := by simpa using haΩ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ' (Λ a) haΩ'
  set ρ₀ := r / 2 with hρ₀
  have hρ₀pos : 0 < ρ₀ := by positivity
  set R := (fun z => ‖(Λ z).2 - (Λ a).2‖) '' (E ∩ {z | (Λ z).1 = (Λ a).1}) with hR
  obtain ⟨ρ, ⟨hρ0, hρ1⟩, hρR⟩ := ((hD.image (fun z => ‖(Λ z).2 - (Λ a).2‖)).dense_compl ℝ).inter_open_nonempty
    (Ioo 0 ρ₀) isOpen_Ioo ⟨ρ₀ / 2, by positivity, by linarith⟩
  have hGo : IsOpen (Λ.symm ⁻¹' (Ω \ (E ∪ L))) := by
    have : Ω \ (E ∪ L) = Ω ∩ (closure E ∪ L)ᶜ := by
      ext z
      constructor
      · rintro ⟨hzΩ, hz⟩
        refine ⟨hzΩ, ?_⟩
        rintro (hzc | hzL)
        · exact hz (hcl ⟨hzc, hzΩ⟩)
        · exact hz (Or.inr hzL)
      · rintro ⟨hzΩ, hz⟩
        exact ⟨hzΩ, fun h => hz (h.elim (fun h => Or.inl (subset_closure h)) Or.inr)⟩
    rw [this]
    exact (hΩ.inter (isClosed_closure.union hL).isOpen_compl).preimage Λ.symm.continuous
  have hsub : ({(Λ a).1} : Set (ComplexModel s)) ×ˢ sphere (Λ a).2 ρ ⊆
      Λ.symm ⁻¹' (Ω \ (E ∪ L)) := by
    rintro ⟨w, v⟩ ⟨hw, hv⟩
    simp only [mem_singleton_iff] at hw
    subst hw
    rw [mem_sphere_iff_norm] at hv
    set z := Λ.symm ((Λ a).1, v) with hz
    have hΛz : Λ z = ((Λ a).1, v) := by simp [hz]
    refine ⟨?_, ?_⟩
    · have : ((Λ a).1, v) ∈ ball (Λ a) r := by
        rw [mem_ball, Prod.dist_eq, dist_self, dist_eq_norm, hv]
        simp only [max_eq_right hρ0.le]
        linarith
      exact hball this
    · rintro (hzE | hzL)
      · apply hρR
        refine ⟨z, ⟨hzE, by simp [hΛz]⟩, ?_⟩
        simp only [hΛz]
        exact hv
      · have := hLinj z hzL (by simp [hΛz])
        have hva : v = (Λ a).2 := by
          have h := congrArg (fun x => (Λ x).2) this
          simpa [hΛz] using h
        rw [hva, sub_self, norm_zero] at hv
        linarith
  obtain ⟨u, v, hu, -, hau, hvs, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_sphere _ _) hGo hsub
  obtain ⟨δ₁, hδ₁, hδ₁u⟩ := Metric.isOpen_iff.mp hu (Λ a).1 (hau rfl)
  refine ⟨min (δ₁ / 2) ρ₀, by positivity, ρ, hρ0, ?_, ?_⟩
  · intro z hz1 hz2
    have : Λ z ∈ ball (Λ a) r := by
      rw [mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      have h1 : ‖(Λ z).1 - (Λ a).1‖ ≤ ρ₀ := hz1.trans (min_le_right _ _)
      rw [max_lt_iff]
      constructor <;> linarith
    simpa using hball this
  · intro z hz1 hz2
    have h1 : (Λ z).1 ∈ u := hδ₁u (by
      rw [mem_ball, dist_eq_norm]
      have := hz1.trans (min_le_left _ _)
      linarith)
    have h2 : (Λ z).2 ∈ v := hvs (by rw [mem_sphere_iff_norm]; exact hz2)
    have := huv (mk_mem_prod h1 h2)
    simp only [Prod.mk.eta, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at this
    exact ⟨fun h => this.2 (Or.inl h), fun h => this.2 (Or.inr h)⟩

end Radii

section Proper

variable {n s d : ℕ} {Ω E L : Set (ComplexModel n)}
  {Λ : ComplexModel n ≃L[ℂ] ComplexModel s × ComplexModel d} {a : ComplexModel n} {δ ρ : ℝ}

/-- The open polydisc of the construction. -/
def polydisc (Λ : ComplexModel n ≃L[ℂ] ComplexModel s × ComplexModel d) (a : ComplexModel n)
    (δ ρ : ℝ) : Set (ComplexModel n) :=
  {z | ‖(Λ z).1 - (Λ a).1‖ < δ ∧ ‖(Λ z).2 - (Λ a).2‖ < ρ}

theorem isOpen_polydisc : IsOpen (polydisc Λ a δ ρ) := by
  have h1 : Continuous fun z => ‖(Λ z).1 - (Λ a).1‖ :=
    ((continuous_fst.comp Λ.continuous).sub continuous_const).norm
  have h2 : Continuous fun z => ‖(Λ z).2 - (Λ a).2‖ :=
    ((continuous_snd.comp Λ.continuous).sub continuous_const).norm
  exact (isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)

theorem mem_polydisc_self (hδ : 0 < δ) (hρ : 0 < ρ) : a ∈ polydisc Λ a δ ρ := by
  simp [polydisc, hδ, hρ]

theorem polydisc_subset (hQΩ : ∀ z, ‖(Λ z).1 - (Λ a).1‖ ≤ δ → ‖(Λ z).2 - (Λ a).2‖ ≤ ρ → z ∈ Ω) :
    polydisc Λ a δ ρ ⊆ Ω := fun z hz => hQΩ z hz.1.le hz.2.le

/-- **Properness of `π` on `E ∩ Q`** over compact sets missing `π(L)`. -/
theorem isCompact_inter_preimage (hcl : closure E ∩ Ω ⊆ E ∪ L)
    (hQΩ : ∀ z, ‖(Λ z).1 - (Λ a).1‖ ≤ δ → ‖(Λ z).2 - (Λ a).2‖ ≤ ρ → z ∈ Ω)
    (hsph : ∀ z, ‖(Λ z).1 - (Λ a).1‖ ≤ δ → ‖(Λ z).2 - (Λ a).2‖ = ρ → z ∉ E ∧ z ∉ L)
    {K : Set (ComplexModel s)} (hK : IsCompact K) (hKB : K ⊆ ball (Λ a).1 δ)
    (hKL : ∀ l ∈ L, (Λ l).1 ∉ K) :
    IsCompact (E ∩ polydisc Λ a δ ρ ∩ {z | (Λ z).1 ∈ K}) := by
  set C := Λ.symm '' (K ×ˢ closedBall (Λ a).2 ρ) with hC
  have hCc : IsCompact C := (hK.prod (isCompact_closedBall _ _)).image Λ.symm.continuous
  have hmemC : ∀ z, z ∈ C ↔ (Λ z).1 ∈ K ∧ ‖(Λ z).2 - (Λ a).2‖ ≤ ρ := by
    intro z
    constructor
    · rintro ⟨⟨w, v⟩, ⟨hw, hv⟩, rfl⟩
      rw [mem_closedBall, dist_eq_norm] at hv
      simpa using ⟨hw, hv⟩
    · rintro ⟨hw, hv⟩
      exact ⟨Λ z, ⟨hw, by rw [mem_closedBall, dist_eq_norm]; exact hv⟩, by simp⟩
  have hset : E ∩ polydisc Λ a δ ρ ∩ {z | (Λ z).1 ∈ K} = closure E ∩ C := by
    ext z
    constructor
    · rintro ⟨⟨hzE, -, hz2⟩, hzK⟩
      exact ⟨subset_closure hzE, (hmemC z).mpr ⟨hzK, hz2.le⟩⟩
    · rintro ⟨hzc, hzC⟩
      obtain ⟨hzK, hz2⟩ := (hmemC z).mp hzC
      have hz1 : ‖(Λ z).1 - (Λ a).1‖ < δ := by
        have := hKB hzK
        rwa [mem_ball, dist_eq_norm] at this
      have hzΩ := hQΩ z hz1.le hz2
      have hzE : z ∈ E := by
        rcases hcl ⟨hzc, hzΩ⟩ with h | h
        · exact h
        · exact absurd hzK (hKL z h)
      refine ⟨⟨hzE, hz1, ?_⟩, hzK⟩
      rcases hz2.lt_or_eq with h | h
      · exact h
      · exact absurd hzE (hsph z hz1.le h).1
  rw [hset]
  exact hCc.inter_left isClosed_closure

/-- **The fibres of `π` on `E ∩ Q` are finite** off `π(L)`. -/
theorem finite_fibre (hcl : closure E ∩ Ω ⊆ E ∪ L) (hEL : Disjoint E L)
    (hEpres : ∀ z ∈ Ω, z ∉ L → Nonempty (ComplexAnalyticPresentationAt (n := n) E z))
    (hQΩ : ∀ z, ‖(Λ z).1 - (Λ a).1‖ ≤ δ → ‖(Λ z).2 - (Λ a).2‖ ≤ ρ → z ∈ Ω)
    (hsph : ∀ z, ‖(Λ z).1 - (Λ a).1‖ ≤ δ → ‖(Λ z).2 - (Λ a).2‖ = ρ → z ∉ E ∧ z ∉ L)
    {w : ComplexModel s} (hw : w ∈ ball (Λ a).1 δ) (hwL : ∀ l ∈ L, (Λ l).1 ≠ w) :
    (E ∩ polydisc Λ a δ ρ ∩ {z | (Λ z).1 = w}).Finite := by
  set F := E ∩ polydisc Λ a δ ρ ∩ {z | (Λ z).1 = w} with hF
  have hFc : IsCompact F := by
    have := isCompact_inter_preimage hcl hQΩ hsph isCompact_singleton
      (singleton_subset_iff.mpr hw) (fun l hl h => hwL l hl h)
    simpa using this
  set ι : ComplexModel d → ComplexModel n := fun v => Λ.symm (w, v) with hι
  have hιc : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ ι := by
    have : ContDiff ℂ ∞ ι := Λ.symm.contDiff.comp (contDiff_const.prodMk contDiff_id)
    exact this.contMDiff
  set K := (fun z => (Λ z).2) '' F with hK
  have hKc : IsCompact K := hFc.image (continuous_snd.comp Λ.continuous)
  have hKmem : ∀ v ∈ ball (Λ a).2 ρ, v ∈ K ↔ ι v ∈ E := by
    intro v hv
    rw [mem_ball, dist_eq_norm] at hv
    constructor
    · rintro ⟨z, ⟨⟨hzE, -⟩, hzw⟩, rfl⟩
      have : ι (Λ z).2 = z := by
        simp only [hι]
        rw [← hzw]
        simp
      rw [this]
      exact hzE
    · intro hE
      refine ⟨ι v, ⟨⟨hE, ?_, ?_⟩, ?_⟩, ?_⟩
      · rw [mem_ball, dist_eq_norm] at hw
        simpa [hι] using hw
      · simpa [hι] using hv
      · simp [hι]
      · simp [hι]
  have hKfin : K.Finite := by
    refine CompactAnalyticFinite.finite_of_isCompact_of_presentation hKc fun v hv => ?_
    obtain ⟨z, ⟨⟨hzE, hzQ⟩, hzw⟩, rfl⟩ := hv
    have hvb : (Λ z).2 ∈ ball (Λ a).2 ρ := by
      rw [mem_ball, dist_eq_norm]
      exact hzQ.2
    have hιz : ι (Λ z).2 = z := by
      simp only [hι]
      rw [← hzw]
      simp
    have hzΩ : z ∈ Ω := hQΩ z hzQ.1.le hzQ.2.le
    have hzL : z ∉ L := fun h => disjoint_left.mp hEL hzE h
    obtain ⟨P⟩ := hEpres z hzΩ hzL
    rw [← hιz] at P
    exact nonempty_presentation_comp isOpen_ball hvb hιc.contMDiffOn P hKmem
  refine (hKfin.image ι).subset fun z hz => ?_
  refine ⟨(Λ z).2, ⟨z, hz, rfl⟩, ?_⟩
  simp only [hι]
  rw [← hz.2]
  simp

end Proper

end Hironaka.RemmertSteinFlat
