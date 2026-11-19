import Hironaka.Resolution.HironakaG34CoordinateScaling

/-!
# Explicit section of the weighted Gamma scalings

When the distinguished binomial coordinate is normal to the carrier and
is absent from the monomial, its weight is determined by the other weights.
Near the identity this realizes arbitrary weights on the carrier coordinates.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology
namespace Hironaka.HironakaG4WeightedGammaSection
noncomputable section

variable {n : ℕ}

/-- Replace the dependent weight by the monomial of the free weights. -/
def gammaWeights (s t : Fin n) (c : Fin n → ℕ) (b : Fin n → ℂ) : Fin n → ℂ :=
  fun i => if i = s then b t * ∏ j, b j ^ c j else b i

theorem continuous_gammaWeights (s t : Fin n) (c : Fin n → ℕ) :
    Continuous (gammaWeights s t c) := by
  refine continuous_pi fun i => ?_
  by_cases hi : i = s
  · simp only [gammaWeights, if_pos hi]
    exact (continuous_apply t).mul (continuous_finsetProd _ fun j _ => (continuous_apply j).pow (c j))
  · simpa only [gammaWeights, if_neg hi] using (continuous_apply i : Continuous fun b : Fin n → ℂ => b i)

theorem gammaWeights_one (s t : Fin n) (c : Fin n → ℕ) : gammaWeights s t c 1 = 1 := by
  funext i
  by_cases hi : i = s <;> simp [gammaWeights, hi]

/-- The weighted equation is satisfied whenever the dependent coordinate is
not used in the monomial and is distinct from the other factor. -/
theorem gammaWeights_weight (s t : Fin n) (c : Fin n → ℕ) (hst : t ≠ s) (hcs : c s = 0)
    (b : Fin n → ℂ) :
    gammaWeights s t c b s = gammaWeights s t c b t * ∏ j, (gammaWeights s t c b j) ^ c j := by
  have hprod : (∏ j, (gammaWeights s t c b j) ^ c j) = ∏ j, b j ^ c j := by
    apply Finset.prod_congr rfl
    intro j hj
    by_cases h : j = s
    · subst j
      simp [hcs]
    · simp [gammaWeights, h]
  rw [hprod]
  simp [gammaWeights, hst]

/-- Near the identity the explicit Gamma weights are nonzero. -/
theorem eventually_gammaWeights_nonzero (s t : Fin n) (c : Fin n → ℕ) :
    ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i, gammaWeights s t c b i ≠ 0 := by
  have h : Tendsto (gammaWeights s t c) (𝓝 1) (𝓝 1) := by
    simpa only [gammaWeights_one] using (continuous_gammaWeights s t c).tendsto 1
  have hopen : IsOpen {a : Fin n → ℂ | ∀ i, a i ≠ 0} := by
    have h' : IsOpen (⋂ i : Fin n, {a : Fin n → ℂ | a i ≠ 0}) :=
      isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const
    simpa only [mem_iInter, ofPred_forall] using h'
  exact h.eventually (hopen.mem_nhds (by simp))

/-- A total section, equal near the identity to the polynomial weight
replacement and mapping every input into the group of weighted scalings. -/
def gammaSection (s t : Fin n) (c : Fin n → ℕ) (b : Fin n → ℂ) : Fin n → ℂ :=
  if ∀ i, gammaWeights s t c b i ≠ 0 then gammaWeights s t c b else 1

theorem gammaSection_spec (s t : Fin n) (c : Fin n → ℕ) (hst : t ≠ s) (hcs : c s = 0)
    (b : Fin n → ℂ) : (∀ i, gammaSection s t c b i ≠ 0) ∧
      gammaSection s t c b s = gammaSection s t c b t * ∏ j, (gammaSection s t c b j) ^ c j := by
  by_cases h : ∀ i, gammaWeights s t c b i ≠ 0
  · simp only [gammaSection, if_pos h]
    exact ⟨h, gammaWeights_weight s t c hst hcs b⟩
  · simp [gammaSection, h]

/-- The section tends to the identity in the weighted nonzero locus and
realizes every coordinate outside the carrier's normal mask. -/
theorem gammaSection_partial_realization (s t : Fin n) (c : Fin n → ℕ) (S : Finset (Fin n))
    (hs : s ∈ S) (hst : t ≠ s) (hcs : c s = 0) :
    Tendsto (gammaSection s t c) (𝓝 1)
      (𝓝[{a : Fin n → ℂ | (∀ i, a i ≠ 0) ∧ a s = a t * ∏ j, a j ^ c j}] 1) ∧
    ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S, gammaSection s t c b i = b i := by
  have heq : gammaSection s t c =ᶠ[𝓝 1] gammaWeights s t c := by
    filter_upwards [eventually_gammaWeights_nonzero s t c] with b hb
    simp [gammaSection, hb]
  have hlim : Tendsto (gammaSection s t c) (𝓝 1) (𝓝 1) := by
    apply (show Tendsto (gammaWeights s t c) (𝓝 1) (𝓝 1) from by
      simpa only [gammaWeights_one] using (continuous_gammaWeights s t c).tendsto 1).congr'
    exact heq.symm
  refine ⟨tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (gammaSection_spec s t c hst hcs)⟩, ?_⟩
  filter_upwards [heq] with b hb i hi
  rw [hb]
  have his : i ≠ s := fun h => hi (h ▸ hs)
  simp [gammaWeights, his]

end
end Hironaka.HironakaG4WeightedGammaSection
