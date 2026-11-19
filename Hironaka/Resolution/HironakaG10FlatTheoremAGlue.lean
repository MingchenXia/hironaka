import Hironaka.Coherence.OkaCoherence

/-! # The point case and separation for Cartan relation gluing

Route: `work/hironaka-resume-20261111/G10F/ROUTE-THEOREM-A.md` §1, module 1.
* `TA Q`, `TB Q`: Theorem A / Theorem B (relation-sheaf form) on a compact set `Q`.
* `exists_sep_nhds` (proved): neighbourhood lemma for two compact pieces meeting in `Q*`.
The general union steps remain to be proved.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatTheoremAGlue
open OkaRelationSheaf

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

variable (X) in
/-- Theorem A on `Q` for relation sheaves (the body of `HironakaG10LocSheafExact.RelationsTheoremA` at `K = Q`). -/
def TA (Q : Set X) : Prop :=
  ∀ U : Set X, IsOpen U → Q ⊆ U → ∀ (κ ι : Type) [Fintype κ] [Fintype ι]
    (F : κ → ι → X → ℂ), (∀ i j, DifferentiableOn ℂ (F i j) U) →
      ∃ W : Set X, IsOpen W ∧ Q ⊆ W ∧ W ⊆ U ∧
        ∃ (μ : Type) (_ : Fintype μ) (σ : μ → ι → X → ℂ), GeneratesRelationsOn F W σ

variable (X) in
/-- Theorem B on `Q` in the form used by the gluing: a relation of `F` holomorphic near `Q` is a combination of
generators `σ` of the relations, with coefficients holomorphic near `Q`. -/
def TB (Q : Set X) : Prop :=
  ∀ U : Set X, IsOpen U → Q ⊆ U → ∀ (κ ι μ : Type) [Fintype κ] [Fintype ι] [Fintype μ]
    (F : κ → ι → X → ℂ) (σ : μ → ι → X → ℂ), (∀ i j, DifferentiableOn ℂ (F i j) U) →
      GeneratesRelationsOn F U σ → ∀ v : ι → X → ℂ, (∀ j, DifferentiableOn ℂ (v j) U) →
        (∀ i, ∀ x ∈ U, ∑ j, v j x * F i j x = 0) →
          ∃ W : Set X, IsOpen W ∧ Q ⊆ W ∧ W ⊆ U ∧ ∃ A : μ → X → ℂ,
            (∀ k, DifferentiableOn ℂ (A k) W) ∧ ∀ j, ∀ x ∈ W, v j x = ∑ k, A k x * σ k j x

omit [NormedSpace ℂ X] in
/-- **Neighbourhood lemma.** If the compact pieces `Q'`, `Q''` meet inside the open `N`, neighbourhoods `W'`, `W''`
of them can be shrunk so that they meet only inside `N`. -/
theorem exists_sep_nhds {Q' Q'' W' W'' N : Set X} (hQ' : IsCompact Q') (hQ'' : IsCompact Q'')
    (hW' : IsOpen W') (hW'' : IsOpen W'') (hN : IsOpen N) (h' : Q' ⊆ W') (h'' : Q'' ⊆ W'')
    (hint : Q' ∩ Q'' ⊆ N) :
    ∃ W'₀ W''₀ : Set X, IsOpen W'₀ ∧ IsOpen W''₀ ∧ Q' ⊆ W'₀ ∧ Q'' ⊆ W''₀ ∧ W'₀ ⊆ W' ∧
      W''₀ ⊆ W'' ∧ W'₀ ∩ W''₀ ⊆ N := by
  have hc' : IsCompact (Q' \ N) := hQ'.diff hN
  have hc'' : IsCompact (Q'' \ N) := hQ''.diff hN
  have hdisj : Disjoint (Q' \ N) (Q'' \ N) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx.2 (hint ⟨hx.1, hx'.1⟩)
  obtain ⟨A, B, hA, hB, hcA, hcB, hAB⟩ := SeparatedNhds.of_isCompact_isCompact hc' hc'' hdisj
  refine ⟨W' ∩ (A ∪ N), W'' ∩ (B ∪ N), hW'.inter (hA.union hN), hW''.inter (hB.union hN),
    fun x hx => ⟨h' hx, ?_⟩, fun x hx => ⟨h'' hx, ?_⟩, inter_subset_left, inter_subset_left, ?_⟩
  · by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl (hcA ⟨hx, hxN⟩)
  · by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl (hcB ⟨hx, hxN⟩)
  · rintro x ⟨⟨-, hxA⟩, ⟨-, hxB⟩⟩
    rcases hxA with hxA | hxN
    · rcases hxB with hxB | hxN
      · exact absurd hxB (Set.disjoint_left.mp hAB hxA)
      · exact hxN
    · exact hxN

variable (X) in
/-- Cousin pair (additive): a function holomorphic near `Q' ∩ Q''` is a difference of functions holomorphic near
`Q'` and near `Q''`, near `Q' ∩ Q''`. -/
def CousinPair (Q' Q'' : Set X) : Prop :=
  ∀ N : Set X, IsOpen N → Q' ∩ Q'' ⊆ N → ∀ f : X → ℂ, DifferentiableOn ℂ f N →
    ∃ N' N'' N₀ : Set X, IsOpen N' ∧ IsOpen N'' ∧ IsOpen N₀ ∧ Q' ⊆ N' ∧ Q'' ⊆ N'' ∧ Q' ∩ Q'' ⊆ N₀ ∧
      ∃ f' f'' : X → ℂ, DifferentiableOn ℂ f' N' ∧ DifferentiableOn ℂ f'' N'' ∧
        ∀ x ∈ N₀, f x = f' x - f'' x


/-- Oka coherence proves the relation-generation property on a point. -/
theorem ta_singleton (n : ℕ) (x : EuclideanSpace ℂ (Fin n)) :
    TA (EuclideanSpace ℂ (Fin n)) {x} := by
  intro U hU hUsub κ ι _ _ F hF
  have hxU : x ∈ U := hUsub (Set.mem_singleton x)
  obtain ⟨V, hV, hxV, μ, hμ, σ, hσ⟩ :=
    OkaCoherence.okaProperty_euclidean n κ ι F x
      (fun i j => holAt_of_differentiableOn hU (hF i j) hxU)
  exact ⟨V ∩ U, hV.inter hU, singleton_subset_iff.mpr ⟨hxV,hxU⟩,
    inter_subset_right, μ, hμ, σ, hσ.mono inter_subset_left⟩

/-- Germwise generation gives the corresponding relation-solving property on a point. -/
theorem tb_singleton (x : X) : TB X {x} := by
  classical
  intro U hU hUsub κ ι μ _ _ _ F σ hF hσ v hv hrel
  have hxU : x ∈ U := hUsub (Set.mem_singleton x)
  have hR : IsRelationAt F x v := ⟨fun j => holAt_of_differentiableOn hU (hv j) hxU,
    fun i => eventually_of_mem (hU.mem_nhds hxU) fun z hz => hrel i z hz⟩
  obtain ⟨c, hc, heq⟩ := hσ.2.2 x hxU v hR
  have hnear : ∀ᶠ z in 𝓝 x, z ∈ U ∧ (∀ k, DifferentiableAt ℂ (c k) z) ∧
      (∀ j, v j z = ∑ k, c k z * σ k j z) := by
    filter_upwards [hU.mem_nhds hxU, Filter.eventually_all.mpr hc,
      Filter.eventually_all.mpr heq] with z hzU hzc hze
    exact ⟨hzU,hzc,hze⟩
  obtain ⟨W, hW, ho, hxW⟩ := mem_nhds_iff.mp hnear
  refine ⟨W, ho, singleton_subset_iff.mpr hxW, fun z hz => (hW hz).1,
    c, fun k z hz => ((hW hz).2.1 k).differentiableWithinAt, ?_⟩
  intro j z hz
  exact (hW hz).2.2 j

end Hironaka.HironakaG10FlatTheoremAGlue
