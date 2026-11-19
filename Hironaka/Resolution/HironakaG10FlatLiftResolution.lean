import Hironaka.Resolution.HironakaG10FlatRelationLift
import Hironaka.Resolution.HironakaG10FlatGenerationLocus

/-! # Lifting a finite resolution of the fibre to a finite resolution of a `w`-flat sheaf

Douady 1966, §8 Prop. 1 (proof) and §7 Th. 1: let `𝓕 = coker A` on `ℂ × P` with `w` regular on `𝓕` at
`y = (0, z₀)` (flat over the `w`-line there), and let `e₀ = A(0,·), e₁, …, e_m` (`e_m = 0`) be a finite
free resolution of the fibre `𝓕(0)` near `z₀`. Then there is a finite free resolution
`d₀ = A, d₁, …, d_m` (`d_m = 0`) of `𝓕` on an open neighbourhood of `y` whose restrictions to `w = 0`
are the `e_k` near `z₀` (`exists_lift_chain`).

* `exactStartOn_of_lifts`: relations `τ_k` of `D` at `y` whose restrictions are the columns of `G`, where
  `(G, E)` is an exact start of the fibre (`E = D(0,·)`), are the columns of an exact start `(τ, D)` on an
  open neighbourhood of `y` (Nakayama `isCombinationAt_of_slice_generates` + `exists_generatesRelationsOn`).
* `exists_lift_step`: with `w` regular on `coker D` at `y`, such lifts exist (`exists_lift_relation`).
* `liftChain`: the lifted matrices, by recursion with choice; **`exists_lift_chain`**.
BP: hironaka-g10-flat-lift-resolution.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatLiftResolution
noncomputable section
open OkaRelationSheaf HironakaG10FlatResolutionStart HironakaG10FlatSliceResolution
  HironakaG10FlatRelationLift HironakaG10FlatGenerationLocus

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- **Lifts of the columns of a fibre exact start give an exact start on an open set.** -/
theorem exactStartOn_of_lifts (hX : OkaProperty (ℂ × P)) {a b c : ℕ} {D : Fin a → Fin b → ℂ × P → ℂ}
    {E : Fin a → Fin b → P → ℂ} {G : Fin b → Fin c → P → ℂ} {U₀ : Set P} {z₀ : P}
    (hz₀ : z₀ ∈ U₀) (hGE : ExactStartOn U₀ G E) (hD : ∀ i j, HolAt (D i j) ((0 : ℂ), z₀))
    (hDE : ∀ᶠ z in 𝓝 z₀, ∀ i j, D i j ((0 : ℂ), z) = E i j z)
    {τ : Fin c → Fin b → ℂ × P → ℂ} (hτ : ∀ k, IsRelationAt D ((0 : ℂ), z₀) (τ k))
    (hτG : ∀ᶠ z in 𝓝 z₀, ∀ j k, τ k j ((0 : ℂ), z) = G j k z) :
    ∃ V : Set (ℂ × P), IsOpen V ∧ ((0 : ℂ), z₀) ∈ V ∧ ExactStartOn V (fun j k => τ k j) D := by
  have hgen : ∀ r, IsRelationAt D ((0 : ℂ), z₀) r → IsCombinationAt τ ((0 : ℂ), z₀) r := by
    refine isCombinationAt_of_slice_generates hX hD hτ fun bv hbv => ?_
    -- a relation of the fibre `D(0,·)` is a relation of `E`
    have hbE : IsRelationAt E z₀ bv := ⟨hbv.1, fun i => by
      filter_upwards [hbv.2 i, hDE] with z hz hzE
      simpa [sliceZero, hzE] using hz⟩
    obtain ⟨lam, hlam, hlamG⟩ := hGE.exact z₀ hz₀ bv hbE
    refine ⟨lam, hlam, fun j => ?_⟩
    filter_upwards [hlamG j, hτG] with z hz hzG
    rw [hz]
    exact Finset.sum_congr rfl fun k _ => by simp only [columns, hzG j k]
  obtain ⟨V, hVo, hyV, hDV, hgenV⟩ := exists_generatesRelationsOn hX hD (fun k j => (hτ k).1 j)
    (fun k i => (hτ k).2 i) hgen
  exact ⟨V, hVo, hyV, exactStartOn_of_generates hDV hgenV⟩

/-- **Lifts exist** when `w` is regular on `coker D` at `(0, z₀)`. -/
theorem exists_lift_step {a b c : ℕ} {D : Fin a → Fin b → ℂ × P → ℂ} {E : Fin a → Fin b → P → ℂ}
    {G : Fin b → Fin c → P → ℂ} {U₀ : Set P} {z₀ : P} (hU₀ : IsOpen U₀) (hz₀ : z₀ ∈ U₀)
    (hGE : ExactStartOn U₀ G E) (hD : ∀ i j, HolAt (D i j) ((0 : ℂ), z₀))
    (hDE : ∀ᶠ z in 𝓝 z₀, ∀ i j, D i j ((0 : ℂ), z) = E i j z)
    (hreg : RegularAt D (fun x => x.1) ((0 : ℂ), z₀)) :
    ∃ τ : Fin c → Fin b → ℂ × P → ℂ, (∀ k, IsRelationAt D ((0 : ℂ), z₀) (τ k)) ∧
      ∀ j k z, τ k j ((0 : ℂ), z) = G j k z := by
  have hcol : ∀ k, IsRelationAt (sliceZero D) z₀ (fun j z => G j k z) := by
    intro k
    refine ⟨fun j => holAt_of_differentiableOn hU₀ (hGE.holG j k) hz₀, fun i => ?_⟩
    filter_upwards [hDE, hU₀.mem_nhds hz₀] with z hzE hzU
    simp only [sliceZero, hzE]
    rw [← hGE.comp i k z hzU]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  choose τ hτ hτG using fun k => exists_lift_relation hD hreg _ (hcol k)
  exact ⟨τ, hτ, fun j k z => hτG k j z⟩

/-- One lifting step, chosen (the zero matrix if no lift exists). -/
def liftStep {a b c : ℕ} (D : Fin a → Fin b → ℂ × P → ℂ) (G : Fin b → Fin c → P → ℂ) (z₀ : P) :
    Fin b → Fin c → ℂ × P → ℂ :=
  haveI := Classical.propDecidable
  if h : ∃ τ : Fin c → Fin b → ℂ × P → ℂ, (∀ k, IsRelationAt D ((0 : ℂ), z₀) (τ k)) ∧
      ∀ j k z, τ k j ((0 : ℂ), z) = G j k z then fun j k => h.choose k j else 0

theorem liftStep_spec {a b c : ℕ} {D : Fin a → Fin b → ℂ × P → ℂ} {G : Fin b → Fin c → P → ℂ}
    {z₀ : P} (h : ∃ τ : Fin c → Fin b → ℂ × P → ℂ, (∀ k, IsRelationAt D ((0 : ℂ), z₀) (τ k)) ∧
      ∀ j k z, τ k j ((0 : ℂ), z) = G j k z) :
    (∀ k, IsRelationAt D ((0 : ℂ), z₀) (fun j => liftStep D G z₀ j k)) ∧
      ∀ j k z, liftStep D G z₀ j k ((0 : ℂ), z) = G j k z := by
  unfold liftStep
  rw [dif_pos h]
  exact ⟨h.choose_spec.1, h.choose_spec.2⟩

/-- The lifted matrices `d₀ = A`, `d_{k+1} = liftStep d_k e_{k+1}`. -/
def liftChain {r : ℕ → ℕ} (e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ)
    (A : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ) (z₀ : P) :
    (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → ℂ × P → ℂ
  | 0 => A
  | k + 1 => liftStep (liftChain e A z₀ k) (e (k + 1)) z₀

/-- **Lifting a finite resolution of the fibre** (Douady 1966, §8 Prop. 1, proof). Let `ℂ × P` have
Oka's property, `e₀, …, e_m` (`0 < m`) a finite free resolution of the fibre on an open `U₀ ∋ z₀`
(`(e_{k+1}, e_k)` exact starts on `U₀`, `e_m = 0` on `U₀`), and `A` holomorphic near `y = (0, z₀)` with
`A(0,·) = e₀` near `z₀` and `w` regular on `coker A` at `y`. Then on an open `V ∋ y` there is a finite
free resolution `d₀ = A, …, d_m` (`d_m = 0`) with `d_k(0,·) = e_k` near `z₀`. -/
theorem exists_lift_chain (hX : OkaProperty (ℂ × P)) {m : ℕ} (hm : 0 < m) {r : ℕ → ℕ}
    {e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ} {U₀ : Set P} {z₀ : P} (hU₀ : IsOpen U₀)
    (hz₀ : z₀ ∈ U₀) (he : ∀ k < m, ExactStartOn U₀ (e (k + 1)) (e k))
    (htop : ∀ i j, ∀ z ∈ U₀, e m i j z = 0) {A : Fin (r 0) → Fin (r 1) → ℂ × P → ℂ}
    (hA : ∀ i j, HolAt (A i j) ((0 : ℂ), z₀)) (hAe : ∀ᶠ z in 𝓝 z₀, ∀ i j, A i j ((0 : ℂ), z) = e 0 i j z)
    (hreg : RegularAt A (fun x => x.1) ((0 : ℂ), z₀)) :
    ∃ V : Set (ℂ × P), IsOpen V ∧ ((0 : ℂ), z₀) ∈ V ∧
      ∃ d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → ℂ × P → ℂ, d 0 = A ∧
        (∀ k i j, DifferentiableOn ℂ (d k i j) V) ∧ (∀ k < m, ExactStartOn V (d (k + 1)) (d k)) ∧
        (∀ i j, ∀ x ∈ V, d m i j x = 0) ∧
        ∀ k ≤ m, ∀ᶠ z in 𝓝 z₀, ∀ i j, d k i j ((0 : ℂ), z) = e k i j z := by
  set y : ℂ × P := ((0 : ℂ), z₀)
  set L := liftChain e A z₀
  -- the invariant along the chain
  have hinv : ∀ k, k < m → (∀ i j, HolAt (L k i j) y) ∧
      (∀ᶠ z in 𝓝 z₀, ∀ i j, L k i j ((0 : ℂ), z) = e k i j z) ∧ RegularAt (L k) (fun x => x.1) y ∧
      (k + 1 < m → ∃ V : Set (ℂ × P), IsOpen V ∧ y ∈ V ∧ ExactStartOn V (L (k + 1)) (L k)) := by
    intro k
    induction k with
    | zero =>
        intro h0
        refine ⟨hA, hAe, hreg, fun h1 => ?_⟩
        obtain ⟨τ, hτ, hτG⟩ := exists_lift_step hU₀ hz₀ (he 0 h0) hA hAe hreg
        have hspec := liftStep_spec (D := L 0) (G := e 1) (z₀ := z₀) ⟨τ, hτ, hτG⟩
        exact exactStartOn_of_lifts hX hz₀ (he 0 h0) hA hAe hspec.1
          (Eventually.of_forall fun z j k => hspec.2 j k z)
    | succ k ih =>
        intro hk
        obtain ⟨hhol, hsl, hrg, hex⟩ := ih (Nat.lt_of_succ_lt hk)
        obtain ⟨V, hVo, hyV, hVex⟩ := hex hk
        have hspec := liftStep_spec (D := L k) (G := e (k + 1)) (z₀ := z₀)
          (exists_lift_step hU₀ hz₀ (he k (Nat.lt_of_succ_lt hk)) hhol hsl hrg)
        have hhol' : ∀ i j, HolAt (L (k + 1) i j) y := fun i j => (hspec.1 j).1 i
        have hsl' : ∀ᶠ z in 𝓝 z₀, ∀ i j, L (k + 1) i j ((0 : ℂ), z) = e (k + 1) i j z :=
          Eventually.of_forall fun z i j => hspec.2 i j z
        have hrg' : RegularAt (L (k + 1)) (fun x => x.1) y :=
          regularAt_of_exactStartOn hVex hVo hyV (nonZeroDivisorAt_fst y)
        refine ⟨hhol', hsl', hrg', fun h2 => ?_⟩
        obtain ⟨τ, hτ, hτG⟩ := exists_lift_step hU₀ hz₀ (he (k + 1) hk) hhol' hsl' hrg'
        have hspec' := liftStep_spec (D := L (k + 1)) (G := e (k + 2)) (z₀ := z₀) ⟨τ, hτ, hτG⟩
        exact exactStartOn_of_lifts hX hz₀ (he (k + 1) hk) hhol' hsl' hspec'.1
          (Eventually.of_forall fun z j k => hspec'.2 j k z)
  -- the final chain: `L k` below `m`, then `0`
  set d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → ℂ × P → ℂ :=
    fun k => if k < m then L k else 0 with hd
  have hdL : ∀ k, k < m → d k = L k := fun k hk => if_pos hk
  have hdm : d m = 0 := if_neg (lt_irrefl m)
  -- exact starts in every degree, each on some open set
  have hpair : ∀ k, k < m → ∃ V : Set (ℂ × P), IsOpen V ∧ y ∈ V ∧ ExactStartOn V (d (k + 1)) (d k) := by
    intro k hk
    rw [hdL k hk]
    by_cases hk1 : k + 1 < m
    · rw [hdL (k + 1) hk1]
      exact (hinv k hk).2.2.2 hk1
    · have hkm : k + 1 = m := by omega
      subst hkm
      obtain ⟨hhol, hsl, -, -⟩ := hinv k hk
      have hz : ∀ᶠ z in 𝓝 z₀, ∀ j l, (0 : Fin (r (k + 2)) → Fin (r (k + 1)) → ℂ × P → ℂ) l j
          ((0 : ℂ), z) = e (k + 1) j l z := by
        filter_upwards [hU₀.mem_nhds hz₀] with z hz j l
        rw [htop j l z hz]
        rfl
      obtain ⟨V, hVo, hyV, hVex⟩ := exactStartOn_of_lifts hX hz₀ (he k hk) hhol hsl
        (fun l => ⟨fun j => holAt_const 0 y, fun i => Eventually.of_forall fun x => by simp⟩) hz
      refine ⟨V, hVo, hyV, ?_⟩
      rw [hdm]
      exact hVex
  choose! Vs hVso hyVs hVsex using hpair
  set V : Set (ℂ × P) := ⋂ k ∈ Finset.range m, Vs k with hV
  have hVo : IsOpen V := isOpen_biInter_finset fun k hk => hVso k (Finset.mem_range.mp hk)
  have hyV : y ∈ V := mem_iInter₂.2 fun k hk => hyVs k (Finset.mem_range.mp hk)
  have hVk : ∀ k, k < m → V ⊆ Vs k := fun k hk =>
    biInter_subset_of_mem (Finset.mem_coe.2 (Finset.mem_range.2 hk))
  have hex : ∀ k < m, ExactStartOn V (d (k + 1)) (d k) := fun k hk =>
    (hVsex k hk).mono (hVk k hk)
  refine ⟨V, hVo, hyV, d, if_pos hm, fun k i j => ?_, hex, fun i j x _ => by rw [hdm]; rfl,
    fun k hk => ?_⟩
  · by_cases hk : k < m
    · exact (hex k hk).holF i j
    · by_cases hkm : k = m
      · subst hkm
        rw [hdm]
        exact differentiableOn_const 0
      · rw [show d k = 0 from if_neg hk]
        exact differentiableOn_const 0
  · by_cases hkm : k < m
    · rw [hdL k hkm]
      exact (hinv k hkm).2.1
    · have hk' : k = m := le_antisymm hk (not_lt.mp hkm)
      subst hk'
      filter_upwards [hU₀.mem_nhds hz₀] with z hz i j
      rw [hdm, htop i j z hz]
      rfl

end
end Hironaka.HironakaG10FlatLiftResolution
