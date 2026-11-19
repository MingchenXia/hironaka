import Hironaka.Resolution.HironakaG10FlatSubPresentation
import Hironaka.Resolution.HironakaG10FlatRelationLift

/-! # The `φ`-torsion filtration of a presented sheaf (Noetherian stationarity)

Douady 1966, §7 n° 4, proof of Th. 1: for `𝓕 = coker A` and a function `φ` (the last coordinate
`ζ`), the submodules `N_j = {v | φ^j v ∈ im A}` of germs at `y` increase and are stationary when
the ring of germs is Noetherian. With `T` generating `N_{j₀}`:

* `𝓕/𝓕_tors = coker [A | T]` has `φ` regular at `y` (**`exists_torsionFiltration`**);
* the `φ`-torsion `𝓕_tors = (im A + im T)/im A` is killed by `φ^{j₀}`; for a presentation `C'` of it
  (`HironakaG10FlatSubPresentation.exists_subPresentation`), `φ^{j₀}·1 = C' W` near `y`
  (**`exists_pow_kill`**).

Also: `regularAt_comp_homeomorph` (regularity transports along biholomorphic homeomorphisms, e.g.
the swap `ℂ × P ≃ P × ℂ`); `exists_matrix_of_isCombinationAt` (column-wise germ combinations as a
matrix identity); `isCombinationAt_catCols_left/right`.
BP: hironaka-g10-flat-torsion-filtration.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatTorsionFiltration
noncomputable section
open OkaRelationSheaf OkaGermBridge HolGerm HironakaG10FlatResolutionStart
  HironakaG10FlatSliceResolution HironakaG10FlatRelationLift HironakaG10FlatExtensionStep

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ## Transport along biholomorphic homeomorphisms -/

section Transport
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {ι₀ ι₁ : Type*} [Fintype ι₁]

/-- **Regularity transports along a biholomorphic homeomorphism.** -/
theorem regularAt_comp_homeomorph (φ : X ≃ₜ Y) (hφ : ∀ x, DifferentiableAt ℂ φ x)
    (hφs : ∀ y, DifferentiableAt ℂ φ.symm y) {F : ι₀ → ι₁ → Y → ℂ} {f : Y → ℂ} {x : X}
    (h : RegularAt F f (φ x)) : RegularAt (fun i j => F i j ∘ φ) (f ∘ φ) x := by
  intro c hc hfc
  have hsx : φ.symm (φ x) = x := φ.symm_apply_apply x
  have ht : Tendsto φ.symm (𝓝 (φ x)) (𝓝 x) := by
    have := φ.symm.continuous.tendsto (φ x)
    rwa [hsx] at this
  have hc' : ∀ i, HolAt (c i ∘ φ.symm) (φ x) := fun i => by
    have h1 : HolAt (c i) (φ.symm (φ x)) := by rw [hsx]; exact hc i
    exact h1.comp φ.symm.continuous hφs
  obtain ⟨e, he, hee⟩ := hfc
  have h1 : IsCombinationAt (columns F) (φ x) (fun i y => f y * (c i ∘ φ.symm) y) := by
    refine ⟨fun k => e k ∘ φ.symm, fun k => ?_, fun i => ?_⟩
    · have h1 : HolAt (e k) (φ.symm (φ x)) := by rw [hsx]; exact he k
      exact h1.comp φ.symm.continuous hφs
    · filter_upwards [ht.eventually (hee i)] with y hy
      simp only [Function.comp_apply, columns, Homeomorph.apply_symm_apply] at hy ⊢
      exact hy
  obtain ⟨d, hd, hdd⟩ := h _ hc' h1
  refine ⟨fun k => d k ∘ φ, fun k => (hd k).comp φ.continuous hφ, fun i => ?_⟩
  filter_upwards [(φ.continuous.tendsto x).eventually (hdd i)] with x' hx'
  simpa only [Function.comp_apply, columns, Homeomorph.symm_apply_apply] using hx'

end Transport

/-! ## Matrix forms of germ combinations -/

section Matrix
variable {p q n : ℕ}

theorem holAt_pow {φ : X → ℂ} {y : X} (hφ : HolAt φ y) (j : ℕ) : HolAt (fun x => φ x ^ j) y :=
  hφ.mono fun _ hx => hx.fun_pow j

/-- Column-wise germ combinations of the columns of `C` as a matrix identity `C W = v` near `y`. -/
theorem exists_matrix_of_isCombinationAt {C : Fin p → Fin q → X → ℂ} {y : X}
    {v : Fin n → Fin p → X → ℂ} (h : ∀ k, IsCombinationAt (columns C) y (v k)) :
    ∃ W : Fin q → Fin n → X → ℂ, (∀ i k, HolAt (W i k) y) ∧
      ∀ᶠ x in 𝓝 y, ∀ i k, ∑ l, C i l x * W l k x = v k i x := by
  choose c hc hcv using h
  refine ⟨fun l k => c k l, fun l k => hc k l, ?_⟩
  filter_upwards [eventually_all.2 fun k => eventually_all.2 fun i => hcv k i] with x hx i k
  rw [hx k i]
  simp only [columns]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- A combination of the columns of `A` is one of the columns of `[A | T]`. -/
theorem isCombinationAt_catCols_left {a b t : ℕ} {A : Fin a → Fin b → X → ℂ}
    (T : Fin a → Fin t → X → ℂ) {y : X} {v : Fin a → X → ℂ} (h : IsCombinationAt (columns A) y v) :
    IsCombinationAt (columns (catCols A T)) y v := by
  obtain ⟨c, hc, hcv⟩ := h
  refine ⟨fun k => Sum.elim c (fun _ _ => 0) (finSumFinEquiv.symm k), fun k => ?_, fun j => ?_⟩
  · show HolAt (Sum.elim c (fun _ _ => (0 : ℂ)) (finSumFinEquiv.symm k)) y
    rcases finSumFinEquiv.symm k with k' | k'
    · exact hc k'
    · exact holAt_const 0 y
  · filter_upwards [hcv j] with x hx
    rw [hx, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    simp [columns, catCols]

/-- A combination of the columns of `T` is one of the columns of `[A | T]`. -/
theorem isCombinationAt_catCols_right {a b t : ℕ} (A : Fin a → Fin b → X → ℂ)
    {T : Fin a → Fin t → X → ℂ} {y : X} {v : Fin a → X → ℂ} (h : IsCombinationAt (columns T) y v) :
    IsCombinationAt (columns (catCols A T)) y v := by
  obtain ⟨c, hc, hcv⟩ := h
  refine ⟨fun k => Sum.elim (fun _ _ => 0) c (finSumFinEquiv.symm k), fun k => ?_, fun j => ?_⟩
  · show HolAt (Sum.elim (fun _ _ => (0 : ℂ)) c (finSumFinEquiv.symm k)) y
    rcases finSumFinEquiv.symm k with k' | k'
    · exact holAt_const 0 y
    · exact hc k'
  · filter_upwards [hcv j] with x hx
    rw [hx, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    simp [columns, catCols]

theorem holAt_catCols {a b t : ℕ} {A : Fin a → Fin b → X → ℂ} {T : Fin a → Fin t → X → ℂ} {y : X}
    (hA : ∀ i j, HolAt (A i j) y) (hT : ∀ i j, HolAt (T i j) y) (i : Fin a) (j : Fin (b + t)) :
    HolAt (catCols A T i j) y := by
  show HolAt (Sum.elim (A i) (T i) (finSumFinEquiv.symm j)) y
  rcases finSumFinEquiv.symm j with j' | j'
  · exact hA i j'
  · exact hT i j'

/-- **The torsion of the subsheaf generated by `T` is killed by `φ^{j₀}`**: if every column of
`φ^{j₀} T` lies in `im A` at `y` and `C'` presents `{v | T v ∈ im A}` (the hypothesis `hgen` of
`HironakaG10FlatSubPresentation.exists_subPresentation`), then `φ^{j₀}·1 = C' W` near `y`. -/
theorem exists_pow_kill {a b t c j₀ : ℕ} {A : Fin a → Fin b → X → ℂ} {T : Fin a → Fin t → X → ℂ}
    {C' : Fin t → Fin c → X → ℂ} {φ : X → ℂ} {y : X} (hφ : HolAt φ y)
    (hT : ∀ k, IsCombinationAt (columns A) y (fun i x => φ x ^ j₀ * T i k x))
    (hgen : ∀ v : Fin t → X → ℂ, (∀ j, HolAt (v j) y) →
      IsCombinationAt (columns A) y (fun i x => ∑ l, T i l x * v l x) → IsCombinationAt (columns C') y v) :
    ∃ W : Fin c → Fin t → X → ℂ, (∀ i k, HolAt (W i k) y) ∧
      ∀ᶠ x in 𝓝 y, ∀ i k, ∑ l, C' i l x * W l k x = if i = k then φ x ^ j₀ else 0 := by
  have hφj : HolAt (fun x => φ x ^ j₀) y := holAt_pow hφ j₀
  refine exists_matrix_of_isCombinationAt (v := fun k i x => if i = k then φ x ^ j₀ else 0)
    fun k => hgen _ (fun j => ?_) ?_
  · rcases eq_or_ne j k with rfl | h
    · simpa using hφj
    · simpa [h] using holAt_const (0 : ℂ) y
  · have : (fun i x => ∑ l, T i l x * (if l = k then φ x ^ j₀ else 0)) =
        fun i x => φ x ^ j₀ * T i k x := by
      funext i x
      simp [mul_comm]
    rw [this]
    exact hT k

end Matrix

/-! ## The torsion filtration -/

section Germ
variable {a b : ℕ}

/-- The germs at `y` of the combinations of the columns of `A`. -/
def imSubmodule (A : Fin a → Fin b → X → ℂ) (y : X) : Submodule (HolGerm X) (Fin a → HolGerm X) :=
  Submodule.span (HolGerm X) (Set.range fun k => germVec y (columns A k))

/-- `N_j = {v | φ^j v ∈ im A}` (germs at `y`). -/
def torsionSubmodule (A : Fin a → Fin b → X → ℂ) (φ : X → ℂ) (y : X) (j : ℕ) :
    Submodule (HolGerm X) (Fin a → HolGerm X) where
  carrier := {v | germAt y φ ^ j • v ∈ imSubmodule A y}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_ofPred_eq, smul_add] at hv hw ⊢
    exact Submodule.add_mem _ hv hw
  zero_mem' := by simp
  smul_mem' c v hv := by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [smul_comm]
    exact Submodule.smul_mem _ c hv

theorem mem_torsionSubmodule {A : Fin a → Fin b → X → ℂ} {φ : X → ℂ} {y : X} {j : ℕ}
    {v : Fin a → HolGerm X} : v ∈ torsionSubmodule A φ y j ↔ germAt y φ ^ j • v ∈ imSubmodule A y :=
  Iff.rfl

theorem torsionSubmodule_mono (A : Fin a → Fin b → X → ℂ) (φ : X → ℂ) (y : X) :
    Monotone (torsionSubmodule A φ y) := by
  refine monotone_nat_of_le_succ fun j v hv => ?_
  rw [mem_torsionSubmodule] at hv ⊢
  rw [pow_succ', mul_smul]
  exact Submodule.smul_mem _ _ hv

theorem imSubmodule_le_torsionSubmodule (A : Fin a → Fin b → X → ℂ) (φ : X → ℂ) (y : X) (j : ℕ) :
    imSubmodule A y ≤ torsionSubmodule A φ y j :=
  fun _ hv => Submodule.smul_mem _ _ hv

theorem germVec_mem_imSubmodule_iff {A : Fin a → Fin b → X → ℂ} {y : X}
    (hA : ∀ i j, HolAt (A i j) y) {v : Fin a → X → ℂ} (hv : ∀ i, HolAt (v i) y) :
    germVec y v ∈ imSubmodule A y ↔ IsCombinationAt (columns A) y v :=
  germVec_mem_span_iff (fun k j => hA j k) hv

theorem germVec_mul {φ : X → ℂ} {y : X} (hφ : HolAt φ y) {v : Fin a → X → ℂ}
    (hv : ∀ i, HolAt (v i) y) : germVec y (fun i x => φ x * v i x) = germAt y φ • germVec y v := by
  funext i
  simp only [germVec, Pi.smul_apply, smul_eq_mul]
  exact germAt_mul hφ (hv i)

theorem germVec_pow_mul {φ : X → ℂ} {y : X} (hφ : HolAt φ y) {v : Fin a → X → ℂ}
    (hv : ∀ i, HolAt (v i) y) (j : ℕ) :
    germVec y (fun i x => φ x ^ j * v i x) = germAt y φ ^ j • germVec y v := by
  funext i
  simp only [germVec, Pi.smul_apply, smul_eq_mul]
  rw [germAt_mul (holAt_pow hφ j) (hv i), germAt_pow hφ j]

/-- **The `φ`-torsion filtration** (Douady §7 n° 4). If the ring of germs is Noetherian, there are
`j₀` and holomorphic `T : L_t → L_a` such that the columns of `φ^{j₀} T` lie in `im A` at `y` and `φ`
is regular on `coker [A | T]` at `y` (the columns of `T` generate `N_{j₀} = N_{j₀ + 1}`, so
`coker [A | T] = 𝓕/𝓕_tors`). -/
theorem exists_torsionFiltration [IsNoetherianRing (HolGerm X)] {A : Fin a → Fin b → X → ℂ}
    {φ : X → ℂ} {y : X} (hA : ∀ i j, HolAt (A i j) y) (hφ : HolAt φ y) :
    ∃ (t j₀ : ℕ) (T : Fin a → Fin t → X → ℂ), (∀ i k, HolAt (T i k) y) ∧
      (∀ k, IsCombinationAt (columns A) y (fun i x => φ x ^ j₀ * T i k x)) ∧
      RegularAt (catCols A T) φ y := by
  obtain ⟨j₀, hj₀⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (HolGerm X) (Fin a → HolGerm X))
    ⟨torsionSubmodule A φ y, torsionSubmodule_mono A φ y⟩
  have hj : torsionSubmodule A φ y j₀ = torsionSubmodule A φ y (j₀ + 1) := hj₀ (j₀ + 1) (Nat.le_succ j₀)
  obtain ⟨t, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (torsionSubmodule A φ y j₀))
  choose T hT hTs using fun (i : Fin a) (k : Fin t) => exists_germAt_eq (s k i) y
  have hTv : ∀ k, germVec y (columns T k) = s k := fun k => funext fun i => hTs i k
  have hsN : ∀ k, s k ∈ torsionSubmodule A φ y j₀ := fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩
  have hAT := holAt_catCols hA hT
  refine ⟨t, j₀, T, hT, fun k => ?_, ?_⟩
  · rw [← germVec_mem_imSubmodule_iff hA fun i => (holAt_pow hφ j₀).mul (hT i k),
      germVec_pow_mul hφ (fun i => hT i k), ← mem_torsionSubmodule]
    show germVec y (columns T k) ∈ _
    rw [hTv k]
    exact hsN k
  · intro c hc hφc
    -- `im [A | T] ⊆ N_{j₀}`
    have hJ : imSubmodule (catCols A T) y ≤ torsionSubmodule A φ y j₀ := by
      rw [imSubmodule, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨k', rfl⟩ := finSumFinEquiv.surjective k
      rcases k' with k' | k'
      · show germVec y (columns (catCols A T) (finSumFinEquiv (Sum.inl k'))) ∈ _
        have heq : germVec y (columns (catCols A T) (finSumFinEquiv (Sum.inl k'))) =
            germVec y (columns A k') := by
          funext i; simp [germVec, columns, catCols]
        rw [heq]
        exact imSubmodule_le_torsionSubmodule A φ y j₀ (Submodule.subset_span ⟨k', rfl⟩)
      · show germVec y (columns (catCols A T) (finSumFinEquiv (Sum.inr k'))) ∈ _
        have heq : germVec y (columns (catCols A T) (finSumFinEquiv (Sum.inr k'))) =
            germVec y (columns T k') := by
          funext i; simp [germVec, columns, catCols]
        rw [heq, hTv k']
        exact hsN k'
    have hφcJ : germVec y (fun i x => φ x * c i x) ∈ imSubmodule (catCols A T) y :=
      (germVec_mem_imSubmodule_iff hAT fun i => hφ.mul (hc i)).2 hφc
    have h1 : germVec y c ∈ torsionSubmodule A φ y (j₀ + 1) := by
      rw [mem_torsionSubmodule, pow_succ, mul_smul]
      have := hJ hφcJ
      rwa [mem_torsionSubmodule, germVec_mul hφ hc] at this
    rw [← hj, ← hs] at h1
    have hsJ : Submodule.span (HolGerm X) (Set.range s) ≤ imSubmodule (catCols A T) y := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨finSumFinEquiv (Sum.inr k), ?_⟩
      rw [← hTv k]
      funext i; simp [germVec, columns, catCols]
    exact (germVec_mem_imSubmodule_iff hAT hc).1 (hsJ h1)

end Germ

end
end Hironaka.HironakaG10FlatTorsionFiltration
