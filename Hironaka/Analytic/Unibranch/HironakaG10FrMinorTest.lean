import Hironaka.Resolution.HironakaG10LocRelative
import Hironaka.Resolution.HironakaHolomorphicJetRankLoci
import Hironaka.Resolution.HironakaG10FlatGermChain

/-!
# The pointwise minor test for fibre exactness (route G, step G1)

Plan item G10FR-2.G1 (`work/hironaka-run0081-20261117/G10FR/frisch-constructibility.md` §4.2).
Let `v`, `G_v`, `G_v'` be holomorphic matrices near `y` such that `(G_v, v)` and `(G_v', G_v)` are exact
complexes of germs at `y` (e.g. the fibres at a flat parameter of two relative exact starts), and let
`u = G_v X` near `y`. Then `(u, v)` is exact at `y` if and only if some maximal minor of the VALUE matrix
`[X(y) | G_v'(y)]` is nonzero (`exactAt_iff_exists_minor_ne_zero`): exactness of `(u, v)` means
`Im G_v ⊆ Im (G_v X)`, i.e. `[X | G_v']` is surjective over the ring of germs, and over a local ring a matrix
is surjective iff its residue matrix has full row rank (a maximal minor is a unit).

This replaces Frisch's jet criterion (Prop. (III,6) + Lemme (IV,5), Invent. Math. 4 (1967) pp. 131–132)
on the generic part of the parameter space in route G; no Artin–Rees and no jets are needed.

* `matExact_mul_iff` (any commutative ring): `MatExact (G_v * X) v ↔ ∀ e, ∃ a b, X a + G_v' b = e`;
* `surjective_iff_exists_det_isUnit` (any local ring, through a residue map to `ℂ` detecting units);
* `exactAt_iff_exists_minor_ne_zero` (germs of holomorphic matrices at a point);
* `fibreExactAt_iff_exists_minor_ne_zero` (the same for the fibre at a parameter `s`).

Lane G10FR, run 0081. Blueprint: `hironaka-g10fr-minor-test.tex`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Matrix

namespace Hironaka.Analytic.Unibranch.HironakaG10FrMinorTest

open Hironaka
open OkaRelationSheaf OkaGermBridge HolGerm HironakaG10FlatResolutionStart
  HironakaG10FlatRelationLift HironakaG10FlatGermChain HironakaG10LocSheafExact
  HironakaG10LocFibreOpen

noncomputable section

/-! ## Algebra over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R] {ι₀ ι₁ κ κ' ι₂ : Type*} [Fintype ι₁] [Fintype κ]
  [Fintype κ'] [Fintype ι₂]

/-- If `(G_v, v)` and `(G_v', G_v)` are exact complexes, then `(G_v X, v)` is exact iff `X` and `G_v'`
together generate. -/
theorem matExact_mul_iff {v : Matrix ι₀ ι₁ R} {Gv : Matrix ι₁ κ R} {Gv' : Matrix κ κ' R}
    (X : Matrix κ ι₂ R) (hvG : v * Gv = 0) (hGG : Gv * Gv' = 0) (h1 : MatExact Gv v)
    (h2 : MatExact Gv' Gv) :
    MatExact (Gv * X) v ↔ ∀ e : κ → R, ∃ (a : ι₂ → R) (b : κ' → R), X *ᵥ a + Gv' *ᵥ b = e := by
  constructor
  · intro h e
    have hv : v *ᵥ (Gv *ᵥ e) = 0 := by rw [Matrix.mulVec_mulVec, hvG, Matrix.zero_mulVec]
    obtain ⟨a, ha⟩ := h _ hv
    have hker : Gv *ᵥ (e - X *ᵥ a) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ha, sub_self]
    obtain ⟨b, hb⟩ := h2 _ hker
    exact ⟨a, b, by rw [hb, add_sub_cancel]⟩
  · intro h w hw
    obtain ⟨c, hc⟩ := h1 w hw
    obtain ⟨a, b, hab⟩ := h c
    refine ⟨a, ?_⟩
    rw [← hc, ← hab, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hGG,
      Matrix.zero_mulVec, add_zero]

/-- The block matrix `[X | G_v']`. -/
def blockCols (X : Matrix κ ι₂ R) (Gv' : Matrix κ κ' R) : Matrix κ (ι₂ ⊕ κ') R :=
  Matrix.of fun i j => Sum.elim (X i) (Gv' i) j

omit [Fintype κ] in
theorem blockCols_mulVec (X : Matrix κ ι₂ R) (Gv' : Matrix κ κ' R) (w : ι₂ ⊕ κ' → R) :
    blockCols X Gv' *ᵥ w = X *ᵥ (w ∘ Sum.inl) + Gv' *ᵥ (w ∘ Sum.inr) := by
  funext i
  simp [blockCols, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

omit [Fintype κ] in
theorem exists_add_iff_surjective (X : Matrix κ ι₂ R) (Gv' : Matrix κ κ' R) :
    (∀ e : κ → R, ∃ (a : ι₂ → R) (b : κ' → R), X *ᵥ a + Gv' *ᵥ b = e) ↔
      ∀ e : κ → R, ∃ w, blockCols X Gv' *ᵥ w = e := by
  refine forall_congr' fun e => ⟨?_, ?_⟩
  · rintro ⟨a, b, h⟩
    exact ⟨Sum.elim a b, by rw [blockCols_mulVec]; simpa using h⟩
  · rintro ⟨w, h⟩
    exact ⟨w ∘ Sum.inl, w ∘ Sum.inr, by rw [← blockCols_mulVec]; exact h⟩

end Ring

/-! ## Surjectivity over a local ring with residue field `ℂ` -/

section Local

variable {R : Type*} [CommRing R] [Nontrivial R] {κ μ : Type*} [Fintype κ] [Fintype μ]

/-- A square minor with unit determinant makes the matrix surjective. -/
theorem surjective_of_det_isUnit (M : Matrix κ μ R) {n : ℕ} (hn : Fintype.card κ = n)
    (rows : Fin n → κ) (cols : Fin n → μ)
    (h : IsUnit (Matrix.of fun i j => M (rows i) (cols j)).det) :
    ∀ e : κ → R, ∃ w, M *ᵥ w = e := by
  classical
  set N : Matrix (Fin n) (Fin n) R :=
    Matrix.of fun i j => M (rows i) (cols j) with hN
  -- `rows` is injective (two equal rows force a zero determinant), hence bijective
  have hinj : Function.Injective rows := by
    intro i i' hii'
    by_contra hne
    have h0 : N.det = 0 := Matrix.det_zero_of_row_eq hne (by
      funext j
      simp [hN, hii'])
    rw [h0] at h
    exact not_isUnit_zero h
  have hbij : Function.Bijective rows :=
    (Fintype.bijective_iff_injective_and_card rows).mpr ⟨hinj, by simp [hn]⟩
  intro e
  have hNunit : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr h
  set c : Fin n → R := N⁻¹ *ᵥ (e ∘ rows) with hc
  have hNc : N *ᵥ c = e ∘ rows := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N h, Matrix.one_mulVec]
  refine ⟨fun j => ∑ k ∈ Finset.univ.filter (fun k => cols k = j), c k, ?_⟩
  have hrow : ∀ i, (M *ᵥ fun j => ∑ k ∈ Finset.univ.filter (fun k => cols k = j), c k) (rows i) =
      e (rows i) := by
    intro i
    have h1 : (N *ᵥ c) i = e (rows i) := congrFun hNc i
    rw [← h1]
    simp only [Matrix.mulVec, dotProduct, hN, Matrix.of_apply, Finset.mul_sum]
    rw [← Finset.sum_fiberwise (Finset.univ) cols (fun k => M (rows i) (cols k) * c k)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k hk => ?_
    rw [(Finset.mem_filter.mp hk).2]
  funext x
  obtain ⟨i, rfl⟩ := hbij.2 x
  exact hrow i

/-- **Surjectivity over a local ring**: if units are detected by a ring map `ε : R → ℂ` with a section
`σ`, a matrix is surjective iff some maximal minor of its values is nonzero. -/
theorem surjective_iff_exists_minor_ne_zero (ε : R →+* ℂ) (σ : ℂ →+* R) (hεσ : ∀ z, ε (σ z) = z)
    (hε : ∀ r, IsUnit r ↔ ε r ≠ 0) (M : Matrix κ μ R) {n : ℕ} (hn : Fintype.card κ = n) :
    (∀ e : κ → R, ∃ w, M *ᵥ w = e) ↔
      ∃ (rows : Fin n → κ) (cols : Fin n → μ),
        (Matrix.of fun i j => ε (M (rows i) (cols j))).det ≠ 0 := by
  classical
  constructor
  · intro h
    set Mv : Matrix κ μ ℂ := M.map ε with hMv
    have hrange : LinearMap.range (Fintype.linearCombination ℂ (fun b a => Mv a b)) = ⊤ := by
      rw [eq_top_iff]
      intro e _
      obtain ⟨w, hw⟩ := h (fun i => σ (e i))
      refine ⟨fun j => ε (w j), ?_⟩
      funext i
      have hi := congrArg ε (congrFun hw i)
      rw [hεσ] at hi
      rw [← hi]
      simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.mulVec, dotProduct, map_sum, map_mul, hMv, Matrix.map_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hnot : ¬ Module.finrank ℂ (LinearMap.range
        (Fintype.linearCombination ℂ (fun b a => Mv a b))) < n := by
      rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, hn]
      exact lt_irrefl _
    rw [HironakaHolomorphicJetRankLoci.finite_column_rank_lt_iff_minors_eq_zero] at hnot
    push Not at hnot
    obtain ⟨rows, cols, hdet⟩ := hnot
    exact ⟨rows, cols, by simpa [hMv] using hdet⟩
  · rintro ⟨rows, cols, hdet⟩
    refine surjective_of_det_isUnit M hn rows cols ((hε _).mpr ?_)
    rw [RingHom.map_det]
    convert hdet using 2
    ext i j
    rfl

end Local

/-! ## Germs of holomorphic matrices at a point -/

section Germ

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem germMat_mul_of_eventuallyEq {ι κ ν : Type*} [Fintype κ] {A : ι → κ → Z → ℂ}
    {B : κ → ν → Z → ℂ} {C : ι → ν → Z → ℂ} {y : Z} (hA : ∀ i k, HolAt (A i k) y)
    (hB : ∀ k l, HolAt (B k l) y) (hC : ∀ i l, HolAt (C i l) y)
    (h : ∀ i l, ∀ᶠ z in 𝓝 y, C i l z = ∑ k, A i k z * B k l z) :
    germMat y C = germMat y A * germMat y B := by
  refine Matrix.ext fun i l => ?_
  simp only [germMat, Matrix.of_apply, Matrix.mul_apply]
  have hs : HolAt (fun z => ∑ k, A i k z * B k l z) y :=
    HolAt.fintype_sum fun k => (hA i k).mul (hB k l)
  rw [(germAt_eq_germAt_iff (hC i l) hs).mpr (h i l), germAt_sum _ fun k _ => (hA i k).mul (hB k l)]
  exact Finset.sum_congr rfl fun k _ => germAt_mul (hA i k) (hB k l)

theorem germMat_mul_eq_zero {ι κ ν : Type*} [Fintype κ] {A : ι → κ → Z → ℂ}
    {B : κ → ν → Z → ℂ} {y : Z} (hA : ∀ i k, HolAt (A i k) y) (hB : ∀ k l, HolAt (B k l) y)
    (h : ∀ i l, ∀ᶠ z in 𝓝 y, ∑ k, A i k z * B k l z = 0) :
    germMat y A * germMat y B = 0 := by
  refine Matrix.ext fun i l => ?_
  simp only [germMat, Matrix.of_apply, Matrix.mul_apply, Matrix.zero_apply]
  have hs : HolAt (fun z => ∑ k, A i k z * B k l z) y :=
    HolAt.fintype_sum fun k => (hA i k).mul (hB k l)
  rw [← Finset.sum_congr rfl fun k _ => germAt_mul (hA i k) (hB k l),
    ← germAt_sum _ fun k _ => (hA i k).mul (hB k l)]
  exact (germAt_eq_zero_iff hs).mpr (h i l)

/-- **The minor test (G1).** Let `(G_v, v)` and `(G_v', G_v)` be exact complexes of germs at `y` and
`u = G_v X` near `y`. Then `(u, v)` is exact at `y` iff some maximal minor of the value matrix
`[X(y) | G_v'(y)]` is nonzero. -/
theorem exactAt_iff_exists_minor_ne_zero {a b c c' p : ℕ}
    (v : Fin a → Fin b → Z → ℂ) (Gv : Fin b → Fin c → Z → ℂ) (Gv' : Fin c → Fin c' → Z → ℂ)
    (X : Fin c → Fin p → Z → ℂ) (u : Fin b → Fin p → Z → ℂ) (y : Z)
    (hv : ∀ i j, HolAt (v i j) y) (hGv : ∀ j k, HolAt (Gv j k) y)
    (hGv' : ∀ k l, HolAt (Gv' k l) y) (hX : ∀ k l, HolAt (X k l) y) (hu : ∀ j l, HolAt (u j l) y)
    (hvG : ∀ i k, ∀ᶠ z in 𝓝 y, ∑ j, v i j z * Gv j k z = 0)
    (hGG : ∀ j l, ∀ᶠ z in 𝓝 y, ∑ k, Gv j k z * Gv' k l z = 0)
    (h1 : ∀ e, IsRelationAt v y e → IsCombinationAt (columns Gv) y e)
    (h2 : ∀ e, IsRelationAt Gv y e → IsCombinationAt (columns Gv') y e)
    (huX : ∀ j l, ∀ᶠ z in 𝓝 y, u j l z = ∑ k, Gv j k z * X k l z) :
    (∀ e, IsRelationAt v y e → IsCombinationAt (columns u) y e) ↔
      ∃ (rows : Fin c → Fin c) (cols : Fin c → Fin p ⊕ Fin c'),
        (Matrix.of fun i j =>
          Sum.elim (fun l => X (rows i) l y) (fun l => Gv' (rows i) l y) (cols j)).det ≠ 0 := by
  rw [exact_iff_matExact hv hu, germMat_mul_of_eventuallyEq hGv hX hu huX,
    matExact_mul_iff (germMat y X) (germMat_mul_eq_zero hv hGv hvG)
      (germMat_mul_eq_zero hGv hGv' hGG) ((exact_iff_matExact hv hGv).mp h1)
      ((exact_iff_matExact hGv hGv').mp h2),
    exists_add_iff_surjective,
    surjective_iff_exists_minor_ne_zero HolGerm.eval HolGerm.constHom HolGerm.eval_constHom
      HolGerm.isUnit_iff_eval_ne_zero _ (Fintype.card_fin c)]
  have hval : ∀ (k : Fin c) (j : Fin p ⊕ Fin c'),
      HolGerm.eval (blockCols (germMat y X) (germMat y Gv') k j) =
        Sum.elim (fun l => X k l y) (fun l => Gv' k l y) j := by
    intro k j
    cases j with
    | inl l => exact eval_germAt (hX k l)
    | inr l => exact eval_germAt (hGv' k l)
  simp only [hval]

/-- **The minor test on a fibre**: the same for the fibre start at a parameter `s`. -/
theorem fibreExactAt_iff_exists_minor_ne_zero {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
    {a b c c' p : ℕ}
    (v : Fin a → Fin b → S × Z → ℂ) (Gv : Fin b → Fin c → S × Z → ℂ)
    (Gv' : Fin c → Fin c' → S × Z → ℂ) (X : Fin c → Fin p → S × Z → ℂ)
    (u : Fin b → Fin p → S × Z → ℂ) (s : S) (y : Z)
    (hv : ∀ i j, HolAt (fib v s i j) y) (hGv : ∀ j k, HolAt (fib Gv s j k) y)
    (hGv' : ∀ k l, HolAt (fib Gv' s k l) y) (hX : ∀ k l, HolAt (fib X s k l) y)
    (hu : ∀ j l, HolAt (fib u s j l) y)
    (hvG : ∀ i k, ∀ᶠ z in 𝓝 y, ∑ j, v i j (s, z) * Gv j k (s, z) = 0)
    (hGG : ∀ j l, ∀ᶠ z in 𝓝 y, ∑ k, Gv j k (s, z) * Gv' k l (s, z) = 0)
    (h1 : FibreExactAt Gv v s y) (h2 : FibreExactAt Gv' Gv s y)
    (huX : ∀ j l, ∀ᶠ z in 𝓝 y, u j l (s, z) = ∑ k, Gv j k (s, z) * X k l (s, z)) :
    FibreExactAt u v s y ↔
      ∃ (rows : Fin c → Fin c) (cols : Fin c → Fin p ⊕ Fin c'),
        (Matrix.of fun i j =>
          Sum.elim (fun l => X (rows i) l (s, y)) (fun l => Gv' (rows i) l (s, y)) (cols j)).det ≠ 0 :=
  exactAt_iff_exists_minor_ne_zero (fib v s) (fib Gv s) (fib Gv' s) (fib X s) (fib u s) y
    hv hGv hGv' hX hu hvG hGG h1 h2 huX

end Germ

end
end Hironaka.Analytic.Unibranch.HironakaG10FrMinorTest
