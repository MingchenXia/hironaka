import DeJongAlterations.StableModification.ValuationRing.Nagata
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Elementary divisors over a valuation ring

Let `V` be a valuation ring (`[IsDomain V] [ValuationRing V]`). This file proves that `V` is an
elementary divisor ring in the following form: for a finitely generated submodule `L` of a
finite free `V`-module `N` there is a basis `c₁, …, cₙ` of `N` and elements `a₁, …, aₙ ∈ V` with
`L = ⟨a₁c₁, …, aₙcₙ⟩`. Consequently, for a linear map `f : M → N` of finite free `V`-modules the
cokernel is `⊕ V/(aᵢ)`, the kernel is free of finite rank, and the rank of `f ⊗ κ` over any
field `κ` under `V` is the number of `aᵢ` that do not vanish in `κ`. These are the facts used to
read the cohomology of the fibres of a proper flat curve over `Spec V` off a two-term complex
`K⁰ → K¹` of finite free `V`-modules (the transfer of cohomology and base change to valuation
rings in the proof of Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), Lemma 4.4.2 and Proposition 4.4.6, `semi-stable.tex` lines 3106–3133 and 3213–3219,
where Temkin applies EGA III 7.9.4, 7.6.9 and 7.7.5 through noetherian approximation).
Blueprint chapter `sm-valuation-geometry.tex`, node `lem:sm-elementary-divisors`.

## Main results

* `flat_of_isTorsionFree`, `free_of_isTorsionFree`: torsion-free `V`-modules are flat
  (`flat_iff_forall_smul_eq_zero` of `Nagata.lean`), and finitely generated ones are free.
* `exists_dvd_forall`: among finitely many elements of `V` one divides all the others.
* `exists_pivot`: a nonzero finitely generated submodule has a coordinate of minimal valuation.
* `exists_basis_span_eq` (elementary divisors): for a basis of `N` indexed by `Fin n` and a
  finitely generated `L ≤ N` there is a basis `c` of `N` indexed by `Fin n` and `a : Fin n → V`
  with `L = span {a i • c i}`.
* `exists_basis_range_eq`: the same for the image of a linear map between finite free modules.
* `map_equivFun_span_smul`, `quotientEquivPi`: `N ⧸ span {a i • c i} ≃ Π i, V ⧸ (a i)`.
* `free_ker`, `finite_ker`: the kernel of a map from a finite free module to a torsion-free one
  is finite free (coherence for maps of finite free modules).
* `range_baseChange`, `finrank_span_smul_basis`, `finrank_range_baseChange`: for a field `κ`
  under `V`, the rank of `f ⊗ κ` is the number of indices `i` with `aᵢ ≠ 0` in `κ`;
  `finrank_ker_baseChange_add` and `finrank_quotient_range_baseChange_add` are the resulting
  dimensions of the kernel (`h⁰`) and the cokernel (`h¹`) of `f ⊗ κ`.
-/

noncomputable section

open Module Submodule
open scoped TensorProduct

namespace DeJongAlterations.StableModification.ValuationRing

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]

section Free

variable (V) (M : Type*) [AddCommGroup M] [Module V M]

/-- A torsion-free module over a valuation ring is flat (`flat_iff_forall_smul_eq_zero`,
Temkin, Lemma 3.5.1, first part). -/
theorem flat_of_isTorsionFree [Module.IsTorsionFree V M] : Module.Flat V M :=
  flat_iff_forall_smul_eq_zero.mpr fun _ hc x hx ↦
    Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero hc)
      (show _ • x = _ • (0 : M) by rw [hx, smul_zero])

/-- A finitely generated torsion-free module over a valuation ring is free. -/
theorem free_of_isTorsionFree [Module.Finite V M] [Module.IsTorsionFree V M] :
    Module.Free V M :=
  haveI := flat_of_isTorsionFree V M
  Module.free_of_flat_of_isLocalRing

end Free

/-- In a valuation ring, among the members of a finite nonempty family indexed by `s` there is one
dividing all the others. -/
theorem exists_dvd_forall {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (a : ι → V) :
    ∃ i ∈ s, ∀ j ∈ s, a i ∣ a j := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => exact ⟨i, by simp, by simp⟩
  | cons j s hj hs ih =>
    obtain ⟨i, hi, hdiv⟩ := ih
    rcases _root_.ValuationRing.dvd_total (a i) (a j) with h | h
    · refine ⟨i, Finset.mem_cons_of_mem hi, fun k hk ↦ ?_⟩
      rcases Finset.mem_cons.mp hk with rfl | hk
      · exact h
      · exact hdiv k hk
    · refine ⟨j, Finset.mem_cons_self _ _, fun k hk ↦ ?_⟩
      rcases Finset.mem_cons.mp hk with rfl | hk
      · exact dvd_rfl
      · exact h.trans (hdiv k hk)

section Pivot

variable {N : Type*} [AddCommGroup N] [Module V N]

/-- **The pivot.** If `L ≠ 0` is a finitely generated submodule of a module with a finite basis
`b`, some coordinate `a = b.repr l₀ j₀` of some `l₀ ∈ L` is nonzero and divides every coordinate
of every element of `L`. -/
theorem exists_pivot {ι : Type*} [Fintype ι] (b : Basis ι V N) {L : Submodule V N} (hL : L.FG)
    (hL0 : L ≠ ⊥) :
    ∃ l₀ ∈ L, ∃ j₀ : ι, b.repr l₀ j₀ ≠ 0 ∧ ∀ l ∈ L, ∀ j, b.repr l₀ j₀ ∣ b.repr l j := by
  classical
  obtain ⟨S, rfl⟩ := hL
  have hS : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hL0
  have hι : Nonempty ι := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · have : Subsingleton N := b.repr.toEquiv.subsingleton
      exact absurd (Subsingleton.elim _ _) hL0
    · exact hι
  have hSj : (S ×ˢ (Finset.univ : Finset ι)).Nonempty := hS.product Finset.univ_nonempty
  obtain ⟨⟨l₀, j₀⟩, hmem, hdiv⟩ := exists_dvd_forall hSj (fun p ↦ b.repr p.1 p.2)
  have hl₀ : l₀ ∈ S := (Finset.mem_product.mp hmem).1
  have hdivS : ∀ l ∈ span V (S : Set N), ∀ j, b.repr l₀ j₀ ∣ b.repr l j := by
    intro l hl j
    induction hl using Submodule.span_induction with
    | mem x hx => exact hdiv ⟨x, j⟩ (Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩)
    | zero => simp
    | add x y _ _ hx hy => simpa using dvd_add hx hy
    | smul r x _ hx => simpa using dvd_mul_of_dvd_right hx r
  refine ⟨l₀, subset_span hl₀, j₀, fun h0 ↦ hL0 ?_, hdivS⟩
  rw [eq_bot_iff]
  intro l hl
  rw [mem_bot]
  apply b.repr.injective
  ext j
  have := hdivS l hl j
  rw [h0, zero_dvd_iff] at this
  simp [this]

end Pivot

section Main

/-- **Elementary divisors over a valuation ring.** Let `N` have a basis indexed by `Fin n` and let
`L ≤ N` be finitely generated. Then there are a basis `c` of `N` indexed by `Fin n` and
`a : Fin n → V` such that `L` is spanned by the `a i • c i`. -/
theorem exists_basis_span_eq (n : ℕ) {N : Type*} [AddCommGroup N] [Module V N]
    (b : Basis (Fin n) V N) (L : Submodule V N) (hL : L.FG) :
    ∃ (c : Basis (Fin n) V N) (a : Fin n → V), L = span V (Set.range fun i ↦ a i • c i) := by
  classical
  induction n generalizing N with
  | zero =>
    have : Subsingleton N := b.repr.toEquiv.subsingleton
    refine ⟨b, 0, ?_⟩
    rw [Set.range_eq_empty, span_empty]
    exact Subsingleton.elim _ _
  | succ k ih =>
    by_cases hL0 : L = ⊥
    · refine ⟨b, 0, ?_⟩
      simp [hL0]
    obtain ⟨l₀, hl₀, j₀, ha, hdiv⟩ := exists_pivot b hL hL0
    set a := b.repr l₀ j₀ with ha_def
    choose q hq using hdiv l₀ hl₀
    -- `n₀ = l₀ / a`, a vector with `j₀`-th coordinate `1`
    set n₀ : N := b.equivFun.symm q with hn₀
    have hrepr_n₀ : ∀ j, b.repr n₀ j = q j := by
      intro j
      rw [← b.equivFun_apply, hn₀, LinearEquiv.apply_symm_apply]
    have hqj₀ : q j₀ = 1 := by
      have h := hq j₀
      rw [← ha_def] at h
      exact (mul_eq_left₀ ha).mp h.symm
    have hsmul_n₀ : a • n₀ = l₀ := by
      apply b.repr.injective
      ext j
      rw [map_smul, Finsupp.smul_apply, hrepr_n₀, smul_eq_mul, ← hq j]
    -- the complement `N' = span {b j | j ≠ j₀}`
    let v : Fin k → N := b ∘ j₀.succAbove
    have hv : LinearIndependent V v :=
      b.linearIndependent.comp _ (Fin.succAbove_right_injective)
    let N' := span V (Set.range v)
    have hmemN' : ∀ x : N, x ∈ N' ↔ b.repr x j₀ = 0 := by
      intro x
      have hrange : Set.range v = b '' {j₀}ᶜ := by
        rw [Set.range_comp, Fin.range_succAbove]
      change x ∈ span V (Set.range v) ↔ _
      rw [hrange, b.mem_span_image]
      constructor
      · intro h
        by_contra hne
        exact h (Finsupp.mem_support_iff.mpr hne) rfl
      · intro h j hj hjj
        rw [Set.mem_singleton_iff] at hjj
        subst hjj
        exact (Finsupp.mem_support_iff.mp hj) h
    -- the projection `π : N → N'` along `n₀`
    let π₀ : N →ₗ[V] N := LinearMap.id - (b.coord j₀).smulRight n₀
    have hπ₀ : ∀ x, π₀ x = x - b.repr x j₀ • n₀ := fun x ↦ rfl
    have hπ₀mem : ∀ x, π₀ x ∈ N' := by
      intro x
      rw [hmemN', hπ₀, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, hrepr_n₀, hqj₀,
        smul_eq_mul, mul_one, sub_self]
    let π : N →ₗ[V] N' := LinearMap.codRestrict N' π₀ hπ₀mem
    have hπ : ∀ x, (π x : N) = x - b.repr x j₀ • n₀ := fun x ↦ rfl
    -- every coordinate of an element of `L` is divisible by `a`
    have hdecomp : ∀ l ∈ L, ∃ u : V, b.repr l j₀ • n₀ = u • l₀ := by
      intro l hl
      obtain ⟨u, hu⟩ := hdiv l hl j₀
      exact ⟨u, by rw [hu, mul_comm, mul_smul, hsmul_n₀]⟩
    -- apply the induction hypothesis to `L' = π(L) ≤ N'`
    obtain ⟨c', a', hc'⟩ := ih (Basis.span hv) (L.map π) (hL.map π)
    -- the new basis of `N`
    let e : N ≃ₗ[V] (Fin (k + 1) → V) :=
      { toFun := fun x ↦ Fin.cons (b.repr x j₀) (c'.equivFun (π x))
        map_add' := fun x y ↦ by
          ext i
          refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp
        map_smul' := fun r x ↦ by
          ext i
          refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp
        invFun := fun t ↦ t 0 • n₀ + (c'.equivFun.symm (Fin.tail t) : N)
        left_inv := fun x ↦ by
          simp only [Fin.cons_zero, Fin.tail_cons, LinearEquiv.symm_apply_apply, hπ]
          abel
        right_inv := fun t ↦ by
          have hmem : (c'.equivFun.symm (Fin.tail t) : N) ∈ N' := Submodule.coe_mem _
          have h0 : b.repr (c'.equivFun.symm (Fin.tail t) : N) j₀ = 0 := (hmemN' _).mp hmem
          have h1 : b.repr (t 0 • n₀ + (c'.equivFun.symm (Fin.tail t) : N)) j₀ = t 0 := by
            rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, hrepr_n₀, hqj₀, h0,
              smul_eq_mul, mul_one, add_zero]
          have h2 : π (t 0 • n₀ + (c'.equivFun.symm (Fin.tail t) : N)) =
              c'.equivFun.symm (Fin.tail t) := by
            apply Subtype.ext
            rw [hπ, h1]
            abel
          change (Fin.cons (b.repr (t 0 • n₀ + (c'.equivFun.symm (Fin.tail t) : N)) j₀)
            (c'.equivFun (π (t 0 • n₀ + (c'.equivFun.symm (Fin.tail t) : N)))) :
              Fin (k + 1) → V) = t
          rw [h1, h2, LinearEquiv.apply_symm_apply, Fin.cons_self_tail] }
    let c : Basis (Fin (k + 1)) V N := Basis.ofEquivFun e
    have hc0 : c 0 = n₀ := by
      simp only [c, Basis.coe_ofEquivFun]
      change (Pi.single 0 1 : Fin (k + 1) → V) 0 • n₀ +
        (c'.equivFun.symm (Fin.tail (Pi.single 0 1 : Fin (k + 1) → V)) : N) = n₀
      have : Fin.tail (Pi.single (0 : Fin (k + 1)) (1 : V) : Fin (k + 1) → V) = 0 := by
        ext i
        simp [Fin.tail, Fin.succ_ne_zero]
      simp [this]
    have hcsucc : ∀ i : Fin k, c i.succ = (c' i : N) := by
      intro i
      simp only [c, Basis.coe_ofEquivFun]
      change (Pi.single i.succ 1 : Fin (k + 1) → V) 0 • n₀ +
        (c'.equivFun.symm (Fin.tail (Pi.single i.succ 1 : Fin (k + 1) → V)) : N) = c' i
      have h0 : (Pi.single i.succ (1 : V) : Fin (k + 1) → V) 0 = 0 := by
        simp [(Fin.succ_ne_zero i).symm]
      have h1 : Fin.tail (Pi.single i.succ (1 : V) : Fin (k + 1) → V) = Pi.single i 1 := by
        ext j
        simp [Fin.tail, Pi.single_apply, Fin.succ_inj]
      rw [h0, h1, zero_smul, zero_add, c'.equivFun_symm_apply]
      simp [Pi.single_apply]
    refine ⟨c, Fin.cons a a', ?_⟩
    have hfun : (fun i ↦ (Fin.cons a a' : Fin (k + 1) → V) i • c i) =
        Fin.cons l₀ (fun i ↦ ((a' i • c' i : N') : N)) := by
      funext i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · simp [hc0, hsmul_n₀]
      · simp [hcsucc]
    rw [hfun, Fin.range_cons, span_insert]
    have hrange : Set.range (fun i ↦ ((a' i • c' i : N') : N)) =
        N'.subtype '' Set.range (fun i ↦ a' i • c' i) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, span_image, ← hc', ← Submodule.map_comp]
    apply le_antisymm
    · intro l hl
      obtain ⟨u, hu⟩ := hdecomp l hl
      have : l = u • l₀ + (π l : N) := by rw [hπ, ← hu]; abel
      rw [this]
      exact add_mem_sup (mem_span_singleton.mpr ⟨u, rfl⟩) ⟨l, hl, rfl⟩
    · refine sup_le ((span_singleton_le_iff_mem _ _).mpr hl₀) ?_
      rintro _ ⟨l, hl, rfl⟩
      obtain ⟨u, hu⟩ := hdecomp l hl
      change (π l : N) ∈ L
      rw [hπ, hu]
      exact L.sub_mem hl (L.smul_mem u hl₀)

/-- **Elementary divisors of a linear map.** For a linear map `f : M → N` with `M` finitely
generated and `N` finite free over a valuation ring, there are a basis `c` of `N` and
`a : Fin (finrank V N) → V` such that the image of `f` is spanned by the `a i • c i`. -/
theorem exists_basis_range_eq {M N : Type*} [AddCommGroup M] [Module V M] [Module.Finite V M]
    [AddCommGroup N] [Module V N] [Module.Free V N] [Module.Finite V N] (f : M →ₗ[V] N) :
    ∃ (c : Basis (Fin (finrank V N)) V N) (a : Fin (finrank V N) → V),
      LinearMap.range f = span V (Set.range fun i ↦ a i • c i) :=
  exists_basis_span_eq _ (Module.finBasis V N) _
    (Module.Finite.iff_fg.mp (Module.Finite.range f))

end Main

section Consequences

variable {ι : Type*} [Fintype ι] {N : Type*} [AddCommGroup N] [Module V N]

omit [IsDomain V] [ValuationRing V] in
/-- In the coordinates of a basis `c`, the span of the `a i • c i` is the product of the ideals
`(a i)`. -/
theorem map_equivFun_span_smul [DecidableEq ι] (c : Basis ι V N) (a : ι → V) :
    (span V (Set.range fun i ↦ a i • c i)).map (c.equivFun : N →ₗ[V] ι → V) =
      Submodule.pi Set.univ fun i ↦ Ideal.span {a i} := by
  rw [Submodule.map_span, ← Set.range_comp]
  have hfun : ⇑(c.equivFun : N →ₗ[V] ι → V) ∘ (fun i ↦ a i • c i) =
      fun i ↦ Pi.single i (a i) := by
    funext i j
    rw [Function.comp_apply, LinearEquiv.coe_coe, map_smul, Pi.smul_apply, Basis.equivFun_self,
      Pi.single_apply, smul_eq_mul]
    by_cases h : j = i
    · subst h
      simp
    · simp [h, Ne.symm h]
  rw [hfun]
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨i, rfl⟩ j -
    by_cases hij : j = i
    · subst hij
      simp
    · simp [hij]
  · intro x hx
    have hx' : ∀ j, ∃ r : V, r * a j = x j := fun j ↦
      Ideal.mem_span_singleton'.mp (hx j (Set.mem_univ j))
    choose r hr using hx'
    have : x = ∑ j, r j • Pi.single j (a j) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply, hr]
    rw [this]
    exact sum_mem fun j _ ↦ smul_mem _ _ (subset_span ⟨j, rfl⟩)

omit [IsDomain V] [ValuationRing V] in
/-- The quotient of `N` by the span of the `a i • c i` is `Π i, V ⧸ (a i)`; for the elementary
divisors of a map `f`, this is the cokernel of `f`. -/
def quotientEquivPi [DecidableEq ι] (c : Basis ι V N) (a : ι → V) :
    (N ⧸ span V (Set.range fun i ↦ a i • c i)) ≃ₗ[V] ((i : ι) → V ⧸ Ideal.span {a i}) :=
  (Submodule.Quotient.equiv _ _ c.equivFun (map_equivFun_span_smul c a)).trans
    (Submodule.quotientPi _)

variable {M : Type*} [AddCommGroup M] [Module V M]

/-- The kernel of a linear map from a finite free module over a valuation ring to a torsion-free
module is finitely generated (valuation rings are coherent). -/
theorem finite_ker [Module.Free V M] [Module.Finite V M] [Module.IsTorsionFree V N]
    (f : M →ₗ[V] N) : Module.Finite V (LinearMap.ker f) := by
  have : Module.Finite V (LinearMap.range f) := Module.Finite.range f
  have : Module.Free V (LinearMap.range f) := free_of_isTorsionFree V _
  have : Module.FinitePresentation V (LinearMap.range f) :=
    Module.finitePresentation_of_projective _ _
  have h := Module.FinitePresentation.fg_ker f.rangeRestrict f.surjective_rangeRestrict
  rw [LinearMap.ker_rangeRestrict] at h
  exact Module.Finite.iff_fg.mpr h

/-- The kernel of a linear map from a finite free module over a valuation ring to a torsion-free
module is free. -/
theorem free_ker [Module.Free V M] [Module.Finite V M] [Module.IsTorsionFree V N]
    (f : M →ₗ[V] N) : Module.Free V (LinearMap.ker f) :=
  haveI := finite_ker f
  free_of_isTorsionFree V _

omit [IsDomain V] [ValuationRing V] in
/-- The image of a base change is the base change of the image. -/
theorem range_baseChange (A : Type*) [CommRing A] [Algebra V A] (f : M →ₗ[V] N) :
    LinearMap.range (f.baseChange A) = (LinearMap.range f).baseChange A := by
  rw [Submodule.baseChange]
  have hf : f = (LinearMap.range f).subtype ∘ₗ f.rangeRestrict :=
    (LinearMap.subtype_comp_codRestrict _ _ _).symm
  conv_lhs => rw [hf]
  rw [LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.mpr
    (LinearMap.baseChange_surjective A f.surjective_rangeRestrict)

omit [IsDomain V] [ValuationRing V] in
/-- Over a field, the span of the multiples `s i • e i` of a basis has dimension the number of
nonzero `s i`. -/
theorem finrank_span_smul_basis {κ W : Type*} [Field κ] [AddCommGroup W] [Module κ W]
    (e : Basis ι κ W) (s : ι → κ) :
    finrank κ (span κ (Set.range fun i ↦ s i • e i)) = Nat.card {i // s i ≠ 0} := by
  classical
  have hspan : span κ (Set.range fun i ↦ s i • e i) =
      span κ (Set.range fun i : {i // s i ≠ 0} ↦ e i) := by
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      by_cases hi : s i = 0
      · simp [hi]
      · exact smul_mem _ _ (subset_span ⟨⟨i, hi⟩, rfl⟩)
    · rw [span_le]
      rintro _ ⟨⟨i, hi⟩, rfl⟩
      have : e i = (s i)⁻¹ • (s i • e i) := by rw [smul_smul, inv_mul_cancel₀ hi, one_smul]
      change e i ∈ _
      rw [this]
      exact smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [hspan]
  exact (finrank_span_eq_card (e.linearIndependent.comp _ Subtype.val_injective)).trans
    Nat.card_eq_fintype_card.symm

omit [IsDomain V] [ValuationRing V] in
/-- **Ranks of fibres.** If the image of `f : M → N` is spanned by the `a i • c i` for a basis `c`
of `N`, then for every field `κ` under `V` the rank of `f ⊗ κ` is the number of indices `i` with
`a i ≠ 0` in `κ`. -/
theorem finrank_range_baseChange (κ : Type*) [Field κ] [Algebra V κ] (f : M →ₗ[V] N)
    (c : Basis ι V N) (a : ι → V)
    (h : LinearMap.range f = span V (Set.range fun i ↦ a i • c i)) :
    finrank κ (LinearMap.range (f.baseChange κ)) = Nat.card {i // algebraMap V κ (a i) ≠ 0} := by
  rw [range_baseChange, h, Submodule.baseChange_span, ← Set.range_comp]
  have hfun : (TensorProduct.mk V κ N 1) ∘ (fun i ↦ a i • c i) =
      fun i ↦ algebraMap V κ (a i) • c.baseChange κ i := by
    funext i
    simp [algebraMap_smul]
  rw [hfun, finrank_span_smul_basis]

omit [ValuationRing V] in
/-- **`h⁰` of the fibres of a two-term complex.** In the situation of `finrank_range_baseChange`,
with `M` finite free, the kernel of `f ⊗ κ` has dimension `rank M − #{i | aᵢ ≠ 0 in κ}`. -/
theorem finrank_ker_baseChange_add (κ : Type*) [Field κ] [Algebra V κ] [Module.Free V M]
    [Module.Finite V M] (f : M →ₗ[V] N) (c : Basis ι V N) (a : ι → V)
    (h : LinearMap.range f = span V (Set.range fun i ↦ a i • c i)) :
    finrank κ (LinearMap.ker (f.baseChange κ)) + Nat.card {i // algebraMap V κ (a i) ≠ 0} =
      finrank V M := by
  rw [← finrank_range_baseChange κ f c a h, add_comm, LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_baseChange]

omit [ValuationRing V] in
/-- **`h¹` of the fibres of a two-term complex.** In the situation of `finrank_range_baseChange`,
with `N` finite free, the cokernel of `f ⊗ κ` has dimension `rank N − #{i | aᵢ ≠ 0 in κ}`. -/
theorem finrank_quotient_range_baseChange_add (κ : Type*) [Field κ] [Algebra V κ]
    [Module.Free V N] [Module.Finite V N] (f : M →ₗ[V] N) (c : Basis ι V N) (a : ι → V)
    (h : LinearMap.range f = span V (Set.range fun i ↦ a i • c i)) :
    finrank κ ((κ ⊗[V] N) ⧸ LinearMap.range (f.baseChange κ)) +
      Nat.card {i // algebraMap V κ (a i) ≠ 0} = finrank V N := by
  rw [← finrank_range_baseChange κ f c a h, Submodule.finrank_quotient_add_finrank,
    Module.finrank_baseChange]

end Consequences

end DeJongAlterations.StableModification.ValuationRing
