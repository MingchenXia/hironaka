/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hironaka.Geometry.StableModification.Valuation.Analytic.Uniformization

/-!
# Stability of one-dimensional analytic fields of types 2 and 3

Let `k` be an algebraically closed complete non-archimedean field of equal characteristic. This
file proves M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
Theorem 6.3.1(iii) (`semi-stable.tex`, statement line 3995, proof lines 4065–4067) for
algebraically closed `k`:

* `IsOneDimensional.isCartesian`: a one-dimensional analytic `k`-field `L` which is not
  `k`-immediate (Temkin's types 2 and 3) is **stable**: every finite extension `F/L` is
  Cartesian (`e_{F/L} f_{F/L} = [F : L]`).

The proof follows blueprint `thm:sm-an-type2-stable`, along plan simplification S5: every finite
extension `M` of `L` has minimal elements in its special cosets
(`IsOneDimensional.exists_isMinimalInCoset`, from Theorem 6.3.1(i)), so no Artin–Schreier or
`p`-th root step over `M` is immediate; by the degree bounds `e, f ∈ {1, p}` for such steps
(`ramificationIndex_eq_one_or_eq_of_pow_mem`, `inertiaDegree_eq_one_or_eq_of_isPurelyInseparable`)
every step is Cartesian (`isCartesian_of_not_isImmediate`). The towers are those of the Galois
closure over the tame part (`N^V` in type 3, the inertia field in type 2) and of the purely
inseparable part (`isCartesian_of_isPGroup`, `isCartesian_of_isPurelyInseparable`).

## References

Blueprint chapter `sm-val-onedim.tex`: `lem:sm-an-step-degrees`, `thm:sm-an-type2-stable`.
-/

noncomputable section

open IsLocalRing Polynomial Module Topology
open scoped IntermediateField

namespace Hironaka.StableModification.Valuation.Analytic

/-! ### Invariance under isometric isomorphisms -/

section Invariance

/-- Isometric isomorphisms preserve the value group. -/
theorem valueGroup_eq_of_isometry {A B : Type*} [NormedField A] [IsUltrametricDist A]
    [NormedField B] [IsUltrametricDist B] (φ : A ≃+* B) (hφ : ∀ a, ‖φ a‖ = ‖a‖) :
    valueGroup A = valueGroup B := by
  ext γ
  rw [mem_valueGroup_iff, mem_valueGroup_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨φ x, by rw [← hx]; exact NNReal.eq (hφ x)⟩
  · rintro ⟨y, hy⟩
    refine ⟨φ.symm y, ?_⟩
    rw [← hy]
    refine NNReal.eq ?_
    change ‖φ.symm y‖ = ‖y‖
    rw [← hφ, φ.apply_symm_apply]

/-- The ramification index is invariant under isometric `K`-isomorphisms. -/
theorem ramificationIndex_eq_of_algEquiv {K A B : Type*} [NormedField K] [IsUltrametricDist K]
    [NormedField A] [IsUltrametricDist A] [NormedField B] [IsUltrametricDist B] [Algebra K A]
    [Algebra K B] (φ : A ≃ₐ[K] B) (hφ : ∀ a, ‖φ a‖ = ‖a‖) :
    ramificationIndex K A = ramificationIndex K B := by
  unfold ramificationIndex
  rw [valueGroup_eq_of_isometry φ.toRingEquiv hφ]

/-- Being Cartesian is invariant under isometric `K`-isomorphisms. -/
theorem IsCartesian.of_algEquiv {K A B : Type*} [NormedField K] [IsUltrametricDist K]
    [NormedField A] [IsUltrametricDist A] [NormedField B] [IsUltrametricDist B]
    [NormedAlgebra K A] [NormedAlgebra K B] (φ : A ≃ₐ[K] B) (hφ : ∀ a, ‖φ a‖ = ‖a‖)
    (h : IsCartesian K A) : IsCartesian K B := by
  unfold IsCartesian at h ⊢
  rw [← ramificationIndex_eq_of_algEquiv φ hφ, ← inertiaDegree_eq_of_algEquiv φ hφ, h]
  exact φ.toLinearEquiv.finrank_eq

end Invariance

section Equivs

/-- For intermediate fields `E ≤ F` of `N/K`, the field `extendScalars h` is `K`-isomorphic to
`F` (by the identity of `N`). -/
def extendScalarsEquiv {K N : Type*} [Field K] [Field N] [Algebra K N]
    {E F : IntermediateField K N} (h : E ≤ F) : IntermediateField.extendScalars h ≃ₐ[K] F where
  toFun x := ⟨x, (IntermediateField.mem_extendScalars h).mp x.2⟩
  invFun x := ⟨x, (IntermediateField.mem_extendScalars h).mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- An intermediate field `F` of `N/E` is `K`-isomorphic to its restriction of scalars to `K`. -/
def restrictScalarsEquiv {K E N : Type*} [Field K] [Field E] [Field N] [Algebra K E]
    [Algebra E N] [Algebra K N] [IsScalarTower K E N] (F : IntermediateField E N) :
    F ≃ₐ[K] IntermediateField.restrictScalars K F where
  toFun x := ⟨x, (IntermediateField.mem_restrictScalars K).mpr x.2⟩
  invFun x := ⟨x, (IntermediateField.mem_restrictScalars K).mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end Equivs

/-! ### Degree-`p` steps -/

section Steps

variable {M M' : Type*} [NormedField M] [IsUltrametricDist M] [NormedField M']
  [IsUltrametricDist M'] [NormedAlgebra M M'] [FiniteDimensional M M']

/-- A trivial extension is Cartesian. -/
theorem isCartesian_of_forall_mem_range (h : ∀ y : M', y ∈ Set.range (algebraMap M M')) :
    IsCartesian M M' := by
  have hU := isUnramified_of_forall_mem_range h
  have hle := ramificationIndex_mul_inertiaDegree_le (K := M) (L := M')
  have hn : 0 < finrank M M' := Module.finrank_pos
  unfold IsCartesian
  rw [hU.inertiaDegree_eq] at hle ⊢
  have he : ramificationIndex M M' ≤ 1 :=
    Nat.le_of_mul_le_mul_right (hle.trans (one_mul _).symm.le) hn
  have he1 : ramificationIndex M M' = 1 := le_antisymm he ramificationIndex_pos
  rw [he1, one_mul]

/-- If `[M' : M] = p` is prime and `‖x‖ ^ p ∈ |M|` for every `x ∈ M'^×`, then
`e_{M'/M} ∈ {1, p}` (blueprint `lem:sm-an-step-degrees`(1)). -/
theorem ramificationIndex_eq_one_or_eq_of_pow_mem {p : ℕ} (hp : p.Prime)
    (hdeg : finrank M M' = p) (h : ∀ x : M', x ≠ 0 → ∃ c : M, ‖x‖ ^ p = ‖c‖) :
    ramificationIndex M M' = 1 ∨ ramificationIndex M M' = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases he : ramificationIndex M M' = 1
  · exact Or.inl he
  right
  have hle : ramificationIndex M M' ≤ p := hdeg ▸ ramificationIndex_le_finrank
  rw [ramificationIndex_eq_card] at he hle ⊢
  have := Fintype.ofFinite (ValueGroupQuotient M M')
  obtain ⟨q, hq⟩ : ∃ q : ValueGroupQuotient M M', q ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact he (Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b ↦ (hcon a).trans (hcon b).symm⟩, ⟨1⟩⟩)
  obtain ⟨u, rfl⟩ := valueClass_surjective (K := M) (L := M') q
  have hpow : valueClass M M' u ^ p = 1 := by
    obtain ⟨c, hc⟩ := h u u.ne_zero
    rw [← map_pow]
    have h1 : valueClass M M' 1 = valueClass M M' (u ^ p) :=
      valueClass_eq_valueClass_iff.mpr ⟨c, by
        rw [Units.val_pow_eq_pow_val, norm_pow, hc, Units.val_one, norm_one, mul_one]⟩
    rw [← h1, map_one]
  have hord : orderOf (valueClass M M' u) = p := orderOf_eq_prime hpow hq
  have hcard := orderOf_le_card_univ (x := valueClass M M' u)
  rw [hord, ← Nat.card_eq_fintype_card] at hcard
  omega

/-- If `[M' : M] = p` is prime and `M̃'/M̃` is purely inseparable, then `f_{M'/M} ∈ {1, p}`
(blueprint `lem:sm-an-step-degrees`(2)). -/
theorem inertiaDegree_eq_one_or_eq_of_isPurelyInseparable {p : ℕ} [Fact p.Prime]
    (hdeg : finrank M M' = p) [CharP (ResidueField (unitBall M)) p]
    [IsPurelyInseparable (ResidueField (unitBall M)) (ResidueField (unitBall M'))] :
    inertiaDegree M M' = 1 ∨ inertiaDegree M M' = p := by
  by_cases hf : inertiaDegree M M' = 1
  · exact Or.inl hf
  right
  have hle : inertiaDegree M M' ≤ p := hdeg ▸ inertiaDegree_le_finrank
  obtain ⟨w, hw⟩ : ∃ w : ResidueField (unitBall M'),
      w ∉ Set.range (algebraMap (ResidueField (unitBall M)) (ResidueField (unitBall M'))) := by
    by_contra hcon
    push Not at hcon
    apply hf
    rw [inertiaDegree_def]
    refine IntermediateField.bot_eq_top_iff_finrank_eq_one.mp (eq_top_iff.mpr fun y _ ↦ ?_)
    obtain ⟨c, rfl⟩ := hcon y
    exact IntermediateField.algebraMap_mem _ c
  have : ExpChar (ResidueField (unitBall M)) p := ExpChar.prime Fact.out
  have : CharP (ResidueField (unitBall M')) p :=
    charP_of_injective_algebraMap
      (algebraMap (ResidueField (unitBall M)) (ResidueField (unitBall M'))).injective p
  obtain ⟨γ, hγ, c, hc⟩ := exists_pow_char_mem_of_isPurelyInseparable p hw
  have h1 := finrank_adjoin_of_pow_char_mem p (fun h ↦ hγ (RingHom.mem_range.mp h)) hc
  have h2 := Module.finrank_mul_finrank (ResidueField (unitBall M))
    (ResidueField (unitBall M))⟮γ⟯ (ResidueField (unitBall M'))
  have h3 : 0 < finrank (ResidueField (unitBall M))⟮γ⟯ (ResidueField (unitBall M')) :=
    Module.finrank_pos
  rw [h1] at h2
  rw [inertiaDegree_def] at hle ⊢
  have h4 : p ≤ finrank (ResidueField (unitBall M)) (ResidueField (unitBall M')) := by
    rw [← h2]
    exact Nat.le_mul_of_pos_right p h3
  omega

/-- A degree-`p` step with `e, f ∈ {1, p}` which is not immediate is Cartesian. -/
theorem isCartesian_of_not_isImmediate {p : ℕ} (hp : p.Prime) (hdeg : finrank M M' = p)
    (he : ramificationIndex M M' = 1 ∨ ramificationIndex M M' = p)
    (hf : inertiaDegree M M' = 1 ∨ inertiaDegree M M' = p) (hnot : ¬ IsImmediate M M') :
    IsCartesian M M' := by
  have hle := ramificationIndex_mul_inertiaDegree_le (K := M) (L := M')
  unfold IsCartesian
  rw [hdeg] at hle ⊢
  rcases he with he | he <;> rcases hf with hf | hf
  · exact absurd ⟨he, hf⟩ hnot
  · rw [he, hf, one_mul]
  · rw [he, hf, mul_one]
  · rw [he, hf] at hle
    nlinarith [hp.two_le]

omit [FiniteDimensional M M'] in
/-- If every element of `M'°` is congruent modulo `M'°°` to an element of `M°`, then
`f_{M'/M} = 1`. -/
theorem inertiaDegree_eq_one_of_forall
    (h : ∀ x : M', ‖x‖ ≤ 1 → ∃ c : M, ‖c‖ ≤ 1 ∧ ‖x - algebraMap M M' c‖ < 1) :
    inertiaDegree M M' = 1 := by
  rw [inertiaDegree_def]
  refine IntermediateField.bot_eq_top_iff_finrank_eq_one.mp (eq_top_iff.mpr fun w _ ↦ ?_)
  obtain ⟨y, rfl⟩ := residue_surjective w
  obtain ⟨c, hc1, hc⟩ := h y (norm_coe_unitBall_le_one y)
  have hres : residue (unitBall M') y = algebraMap (ResidueField (unitBall M))
      (ResidueField (unitBall M')) (residue (unitBall M) ⟨c, mem_unitBall.mpr hc1⟩) := by
    rw [algebraMap_residue, residue_eq_residue_iff]
    exact hc
  rw [hres]
  exact IntermediateField.algebraMap_mem _ _

end Steps

section GaloisNorm

variable {M M' : Type*} [NontriviallyNormedField M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedField M'] [NormedAlgebra M M'] [FiniteDimensional M M'] [IsGalois M M']

/-- For a finite Galois extension `M'/M` of a complete field, `‖x‖ ^ [M' : M]` is the absolute
value of the norm of `x`, an element of `M`. -/
theorem exists_norm_pow_finrank_eq (x : M') : ∃ c : M, ‖x‖ ^ finrank M M' = ‖c‖ := by
  classical
  refine ⟨Algebra.norm M x, ?_⟩
  rw [← norm_algebraMap' M' (Algebra.norm M x), Algebra.norm_eq_prod_automorphisms, norm_prod,
    ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.prod_const]
  exact Finset.prod_congr rfl fun σ _ ↦ (norm_algEquiv_apply σ x).symm

end GaloisNorm

section Frobenius

/-- If `γ ^ p ∈ E` in characteristic `p`, then `x ^ p ∈ E` for every `x ∈ E(γ)`. -/
theorem pow_char_mem_of_mem_adjoin {E L : Type*} [Field E] [Field L] [Algebra E L] (p : ℕ)
    [Fact p.Prime] [CharP L p] {γ : L} (hγ : γ ^ p ∈ Set.range (algebraMap E L)) {x : L}
    (hx : x ∈ E⟮γ⟯) : x ^ p ∈ Set.range (algebraMap E L) := by
  let S : IntermediateField E L := Subfield.toIntermediateField
    ((algebraMap E L).fieldRange.comap (frobenius L p)) fun c ↦ by
      rw [Subfield.mem_comap, frobenius_def, RingHom.mem_fieldRange]
      exact ⟨c ^ p, by rw [map_pow]⟩
  have hγS : γ ∈ S := by
    change γ ∈ (algebraMap E L).fieldRange.comap (frobenius L p)
    rw [Subfield.mem_comap, frobenius_def, RingHom.mem_fieldRange]
    exact hγ
  have hxS : x ∈ S := IntermediateField.adjoin_simple_le_iff.mpr hγS hx
  change x ∈ (algebraMap E L).fieldRange.comap (frobenius L p) at hxS
  rw [Subfield.mem_comap, frobenius_def, RingHom.mem_fieldRange] at hxS
  exact hxS

end Frobenius

/-! ### Towers -/

section Towers

variable {W N : Type*} [NontriviallyNormedField W] [IsUltrametricDist W] [NormedField N]
  [IsUltrametricDist N] [NormedAlgebra W N] [FiniteDimensional W N]

set_option linter.style.haveILetI false in
/-- **Cartesian `p`-towers**: if `Gal(N/W)` is a `p`-group and every Galois step of degree `p`
between intermediate fields is Cartesian, then `N/W` is Cartesian. -/
theorem isCartesian_of_isPGroup [IsGalois W N] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p (N ≃ₐ[W] N))
    (hstep : ∀ (E F : IntermediateField W N) (h : E ≤ F),
      IsGalois E (IntermediateField.extendScalars h) →
        finrank E (IntermediateField.extendScalars h) = p →
          IsCartesian E (IntermediateField.extendScalars h)) :
    IsCartesian W N := by
  have key : ∀ M : IntermediateField W N, IsCartesian W M := by
    refine IsPGroup.induction_intermediateField hG (P := fun M ↦ IsCartesian W M) ?_ ?_
    · refine isCartesian_of_forall_mem_range fun y ↦ ?_
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp y.2
      exact ⟨c, Subtype.ext hc⟩
    · intro E F hEF hgal hdeg hPE
      set F' := IntermediateField.extendScalars hEF
      letI := normedAlgebraOfTower W F'
      haveI : IsScalarTower W E F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      have h1 : IsCartesian W F' :=
        (isCartesian_iff_of_tower W E F').mpr ⟨hPE, hstep E F hEF hgal hdeg⟩
      exact h1.of_algEquiv (extendScalarsEquiv hEF) fun _ ↦ rfl
  exact (key ⊤).of_algEquiv IntermediateField.topEquiv fun _ ↦ rfl

set_option linter.style.haveILetI false in
/-- **Cartesian purely inseparable towers**: if `N/W` is purely inseparable in characteristic
`p` and every step `E ⊆ E(γ)` with `γ ∉ E`, `γ ^ p ∈ E` is Cartesian, then `N/W` is
Cartesian. -/
theorem isCartesian_of_isPurelyInseparable (p : ℕ) [Fact p.Prime] [CharP W p]
    [IsPurelyInseparable W N]
    (hstep : ∀ (E : IntermediateField W N) (γ : N), γ ∉ E → γ ^ p ∈ E →
      IsCartesian E (IntermediateField.adjoin E {γ})) :
    IsCartesian W N := by
  have key : ∀ M : IntermediateField W N, IsCartesian W M := by
    refine induction_intermediateField_of_isPurelyInseparable p
      (P := fun M ↦ IsCartesian W M) ?_ ?_
    · refine isCartesian_of_forall_mem_range fun y ↦ ?_
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp y.2
      exact ⟨c, Subtype.ext hc⟩
    · intro E γ hγ hγp hPE
      set F' := IntermediateField.adjoin E {γ}
      letI := normedAlgebraOfTower W F'
      haveI : IsScalarTower W E F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      have h1 : IsCartesian W F' :=
        (isCartesian_iff_of_tower W E F').mpr ⟨hPE, hstep E γ hγ hγp⟩
      exact h1.of_algEquiv (restrictScalarsEquiv F') fun _ ↦ rfl
  exact (key ⊤).of_algEquiv IntermediateField.topEquiv fun _ ↦ rfl

end Towers

/-! ### Finite extensions of one-dimensional fields -/

section FiniteExt

variable {k L E : Type*} [NontriviallyNormedField k] [NormedField L] [IsUltrametricDist L]
  [NormedAlgebra k L] [NormedField E] [IsUltrametricDist E] [NormedAlgebra k E]
  [NormedAlgebra L E] [IsScalarTower k L E]

omit [IsUltrametricDist L] [IsUltrametricDist E] in
/-- A field containing a field which is not `k`-immediate is not `k`-immediate. -/
theorem not_isImmediateOver_of_isScalarTower (hnot : ¬ IsImmediateOver k L) :
    ¬ IsImmediateOver k E := by
  intro hE
  apply hnot
  intro x hx
  obtain ⟨c, hc⟩ := hE (algebraMap L E x) ((_root_.map_ne_zero _).mpr hx)
  refine ⟨c, ?_⟩
  rwa [IsScalarTower.algebraMap_apply k L E, ← map_sub, norm_algebraMap', norm_algebraMap'] at hc

omit [IsUltrametricDist L] [IsUltrametricDist E] in
set_option linter.style.haveILetI false in
/-- A finite extension of a one-dimensional field is one-dimensional. -/
theorem IsOneDimensional.of_finiteDimensional [FiniteDimensional L E]
    (hL : IsOneDimensional k L) : IsOneDimensional k E := by
  obtain ⟨y, hy, hfin⟩ := hL
  set y' := algebraMap L E y with hy'_def
  have hy' : y' ∉ Set.range (algebraMap k E) := by
    rintro ⟨c, hc⟩
    apply hy
    refine ⟨c, (algebraMap L E).injective ?_⟩
    rw [← IsScalarTower.algebraMap_apply, hc]
  refine ⟨y', hy', ?_⟩
  set K₀ := closureAdjoin k y with hK₀
  have hiso : Isometry (algebraMap L E) :=
    AddMonoidHomClass.isometry_of_norm _ fun x ↦ norm_algebraMap' E x
  have himage : algebraMap L E '' (k⟮y⟯ : Set L) = (k⟮y'⟯ : Set E) := by
    have := IntermediateField.adjoin_map k {y} (IsScalarTower.toAlgHom k L E)
    rw [Set.image_singleton] at this
    exact congrArg (fun T : IntermediateField k E ↦ (T : Set E)) this
  have hmem : ∀ w : K₀, algebraMap K₀ E w ∈ closureAdjoin k y' :=
    fun w ↦ by
      rw [mem_closureAdjoin_iff, ← himage]
      exact image_closure_subset_closure_image hiso.continuous ⟨w, w.2, rfl⟩
  haveI : Module.Finite K₀ E := Module.Finite.trans L E
  letI : Algebra K₀ (closureAdjoin k y') :=
    ((algebraMap K₀ E).codRestrict (closureAdjoin k y') hmem).toAlgebra
  haveI : IsScalarTower K₀ (closureAdjoin k y') E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact Module.Finite.of_restrictScalars_finite K₀ (closureAdjoin k y') E

end FiniteExt

/-- An exponential characteristic which is prime is the characteristic. -/
theorem charP_of_expChar_of_prime {R : Type*} [AddMonoidWithOne R] {p : ℕ} [h : ExpChar R p]
    (hp : p.Prime) : CharP R p := by
  cases h with
  | zero => exact absurd hp Nat.not_prime_one
  | prime _ => assumption

/-! ### Theorem 6.3.1(iii) -/

section Stable

variable {k L : Type*} [NontriviallyNormedField k] [IsUltrametricDist k] [CompleteSpace k]
  [IsAlgClosed k]

/-- **Minimal elements in one-dimensional fields of types 2 and 3** (char `p`): in a
one-dimensional analytic `k`-field `M` which is not `k`-immediate, every special coset contains
an element of minimal absolute value. By Theorem 6.3.1(i) `M` is an annulus field, or finite and
unramified over a Gauss field, and Temkin's Proposition 6.2.4 applies. -/
theorem IsOneDimensional.exists_isMinimalInCoset (p : ℕ) [Fact p.Prime] [CharP k p]
    [ExpChar (ResidueField (unitBall k)) p] {M : Type*} [NormedField M] [IsUltrametricDist M]
    [CompleteSpace M] [NormedAlgebra k M] (hM : IsOneDimensional k M)
    (hnot : ¬ IsImmediateOver k M) {a b : M} {s : ℝ} (hsp : IsSpecialCoset p a s b) :
    ∃ x, IsMinimalInCoset p a s b x := by
  obtain ⟨x, -, hU, h4 | h3 | h2⟩ := hM.exists_isUnramified p
  · exact absurd (fun w hw ↦ h4.exists_norm_sub_lt hw) hnot
  · obtain ⟨v, -, hv⟩ := h3.exists_isMinimalInCoset hsp
    exact ⟨v, hv⟩
  · have := hU.finiteDimensional
    have := hU.isSeparable
    obtain ⟨U, -, -, hmin⟩ := IsGaussGenerator.exists_isMinimalInCoset
      (K := closureAdjoin k x) (L := M) p h2 hU.inertiaDegree_eq.ge
    obtain ⟨v, -, hv, -⟩ := hmin hsp
    exact ⟨v, hv⟩

variable [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra k L]

set_option linter.style.haveILetI false in
/-- **Temkin, Theorem 6.3.1(iii)** (line 3995, proof lines 4065–4067; blueprint
`thm:sm-an-type2-stable`):
let `k` be algebraically closed of equal characteristic and `L` a one-dimensional analytic
`k`-field which is not `k`-immediate (Temkin's types 2 and 3). Then `L` is **stable**: every
finite extension `F/L` is Cartesian. -/
theorem IsOneDimensional.isCartesian (p : ℕ) [hk : ExpChar k p]
    [ExpChar (ResidueField (unitBall k)) p] (hL : IsOneDimensional k L)
    (hnot : ¬ IsImmediateOver k L) {F : Type*} [NormedField F] [IsUltrametricDist F]
    [NormedAlgebra L F] [FiniteDimensional L F] : IsCartesian L F := by
  -- `L` has the residue field or the value group of `k`
  have hcase : IsResidueTrivial k L ∨ IsValueTrivial k L := by
    obtain ⟨y, hy, hfin⟩ := id hL
    set y₀ : closureAdjoin k y := ⟨y, mem_closureAdjoin_self y⟩
    have hy₀ : y₀ ∉ Set.range (algebraMap k (closureAdjoin k y)) := by
      rintro ⟨c, hc⟩
      exact hy ⟨c, congrArg Subtype.val hc⟩
    rcases isTypeFourGenerator_or_isAnnulusGenerator_or_isGaussGenerator hy₀
      (dense_adjoin_closureAdjoin y) with h4 | ⟨a, h3⟩ | ⟨a, t, ht, h2⟩
    · exact absurd (IsImmediateOver.of_finiteDimensional (K := closureAdjoin k y) (L := L)
        fun w hw ↦ h4.exists_norm_sub_lt hw) hnot
    · exact Or.inl (IsResidueTrivial.of_finiteDimensional (K := closureAdjoin k y)
        fun w hw ↦ h3.exists_norm_sub_lt_one hw)
    · exact Or.inr (IsValueTrivial.of_finiteDimensional (K := closureAdjoin k y)
        fun w ↦ h2.exists_norm_eq w)
  have : ExpChar (ResidueField (unitBall L)) p := expChar_residueField_of_normedAlgebra (k := k) p
  haveI : CompleteSpace F := FiniteDimensional.complete L F
  letI := normedAlgebraComp k L F
  haveI := isScalarTower_normedAlgebraComp k L F
  set Fs := separableClosure L F with hFs
  haveI : CompleteSpace Fs := FiniteDimensional.complete L Fs
  -- the separable part
  have hFsc : IsCartesian L Fs := by
    refine galoisClosure_induction (K := L) (M := Fs) fun N _ _ _ _ _ _ _ ↦ ?_
    letI := normedAlgebraComp k L N
    haveI := isScalarTower_normedAlgebraComp k L N
    -- `N/L` is Cartesian
    have hNL : IsCartesian L N := by
      rcases hcase with hres | hval
      · -- type 3: the residue field of `k`; `W = N^V` is Cartesian over `L`
        have hresN : IsResidueTrivial k N := hres.of_finiteDimensional
        have hT : inertiaSubgroup L N = ⊤ := by
          refine inertiaSubgroup_eq_top_of_forall fun x hx ↦ ?_
          obtain ⟨c, hc1, hc⟩ := hresN x hx
          refine ⟨algebraMap k L c, by rwa [norm_algebraMap'], ?_⟩
          rwa [← IsScalarTower.algebraMap_apply]
        have hVp : IsPGroup p (wildInertiaSubgroup L N) := isPGroup_wildInertiaSubgroup p
        have hGW : IsPGroup p (N ≃ₐ[IntermediateField.fixedField (wildInertiaSubgroup L N)] N) :=
          (hVp.of_equiv (MulEquiv.subgroupCongr
            (IntermediateField.fixingSubgroup_fixedField (wildInertiaSubgroup L N)).symm)).of_equiv
            (IntermediateField.fixingSubgroupEquiv _)
        have hWcart := isCartesian_fixedField_wildInertiaSubgroup hT
        obtain ⟨W, hW⟩ : ∃ W, W = IntermediateField.fixedField (wildInertiaSubgroup L N) :=
          ⟨_, rfl⟩
        rw [← hW] at hGW hWcart
        have hNW : IsCartesian W N := by
          rcases expChar_is_prime_or_one k p with hprime | hp1
          · have : Fact p.Prime := ⟨hprime⟩
            have : CharP k p := charP_of_expChar_of_prime hprime
            haveI : IsScalarTower k W N := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
            refine isCartesian_of_isPGroup hGW fun E F' hEF hgal hdeg ↦ ?_
            letI := normedAlgebraOfTower k E
            letI := normedAlgebraOfTower L E
            haveI : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
            haveI : IsScalarTower L W E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
            haveI : FiniteDimensional L E := Module.Finite.trans W E
            haveI : CompleteSpace E := FiniteDimensional.complete L E
            have hE1 : IsOneDimensional k E := hL.of_finiteDimensional
            have hEnot : ¬ IsImmediateOver k E := not_isImmediateOver_of_isScalarTower hnot
            have : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
            set F'' := IntermediateField.extendScalars hEF
            have : CharP F'' p := charP_of_injective_algebraMap (algebraMap E F'').injective p
            obtain ⟨α, hα, hαp, -⟩ := exists_artinSchreier_generator (M := E) (L := F'') p hdeg
            have hnotimm : ¬ IsImmediate E F'' := fun himm ↦ by
              obtain ⟨a, s, b, -, hsp, hnomin, -⟩ :=
                himm.exists_isSpecialCoset p (Or.inr ⟨α, fun h ↦ hα h, hαp⟩)
              exact hnomin (hE1.exists_isMinimalInCoset p hEnot hsp)
            refine isCartesian_of_not_isImmediate hprime hdeg
              (ramificationIndex_eq_one_or_eq_of_pow_mem hprime hdeg fun x _ ↦ ?_)
              (Or.inl (inertiaDegree_eq_one_of_forall fun x hx ↦ ?_)) hnotimm
            · obtain ⟨c, hc⟩ := exists_norm_pow_finrank_eq (M := E) (M' := F'') x
              exact ⟨c, hdeg ▸ hc⟩
            · obtain ⟨c, hc1, hc⟩ := hresN (x : N) hx
              exact ⟨algebraMap k E c, by rwa [norm_algebraMap'], hc⟩
          · -- `p = 1`: `V = 1` and `W = N`
            subst hp1
            have hV : wildInertiaSubgroup L N = ⊥ := by
              refine eq_bot_iff.mpr fun σ hσ ↦ ?_
              obtain ⟨n, hn⟩ := hVp ⟨σ, hσ⟩
              rw [one_pow, pow_one] at hn
              exact Subgroup.mem_bot.mpr (congrArg Subtype.val hn)
            rw [hW, hV, IntermediateField.fixedField_bot]
            exact isCartesian_of_forall_mem_range fun y ↦ ⟨⟨y, IntermediateField.mem_top⟩, rfl⟩
        exact (isCartesian_iff_of_tower L W N).mpr ⟨hWcart, hNW⟩
      · -- type 2: the value group of `k`; the inertia field `Z` is unramified over `L`
        have hvalN : IsValueTrivial k N := hval.of_finiteDimensional
        have hNK : ∀ x : N, ∃ c : L, ‖c‖ = ‖x‖ := fun x ↦ by
          obtain ⟨c, hc⟩ := hvalN x
          exact ⟨algebraMap k L c, by rw [norm_algebraMap', hc]⟩
        have hTV : inertiaSubgroup L N = wildInertiaSubgroup L N :=
          le_antisymm (inertiaSubgroup_le_wildInertiaSubgroup fun x _ ↦ hNK x)
            wildInertiaSubgroup_le_inertiaSubgroup
        have hTp : IsPGroup p (inertiaSubgroup L N) := by
          rw [hTV]
          exact isPGroup_wildInertiaSubgroup p
        have hGZ : IsPGroup p (N ≃ₐ[IntermediateField.fixedField (inertiaSubgroup L N)] N) :=
          (hTp.of_equiv (MulEquiv.subgroupCongr
            (IntermediateField.fixingSubgroup_fixedField (inertiaSubgroup L N)).symm)).of_equiv
            (IntermediateField.fixingSubgroupEquiv _)
        have hZf := inertiaDegree_inertiaField (K := L) (N := N)
        have hZpi := isPurelyInseparable_residueField_inertiaField (K := L) (N := N)
        obtain ⟨Z, hZ⟩ : ∃ Z, Z = IntermediateField.fixedField (inertiaSubgroup L N) := ⟨_, rfl⟩
        rw [← hZ] at hGZ hZf hZpi
        have hZcart : IsCartesian L Z := by
          unfold IsCartesian
          rw [ramificationIndex_eq_one_of_forall_exists_norm_eq (B := Z) fun x ↦ hNK x, one_mul,
            hZf]
        have hNZ : IsCartesian Z N := by
          rcases expChar_is_prime_or_one k p with hprime | hp1
          · have : Fact p.Prime := ⟨hprime⟩
            have : CharP k p := charP_of_expChar_of_prime hprime
            haveI : IsScalarTower k Z N := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
            refine isCartesian_of_isPGroup hGZ fun E F' hEF hgal hdeg ↦ ?_
            letI := normedAlgebraOfTower k E
            letI := normedAlgebraOfTower L E
            haveI : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
            haveI : IsScalarTower L Z E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
            haveI : FiniteDimensional L E := Module.Finite.trans Z E
            haveI : CompleteSpace E := FiniteDimensional.complete L E
            have hE1 : IsOneDimensional k E := hL.of_finiteDimensional
            have hEnot : ¬ IsImmediateOver k E := not_isImmediateOver_of_isScalarTower hnot
            have : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
            set F'' := IntermediateField.extendScalars hEF
            have : CharP F'' p := charP_of_injective_algebraMap (algebraMap E F'').injective p
            obtain ⟨α, hα, hαp, -⟩ := exists_artinSchreier_generator (M := E) (L := F'') p hdeg
            have hnotimm : ¬ IsImmediate E F'' := fun himm ↦ by
              obtain ⟨a, s, b, -, hsp, hnomin, -⟩ :=
                himm.exists_isSpecialCoset p (Or.inr ⟨α, fun h ↦ hα h, hαp⟩)
              exact hnomin (hE1.exists_isMinimalInCoset p hEnot hsp)
            have : CharP (ResidueField (unitBall E)) p := charP_residueField (p := p)
            have : IsPurelyInseparable (ResidueField (unitBall E)) (ResidueField (unitBall N)) :=
              IsPurelyInseparable.tower_top (ResidueField (unitBall Z)) _ _
            have : IsPurelyInseparable (ResidueField (unitBall E))
                (ResidueField (unitBall F'')) :=
              IsPurelyInseparable.tower_bot _ _ (ResidueField (unitBall N))
            refine isCartesian_of_not_isImmediate hprime hdeg
              (Or.inl (ramificationIndex_eq_one_of_forall_exists_norm_eq fun x ↦ ?_))
              (inertiaDegree_eq_one_or_eq_of_isPurelyInseparable hdeg) hnotimm
            obtain ⟨c, hc⟩ := hvalN (x : N)
            exact ⟨algebraMap k E c, by rw [norm_algebraMap']; exact hc⟩
          · -- `p = 1`: `T = 1` and `Z = N`
            subst hp1
            have hT : inertiaSubgroup L N = ⊥ := by
              refine eq_bot_iff.mpr fun σ hσ ↦ ?_
              obtain ⟨n, hn⟩ := hTp ⟨σ, hσ⟩
              rw [one_pow, pow_one] at hn
              exact Subgroup.mem_bot.mpr (congrArg Subtype.val hn)
            rw [hZ, hT, IntermediateField.fixedField_bot]
            exact isCartesian_of_forall_mem_range fun y ↦ ⟨⟨y, IntermediateField.mem_top⟩, rfl⟩
        exact (isCartesian_iff_of_tower L Z N).mpr ⟨hZcart, hNZ⟩
    -- transport along `ι : F_s → N`
    set ι := IsScalarTower.toAlgHom L Fs N with hι
    have hL' : IsCartesian L ι.fieldRange :=
      ((isCartesian_iff_of_tower L ι.fieldRange N).mp hNL).1
    refine hL'.of_algEquiv ι.equivFieldRange.symm fun y ↦ ?_
    have h := congrArg Subtype.val (ι.equivFieldRange.apply_symm_apply y)
    rw [← norm_algebraMap' N (ι.equivFieldRange.symm y)]
    exact congrArg norm h
  -- the purely inseparable part
  have hFsF : IsCartesian Fs F := by
    rcases expChar_is_prime_or_one k p with hprime | hp1
    · have : Fact p.Prime := ⟨hprime⟩
      have : CharP k p := charP_of_expChar_of_prime hprime
      letI := normedAlgebraOfTower k Fs
      haveI : IsScalarTower k Fs F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      have : CharP Fs p := charP_of_injective_algebraMap (algebraMap k Fs).injective p
      refine isCartesian_of_isPurelyInseparable p fun E γ hγ hγp ↦ ?_
      letI := normedAlgebraOfTower k E
      letI := normedAlgebraOfTower L E
      haveI : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      haveI : IsScalarTower L Fs E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      haveI : FiniteDimensional L E := Module.Finite.trans Fs E
      haveI : CompleteSpace E := FiniteDimensional.complete L E
      have hE1 : IsOneDimensional k E := hL.of_finiteDimensional
      have hEnot : ¬ IsImmediateOver k E := not_isImmediateOver_of_isScalarTower hnot
      have : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
      have : CharP F p := charP_of_injective_algebraMap (algebraMap k F).injective p
      set F'' := IntermediateField.adjoin E {γ} with hF''
      have : CharP F'' p := charP_of_injective_algebraMap (algebraMap E F'').injective p
      have hγE : γ ∉ Set.range (algebraMap E F) := fun ⟨e, he⟩ ↦ hγ (he ▸ e.2)
      have hγpE : γ ^ p ∈ Set.range (algebraMap E F) := ⟨⟨γ ^ p, hγp⟩, rfl⟩
      have hdeg : finrank E F'' = p :=
        finrank_adjoin_of_pow_char_mem p (fun h ↦ hγE (RingHom.mem_range.mp h))
          (c := ⟨γ ^ p, hγp⟩) rfl
      -- every `x ∈ E(γ)` has `x ^ p ∈ E`
      have hpow : ∀ x : F'', ∃ c : E, algebraMap E F'' c = x ^ p := fun x ↦ by
        obtain ⟨c, hc⟩ := pow_char_mem_of_mem_adjoin p hγpE x.2
        exact ⟨c, Subtype.ext hc⟩
      set γ' : F'' := ⟨γ, IntermediateField.mem_adjoin_simple_self E γ⟩
      have hnotimm : ¬ IsImmediate E F'' := fun himm ↦ by
        obtain ⟨a, s, b, -, hsp, hnomin, -⟩ := himm.exists_isSpecialCoset p
          (Or.inl ⟨γ', fun ⟨e, he⟩ ↦ hγE ⟨e, congrArg Subtype.val he⟩, hpow γ'⟩)
        exact hnomin (hE1.exists_isMinimalInCoset p hEnot hsp)
      have : IsPurelyInseparable E F'' :=
        (isPurelyInseparable_iff_pow_mem E p).mpr fun x ↦ ⟨1, by
          obtain ⟨c, hc⟩ := hpow x
          exact ⟨c, by rw [pow_one, hc]⟩⟩
      have : CharP (ResidueField (unitBall E)) p := charP_residueField (p := p)
      have : IsPurelyInseparable (ResidueField (unitBall E)) (ResidueField (unitBall F'')) :=
        isPurelyInseparable_residueField p
      refine isCartesian_of_not_isImmediate hprime hdeg
        (ramificationIndex_eq_one_or_eq_of_pow_mem hprime hdeg fun x _ ↦ ?_)
        (inertiaDegree_eq_one_or_eq_of_isPurelyInseparable hdeg) hnotimm
      obtain ⟨c, hc⟩ := hpow x
      exact ⟨c, by rw [← norm_pow, ← hc, norm_algebraMap']⟩
    · -- `p = 1`: `F/L` is separable
      subst hp1
      have : CharZero k := charZero_of_expChar_one' k
      have : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
      have : Algebra.IsSeparable L F := Algebra.IsAlgebraic.isSeparable_of_perfectField
      have htop : Fs = ⊤ := (separableClosure.eq_top_iff L F).mpr inferInstance
      refine isCartesian_of_forall_mem_range fun y ↦ ⟨⟨y, ?_⟩, rfl⟩
      rw [htop]
      exact IntermediateField.mem_top
  exact (isCartesian_iff_of_tower L Fs F).mpr ⟨hFsc, hFsF⟩

end Stable

end Hironaka.StableModification.Valuation.Analytic
