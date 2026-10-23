/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.Continuity
import DeJongAlterations.StableModification.Valuation.Analytic.Kummer
import DeJongAlterations.StableModification.Valuation.Analytic.Towers
import DeJongAlterations.StableModification.Valuation.Analytic.ArtinSchreier
import DeJongAlterations.StableModification.Valuation.Analytic.CritMinZero

/-!
# Galois closures and immediate extensions of analytic fields

This file collects the field-theoretic tools used in place of Temkin's maximal moderately
ramified extension `K^mr` in the proof of Theorem 6.3.1 of M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010) (`semi-stable.tex`, lines 4052–4111): finite normed
Galois closures, immediate extensions in towers, a base change lemma for immediate extensions, and
the absence of immediate degree-`p` towers over fields whose special cosets have minimal elements.

## Main results

* `galoisClosure_induction` (**normed Galois closures**): a finite separable normed extension `M`
  of an analytic field `K` embeds isometrically into a finite Galois normed extension `N`.
* `IsImmediate.of_isScalarTower_left`, `IsImmediate.of_isScalarTower_right`,
  `IsImmediate.fieldRange`: immediate extensions in towers and under isometric embeddings.
* `normedAlgebraOfLE`: for intermediate fields `A ≤ B`, `B` is a normed `A`-algebra.
* `isImmediate_sup_of_isCartesian` (**base change of immediate extensions**): if `W/K` is Galois
  and Cartesian and `L'/(L' ∩ W)` is immediate, then `L'W/W` is immediate.
* `eq_bot_of_isImmediate_of_isPGroup` (**no immediate `p`-towers**): over an analytic field of
  characteristic `p` whose special cosets have minimal elements, a Galois extension with `p`-group
  Galois group has no nontrivial immediate intermediate field.

## References

Blueprint chapter `sm-val-onedim.tex`: `lem:sm-an-galois-closure`, `lem:sm-an-immediate-sub`,
`lem:sm-an-immediate-base-change`, `lem:sm-an-no-immediate-tower`.
-/

noncomputable section

open IsLocalRing Polynomial Module Topology
open scoped IntermediateField

universe v

namespace DeJongAlterations.StableModification.Valuation.Analytic

/-! ### Normed Galois closures -/

section GaloisClosure

/-- **Normed Galois closures** (Temkin's `K^mr` replaced by a finite Galois closure): if `M` is a
finite separable extension of normed fields of the analytic field `K`, then there is a finite
Galois normed extension `N` of `K` together with an isometric `K`-embedding `M → N` (a normed
`M`-algebra structure on `N`). The statement is in continuation-passing form. -/
theorem galoisClosure_induction {K : Type*} {M : Type v} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [NormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M] {P : Prop}
    (h : ∀ (N : Type v) [NormedField N] [IsUltrametricDist N] [NormedAlgebra K N]
      [FiniteDimensional K N] [IsGalois K N] [NormedAlgebra M N] [IsScalarTower K M N], P) : P := by
  let Ω := AlgebraicClosure M
  have : IsAlgClosure K Ω := ⟨AlgebraicClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
  have hsep : Algebra.IsSeparable K (IntermediateField.normalClosure K M Ω) := by
    rw [normalClosure_def]
    have : ∀ f : M →ₐ[K] Ω, Algebra.IsSeparable K f.fieldRange := fun f ↦
      AlgEquiv.Algebra.isSeparable f.equivFieldRange
    infer_instance
  let N := IntermediateField.normalClosure K M Ω
  have : IsGalois K N := isGalois_iff.mpr ⟨hsep, inferInstance⟩
  have : Algebra.IsAlgebraic K N := Algebra.IsAlgebraic.of_finite K N
  let : NormedField N := spectralNorm.normedField K N
  let : NormedAlgebra K N := spectralNorm.normedAlgebra K N
  have : IsUltrametricDist N := IsUltrametricDist.of_normedAlgebra K
  let : NormedAlgebra M N := spectralNorm.normedAlgebra' K M N
  exact h N

end GaloisClosure

/-! ### Immediate extensions in towers -/

section ImmediateTower

variable {K M L : Type*} [NormedField K] [IsUltrametricDist K] [NormedField M]
  [IsUltrametricDist M] [NormedField L] [IsUltrametricDist L] [NormedAlgebra K M]
  [NormedAlgebra M L] [NormedAlgebra K L] [IsScalarTower K M L]

/-- A subextension of an immediate extension is immediate. -/
theorem IsImmediate.of_isScalarTower_left [FiniteDimensional K M] (h : IsImmediate K L) :
    IsImmediate K M := by
  refine isImmediate_of_forall_exists_norm_sub_lt fun x hx ↦ ?_
  have hx' : algebraMap M L x ≠ 0 := (_root_.map_ne_zero _).mpr hx
  obtain ⟨c, hc⟩ := h.exists_norm_sub_lt hx'
  refine ⟨c, ?_⟩
  rwa [IsScalarTower.algebraMap_apply K M L, ← map_sub, norm_algebraMap', norm_algebraMap'] at hc

/-- The upper part of an immediate extension is immediate. -/
theorem IsImmediate.of_isScalarTower_right [FiniteDimensional M L] (h : IsImmediate K L) :
    IsImmediate M L := by
  refine isImmediate_of_forall_exists_norm_sub_lt fun x hx ↦ ?_
  obtain ⟨c, hc⟩ := h.exists_norm_sub_lt hx
  exact ⟨algebraMap K M c, by rwa [← IsScalarTower.algebraMap_apply]⟩

end ImmediateTower

/-! ### Intermediate fields as normed algebras over smaller ones -/

section LE

variable {K N : Type*} [Field K] [NormedField N] [Algebra K N]

/-- For intermediate fields `A ≤ B` of `N/K`, `B` is a normed `A`-algebra via the inclusion. Not
an instance; introduce it with `let` where needed. -/
abbrev normedAlgebraOfLE {A B : IntermediateField K N} (h : A ≤ B) : NormedAlgebra A B :=
  { (IntermediateField.inclusion h).toAlgebra with
    norm_smul_le := fun c x ↦ by
      change ‖((IntermediateField.inclusion h c * x : B) : N)‖ ≤ ‖(c : N)‖ * ‖(x : N)‖
      rw [MulMemClass.coe_mul, norm_mul]
      rfl }

theorem isScalarTower_normedAlgebraOfLE {A B C : IntermediateField K N} (hAB : A ≤ B)
    (hBC : B ≤ C) :
    letI := normedAlgebraOfLE hAB
    letI := normedAlgebraOfLE hBC
    letI := normedAlgebraOfLE (hAB.trans hBC)
    IsScalarTower A B C := by
  let := normedAlgebraOfLE hAB
  let := normedAlgebraOfLE hBC
  let := normedAlgebraOfLE (hAB.trans hBC)
  exact IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

theorem isScalarTower_base_normedAlgebraOfLE {A B : IntermediateField K N} (hAB : A ≤ B) :
    letI := normedAlgebraOfLE hAB
    IsScalarTower K A B := by
  let := normedAlgebraOfLE hAB
  exact IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

theorem isScalarTower_top_normedAlgebraOfLE {A B : IntermediateField K N} (hAB : A ≤ B) :
    letI := normedAlgebraOfLE hAB
    IsScalarTower A B N := by
  let := normedAlgebraOfLE hAB
  exact IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

end LE

/-! ### Base change of immediate extensions -/

section BaseChange

variable {K N : Type*} [NormedField K] [IsUltrametricDist K] [NormedField N] [IsUltrametricDist N]
  [NormedAlgebra K N] [FiniteDimensional K N]

set_option linter.style.haveILetI false in
/-- **Base change of immediate extensions** (blueprint `lem:sm-an-immediate-base-change`): let
`L', W` be intermediate fields of `N/K` with `W/K` Galois and Cartesian, and assume that `L'` is
immediate over `B = L' ∩ W` (every `x ∈ L' ∖ 0` admits `c ∈ B` with `‖x - c‖ < ‖x‖`). Then `L'W`
is immediate over `W`. -/
theorem isImmediate_sup_of_isCartesian {L' W : IntermediateField K N} [IsGalois K W]
    (hW : IsCartesian K W) (hL' : ∀ x ∈ L', x ≠ 0 → ∃ c ∈ L' ⊓ W, ‖x - c‖ < ‖x‖) :
    ∀ x ∈ L' ⊔ W, x ≠ 0 → ∃ c ∈ W, ‖x - c‖ < ‖x‖ := by
  obtain ⟨B, hB⟩ : ∃ B, B = L' ⊓ W := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = L' ⊔ W := ⟨_, rfl⟩
  rw [← hB] at hL'
  rw [← hC]
  have hBL : B ≤ L' := hB ▸ inf_le_left
  have hBW : B ≤ W := hB ▸ inf_le_right
  have hLC : L' ≤ C := hC ▸ le_sup_left
  have hWC : W ≤ C := hC ▸ le_sup_right
  letI := normedAlgebraOfLE hBL
  letI := normedAlgebraOfLE hBW
  letI := normedAlgebraOfLE hLC
  letI := normedAlgebraOfLE hWC
  letI := normedAlgebraOfLE (hBL.trans hLC)
  haveI : IsScalarTower B L' C := isScalarTower_normedAlgebraOfLE hBL hLC
  haveI : IsScalarTower B W C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower K B W := isScalarTower_base_normedAlgebraOfLE hBW
  haveI : IsScalarTower K L' C := isScalarTower_base_normedAlgebraOfLE hLC
  haveI : IsScalarTower K B L' := isScalarTower_base_normedAlgebraOfLE hBL
  haveI : IsScalarTower K W C := isScalarTower_base_normedAlgebraOfLE hWC
  have : FiniteDimensional B W := FiniteDimensional.right K B W
  have : FiniteDimensional B L' := FiniteDimensional.right K B L'
  have : FiniteDimensional L' C := FiniteDimensional.right K L' C
  have : FiniteDimensional W C := FiniteDimensional.right K W C
  -- degrees: `[L'W : L'] = [W : B]`
  have hdisj := finrank_sup_mul_finrank_inf L' W
  have t1 : finrank K B * finrank B W = finrank K W :=
    @Module.finrank_mul_finrank K B W _ _ _ _ _ _ _ _ _ (Module.Free.of_divisionRing K B)
      (Module.Free.of_divisionRing B W)
  have t2 : finrank K L' * finrank L' C = finrank K C :=
    @Module.finrank_mul_finrank K L' C _ _ _ _ _ _ _ _ _ (Module.Free.of_divisionRing K L')
      (Module.Free.of_divisionRing L' C)
  have hBpos : 0 < finrank K B := Module.finrank_pos
  have hLpos : 0 < finrank K L' := Module.finrank_pos
  have hdeg : finrank L' C = finrank B W := by
    have h' : finrank L' C * (finrank K L' * finrank K B) =
        finrank B W * (finrank K L' * finrank K B) := by
      have e1 : finrank K C * finrank K B = finrank K L' * finrank K W := by
        rw [hB, hC]; exact hdisj
      rw [← t2, ← t1] at e1
      linarith [e1]
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hLpos hBpos) h'
  -- `L'/B` is immediate and `W/B` is Cartesian
  have hLB : IsImmediate B L' :=
    isImmediate_of_forall_exists_norm_sub_lt fun x hx ↦ by
      have hx0 : (x : N) ≠ 0 := fun h0 ↦ hx (Subtype.ext h0)
      obtain ⟨c, hcB, hc⟩ := hL' x x.2 hx0
      exact ⟨⟨c, hcB⟩, hc⟩
  have hWB : IsCartesian B W := ((isCartesian_iff_of_tower K B W).mp hW).2
  -- multiplicativity
  have m1 := ramificationIndex_mul_ramificationIndex B L' C
  have m2 := inertiaDegree_mul_inertiaDegree B L' C
  have m3 := ramificationIndex_mul_ramificationIndex B W C
  have m4 := inertiaDegree_mul_inertiaDegree B W C
  have fi := ramificationIndex_mul_inertiaDegree_le (K := L') (L := C)
  have hWBpos : 0 < finrank B W := by
    have hWpos : 0 < finrank K W := Module.finrank_pos
    rw [← t1] at hWpos
    exact Nat.pos_of_mul_pos_left hWpos
  have e1 := ramificationIndex_pos (K := W) (L := C)
  have f1 : 0 < inertiaDegree W C := by rw [inertiaDegree_def]; exact Module.finrank_pos
  rw [hLB.1, one_mul] at m1
  rw [hLB.2, one_mul] at m2
  have hWB' : ramificationIndex B W * inertiaDegree B W = finrank B W := hWB
  have hkey : ramificationIndex W C * inertiaDegree W C * finrank B W ≤ 1 * finrank B W := by
    calc ramificationIndex W C * inertiaDegree W C * finrank B W
        = (ramificationIndex B W * ramificationIndex W C) *
            (inertiaDegree B W * inertiaDegree W C) := by rw [← hWB']; ring
      _ = ramificationIndex L' C * inertiaDegree L' C := by rw [m3, m4, ← m1, ← m2]
      _ ≤ finrank L' C := fi
      _ = 1 * finrank B W := by rw [hdeg, one_mul]
  have hle := Nat.le_of_mul_le_mul_right hkey hWBpos
  have hef : ramificationIndex W C * inertiaDegree W C = 1 :=
    le_antisymm hle (Nat.mul_pos e1 f1)
  have hWimm : IsImmediate W C :=
    ⟨Nat.eq_one_of_mul_eq_one_right hef, Nat.eq_one_of_mul_eq_one_left hef⟩
  intro x hx hx0
  obtain ⟨c, hc⟩ := hWimm.exists_norm_sub_lt (x := (⟨x, hx⟩ : C))
    fun h0 ↦ hx0 (by
      have h1 : ((⟨x, hx⟩ : C) : N) = 0 := by rw [h0]; rfl
      exact h1)
  exact ⟨c, c.2, hc⟩

end BaseChange

/-! ### No immediate `p`-towers -/

section NoImmediate

variable {W N : Type*} [NontriviallyNormedField W] [IsUltrametricDist W] [CompleteSpace W]
  [NormedField N] [IsUltrametricDist N] [NormedAlgebra W N] [FiniteDimensional W N] [IsGalois W N]

/-- **No immediate `p`-towers** (blueprint `lem:sm-an-no-immediate-tower`): let `W` be an analytic
field of characteristic `p` in which every special coset has a minimal element, and `N/W` a finite
Galois extension whose Galois group is a `p`-group. Then every intermediate field `M` of `N/W`
which is immediate over `W` is `W` itself. -/
theorem eq_bot_of_isImmediate_of_isPGroup (p : ℕ) [Fact p.Prime] [CharP W p]
    (hG : IsPGroup p (N ≃ₐ[W] N))
    (hcm : ∀ (a : W) (s : ℝ) (b : W), IsSpecialCoset p a s b → ∃ x, IsMinimalInCoset p a s b x)
    {M : IntermediateField W N} (hM : IsImmediate W M) : M = ⊥ := by
  have : CharP N p := charP_of_injective_algebraMap (algebraMap W N).injective p
  refine IsPGroup.induction_intermediateField hG (P := fun M ↦ IsImmediate W M → M = ⊥)
    (fun _ ↦ rfl) ?_ M hM
  intro E F hEF hgal hdeg hPE hF
  have hE : IsImmediate W E :=
    isImmediate_of_forall_exists_norm_sub_lt fun x hx ↦ by
      obtain ⟨c, hc⟩ := hF.exists_norm_sub_lt (x := (⟨x, hEF x.2⟩ : F))
        fun h0 ↦ hx (by
          have h1 : ((⟨x, hEF x.2⟩ : F) : N) = 0 := by rw [h0]; rfl
          exact Subtype.ext h1)
      exact ⟨c, hc⟩
  have hE0 := hPE hE
  obtain ⟨α, hα, hαp, -⟩ := exists_artinSchreier_generator (M := E)
    (L := IntermediateField.extendScalars hEF) p hdeg
  set α' : F := ⟨α, (IntermediateField.mem_extendScalars hEF).mp α.2⟩
  have hα' : α' ∉ Set.range (algebraMap W F) := by
    rintro ⟨c, hc⟩
    apply hα
    refine ⟨algebraMap W E c, Subtype.ext ?_⟩
    have := congrArg Subtype.val hc
    simpa [α'] using this
  have hα'p : α' ^ p - α' ∈ Set.range (algebraMap W F) := by
    obtain ⟨e, he⟩ := hαp
    have heW : (e : N) ∈ (⊥ : IntermediateField W N) := hE0 ▸ e.2
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp heW
    refine ⟨c, Subtype.ext ?_⟩
    have := congrArg Subtype.val he
    simp only [α', SubalgebraClass.coe_algebraMap] at this ⊢
    rw [hc]
    simpa using this
  obtain ⟨a, s, b, -, hsp, hnomin, -⟩ := hF.exists_isSpecialCoset p (Or.inr ⟨α', hα', hα'p⟩)
  exact absurd (hcm a s b hsp) hnomin

end NoImmediate

end DeJongAlterations.StableModification.Valuation.Analytic
