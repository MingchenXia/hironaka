/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.AnalyticSubsetPresentationsExact
import Hironaka.Support.ConstantRankImageGraphExact
import Hironaka.Analytic.GenericSections
import Hironaka.Analytic.RemmertStatements
import Hironaka.Analytic.ConstantRankSubmanifold

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Generic linear coordinates for the flat case of the Remmert--Stein theorem

Blueprint `rem:remmert-stein-flat`, paragraph "Coordinates" (Demailly, *Complex analytic and
differential geometry*, II.8.7).  Let `L = ℂᵖ × {0} ⊆ ℂⁿ` and `E` analytic in an open set
`U ⊆ ℂⁿ \ L` with `dim E ≤ s`, `p < s ≤ n`, and `a ∈ L`.  We find a linear isomorphism
`Λ = (π, κ) : ℂⁿ ≃ ℂˢ × ℂᵈ` such that

* `π(L) ⊆ ℂᵖ × {0} ⊆ ℂˢ` and `π` is injective on `L`;
* `E ∩ π⁻¹(ℂᵖ × {0})` has dimension `≤ p`;
* `E ∩ π⁻¹(π a)` has dimension `≤ 0` (it is discrete).

The forms are chosen by iterated generic sections (`GenericSections`), in a version where the level
is measured against a base VECTOR `c` (the point `a ∈ L` is not a point of the manifold `U`) and
where the chosen forms satisfy an independence constraint `ρ ∘ ξ` linearly independent
(`exists_generic_forms`): first `s - p` forms vanishing on `L`, independent; then `p` forms whose
restrictions to `L` are independent.

Sorry-free.
-/

open Set Filter Topology TopologicalSpace Module
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.RemmertSteinCoordinates

open AnalyticDimensionBasics AnalyticSubsetOpens GenericSections ThinDimensionDrop
  DimensionMonotone

section Generic

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The forms whose values along `g` on `S` all equal their value at the vector `c`. -/
def levelSubmoduleVec {N : ℕ} (g : M → ComplexModel N) (c : ComplexModel N) (S : Set M) :
    Submodule ℂ (ComplexModel N →L[ℂ] ℂ) where
  carrier := {ξ | ∀ y ∈ S, ξ (g y) = ξ c}
  add_mem' := by
    intro ξ η hξ hη y hy
    simp [hξ y hy, hη y hy]
  zero_mem' := by
    intro y _
    simp
  smul_mem' := by
    intro c' ξ hξ y hy
    simp [hξ y hy]

/-- **Generic sections relative to a base vector**: as `GenericSections.exists_generic_sections`,
the level of `ξ ∘ g` being `ξ c` for a fixed vector `c` separated from `g(T)` by `Ξ`. -/
theorem exists_generic_sections_vec {T : Set M} (hT : IsComplexAnalyticSubset (n := n) T)
    {k : ℕ} (hk : 1 ≤ k) (hdim : DimLE (n := n) T k) {N : ℕ} (g : M → ComplexModel N)
    (c : ComplexModel N) (Ξ : Submodule ℂ (ComplexModel N →L[ℂ] ℂ))
    (hsep : ∀ y ∈ T, ∃ ξ ∈ Ξ, ξ (g y) ≠ ξ c) :
    ∃ S : Set (Submodule ℂ (ComplexModel N →L[ℂ] ℂ)), S.Countable ∧ (∀ H ∈ S, ¬ Ξ ≤ H) ∧
      ∀ ξ ∈ Ξ, (∀ H ∈ S, ξ ∉ H) → DimLE (n := n) (T ∩ {y | ξ (g y) = ξ c}) (k - 1) := by
  classical
  have hBc := TopologicalSpace.countable_countableBasis M
  have hB := TopologicalSpace.isBasis_countableBasis M
  set B := TopologicalSpace.countableBasis M with hBdef
  set I : Set (Set M) := {O | O ∈ B ∧ (T ∩ O).Nonempty} with hI
  refine ⟨(fun O => levelSubmoduleVec g c (T ∩ O)) '' I, (hBc.mono fun O hO => hO.1).image _,
    ?_, ?_⟩
  · rintro _ ⟨O, ⟨-, y, hyTO⟩, rfl⟩ hle
    obtain ⟨ξ, hξΞ, hξ⟩ := hsep y hyTO.1
    exact hξ (hle hξΞ y hyTO)
  · intro ξ hξΞ hξS y j hy
    have hT'T : T ∩ {y | ξ (g y) = ξ c} ⊆ T := inter_subset_left
    have := lt_of_regularAtDim_of_thin hT hT'T (a := k) (hdim := hdim) (hy := hy) (by
      intro O hO hOT
      by_contra hne
      obtain ⟨y', hy'O, hy'T⟩ := nonempty_iff_ne_empty.mpr hne
      obtain ⟨Ob, hObB, hy'Ob, hObO⟩ := hB.exists_subset_of_mem_open hy'O hO
      have hOb : Ob ∈ I := ⟨hObB, y', hy'T, hy'Ob⟩
      apply hξS _ ⟨Ob, hOb, rfl⟩
      intro z hz
      exact (hOT ⟨hObO hz.2, hz.1⟩).2)
    omega

/-- **Iterated generic sections with an independence constraint.**  Let `T` be analytic with
`dim T ≤ d + j`, `g` holomorphic, `Ξ` a space of forms separating `g(T)` from the vector `c`,
`ρ` a linear map from forms to a finite-dimensional space and `W` a subspace there with
`finrank W + j ≤ finrank (W ⊔ ρ(Ξ))`.  There are `ξ₁, …, ξ_j ∈ Ξ` with
`finrank (W ⊔ span (ρ ξ)) = finrank W + j` and `dim (T ∩ {ξ_i ∘ g = ξ_i c}) ≤ d`. -/
theorem exists_generic_forms {N : ℕ} {g : M → ComplexModel N}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ g) (c : ComplexModel N)
    (Ξ : Submodule ℂ (ComplexModel N →L[ℂ] ℂ)) {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : (ComplexModel N →L[ℂ] ℂ) →ₗ[ℂ] V) (d : ℕ) :
    ∀ (j : ℕ) {T : Set M}, IsComplexAnalyticSubset (n := n) T → DimLE (n := n) T (d + j) →
      (∀ y ∈ T, ∃ ξ ∈ Ξ, ξ (g y) ≠ ξ c) →
      ∀ W : Submodule ℂ V, finrank ℂ W + j ≤ finrank ℂ ↥(W ⊔ Ξ.map ρ) →
      ∃ ξ : Fin j → (ComplexModel N →L[ℂ] ℂ), (∀ i, ξ i ∈ Ξ) ∧
        finrank ℂ ↥(W ⊔ Submodule.span ℂ (range (ρ ∘ ξ))) = finrank ℂ W + j ∧
        DimLE (n := n) (T ∩ {y | ∀ i, ξ i (g y) = ξ i c}) d := by
  intro j
  induction j with
  | zero =>
    intro T _ hdim _ W _
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_, ?_⟩
    · have : range (ρ ∘ (Fin.elim0 : Fin 0 → (ComplexModel N →L[ℂ] ℂ))) = ∅ := by
        ext v
        simp
      rw [this, Submodule.span_empty, sup_bot_eq]
      rfl
    · have hset : T ∩ {y | ∀ i : Fin 0, (Fin.elim0 i : ComplexModel N →L[ℂ] ℂ) (g y) =
          (Fin.elim0 i : ComplexModel N →L[ℂ] ℂ) c} = T := by
        ext y
        simp
      rw [hset]
      simpa using hdim
  | succ j ih =>
    intro T hT hdim hsep W hW
    obtain ⟨S, hSc, hSprop, hS⟩ :=
      exists_generic_sections_vec hT (by omega) hdim g c Ξ hsep
    have hH₀ : ¬ Ξ ≤ W.comap ρ := by
      intro hle
      have : W ⊔ Ξ.map ρ = W := sup_eq_left.mpr (Submodule.map_le_iff_le_comap.mpr hle)
      rw [this] at hW
      omega
    obtain ⟨ξ₀, hξ₀Ξ, hξ₀S⟩ := exists_mem_forall_not_mem Ξ (hSc.insert (W.comap ρ))
      (by
        rintro H (rfl | hH)
        · exact hH₀
        · exact hSprop H hH)
    have hξ₀W : ρ ξ₀ ∉ W := fun h => hξ₀S _ (mem_insert _ _) h
    set T₁ := T ∩ {y | ξ₀ (g y) = ξ₀ c} with hT₁
    have hT₁a : IsComplexAnalyticSubset (n := n) T₁ :=
      isComplexAnalyticSubset_section hT hg ξ₀ _
    have hT₁d : DimLE (n := n) T₁ (d + j) := by
      have := hS ξ₀ hξ₀Ξ fun H hH => hξ₀S H (mem_insert_of_mem _ hH)
      simpa using this
    set W' := W ⊔ Submodule.span ℂ {ρ ξ₀} with hW'
    have hW'rank : finrank ℂ W' = finrank ℂ W + 1 := by
      have hinf : W ⊓ Submodule.span ℂ {ρ ξ₀} = ⊥ := by
        rw [eq_bot_iff]
        intro v ⟨hvW, hvs⟩
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hvs
        by_cases ht : t = 0
        · simp [ht]
        · exact absurd ((Submodule.smul_mem_iff W ht).mp hvW) hξ₀W
      have hne : ρ ξ₀ ≠ 0 := fun h => hξ₀W (h ▸ W.zero_mem)
      have := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℂ {ρ ξ₀})
      rw [hinf, finrank_bot, finrank_span_singleton hne] at this
      omega
    have hW'sup : W' ⊔ Ξ.map ρ = W ⊔ Ξ.map ρ := by
      rw [hW', sup_assoc]
      congr 1
      exact sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr
        (Submodule.mem_map_of_mem hξ₀Ξ))
    obtain ⟨ξ', hξ'Ξ, hξ'rank, hξ'dim⟩ := ih hT₁a hT₁d (fun y hy => hsep y hy.1) W' (by
      rw [hW'sup, hW'rank]
      omega)
    refine ⟨Fin.cons ξ₀ ξ', fun i => Fin.cases hξ₀Ξ hξ'Ξ i, ?_, ?_⟩
    · have hrange : range (ρ ∘ (Fin.cons ξ₀ ξ' : Fin (j + 1) → _)) =
          insert (ρ ξ₀) (range (ρ ∘ ξ')) := by
        rw [Fin.comp_cons, Fin.range_cons]
      rw [hrange, Submodule.span_insert, ← sup_assoc, ← hW', hξ'rank, hW'rank]
      ring
    · have hset : T ∩ {y | ∀ i, (Fin.cons ξ₀ ξ' : Fin (j + 1) → _) i (g y) =
          (Fin.cons ξ₀ ξ' : Fin (j + 1) → _) i c} =
          T₁ ∩ {y | ∀ i, ξ' i (g y) = ξ' i c} := by
        ext y
        simp only [hT₁, mem_inter_iff, mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero,
          Fin.cons_succ]
        tauto
      rw [hset]
      exact hξ'dim

end Generic

section Linear

variable {n : ℕ}

/-- The common zero set of finitely many affine-linear equations is analytic in `ℂⁿ`. -/
theorem isComplexAnalyticSubset_levels {r : ℕ} (ξ : Fin r → (ComplexModel n →L[ℂ] ℂ))
    (c : ComplexModel n) :
    IsComplexAnalyticSubset (n := n) (M := ComplexModel n) {w | ∀ i, ξ i w = ξ i c} := by
  intro x
  exact ⟨{ generatorCount := r
           generator := fun i w => ξ i w - ξ i c
           coordinateNeighborhood := (complexChartAt (n := n) x).val.target
           isOpen_coordinateNeighborhood := (complexChartAt (n := n) x).val.open_target
           center_mem_coordinateNeighborhood :=
             (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
           coordinateNeighborhood_subset_target := Subset.rfl
           generator_holomorphic := fun i => ((ξ i).differentiable.sub_const _).differentiableOn
           zeroLocus := by
             intro y _ _
             change (∀ i, ξ i y = ξ i c) ↔ ∀ i, ξ i y - ξ i c = 0
             simp [sub_eq_zero] }⟩

/-- Coordinate projections at distinct indices are linearly independent forms. -/
theorem linearIndependent_proj {r : ℕ} {f : Fin r → Fin n} (hf : Function.Injective f) :
    LinearIndependent ℂ (fun j => (EuclideanSpace.proj (f j) : ComplexModel n →L[ℂ] ℂ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have := congrArg (fun φ : ComplexModel n →L[ℂ] ℂ => φ (EuclideanSpace.single (f j) 1)) hg
  simp [PiLp.single_apply, hf.eq_iff] at this
  exact this

/-- The forms vanishing on `ℂᵖ × {0}`. -/
def annPlane (n p : ℕ) : Submodule ℂ (ComplexModel n →L[ℂ] ℂ) where
  carrier := {ξ | ∀ v ∈ complexCoordinatePlane n p, ξ v = 0}
  add_mem' := by
    intro ξ η hξ hη v hv
    simp [hξ v hv, hη v hv]
  zero_mem' := by
    intro v _
    simp
  smul_mem' := by
    intro c ξ hξ v hv
    simp [hξ v hv]

theorem proj_mem_annPlane {p : ℕ} {i : Fin n} (hi : p ≤ i.1) :
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ) ∈ annPlane n p := fun _ hv => hv i hi

theorem le_finrank_annPlane {p : ℕ} (hpn : p ≤ n) : n - p ≤ finrank ℂ (annPlane n p) := by
  let f : Fin (n - p) → Fin n := fun j => ⟨p + j.1, by omega⟩
  have hf : Function.Injective f := by
    intro j j' h
    ext
    simpa [f] using h
  have hli := linearIndependent_proj hf
  have hspan : Submodule.span ℂ (range fun j => (EuclideanSpace.proj (f j) :
      ComplexModel n →L[ℂ] ℂ)) ≤ annPlane n p := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact proj_mem_annPlane (by simp [f])
  have := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_fin] at this
  exact this

/-- Restriction of forms to `ℂᵖ × {0}`. -/
def restrictPlane (n p : ℕ) :
    (ComplexModel n →L[ℂ] ℂ) →ₗ[ℂ] (ConstantRankSubmanifold.planeSubmodule n p →ₗ[ℂ] ℂ) :=
  (LinearMap.domRestrict' (ConstantRankSubmanifold.planeSubmodule n p)).comp
    (ContinuousLinearMap.coeLM ℂ)

@[simp] theorem restrictPlane_apply {p : ℕ} (ξ : ComplexModel n →L[ℂ] ℂ)
    (v : ConstantRankSubmanifold.planeSubmodule n p) : restrictPlane n p ξ v = ξ v := rfl

theorem single_mem_plane {p : ℕ} {i : Fin n} (hi : i.1 < p) :
    (EuclideanSpace.single i (1 : ℂ) : ComplexModel n) ∈ complexCoordinatePlane n p := by
  intro j hj
  have : j ≠ i := fun h => by subst h; omega
  simp [this]

theorem le_finrank_map_restrictPlane {p : ℕ} (hpn : p ≤ n) :
    p ≤ finrank ℂ ((⊤ : Submodule ℂ (ComplexModel n →L[ℂ] ℂ)).map (restrictPlane n p)) := by
  classical
  let f : Fin p → Fin n := fun j => ⟨j.1, by omega⟩
  let v : Fin p → (ConstantRankSubmanifold.planeSubmodule n p →ₗ[ℂ] ℂ) :=
    fun j => restrictPlane n p (EuclideanSpace.proj (f j))
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun φ : ConstantRankSubmanifold.planeSubmodule n p →ₗ[ℂ] ℂ =>
      φ ⟨EuclideanSpace.single (f j) 1, single_mem_plane (by simp [f])⟩) hg
    have hfi : ∀ i, f i = f j ↔ i = j := fun i => by
      constructor
      · intro h
        ext
        simpa [f] using congrArg Fin.val h
      · rintro rfl
        rfl
    simp [v, PiLp.single_apply, hfi] at this
    exact this
  have hspan : Submodule.span ℂ (range v) ≤
      (⊤ : Submodule ℂ (ComplexModel n →L[ℂ] ℂ)).map (restrictPlane n p) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_map_of_mem Submodule.mem_top
  have := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_fin] at this
  exact this

end Linear

section Flat

variable {n : ℕ}

/-- **Generic linear coordinates for the flat case of Remmert--Stein.**  Let `L = ℂᵖ × {0}`,
`E` analytic in an open `U ⊆ ℂⁿ \ L` with `dim E ≤ p + t` (`t ≥ 1`, `p + t ≤ n`), and `a ∈ L`.
There is a linear isomorphism `Λ = (π, κ) : ℂⁿ ≃ ℂ^{p+t} × ℂ^{n-p-t}` with `π(L) ⊆ ℂᵖ × {0}`,
`π` injective on `L` (relative to `a`), `dim (E ∩ π⁻¹(ℂᵖ × {0})) ≤ p` and
`dim (E ∩ π⁻¹(π a)) ≤ 0`. -/
theorem exists_flat_coordinates {p t : ℕ} (ht : 1 ≤ t) (hsn : p + t ≤ n)
    {U : Opens (ComplexModel n)} (hUL : ∀ z ∈ U, z ∉ complexCoordinatePlane n p)
    {E : Set (ComplexModel n)} (hEU : E ⊆ U)
    (hE : IsComplexAnalyticSubset (n := n) ((↑) ⁻¹' E : Set U))
    (hdim : DimLE (n := n) E (p + t)) {a : ComplexModel n}
    (ha : a ∈ complexCoordinatePlane n p) :
    ∃ Λ : ComplexModel n ≃L[ℂ] ComplexModel (p + t) × ComplexModel (n - (p + t)),
      (∀ l ∈ complexCoordinatePlane n p, (Λ l).1 ∈ complexCoordinatePlane (p + t) p) ∧
      (∀ l ∈ complexCoordinatePlane n p, (Λ l).1 = (Λ a).1 → l = a) ∧
      DimLE (n := n) (E ∩ {z | (Λ z).1 ∈ complexCoordinatePlane (p + t) p}) p ∧
      DimLE (n := n) (E ∩ {z | (Λ z).1 = (Λ a).1}) 0 := by
  classical
  set T : Set U := (↑) ⁻¹' E with hTdef
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      ((↑) : U → ComplexModel n) := contMDiff_subtype_val
  have hTdim : DimLE (n := n) T (p + t) := dimLE_preimage_val hdim U
  have hsepi : ∀ y : U, ∃ i : Fin n, p ≤ i.1 ∧ (y : ComplexModel n) i ≠ a i := by
    intro y
    have hyL : (y : ComplexModel n) ∉ complexCoordinatePlane n p := hUL y y.2
    simp only [complexCoordinatePlane, mem_ofPred_eq, not_forall] at hyL
    obtain ⟨i, hi, hyi⟩ := hyL
    exact ⟨i, hi, by rw [ha i hi]; exact hyi⟩
  -- phase 1: `t` independent forms vanishing on `L`
  obtain ⟨ξ₁, hξ₁Ξ, hξ₁rank, hT₁dim⟩ := exists_generic_forms hg a (annPlane n p) LinearMap.id p t
    hE hTdim (fun y _ => by
      obtain ⟨i, hi, hne⟩ := hsepi y
      exact ⟨_, proj_mem_annPlane hi, by simpa using hne⟩) ⊥ (by
      rw [finrank_bot, zero_add, bot_sup_eq, Submodule.map_id]
      have := le_finrank_annPlane (n := n) (p := p) (by omega)
      omega)
  set T₁ := T ∩ {y | ∀ i, ξ₁ i (y : ComplexModel n) = ξ₁ i a} with hT₁
  have hT₁a : IsComplexAnalyticSubset (n := n) T₁ :=
    hE.inter (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg
      (isComplexAnalyticSubset_levels ξ₁ a))
  -- phase 2: `p` forms with independent restrictions to `L`
  obtain ⟨ξ₂, -, hξ₂rank, hT₂dim⟩ := exists_generic_forms hg a ⊤ (restrictPlane n p) 0 p
    hT₁a (by simpa using hT₁dim) (fun y _ => by
      obtain ⟨i, -, hne⟩ := hsepi y
      exact ⟨EuclideanSpace.proj i, Submodule.mem_top, by simpa using hne⟩) ⊥ (by
      rw [finrank_bot, zero_add, bot_sup_eq]
      exact le_finrank_map_restrictPlane (n := n) (p := p) (by omega))
  set T₂ := T₁ ∩ {y | ∀ i, ξ₂ i (y : ComplexModel n) = ξ₂ i a} with hT₂
  have hT₂a : IsComplexAnalyticSubset (n := n) T₂ :=
    hT₁a.inter (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg
      (isComplexAnalyticSubset_levels ξ₂ a))
  -- independence
  have hξ₁li : LinearIndependent ℂ ξ₁ := by
    rw [bot_sup_eq, finrank_bot, zero_add] at hξ₁rank
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    simpa [Set.finrank] using hξ₁rank.symm
  have hξ₂li : LinearIndependent ℂ (restrictPlane n p ∘ ξ₂) := by
    rw [bot_sup_eq, finrank_bot, zero_add] at hξ₂rank
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    simpa [Set.finrank] using hξ₂rank.symm
  have hres₁ : ∀ j, restrictPlane n p (ξ₁ j) = 0 := fun j => by
    ext v
    exact hξ₁Ξ j v v.2
  set ζ : Fin (p + t) → (ComplexModel n →L[ℂ] ℂ) := Fin.append ξ₂ ξ₁ with hζ
  have hζli : LinearIndependent ℂ ζ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [hζ, Fin.append_left, Fin.append_right] at hg
    have h₂ : ∀ i, g (Fin.castAdd t i) = 0 := by
      have := congrArg (restrictPlane n p) hg
      simp only [map_add, map_sum, map_smul, hres₁, smul_zero, Finset.sum_const_zero,
        add_zero, map_zero] at this
      exact (Fintype.linearIndependent_iff.mp hξ₂li) _ this
    have h₁ : ∀ j, g (Fin.natAdd p j) = 0 := by
      have h0 : ∑ x, g (Fin.castAdd t x) • ξ₂ x = 0 :=
        Finset.sum_eq_zero fun x _ => by rw [h₂ x]; exact zero_smul ℂ (ξ₂ x)
      rw [h0, zero_add] at hg
      exact (Fintype.linearIndependent_iff.mp hξ₁li) _ hg
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact h₂ i
    · exact h₁ j
  -- the map `π`
  set π : ComplexModel n →L[ℂ] ComplexModel (p + t) :=
    (EuclideanSpace.equiv (Fin (p + t)) ℂ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi ζ) with hπ
  have hπapp : ∀ z i, π z i = ζ i z := fun z i => rfl
  have hπsurj : Function.Surjective π := by
    have : Function.Surjective (π : ComplexModel n →ₗ[ℂ] ComplexModel (p + t)) := by
      rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
      intro ψ hψ
      have hsum : ∑ i, ψ (EuclideanSpace.single i 1) • ζ i = 0 := by
        ext z
        have h1 : ψ (π z) = 0 := by simpa using LinearMap.congr_fun hψ z
        have h2 : π z = ∑ i, ζ i z • (EuclideanSpace.single i 1 : ComplexModel (p + t)) := by
          have := (EuclideanSpace.basisFun (Fin (p + t)) ℂ).sum_repr (π z)
          simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
            hπapp] at this
          exact this.symm
        rw [h2, map_sum] at h1
        simp only [map_smul, smul_eq_mul] at h1
        simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
          smul_eq_mul, zero_apply]
        rw [← h1]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      have hzero := (Fintype.linearIndependent_iff.mp hζli) _ hsum
      exact (EuclideanSpace.basisFun (Fin (p + t)) ℂ).toBasis.ext fun i => by
        simpa [EuclideanSpace.basisFun_apply] using hzero i
    exact this
  -- the complement `κ` and `Λ`
  set πl : ComplexModel n →ₗ[ℂ] ComplexModel (p + t) := π.toLinearMap with hπl
  have hrange : LinearMap.range πl = ⊤ := LinearMap.range_eq_top.mpr hπsurj
  have hK : finrank ℂ (LinearMap.ker πl) = n - (p + t) := by
    have := LinearMap.finrank_range_add_finrank_ker πl
    rw [hrange, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at this
    omega
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker πl)
  let ι : LinearMap.ker πl ≃ₗ[ℂ] ComplexModel (n - (p + t)) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hK, finrank_euclideanSpace_fin])
  let κl : ComplexModel n →ₗ[ℂ] ComplexModel (n - (p + t)) :=
    ι.toLinearMap ∘ₗ (LinearMap.ker πl).projectionOnto C hC
  let Λl := πl.prod κl
  have hΛinj : Function.Injective Λl := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 : πl z = 0 := congrArg Prod.fst hz
    have h2 : κl z = 0 := congrArg Prod.snd hz
    have hzK : z ∈ LinearMap.ker πl := h1
    simp only [κl, LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_left hC hzK,
      LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff] at h2
    simpa using congrArg Subtype.val h2
  have hΛbij : Function.Bijective Λl := by
    refine ⟨hΛinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hΛinj⟩
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin]
    omega
  let Λ : ComplexModel n ≃L[ℂ] ComplexModel (p + t) × ComplexModel (n - (p + t)) :=
    (LinearEquiv.ofBijective Λl hΛbij).toContinuousLinearEquiv
  have hΛ1 : ∀ z, (Λ z).1 = π z := fun z => rfl
  -- the properties
  have hξ₁a : ∀ j, ξ₁ j a = 0 := fun j => hξ₁Ξ j a ha
  have hfst : ∀ z i, (Λ z).1 i = ζ i z := fun z i => rfl
  have himage : ∀ X : Set (ComplexModel n), X ⊆ E →
      ((↑) '' ((↑) ⁻¹' X : Set U) : Set (ComplexModel n)) = X := by
    intro X hX
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hz
      exact ⟨⟨z, hEU (hX hz)⟩, hz, rfl⟩
  refine ⟨Λ, ?_, ?_, ?_, ?_⟩
  · intro l hl i hi
    have : i = Fin.natAdd p ⟨i.1 - p, by omega⟩ := by ext; simp; omega
    rw [hfst, this, hζ, Fin.append_right]
    exact hξ₁Ξ _ l hl
  · intro l hl hla
    have hlaP : l - a ∈ ConstantRankSubmanifold.planeSubmodule n p :=
      Submodule.sub_mem _ hl ha
    have hzero : ∀ k, restrictPlane n p (ξ₂ k) ⟨l - a, hlaP⟩ = 0 := by
      intro k
      have := congrArg (fun w => w (Fin.castAdd t k)) hla
      simp only [hfst, hζ, Fin.append_left] at this
      simp [this]
    have hspan : Submodule.span ℂ (range (restrictPlane n p ∘ ξ₂)) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card hξ₂li, Fintype.card_fin, Subspace.dual_finrank_eq,
        ConstantRankSubmanifold.finrank_planeSubmodule (by omega)]
    have hall : ∀ φ : Module.Dual ℂ (ConstantRankSubmanifold.planeSubmodule n p),
        φ ⟨l - a, hlaP⟩ = 0 := by
      intro φ
      have hφ : φ ∈ Submodule.span ℂ (range (restrictPlane n p ∘ ξ₂)) := hspan ▸ Submodule.mem_top
      have hle : Submodule.span ℂ (range (restrictPlane n p ∘ ξ₂)) ≤
          LinearMap.ker (Module.Dual.eval ℂ _ ⟨l - a, hlaP⟩) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        simpa using hzero k
      simpa using hle hφ
    have := (Module.forall_dual_apply_eq_zero_iff ℂ _).mp hall
    simpa [sub_eq_zero] using congrArg Subtype.val this
  · have hsub : ((↑) ⁻¹' (E ∩ {z | (Λ z).1 ∈ complexCoordinatePlane (p + t) p}) : Set U) ⊆
        T₁ := by
      rintro y ⟨hyE, hyP⟩
      refine ⟨hyE, fun j => ?_⟩
      have := hyP (Fin.natAdd p j) (by simp)
      rw [hfst, hζ, Fin.append_right] at this
      rw [this, hξ₁a]
    have h := DimLE.anti hT₁a hsub hT₁dim
    rw [← dimLE_image_val_iff] at h
    rwa [himage _ inter_subset_left] at h
  · have hsub : ((↑) ⁻¹' (E ∩ {z | (Λ z).1 = (Λ a).1}) : Set U) ⊆ T₂ := by
      rintro y ⟨hyE, hya⟩
      refine ⟨⟨hyE, fun j => ?_⟩, fun k => ?_⟩
      · have := congrArg (fun w => w (Fin.natAdd p j)) hya
        simpa only [hfst, hζ, Fin.append_right] using this
      · have := congrArg (fun w => w (Fin.castAdd t k)) hya
        simpa only [hfst, hζ, Fin.append_left] using this
    have h := DimLE.anti hT₂a hsub hT₂dim
    rw [← dimLE_image_val_iff] at h
    rwa [himage _ inter_subset_left] at h

end Flat

end Hironaka.RemmertSteinCoordinates
