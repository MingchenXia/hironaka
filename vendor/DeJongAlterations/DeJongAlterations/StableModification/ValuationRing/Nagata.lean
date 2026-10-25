import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Flat modules of finite type over a valuation ring are finitely presented

Let `V` be a valuation ring (`[IsDomain V] [ValuationRing V]`), with maximal ideal `𝔪` and
residue field `k`. This file proves that finite generation implies finite presentation for
`V`-flat objects, the valuation-ring case of Raynaud–Gruson, *Critères de platitude et de
projectivité*, I 3.4.7, as used in Temkin, *Stable modification of relative curves*, J. Algebraic
Geom. 19 (2010), Lemma 3.5.1 (`valringlem`, `semi-stable.tex` lines 2578–2585), and deduces that
finitely presented `V`-algebras are coherent rings. Blueprint: `sm-nagata.tex`
(`thm:sm-nagata-fp`, `cor:sm-fp-coherent`).

## Main results

* `flat_iff_forall_smul_eq_zero`: a `V`-module is flat iff it is torsion-free (Temkin 3.5.1,
  first part).
* `fg_of_saturated_mvPolynomial`: for `σ, ι` finite, a `V[x_σ]`-submodule `N ⊆ V[x_σ]^ι` which is
  saturated (`c • f ∈ N`, `c ≠ 0` ⇒ `f ∈ N`) is finitely generated.
* `fg_of_saturated`: the same for `A^ι`, `A` a `V`-algebra of finite type.
* `finitePresentation_of_flat` (`thm:sm-nagata-fp`): if `A` is a `V`-algebra of finite type and
  `M` a finite `A`-module flat over `V`, then `M` is finitely presented over `A`.
* `finitePresentation_of_finiteType_of_flat`, `finitePresentation_iff_finiteType_of_flat`
  (Temkin 3.5.1): a flat `V`-algebra is finitely presented iff it is of finite type.
* `cor:sm-fp-coherent`, for `A` a finitely presented `V`-algebra:
  `fg_ker_of_finitePresentation` (kernels of maps `A^ι → A^κ` are finitely generated),
  `finitePresentation_of_fg_of_finitePresentation` (finitely generated submodules of finitely
  presented modules are finitely presented), `finitePresentation_of_fg_ideal` (`A` is coherent),
  `finitePresentation_ker_of_finitePresentation` (kernels of maps between finitely presented
  modules are finitely presented).

## Proof

The argument is not the dévissage of Raynaud–Gruson. A saturated submodule of a finite
`V`-module is finitely generated, because the quotient is finite and torsion-free, hence flat
and free (`fg_of_saturated_of_finite`). For a saturated `N ⊆ V[x_σ]^ι`, let `W d` be the
homogeneous vectors of degree `d` in `V[x₀, x_σ]^ι` whose dehomogenization (`x₀ ↦ 1`) lies in
`N`; every element of `N` is such a dehomogenization (`exists_isHomogeneous_dehomogenize_eq`).
The graded Nakayama lemma `exists_finset_forall_le_span_of_graded` shows that finitely many
elements generate all `W d`: their reductions modulo `𝔪` generate the reduction of `⋃ W d` over
the noetherian ring `k[x₀, x_σ]`, projecting to degree `d` and lifting coefficients shows
`W d ⊆ W'_d + 𝔪 • W d`, where the saturation and a common divisor of the coefficients
(`exists_smul_eq_of_coeff_mem_maximalIdeal`) handle the error term, and Nakayama's lemma
applies since `W d` is finitely generated. Coherence follows by lifting a map over `A = P ⧸ J`
to the polynomial ring `P` and writing preimages of finitely generated submodules as projections
of kernels (`comap_span_range_eq_map_ker`).
-/

noncomputable section

open MvPolynomial IsLocalRing
open scoped Pointwise

namespace DeJongAlterations.StableModification.ValuationRing

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]

section Flat

/-- Over a valuation ring, a module is flat if and only if it is torsion-free (Temkin, Lemma 3.5.1,
first part). -/
theorem flat_iff_forall_smul_eq_zero {M : Type*} [AddCommGroup M] [Module V M] :
    Module.Flat V M ↔ ∀ c : V, c ≠ 0 → ∀ x : M, c • x = 0 → x = 0 := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
  constructor
  · intro h c hc x hx
    have hx' : x ∈ Submodule.torsion V M :=
      (Submodule.mem_torsion_iff x).2 ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, hx⟩
    rw [h] at hx'
    exact (Submodule.mem_bot V).1 hx'
  · intro h
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    exact (Submodule.mem_bot V).2 (h a (nonZeroDivisors.ne_zero ha) x hax)

/-- A saturated submodule of a finitely generated module over a valuation ring is finitely
generated: the quotient is finitely generated and torsion-free, hence free. -/
theorem fg_of_saturated_of_finite {E : Type*} [AddCommGroup E] [Module V E] [Module.Finite V E]
    (L : Submodule V E) (hL : ∀ c : V, c ≠ 0 → ∀ x : E, c • x ∈ L → x ∈ L) : L.FG := by
  have hflat : Module.Flat V (E ⧸ L) := by
    rw [flat_iff_forall_smul_eq_zero]
    intro c hc x hx
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact hL c hc y hx
  have : Module.Free V (E ⧸ L) := Module.free_of_flat_of_isLocalRing
  have : Module.FinitePresentation V (E ⧸ L) := Module.finitePresentation_of_projective _ _
  have h := Module.FinitePresentation.fg_ker L.mkQ L.mkQ_surjective
  rwa [Submodule.ker_mkQ] at h

end Flat

section Content

variable {τ : Type*}

/-- If all coefficients of a vector of polynomials over a valuation ring lie in the maximal ideal,
the vector is a multiple of an element of the maximal ideal. -/
theorem exists_smul_eq_of_coeff_mem_maximalIdeal {ι : Type*} [Finite ι]
    (h : ι → MvPolynomial τ V) (hh : ∀ j α, coeff α (h j) ∈ maximalIdeal V) :
    ∃ c ∈ maximalIdeal V, ∃ h' : ι → MvPolynomial τ V, h = c • h' := by
  classical
  have := Fintype.ofFinite ι
  let S : Finset V := Finset.univ.biUnion fun j => (h j).support.image fun α => coeff α (h j)
  obtain ⟨c, hc⟩ := (IsBezout.isPrincipal_of_FG (Ideal.span (S : Set V)) ⟨S, rfl⟩).principal
  have hS : ∀ j α, coeff α (h j) ∈ Ideal.span (S : Set V) := by
    intro j α
    by_cases hα : α ∈ (h j).support
    · apply Ideal.subset_span
      simp only [S, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
        Finset.coe_image, Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
      exact ⟨j, α, hα, rfl⟩
    · rw [MvPolynomial.notMem_support_iff.1 hα]
      exact zero_mem _
  have hcm : c ∈ maximalIdeal V := by
    have hle : Ideal.span (S : Set V) ≤ maximalIdeal V := by
      rw [Ideal.span_le]
      intro a ha
      simp only [S, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
        Finset.coe_image, Set.mem_iUnion, Set.mem_image, Finset.mem_coe] at ha
      obtain ⟨j, α, -, rfl⟩ := ha
      exact hh j α
    apply hle
    rw [hc]
    exact Submodule.mem_span_singleton_self c
  have hdvd : ∀ j, C c ∣ h j := by
    intro j
    rw [C_dvd_iff_dvd_coeff]
    intro α
    have := hS j α
    rw [hc] at this
    exact Ideal.mem_span_singleton.1 this
  choose h' hh' using hdvd
  refine ⟨c, hcm, h', funext fun j => ?_⟩
  rw [Pi.smul_apply, smul_eq_C_mul]
  exact hh' j

omit [ValuationRing V] in
/-- Cancelling a nonzero scalar preserves homogeneity. -/
theorem isHomogeneous_of_smul {c : V} (hc : c ≠ 0) {p : MvPolynomial τ V} {d : ℕ}
    (hp : (c • p).IsHomogeneous d) : p.IsHomogeneous d := by
  intro α hα
  apply hp
  rw [coeff_smul, smul_eq_mul]
  exact mul_ne_zero hc hα

end Content

section Graded

variable {τ ι : Type*} [Finite τ] [Finite ι]

/-- A saturated submodule of the homogeneous vectors of degree `d` is finitely generated over
`V`. -/
theorem fg_of_saturated_homogeneous (W : Submodule V (ι → MvPolynomial τ V)) (d : ℕ)
    (hW_hom : ∀ F ∈ W, ∀ j, (F j).IsHomogeneous d)
    (hW_sat : ∀ c : V, c ≠ 0 → ∀ F : ι → MvPolynomial τ V,
      (∀ j, (F j).IsHomogeneous d) → c • F ∈ W → F ∈ W) :
    W.FG := by
  let Φ : (ι → homogeneousSubmodule τ V d) →ₗ[V] (ι → MvPolynomial τ V) :=
    (homogeneousSubmodule τ V d).subtype.compLeft ι
  have : Module.Finite V (homogeneousSubmodule τ V d) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg τ V d)
  have hfg : (W.comap Φ).FG := by
    refine fg_of_saturated_of_finite _ fun c hc x hx => ?_
    rw [Submodule.mem_comap, map_smul] at hx
    rw [Submodule.mem_comap]
    exact hW_sat c hc (Φ x) (fun j => (x j).2) hx
  have hW : W = (W.comap Φ).map Φ := by
    rw [Submodule.map_comap_eq, eq_comm, inf_eq_right]
    intro F hF
    exact ⟨fun j => ⟨F j, hW_hom F hF j⟩, rfl⟩
  rw [hW]
  exact hfg.map Φ

/-- **Graded Nakayama lemma over a valuation ring.** Let `W d` be `V`-submodules of the
homogeneous vectors of degree `d` in `(V[x_τ])^ι`, saturated and stable under multiplication by
monomials (raising the degree). Then finitely many elements of `⋃ W d` generate all `W d` over
`V[x_τ]`. The elements of the finite set are recorded together with a degree. -/
theorem exists_finset_forall_le_span_of_graded (W : ℕ → Submodule V (ι → MvPolynomial τ V))
    (hW_hom : ∀ d, ∀ F ∈ W d, ∀ j, (F j).IsHomogeneous d)
    (hW_sat : ∀ d (c : V), c ≠ 0 → ∀ F : ι → MvPolynomial τ V,
      (∀ j, (F j).IsHomogeneous d) → c • F ∈ W d → F ∈ W d)
    (hW_mul : ∀ d (α : τ →₀ ℕ), ∀ F ∈ W d, (monomial α (1 : V)) • F ∈ W (d + α.degree)) :
    ∃ G : Finset (ℕ × (ι → MvPolynomial τ V)), (∀ g ∈ G, g.2 ∈ W g.1) ∧
      ∀ d, (W d : Set (ι → MvPolynomial τ V)) ⊆
        Submodule.span (MvPolynomial τ V) (Prod.snd '' (G : Set (ℕ × (ι → MvPolynomial τ V)))) := by
  classical
  let k := ResidueField V
  let ρ : MvPolynomial τ V →ₐ[V] MvPolynomial τ k := MvPolynomial.mapAlgHom (Algebra.ofId V k)
  let Φ : (ι → MvPolynomial τ V) →ₗ[V] (ι → MvPolynomial τ k) := ρ.toLinearMap.compLeft ι
  have hΦ : ∀ F j, Φ F j = map (algebraMap V k) (F j) := fun F j => by
    simp [Φ, ρ, mapAlgHom_apply]
  let U : Set (ℕ × (ι → MvPolynomial τ V)) := {g | g.2 ∈ W g.1}
  let ΦU : ℕ × (ι → MvPolynomial τ V) → (ι → MvPolynomial τ k) := fun g => Φ g.2
  have hfg : (Submodule.span (MvPolynomial τ k) (ΦU '' U)).FG := IsNoetherian.noetherian _
  obtain ⟨s', hs'U, hs'⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  obtain ⟨G, hGU, rfl⟩ := Finset.subset_set_image_iff.1 hs'U
  refine ⟨G, fun g hg => hGU hg, fun d => ?_⟩
  let T : Set (ι → MvPolynomial τ V) :=
    {x | ∃ g ∈ G, ∃ α : τ →₀ ℕ, g.1 + α.degree = d ∧ x = monomial α (1 : V) • g.2}
  have hTW : T ⊆ W d := by
    rintro x ⟨g, hg, α, hdeg, rfl⟩
    rw [← hdeg]
    exact hW_mul g.1 α g.2 (hGU hg)
  have hTspan : T ⊆ (Submodule.span (MvPolynomial τ V)
      (Prod.snd '' (G : Set (ℕ × (ι → MvPolynomial τ V)))) : Set (ι → MvPolynomial τ V)) := by
    rintro x ⟨g, hg, α, -, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)
  have hfgW : (W d).FG := fg_of_saturated_homogeneous (W d) d (hW_hom d) (hW_sat d)
  have hle : W d ≤ Submodule.span V T := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfgW (maximalIdeal_le_jacobson _) ?_
    intro F hF
    -- the reduction of `F` lies in the span of the reductions of `G`
    have h1 : Φ F ∈
        Submodule.span (MvPolynomial τ k) (ΦU '' (G : Set (ℕ × (ι → MvPolynomial τ V)))) := by
      rw [← Finset.coe_image, ← hs']
      exact Submodule.subset_span ⟨(d, F), hF, rfl⟩
    have hmon : Submodule.span k (Set.range fun α : τ →₀ ℕ => monomial α (1 : k)) = ⊤ := by
      rw [← coe_basisMonomials]
      exact (basisMonomials τ k).span_eq
    have h2 : Φ F ∈ Submodule.span k
        ((Set.range fun α : τ →₀ ℕ => monomial α (1 : k)) •
          (ΦU '' (G : Set (ℕ × (ι → MvPolynomial τ V))))) := by
      rw [Submodule.span_smul_of_span_eq_top hmon]
      exact h1
    -- projecting to degree `d`
    let πd : (ι → MvPolynomial τ k) →ₗ[k] (ι → MvPolynomial τ k) :=
      (homogeneousComponent d).compLeft ι
    have hπd : ∀ x j, πd x j = homogeneousComponent d (x j) := fun _ _ => rfl
    have hπF : πd (Φ F) = Φ F := by
      funext j
      rw [hπd, hΦ]
      exact homogeneousComponent_eq_self ((hW_hom d F hF j).map _)
    have h3 : Φ F ∈ Submodule.span k (Φ '' T) := by
      rw [← hπF]
      have h2' := Submodule.mem_map_of_mem (f := πd) h2
      rw [Submodule.map_span] at h2'
      refine Submodule.span_le.2 ?_ h2'
      rintro _ ⟨_, ⟨_, ⟨α, rfl⟩, _, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
      have hmul : (monomial α (1 : k)) • ΦU g = Φ (monomial α (1 : V) • g.2) := by
        funext j
        simp only [ΦU, Pi.smul_apply, smul_eq_mul, hΦ, map_mul, map_monomial, map_one]
      have hhom : ∀ j, (Φ (monomial α (1 : V) • g.2) j).IsHomogeneous (g.1 + α.degree) :=
        fun j => by
          rw [hΦ]
          exact (hW_hom _ _ (hW_mul g.1 α g.2 (hGU hg)) j).map _
      change πd ((monomial α (1 : k)) • ΦU g) ∈ _
      rw [hmul]
      by_cases hd : g.1 + α.degree = d
      · have hπ : πd (Φ (monomial α (1 : V) • g.2)) = Φ (monomial α (1 : V) • g.2) := by
          funext j
          rw [hπd, ← hd]
          exact homogeneousComponent_eq_self (hhom j)
        rw [SetLike.mem_coe, hπ]
        exact Submodule.subset_span ⟨_, ⟨g, hg, α, hd, rfl⟩, rfl⟩
      · have hπ : πd (Φ (monomial α (1 : V) • g.2)) = 0 := by
          funext j
          rw [hπd, homogeneousComponent_of_mem (hhom j), if_neg (Ne.symm hd)]
          rfl
        rw [SetLike.mem_coe, hπ]
        exact zero_mem _
    -- lifting the coefficients to `V`
    have hsurj : Function.Surjective (algebraMap V k) := by
      rw [ResidueField.algebraMap_eq]
      exact residue_surjective
    have h4 : Φ F ∈ (Submodule.span V T).map Φ := by
      rw [Submodule.map_span, ← Submodule.restrictScalars_span V k hsurj]
      exact h3
    obtain ⟨w, hw, hwF⟩ := h4
    have hwW : w ∈ W d := Submodule.span_le.2 hTW hw
    -- the difference has all its coefficients in the maximal ideal
    have hhW : F - w ∈ W d := sub_mem hF hwW
    have hcoeff : ∀ j α, coeff α ((F - w) j) ∈ maximalIdeal V := by
      intro j α
      have hΦh : Φ (F - w) = 0 := by rw [map_sub, hwF, sub_self]
      have h5 : map (algebraMap V k) ((F - w) j) = 0 := by
        rw [← hΦ, hΦh]
        rfl
      have h6 := congrArg (coeff α) h5
      rw [coeff_map, coeff_zero, ResidueField.algebraMap_eq] at h6
      exact (residue_eq_zero_iff _).1 h6
    obtain ⟨c, hcm, h', hh'⟩ := exists_smul_eq_of_coeff_mem_maximalIdeal (F - w) hcoeff
    have hhm : F - w ∈ maximalIdeal V • W d := by
      by_cases hc0 : c = 0
      · rw [hh', hc0, zero_smul]
        exact zero_mem _
      · have hh'hom : ∀ j, (h' j).IsHomogeneous d := fun j =>
          isHomogeneous_of_smul hc0 (by rw [← Pi.smul_apply, ← hh']; exact hW_hom d _ hhW j)
        have hh'W : h' ∈ W d := hW_sat d c hc0 h' hh'hom (by rw [← hh']; exact hhW)
        rw [hh']
        exact Submodule.smul_mem_smul hcm hh'W
    have hF' : F = w + (F - w) := by abel
    rw [hF']
    exact Submodule.add_mem_sup hw hhm
  intro F hF
  exact (Submodule.span_le.2 hTspan :
    Submodule.span V T ≤ (Submodule.span (MvPolynomial τ V) _).restrictScalars V) (hle hF)

end Graded

section Homogenize

variable {σ : Type*}

omit [IsDomain V] [ValuationRing V] in
/-- The sum of the homogeneous components of degree at most `d ≥ deg φ` is `φ`. -/
theorem sum_homogeneousComponent_of_le {φ : MvPolynomial σ V} {d : ℕ} (hd : φ.totalDegree ≤ d) :
    ∑ e ∈ Finset.range (d + 1), homogeneousComponent e φ = φ := by
  conv_rhs => rw [← sum_homogeneousComponent φ]
  symm
  apply Finset.sum_subset
  · intro e he
    simp only [Finset.mem_range] at he ⊢
    omega
  · intro e _ he
    simp only [Finset.mem_range, not_lt] at he
    exact homogeneousComponent_eq_zero e φ (by omega)

variable (V σ) in
/-- The dehomogenization `V[x₀, x_σ] → V[x_σ]`, `x₀ ↦ 1`, `x_i ↦ x_i`; the variable `x₀` is
`none : Option σ`. -/
def dehomogenize : MvPolynomial (Option σ) V →ₐ[V] MvPolynomial σ V :=
  aeval fun o => o.elim 1 X

omit [IsDomain V] [ValuationRing V] in
/-- `dehomogenize` sends the homogenizing variable to `1`. -/
@[simp]
theorem dehomogenize_X_none : dehomogenize V σ (X none) = 1 := by
  simp [dehomogenize]

omit [IsDomain V] [ValuationRing V] in
/-- `dehomogenize` is the identity on polynomials not involving the homogenizing variable. -/
@[simp]
theorem dehomogenize_rename_some (p : MvPolynomial σ V) :
    dehomogenize V σ (rename some p) = p := by
  rw [dehomogenize, aeval_rename]
  have : ((fun o : Option σ => o.elim (1 : MvPolynomial σ V) X) ∘ some) = X := rfl
  rw [this, aeval_X_left, AlgHom.id_apply]

omit [IsDomain V] [ValuationRing V] in
/-- **Homogenization.** Every vector of polynomials is the dehomogenization of a vector of
homogeneous polynomials of a common degree. -/
theorem exists_isHomogeneous_dehomogenize_eq {ι : Type*} [Finite ι] (f : ι → MvPolynomial σ V) :
    ∃ d, ∃ F : ι → MvPolynomial (Option σ) V,
      (∀ j, (F j).IsHomogeneous d) ∧ ∀ j, dehomogenize V σ (F j) = f j := by
  classical
  have := Fintype.ofFinite ι
  let d := Finset.univ.sup fun j => (f j).totalDegree
  refine ⟨d, fun j => ∑ e ∈ Finset.range (d + 1),
    X none ^ (d - e) * rename some (homogeneousComponent e (f j)), fun j => ?_, fun j => ?_⟩
  · apply IsHomogeneous.sum
    intro e he
    have he' : e ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 he)
    have h := (isHomogeneous_X_pow (R := V) (none : Option σ) (d - e)).mul
      ((homogeneousComponent_isHomogeneous e (f j)).rename_isHomogeneous (f := some))
    rwa [Nat.sub_add_cancel he'] at h
  · simp only [map_sum, map_mul, map_pow, dehomogenize_X_none, one_pow, one_mul,
      dehomogenize_rename_some]
    exact sum_homogeneousComponent_of_le
      (Finset.le_sup (f := fun j => (f j).totalDegree) (Finset.mem_univ j))

end Homogenize

section Polynomial

variable {σ ι : Type*} [Finite σ] [Finite ι]

/-- Saturated submodules of finite free modules over a polynomial ring in finitely many variables
over a valuation ring are finitely generated. -/
theorem fg_of_saturated_mvPolynomial (N : Submodule (MvPolynomial σ V) (ι → MvPolynomial σ V))
    (hN : ∀ c : V, c ≠ 0 → ∀ f : ι → MvPolynomial σ V, c • f ∈ N → f ∈ N) : N.FG := by
  classical
  let D : (ι → MvPolynomial (Option σ) V) →ₗ[V] (ι → MvPolynomial σ V) :=
    (dehomogenize V σ).toLinearMap.compLeft ι
  have hD : ∀ F j, D F j = dehomogenize V σ (F j) := fun _ _ => rfl
  have hDsmul : ∀ (r : MvPolynomial (Option σ) V) F, D (r • F) = dehomogenize V σ r • D F := by
    intro r F
    funext j
    simp [hD, map_mul]
  let W : ℕ → Submodule V (ι → MvPolynomial (Option σ) V) := fun d =>
    { carrier := {F | (∀ j, (F j).IsHomogeneous d) ∧ D F ∈ N}
      add_mem' := fun {F G} hF hG => ⟨fun j => (hF.1 j).add (hG.1 j), by
        rw [map_add]; exact N.add_mem hF.2 hG.2⟩
      zero_mem' := ⟨fun j => isHomogeneous_zero _ _ _, by rw [map_zero]; exact N.zero_mem⟩
      smul_mem' := fun c F hF => ⟨fun j => by
        rw [Pi.smul_apply, smul_eq_C_mul]; exact (hF.1 j).C_mul c, by
        rw [map_smul]; exact N.smul_of_tower_mem c hF.2⟩ }
  have hW : ∀ d F, F ∈ W d ↔ (∀ j, (F j).IsHomogeneous d) ∧ D F ∈ N := fun _ _ => Iff.rfl
  obtain ⟨G, hGW, hG⟩ := exists_finset_forall_le_span_of_graded W
    (fun d F hF => ((hW d F).1 hF).1)
    (fun d c hc F hFh hcF => (hW d F).2 ⟨hFh, hN c hc _ (by
      rw [← map_smul]; exact ((hW d _).1 hcF).2)⟩)
    (fun d α F hF => (hW _ _).2 ⟨fun j => by
        rw [Pi.smul_apply, smul_eq_mul, add_comm]
        exact (isHomogeneous_monomial 1 rfl).mul (((hW d F).1 hF).1 j), by
      rw [hDsmul]; exact N.smul_mem _ ((hW d F).1 hF).2⟩)
  refine ⟨(G.image Prod.snd).image D, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨_, ⟨g, hg, rfl⟩, rfl⟩ := hx
    exact ((hW _ _).1 (hGW g hg)).2
  · intro f hf
    obtain ⟨d, F, hFh, hFf⟩ := exists_isHomogeneous_dehomogenize_eq f
    have hDF : D F = f := by
      funext j
      rw [hD]
      exact hFf j
    have hFW : F ∈ W d := (hW d F).2 ⟨hFh, by rw [hDF]; exact hf⟩
    have hspan := hG d hFW
    rw [← hDF]
    refine Submodule.span_induction (p := fun x _ => D x ∈ Submodule.span (MvPolynomial σ V)
      (((G.image Prod.snd).image D : Finset _) : Set (ι → MvPolynomial σ V))) ?_ ?_ ?_ ?_ hspan
    · rintro x ⟨g, hg, rfl⟩
      apply Submodule.subset_span
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨g.2, ⟨g, hg, rfl⟩, rfl⟩
    · rw [map_zero]
      exact zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro r x _ hx
      rw [hDsmul]
      exact Submodule.smul_mem _ _ hx

end Polynomial

section PiMap

variable {R S : Type*} [Semiring R] [Semiring S]

/-- Coordinatewise application of a ring homomorphism to vectors, as a semilinear map. -/
def piMapₛₗ (f : R →+* S) (ι : Type*) : (ι → R) →ₛₗ[f] (ι → S) where
  toFun F j := f (F j)
  map_add' _ _ := funext fun _ => map_add f _ _
  map_smul' _ _ := funext fun _ => map_mul f _ _

/-- Coordinates of `piMapₛₗ f ι F`. -/
@[simp]
theorem piMapₛₗ_apply (f : R →+* S) {ι : Type*} (F : ι → R) (j : ι) :
    piMapₛₗ f ι F j = f (F j) := rfl

/-- Coordinatewise application of a surjective ring homomorphism is surjective. -/
theorem piMapₛₗ_surjective {f : R →+* S} (hf : Function.Surjective f) (ι : Type*) :
    Function.Surjective (piMapₛₗ f ι) := fun x =>
  ⟨fun j => Function.surjInv hf (x j), funext fun j => Function.surjInv_eq hf (x j)⟩

end PiMap

section FiniteType

variable {A : Type*} [CommRing A] [Algebra V A]

/-- **Saturated submodules over algebras of finite type.** If `A` is a `V`-algebra of finite type,
then every `A`-submodule of `A^ι` (`ι` finite) which is saturated for the scalars of `V` is
finitely generated. -/
theorem fg_of_saturated [Algebra.FiniteType V A] {ι : Type*} [Finite ι]
    (N : Submodule A (ι → A)) (hN : ∀ c : V, c ≠ 0 → ∀ f : ι → A, c • f ∈ N → f ∈ N) : N.FG := by
  obtain ⟨n, π, hπ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := V)).1 ‹_›
  let πr : MvPolynomial (Fin n) V →+* A := π.toRingHom
  have hπr : Function.Surjective πr := hπ
  have : RingHomSurjective πr := ⟨hπr⟩
  let Pr := piMapₛₗ πr ι
  have hfg := fg_of_saturated_mvPolynomial (N.comap Pr) fun c hc F hF => by
    rw [Submodule.mem_comap] at hF ⊢
    have h : Pr (c • F) = c • Pr F := funext fun j => by
      change π (c • F j) = c • π (F j)
      exact map_smul π c (F j)
    rw [h] at hF
    exact hN c hc _ hF
  rw [← Submodule.map_comap_eq_of_surjective (piMapₛₗ_surjective hπr ι) N]
  exact hfg.map Pr

variable (V) in
/-- **Flat modules of finite type are finitely presented** (Raynaud–Gruson I 3.4.7 for valuation
rings; cited in Temkin, Lemma 3.5.1). If `A` is a `V`-algebra of finite type and `M` is a finite
`A`-module which is flat over `V`, then `M` is finitely presented over `A`. -/
theorem finitePresentation_of_flat [Algebra.FiniteType V A] {M : Type*} [AddCommGroup M]
    [Module A M] [Module V M] [IsScalarTower V A M] [Module.Finite A M] [Module.Flat V M] :
    Module.FinitePresentation A M := by
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' A M
  refine Module.finitePresentation_of_surjective φ hφ
    (fg_of_saturated (V := V) _ fun c hc x hx => ?_)
  rw [LinearMap.mem_ker, LinearMap.map_smul_of_tower] at hx
  rw [LinearMap.mem_ker]
  exact flat_iff_forall_smul_eq_zero.1 ‹_› c hc _ hx

/-- **Temkin, Lemma 3.5.1.** A flat `V`-algebra of finite type is finitely presented. -/
theorem finitePresentation_of_finiteType_of_flat [Algebra.FiniteType V A] [Module.Flat V A] :
    Algebra.FinitePresentation V A := by
  obtain ⟨n, π, hπ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := V)).1 ‹_›
  refine ⟨n, π, hπ, ?_⟩
  let P := MvPolynomial (Fin n) V
  let e : (Unit → P) ≃ₗ[P] P := LinearEquiv.funUnique Unit P P
  have hfg := fg_of_saturated_mvPolynomial
    (Submodule.comap e.toLinearMap (RingHom.ker π.toRingHom)) fun c hc f hf => by
      have key : ∀ g : Unit → P,
          g ∈ Submodule.comap e.toLinearMap (RingHom.ker π.toRingHom) ↔ π (e.toLinearMap g) = 0 :=
        fun g => Iff.rfl
      rw [key, LinearMap.map_smul_of_tower, map_smul] at hf
      rw [key]
      exact flat_iff_forall_smul_eq_zero.1 ‹_› c hc _ hf
  have h := hfg.map e.toLinearMap
  rwa [Submodule.map_comap_eq_of_surjective e.surjective] at h

/-- A flat `V`-algebra is finitely presented if and only if it is of finite type
(Temkin, Lemma 3.5.1). -/
theorem finitePresentation_iff_finiteType_of_flat [Module.Flat V A] :
    Algebra.FinitePresentation V A ↔ Algebra.FiniteType V A :=
  ⟨fun _ => inferInstance, fun _ => finitePresentation_of_finiteType_of_flat⟩

end FiniteType

section Comap

omit [IsDomain V] [ValuationRing V]

/-- The preimage of the submodule generated by `ℓ₁, …, ℓₘ` under `u : B^ι → B^κ` is the
projection of the kernel of `(x, b) ↦ u x - ∑ₜ bₜ ℓₜ`. -/
theorem comap_span_range_eq_map_ker {B : Type*} [CommRing B] {ι κ : Type*} {m : ℕ}
    (u : (ι → B) →ₗ[B] (κ → B)) (ℓ : Fin m → (κ → B)) :
    (Submodule.span B (Set.range ℓ)).comap u =
      (LinearMap.ker (u ∘ₗ LinearMap.funLeft B B Sum.inl -
        Fintype.linearCombination B ℓ ∘ₗ LinearMap.funLeft B B Sum.inr)).map
        (LinearMap.funLeft B B (Sum.inl : ι → ι ⊕ Fin m)) := by
  ext x
  simp only [Submodule.mem_comap, Submodule.mem_map, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.comp_apply, sub_eq_zero]
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hx
    exact ⟨Sum.elim x b, hb.symm, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    rw [hG, Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

end Comap

section Coherent

/-- Over a polynomial ring in finitely many variables over a valuation ring, kernels of linear
maps between finite free modules are finitely generated. -/
theorem fg_ker_mvPolynomial {σ ι κ : Type*} [Finite σ] [Finite ι]
    (u : (ι → MvPolynomial σ V) →ₗ[MvPolynomial σ V] (κ → MvPolynomial σ V)) :
    (LinearMap.ker u).FG := by
  refine fg_of_saturated_mvPolynomial _ fun c hc x hx => ?_
  rw [LinearMap.mem_ker, LinearMap.map_smul_of_tower] at hx
  rw [LinearMap.mem_ker]
  funext j
  have h := congrFun hx j
  rw [Pi.smul_apply, smul_eq_C_mul, Pi.zero_apply, mul_eq_zero] at h
  exact h.resolve_left (by rwa [C_eq_zero])

/-- Over a polynomial ring in finitely many variables over a valuation ring, preimages of finitely
generated submodules under linear maps between finite free modules are finitely generated. -/
theorem fg_comap_mvPolynomial {σ ι κ : Type*} [Finite σ] [Finite ι]
    (u : (ι → MvPolynomial σ V) →ₗ[MvPolynomial σ V] (κ → MvPolynomial σ V))
    {K : Submodule (MvPolynomial σ V) (κ → MvPolynomial σ V)} (hK : K.FG) :
    (K.comap u).FG := by
  obtain ⟨m, ℓ, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hK
  rw [comap_span_range_eq_map_ker]
  exact (fg_ker_mvPolynomial _).map _

variable (V) {A : Type*} [CommRing A] [Algebra V A] [Algebra.FinitePresentation V A]
include V

/-- **Coherence, first form.** If `A` is a finitely presented `V`-algebra, kernels of `A`-linear
maps between finite free `A`-modules are finitely generated. -/
theorem fg_ker_of_finitePresentation {ι κ : Type*} [Finite ι] [Finite κ]
    (u : (ι → A) →ₗ[A] (κ → A)) : (LinearMap.ker u).FG := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  obtain ⟨n, π, hπ, hJ⟩ := ‹Algebra.FinitePresentation V A›.out
  let P := MvPolynomial (Fin n) V
  let πr : P →+* A := π.toRingHom
  have hπr : Function.Surjective πr := hπ
  have : RingHomSurjective πr := ⟨hπr⟩
  -- lift the matrix of `u` to `P`
  let U := LinearMap.toMatrix' u
  let U' : Matrix κ ι P := fun l i => Function.surjInv hπr (U l i)
  let u' : (ι → P) →ₗ[P] (κ → P) := U'.mulVecLin
  have hU' : U'.map πr = U := by
    ext l i
    exact Function.surjInv_eq hπr (U l i)
  have key : ∀ F, piMapₛₗ πr κ (u' F) = u (piMapₛₗ πr ι F) := by
    intro F
    funext l
    rw [piMapₛₗ_apply, Matrix.mulVecLin_apply, RingHom.map_mulVec, hU',
      ← LinearMap.toMatrix'_mulVec]
    rfl
  -- the kernel of `P^κ → A^κ` is finitely generated
  have hker : (LinearMap.ker (piMapₛₗ πr κ)).FG := by
    have heq : LinearMap.ker (piMapₛₗ πr κ) =
        ⨆ l : κ, Submodule.map (LinearMap.single P (fun _ : κ => P) l) (RingHom.ker πr) := by
      apply le_antisymm
      · intro G hG
        rw [LinearMap.mem_ker] at hG
        rw [← Finset.univ_sum_single G]
        refine Submodule.sum_mem _ fun l _ => Submodule.mem_iSup_of_mem l ⟨G l, ?_, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker]
        have := congrFun hG l
        rwa [piMapₛₗ_apply] at this
      · refine iSup_le fun l => ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [LinearMap.mem_ker]
        funext l'
        rw [piMapₛₗ_apply, LinearMap.coe_single]
        by_cases hl : l' = l
        · subst hl
          rw [Pi.single_eq_same]
          exact ha
        · rw [Pi.single_eq_of_ne hl, map_zero]
          rfl
    rw [heq]
    exact Submodule.fg_iSup _ fun l => Submodule.FG.map _ hJ
  have heq : LinearMap.ker u = ((LinearMap.ker (piMapₛₗ πr κ)).comap u').map (piMapₛₗ πr ι) := by
    ext x
    constructor
    · intro hx
      obtain ⟨F, rfl⟩ := piMapₛₗ_surjective hπr ι x
      refine ⟨F, ?_, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mem_ker, key]
      exact hx
    · rintro ⟨F, hF, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mem_ker, key] at hF
      exact hF
  rw [heq]
  exact (fg_comap_mvPolynomial u' hker).map _

/-- Over a finitely presented `V`-algebra, preimages of finitely generated submodules under linear
maps between finite free modules are finitely generated. -/
theorem fg_comap_of_finitePresentation {ι κ : Type*} [Finite ι] [Finite κ]
    (u : (ι → A) →ₗ[A] (κ → A)) {K : Submodule A (κ → A)} (hK : K.FG) : (K.comap u).FG := by
  obtain ⟨m, ℓ, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hK
  rw [comap_span_range_eq_map_ker]
  exact (fg_ker_of_finitePresentation (V := V) _).map _

/-- **Coherence.** Over a finitely presented `V`-algebra, every finitely generated submodule of a
finitely presented module is finitely presented. -/
theorem finitePresentation_of_fg_of_finitePresentation {M : Type*} [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] (L : Submodule A M) (hL : L.FG) :
    Module.FinitePresentation A L := by
  have : Module.Finite A L := Module.Finite.iff_fg.2 hL
  obtain ⟨r, g, hg⟩ := Module.Finite.exists_fin' A L
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' A M
  have hφker : (LinearMap.ker φ).FG := Module.FinitePresentation.fg_ker φ hφ
  obtain ⟨h, hh⟩ := Module.projective_lifting_property φ (L.subtype ∘ₗ g) hφ
  refine Module.finitePresentation_of_surjective g hg ?_
  have heq : LinearMap.ker g = (LinearMap.ker φ).comap h := by
    ext x
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker, ← LinearMap.comp_apply, hh,
      LinearMap.comp_apply, Submodule.subtype_apply, ZeroMemClass.coe_eq_zero]
  rw [heq]
  exact fg_comap_of_finitePresentation (V := V) h hφker

/-- **Finitely presented `V`-algebras are coherent:** every finitely generated ideal is finitely
presented. -/
theorem finitePresentation_of_fg_ideal (I : Ideal A) (hI : I.FG) :
    Module.FinitePresentation A I :=
  finitePresentation_of_fg_of_finitePresentation (V := V) I hI

/-- Over a finitely presented `V`-algebra, the kernel of a linear map between finitely presented
modules is finitely presented. -/
theorem finitePresentation_ker_of_finitePresentation {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.FinitePresentation A M] [Module.FinitePresentation A N]
    (u : M →ₗ[A] N) : Module.FinitePresentation A (LinearMap.ker u) := by
  have : Module.FinitePresentation A (LinearMap.range u) :=
    finitePresentation_of_fg_of_finitePresentation (V := V) _ (Submodule.fg_range u)
  have h := Module.FinitePresentation.fg_ker u.rangeRestrict u.surjective_rangeRestrict
  rw [LinearMap.ker_rangeRestrict] at h
  exact finitePresentation_of_fg_of_finitePresentation (V := V) _ h

end Coherent

end DeJongAlterations.StableModification.ValuationRing
