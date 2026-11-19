import Hironaka.Analytic.GAGA.CoreGermModule
import Hironaka.Coherence.OkaCoherence

/-!
# Oka's coherence theorem for modules

Source: Oka's coherence theorem and its consequences for coherent subsheaves of `𝒪^p`
(Grauert--Remmert, *Coherent analytic sheaves*, Ch. 2 §§4--5; Demailly, *Complex analytic and
differential geometry*, II.3.15--3.20). Infrastructure of lane SERRE-CORE (Serre's GAGA,
towards source `lma:GAGA`).

On a complex normed space `X` with Oka's property (`OkaProperty X`: relation sheaves of finite
matrices of holomorphic functions are locally finitely generated; TN proves it for `ℂⁿ`,
`OkaCoherence.okaProperty_euclidean`, and `okaProperty_of_finiteDimensional` below transports
it to every finite-dimensional space), the coherent subsheaves of `𝒪^ι` are stable under

* preimages `comap A N = {a : A a ∈ N}` under holomorphic matrices `A`
  (`CoherentAt.comap`; the generators are the `a`-parts of generators of the relations of the
  system `(A | -τ)`, `τ` generators of `N`);
* intersections (`CoherentAt.inf`, from `comap` and `map`);
* kernels of holomorphic matrices (`CoherentAt.ker`) and modules of relations among finitely
  many sections (`CoherentAt.relations`, Oka's theorem itself).

Together with sums and images (`CoreGermModule`) this is the statement that kernels, images,
cokernels, sums and intersections of coherent subsheaves of free modules are coherent.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Filter Topology Set
open Hironaka.OkaRelationSheaf

namespace Hironaka.Analytic.GAGA.Core

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **Oka's theorem on every finite-dimensional complex normed space**, transported from
`ℂⁿ = EuclideanSpace ℂ (Fin n)` (TN `okaProperty_euclidean`) along a linear isomorphism. -/
theorem okaProperty_of_finiteDimensional (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [FiniteDimensional ℂ X] : OkaProperty X := by
  let e : X ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ X)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  exact OkaProperty.of_homeomorph e.toHomeomorph (fun _ => e.differentiableAt)
    (fun _ => e.symm.differentiableAt)
    (Hironaka.OkaCoherence.okaProperty_euclidean _)

namespace GermModule

variable {ι κ μ ν : Type} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]

/-- The preimage `A⁻¹(N) = {a ∈ 𝒪^ι : A a ∈ N}` of `N ⊆ 𝒪^κ` under `A : 𝒪^ι → 𝒪^κ`. -/
def comap (A : κ → ι → X → ℂ) (N : GermModule X κ) : GermModule X ι :=
  ⟨fun y a => HolTupleAt a y ∧ N.mem y (matApply A a)⟩

/-- The intersection of two subsheaves of `𝒪^ι`. -/
def inf (M N : GermModule X ι) : GermModule X ι :=
  ⟨fun y a => M.mem y a ∧ N.mem y a⟩

/-- The kernel of a matrix `A : 𝒪^ι → 𝒪^κ`. -/
def ker (A : κ → ι → X → ℂ) : GermModule X ι :=
  comap A (bot X κ)

/-- The module of relations `{c ∈ 𝒪^μ : ∑ c_k σ_k = 0}` among finitely many tuples. -/
def relations (σ : μ → ι → X → ℂ) : GermModule X μ :=
  ker (colMatrix σ)

theorem mem_ker_iff {A : κ → ι → X → ℂ} {y : X} {a : ι → X → ℂ} :
    (ker A).mem y a ↔ HolTupleAt a y ∧ ∀ i, matApply A a i =ᶠ[𝓝 y] fun _ => 0 :=
  Iff.rfl

theorem mem_relations_iff {σ : μ → ι → X → ℂ} {y : X} {c : μ → X → ℂ} :
    (relations σ).mem y c ↔
      HolTupleAt c y ∧ ∀ j, (fun x => ∑ k, c k x * σ k j x) =ᶠ[𝓝 y] fun _ => 0 := by
  have h : ∀ j, matApply (colMatrix σ) c j = fun x => ∑ k, c k x * σ k j x :=
    fun j => funext (matApply_colMatrix σ c j)
  simp only [relations, mem_ker_iff, h]

/-- **Oka's theorem for preimages.** If `N ⊆ 𝒪^κ` is coherent at `x₀` and `A` is holomorphic
at `x₀`, then `A⁻¹(N)` is coherent at `x₀`. -/
theorem CoherentAt.comap (hX : OkaProperty X) {N : GermModule X κ} {x₀ : X}
    (hN : N.CoherentAt x₀) {A : κ → ι → X → ℂ} (hA : ∀ i j, HolAt (A i j) x₀) :
    (N.comap A).CoherentAt x₀ := by
  classical
  obtain ⟨U, hU, hx₀U, ν', _, τ, hτ⟩ := hN
  let F : κ → (ι ⊕ ν') → X → ℂ := fun i =>
    Sum.elim (fun j => A i j) (fun l x => -τ l i x)
  have hF : ∀ i j, HolAt (F i j) x₀ := by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr l => exact (hτ.holAt hU hx₀U l i).neg
  obtain ⟨U', hU', hx₀U', μ', _, ρ, hρd, hρrel, hρgen⟩ := hX κ (ι ⊕ ν') F x₀ hF
  obtain ⟨V, hV, hx₀V, hAV⟩ :=
    exists_isOpen_differentiableOn (f := fun p : κ × ι => A p.1 p.2) (x₀ := x₀)
      fun p => hA p.1 p.2
  -- the relation identity `∑_j ρ_r(j) A_{ij} = ∑_l ρ_r(l) τ_{l,i}` on `U'`
  have key : ∀ r i, ∀ x ∈ U', ∑ j, ρ r (Sum.inl j) x * A i j x =
      ∑ l, ρ r (Sum.inr l) x * τ l i x := by
    intro r i x hx
    have h := hρrel r i x hx
    rw [Fintype.sum_sum_type] at h
    simp only [F, Sum.elim_inl, Sum.elim_inr, mul_neg, Finset.sum_neg_distrib] at h
    linear_combination h
  refine ⟨U ∩ U' ∩ V, (hU.inter hU').inter hV, ⟨⟨hx₀U, hx₀U'⟩, hx₀V⟩, μ', inferInstance,
    fun r j => ρ r (Sum.inl j), ⟨fun r j => (hρd r (Sum.inl j)).mono
      (inter_subset_left.trans inter_subset_right), fun y hy a => ⟨?_, ?_⟩⟩⟩
  · rintro ⟨ha, hNa⟩
    obtain ⟨d, hd, hda⟩ := (hτ.2 y hy.1.1 _).1 hNa
    have hrel : IsRelationAt F y (Sum.elim a d) := by
      refine ⟨fun j => ?_, fun i => ?_⟩
      · cases j with
        | inl j => exact ha j
        | inr l => exact hd l
      · filter_upwards [hda i] with x hx
        have hx' : ∑ j, a j x * A i j x = ∑ l, d l x * τ l i x := by
          rw [← hx]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
        rw [Fintype.sum_sum_type]
        simp only [F, Sum.elim_inl, Sum.elim_inr, mul_neg, Finset.sum_neg_distrib]
        linear_combination hx'
    obtain ⟨e, he, hea⟩ := hρgen y hy.1.2 _ hrel
    exact ⟨e, he, fun j => hea (Sum.inl j)⟩
  · rintro ⟨e, he, hea⟩
    have hρy : ∀ r j, HolAt (ρ r (Sum.inl j)) y := fun r j =>
      holAt_of_differentiableOn hU' (hρd r (Sum.inl j)) hy.1.2
    refine ⟨IsCombinationAt.holTupleAt hρy ⟨e, he, hea⟩, (hτ.2 y hy.1.1 _).2 ?_⟩
    refine ⟨fun l x => ∑ r, e r x * ρ r (Sum.inr l) x,
      fun l => HolAt.fintype_sum fun r =>
        (he r).mul (holAt_of_differentiableOn hU' (hρd r (Sum.inr l)) hy.1.2), fun i => ?_⟩
    have hall : ∀ᶠ x in 𝓝 y, ∀ j, a j x = ∑ r, e r x * ρ r (Sum.inl j) x :=
      eventually_all.2 hea
    filter_upwards [hall, hU'.mem_nhds hy.1.2] with x hx hxU'
    calc matApply A a i x = ∑ j, A i j x * ∑ r, e r x * ρ r (Sum.inl j) x := by
          simp only [matApply, hx]
      _ = ∑ r, e r x * ∑ j, ρ r (Sum.inl j) x * A i j x := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ r, e r x * ∑ l, ρ r (Sum.inr l) x * τ l i x := by
          simp only [key _ i x hxU']
      _ = ∑ l, (∑ r, e r x * ρ r (Sum.inr l) x) * τ l i x := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun r _ => by ring

theorem IsCoherentOn.comap (hX : OkaProperty X) {N : GermModule X κ} {Ω : Set X}
    (hN : N.IsCoherentOn Ω) {A : κ → ι → X → ℂ} (hA : ∀ x ∈ Ω, ∀ i j, HolAt (A i j) x) :
    (N.comap A).IsCoherentOn Ω :=
  fun x hx => (hN x hx).comap hX (hA x hx)

/-- The intersection of `M` with `N`, near a point where `M` is generated by `σ`, is the image
under `σ` of the preimage of `N` under `σ`. -/
theorem GeneratedOn.inf_eqOn {M N : GermModule X ι} {U : Set X} {σ : μ → ι → X → ℂ}
    (hM : M.GeneratedOn U σ) {Ω : Set X} (hN : N.IsCoherentOn Ω) :
    (M.inf N).EqOn ((N.comap (colMatrix σ)).map (colMatrix σ)) (U ∩ Ω) := by
  intro y hy a
  constructor
  · rintro ⟨hMa, hNa⟩
    obtain ⟨c, hc, hca⟩ := (hM.2 y hy.1 a).1 hMa
    have hcj : ∀ j, a j =ᶠ[𝓝 y] matApply (colMatrix σ) c j := fun j =>
      (hca j).trans (Eventually.of_forall fun x => (matApply_colMatrix σ c j x).symm)
    exact ⟨c, ⟨hc, (hN y hy.2).congr_mem hNa hcj⟩, hcj⟩
  · rintro ⟨c, ⟨hc, hNc⟩, hac⟩
    refine ⟨(hM.2 y hy.1 a).2 ⟨c, hc, fun j => (hac j).trans
      (Eventually.of_forall fun x => matApply_colMatrix σ c j x)⟩,
      (hN y hy.2).congr_mem hNc fun j => (hac j).symm⟩

/-- **Intersections of coherent modules are coherent** (Oka). -/
theorem CoherentAt.inf (hX : OkaProperty X) {M N : GermModule X ι} {x₀ : X}
    (hM : M.CoherentAt x₀) (hN : N.CoherentAt x₀) : (M.inf N).CoherentAt x₀ := by
  obtain ⟨U, hU, hx₀U, μ', _, σ, hσ⟩ := hM
  have hS : ∀ i j, HolAt (colMatrix σ i j) x₀ := fun i j => hσ.holAt hU hx₀U j i
  have hP := ((hN.comap hX hS).map hS)
  have hΩ : U ∩ {y | N.CoherentAt y} ∈ 𝓝 x₀ :=
    inter_mem (hU.mem_nhds hx₀U) hN.eventually
  exact hP.of_eqOn hΩ (hσ.inf_eqOn (Ω := {y | N.CoherentAt y}) fun y hy => hy).symm

theorem IsCoherentOn.inf (hX : OkaProperty X) {M N : GermModule X ι} {Ω : Set X}
    (hM : M.IsCoherentOn Ω) (hN : N.IsCoherentOn Ω) : (M.inf N).IsCoherentOn Ω :=
  fun x hx => (hM x hx).inf hX (hN x hx)

/-- **Kernels of holomorphic matrices are coherent** (Oka). -/
theorem CoherentAt.ker (hX : OkaProperty X) {A : κ → ι → X → ℂ} {x₀ : X}
    (hA : ∀ i j, HolAt (A i j) x₀) : (ker A).CoherentAt x₀ :=
  CoherentAt.comap hX (bot_isCoherentOn {x₀} x₀ rfl) hA

/-- **Oka's theorem**: the relations among finitely many tuples holomorphic at `x₀` form a
module coherent at `x₀`. -/
theorem CoherentAt.relations (hX : OkaProperty X) {σ : μ → ι → X → ℂ} {x₀ : X}
    (hσ : ∀ k j, HolAt (σ k j) x₀) : (relations σ).CoherentAt x₀ :=
  CoherentAt.ker hX fun j k => hσ k j

theorem inf_le_left {M N : GermModule X ι} {Ω : Set X} : (M.inf N).LeOn M Ω :=
  fun _ _ _ h => h.1

theorem inf_le_right {M N : GermModule X ι} {Ω : Set X} : (M.inf N).LeOn N Ω :=
  fun _ _ _ h => h.2

theorem le_inf {M N P : GermModule X ι} {Ω : Set X} (hM : P.LeOn M Ω) (hN : P.LeOn N Ω) :
    P.LeOn (M.inf N) Ω :=
  fun y hy a ha => ⟨hM y hy a ha, hN y hy a ha⟩

/-- The image of a module lies in `N` iff the module lies in the preimage of `N`. -/
theorem map_le_iff_le_comap {M : GermModule X ι} {N : GermModule X κ} {Ω : Set X}
    (hM : M.IsCoherentOn Ω) (hN : N.IsCoherentOn Ω) {A : κ → ι → X → ℂ} :
    (M.map A).LeOn N Ω ↔ M.LeOn (N.comap A) Ω := by
  constructor
  · intro h y hy a ha
    exact ⟨(hM y hy).holTupleAt_of_mem ha, h y hy _ (mem_map_of_mem ha)⟩
  · intro h
    exact map_le hN fun y hy a ha => (h y hy a ha).2

/-- The composite `B ∘ A` of matrices; `matApply_matApply` computes its action. -/
def matMul (B : κ → ι → X → ℂ) (A : ι → μ → X → ℂ) : κ → μ → X → ℂ :=
  fun i k x => ∑ j, B i j x * A j k x

theorem comap_comap_eqOn {N : GermModule X κ} {Ω : Set X}
    {B : κ → ι → X → ℂ} {A : ι → μ → X → ℂ} (hA : ∀ x ∈ Ω, ∀ i j, HolAt (A i j) x) :
    ((N.comap B).comap A).EqOn (N.comap (matMul B A)) Ω := by
  intro y hy a
  simp only [comap, matApply_matApply]
  constructor
  · rintro ⟨ha, -, h⟩
    exact ⟨ha, h⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, HolTupleAt.matApply (hA y hy) ha, h⟩

end GermModule

end Hironaka.Analytic.GAGA.Core
