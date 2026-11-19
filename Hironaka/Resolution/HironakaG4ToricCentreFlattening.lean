import Hironaka.Resolution.HironakaG34ToricCharts
import Hironaka.Resolution.HironakaG34ChartTorusLemma

/-!
# Flattening an invariant next centre without losing its diagonal action

This supplies the chart restriction/permutation step (d3) in the G34
all-dimensional toric route. The permutation construction is a public API
extraction of the private `HironakaG8MemberLoci.permuteCoords`; that construction
is reuse, not new mathematical credit. New statements derive convergence of
the actual local actions from their diagonal relation, preserve that relation
on a genuine smaller chart domain, and flatten a germ of an invariant centre.

The input invariance of the centre is the local scaling-invariance hypothesis
of the already proved chart torus lemma. No equivariant protection certificate,
all-future chart package, or resolution conclusion is an input.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4ToricCentreFlattening

noncomputable section

open BlowupFlatCoordinates NormalCrossings SimultaneousNormalCrossings
  HironakaG34CoordinateScaling HironakaG34ToricCharts HironakaG34ChartTorusLemma
  HironakaNormalCrossingsDiagonalLiftOrbits

variable {n : ℕ}

/-- Public extraction of the existing private coordinate-permutation construction. -/
def permuteChart {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    (σ : Fin n ≃ Fin n) : LocalHolomorphicEquivAt (n := n) p := by
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ
  exact
    { source := Φ.source
      target := L.symm ⁻¹' Φ.target
      isOpen_source := Φ.isOpen_source
      isOpen_target := Φ.isOpen_target.preimage L.symm.continuous
      center_mem_source := Φ.center_mem_source
      toFun := fun z => L (Φ.toFun z)
      invFun := fun z => Φ.invFun (L.symm z)
      toFun_holomorphic := L.toContinuousLinearEquiv.toContinuousLinearMap.differentiableOn.comp
        Φ.toFun_holomorphic (fun _ _ => mem_univ _)
      invFun_holomorphic := Φ.invFun_holomorphic.comp
        L.symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableOn
        (fun _ hz => hz)
      mapsTo_toFun := fun z hz => by
        change L.symm (L (Φ.toFun z)) ∈ Φ.target
        rw [L.symm_apply_apply]
        exact Φ.mapsTo_toFun hz
      mapsTo_invFun := fun z hz => Φ.mapsTo_invFun hz
      left_inv := fun z hz => by
        rw [L.symm_apply_apply]
        exact Φ.left_inv z hz
      right_inv := fun z hz => by
        rw [Φ.right_inv _ hz]
        exact L.apply_symm_apply z }

/-- Permuting coordinates sends the old index `i` to `σ i`. -/
theorem permuteChart_apply {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    (σ : Fin n ≃ Fin n) (z : ComplexModel n) (i : Fin n) :
    (permuteChart Φ σ).toFun z (σ i) = Φ.toFun z i := by
  simp [permuteChart, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

section Manifold

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {x : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)}

/-- The diagonal relation with characters tending to `1` forces the actual
images to tend to the chart centre; no joint continuity of the action is assumed. -/
theorem tendsto_act_of_diagonal {A : Type*} {F : Filter A} {act : A → M → M}
    {μ : A → Fin n → ℂ} (hμ : Tendsto μ F (𝓝 1))
    (hdiag : ActsDiagonallyNear F act μ Φ x) :
    Tendsto (fun p : A × M => act p.1 p.2) (F ×ˢ 𝓝 x) (𝓝 x) := by
  have hx : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hflat : Tendsto (fun p : A × M => flatMap Φ p.2) (F ×ˢ 𝓝 x)
      (𝓝 (flatMap Φ x)) :=
    ((continuousOn_flatMap Φ).continuousAt ((isOpen_flatDomain Φ).mem_nhds hx)).tendsto.comp
      tendsto_snd
  have hmul : Tendsto (fun p : A × M => diagonal (μ p.1) (flatMap Φ p.2))
      (F ×ˢ 𝓝 x) (𝓝 (flatMap Φ x)) := by
    have h := (continuous_diagonal_prod.tendsto (1, flatMap Φ x)).comp
      ((hμ.comp tendsto_fst).prodMk_nhds hflat)
    rw [diagonal_one] at h
    exact h
  have hinverse := (tendsto_flatInverse Φ hx).comp hmul
  apply hinverse.congr'
  filter_upwards [hdiag] with p hp
  change (chartAt (ComplexModel n) x).symm
    (Φ.invFun (diagonal (μ p.1) (flatMap Φ p.2))) = act p.1 p.2
  rw [← hp.2.2]
  exact flatInverse_flat Φ hp.2.1

/-- Restricting a chart to any open source neighbourhood retains the diagonal
relation, because both the point and its image eventually belong to that domain. -/
theorem actsDiagonallyNear_restrict {A : Type*} {F : Filter A} {act : A → M → M}
    {μ : A → Fin n → ℂ} (hμ : Tendsto μ F (𝓝 1))
    (hdiag : ActsDiagonallyNear F act μ Φ x)
    (s : Set (ComplexModel n)) (hs : IsOpen s) (hx : chartAt (ComplexModel n) x x ∈ s) :
    ActsDiagonallyNear F act μ
      (Φ.restrict s hs (chartAt (ComplexModel n) x x) ⟨Φ.center_mem_source, hx⟩) x := by
  let Ψ := Φ.restrict s hs (chartAt (ComplexModel n) x x) ⟨Φ.center_mem_source, hx⟩
  have hxΨ : x ∈ flatDomain Ψ := mem_flatDomain_self Ψ
  have hsource : ∀ᶠ p : A × M in F ×ˢ 𝓝 x, p.2 ∈ flatDomain Ψ :=
    tendsto_snd.eventually ((isOpen_flatDomain Ψ).mem_nhds hxΨ)
  have himage : ∀ᶠ p : A × M in F ×ˢ 𝓝 x, act p.1 p.2 ∈ flatDomain Ψ :=
    (tendsto_act_of_diagonal hμ hdiag).eventually ((isOpen_flatDomain Ψ).mem_nhds hxΨ)
  filter_upwards [hsource, himage, hdiag] with p hp hpa hpd
  exact ⟨hp, hpa, hpd.2.2⟩

omit [IsComplexManifold n M] in
/-- A permutation conjugates the diagonal characters by the inverse index map. -/
theorem actsDiagonallyNear_permute {A : Type*} {F : Filter A} {act : A → M → M}
    {μ : A → Fin n → ℂ} (hdiag : ActsDiagonallyNear F act μ Φ x)
    (σ : Fin n ≃ Fin n) :
    ActsDiagonallyNear F act (fun a i => μ a (σ.symm i)) (permuteChart Φ σ) x := by
  filter_upwards [hdiag] with p hp
  refine ⟨hp.1, hp.2.1, ?_⟩
  ext i
  obtain ⟨j, rfl⟩ := σ.surjective i
  change (permuteChart Φ σ).toFun _ (σ j) = _
  rw [permuteChart_apply]
  change flatMap Φ (act p.1 p.2) j = μ p.1 (σ.symm (σ j)) *
    (permuteChart Φ σ).toFun _ (σ j)
  rw [permuteChart_apply, σ.symm_apply_apply, hp.2.2]
  rfl

/-- A coordinate-subspace germ gives an actual flattening on a restricted
source domain, together with the inherited diagonal action. -/
theorem exists_flattening_of_coordSubspace_germ {C : Set M}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (B : Finset (Fin n))
    (hC : ∀ᶠ y in 𝓝 x, y ∈ C ↔ flatMap Φ y ∈ coordSubspace B)
    {A : Type*} {F : Filter A} {act : A → M → M} {μ : A → Fin n → ℂ}
    (hμ : Tendsto μ F (𝓝 1)) (hdiag : ActsDiagonallyNear F act μ Φ x) :
    ∃ (σ : Fin n ≃ Fin n)
      (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
      (∀ i, n - B.card ≤ (σ i).1 ↔ i ∈ B) ∧
      Ψ.source ⊆ Φ.source ∧ Ψ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      (∀ y, y ∈ flatDomain Ψ →
        (y ∈ C ↔ flatMap Ψ y ∈ complexCoordinatePlane n (n - B.card))) ∧
      (∀ z i, Ψ.toFun z (σ i) = Φ.toFun z i) ∧
      ActsDiagonallyNear F act (fun a i => μ a (σ.symm i)) Ψ x := by
  classical
  obtain ⟨U, hUC, hU, hxU⟩ := mem_nhds_iff.mp hC
  let e := chartAt (ComplexModel n) x
  let s : Set (ComplexModel n) := e.target ∩ e.symm ⁻¹' U
  have hs : IsOpen s := e.isOpen_inter_preimage_symm hU
  have hxs : e x ∈ s := ⟨e.map_source (mem_chart_source _ x), by
    simpa only [mem_preimage, e.left_inv (mem_chart_source _ x)] using hxU⟩
  let Φs := Φ.restrict s hs (e x) ⟨Φ.center_mem_source, hxs⟩
  obtain ⟨σ, hσ⟩ := exists_perm_nested (X := B) (Y := B) (Subset.refl _)
  let Ψ := permuteChart Φs σ
  refine ⟨σ, Ψ, fun i => (hσ i).1, inter_subset_left,
    fun z hz => hΦsrc hz.1, ?_, ?_, ?_⟩
  · intro y hy
    have hyU : y ∈ U := by
      have hys : e y ∈ s := hy.2.2
      have hye : y ∈ e.source := hy.1
      simpa only [s, mem_inter_iff, mem_preimage, e.left_inv hye] using hys.2
    have hyC : y ∈ C ↔ flatMap Φ y ∈ coordSubspace B := hUC hyU
    rw [hyC]
    constructor
    · intro h i hi
      obtain ⟨j, rfl⟩ := σ.surjective i
      change Ψ.toFun (e y) (σ j) = 0
      rw [permuteChart_apply]
      exact h j ((hσ j).1.mp hi)
    · intro h j hj
      have hh := h (σ j) ((hσ j).1.mpr hj)
      change (permuteChart Φs σ).toFun (e y) (σ j) = 0 at hh
      rw [permuteChart_apply] at hh
      exact hh
  · intro z i
    exact permuteChart_apply Φs σ z i
  · exact actsDiagonallyNear_permute (actsDiagonallyNear_restrict hμ hdiag s hs hxs) σ

/-- The existing chart torus lemma constructs the coordinate-subspace germ;
the preceding theorem converts it to the actual next-centre flattening. -/
theorem exists_flattening_of_scaling_invariant {C : Set M} {k : ℕ}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hCan : IsComplexAnalyticSubset (n := n) C) (hreg : RegularAtDim (n := n) C x k)
    (hinv : ∀ᶠ q in 𝓝 x, q ∈ C → ∀ᶠ τ in 𝓝 (1 : Fin n → ℂ),
      ∀ q' ∈ flatDomain Φ, flatMap Φ q' = diagonal τ (flatMap Φ q) → q' ∈ C)
    {A : Type*} {F : Filter A} {act : A → M → M} {μ : A → Fin n → ℂ}
    (hμ : Tendsto μ F (𝓝 1)) (hdiag : ActsDiagonallyNear F act μ Φ x) :
    ∃ (B : Finset (Fin n)) (σ : Fin n ≃ Fin n)
      (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
      (∀ i ∈ B, flatMap Φ x i = 0) ∧
      (∀ i, n - B.card ≤ (σ i).1 ↔ i ∈ B) ∧
      Ψ.source ⊆ Φ.source ∧ Ψ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      (∀ y, y ∈ flatDomain Ψ →
        (y ∈ C ↔ flatMap Ψ y ∈ complexCoordinatePlane n (n - B.card))) ∧
      (∀ z i, Ψ.toFun z (σ i) = Φ.toFun z i) ∧
      ActsDiagonallyNear F act (fun a i => μ a (σ.symm i)) Ψ x := by
  obtain ⟨B, hBzero, hB⟩ :=
    eventually_mem_iff_flat_coordSubspace Φ hΦsrc (mem_flatDomain_self Φ) hCan hreg hinv
  obtain ⟨σ, Ψ, hσ, hΨ, hsrc, hflat, hcoords, haction⟩ :=
    exists_flattening_of_coordSubspace_germ hΦsrc B hB hμ hdiag
  exact ⟨B, σ, Ψ, hBzero, hσ, hΨ, hsrc, hflat, hcoords, haction⟩

end Manifold

end

end Hironaka.HironakaG4ToricCentreFlattening
