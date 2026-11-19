import Hironaka.Resolution.HironakaG34TorusLemma
import Hironaka.Resolution.HironakaG34CoordinateScaling
import Hironaka.Blowup.LiftedOpenModel
import Hironaka.Invariant.CodimOnePartCanonical

/-!
# The torus lemma in flat coordinates of a manifold (brick (c), chart form)

Lane G34 (run 0080, round 11).  Blueprint: `hironaka-g34-resume-chart-torus-lemma.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §9.2 (c), (d4).

The torus lemma of `HironakaG34TorusLemma` transported to the flat coordinates `Ψ ∘ e` of a complex manifold `M`
(any universe): if an analytic set `C`, regular at `x`, is invariant near its points under the diagonal scalings near
`1` of the coordinates `Ψ ∘ e`, then near `x` it is a coordinate subspace of those coordinates
(`eventually_mem_iff_flat_coordSubspace`).  This is the form in which the torus lemma is applied at every stage of a
lower tail (the toric charts of the stages are flattenings in which the lifted scalings act diagonally).

## Main results

* `regularAtDim_liftedModel_coordSubspace`, `regularAtDim_liftedOpen_coordSubspace`: coordinate subspaces of the
  universe-lifted model and of its opens are regular;
* `eventually_mem_iff_coordSubspace_of_scaling_invariant_lifted`: the model torus lemma on a lifted open of `ℂⁿ`;
* `liftedFlatDiffeo`: the flat coordinates `Ψ ∘ e` as a biholomorphism from the lifted target onto the flat domain;
* **`eventually_mem_iff_flat_coordSubspace`**: the torus lemma in flat coordinates.

New file; no existing statement changed; no sorry; no axiom.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34ChartTorusLemma
noncomputable section
open NormalCrossings BlowupFlatCoordinates HironakaActualFlatCoordinateIntrinsicHS
  HironakaNormalCrossingsDiagonalLiftOrbits HironakaG34CoordinateScaling HironakaG34TorusLemma

variable {n : ℕ}

/-! ### Coordinate subspaces of the lifted model -/

/-- Coordinate subspaces of the universe-lifted model are regular of dimension `n - |B|`. -/
theorem regularAtDim_liftedModel_coordSubspace (B : Finset (Fin n)) {p : LiftedModel.{u} n}
    (hp : p.down ∈ coordSubspace B) :
    RegularAtDim (n := n) {q : LiftedModel.{u} n | q.down ∈ coordSubspace B} p (n - B.card) :=
  HironakaG8MemberLoci.regularAtDim_of_flat_coordSubspace
    (HironakaG8BFamilyEmptyMember.translationAt p.down) (fun _ _ => mem_univ _) (sub_self _)
    (fun {_y} _ _ => (HironakaG8BFamilyEmptyMember.sub_mem_coordSubspace_iff hp).symm)

/-- Coordinate subspaces of a lifted open of `ℂⁿ` are regular of dimension `n - |B|`. -/
theorem regularAtDim_liftedOpen_coordSubspace (S : Opens (ComplexModel n)) (B : Finset (Fin n))
    {p : LiftedOpen.{u} S} (hp : LiftedOpen.toModel S p ∈ coordSubspace B) :
    RegularAtDim (n := n) (coordLocus (LiftedOpen.toModel S) B) p (n - B.card) :=
  AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
    (regularAtDim_liftedModel_coordSubspace B hp)

/-- **The model torus lemma on a lifted open of `ℂⁿ`.** -/
theorem eventually_mem_iff_coordSubspace_of_scaling_invariant_lifted {S : Opens (ComplexModel n)}
    {C : Set (LiftedOpen.{u} S)} {p : LiftedOpen.{u} S} {k : ℕ}
    (hCan : IsComplexAnalyticSubset (n := n) C) (hp : RegularAtDim (n := n) C p k)
    (hinv : ∀ᶠ q in 𝓝 p, q ∈ C → ∀ᶠ τ in 𝓝 (1 : Fin n → ℂ),
      ∀ q' : LiftedOpen.{u} S, LiftedOpen.toModel S q' = diagonal τ (LiftedOpen.toModel S q) → q' ∈ C) :
    ∃ B : Finset (Fin n), (∀ l ∈ B, LiftedOpen.toModel S p l = 0) ∧
      ∀ᶠ y in 𝓝 p, y ∈ C ↔ LiftedOpen.toModel S y ∈ coordSubspace B := by
  have hL : ∀ B : Finset (Fin n), IsComplexAnalyticSubset (n := n) (coordLocus (LiftedOpen.toModel S) B) :=
    fun B => AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (LiftedOpen.contMDiff_toModel S)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
        (HironakaG8BFamilyEmptyMember.isClosedSubmanifold_coordSubspace B))
  have hLreg : ∀ B : Finset (Fin n), ∀ᶠ y in 𝓝 p, y ∈ coordLocus (LiftedOpen.toModel S) B →
      RegularAtDim (n := n) (coordLocus (LiftedOpen.toModel S) B) y (n - B.card) :=
    fun B => Eventually.of_forall fun y hy => regularAtDim_liftedOpen_coordSubspace S B hy
  have horbit : ∀ᶠ q in 𝓝 p, q ∈ C → ∀ᶠ q' in 𝓝 q,
      (∀ l, LiftedOpen.toModel S q l = 0 → LiftedOpen.toModel S q' l = 0) → q' ∈ C := by
    filter_upwards [hinv] with q hq hqC
    have ht : Tendsto (fun q' : LiftedOpen.{u} S =>
        ratioScale (LiftedOpen.toModel S q) (LiftedOpen.toModel S q')) (𝓝 q) (𝓝 1) :=
      (tendsto_ratioScale (LiftedOpen.toModel S q)).comp (LiftedOpen.continuous_toModel S).continuousAt
    filter_upwards [ht.eventually (hq hqC)] with q' hq' hpat
    exact hq' q' (diagonal_ratioScale hpat).symm
  exact eventually_mem_iff_coordLocus_of_orbit (LiftedOpen.toModel S) hCan hp hL hLreg horbit

/-! ### Flat coordinates as a biholomorphism -/

section Flat

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {x₀ : M} (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
  (hΨsrc : Ψ.source ⊆ (chartAt (ComplexModel n) x₀).target)

/-- The open flat domain. -/
abbrev flatOpens : Opens M := ⟨flatDomain Ψ, isOpen_flatDomain Ψ⟩

/-- The open target. -/
abbrev targetOpens : Opens (ComplexModel n) := ⟨Ψ.target, Ψ.isOpen_target⟩

/-- **The flat coordinates as a biholomorphism** from the lifted target onto the flat domain. -/
def liftedFlatDiffeo :
    LiftedOpen.{u} (targetOpens Ψ) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ flatOpens Ψ where
  toFun p := (actualFlatCoordinateDiffeomorph Ψ hΨsrc).symm
    ⟨LiftedOpen.toModel _ p, LiftedOpen.toModel_mem _ p⟩
  invFun y := LiftedOpen.mk _ (actualFlatCoordinateDiffeomorph Ψ hΨsrc y : ComplexModel n)
    (actualFlatCoordinateDiffeomorph Ψ hΨsrc y).2
  left_inv p := by
    apply Subtype.ext
    apply ULift.ext
    show ((actualFlatCoordinateDiffeomorph Ψ hΨsrc ((actualFlatCoordinateDiffeomorph Ψ hΨsrc).symm
      ⟨LiftedOpen.toModel _ p, LiftedOpen.toModel_mem _ p⟩)) : ComplexModel n) = LiftedOpen.toModel _ p
    rw [Diffeomorph.apply_symm_apply]
  right_inv y := (actualFlatCoordinateDiffeomorph Ψ hΨsrc).symm_apply_apply y
  contMDiff_toFun := (actualFlatCoordinateDiffeomorph Ψ hΨsrc).symm.contMDiff.comp
    (BlowupRestrictOpen.contMDiff_opens_mk (V := targetOpens Ψ) (LiftedOpen.contMDiff_toModel _)
      (fun p => LiftedOpen.toModel_mem _ p))
  contMDiff_invFun := fun y => LiftedOpen.contMDiffAt_of_toModel _
    ((contMDiff_subtype_val.comp (actualFlatCoordinateDiffeomorph Ψ hΨsrc).contMDiff) y)

theorem flatMap_liftedFlatDiffeo (p : LiftedOpen.{u} (targetOpens Ψ)) :
    flatMap Ψ ((liftedFlatDiffeo Ψ hΨsrc p : flatOpens Ψ) : M) = LiftedOpen.toModel _ p := by
  show ((actualFlatCoordinateDiffeomorph Ψ hΨsrc ((actualFlatCoordinateDiffeomorph Ψ hΨsrc).symm
      ⟨LiftedOpen.toModel _ p, LiftedOpen.toModel_mem _ p⟩)) : ComplexModel n) = LiftedOpen.toModel _ p
  rw [Diffeomorph.apply_symm_apply]

theorem toModel_liftedFlatDiffeo_symm (y : flatOpens Ψ) :
    LiftedOpen.toModel _ ((liftedFlatDiffeo Ψ hΨsrc).symm y) = flatMap Ψ (y : M) := rfl

include hΨsrc in
/-- **The torus lemma in flat coordinates.**  An analytic set `C`, regular at `x` (a point of the flat domain of
`Ψ`), invariant near its points under the diagonal scalings near `1` of the coordinates `Ψ ∘ e`, is near `x` a
coordinate subspace of these coordinates, cut out by coordinates vanishing at `x`. -/
theorem eventually_mem_iff_flat_coordSubspace {C : Set M} {x : M} {k : ℕ} (hx : x ∈ flatDomain Ψ)
    (hCan : IsComplexAnalyticSubset (n := n) C) (hreg : RegularAtDim (n := n) C x k)
    (hinv : ∀ᶠ q in 𝓝 x, q ∈ C → ∀ᶠ τ in 𝓝 (1 : Fin n → ℂ),
      ∀ q' ∈ flatDomain Ψ, flatMap Ψ q' = diagonal τ (flatMap Ψ q) → q' ∈ C) :
    ∃ B : Finset (Fin n), (∀ l ∈ B, flatMap Ψ x l = 0) ∧
      ∀ᶠ y in 𝓝 x, y ∈ C ↔ flatMap Ψ y ∈ coordSubspace B := by
  set D := liftedFlatDiffeo Ψ hΨsrc with hD
  let C₁ : Set (LiftedOpen.{u} (targetOpens Ψ)) := (fun p => ((D p : flatOpens Ψ) : M)) ⁻¹' C
  let x' : flatOpens Ψ := ⟨x, hx⟩
  let p : LiftedOpen.{u} (targetOpens Ψ) := D.symm x'
  have hDp : D p = x' := D.apply_symm_apply x'
  have hcont : Continuous fun p : LiftedOpen.{u} (targetOpens Ψ) => ((D p : flatOpens Ψ) : M) :=
    continuous_subtype_val.comp D.continuous
  have hCan₁ : IsComplexAnalyticSubset (n := n) C₁ :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_subtype_val.comp D.contMDiff) hCan
  have hreg₁ : RegularAtDim (n := n) C₁ p k := by
    have h1 : RegularAtDim (n := n) ((Subtype.val : flatOpens Ψ → M) ⁻¹' C) (D p) k := by
      rw [hDp]
      exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hreg
    exact (CodimOnePartCanonical.regularAtDim_preimage_iff D).mpr h1
  have hpx : ((D p : flatOpens Ψ) : M) = x := by rw [hDp]
  have ht : Tendsto (fun p : LiftedOpen.{u} (targetOpens Ψ) => ((D p : flatOpens Ψ) : M)) (𝓝 p) (𝓝 x) := by
    have := hcont.tendsto p
    rwa [hpx] at this
  have hinv₁ : ∀ᶠ q in 𝓝 p, q ∈ C₁ → ∀ᶠ τ in 𝓝 (1 : Fin n → ℂ),
      ∀ q' : LiftedOpen.{u} (targetOpens Ψ),
        LiftedOpen.toModel _ q' = diagonal τ (LiftedOpen.toModel _ q) → q' ∈ C₁ := by
    filter_upwards [ht.eventually hinv] with q hq hqC
    filter_upwards [hq hqC] with τ hτ q' hq'
    refine hτ _ (D q').2 ?_
    rw [flatMap_liftedFlatDiffeo, flatMap_liftedFlatDiffeo, hq']
  obtain ⟨B, hB0, hB⟩ :=
    eventually_mem_iff_coordSubspace_of_scaling_invariant_lifted hCan₁ hreg₁ hinv₁
  have hpm : LiftedOpen.toModel _ p = flatMap Ψ x := toModel_liftedFlatDiffeo_symm Ψ hΨsrc x'
  refine ⟨B, fun l hl => by rw [← hpm]; exact hB0 l hl, ?_⟩
  -- transport the eventual description back to `M`
  have hsub : ∀ᶠ y' in 𝓝 x', (D.symm y' ∈ C₁ ↔ LiftedOpen.toModel _ (D.symm y') ∈ coordSubspace B) :=
    (D.symm.continuous.tendsto x').eventually hB
  have hsub' : ∀ᶠ (y' : flatOpens Ψ) in 𝓝 x', ((y' : M) ∈ C ↔ flatMap Ψ (y' : M) ∈ coordSubspace B) := by
    filter_upwards [hsub] with y' hy'
    have e1 : (D.symm y' ∈ C₁) ↔ (y' : M) ∈ C := by
      show ((D (D.symm y') : flatOpens Ψ) : M) ∈ C ↔ _
      rw [D.apply_symm_apply]
    rw [← e1, hy', toModel_liftedFlatDiffeo_symm]
  have hmap := map_nhds_subtype_coe_eq_nhds hx ((isOpen_flatDomain Ψ).mem_nhds hx)
  rw [← hmap]
  exact Filter.eventually_map.mpr hsub'

end Flat

end
end Hironaka.HironakaG34ChartTorusLemma
