import Hironaka.Analytic.FlatteningTangentSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The flattening tangent space is independent of the flattening

Source: Copy-4, Steps 4 and 6 of `prop:principalization`, where `A_W` has to be
Kähler *on `W`*, i.e. where `β` has to be strictly positive exactly on `T_W`.

`Pending/SmoothPotentialDomination.exists_tube_dominatesKahlerFormOn` and
`Pending/ManifoldTubePositivity.exists_tube_forall_strictPosAt` ask for strict
positivity of `β` on `(dF)⁻¹(ℂᵏ × 0)` for **every** nondegenerate holomorphic
flattening `F` of `W` in **every** ambient chart.  A consumer cannot discharge a
`∀ F` hypothesis without knowing that the subspace does not depend on `F`; that
is the design question I-0356 left open, and `Pending/FlatteningTangentSpace`
assembles the ingredients for it without stating it.  This module states and
proves it.

## The argument

Fix a chart `f`, a point `w ∈ W` and write `z₀ = f w`.  Regularity of `W` at `w`
supplies a **canonical** flattening `Ψ = flatChartMap e f Φ` (`e` the preferred
chart at `w`), which is distinguished by carrying an explicit inverse
`flatChartMapInv`; no inverse function theorem is used anywhere below.

* `comap_le_comap_of_admissible` — `(dΨ)⁻¹(P) ⊆ (dF)⁻¹(P)` for every admissible
  `F`.  A vector `v` of the left side is the velocity at `0` of the curve
  `t ↦ Ψ⁻¹(Ψ z₀ + t · dΨ z₀ v)`, which stays inside `W` because `Ψ` sends it to
  the affine line `Ψ z₀ + t · dΨ z₀ v` lying in `P`; so `F` of that curve stays
  in `P`, and a derivative of a curve confined to a closed subspace lies in that
  subspace (`mem_of_hasDerivAt_of_eventually_mem`).
* The rank squeeze of `FlatteningTangentSpace` closes it: `dΨ z₀` is injective on
  a finite-dimensional space, hence bijective, so `(dΨ)⁻¹(P)` has rank exactly
  `rank P`, while `(dF)⁻¹(P)` has rank at most `rank P` because `dF z₀` is
  injective.  Inclusion plus the rank inequality forces equality.

`forall_admissible_flattening_of_exists` packages this as the `∃ → ∀` transfer a
consumer actually performs: any property of the vectors tangent to *one*
admissible nondegenerate flattening holds for *every* one.  Its shape is exactly
the `hβ` of `exists_tube_dominatesKahlerFormOn`.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.FlatteningTangentSpaceIndependence

noncomputable section

open GlobalTubeFunction FlatteningTangentSpace

variable {n : ℕ}

/-! ### A derivative of a curve confined to a closed subspace -/

/-- If a curve lies in a closed subspace near a parameter value, so does its
velocity there.  This is the only analytic input of the module. -/
theorem mem_of_hasDerivAt_of_eventually_mem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {h : ℝ → E} {L : E} {P : Submodule ℝ E}
    (hP : IsClosed (P : Set E)) (hd : HasDerivAt h L 0)
    (hmem : ∀ᶠ t in 𝓝 (0 : ℝ), h t ∈ P) : L ∈ P := by
  have h0 : h 0 ∈ P := hmem.self_of_nhds
  rw [hasDerivAt_iff_tendsto_slope] at hd
  refine hP.mem_of_tendsto hd ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with t _ htP
  have hslope : slope h 0 t = (t - 0)⁻¹ • (h t - h 0) := by
    rw [slope_def_module]
  rw [hslope]
  exact P.smul_mem _ (P.sub_mem htP h0)

/-! ### The explicit inverse of the canonical flattening -/

section Canonical

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {p : ComplexModel n}
  {e f : ComplexChart n M} {Φ : LocalHolomorphicEquivAt (n := n) p}

/-- The points of `Φ.target` that `flatChartMapInv e f Φ` carries back into
`flatChartDomain e f Φ`. -/
def invChartDomain (e f : ComplexChart n M) (Φ : LocalHolomorphicEquivAt (n := n) p) :
    Set (ComplexModel n) :=
  Φ.target ∩ Φ.invFun ⁻¹' (chartTransition f e).target

theorem isOpen_invChartDomain : IsOpen (invChartDomain e f Φ) :=
  ContinuousOn.isOpen_inter_preimage Φ.invFun_holomorphic.continuousOn
    Φ.isOpen_target (chartTransition f e).open_target

theorem flatChartMapInv_mem_flatChartDomain {y : ComplexModel n}
    (hy : y ∈ invChartDomain e f Φ) :
    flatChartMapInv e f Φ y ∈ flatChartDomain e f Φ := by
  have h1 : flatChartMapInv e f Φ y ∈ (chartTransition f e).source :=
    (chartTransition f e).map_target hy.2
  have h2 : chartTransition f e (flatChartMapInv e f Φ y) = Φ.invFun y :=
    (chartTransition f e).right_inv hy.2
  have h3 : Φ.invFun y ∈ Φ.source := Φ.mapsTo_invFun hy.1
  have h4 : chartTransition f e (flatChartMapInv e f Φ y) ∈ Φ.source := by
    rw [h2]; exact h3
  exact ⟨h1.1, h1.2, h4⟩

theorem flatChartMap_flatChartMapInv {y : ComplexModel n}
    (hy : y ∈ invChartDomain e f Φ) :
    flatChartMap e f Φ (flatChartMapInv e f Φ y) = y := by
  show Φ.toFun (chartTransition f e ((chartTransition f e).symm (Φ.invFun y))) = y
  rw [(chartTransition f e).right_inv hy.2]
  exact Φ.right_inv y hy.1

theorem flatChartMap_mem_invChartDomain {z : ComplexModel n}
    (hz : z ∈ flatChartDomain e f Φ) :
    flatChartMap e f Φ z ∈ invChartDomain e f Φ :=
  ⟨flatChartMap_mem_Φtarget hz, by
    show Φ.invFun (flatChartMap e f Φ z) ∈ (chartTransition f e).target
    rw [invFun_flatChartMap hz]
    exact (chartTransition f e).map_source (mem_chartTransition_source hz)⟩

/-! ### A canonical tangent vector is tangent to every admissible flattening -/

/-- **The inclusion.**  Every vector that the canonical flattening `Ψ` sends into
the coordinate plane is sent there by any other admissible flattening `F`:
it is the velocity of a holomorphic curve that stays inside `W`. -/
theorem comap_le_comap_of_admissible {W : Set M} {k : ℕ}
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ flatChartDomain e f Φ)
    (hW : f.val.symm z₀ ∈ W)
    (hflat : ∀ z ∈ flatChartDomain e f Φ,
      (f.val.symm z ∈ W ↔ flatChartMap e f Φ z ∈ complexCoordinatePlane n k))
    {F : ComplexModel n → ComplexModel n} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hz₀D : z₀ ∈ D) (hF : DifferentiableAt ℝ F z₀)
    (hFflat : ∀ z ∈ D, (f.val.symm z ∈ W ↔ F z ∈ complexCoordinatePlane n k)) :
    (planeSubmodule n k).comap
        (fderiv ℝ (flatChartMap e f Φ) z₀ : ComplexModel n →ₗ[ℝ] ComplexModel n) ≤
      (planeSubmodule n k).comap
        (fderiv ℝ F z₀ : ComplexModel n →ₗ[ℝ] ComplexModel n) := by
  intro v hv
  show fderiv ℝ F z₀ v ∈ planeSubmodule n k
  have hvP : fderiv ℝ (flatChartMap e f Φ) z₀ v ∈ planeSubmodule n k := hv
  -- the affine line the canonical flattening sends the curve to
  have hy₀P : flatChartMap e f Φ z₀ ∈ planeSubmodule n k := (hflat z₀ hz₀).mp hW
  have hcP : ∀ t : ℝ,
      flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v
        ∈ planeSubmodule n k := fun t =>
    (planeSubmodule n k).add_mem hy₀P ((planeSubmodule n k).smul_mem t hvP)
  have hcderiv : HasDerivAt
      (fun t : ℝ => flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v)
      (fderiv ℝ (flatChartMap e f Φ) z₀ v) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const
      (fderiv ℝ (flatChartMap e f Φ) z₀ v)).const_add (flatChartMap e f Φ z₀)
    rwa [one_smul] at h
  have hzero : (fun t : ℝ =>
      flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v) 0
        = flatChartMap e f Φ z₀ := by simp
  -- transporting the line back by the explicit inverse gives a curve inside `W`
  have hΨiF : HasFDerivAt (flatChartMapInv e f Φ)
      (fderiv ℝ (flatChartMapInv e f Φ) (flatChartMap e f Φ z₀))
      ((fun t : ℝ =>
        flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v) 0) := by
    rw [hzero]
    exact (differentiableAt_flatChartMapInv hz₀).hasFDerivAt
  have hcurve : HasDerivAt
      (fun t : ℝ => flatChartMapInv e f Φ
        (flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v))
      (fderiv ℝ (flatChartMapInv e f Φ) (flatChartMap e f Φ z₀)
        (fderiv ℝ (flatChartMap e f Φ) z₀ v)) 0 :=
    HasFDerivAt.comp_hasDerivAt (l := flatChartMapInv e f Φ) (0 : ℝ) hΨiF hcderiv
  have hbase : flatChartMapInv e f Φ
      ((fun t : ℝ =>
        flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v) 0) = z₀ := by
    rw [hzero]; exact flatChartMapInv_flatChartMap hz₀
  have hFF : HasFDerivAt F (fderiv ℝ F z₀)
      (flatChartMapInv e f Φ
        ((fun t : ℝ =>
          flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v) 0)) := by
    rw [hbase]; exact hF.hasFDerivAt
  have hh : HasDerivAt
      (fun t : ℝ => F (flatChartMapInv e f Φ
        (flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v)))
      (fderiv ℝ F z₀ (fderiv ℝ (flatChartMapInv e f Φ) (flatChartMap e f Φ z₀)
        (fderiv ℝ (flatChartMap e f Φ) z₀ v))) 0 :=
    HasFDerivAt.comp_hasDerivAt (l := F) (0 : ℝ) hFF hcurve
  -- the velocity of the transported curve is `v` itself
  have hvel : fderiv ℝ (flatChartMapInv e f Φ) (flatChartMap e f Φ z₀)
      (fderiv ℝ (flatChartMap e f Φ) z₀ v) = v := by
    have hcomp := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L v)
      (fderiv_flatChartMapInv_comp hz₀)
    simpa using hcomp
  rw [hvel] at hh
  -- the transported curve stays inside `W`, so `F` of it stays inside the plane
  have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      F (flatChartMapInv e f Φ
        (flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v))
      ∈ planeSubmodule n k := by
    have h1 : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
        flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v
          ∈ invChartDomain e f Φ := by
      refine hcderiv.continuousAt.preimage_mem_nhds ?_
      rw [zero_smul, add_zero]
      exact isOpen_invChartDomain.mem_nhds (flatChartMap_mem_invChartDomain hz₀)
    have h2 : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
        flatChartMapInv e f Φ
          (flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v) ∈ D := by
      refine hcurve.continuousAt.preimage_mem_nhds ?_
      rw [zero_smul, add_zero, flatChartMapInv_flatChartMap hz₀]
      exact hD.mem_nhds hz₀D
    filter_upwards [h1, h2] with t ht htD
    have hmem : flatChartMapInv e f Φ
        (flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v)
        ∈ flatChartDomain e f Φ := flatChartMapInv_mem_flatChartDomain ht
    have hΨc : flatChartMap e f Φ (flatChartMapInv e f Φ
        (flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v))
        = flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v :=
      flatChartMap_flatChartMapInv ht
    have hWc : f.val.symm (flatChartMapInv e f Φ
        (flatChartMap e f Φ z₀ + t • fderiv ℝ (flatChartMap e f Φ) z₀ v)) ∈ W :=
      (hflat _ hmem).mpr (by rw [hΨc]; exact hcP t)
    exact (hFflat _ htD).mp hWc
  exact mem_of_hasDerivAt_of_eventually_mem
    (Submodule.closed_of_finiteDimensional (planeSubmodule n k)) hh hev

/-! ### Independence -/

/-- **The flattening tangent space is independent of the flattening.**  For any
admissible nondegenerate `F`, the preimage of the coordinate plane under
`dF z₀` is the preimage under the differential of the canonical flattening. -/
theorem comap_fderiv_eq_comap_fderiv_flatChartMap {W : Set M} {k : ℕ}
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ flatChartDomain e f Φ)
    (hW : f.val.symm z₀ ∈ W)
    (hflat : ∀ z ∈ flatChartDomain e f Φ,
      (f.val.symm z ∈ W ↔ flatChartMap e f Φ z ∈ complexCoordinatePlane n k))
    {F : ComplexModel n → ComplexModel n} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hz₀D : z₀ ∈ D) (hF : DifferentiableAt ℝ F z₀)
    (hFinj : Function.Injective (fderiv ℝ F z₀))
    (hFflat : ∀ z ∈ D, (f.val.symm z ∈ W ↔ F z ∈ complexCoordinatePlane n k)) :
    (planeSubmodule n k).comap
        (fderiv ℝ F z₀ : ComplexModel n →ₗ[ℝ] ComplexModel n) =
      (planeSubmodule n k).comap
        (fderiv ℝ (flatChartMap e f Φ) z₀ : ComplexModel n →ₗ[ℝ] ComplexModel n) := by
  have hle := comap_le_comap_of_admissible hz₀ hW hflat hD hz₀D hF hFflat
  have hinj : Function.Injective (fderiv ℝ (flatChartMap e f Φ) z₀) :=
    fderiv_flatChartMap_injective e f Φ hz₀
  have hbij : Function.Bijective
      ((fderiv ℝ (flatChartMap e f Φ) z₀ : ComplexModel n →ₗ[ℝ] ComplexModel n)) :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have h1 := finrank_comap_eq_of_bijective (fderiv ℝ (flatChartMap e f Φ) z₀) hbij
    (planeSubmodule n k)
  have h2 := finrank_comap_le (fderiv ℝ F z₀) hFinj (planeSubmodule n k)
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [h1]; exact h2)).symm

end Canonical

/-! ### Discharging a `∀ F` hypothesis -/

section Transfer

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]


/-- **The `∃ → ∀` transfer.**  A property of the vectors tangent to *one*
admissible nondegenerate flattening of `W` in the chart `f` at `w` holds for
*every* one.  This is the shape of the `hβ` hypothesis of
`Hironaka.SmoothPotentialDomination.exists_tube_dominatesKahlerFormOn` and of
`Hironaka.ManifoldTubePositivity.exists_tube_forall_strictPosAt`. -/
theorem forall_admissible_flattening_of_exists {W : Set M} {k : ℕ}
    {w : M} (hw : w ∈ W) (hreg : RegularAtDim (n := n) W w k)
    {f : ComplexChart n M} (hwf : w ∈ f.val.source)
    (P : ComplexModel n → Prop)
    (hex : ∃ (F : ComplexModel n → ComplexModel n) (D : Set (ComplexModel n)),
      IsOpen D ∧ f.val w ∈ D ∧ D ⊆ f.val.target ∧ ContDiffOn ℂ ∞ F D ∧
      Function.Injective (fderiv ℝ F (f.val w)) ∧
      (∀ z ∈ D, (f.val.symm z ∈ W ↔ F z ∈ complexCoordinatePlane n k)) ∧
      ∀ v : ComplexModel n,
        fderiv ℝ F (f.val w) v ∈ complexCoordinatePlane n k → P v) :
    ∀ (F : ComplexModel n → ComplexModel n) (D : Set (ComplexModel n)),
      IsOpen D → f.val w ∈ D → D ⊆ f.val.target → ContDiffOn ℂ ∞ F D →
      Function.Injective (fderiv ℝ F (f.val w)) →
      (∀ z ∈ D, (f.val.symm z ∈ W ↔ F z ∈ complexCoordinatePlane n k)) →
      ∀ v : ComplexModel n,
        fderiv ℝ F (f.val w) v ∈ complexCoordinatePlane n k → P v := by
  classical
  obtain ⟨-, -, Φ, -, -, hΦflat⟩ := hreg
  have hsymm : f.val.symm (f.val w) = w := f.val.left_inv hwf
  have hz₀ : f.val w ∈ flatChartDomain (complexChartAt (n := n) w) f Φ := by
    refine ⟨f.val.map_source hwf, ?_, ?_⟩
    · rw [hsymm]; exact mem_complexChartAt_source w
    · show (complexChartAt (n := n) w).val (f.val.symm (f.val w)) ∈ Φ.source
      rw [hsymm]; exact Φ.center_mem_source
  have hW : f.val.symm (f.val w) ∈ W := by rw [hsymm]; exact hw
  have hflat : ∀ z ∈ flatChartDomain (complexChartAt (n := n) w) f Φ,
      (f.val.symm z ∈ W ↔
        flatChartMap (complexChartAt (n := n) w) f Φ z ∈ complexCoordinatePlane n k) := by
    intro z hz
    exact hΦflat hz.2.1 (Set.mem_preimage.mp hz.2.2)
  -- both the given and the quantified flattening see the same tangent space
  obtain ⟨F₀, D₀, hD₀, hz₀D₀, -, hF₀c, hF₀inj, hF₀flat, hF₀⟩ := hex
  have hF₀diff : DifferentiableAt ℝ F₀ (f.val w) :=
    ((hF₀c.differentiableOn (by simp)).differentiableAt
      (hD₀.mem_nhds hz₀D₀)).restrictScalars ℝ
  have heq₀ := comap_fderiv_eq_comap_fderiv_flatChartMap (Φ := Φ) (W := W) (k := k)
    hz₀ hW hflat hD₀ hz₀D₀ hF₀diff hF₀inj hF₀flat
  -- the quantified flattening
  intro F D hD hzD _ hFc hFinj hFflat v hv
  have hFdiff : DifferentiableAt ℝ F (f.val w) :=
    ((hFc.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hzD)).restrictScalars ℝ
  have heq := comap_fderiv_eq_comap_fderiv_flatChartMap (Φ := Φ) (W := W) (k := k)
    hz₀ hW hflat hD hzD hFdiff hFinj hFflat
  have hmem : v ∈ (planeSubmodule n k).comap
      (fderiv ℝ F (f.val w) : ComplexModel n →ₗ[ℝ] ComplexModel n) := hv
  rw [heq, ← heq₀] at hmem
  exact hF₀ v hmem

end Transfer

end

end Hironaka.FlatteningTangentSpaceIndependence
