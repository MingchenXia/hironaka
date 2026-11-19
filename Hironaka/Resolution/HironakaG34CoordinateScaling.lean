import Hironaka.Resolution.HironakaActualFlatCoordinateIntrinsicHS
import Hironaka.Resolution.HironakaNormalCrossingsDiagonalLiftOrbits
import Hironaka.Blowup.BlowupRestrictOpen

/-!
# Coordinate scalings at a point as biholomorphisms of opens (brick (b), generic part)

Lane G34 (run 0080, round 11).  Blueprint: `hironaka-g34-resume-coordinate-scaling.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §3.2, §8 item 3 (b), §9.

Let `Φ ∘ e` be holomorphic coordinates at `x₀` (a `LocalHolomorphicEquivAt` after the preferred chart), `O` an
open window of coordinate values inside `Φ.target`, and `a ∈ (ℂ^*)ⁿ`.  The diagonal scaling `z ↦ a · z` of the
coordinates is a biholomorphism `scaleDiffeo` between the opens

  `scaleDomain Φ O a = {y | Φ(e y) ∈ O, a · Φ(e y) ∈ O}`  and  `scaleDomain Φ O a⁻¹`

of the manifold (`(Φ ∘ e)(scaleDiffeo y) = a · (Φ ∘ e)(y)`, `flatMap_scaleDiffeo`).  It preserves every set which
is, inside the window, the preimage of a set invariant under the scaling (`scaleDiffeo_mem_iff`): coordinate
subspaces (`diagonal_mem_coordSubspace_iff`), the zero set of any weight vector
(`diagonal_mem_zeroSet_iff`), in particular the weighted binomial hypersurface
`{z_s + z_t · ∏ z_b^{c_b} = 0}` when `a_s = a_t · ∏ a_b^{c_b}` (`binomial_diagonal`).  These are exactly the
hypotheses of `HironakaG34MaskFoldEquivariance.IsEquivariant` for data described in the coordinates.

## Main results

* `flatMap`, `scaleDomain`, **`scaleDiffeo`**, `flatMap_scaleDiffeo`, `scaleDiffeo_coe`;
* **`scaleDiffeo_mem_iff`**: preservation of coordinate-described scaling-invariant sets;
* `diagonal_mem_coordSubspace_iff`, `diagonal_mem_zeroSet_iff`, `binomial`, `binomial_diagonal`,
  `diagonal_mem_binomialLocus_iff`.

New file; no existing statement changed; no sorry; no axiom.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG34CoordinateScaling
noncomputable section
open NormalCrossings BlowupFlatCoordinates HironakaActualFlatCoordinateIntrinsicHS
  HironakaNormalCrossingsDiagonalLiftOrbits

/-! ### Scaling-invariant sets of coordinate values -/

section Model

variable {n : ℕ}

/-- The coordinatewise inverse of a scaling vector. -/
def invScale (a : Fin n → ℂ) : Fin n → ℂ := fun i => (a i)⁻¹

theorem diagonal_invScale_diagonal {a : Fin n → ℂ} (ha : ∀ i, a i ≠ 0) (z : ComplexModel n) :
    diagonal (invScale a) (diagonal a z) = z := by
  ext i
  simp only [diagonal_apply, invScale, ← mul_assoc, inv_mul_cancel₀ (ha i), one_mul]

theorem diagonal_diagonal_invScale {a : Fin n → ℂ} (ha : ∀ i, a i ≠ 0) (z : ComplexModel n) :
    diagonal a (diagonal (invScale a) z) = z := by
  ext i
  simp only [diagonal_apply, invScale, ← mul_assoc, mul_inv_cancel₀ (ha i), one_mul]

@[simp] theorem invScale_invScale (a : Fin n → ℂ) : invScale (invScale a) = a := by
  funext i; simp [invScale]

theorem invScale_ne_zero {a : Fin n → ℂ} (ha : ∀ i, a i ≠ 0) (i : Fin n) : invScale a i ≠ 0 :=
  inv_ne_zero (ha i)

/-- Coordinate subspaces are invariant under every scaling with nonzero entries. -/
theorem diagonal_mem_coordSubspace_iff {a : Fin n → ℂ} (ha : ∀ i, a i ≠ 0) (S : Finset (Fin n))
    (z : ComplexModel n) : diagonal a z ∈ coordSubspace S ↔ z ∈ coordSubspace S := by
  simp only [coordSubspace, mem_ofPred_eq, diagonal_apply, mul_eq_zero, ha, false_or]

/-- The zero set of a weight vector `f` (`f (a · z) = κ f z`, `κ ≠ 0`) is invariant under the scaling `a`. -/
theorem diagonal_mem_zeroSet_iff {a : Fin n → ℂ} {f : ComplexModel n → ℂ} {κ : ℂ} (hκ : κ ≠ 0)
    (hf : ∀ z, f (diagonal a z) = κ * f z) (z : ComplexModel n) :
    diagonal a z ∈ {z | f z = 0} ↔ z ∈ {z | f z = 0} := by
  simp only [mem_ofPred_eq, hf, mul_eq_zero, hκ, false_or]

/-- The weighted binomial `z_s + z_t · ∏_b z_b^{c_b}`. -/
def binomial (s t : Fin n) (c : Fin n → ℕ) (z : ComplexModel n) : ℂ :=
  z s + z t * ∏ b, z b ^ c b

/-- The binomial is a weight vector for every scaling with `a_s = a_t · ∏ a_b^{c_b}`. -/
theorem binomial_diagonal {s t : Fin n} {c : Fin n → ℕ} {a : Fin n → ℂ}
    (hw : a s = a t * ∏ b, a b ^ c b) (z : ComplexModel n) :
    binomial s t c (diagonal a z) = a s * binomial s t c z := by
  simp only [binomial, diagonal_apply, mul_pow, Finset.prod_mul_distrib, hw]
  ring

/-- The weighted binomial hypersurface is invariant under the weighted scalings. -/
theorem diagonal_mem_binomialLocus_iff {s t : Fin n} {c : Fin n → ℕ} {a : Fin n → ℂ}
    (ha : ∀ i, a i ≠ 0) (hw : a s = a t * ∏ b, a b ^ c b) (z : ComplexModel n) :
    diagonal a z ∈ {z | binomial s t c z = 0} ↔ z ∈ {z | binomial s t c z = 0} :=
  diagonal_mem_zeroSet_iff (ha s) (binomial_diagonal hw) z

end Model

/-! ### The scaling biholomorphism of a coordinate window -/

section Scaling

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {x₀ : M} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))

/-- The coordinates `Φ ∘ e` of a point. -/
def flatMap (y : M) : ComplexModel n := Φ.toFun (chartAt (ComplexModel n) x₀ y)

omit [IsComplexManifold n M] in
theorem continuousOn_flatMap : ContinuousOn (flatMap Φ) (flatDomain Φ) := by
  intro y hy
  have h1 : ContinuousAt (chartAt (ComplexModel n) x₀) y :=
    (chartAt (ComplexModel n) x₀).continuousAt hy.1
  have h2 : ContinuousAt Φ.toFun (chartAt (ComplexModel n) x₀ y) :=
    (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.2)).continuousAt
  exact (h2.comp h1).continuousWithinAt

/-- The domain of the scaling by `a` inside the window `O`. -/
def scaleDomain (O : Opens (ComplexModel n)) (a : Fin n → ℂ) : Opens M :=
  ⟨flatDomain Φ ∩ flatMap Φ ⁻¹' ((O : Set (ComplexModel n)) ∩ diagonal a ⁻¹' O), by
    refine (continuousOn_flatMap Φ).isOpen_inter_preimage (isOpen_flatDomain Φ) ?_
    exact O.isOpen.inter (O.isOpen.preimage (contDiff_diagonal a).continuous)⟩

theorem mem_scaleDomain {O : Opens (ComplexModel n)} {a : Fin n → ℂ} {y : M} :
    y ∈ scaleDomain Φ O a ↔ y ∈ flatDomain Φ ∧ flatMap Φ y ∈ O ∧ diagonal a (flatMap Φ y) ∈ O :=
  Iff.rfl

variable {Φ} (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
  {O : Opens (ComplexModel n)} (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
  {a : Fin n → ℂ} (ha : ∀ i, a i ≠ 0)

/-- The point with coordinates `a · (Φ ∘ e)(y)`. -/
def scaleMap (a : Fin n → ℂ) (y : M) : M :=
  (chartAt (ComplexModel n) x₀).symm (Φ.invFun (diagonal a (flatMap Φ y)))

include hΦsrc hOt in
theorem scaleMap_spec {y : M} (hy : y ∈ scaleDomain Φ O a) :
    scaleMap (Φ := Φ) a y ∈ flatDomain Φ ∧ flatMap Φ (scaleMap (Φ := Φ) a y) = diagonal a (flatMap Φ y) :=
  flatInverse_mem Φ (hOt hy.2.2) hΦsrc

include hΦsrc hOt ha in
theorem scaleMap_mem {y : M} (hy : y ∈ scaleDomain Φ O a) :
    scaleMap (Φ := Φ) a y ∈ scaleDomain Φ O (invScale a) := by
  obtain ⟨h1, h2⟩ := scaleMap_spec hΦsrc hOt hy
  refine ⟨h1, ?_, ?_⟩
  · rw [h2]; exact hy.2.2
  · rw [h2, mem_preimage, diagonal_invScale_diagonal ha]; exact hy.2.1

include hΦsrc hOt ha in
theorem scaleMap_invScale_scaleMap {y : M} (hy : y ∈ scaleDomain Φ O a) :
    scaleMap (Φ := Φ) (invScale a) (scaleMap (Φ := Φ) a y) = y := by
  have h2 := (scaleMap_spec hΦsrc hOt hy).2
  simp only [scaleMap] at h2 ⊢
  rw [h2, diagonal_invScale_diagonal ha]
  exact flatInverse_flat Φ hy.1

include hΦsrc hOt ha in
theorem scaleMap_invScale_mem {y : M} (hy : y ∈ scaleDomain Φ O (invScale a)) :
    scaleMap (Φ := Φ) (invScale a) y ∈ scaleDomain Φ O a := by
  have h := scaleMap_mem hΦsrc hOt (invScale_ne_zero ha) hy
  rwa [invScale_invScale] at h

include hΦsrc hOt ha in
theorem scaleMap_scaleMap_invScale {y : M} (hy : y ∈ scaleDomain Φ O (invScale a)) :
    scaleMap (Φ := Φ) a (scaleMap (Φ := Φ) (invScale a) y) = y := by
  have h := scaleMap_invScale_scaleMap hΦsrc hOt (invScale_ne_zero ha) hy
  rwa [invScale_invScale] at h

include hΦsrc hOt in
private theorem contMDiff_scaleMap :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun y : scaleDomain Φ O a => scaleMap (Φ := Φ) a (y : M)) := by
  have hle : scaleDomain Φ O a ≤ ⟨flatDomain Φ, isOpen_flatDomain Φ⟩ := fun y hy => hy.1
  have hflat : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun y : scaleDomain Φ O a => flatMap Φ (y : M)) :=
    contMDiff_subtype_val.comp ((actualFlatCoordinateDiffeomorph Φ hΦsrc).contMDiff.comp
      (contMDiff_inclusion hle))
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun y : scaleDomain Φ O a =>
        (⟨diagonal a (flatMap Φ (y : M)), hOt y.2.2.2⟩ :
          (⟨Φ.target, Φ.isOpen_target⟩ : Opens (ComplexModel n)))) :=
    BlowupRestrictOpen.contMDiff_opens_mk (V := ⟨Φ.target, Φ.isOpen_target⟩)
      (f := fun y : scaleDomain Φ O a => diagonal a (flatMap Φ (y : M)))
      ((contDiff_diagonal a).contMDiff.comp hflat) (fun y => hOt y.2.2.2)
  exact (contMDiff_actual_flat_inverse Φ hΦsrc).comp hg

end Scaling

section Diffeo

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {x₀ : M}

/-- **The scaling biholomorphism**: `y ↦ (Φ ∘ e)⁻¹ (a · (Φ ∘ e)(y))` from `scaleDomain Φ O a` onto
`scaleDomain Φ O a⁻¹`. -/
def scaleDiffeo {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)}
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    {O : Opens (ComplexModel n)} (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
    {a : Fin n → ℂ} (ha : ∀ i, a i ≠ 0) :
    scaleDomain Φ O a ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ scaleDomain Φ O (invScale a) where
  toFun y := ⟨scaleMap (Φ := Φ) a y, scaleMap_mem hΦsrc hOt ha y.2⟩
  invFun y := ⟨scaleMap (Φ := Φ) (invScale a) y, scaleMap_invScale_mem hΦsrc hOt ha y.2⟩
  left_inv y := Subtype.ext (scaleMap_invScale_scaleMap hΦsrc hOt ha y.2)
  right_inv y := Subtype.ext (scaleMap_scaleMap_invScale hΦsrc hOt ha y.2)
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk (contMDiff_scaleMap hΦsrc hOt)
    fun y => scaleMap_mem hΦsrc hOt ha y.2
  contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk (contMDiff_scaleMap hΦsrc hOt)
    fun y => scaleMap_invScale_mem hΦsrc hOt ha y.2

variable {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)}
  (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
  {O : Opens (ComplexModel n)} (hOt : (O : Set (ComplexModel n)) ⊆ Φ.target)
  {a : Fin n → ℂ} (ha : ∀ i, a i ≠ 0)

theorem scaleDiffeo_coe (y : scaleDomain Φ O a) :
    ((scaleDiffeo hΦsrc hOt ha y : scaleDomain Φ O (invScale a)) : M) = scaleMap (Φ := Φ) a y := rfl

/-- The scaling biholomorphism scales the coordinates. -/
theorem flatMap_scaleDiffeo (y : scaleDomain Φ O a) :
    flatMap Φ ((scaleDiffeo hΦsrc hOt ha y : scaleDomain Φ O (invScale a)) : M) =
      diagonal a (flatMap Φ (y : M)) :=
  (scaleMap_spec hΦsrc hOt y.2).2

/-- **The scaling biholomorphism preserves every coordinate-described, scaling-invariant set**: if inside the
window `A` is the preimage of `B` and `B` is invariant under the scaling `a`, then `scaleDiffeo` preserves `A`
(the form of the hypotheses of `IsEquivariant`). -/
theorem scaleDiffeo_mem_iff {A : Set M} {B : Set (ComplexModel n)}
    (hA : ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → (y ∈ A ↔ flatMap Φ y ∈ B))
    (hB : ∀ z ∈ O, diagonal a z ∈ O → (diagonal a z ∈ B ↔ z ∈ B)) (p : scaleDomain Φ O a) :
    ((scaleDiffeo hΦsrc hOt ha p : scaleDomain Φ O (invScale a)) : M) ∈ A ↔ (p : M) ∈ A := by
  have hq := (scaleDiffeo hΦsrc hOt ha p).2
  rw [hA _ hq.1 hq.2.1, flatMap_scaleDiffeo, hA _ p.2.1 p.2.2.1]
  exact hB _ p.2.2.1 p.2.2.2

end Diffeo

end
end Hironaka.HironakaG34CoordinateScaling
