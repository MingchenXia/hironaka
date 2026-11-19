import Hironaka.Resolution.HironakaG34LocalIdentityCover
import Hironaka.MarkedIdeal.CodimOneSupport
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Resolution.HironakaG8BFamilyEmptyMember
import Hironaka.Resolution.HironakaNormalCrossingsDiagonalLiftOrbits

/-!
# The torus lemma: a germ saturated along the coordinate orbits is a coordinate subspace (brick (c))

Lane G34 (run 0080, round 11).  Blueprint: `hironaka-g34-resume-torus-lemma.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §3.4, §8 item 3 (c), §9.

Let `w : M → ℂⁿ` be coordinate functions on a complex manifold `M` (every coordinate locus
`L_B = {w_l = 0, l ∈ B}` analytic and regular of dimension `n - |B|` near `x`), and let `C` be an analytic
germ, regular at `x`, which is SATURATED ALONG THE COORDINATE ORBITS near its points: every point `q'`
close to a point `q ∈ C` whose coordinates vanish wherever those of `q` vanish lies in `C`.  Then `C` is,
near `x`, the coordinate locus `L_B` cut out by the coordinates that vanish identically on the germ
(`eventually_mem_iff_coordLocus_of_orbit`).  No torus appears in this statement: in the application the
saturation is the invariance of `C` under the (lifted) diagonal scalings `w ↦ τ · w`, `τ` near `1`
(`orbit_of_scaling_invariant`: for `q'` near `q` with the vanishing pattern of `q`, the ratio
`τ_l = q'_l / q_l` is near `1` and `τ · q = q'`).

Proof.  `B` := coordinates vanishing on the germ of `C`; `C ⊆ L_B` near `x`.  By the held identity cover
(`HironakaG34LocalIdentityCover.exists_eventually_subset_of_cover`) points `q ∈ C` with `w_l(q) ≠ 0` for
every `l ∉ B` accumulate at `x`; at such a `q` saturation gives `L_B ⊆ C` near `q`, so `C = L_B` near `q`
and the dimension of `C` is `n - |B|`; same-dimension filling (`eventually_subset_of_same_dim`) at `x`
then gives `L_B ⊆ C` near `x`.

## Main results

* `coordLocus w B`;
* **`eventually_mem_iff_coordLocus_of_orbit`** (manifold form, abstract coordinates);
* `orbit_of_scaling_invariant` (scaling invariance near `1` ⟹ saturation, on an open of `ℂⁿ`);
* **`eventually_mem_iff_coordSubspace_of_scaling_invariant`** (model form on an open `Ω ⊆ ℂⁿ`).

New file; no existing statement changed; no sorry; no axiom.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold
namespace Hironaka.HironakaG34TorusLemma
noncomputable section
open NormalCrossings HironakaNormalCrossingsDiagonalLiftOrbits

/-! ### Manifold form -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The coordinate locus `{y | w y l = 0 for every l ∈ B}` of coordinate functions `w`. -/
def coordLocus (w : M → ComplexModel n) (B : Finset (Fin n)) : Set M :=
  {y | ∀ l ∈ B, w y l = 0}

/-- **The torus lemma (manifold form).**  An analytic germ `(C, x)`, regular at `x` and saturated along
the coordinate orbits near its points, is the coordinate locus of the coordinates vanishing on it. -/
theorem eventually_mem_iff_coordLocus_of_orbit {C : Set M} {x : M} {k : ℕ} (w : M → ComplexModel n)
    (hCan : IsComplexAnalyticSubset (n := n) C) (hx : RegularAtDim (n := n) C x k)
    (hL : ∀ B : Finset (Fin n), IsComplexAnalyticSubset (n := n) (coordLocus w B))
    (hLreg : ∀ B : Finset (Fin n), ∀ᶠ y in 𝓝 x, y ∈ coordLocus w B →
      RegularAtDim (n := n) (coordLocus w B) y (n - B.card))
    (horbit : ∀ᶠ q in 𝓝 x, q ∈ C →
      ∀ᶠ q' in 𝓝 q, (∀ l, w q l = 0 → w q' l = 0) → q' ∈ C) :
    ∃ B : Finset (Fin n), (∀ l ∈ B, w x l = 0) ∧ ∀ᶠ y in 𝓝 x, y ∈ C ↔ y ∈ coordLocus w B := by
  classical
  let B : Finset (Fin n) := Finset.univ.filter fun l => ∀ᶠ y in 𝓝 x, y ∈ C → w y l = 0
  have hB : ∀ l ∈ B, ∀ᶠ y in 𝓝 x, y ∈ C → w y l = 0 := fun l hl => (Finset.mem_filter.mp hl).2
  have hsub : ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ coordLocus w B := by
    filter_upwards [(Filter.eventually_all_finset B).2 hB] with y hy hyC l hl using hy l hl hyC
  -- generic points of `C` accumulate at `x`
  have hfreq : ∃ᶠ q in 𝓝 x, q ∈ C ∧ ∀ l, l ∉ B → w q l ≠ 0 := by
    intro hev
    have hcov : ∀ᶠ q in 𝓝 x, q ∈ C → ∃ l : {l : Fin n // l ∉ B}, q ∈ coordLocus w {l.1} := by
      filter_upwards [hev] with q hq hqC
      have : ∃ l, l ∉ B ∧ w q l = 0 := by
        by_contra hcon
        push Not at hcon
        exact hq ⟨hqC, hcon⟩
      obtain ⟨l, hl, hql⟩ := this
      exact ⟨⟨l, hl⟩, fun l' hl' => by rw [Finset.mem_singleton.mp hl']; exact hql⟩
    obtain ⟨⟨l, hl⟩, hl'⟩ := HironakaG34LocalIdentityCover.exists_eventually_subset_of_cover hx
      (fun l : {l : Fin n // l ∉ B} => coordLocus w {l.1}) (fun l => hL _) hcov
    apply hl
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    filter_upwards [hl'] with y hy hyC
    exact hy hyC l (Finset.mem_singleton_self l)
  obtain ⟨q, ⟨hqC, hqgen⟩, hqsub, hqreg, hqorb, hqsub', hqL⟩ :=
    (hfreq.and_eventually (hsub.and
      ((RegularPatchNeighborhood.eventually_regularAtDim hx).and
        (horbit.and ((eventually_eventually_nhds.mpr hsub).and (hLreg B)))))).exists
  have hqLB : q ∈ coordLocus w B := hqsub hqC
  have hpat : ∀ l, w q l = 0 → l ∈ B := by
    intro l hl
    by_contra hlB
    exact hqgen l hlB hl
  have hiff : ∀ᶠ q' in 𝓝 q, q' ∈ coordLocus w B ↔ q' ∈ C := by
    filter_upwards [hqorb hqC, hqsub'] with q' h1 h2
    exact ⟨fun hq' => h1 fun l hl => hq' l (hpat l hl), h2⟩
  have hk : k = n - B.card :=
    RegularPointDimension.eq_of_regularAtDim (hqreg hqC)
      (CodimOneSupport.regularAtDim_of_eventually_mem_iff hiff (hqL hqLB))
  have hLk : ∀ᶠ y in 𝓝 x, y ∈ coordLocus w B → RegularAtDim (n := n) (coordLocus w B) y k := by
    rw [hk]
    exact hLreg B
  have hfill := HironakaG34LocalIdentityCover.eventually_subset_of_same_dim hCan (hL B) hx hLk hsub
  refine ⟨B, fun l hl => hsub.self_of_nhds hx.2.1 l hl, ?_⟩
  filter_upwards [hsub, hfill] with y h1 h2
  exact ⟨h1, h2⟩

end Manifold

/-! ### Model form: scalings of an open of `ℂⁿ` -/

section Model

variable {n : ℕ}

/-- The ratio scaling taking `q` to `q'` on the coordinates where `q` does not vanish. -/
def ratioScale (q q' : ComplexModel n) : Fin n → ℂ := fun l => if q l = 0 then 1 else q' l / q l

theorem diagonal_ratioScale {q q' : ComplexModel n} (h : ∀ l, q l = 0 → q' l = 0) :
    diagonal (ratioScale q q') q = q' := by
  ext l
  simp only [diagonal_apply, ratioScale]
  by_cases hl : q l = 0
  · rw [if_pos hl, hl, h l hl, mul_zero]
  · rw [if_neg hl, div_mul_cancel₀ _ hl]

theorem tendsto_ratioScale (q : ComplexModel n) :
    Tendsto (fun q' : ComplexModel n => ratioScale q q') (𝓝 q) (𝓝 (1 : Fin n → ℂ)) := by
  refine tendsto_pi_nhds.2 fun l => ?_
  simp only [ratioScale, Pi.one_apply]
  by_cases hl : q l = 0
  · simp only [if_pos hl]
    exact tendsto_const_nhds
  · simp only [if_neg hl]
    have hc : Continuous fun q' : ComplexModel n => q' l / q l :=
      ((EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).continuous).div_const _
    have := hc.tendsto q
    simp only [div_self hl] at this
    exact this

/-- **Scaling invariance near `1` gives saturation along the coordinate orbits** (on an open `Ω ⊆ ℂⁿ`):
if every scaling `τ · q` with `τ` near `1` (inside `Ω`) of a point `q ∈ C` lies in `C`, then every point
near `q` with the vanishing pattern of `q` lies in `C`. -/
theorem orbit_of_scaling_invariant {Ω : Opens (ComplexModel n)} {C : Set Ω} {q : Ω}
    (hinv : ∀ᶠ τ in 𝓝 (1 : Fin n → ℂ), ∀ q' : Ω, (q' : ComplexModel n) = diagonal τ q → q' ∈ C) :
    ∀ᶠ (q' : Ω) in 𝓝 q, (∀ l, (q : ComplexModel n) l = 0 → (q' : ComplexModel n) l = 0) → q' ∈ C := by
  have ht : Tendsto (fun q' : Ω => ratioScale (q : ComplexModel n) q') (𝓝 q) (𝓝 1) :=
    (tendsto_ratioScale (q : ComplexModel n)).comp continuous_subtype_val.continuousAt
  filter_upwards [ht.eventually hinv] with q' hq' hpat
  exact hq' q' (diagonal_ratioScale hpat).symm

/-- **The torus lemma (model form).**  On an open `Ω ⊆ ℂⁿ`, an analytic germ `(C, p)`, regular at `p` and
invariant near its points under the diagonal scalings near `1`, is a coordinate subspace near `p`, cut out by
coordinates vanishing at `p`. -/
theorem eventually_mem_iff_coordSubspace_of_scaling_invariant {Ω : Opens (ComplexModel n)} {C : Set Ω}
    {p : Ω} {k : ℕ} (hCan : IsComplexAnalyticSubset (n := n) C) (hp : RegularAtDim (n := n) C p k)
    (hinv : ∀ᶠ q in 𝓝 p, q ∈ C → ∀ᶠ τ in 𝓝 (1 : Fin n → ℂ),
      ∀ q' : Ω, (q' : ComplexModel n) = diagonal τ q → q' ∈ C) :
    ∃ B : Finset (Fin n), (∀ l ∈ B, (p : ComplexModel n) l = 0) ∧
      ∀ᶠ y in 𝓝 p, y ∈ C ↔ (y : ComplexModel n) ∈ coordSubspace B := by
  have hL : ∀ B : Finset (Fin n),
      IsComplexAnalyticSubset (n := n) (coordLocus (Subtype.val : Ω → ComplexModel n) B) := fun B =>
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
        (HironakaG8BFamilyEmptyMember.isClosedSubmanifold_coordSubspace B)) Ω
  have hLreg : ∀ B : Finset (Fin n), ∀ᶠ y in 𝓝 p, y ∈ coordLocus (Subtype.val : Ω → ComplexModel n) B →
      RegularAtDim (n := n) (coordLocus (Subtype.val : Ω → ComplexModel n) B) y (n - B.card) :=
    fun B => Eventually.of_forall fun y hy =>
      AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
        (HironakaG8BFamilyEmptyMember.regularAtDim_coordSubspace B hy)
  have horbit : ∀ᶠ q in 𝓝 p, q ∈ C → ∀ᶠ (q' : Ω) in 𝓝 q,
      (∀ l, (q : ComplexModel n) l = 0 → (q' : ComplexModel n) l = 0) → q' ∈ C := by
    filter_upwards [hinv] with q hq hqC
    exact orbit_of_scaling_invariant (hq hqC)
  exact eventually_mem_iff_coordLocus_of_orbit Subtype.val hCan hp hL hLreg horbit

end Model

end
end Hironaka.HironakaG34TorusLemma
