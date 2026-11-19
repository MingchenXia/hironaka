import Hironaka.Resolution.HironakaG4BoundaryDifferentialCriterion

set_option autoImplicit false

/-! Actual relative whole-ideal generators retain their tangent differentials
up to a nonzero scalar. Blueprint: `hironaka-g4-relative-differential-units.tex`.
This is current geometric transport, not a choice of future sharp centres. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators

universe u v

namespace Hironaka.HironakaG4RelativeDifferentialUnits

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences RankDegeneracy
  BlowupTowers HironakaG4BoundaryDifferentialCriterion MonomialPartAlong
  RelativePrincipalizationSpan InvertibleIdealQuotient DerivativeIdeal
  Hironaka.RegularLocusDense

variable {n : ℕ} {X : CMfd.{u} n}

/-- Equality of actual holomorphic germs on the carrier gives equality of
their actual restricted differentials, even for a singular carrier. -/
theorem restrictedDifferential_eq_of_eventuallyEq_on {N : Set X}
    {f g : X → ℂ} {x : X} (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (heq : ∀ᶠ y in 𝓝 x, y ∈ N → f y = g y) :
    restrictedDifferential N f x = restrictedDifferential N g x := by
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hfd := (eventually_differentiableAt_comp_symm e hx hf).self_of_nhds
  have hgd := (eventually_differentiableAt_comp_symm e hx hg).self_of_nhds
  have hhol : HolomorphicAt n (fun y => f y - g y) x := by
    filter_upwards [hf, hg] with y hyf hyg
    exact hyf.sub hyg
  have hI : (vanishingIdeal (n := n) N).mem x (fun y => f y - g y) :=
    ⟨hhol, heq.mono fun _ hy hyN => sub_eq_zero.mpr (hy hyN)⟩
  have hsub : chartDifferential (fun y => f y - g y) x =
      chartDifferential f x - chartDifferential g x := fderiv_sub hfd hgd
  ext v
  have hv := mem_tangentSpaceIn.mp v.property _ hI
  change chartDifferential (fun y => f y - g y) x (v : ComplexModel n) = 0 at hv
  rw [hsub] at hv
  exact sub_eq_zero.mp hv

/-- The actual product rule on the whole tangent space, when the original
equation is a carrier-relative holomorphic multiple of a vanishing generator. -/
theorem restrictedDifferential_eq_smul_of_eventually_mul_on {N : Set X}
    {f g a : X → ℂ} {x : X} (hf : HolomorphicAt n f x)
    (hg : HolomorphicAt n g x) (ha : HolomorphicAt n a x) (hg0 : g x = 0)
    (heq : ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y * g y) :
    restrictedDifferential N f x = a x • restrictedDifferential N g x := by
  rw [restrictedDifferential_eq_of_eventuallyEq_on hf (ha.mul hg) heq]
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have had := (eventually_differentiableAt_comp_symm e hx ha).self_of_nhds
  have hgd := (eventually_differentiableAt_comp_symm e hx hg).self_of_nhds
  have hp := (had.hasFDerivAt.mul hgd.hasFDerivAt).fderiv
  have hfun : ((a ∘ e.val.symm) * (g ∘ e.val.symm)) =
      (fun w => a (e.val.symm w) * g (e.val.symm w)) := by
    funext w
    rfl
  rw [hfun] at hp
  ext v
  have h := DFunLike.congr_fun hp (v : ComplexModel n)
  simpa only [restrictedDifferential, chartDifferential, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, add_apply, smul_apply, Function.comp_apply,
    e.val.left_inv hx, hg0, smul_eq_mul, zero_mul, add_zero, e, Pi.mul_apply,
    Function.comp_def] using h

/-- True whole relative ideal generators differ by a nonzero scalar on the
actual tangent differential. No reduced zero-set comparison is substituted. -/
theorem exists_nonzero_smul_restrictedDifferential_of_same_relative_generator
    {N : Set X} {I : GermIdeal n X} {f g : X → ℂ} {x : X}
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x)
    (hf0 : f x = 0) (hg0 : g x = 0)
    (hF : ∀ v, I.mem x v ↔ HolomorphicAt n v x ∧ IsInSpanOnAt (n := n) N (· = f) x v)
    (hG : ∀ v, I.mem x v ↔ HolomorphicAt n v x ∧ IsInSpanOnAt (n := n) N (· = g) x v)
    (hdg : restrictedDifferential N g x ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ restrictedDifferential N f x = c • restrictedDifferential N g x := by
  have hfI : I.mem x f := (hF f).mpr ⟨hf, isInSpanOnAt_eq_iff.mpr
    ⟨1, holomorphicAt_const 1, Eventually.of_forall fun _ _ => by simp⟩⟩
  have hgI : I.mem x g := (hG g).mpr ⟨hg, isInSpanOnAt_eq_iff.mpr
    ⟨1, holomorphicAt_const 1, Eventually.of_forall fun _ _ => by simp⟩⟩
  obtain ⟨a, ha, hfa⟩ := isInSpanOnAt_eq_iff.mp ((hG f).mp hfI).2
  obtain ⟨b, hb, hgb⟩ := isInSpanOnAt_eq_iff.mp ((hF g).mp hgI).2
  have hdf := restrictedDifferential_eq_smul_of_eventually_mul_on hf hg ha hg0 hfa
  have hdg' := restrictedDifferential_eq_smul_of_eventually_mul_on hg hf hb hf0 hgb
  refine ⟨a x, ?_, hdf⟩
  intro hzero
  have hdf0 : restrictedDifferential N f x = 0 := by
    ext v
    have h := DFunLike.congr_fun hdf v
    simpa only [smul_apply, hzero, smul_eq_mul, zero_mul, zero_apply] using h
  apply hdg
  ext v
  have h := DFunLike.congr_fun hdg' v
  simpa only [smul_apply, hdf0, zero_apply, smul_eq_mul, mul_zero] using h

/-- Finite independent actual residual generator differentials transfer through
the entire relative ideal dictionaries to the same original equations. -/
theorem linearIndependent_restrictedDifferential_of_same_relative_generators
    {N : Set X} {ι : Type v} [Fintype ι] (I : ι → GermIdeal n X)
    (f g : ι → X → ℂ) {x : X}
    (hf : ∀ i, HolomorphicAt n (f i) x) (hg : ∀ i, HolomorphicAt n (g i) x)
    (hf0 : ∀ i, f i x = 0) (hg0 : ∀ i, g i x = 0)
    (hF : ∀ i v, (I i).mem x v ↔
      HolomorphicAt n v x ∧ IsInSpanOnAt (n := n) N (· = f i) x v)
    (hG : ∀ i v, (I i).mem x v ↔
      HolomorphicAt n v x ∧ IsInSpanOnAt (n := n) N (· = g i) x v)
    (hli : LinearIndependent ℂ (fun i => restrictedDifferential N (g i) x)) :
    LinearIndependent ℂ (fun i => restrictedDifferential N (f i) x) := by
  classical
  have hunit (i : ι) := exists_nonzero_smul_restrictedDifferential_of_same_relative_generator
    (hf i) (hg i) (hf0 i) (hg0 i) (hF i) (hG i) (hli.ne_zero i)
  choose c hc hdiff using hunit
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro a ha i
  have hsum : (∑ j, (a j * c j) • restrictedDifferential N (g j) x) = 0 := by
    calc
      _ = ∑ j, a j • restrictedDifferential N (f j) x := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hdiff j, smul_smul]
      _ = 0 := ha
  exact (mul_eq_zero.mp (hli (fun j => a j * c j) hsum i)).resolve_right (hc i)

end

end Hironaka.HironakaG4RelativeDifferentialUnits
