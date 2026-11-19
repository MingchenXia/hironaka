import Hironaka.Analytic.Unibranch.HironakaG10OneParameterFlatOpen
import Hironaka.Resolution.HironakaG10FlatTorsionFiltration
import Hironaka.Analytic.HolomorphicGermNoetherian

/-!
# Generic flatness over a smooth base, I: one parameter (lane G10GF, run 0081, plan item G10-03-05.c1)

Frisch 1967, Prop. (IV,14) (`references/frisch67-points-platitude`, p. 135: over a reduced base the image of the
non-flat locus is negligible) is reduced at regular points of the base to a smooth parameter space, where it is
proved by slicing one parameter at a time.  This module is the one-parameter step, for a finite holomorphic
matrix `M` on `ℂ × ℂᴺ` (first coordinate `t` = the parameter), in the Tor₁ form of the library
(`HironakaG10LocFibreOpen.FibreFlatAt`):

* `fibreFlatAt_iff_regularAt_sub`: one-parameter flatness at `(s, z)` is regularity of `t − s` on `coker M`
  (recentring of `HironakaG10FibreRegularCriterion.fibreFlatAt_iff_coordinate_regular`);
* **`eventually_regularAt_sub` (local verticality)**: near any point `(w₀, q₀)`, every point `p` with
  `p.1 ≠ w₀` has `t − p.1` regular on `coker M` at `p`.  Proof: the `(t − w₀)`-torsion filtration
  (`HironakaG10FlatTorsionFiltration.exists_torsionFiltration`, Noetherian germs) gives `T` with
  `(t − w₀)^{j₀} T ⊆ im M` and `t − w₀` regular on `coker [M | T]`; the latter is one-parameter flat at
  `(w₀, q₀)`, hence nearby (Douady openness, `HironakaG10LocEuclideanCartan.isOpen_fibreFlatAt`); off
  `t = w₀` the factor `(t − w₀)^{j₀}` is a unit, so `im [M | T] = im M` there;
* **`eventually_forall_regularAt_sub` (vertical avoidance)**: for a compact `L ⊆ ℂᴺ`, regularity holds on
  `{w} × L` for every `w ≠ w₀` near `w₀`;
* `exactStartOn_slice_at`: an exact start restricts to the slice `t = w` where `t − w` is regular
  (translation of `HironakaG10FlatSliceResolution.exactStartOn_slice`).

No named input; only library theorems.  Blueprint: `hironaka-g10gf-smooth-base.tex`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GfVertical

noncomputable section

open Hironaka OkaRelationSheaf OkaGermBridge HironakaG10FlatResolutionStart
  HironakaG10FlatSliceResolution HironakaG10FlatTorsionFiltration HironakaG10FlatExtensionStep
  HironakaG10FlatPrivilegedNbhd HironakaG10LocFibreOpen HironakaG10FibreRegularCriterion
  HironakaG10FlatRelationLift Hironaka.Analytic.Unibranch.HironakaG10OneParameterFlatOpen

/-! ## Translation in the parameter -/

section Translation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] {a b : ℕ}

theorem differentiableAt_shift (s : ℂ) (p : ℂ × P) : DifferentiableAt ℂ (shift s) p :=
  ((differentiableAt_const s).add differentiableAt_fst).prodMk differentiableAt_snd

theorem differentiableAt_shift_symm (s : ℂ) (p : ℂ × P) : DifferentiableAt ℂ (shift s).symm p :=
  ((differentiableAt_const (-s)).add differentiableAt_fst).prodMk differentiableAt_snd

theorem holAt_recenterMatrix (M : Fin a → Fin b → ℂ × P → ℂ) (s : ℂ) (z : P)
    (hM : ∀ i j, HolAt (M i j) (s, z)) : ∀ i j, HolAt (recenterMatrix M s i j) ((0 : ℂ), z) := by
  intro i j
  have hp : shift s ((0 : ℂ), z) = (s, z) := by simp
  have h : HolAt (M i j) (shift s ((0 : ℂ), z)) := by rw [hp]; exact hM i j
  exact h.comp (shift s).continuous (differentiableAt_shift s)

/-- **One-parameter flatness at `(s, z)` is regularity of `t − s` on the cokernel.** -/
theorem fibreFlatAt_iff_regularAt_sub (hX : OkaProperty (ℂ × P)) (M : Fin a → Fin b → ℂ × P → ℂ)
    {s : ℂ} {z : P} (hM : ∀ i j, HolAt (M i j) (s, z)) :
    FibreFlatAt M (s, z) ↔ RegularAt M (fun x => x.1 - s) (s, z) := by
  rw [← fibreFlatAt_recenter_iff M s z,
    fibreFlatAt_iff_coordinate_regular hX (recenterMatrix M s) z (holAt_recenterMatrix M s z hM)]
  constructor
  · intro h
    have hp : shift (-s) (s, z) = ((0 : ℂ), z) := by simp
    have h' : RegularAt (recenterMatrix M s) (fun x => x.1) (shift (-s) (s, z)) := by
      rw [hp]; exact h
    have h2 := regularAt_comp_homeomorph (X := ℂ × P) (Y := ℂ × P) (shift (-s))
      (differentiableAt_shift (-s)) (differentiableAt_shift_symm (-s)) h'
    have e1 : (fun i j => recenterMatrix M s i j ∘ shift (-s)) = M := by
      funext i j x
      simp [recenterMatrix]
    have e2 : ((fun x : ℂ × P => x.1) ∘ shift (-s)) = fun x => x.1 - s := by
      funext x
      simp only [Function.comp_apply, shift_apply]
      ring
    rw [e1, e2] at h2
    exact h2
  · intro h
    have hp : shift s ((0 : ℂ), z) = (s, z) := by simp
    have h' : RegularAt M (fun x => x.1 - s) (shift s ((0 : ℂ), z)) := by
      rw [hp]; exact h
    have h2 := regularAt_comp_homeomorph (X := ℂ × P) (Y := ℂ × P) (shift s)
      (differentiableAt_shift s) (differentiableAt_shift_symm s) h'
    have e2 : ((fun x : ℂ × P => x.1 - s) ∘ shift s) = fun x => x.1 := by
      funext x
      simp only [Function.comp_apply, shift_apply]
      ring
    rw [e2] at h2
    exact h2

variable {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- **An exact start restricts to the slice `t = w`** where `t − w` is regular on the cokernel. -/
theorem exactStartOn_slice_at {U : Set (ℂ × P)} {G : ι₁ → ι₂ → ℂ × P → ℂ} {F : ι₀ → ι₁ → ℂ × P → ℂ}
    (h : ExactStartOn U G F) (hU : IsOpen U) (w : ℂ)
    (hreg : ∀ z : P, (w, z) ∈ U → RegularAt F (fun x => x.1 - w) (w, z)) :
    ExactStartOn {z : P | (w, z) ∈ U} (fun j k z => G j k (w, z)) (fun i j z => F i j (w, z)) := by
  have h1 := exactStartOn_comp_homeomorph (shift w) (differentiableAt_shift w)
    (differentiableAt_shift_symm w) h
  have hU1 : IsOpen (shift w ⁻¹' U) := hU.preimage (shift w).continuous
  have hreg1 : ∀ z : P, ((0 : ℂ), z) ∈ shift w ⁻¹' U →
      RegularAt (fun i j => F i j ∘ shift w) (fun x => x.1) ((0 : ℂ), z) := by
    intro z hz
    have hp : shift w ((0 : ℂ), z) = (w, z) := by simp
    have hz' : (w, z) ∈ U := by rw [← hp]; exact hz
    have hr : RegularAt F (fun x => x.1 - w) (shift w ((0 : ℂ), z)) := by
      rw [hp]; exact hreg z hz'
    have h2 := regularAt_comp_homeomorph (X := ℂ × P) (Y := ℂ × P) (shift w)
      (differentiableAt_shift w) (differentiableAt_shift_symm w) hr
    have e : ((fun x : ℂ × P => x.1 - w) ∘ shift w) = fun x => x.1 := by
      funext x
      simp only [Function.comp_apply, shift_apply]
      ring
    rw [e] at h2
    exact h2
  have h3 := exactStartOn_slice h1 hU1 hreg1
  have eS : {z : P | ((0 : ℂ), z) ∈ shift w ⁻¹' U} = {z : P | (w, z) ∈ U} := by
    ext z
    simp
  have eG : sliceZero (fun j k => G j k ∘ shift w) = fun j k z => G j k (w, z) := by
    funext j k z
    simp [sliceZero]
  have eF : sliceZero (fun i j => F i j ∘ shift w) = fun i j z => F i j (w, z) := by
    funext i j z
    simp [sliceZero]
  rw [eS, eG, eF] at h3
  exact h3

end Translation

/-! ## Columns already in the image -/

section Combination

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Columns of `T` that are combinations of the columns of `A` add nothing to `im A`. -/
theorem isCombinationAt_of_catCols {a b t : ℕ} {A : Fin a → Fin b → X → ℂ}
    {T : Fin a → Fin t → X → ℂ} {y : X} (hA : ∀ i j, HolAt (A i j) y) (hT : ∀ i k, HolAt (T i k) y)
    (hTA : ∀ k, IsCombinationAt (columns A) y (columns T k)) {v : Fin a → X → ℂ}
    (hv : ∀ i, HolAt (v i) y) (h : IsCombinationAt (columns (catCols A T)) y v) :
    IsCombinationAt (columns A) y v := by
  have hAT := holAt_catCols hA hT
  have hJ : imSubmodule (catCols A T) y ≤ imSubmodule A y := by
    rw [imSubmodule, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨k', rfl⟩ := finSumFinEquiv.surjective k
    rcases k' with k' | k'
    · show germVec y (columns (catCols A T) (finSumFinEquiv (Sum.inl k'))) ∈ _
      have heq : germVec y (columns (catCols A T) (finSumFinEquiv (Sum.inl k'))) =
          germVec y (columns A k') := by
        funext i; simp [germVec, columns, catCols]
      rw [heq]
      exact Submodule.subset_span ⟨k', rfl⟩
    · show germVec y (columns (catCols A T) (finSumFinEquiv (Sum.inr k'))) ∈ _
      have heq : germVec y (columns (catCols A T) (finSumFinEquiv (Sum.inr k'))) =
          germVec y (columns T k') := by
        funext i; simp [germVec, columns, catCols]
      rw [heq]
      exact (germVec_mem_imSubmodule_iff hA fun i => hT i k').2 (hTA k')
  exact (germVec_mem_imSubmodule_iff hA hv).1 (hJ ((germVec_mem_imSubmodule_iff hAT hv).2 h))

end Combination

/-! ## Local verticality of the one-parameter non-flat locus -/

section Vertical

variable {N : ℕ}

/-- Holomorphic germs on `ℂ × ℂᴺ` form a Noetherian ring. -/
theorem isNoetherianRing_holGerm_prod_euclidean (N : ℕ) :
    IsNoetherianRing (HolGerm (ℂ × EuclideanSpace ℂ (Fin N))) := by
  have hr : Module.finrank ℂ (ℂ × EuclideanSpace ℂ (Fin N)) =
      Module.finrank ℂ (EuclideanSpace ℂ (Fin (N + 1))) := by
    rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin, add_comm]
  let e : (ℂ × EuclideanSpace ℂ (Fin N)) ≃L[ℂ] EuclideanSpace ℂ (Fin (N + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq hr
  have := isNoetherianRing_holGerm_euclidean (N + 1)
  exact isNoetherianRing_of_ringEquiv _ (HolGerm.comapEquiv e)

/-- **Local verticality**: near `(w₀, q₀)`, every point `p` off the slice `t = w₀` has `t − p.1` regular on
`coker M` at `p`, i.e. `coker M` is flat over the parameter line there. -/
theorem eventually_regularAt_sub {a b : ℕ} (M : Fin a → Fin b → ℂ × EuclideanSpace ℂ (Fin N) → ℂ)
    {w₀ : ℂ} {q₀ : EuclideanSpace ℂ (Fin N)} (hM : ∀ i j, HolAt (M i j) (w₀, q₀)) :
    ∀ᶠ p in 𝓝 (w₀, q₀), p.1 ≠ w₀ → RegularAt M (fun x => x.1 - p.1) p := by
  have := isNoetherianRing_holGerm_prod_euclidean N
  have hX := HironakaG10FlatRelationLift.okaProperty_prod_euclidean N
  have hφ : HolAt (fun x : ℂ × EuclideanSpace ℂ (Fin N) => x.1 - w₀) (w₀, q₀) :=
    Eventually.of_forall fun _ => differentiableAt_fst.sub (differentiableAt_const _)
  obtain ⟨t, j₀, T, hT, hTk, hreg⟩ := exists_torsionFiltration hM hφ
  have hMT := holAt_catCols hM hT
  have hflat₀ : FibreFlatAt (catCols M T) (w₀, q₀) :=
    (fibreFlatAt_iff_regularAt_sub hX (catCols M T) hMT).2 hreg
  have hopen : ∀ᶠ p in 𝓝 (w₀, q₀), FibreFlatAt (catCols M T) p :=
    (HironakaG10LocEuclideanCartan.isOpen_fibreFlatAt (catCols M T)).mem_nhds hflat₀
  have hholMT : ∀ᶠ p in 𝓝 (w₀, q₀), ∀ i j, HolAt (catCols M T i j) p :=
    eventually_all.2 fun i => eventually_all.2 fun j => (hMT i j).eventually
  have hholM : ∀ᶠ p in 𝓝 (w₀, q₀), ∀ i j, HolAt (M i j) p :=
    eventually_all.2 fun i => eventually_all.2 fun j => (hM i j).eventually
  have hholT : ∀ᶠ p in 𝓝 (w₀, q₀), ∀ i k, HolAt (T i k) p :=
    eventually_all.2 fun i => eventually_all.2 fun k => (hT i k).eventually
  choose c hc hceq using hTk
  have hholc : ∀ᶠ p in 𝓝 (w₀, q₀), ∀ k l, HolAt (c k l) p :=
    eventually_all.2 fun k => eventually_all.2 fun l => (hc k l).eventually
  have heq : ∀ᶠ p in 𝓝 (w₀, q₀), ∀ k i,
      (fun x : ℂ × EuclideanSpace ℂ (Fin N) => (x.1 - w₀) ^ j₀ * T i k x) =ᶠ[𝓝 p]
        fun x => ∑ l, c k l x * columns M l i x :=
    eventually_all.2 fun k => eventually_all.2 fun i => (hceq k i).eventuallyEq_nhds
  filter_upwards [hopen, hholMT, hholM, hholT, hholc, heq] with p hpflat hpMT hpM hpT hpc hpeq hne
  rcases p with ⟨s, z⟩
  have hregT : RegularAt (catCols M T) (fun x => x.1 - s) (s, z) :=
    (fibreFlatAt_iff_regularAt_sub hX (catCols M T) hpMT).1 hpflat
  have hφs : HolAt (fun x : ℂ × EuclideanSpace ℂ (Fin N) => x.1 - w₀) (s, z) :=
    Eventually.of_forall fun _ => differentiableAt_fst.sub (differentiableAt_const _)
  have hφp : (s, z).1 - w₀ ≠ 0 := sub_ne_zero.2 hne
  have hφpow : HolAt (fun x : ℂ × EuclideanSpace ℂ (Fin N) => ((x.1 - w₀) ^ j₀)⁻¹) (s, z) :=
    (holAt_pow hφs j₀).inv (pow_ne_zero _ hφp)
  have hne' : ∀ᶠ x in 𝓝 (s, z), (x : ℂ × EuclideanSpace ℂ (Fin N)).1 - w₀ ≠ 0 :=
    hφs.continuousAt.eventually_ne hφp
  have hTA : ∀ k, IsCombinationAt (columns M) (s, z) (columns T k) := by
    intro k
    refine ⟨fun l x => c k l x * ((x.1 - w₀) ^ j₀)⁻¹, fun l => (hpc k l).mul hφpow, fun i => ?_⟩
    filter_upwards [hpeq k i, hne'] with x hx hx0
    simp only [columns] at hx ⊢
    have hpow : (x.1 - w₀) ^ j₀ ≠ 0 := pow_ne_zero _ hx0
    calc T i k x = ((x.1 - w₀) ^ j₀)⁻¹ * ((x.1 - w₀) ^ j₀ * T i k x) := by
          rw [← mul_assoc, inv_mul_cancel₀ hpow, one_mul]
      _ = ∑ l, c k l x * ((x.1 - w₀) ^ j₀)⁻¹ * M i l x := by
          rw [hx, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
  intro d hd hφd
  exact isCombinationAt_of_catCols hpM hpT hTA hd (hregT d hd (isCombinationAt_catCols_left T hφd))

/-- **Vertical avoidance**: for a compact `L`, regularity of `t − w` holds on `{w} × L` for all `w ≠ w₀`
near `w₀`. -/
theorem eventually_forall_regularAt_sub {a b : ℕ}
    (M : Fin a → Fin b → ℂ × EuclideanSpace ℂ (Fin N) → ℂ) {w₀ : ℂ}
    {L : Set (EuclideanSpace ℂ (Fin N))} (hL : IsCompact L)
    (hM : ∀ u ∈ L, ∀ i j, HolAt (M i j) (w₀, u)) :
    ∀ᶠ w in 𝓝 w₀, w ≠ w₀ → ∀ u ∈ L, RegularAt M (fun x => x.1 - w) (w, u) := by
  let D : Set (ℂ × EuclideanSpace ℂ (Fin N)) :=
    {p | p.1 ≠ w₀ → RegularAt M (fun x => x.1 - p.1) p}
  have hD : ∀ u ∈ L, (w₀, u) ∈ interior D := fun u hu =>
    mem_interior_iff_mem_nhds.2 (eventually_regularAt_sub M (hM u hu))
  filter_upwards [HironakaG10LocEuclideanCartan.eventually_forall_mem_of_isOpen hL isOpen_interior hD]
    with w hw hne u hu
  exact interior_subset (hw u hu) hne

end Vertical

end

end Hironaka.Analytic.Unibranch.HironakaG10GfVertical
