import Hironaka.Analytic.Unibranch.HironakaG10LfChartAlgebra
import Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily
import Hironaka.Analytic.Unibranch.HironakaG10SmoothProjectionFlat

/-!
# Item 1b, analytic dictionary: the slice restriction of product germs (lane G10LF)

`R = 𝒪_{ℂ^d × ℂ^t, 0}` over `A = 𝒪_{ℂ^d, 0}` by the first-projection pullback `basePullback`:
* `A`, `R` are Noetherian local, `basePullback` is local and flat (`basePullback_flat`, from the
  library's `tangentPullback_flat` through `ambientGermEquiv`);
* the slice restriction `sliceHom : R → 𝒪_{ℂ^t,0}` (`f ↦ f(0, ·)`) is surjective with kernel exactly
  `𝔪_A R` (`ker_sliceHom`, from the library's `baseMaximalIdeal_eq_ker_jointBaseZeroTrace`), and it
  carries the germ matrix at `p` to the fibre germ matrix at `p.2` (`germ_matrix_map_sliceHom`);
* exactness modulo `ker σ` of a start over `R` is matrix exactness of its image (`sliceExact_iff_matExact`).

BP: hironaka-g10lf-local-flatness.tex. No named input.
-/

set_option autoImplicit false

open Set Filter Function
open scoped Topology Matrix

namespace Hironaka.Analytic.Unibranch.HironakaG10LfChart

noncomputable section

open Hironaka Hironaka HolGerm OkaRelationSheaf
  OkaGermBridge HironakaG10FlatGermChain HironakaG10LocSheafExact HironakaG10LocFibreOpen
  HironakaRelativeNormalIdeal HironakaRelativeNormalFibreHilbertSamuel HironakaActualJointBaseFibre
  HironakaActualCentreJointJets HironakaHolomorphicJetChartInvariance
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen

/-! ### Exactness modulo a kernel -/

/-- A start over `R` is exact modulo `ker σ` iff its image under a surjective `σ` is exact. -/
theorem sliceExact_iff_matExact {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S)
    (hσ : Surjective σ) {a b c : ℕ} (F : Matrix (Fin a) (Fin b) R) (G : Matrix (Fin b) (Fin c) R) :
    (∀ v : Fin b → R, (∀ i, (F *ᵥ v) i ∈ RingHom.ker σ) →
      ∃ w : Fin c → R, ∀ j, (v - G *ᵥ w) j ∈ RingHom.ker σ) ↔
      MatExact (G.map σ) (F.map σ) := by
  have hmv : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (v : Fin n → R),
      M.map σ *ᵥ (σ ∘ v) = σ ∘ (M *ᵥ v) := by
    intro m n M v
    funext i
    exact (RingHom.map_mulVec σ M v i).symm
  constructor
  · intro h v' hv'
    choose v hv using fun j => hσ (v' j)
    have hvv : σ ∘ v = v' := funext hv
    have hF : ∀ i, (F *ᵥ v) i ∈ RingHom.ker σ := by
      intro i
      rw [RingHom.mem_ker]
      have h1 := congrFun hv' i
      rw [← hvv, hmv] at h1
      exact h1
    obtain ⟨w, hw⟩ := h v hF
    refine ⟨σ ∘ w, ?_⟩
    rw [hmv, ← hvv]
    funext j
    have h1 := hw j
    rw [RingHom.mem_ker, Pi.sub_apply, map_sub, sub_eq_zero] at h1
    exact h1.symm
  · intro h v hv
    have h0 : F.map σ *ᵥ (σ ∘ v) = 0 := by
      rw [hmv]
      funext i
      exact hv i
    obtain ⟨c', hc'⟩ := h _ h0
    choose w hw using fun k => hσ (c' k)
    have hww : σ ∘ w = c' := funext hw
    refine ⟨w, fun j => ?_⟩
    rw [RingHom.mem_ker, Pi.sub_apply, map_sub, sub_eq_zero]
    have h1 := congrFun hc' j
    rw [← hww, hmv] at h1
    exact h1.symm

/-! ### The germ rings -/

theorem isNoetherianRing_base (d : ℕ) : IsNoetherianRing (HolGerm (ComplexModel d)) :=
  isNoetherianRing_holGerm_euclidean d

theorem isNoetherianRing_prod (d t : ℕ) :
    IsNoetherianRing (HolGerm (ComplexModel d × ComplexModel t)) := by
  have := isNoetherianRing_holGerm_euclidean (d + t)
  exact isNoetherianRing_of_ringEquiv _ (ambientGermEquiv d t)

theorem isLocalHom_basePullback (d t : ℕ) : IsLocalHom (basePullback d t) := by
  constructor
  intro a ha
  rw [HolGerm.isUnit_iff_eval_ne_zero] at ha ⊢
  unfold basePullback at ha
  rwa [HolGerm.eval_comap] at ha

theorem basePullback_eq_comp (d t : ℕ) :
    basePullback d t = (ambientGermEquiv d t).toRingHom.comp (tangentPullback d t).toRingHom :=
  RingHom.ext fun a => (ambientGermEquiv_tangentPullback d t a).symm

theorem basePullback_flat (d t : ℕ) : (basePullback d t).Flat := by
  rw [basePullback_eq_comp]
  exact (Hironaka.Analytic.Unibranch.HironakaG10SmoothProjectionFlat.tangentPullback_flat d t).comp
    (RingHom.Flat.of_bijective (ambientGermEquiv d t).bijective)

/-! ### The slice restriction -/

/-- Restriction of product germs to the slice `{0} × ℂ^t`. -/
def sliceHom (d t : ℕ) : HolGerm (ComplexModel d × ComplexModel t) →+* HolGerm (ComplexModel t) :=
  HolGerm.comap (ContinuousLinearMap.inr ℂ (ComplexModel d) (ComplexModel t))

theorem splitModel_symm_inr (d t : ℕ) (z : ComplexModel t) :
    (splitModel d t).symm (ContinuousLinearMap.inr ℂ (ComplexModel d) (ComplexModel t) z) =
      actualJointNormalInclusion d t z := by
  rw [ContinuousLinearMap.inr_apply, ← splitModel_normalInclusion d t z,
    ContinuousLinearEquiv.symm_apply_apply]

theorem sliceHom_ambientGermEquiv (d t : ℕ) (g : HolGerm (ComplexModel (d + t))) :
    sliceHom d t (ambientGermEquiv d t g) = jointBaseZeroTrace d t g := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    show HolGerm.mk (fun z => f ((splitModel d t).symm
        (ContinuousLinearMap.inr ℂ (ComplexModel d) (ComplexModel t) z)))
        (eventually_differentiableAt_comp_clm (((splitModel d t).symm :
          ComplexModel d × ComplexModel t →L[ℂ] ComplexModel (d + t)).comp
            (ContinuousLinearMap.inr ℂ (ComplexModel d) (ComplexModel t))) hf) =
      HolGerm.mk (fun z => f (actualJointNormalInclusion d t z))
        (eventually_differentiableAt_comp_clm (actualJointNormalInclusion d t) hf)
    exact HolGerm.mk_eq_mk_iff.mpr
      (Eventually.of_forall fun z => congrArg f (splitModel_symm_inr d t z))

theorem sliceHom_surjective (d t : ℕ) : Surjective (sliceHom d t) := by
  intro g
  refine ⟨HolGerm.comap (ContinuousLinearMap.snd ℂ (ComplexModel d) (ComplexModel t)) g, ?_⟩
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold sliceHom
    rw [HolGerm.comap_mk, HolGerm.comap_mk]
    exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun _ => rfl)

/-- **The kernel of the slice restriction is `𝔪_A R`** (Hadamard). -/
theorem ker_sliceHom (d t : ℕ) :
    RingHom.ker (sliceHom d t) =
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))).map (basePullback d t) := by
  have h1 : sliceHom d t =
      (jointBaseZeroTrace d t).toRingHom.comp (ambientGermEquiv d t).symm.toRingHom := by
    refine RingHom.ext fun g => ?_
    obtain ⟨g', rfl⟩ := (ambientGermEquiv d t).surjective g
    rw [sliceHom_ambientGermEquiv]
    change _ = jointBaseZeroTrace d t ((ambientGermEquiv d t).symm (ambientGermEquiv d t g'))
    rw [RingEquiv.symm_apply_apply]
  rw [h1, ← RingHom.comap_ker, ← baseMaximalIdeal_eq_ker_jointBaseZeroTrace]
  show Ideal.comap (ambientGermEquiv d t).symm (originalBaseMaximalIdeal d t) = _
  rw [Ideal.comap_symm, basePullback_eq_comp, ← Ideal.map_map]
  rfl

theorem holAt_slice {d t : ℕ} {f : ComplexModel d × ComplexModel t → ℂ}
    {p : ComplexModel d × ComplexModel t} (hf : HolAt f p) : HolAt (fun z => f (p.1, z)) p.2 :=
  hf.comp (continuous_const.prodMk continuous_id)
    (fun _ => (differentiableAt_const p.1).prodMk differentiableAt_id)

theorem sliceHom_germAt (d t : ℕ) {f : ComplexModel d × ComplexModel t → ℂ}
    {p : ComplexModel d × ComplexModel t} (hf : HolAt f p) :
    sliceHom d t (germAt p f) = germAt p.2 (fun z => f (p.1, z)) := by
  rw [germAt_of_holAt hf, germAt_of_holAt (holAt_slice hf)]
  unfold sliceHom
  rw [HolGerm.comap_mk]
  exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun z =>
    congrArg f (Prod.ext (add_zero p.1) rfl))

theorem germ_matrix_map_sliceHom (d t : ℕ) {a b : ℕ}
    (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ) (p : ComplexModel d × ComplexModel t)
    (hF : ∀ i j, HolAt (F i j) p) :
    Matrix.map (fun i j => germAt p (F i j) : Matrix (Fin a) (Fin b) _) (sliceHom d t) =
      germMat p.2 (fib F p.1) :=
  Matrix.ext fun i j => sliceHom_germAt d t (hF i j)

end

end Hironaka.Analytic.Unibranch.HironakaG10LfChart
