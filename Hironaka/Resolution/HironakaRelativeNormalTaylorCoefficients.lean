/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothCentreRelativeIdeal
import Hironaka.MarkedIdeal.NormalTaylorOrder

/-!
# Actual relative normal Taylor coefficients and whole ideal-power kernels

The maps use actual original holomorphic representatives and genuine whole
plane-trace germs, with true tangential base-germ linearity. Only actual
normal derivatives enter the convergent Taylor producer. Its complete kernel
is the entire original normal ideal power, not a point-value surrogate.
Every whole original ideal has internally selected original generators and
literal all-degree coefficient-image quotient presentations. Original regular
centre geometry internally produces the actual nonlinear flattening and every
transported full vanishing-ideal-power kernel.

The ordered normal-word family retains its actual symmetries and is not claimed
to be independent. Arbitrary ideal quotients are not asserted free or flat.
All-degree normal-flat centre selection, higher-HS descent and general G8
remain OPEN. No kernel, coefficient, flattening or flatness certificate is input.
Blueprint: `hironaka-relative-normal-taylor-coefficients-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff Nat
namespace Hironaka.HironakaRelativeNormalTaylorCoefficients
open Hironaka.HolomorphicIdealSheaves HolGerm HolomorphicTaylorTail
  NormalTaylorOrder HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalIdeal HironakaSmoothCentreRelativeIdeal HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci
open Hironaka
attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass
noncomputable section
variable {n : ℕ}

/-- Actual iterated derivatives of every original holomorphic representative stay holomorphic near zero. -/
theorem eventually_holomorphic_iterDeriv {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (L : List (ComplexModel n)) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (iterDeriv L f) z := by
  obtain ⟨U, hUf, hU, h0⟩ := eventually_nhds_iff.mp hf
  have hd := differentiableOn_iterDeriv
    (fun z hz => (hUf z hz).differentiableWithinAt) hU L
  filter_upwards [hU.mem_nhds h0] with z hz
  exact (hd z hz).differentiableAt (hU.mem_nhds hz)

/-- Genuine whole representative equality preserves ALL actual original iterated derivatives. -/
theorem iterDeriv_eventually_congr {f g : ComplexModel n → ℂ}
    (he : f =ᶠ[𝓝 0] g) : ∀ L : List (ComplexModel n),
      iterDeriv L f =ᶠ[𝓝 0] iterDeriv L g
  | [] => he
  | v :: L => by
    filter_upwards [(iterDeriv_eventually_congr he L).eventually_nhds] with z hz
    exact congrArg (fun T : ComplexModel n →L[ℂ] ℂ => T v) (show iterDeriv L f =ᶠ[𝓝 z] iterDeriv L g from hz).fderiv_eq

private theorem iterDeriv_eventually_add {f g : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    ∀ L : List (ComplexModel n),
      iterDeriv L (fun z => f z+g z) =ᶠ[𝓝 0] fun z => iterDeriv L f z+iterDeriv L g z
  | [] => EventuallyEq.rfl
  | v :: L => by
    filter_upwards [(iterDeriv_eventually_add hf hg L).eventually_nhds,
      eventually_holomorphic_iterDeriv hf L, eventually_holomorphic_iterDeriv hg L] with z he hdf hdg
    simp only [iterDeriv_cons, dirDeriv]
    rw [(show iterDeriv L (fun z => f z+g z) =ᶠ[𝓝 z] (fun z => iterDeriv L f z+iterDeriv L g z) from he).fderiv_eq]
    change (fderiv ℂ (iterDeriv L f + iterDeriv L g) z) v = _
    rw [fderiv_add hdf hdg]
    rfl

private theorem iterDeriv_eventually_const_mul {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (c : ℂ) :
    ∀ L : List (ComplexModel n),
      iterDeriv L (fun z => c*f z) =ᶠ[𝓝 0] fun z => c*iterDeriv L f z
  | [] => EventuallyEq.rfl
  | v :: L => by
    filter_upwards [(iterDeriv_eventually_const_mul hf c L).eventually_nhds,
      eventually_holomorphic_iterDeriv hf L] with z he hdf
    simp only [iterDeriv_cons, dirDeriv]
    rw [(show iterDeriv L (fun z => c*f z) =ᶠ[𝓝 z] (fun z => c*iterDeriv L f z) from he).fderiv_eq, fderiv_const_mul hdf]
    rfl

/-- The genuine complex-linear derivative operation on the ENTIRE actual holomorphic germ ring. -/
def iteratedDerivativeGerm (L : List (ComplexModel n)) :
    HolGerm (ComplexModel n) →ₗ[ℂ] HolGerm (ComplexModel n) where
  toFun g := ⟨Germ.liftOn (g : Germ (𝓝 (0 : ComplexModel n)) ℂ)
    (fun f => (iterDeriv L f : Germ (𝓝 (0 : ComplexModel n)) ℂ))
    (fun f g he => Germ.coe_eq.mpr (iterDeriv_eventually_congr he L)), by
      obtain ⟨_, f, hf, rfl⟩ := g
      exact ⟨iterDeriv L f, eventually_holomorphic_iterDeriv hf L, rfl⟩⟩
  map_add' g h := by
    induction g using HolGerm.induction_on with
    | h f hf =>
      induction h using HolGerm.induction_on with
      | h g hg =>
        change HolGerm.mk (iterDeriv L (fun z => f z+g z))
          (eventually_holomorphic_iterDeriv (eventually_differentiableAt_add hf hg) L) =
          HolGerm.mk (iterDeriv L f) (eventually_holomorphic_iterDeriv hf L) +
          HolGerm.mk (iterDeriv L g) (eventually_holomorphic_iterDeriv hg L)
        rw [← HolGerm.mk_add]
        exact HolGerm.mk_eq_mk_iff.mpr (iterDeriv_eventually_add hf hg L)
  map_smul' c g := by
    induction g using HolGerm.induction_on with
    | h f hf =>
      have hcf := eventually_differentiableAt_mul (eventually_differentiableAt_const c) hf
      have he : c • HolGerm.mk f hf = HolGerm.mk (fun z => c*f z) hcf := by
        rw [Algebra.smul_def]
        rfl
      rw [he]
      change HolGerm.mk (iterDeriv L (fun z => c*f z))
        (eventually_holomorphic_iterDeriv hcf L) =
        c • HolGerm.mk (iterDeriv L f) (eventually_holomorphic_iterDeriv hf L)
      have hs : c • HolGerm.mk (iterDeriv L f) (eventually_holomorphic_iterDeriv hf L) =
          HolGerm.mk (fun z => c*iterDeriv L f z)
            (eventually_differentiableAt_mul (eventually_differentiableAt_const c)
              (eventually_holomorphic_iterDeriv hf L)) := by
        rw [Algebra.smul_def]
        rfl
      rw [hs]
      exact HolGerm.mk_eq_mk_iff.mpr (iterDeriv_eventually_const_mul hf c L)

/-- Entire output on each actual original representative is exactly the actual original derivative germ. -/
theorem iteratedDerivativeGerm_mk (L : List (ComplexModel n))
    {f : ComplexModel n → ℂ} (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    iteratedDerivativeGerm L (HolGerm.mk f hf) =
      HolGerm.mk (iterDeriv L f) (eventually_holomorphic_iterDeriv hf L) := rfl

/-- The true original normal coordinate direction. -/
def normalVector (d t : ℕ) (i : Fin t) : ComplexModel (d+t) :=
  EuclideanSpace.single (i.natAdd d) (1 : ℂ)

/-- The actual original tangent projection kills every real normal coordinate direction. -/
theorem tangentProjection_normalVector (d t : ℕ) (i : Fin t) :
    tangentProjection d t (normalVector d t i) = 0 := by
  ext j
  have hn : j.castAdd t ≠ i.natAdd d := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  simp [tangentProjection_apply, normalVector, hn]

private theorem eventually_dirDeriv_tangent_zero (d t : ℕ) (i : Fin t)
    {a : ComplexModel d → ℂ} (ha : ∀ᶠ u in 𝓝 0, DifferentiableAt ℂ a u) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)),
      dirDeriv (normalVector d t i) (fun w => a (tangentProjection d t w)) z = 0 := by
  have ht : Tendsto (tangentProjection d t) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (tangentProjection d t).continuous.tendsto (0 : ComplexModel (d+t))
  filter_upwards [ht.eventually ha] with z hz
  change (fderiv ℂ (a ∘ tangentProjection d t) z) (normalVector d t i) = 0
  rw [fderiv_comp z hz (tangentProjection d t).differentiableAt,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv, tangentProjection_normalVector, map_zero]

/-- Actual normal differentiation keeps ENTIRE original tangential coefficient functions unchanged. -/
theorem iterDeriv_eventually_tangent_mul (d t : ℕ)
    {a : ComplexModel d → ℂ} (ha : ∀ᶠ u in 𝓝 0, DifferentiableAt ℂ a u)
    {g : ComplexModel (d+t) → ℂ} (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    ∀ L : List (Fin t),
      iterDeriv (L.map (normalVector d t)) (fun z => a (tangentProjection d t z)*g z) =ᶠ[𝓝 0]
        fun z => a (tangentProjection d t z)*iterDeriv (L.map (normalVector d t)) g z
  | [] => EventuallyEq.rfl
  | i :: L => by
    have hac := eventually_differentiableAt_comp_clm (tangentProjection d t) ha
    filter_upwards [(iterDeriv_eventually_tangent_mul d t ha hg L).eventually_nhds,
      hac, eventually_holomorphic_iterDeriv hg (L.map (normalVector d t)),
      eventually_dirDeriv_tangent_zero d t i ha] with z he hda hdg hz
    simp only [List.map_cons, iterDeriv_cons, dirDeriv]
    have he' : iterDeriv (L.map (normalVector d t)) (fun z => a (tangentProjection d t z)*g z) =ᶠ[𝓝 z]
        fun z => a (tangentProjection d t z)*iterDeriv (L.map (normalVector d t)) g z := he
    rw [he'.fderiv_eq]
    change (fderiv ℂ ((a ∘ tangentProjection d t) * iterDeriv (L.map (normalVector d t)) g) z)
      (normalVector d t i) = _
    rw [fderiv_mul hda hdg]
    change a (tangentProjection d t z) *
        (fderiv ℂ (iterDeriv (L.map (normalVector d t)) g) z) (normalVector d t i) +
        (iterDeriv (L.map (normalVector d t)) g z) *
        dirDeriv (normalVector d t i) (fun w => a (tangentProjection d t w)) z = _
    rw [hz, mul_zero, add_zero]

/-- True whole normal derivative germs respect the actual ENTIRE base-ring scalar action. -/
theorem iteratedDerivativeGerm_tangent_mul (d t : ℕ) (L : List (Fin t))
    (a : HolGerm (ComplexModel d)) (g : HolGerm (ComplexModel (d+t))) :
    iteratedDerivativeGerm (L.map (normalVector d t)) (tangentPullback d t a * g) =
      tangentPullback d t a * iteratedDerivativeGerm (L.map (normalVector d t)) g := by
  induction a using HolGerm.induction_on with
  | h a ha =>
    induction g using HolGerm.induction_on with
    | h g hg =>
      unfold tangentPullback
      rw [HironakaHolomorphicJetChartInvariance.compAlgHom_mk, ← HolGerm.mk_mul,
        iteratedDerivativeGerm_mk, iteratedDerivativeGerm_mk, ← HolGerm.mk_mul]
      exact HolGerm.mk_eq_mk_iff.mpr (iterDeriv_eventually_tangent_mul d t ha hg L)

/-- The genuine normalized entire relative Taylor coefficient for any actual ordered normal word. -/
def relativeTaylorCoefficient (d t : ℕ) (L : List (Fin t))
    (g : HolGerm (ComplexModel (d+t))) : HolGerm (ComplexModel d) :=
  (L.length.factorial : ℂ)⁻¹ •
    planeTrace d t (iteratedDerivativeGerm (L.map (normalVector d t)) g)

/-- Actual whole normal coefficients are additive, including their real factorial normalizations. -/
theorem relativeTaylorCoefficient_add (d t : ℕ) (L : List (Fin t))
    (g h : HolGerm (ComplexModel (d+t))) :
    relativeTaylorCoefficient d t L (g+h) =
      relativeTaylorCoefficient d t L g + relativeTaylorCoefficient d t L h := by
  simp only [relativeTaylorCoefficient, map_add, smul_add]

/-- Genuine normal coefficients are linear over the ENTIRE actual original tangential germ ring. -/
theorem relativeTaylorCoefficient_tangent_mul (d t : ℕ) (L : List (Fin t))
    (a : HolGerm (ComplexModel d)) (g : HolGerm (ComplexModel (d+t))) :
    relativeTaylorCoefficient d t L (tangentPullback d t a*g) =
      a*relativeTaylorCoefficient d t L g := by
  rw [relativeTaylorCoefficient, iteratedDerivativeGerm_tangent_mul,
    map_mul, planeTrace_tangentPullback, ← mul_smul_comm]
  rfl

/-- Actual finite ALL-word relative normal Taylor tuple, as a true whole-base linear map. -/
def normalTaylorCoefficients (d t q : ℕ) :
    letI := tangentAlgebra d t
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)]
      (monomialIndex t q → HolGerm (ComplexModel d)) :=
  letI := tangentAlgebra d t
  { toFun := fun g w => relativeTaylorCoefficient d t (List.ofFn w.2) g
    map_add' := fun g h => funext fun w => relativeTaylorCoefficient_add d t _ g h
    map_smul' := fun a g => by
      funext w
      change relativeTaylorCoefficient d t (List.ofFn w.2) (tangentPullback d t a*g) =
        a*relativeTaylorCoefficient d t (List.ofFn w.2) g
      exact relativeTaylorCoefficient_tangent_mul d t _ a g }

/-- Every true recursive normal-power expression gives membership in the ENTIRE actual ideal power. -/
theorem mem_normalIdeal_pow_of_InNormalPow (d t q : ℕ)
    {f : ComplexModel (d+t) → ℂ} (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hpow : InNormalPow d (0 : ComplexModel (d+t)) q f) :
    HolGerm.mk f hf ∈ normalIdeal d t ^ q := by
  induction q generalizing f with
  | zero => simp
  | succ q ih =>
    obtain ⟨H, hH0, hH, heq⟩ := hpow
    have hhol : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (H i) z :=
      fun i => (hH i).eventually_differentiableAt
    have hc : ∀ i : Fin (d+t), ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)),
        DifferentiableAt ℂ (fun w : ComplexModel (d+t) => w i) z :=
      fun i => Eventually.of_forall fun _ => (EuclideanSpace.proj i : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt
    have hs := eventually_differentiableAt_sum Finset.univ
      (fun i => eventually_differentiableAt_mul (hc i) (hhol i))
    have he : HolGerm.mk f hf = ∑ i : Fin (d+t), coordinateGerm i * HolGerm.mk (H i) (hhol i) := by
      calc
        HolGerm.mk f hf = HolGerm.mk (fun z => ∑ i : Fin (d+t), z i*H i z) hs :=
          HolGerm.mk_eq_mk_iff.mpr heq
        _ = _ := by
          rw [HolGerm.mk_sum Finset.univ]
          · exact Finset.sum_congr rfl fun i _ => HolGerm.mk_mul _ _ _ _
          · exact fun i => eventually_differentiableAt_mul (hc i) (hhol i)
    rw [he, pow_succ']
    apply Ideal.sum_mem
    intro i _
    by_cases hi : i.val < d
    · have hz : HolGerm.mk (H i) (hhol i) = 0 := by
        change HolGerm.mk (H i) (hhol i) = HolGerm.mk (0 : ComplexModel (d+t) → ℂ) eventually_differentiableAt_zero
        apply HolGerm.mk_eq_mk_iff.mpr
        exact Eventually.of_forall fun z => congrFun (hH0 i hi) z
      rw [hz, mul_zero]
      exact Ideal.zero_mem _
    · let j : Fin t := ⟨i.val-d, by omega⟩
      have hij : i = j.natAdd d := Fin.ext (by dsimp [j]; omega)
      apply Ideal.mul_mem_mul
      · rw [hij]
        exact Ideal.subset_span ⟨j, rfl⟩
      · exact ih (hhol i) (hH i)

private def normalPowerIdeal (d t q : ℕ) : Ideal (HolGerm (ComplexModel (d+t))) where
  carrier := {g | ∃ (f : ComplexModel (d+t) → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z),
    g = HolGerm.mk f hf ∧ InNormalPow d (0 : ComplexModel (d+t)) q f}
  zero_mem' := ⟨fun _ => 0, eventually_differentiableAt_zero, rfl, inNormalPow_zero_fun q⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl, hp⟩ ⟨g, hg, rfl, hq⟩
    exact ⟨fun z => f z+g z, eventually_differentiableAt_add hf hg, rfl, hp.add hq⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl, hp⟩
    obtain ⟨a, ha, rfl⟩ := HolGerm.exists_eq_mk c
    exact ⟨fun z => a z*f z, eventually_differentiableAt_mul ha hf, rfl,
      hp.const_mul_holo ha⟩

private theorem normalIdeal_pow_le_normalPowerIdeal (d t q : ℕ) :
    normalIdeal d t ^ q ≤ normalPowerIdeal d t q := by
  induction q with
  | zero =>
    intro g _
    obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
    exact ⟨f, hf, rfl, hf⟩
  | succ q ih =>
    rw [pow_succ']
    apply Ideal.mul_le.mpr
    intro a ha b hb
    obtain ⟨f, hf, rfl, hpow⟩ := ih hb
    apply Submodule.span_induction
      (p := fun a _ => a * HolGerm.mk f hf ∈ normalPowerIdeal d t (q+1))
      ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨i, rfl⟩
      have hc : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)),
          DifferentiableAt ℂ (fun w : ComplexModel (d+t) => w (i.natAdd d)) z :=
        Eventually.of_forall fun _ => (EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt
      exact ⟨fun z => z (i.natAdd d)*f z, eventually_differentiableAt_mul hc hf, rfl,
        hpow.coord_mul (by simp)⟩
    · simpa only [zero_mul] using (normalPowerIdeal d t (q+1)).zero_mem
    · intro a b _ _ ha hb
      rw [add_mul]
      exact Ideal.add_mem _ ha hb
    · intro c a _ ha
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c ha

/-- EXACT whole normal ideal powers agree with genuine original recursive normal-power expressions. -/
theorem mem_normalIdeal_pow_iff_InNormalPow (d t q : ℕ)
    {f : ComplexModel (d+t) → ℂ} (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    HolGerm.mk f hf ∈ normalIdeal d t ^ q ↔ InNormalPow d (0 : ComplexModel (d+t)) q f := by
  constructor
  · intro hg
    obtain ⟨a, ha, he, hpow⟩ := normalIdeal_pow_le_normalPowerIdeal d t q hg
    exact hpow.congr (HolGerm.mk_eq_mk_iff.mp he)
  · exact mem_normalIdeal_pow_of_InNormalPow d t q hf

private theorem normal_vanishing_recursive_aux (c : ℕ) :
    ∀ (k : ℕ), n-k=c → ∀ (q : ℕ) {f : ComplexModel n → ℂ},
      (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) →
      (∀ᶠ y in 𝓝 (0 : ComplexModel n), y ∈ complexCoordinatePlane n k →
        ∀ L : List (Fin n), NormalIdx k L → L.length < q → iterDeriv (L.map bv) f y = 0) →
      InNormalPow k (0 : ComplexModel n) q f := by
  induction c with
  | zero =>
    intro k hk q f hf hv
    cases q with
    | zero => exact hf
    | succ q =>
      apply (inNormalPow_zero_fun (k := k) (q := (0 : ComplexModel n)) (q+1)).congr
      filter_upwards [hv] with y hy
      have hp : y ∈ complexCoordinatePlane n k := fun i hi => by
        have := i.isLt
        omega
      exact hy hp [] (fun i hi => by simp at hi) (by simp)
  | succ c ih =>
    intro k hk q f hf hv
    have hkn : k < n := by omega
    let i : Fin n := ⟨k, hkn⟩
    let e : ComplexModel n := bv i
    let pr : ComplexModel n →L[ℂ] ComplexModel n := killCoord i
    obtain ⟨U, hUf, hU, h0⟩ := eventually_nhds_iff.mp hf
    have hfU : DifferentiableOn ℂ f U := fun z hz => (hUf z hz).differentiableWithinAt
    have hprt : Tendsto pr (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using pr.continuous.tendsto (0 : ComplexModel n)
    have hprU := hprt.eventually (hU.mem_nhds h0)
    obtain ⟨G, hG, heq⟩ := exists_taylor_tail hf e q
    have hφt : Tendsto (fun u : ComplexModel n => (pr u, u i)) (𝓝 0) (𝓝 ((0 : ComplexModel n), (0 : ℂ))) := by
      have hc : Continuous (fun u : ComplexModel n => (pr u,u i)) :=
        pr.continuous.prodMk (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous
      simpa only [map_zero, PiLp.zero_apply] using hc.tendsto (0 : ComplexModel n)
    let g : ℕ → ComplexModel n → ℂ := fun j u => iterDeriv (List.replicate j e) f (pr u)
    have hg : ∀ j < q, InNormalPow (k+1) (0 : ComplexModel n) (q-j) (g j) := by
      intro j hj
      apply ih (k+1) (by omega) (q-j)
      · filter_upwards [hprU] with z hz
        exact ((differentiableOn_iterDeriv hfU hU _).differentiableAt (hU.mem_nhds hz)).comp z pr.differentiableAt
      · filter_upwards [hprU, hprt.eventually hv] with y hyU hyV hy L hLn hlen
        let L' := L ++ List.replicate j i
        have hidx : NormalIdx k L' :=
          (hLn.mono (Nat.le_succ k)).append (normalIdx_replicate le_rfl j)
        have hlen' : L'.length < q := by dsimp [L']; simp only [List.length_append, List.length_replicate]; omega
        have hmap : (L.map bv).map pr = L.map bv := by
          rw [List.map_map]
          apply List.map_congr_left
          intro l hl
          have hli : l ≠ i := by
            intro he
            have := hLn l hl
            rw [he] at this
            dsimp [i] at this
            omega
          exact killCoord_bv hli
        have hp : pr y ∈ complexCoordinatePlane n k := by
          intro l hl
          change killCoord i y l = 0
          rw [killCoord_apply_apply]
          split_ifs with he
          · rfl
          · exact hy l (by
              have hne : l.val ≠ k := fun hv => he (Fin.ext hv)
              omega)
        have hc := iterDeriv_comp_clm (differentiableOn_iterDeriv hfU hU (List.replicate j e)) hU pr (L.map bv) y hyU
        change iterDeriv (L.map bv) (fun u => iterDeriv (List.replicate j e) f (pr u)) y = 0
        rw [hc, hmap, ← iterDeriv_append]
        have hz := hyV hp L' hidx hlen'
        simpa only [L', List.map_append, List.map_replicate] using hz
    have hterm : ∀ j ∈ Finset.range q,
        InNormalPow k (0 : ComplexModel n) q (fun u => (j.factorial : ℂ)⁻¹ * (u i ^ j*g j u)) := by
      intro j hj
      have hjq := Finset.mem_range.mp hj
      have hpow := ((hg j hjq).mono_k).coord_pow_mul (i := i) (by simp [i]) j
      rw [Nat.sub_add_cancel hjq.le] at hpow
      exact hpow.const_mul_holo (Eventually.of_forall fun _ => differentiableAt_const _)
    have hlast : InNormalPow k (0 : ComplexModel n) q (fun u => u i ^ q * G (pr u,u i)) := by
      have hhol : InNormalPow k (0 : ComplexModel n) 0 (fun u => G (pr u,u i)) := by
        filter_upwards [hφt.eventually hG] with u hu
        exact hu.comp u (pr.differentiableAt.prodMk (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt)
      simpa only [zero_add] using hhol.coord_pow_mul (i := i) (by simp [i]) q
    apply ((inNormalPow_finset_sum (Finset.range q) hterm).add hlast).congr
    filter_upwards [hφt.eventually heq] with u hu
    have hu' : f u = ∑ j ∈ Finset.range q,
        (j.factorial : ℂ)⁻¹ * iterDeriv (List.replicate j e) f (pr u) * u i ^ j +
        u i ^ q*G (pr u,u i) := by
      have hs : pr u+u i • e = u := killCoord_add i u
      simpa only [hs] using hu
    rw [hu']
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [g]
    ring

/-- ONLY actual normal derivatives on the real plane force a genuine full normal ideal-power expression. -/
theorem inNormalPow_of_normal_derivatives_zero (k q : ℕ)
    {f : ComplexModel n → ℂ} (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hv : ∀ᶠ y in 𝓝 (0 : ComplexModel n), y ∈ complexCoordinatePlane n k →
      ∀ L : List (Fin n), NormalIdx k L → L.length < q → iterDeriv (L.map bv) f y = 0) :
    InNormalPow k (0 : ComplexModel n) q f :=
  normal_vanishing_recursive_aux (n-k) k rfl q hf hv

/-- Genuine directional differentiation removes at most ONE true normal-coordinate factor. -/
theorem InNormalPow_dirDeriv {k : ℕ} (v : ComplexModel n) :
    ∀ (q : ℕ) {f : ComplexModel n → ℂ}, InNormalPow k (0 : ComplexModel n) (q+1) f →
      InNormalPow k (0 : ComplexModel n) q (dirDeriv v f)
  | 0, f, hp => eventually_holomorphic_iterDeriv hp.eventually_differentiableAt [v]
  | q+1, f, ⟨H, hH0, hH, he⟩ => by
    have hhol : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (H j) z :=
      fun j => (hH j).eventually_differentiableAt
    have hall := eventually_all.mpr hhol
    have hterm : ∀ j : Fin n, InNormalPow k (0 : ComplexModel n) (q+1)
        (fun z => v j*H j z+z j*dirDeriv v (H j) z) := by
      intro j
      by_cases hj : j.val < k
      · apply (inNormalPow_zero_fun (k := k) (q := (0 : ComplexModel n)) (q+1)).congr
        exact Eventually.of_forall fun z => by simp [hH0 j hj, dirDeriv]
      · exact ((hH j).const_mul_holo (Eventually.of_forall fun _ => differentiableAt_const _)).add
          ((InNormalPow_dirDeriv v q (hH j)).coord_mul (by omega))
    apply (inNormalPow_finset_sum Finset.univ (fun j _ => hterm j)).congr
    filter_upwards [he.eventually_nhds, hall] with z heq hz
    rw [dirDeriv, (show f =ᶠ[𝓝 z] (fun z => ∑ j : Fin n, z j*H j z) from heq).fderiv_eq]
    rw [fderiv_fun_sum (A := fun j z => z j*H j z)
      (fun j _ => (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).differentiableAt.mul (hz j)),
      sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_fun_mul (c := fun w : ComplexModel n => w j)
      (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).differentiableAt (hz j)]
    have hc : fderiv ℂ (fun w : ComplexModel n => w j) z = EuclideanSpace.proj j :=
      (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).fderiv
    rw [hc]
    change z j*dirDeriv v (H j) z+H j z*v j = v j*H j z+z j*dirDeriv v (H j) z
    ring

/-- The actual full iterated derivative lowers the WHOLE normal power by at most its actual length. -/
theorem InNormalPow_iterDeriv {k : ℕ} (L : List (ComplexModel n)) (q : ℕ)
    {f : ComplexModel n → ℂ} (hp : InNormalPow k (0 : ComplexModel n) (q+L.length) f) :
    InNormalPow k (0 : ComplexModel n) q (iterDeriv L f) := by
  induction L generalizing q with
  | nil => exact hp
  | cons v L ih =>
    have he : q+(v::L).length = (q+1)+L.length := by simp; omega
    rw [he] at hp
    exact InNormalPow_dirDeriv v q (ih (q+1) hp)

/-- Positive genuine normal powers vanish on the true WHOLE coordinate-plane germ. -/
theorem InNormalPow_vanishes_plane {k q : ℕ} {f : ComplexModel n → ℂ}
    (hp : InNormalPow k (0 : ComplexModel n) (q+1) f) :
    ∀ᶠ y in 𝓝 (0 : ComplexModel n), y ∈ complexCoordinatePlane n k → f y = 0 := by
  obtain ⟨H, hH0, _, he⟩ := hp
  filter_upwards [he] with y hy hp
  rw [hy]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val < k
  · simp [hH0 j hj]
  · rw [hp j (by omega), zero_mul]

/-- Zero of a genuine WHOLE coefficient is exactly neighbourhood vanishing of its true plane trace. -/
theorem relativeTaylorCoefficient_mk_eq_zero_iff (d t : ℕ) (L : List (Fin t))
    {f : ComplexModel (d+t) → ℂ} (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    relativeTaylorCoefficient d t L (HolGerm.mk f hf) = 0 ↔
      ∀ᶠ u in 𝓝 (0 : ComplexModel d),
        iterDeriv (L.map (normalVector d t)) f (tangentInclusion d t u) = 0 := by
  have hn : (L.length.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero L.length
  have he : relativeTaylorCoefficient d t L (HolGerm.mk f hf) = 0 ↔
      planeTrace d t (iteratedDerivativeGerm (L.map (normalVector d t)) (HolGerm.mk f hf)) = 0 := by
    constructor
    · intro hz
      have hh := congrArg (fun g : HolGerm (ComplexModel d) => (L.length.factorial : ℂ) • g) hz
      simpa only [relativeTaylorCoefficient, smul_smul, mul_inv_cancel₀ hn, one_smul, smul_zero] using hh
    · intro hz
      rw [relativeTaylorCoefficient, hz, smul_zero]
  rw [he, iteratedDerivativeGerm_mk]
  unfold planeTrace
  rw [HironakaHolomorphicJetChartInvariance.compAlgHom_mk]
  change HolGerm.mk _ _ = HolGerm.mk (0 : ComplexModel d → ℂ) eventually_differentiableAt_zero ↔ _
  exact HolGerm.mk_eq_mk_iff

/-- Every actual normal-index list is a genuine word in the internally indexed finite coefficient family. -/
theorem exists_normal_word (d t q : ℕ) (L : List (Fin (d+t)))
    (hL : NormalIdx d L) (hlen : L.length < q) :
    ∃ w : monomialIndex t q,
      (List.ofFn w.2).map (normalVector d t) = L.map bv := by
  let wf : Fin L.length → Fin t := fun j =>
    ⟨(L.get j).val-d, by have hn := hL (L.get j) (List.get_mem L j); have hb := (L.get j).isLt; omega⟩
  refine ⟨⟨⟨L.length, hlen⟩, wf⟩, ?_⟩
  change (List.ofFn wf).map (normalVector d t) = L.map bv
  rw [List.map_ofFn]
  have he : (fun j => normalVector d t (wf j)) = fun j => bv (L.get j) := by
    funext j
    have hn := hL (L.get j) (List.get_mem L j)
    have hi : (wf j).natAdd d = L.get j := Fin.ext (by
      change d+((L.get j).val-d) = (L.get j).val
      omega)
    simp only [normalVector, hi, bv]
  change List.ofFn (fun j => normalVector d t (wf j)) = L.map bv
  rw [he]
  change List.ofFn (bv ∘ L.get) = L.map bv
  rw [← List.map_ofFn, List.ofFn_get]

/-- The actual entire coefficient map kills EVERY member of the whole original normal ideal power. -/
theorem normalTaylorCoefficients_eq_zero_of_mem (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t ^ q) :
    letI := tangentAlgebra d t
    normalTaylorCoefficients d t q g = 0 := by
  let := tangentAlgebra d t
  induction g using HolGerm.induction_on with
  | h f hf =>
    have hp := (mem_normalIdeal_pow_iff_InNormalPow d t q hf).mp hg
    funext w
    apply (relativeTaylorCoefficient_mk_eq_zero_iff d t (List.ofFn w.2) hf).mpr
    have hl : (List.ofFn w.2).length < q := by simp
    let b := q-(List.ofFn w.2).length-1
    have hq : q = (b+1)+((List.ofFn w.2).map (normalVector d t)).length := by
      dsimp [b]; simp only [List.length_map]; omega
    rw [hq] at hp
    have hd := InNormalPow_iterDeriv ((List.ofFn w.2).map (normalVector d t)) (b+1) hp
    have hv := InNormalPow_vanishes_plane hd
    have ht : Tendsto (tangentInclusion d t) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using (tangentInclusion d t).continuous.tendsto (0 : ComplexModel d)
    filter_upwards [ht.eventually hv] with u hu
    exact hu (tangentInclusion_mem_plane d t u)

/-- Zero of the actual finite WHOLE coefficient tuple internally forces complete normal-power membership. -/
theorem mem_normalIdeal_pow_of_normalTaylorCoefficients_eq_zero (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    letI := tangentAlgebra d t
    normalTaylorCoefficients d t q g = 0 → g ∈ normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  intro hg
  induction g using HolGerm.induction_on with
  | h f hf =>
    have hz : ∀ w : monomialIndex t q, ∀ᶠ u in 𝓝 (0 : ComplexModel d),
        iterDeriv ((List.ofFn w.2).map (normalVector d t)) f (tangentInclusion d t u) = 0 := by
      intro w
      apply (relativeTaylorCoefficient_mk_eq_zero_iff d t (List.ofFn w.2) hf).mp
      exact congrFun hg w
    have hall := eventually_all.mpr hz
    have ht : Tendsto (tangentProjection d t) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using (tangentProjection d t).continuous.tendsto (0 : ComplexModel (d+t))
    have hv : ∀ᶠ y in 𝓝 (0 : ComplexModel (d+t)), y ∈ complexCoordinatePlane (d+t) d →
        ∀ L : List (Fin (d+t)), NormalIdx d L → L.length < q → iterDeriv (L.map bv) f y = 0 := by
      filter_upwards [ht.eventually hall] with y hy hp L hL hl
      obtain ⟨w, hw⟩ := exists_normal_word d t q L hL hl
      have hh := hy w
      rw [hw, tangentInclusion_projection_eq_of_mem_plane d t hp] at hh
      exact hh
    exact mem_normalIdeal_pow_of_InNormalPow d t q hf (inNormalPow_of_normal_derivatives_zero d q hf hv)

/-- The COMPLETE actual relative Taylor kernel is exactly the entire genuine normal ideal power. -/
theorem ker_normalTaylorCoefficients (d t q : ℕ) :
    let := tangentAlgebra d t
    LinearMap.ker (normalTaylorCoefficients d t q) =
      (normalIdeal d t ^ q).restrictScalars (HolGerm (ComplexModel d)) := by
  let := tangentAlgebra d t
  ext g
  rw [LinearMap.mem_ker]
  exact ⟨mem_normalIdeal_pow_of_normalTaylorCoefficients_eq_zero d t q g,
    normalTaylorCoefficients_eq_zero_of_mem d t q g⟩

/-- The actual whole coefficient tuple is genuinely unique modulo the whole original normal power. -/
theorem normalTaylorCoefficients_eq_iff (d t q : ℕ)
    (g h : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    normalTaylorCoefficients d t q g = normalTaylorCoefficients d t q h ↔
      g-h ∈ normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ker_normalTaylorCoefficients]
  rfl

/-- The entire literal normal-power quotient is the genuine actual relative Taylor image module. -/
def normalTaylorQuotientEquiv (d t q : ℕ) :
    letI := tangentAlgebra d t
    (HolGerm (ComplexModel (d+t)) ⧸ (normalIdeal d t ^ q)) ≃ₗ[HolGerm (ComplexModel d)]
      LinearMap.range (normalTaylorCoefficients d t q) :=
  letI := tangentAlgebra d t
  (Submodule.quotEquivOfEq _ _ (ker_normalTaylorCoefficients d t q).symm).trans
    (normalTaylorCoefficients d t q).quotKerEquivRange

/-- The actual WHOLE relative coefficient range equals the finite actual normal-word coefficient span. -/
theorem range_normalTaylorCoefficients_eq_span_words (d t q : ℕ) :
    let := tangentAlgebra d t
    LinearMap.range (normalTaylorCoefficients d t q) = Submodule.span (HolGerm (ComplexModel d))
      (range fun w : monomialIndex t q => normalTaylorCoefficients d t q (normalWord d t w)) := by
  let := tangentAlgebra d t
  let T := normalTaylorCoefficients d t q
  have hmap : (normalWordSpan d t q).map T = Submodule.span (HolGerm (ComplexModel d))
      (range fun w : monomialIndex t q => T (normalWord d t w)) := by
    rw [normalWordSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  apply le_antisymm
  · rintro v ⟨g, rfl⟩
    obtain ⟨p, hp, hrem⟩ := exists_normalWord_representative d t q g
    have he : T g = T p := (normalTaylorCoefficients_eq_iff d t q g p).mpr hrem
    rw [he, ← hmap]
    exact Submodule.mem_map.mpr ⟨p, hp, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨w, rfl⟩
    exact LinearMap.mem_range_self _ _

private theorem normalTaylorCoefficients_mul_mem_word_columns (d t q : ℕ)
    (a h : HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    normalTaylorCoefficients d t q (a*h) ∈ Submodule.span (HolGerm (ComplexModel d))
      (range fun w : monomialIndex t q => normalTaylorCoefficients d t q (normalWord d t w*h)) := by
  let := tangentAlgebra d t
  let T := normalTaylorCoefficients d t q
  let C := Submodule.span (HolGerm (ComplexModel d))
    (range fun w : monomialIndex t q => T (normalWord d t w*h))
  obtain ⟨p, hp, hrem⟩ := exists_normalWord_representative d t q a
  have hzer : T ((a-p)*h) = 0 := normalTaylorCoefficients_eq_zero_of_mem d t q _
    (Ideal.mul_mem_right h _ hrem)
  have he : T (a*h) = T (p*h) := by
    rw [sub_mul, map_sub, sub_eq_zero] at hzer
    exact hzer
  rw [he]
  change T (p*h) ∈ C
  apply Submodule.span_induction (p := fun p _ => T (p*h) ∈ C) ?_ ?_ ?_ ?_ hp
  · rintro p ⟨w, rfl⟩
    exact Submodule.subset_span ⟨w, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [add_mul, map_add]
    exact Submodule.add_mem _ hx hy
  · intro c p _ hp
    rw [smul_mul_assoc, map_smul]
    exact Submodule.smul_mem _ _ hp

/-- The entire ORIGINAL ideal image equals actual finite normal-word-times-original-generator columns. -/
theorem map_span_ideal_normalTaylorCoefficients_eq_word_columns (d t q : ℕ)
    {ι : Type*} [Fintype ι] (G : ι → HolGerm (ComplexModel (d+t))) :
    let := tangentAlgebra d t
    ((Ideal.span (range G)).restrictScalars (HolGerm (ComplexModel d))).map
      (normalTaylorCoefficients d t q) = Submodule.span (HolGerm (ComplexModel d))
      (range fun b : monomialIndex t q × ι =>
        normalTaylorCoefficients d t q (normalWord d t b.1*G b.2)) := by
  classical
  let := tangentAlgebra d t
  let T := normalTaylorCoefficients d t q
  let C := Submodule.span (HolGerm (ComplexModel d))
    (range fun b : monomialIndex t q × ι => T (normalWord d t b.1*G b.2))
  apply le_antisymm
  · rintro v ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
    rw [← ha, map_sum]
    apply Submodule.sum_mem
    intro i _
    have hle : Submodule.span (HolGerm (ComplexModel d))
        (range fun w : monomialIndex t q => T (normalWord d t w*G i)) ≤ C := by
      apply Submodule.span_le.mpr
      rintro v ⟨w, rfl⟩
      exact Submodule.subset_span ⟨(w, i), rfl⟩
    exact hle (normalTaylorCoefficients_mul_mem_word_columns d t q (a i) (G i))
  · apply Submodule.span_le.mpr
    rintro v ⟨b, rfl⟩
    exact Submodule.mem_map.mpr ⟨normalWord d t b.1*G b.2,
      Ideal.mul_mem_left _ _ (Ideal.mem_span_range_self (x := b.2)), rfl⟩

/-- Internally chosen genuine ORIGINAL holomorphic generators give full relative ideal columns at ALL degrees. -/
theorem exists_original_generators_normalTaylor_columns (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    ∃ (r : ℕ) (G : Fin r → ComplexModel (d+t) → ℂ)
      (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)), DifferentiableAt ℂ (G i) z),
      Ideal.span (range fun i => HolGerm.mk (G i) (hG i)) = I ∧
      ∀ q : ℕ, (I.restrictScalars (HolGerm (ComplexModel d))).map (normalTaylorCoefficients d t q) =
        Submodule.span (HolGerm (ComplexModel d))
          (range fun b : monomialIndex t q × Fin r =>
            normalTaylorCoefficients d t q (normalWord d t b.1*HolGerm.mk (G b.2) (hG b.2))) := by
  let := tangentAlgebra d t
  let := isNoetherianRing_holGerm_euclidean (d+t)
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  choose G hG hrep using fun i => HolGerm.exists_eq_mk (g i)
  have heq : (fun i => HolGerm.mk (G i) (hG i)) = g := funext fun i => (hrep i).symm
  have hspan : Ideal.span (range fun i => HolGerm.mk (G i) (hG i)) = I := by
    rw [heq]
    exact hg
  refine ⟨r, G, hG, hspan, ?_⟩
  intro q
  rw [← hspan]
  exact map_span_ideal_normalTaylorCoefficients_eq_word_columns d t q _

/-- The actual whole coefficient image followed by quotient by the image of the ENTIRE original ideal. -/
def relativeIdealCoefficientQuotientMap (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)]
      (LinearMap.range (normalTaylorCoefficients d t q) ⧸
        (I.restrictScalars (HolGerm (ComplexModel d))).map
          (normalTaylorCoefficients d t q).rangeRestrict) :=
  letI := tangentAlgebra d t
  ((I.restrictScalars (HolGerm (ComplexModel d))).map
    (normalTaylorCoefficients d t q).rangeRestrict).mkQ.comp
      (normalTaylorCoefficients d t q).rangeRestrict

/-- The actual second coefficient quotient has the WHOLE original kernel I+J^q. -/
theorem ker_relativeIdealCoefficientQuotientMap (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let := tangentAlgebra d t
    LinearMap.ker (relativeIdealCoefficientQuotientMap d t q I) =
      (I ⊔ normalIdeal d t ^ q).restrictScalars (HolGerm (ComplexModel d)) := by
  let := tangentAlgebra d t
  let T := normalTaylorCoefficients d t q
  let W := (I.restrictScalars (HolGerm (ComplexModel d))).map T.rangeRestrict
  ext g
  rw [LinearMap.mem_ker]
  change W.mkQ (T.rangeRestrict g) = 0 ↔ g ∈ I ⊔ normalIdeal d t ^ q
  change T.rangeRestrict g ∈ LinearMap.ker W.mkQ ↔ _
  rw [Submodule.ker_mkQ]
  constructor
  · intro hg
    obtain ⟨a, ha, he⟩ := Submodule.mem_map.mp hg
    have hrem : g-a ∈ normalIdeal d t ^ q := by
      apply (normalTaylorCoefficients_eq_iff d t q g a).mp
      exact (congrArg Subtype.val he).symm
    have ha' : a ∈ I ⊔ normalIdeal d t ^ q := (show I ≤ I ⊔ normalIdeal d t ^ q from le_sup_left) ha
    have hr' : g-a ∈ I ⊔ normalIdeal d t ^ q :=
      (show normalIdeal d t ^ q ≤ I ⊔ normalIdeal d t ^ q from le_sup_right) hrem
    simpa only [add_sub_cancel] using Ideal.add_mem _ ha' hr'
  · intro hg
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hg
    have hz : T b = 0 := normalTaylorCoefficients_eq_zero_of_mem d t q b hb
    apply Submodule.mem_map.mpr
    refine ⟨a, ha, ?_⟩
    apply Subtype.ext
    change T a = T g
    rw [← he, map_add, hz, add_zero]

/-- The literal ENTIRE original ideal quotient is genuinely the actual whole relative coefficient-image quotient. -/
def relativeIdealTaylorQuotientEquiv (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ normalIdeal d t ^ q)) ≃ₗ[HolGerm (ComplexModel d)]
      (LinearMap.range (normalTaylorCoefficients d t q) ⧸
        (I.restrictScalars (HolGerm (ComplexModel d))).map
          (normalTaylorCoefficients d t q).rangeRestrict) :=
  letI := tangentAlgebra d t
  let F := relativeIdealCoefficientQuotientMap d t q I
  (Submodule.quotEquivOfEq _ _ (ker_relativeIdealCoefficientQuotientMap d t q I).symm).trans
    (F.quotKerEquivOfSurjective (Submodule.mkQ_surjective _ |>.comp
      (normalTaylorCoefficients d t q).surjective_rangeRestrict))

/-- Actual nonlinear flattening transports the genuine Taylor tuple over its INTERNALLY transported whole base algebra. -/
def transportedNormalTaylorCoefficients (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t))) :
    letI := transportedNormalAlgebra d t E
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)]
      (monomialIndex t q → HolGerm (ComplexModel d)) :=
  letI := transportedNormalAlgebra d t E
  { toFun := fun g => normalTaylorCoefficients d t q (E.symm g)
    map_add' := fun g h => by rw [map_add, map_add]
    map_smul' := fun a g => by
      funext w
      change relativeTaylorCoefficient d t (List.ofFn w.2)
        (E.symm (E (tangentPullback d t a)*g)) =
          a*relativeTaylorCoefficient d t (List.ofFn w.2) (E.symm g)
      rw [map_mul, E.symm_apply_apply]
      exact relativeTaylorCoefficient_tangent_mul d t _ a _ }

/-- Genuine entire nonlinear germ transport preserves the COMPLETE original normal-power Taylor kernel. -/
theorem ker_transportedNormalTaylorCoefficients (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t))) :
    let := transportedNormalAlgebra d t E
    LinearMap.ker (transportedNormalTaylorCoefficients d t q E) =
      (Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q).restrictScalars (HolGerm (ComplexModel d)) := by
  let := transportedNormalAlgebra d t E
  ext g
  rw [LinearMap.mem_ker, ← Ideal.map_pow]
  change normalTaylorCoefficients d t q (E.symm g) = 0 ↔
    g ∈ Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t ^ q)
  constructor
  · intro hz
    have hm := mem_normalIdeal_pow_of_normalTaylorCoefficients_eq_zero d t q (E.symm g) hz
    simpa only [RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_ringEquiv, E.apply_symm_apply] using Ideal.mem_map_of_mem E.toRingEquiv.toRingHom hm
  · intro hm
    obtain ⟨h, hh, he⟩ := (Ideal.mem_map_iff_of_surjective E.toRingEquiv.toRingHom E.surjective).mp hm
    have he' : E.symm g = h := by
      change E h = g at he
      rw [← he, E.symm_apply_apply]
    rw [he']
    exact normalTaylorCoefficients_eq_zero_of_mem d t q h hh

section RegularProducer
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ORIGINAL regular centre geometry internally produces all actual Taylor maps with their entire ORIGINAL vanishing-ideal-power kernels. -/
theorem exists_regular_relative_Taylor_kernel (C : Set M) (x : M)
    (hreg : RegularAtDim (n := d+t) C x d) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let E := flatteningGermEquiv _ Φ h0
      let K := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x x (mem_chart_source _ x)
      letI := transportedNormalAlgebra d t E
      ∀ q : ℕ, LinearMap.ker (transportedNormalTaylorCoefficients d t q E) =
        (K ^ q).restrictScalars (HolGerm (ComplexModel d)) := by
  obtain ⟨Φ, hsrc, h0, hflat, hK, _, _, _⟩ := exists_regular_relative_ideal C x hreg
  refine ⟨Φ, hsrc, h0, hflat, ?_⟩
  dsimp only
  intro q
  rw [ker_transportedNormalTaylorCoefficients, hK]

end RegularProducer
end
end Hironaka.HironakaRelativeNormalTaylorCoefficients
