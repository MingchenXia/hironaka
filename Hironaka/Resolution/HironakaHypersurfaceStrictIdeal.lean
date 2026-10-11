/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupStrictIdealControlled
import Hironaka.Resolution.HironakaHypersurfaceStageCenters
import Hironaka.Analytic.ActualReducedHolomorphicEquation
import Hironaka.Analytic.ActualPrimeRegularDifferentialAvoidance
import Hironaka.Analytic.ActualInvertibleIdealDifference
import Hironaka.Analytic.HolomorphicCoordinatePrime
import Hironaka.Analytic.SNCGlobalPrimeComponents
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-!
# Actual reducedness across a divisor and controlled hypersurface ideals

Blueprint: `hironaka-hypersurface-strict-ideal-extension.tex`.
The local reducedness producer uses actual prime factorization and a genuine
regular differential avoiding both original tests. The off-divisor hypothesis
is radicality of the actual local principal ideal, not a global transform
certificate. General G8 and finite restarted descent remain separate.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaHypersurfaceStrictIdeal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open RelativePrincipalizationSpan InvertibleIdealQuotient IdealWeightPowers
open BlowupTowers

noncomputable section

/-- A genuine principal equation, reduced off a coprime divisor, is reduced
at the original germ. Radicality is the literal closure under positive powers
of the local holomorphic span. No generic point or factorization is supplied. -/
theorem squarefree_germ_of_reduced_off_divisor {m : ℕ}
    (f e : ComplexModel (m + 1) → ℂ)
    (hf : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ f x)
    (he : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ e x)
    (hF : HolGerm.mk f hf ≠ 0)
    (hcoprime : ∀ P : HolGerm (ComplexModel (m + 1)), Prime P →
      P ∣ HolGerm.mk f hf → ¬ P ∣ HolGerm.mk e he)
    (hred : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), e x ≠ 0 →
      ∀ (g : ComplexModel (m + 1) → ℂ) (k : ℕ), 0 < k →
        HolomorphicAt (m + 1) g x →
        IsInSpanAt (n := m + 1) (· = f) x (fun y => g y ^ k) →
        IsInSpanAt (n := m + 1) (· = f) x g) :
    Squarefree (HolGerm.mk f hf) := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  apply (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hF).mpr
  intro P hPir hdiv
  have hP : Prime P := irreducible_iff_prime.mp hPir
  have hfin : FiniteMultiplicity P (HolGerm.mk f hf) := .of_prime_left hP hF
  let k := multiplicity P (HolGerm.mk f hf)
  have hk : 2 ≤ k := hfin.le_multiplicity_of_pow_dvd (by simpa [pow_two] using hdiv)
  obtain ⟨B, hfac, hPB⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  obtain ⟨q, hq, hQ⟩ := HolGerm.exists_eq_mk P
  obtain ⟨b, hb, hB⟩ := HolGerm.exists_eq_mk B
  have hQprime : Prime (HolGerm.mk q hq) := hQ ▸ hP
  have hPE : ¬ HolGerm.mk q hq ∣ HolGerm.mk e he := by
    rw [← hQ]
    exact hcoprime P hP ((dvd_mul_right P P).trans hdiv)
  have hQB : ¬ HolGerm.mk q hq ∣ HolGerm.mk b hb := by rwa [← hQ, ← hB]
  let a : Bool → ComplexModel (m + 1) → ℂ := fun i => if i then b else e
  have ha : ∀ i, ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (a i) x := by
    intro i
    cases i <;> first | exact he | exact hb
  have hnot : ∀ i, ¬ HolGerm.mk q hq ∣ HolGerm.mk (a i) (ha i) := by
    intro i
    cases i <;> first | exact hPE | exact hQB
  obtain ⟨v, _, hfreq⟩ :=
    ActualPrimeRegularDifferentialAvoidance.exists_direction_frequently_regular_avoiding_tests
      q hq hQprime a ha hnot
  have hfactor : f =ᶠ[𝓝 (0 : ComplexModel (m + 1))] fun y => q y ^ k * b y := by
    apply HolGerm.mk_eq_mk_iff.mp (show HolGerm.mk f hf =
      HolGerm.mk (fun y => q y ^ k * b y)
        (eventually_differentiableAt_mul (eventually_differentiableAt_pow hq k) hb) from ?_)
    rw [HolGerm.mk_mul (fun y => q y ^ k) b
      (eventually_differentiableAt_pow hq k) hb, HolGerm.mk_pow q hq k, ← hQ, ← hB]
    exact hfac
  obtain ⟨x, hx, hxred, hxq, hxb, hxfn⟩ := (hfreq.and_eventually
    (hred.and (hq.eventually_nhds.and (hb.eventually_nhds.and
      hfactor.eventually_nhds)))).exists
  have hxfn' : f =ᶠ[𝓝 x] fun y => q y ^ k * b y := hxfn
  have hqx0 := hx.1
  have hdq := hx.2.2.2.1
  have hex : e x ≠ 0 := hx.2.2.2.2 false
  have hbx : b x ≠ 0 := hx.2.2.2.2 true
  have hqhol : HolomorphicAt (m + 1) q x := hxq.mono fun _ hy => hy.mdifferentiableAt
  have hbne : ∀ᶠ y in 𝓝 x, b y ≠ 0 := hxb.self_of_nhds.continuousAt.eventually_ne hbx
  have hbinv : HolomorphicAt (m + 1) (fun y => (b y)⁻¹) x := by
    filter_upwards [hxb, hbne] with y hy hne
    exact (hy.inv hne).mdifferentiableAt
  have hqpow : IsInSpanAt (n := m + 1) (· = f) x (fun y => q y ^ k) := by
    refine isInSpanAt_of_eq_mul rfl
      (hxq.mono fun _ hy => (hy.pow k).mdifferentiableAt) hbinv ?_
    filter_upwards [hxfn, hbne] with y hy hne
    rw [hy]
    field_simp
  obtain ⟨_, c, hc, hqc⟩ := isInSpanAt_eq_iff.mp
    (hxred hex q k (by omega) hqhol hqpow)
  have hfx0 : f x = 0 := by
    calc f x = q x ^ k * b x := hxfn'.self_of_nhds
      _ = 0 := by rw [hqx0, zero_pow (by omega : k ≠ 0), zero_mul]
  have hdf : fderiv ℂ f x = 0 := by
    rw [hxfn'.fderiv_eq]
    change fderiv ℂ ((fun y => q y ^ k) * b) x = 0
    rw [((hxq.self_of_nhds.hasFDerivAt.pow k).mul hxb.self_of_nhds.hasFDerivAt).fderiv]
    ext w
    simp [hqx0, zero_pow (by omega : k - 1 ≠ 0), zero_pow (by omega : k ≠ 0)]
  apply hdq
  rw [hqc.fderiv_eq]
  change fderiv ℂ (c * f) x v = 0
  rw [((hc.self_of_nhds.differentiableAt.hasFDerivAt).mul
    (((hxq.self_of_nhds.pow k).mul hxb.self_of_nhds).congr_of_eventuallyEq
      hxfn').hasFDerivAt).fderiv]
  simp [hfx0, hdf]

/-- A member outside the actual exceptional vanishing ideal excludes the
exceptional coordinate from the whole original local generator. -/
theorem not_coordinate_dvd_of_nonexceptional_witness {n : ℕ}
    (R : GermIdeal n (ComplexModel n)) (f : ComplexModel n → ℂ)
    (hf : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ f x) (j : Fin n)
    (hgen : ∀ g, R.mem 0 g ↔ IsInSpanAt (n := n) (· = f) 0 g)
    (hwitness : ∃ g, R.mem 0 g ∧
      ¬ (vanishingIdeal (n := n) {z : ComplexModel n | z j = 0}).mem 0 g) :
    ¬ HolGerm.mk (fun z : ComplexModel n => z j)
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j) ∣ HolGerm.mk f hf := by
  rintro ⟨B, hB⟩
  obtain ⟨b, hb, hrep⟩ := HolGerm.exists_eq_mk B
  have hfactor : f =ᶠ[𝓝 (0 : ComplexModel n)] fun z => z j * b z := by
    apply HolGerm.mk_eq_mk_iff.mp (show HolGerm.mk f hf =
      HolGerm.mk (fun z => z j * b z)
        (eventually_differentiableAt_mul
          (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j) hb) from ?_)
    rw [HolGerm.mk_mul _ _
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j) hb, ← hrep]
    exact hB
  have hfE : (vanishingIdeal (n := n) {z : ComplexModel n | z j = 0}).mem 0 f := by
    refine ⟨hf.mono fun _ hx => hx.mdifferentiableAt, ?_⟩
    filter_upwards [hfactor] with z hz hzE
    rw [hz, hzE, zero_mul]
  obtain ⟨g, hg, hng⟩ := hwitness
  exact hng (BlowupStrictIdeal.mem_vanishingIdeal_of_isInSpanAt'
    (fun a ha => ha ▸ hfE) ((hgen g).mp hg))

/-- Actual factorization and prime avoidance exclude a zero supported only
on the smooth exceptional coordinate, when the whole equation has no such factor. -/
theorem ne_zero_at_zero_of_zero_locus_subset_coordinate {n : ℕ}
    (f : ComplexModel n → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hF : HolGerm.mk f hf ≠ 0) (j : Fin n)
    (hnot : ¬ HolGerm.mk (fun z : ComplexModel n => z j)
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j) ∣ HolGerm.mk f hf)
    (hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel n), f z = 0 → z j = 0) : f 0 ≠ 0 := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel n)) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
  intro hf0
  have hnonunit : ¬IsUnit (HolGerm.mk f hf) := by
    intro hunit
    have hval := (HolGerm.isUnit_iff_eval_ne_zero _).mp hunit
    exact hval (by simpa using hf0)
  obtain ⟨P, hPir, hPF⟩ := WfDvdMonoid.exists_irreducible_factor hnonunit hF
  have hP : Prime P := irreducible_iff_prime.mp hPir
  have hPE : ¬P ∣ HolGerm.mk (fun z : ComplexModel n => z j)
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j) := by
    intro hdiv
    exact hnot ((hPir.associated_of_dvd
      (HolomorphicCoordinatePrime.prime_coordinate_germ j).irreducible hdiv).symm.dvd.trans hPF)
  obtain ⟨q, hq, hQ⟩ := HolGerm.exists_eq_mk P
  obtain ⟨B, hB⟩ := hPF
  obtain ⟨b, hb, hrep⟩ := HolGerm.exists_eq_mk B
  have hfactor : f =ᶠ[𝓝 (0 : ComplexModel n)] fun z => q z * b z := by
    apply HolGerm.mk_eq_mk_iff.mp (show HolGerm.mk f hf =
      HolGerm.mk (fun z => q z * b z) (eventually_differentiableAt_mul hq hb) from ?_)
    rw [HolGerm.mk_mul q b hq hb, ← hQ, ← hrep]
    exact hB
  have hfreq := ActualPrimeGermGenericAvoidance.frequently_zero_avoiding_finite_family
    q hq (hQ ▸ hP) (fun _ : Fin 1 => fun z : ComplexModel n => z j)
    (fun _ => HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j)
    (fun _ => by simpa only [← hQ] using hPE)
  obtain ⟨z, ⟨hqz, hne⟩, hfz, hzz⟩ :=
    (hfreq.and_eventually (hfactor.and hzero)).exists
  exact hne 0 (hzz (by simpa only [hqz, zero_mul] using hfz))

/-- For a genuine smooth coordinate divisor, the actual nondivisibility
of the equation excludes every common prime factor internally. -/
theorem squarefree_germ_of_reduced_off_coordinate {m : ℕ}
    (f : ComplexModel (m + 1) → ℂ)
    (hf : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ f x) (hF : HolGerm.mk f hf ≠ 0)
    (j : Fin (m + 1))
    (hnot : ¬ HolGerm.mk (fun z : ComplexModel (m + 1) => z j)
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j) ∣ HolGerm.mk f hf)
    (hred : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), x j ≠ 0 →
      ∀ (g : ComplexModel (m + 1) → ℂ) (k : ℕ), 0 < k →
        HolomorphicAt (m + 1) g x →
        IsInSpanAt (n := m + 1) (· = f) x (fun y => g y ^ k) →
        IsInSpanAt (n := m + 1) (· = f) x g) :
    Squarefree (HolGerm.mk f hf) := by
  apply squarefree_germ_of_reduced_off_divisor f (fun z => z j) hf
    (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate j) hF ?_ hred
  intro P hP hPF hPE
  exact hnot ((hP.irreducible.associated_of_dvd
    (HolomorphicCoordinatePrime.prime_coordinate_germ j).irreducible hPE).symm.dvd.trans hPF)

/-- The actual squarefree equation generates its whole reduced vanishing ideal. -/
theorem vanishingIdeal_eq_span_of_squarefree {n : ℕ} (f : ComplexModel n → ℂ)
    (hf : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ f x) (hF : HolGerm.mk f hf ≠ 0)
    (hs : Squarefree (HolGerm.mk f hf)) :
    AnalyticGermDecomposition.vanishingIdeal {z | f z = 0} = Ideal.span {HolGerm.mk f hf} := by
  obtain ⟨r, hr, _, hsR, hI, hz⟩ := ActualReducedHolomorphicEquation.exists_reduced_equation f hf hF
  obtain ⟨u, hu, hu0, _, hunit⟩ :=
    ActualReducedHolomorphicEquation.exists_unit_transition_of_reduced_zero_germ f r hf hr hs hsR hz
  have hU : IsUnit (HolGerm.mk u hu) :=
    (HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simpa using hu0)
  have hmul : HolGerm.mk f hf = HolGerm.mk u hu * HolGerm.mk r hr := by
    exact (HolGerm.mk_eq_mk_iff.mpr hunit).trans (HolGerm.mk_mul u r hu hr)
  rw [hI]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ rfl
    apply (Ideal.span {HolGerm.mk f hf}).unit_mul_mem_iff_mem hU |>.mp
    rw [← hmul]
    exact Ideal.mem_span_singleton_self _
  · apply Ideal.span_le.mpr
    rintro _ rfl
    rw [hmul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n X] [IsComplexManifold n Y]

private theorem holomorphicAt_flatInverse_iff {x y : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hy : y ∈ BlowupFlatCoordinates.flatDomain Φ) (f : X → ℂ) :
    HolomorphicAt n (fun z => f ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
      (Φ.toFun (chartAt (ComplexModel n) x y)) ↔ HolomorphicAt n f y := by
  constructor
  · intro hf
    have h := BlowupFlatCoordinates.holomorphicAt_comp_flat Φ hy
      (hf.mono fun _ hz => hz.differentiableAt)
    refine h.congr ?_
    filter_upwards [(BlowupFlatCoordinates.isOpen_flatDomain Φ).mem_nhds hy] with z hz
    exact congrArg f (BlowupFlatCoordinates.flatInverse_flat Φ hz)
  · intro hf
    have hT := BlowupFlatCoordinates.tendsto_flatInverse Φ hy
    have htarget := Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun hy.2)
    filter_upwards [htarget, hT.eventually hf.eventually] with z hz hfz
    have hinvT := hsrc (Φ.mapsTo_invFun hz)
    have hm := hfz.mdifferentiableAt.comp (Φ.invFun z)
      (BlowupFlatCoordinates.mdifferentiableAt_chart_symm hinvT)
    exact ((mdifferentiableAt_iff_differentiableAt.mp hm).comp z
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz))).mdifferentiableAt

private theorem isInSpanAt_flatInverse_iff {x y : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hy : y ∈ BlowupFlatCoordinates.flatDomain Φ) (f g : X → ℂ) :
    IsInSpanAt (n := n) (· = f) y g ↔
      IsInSpanAt (n := n)
        (· = fun z => f ((chartAt (ComplexModel n) x).symm (Φ.invFun z)))
        (Φ.toFun (chartAt (ComplexModel n) x y))
        (fun z => g ((chartAt (ComplexModel n) x).symm (Φ.invFun z))) := by
  have hT := BlowupFlatCoordinates.tendsto_flatInverse Φ hy
  have hforward : Tendsto (fun z : X => Φ.toFun (chartAt (ComplexModel n) x z))
      (𝓝 y) (𝓝 (Φ.toFun (chartAt (ComplexModel n) x y))) :=
    ((Φ.toFun_holomorphic.differentiableAt
      (Φ.isOpen_source.mem_nhds hy.2)).continuousAt.comp
        ((chartAt (ComplexModel n) x).continuousAt hy.1)).tendsto
  constructor
  · intro hg
    obtain ⟨hghol, a, ha, heq⟩ := isInSpanAt_eq_iff.mp hg
    exact isInSpanAt_of_eq_mul rfl
      ((holomorphicAt_flatInverse_iff Φ hsrc hy g).mpr hghol)
      ((holomorphicAt_flatInverse_iff Φ hsrc hy a).mpr ha) (hT.eventually heq)
  · intro hg
    obtain ⟨hghol, a, ha, heq⟩ := isInSpanAt_eq_iff.mp hg
    refine isInSpanAt_of_eq_mul rfl
      ((holomorphicAt_flatInverse_iff Φ hsrc hy g).mp hghol)
      (BlowupFlatCoordinates.holomorphicAt_comp_flat Φ hy
        (ha.mono fun _ hz => hz.differentiableAt)) ?_
    filter_upwards [(BlowupFlatCoordinates.isOpen_flatDomain Φ).mem_nhds hy,
      hforward.eventually heq] with z hz heqz
    simpa only [BlowupFlatCoordinates.flatInverse_flat Φ hz] using heqz

private theorem exists_nonexceptional_generator_chart {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    (R : GermIdeal (m + 1) M) (hR : R.IsInvertible) {E : Set M} {x : M}
    (hx : RegularAtDim (n := m + 1) E x m)
    (hwitness : ∃ g, R.mem x g ∧ ¬ (vanishingIdeal (n := m + 1) E).mem x g) :
    ∃ (U : Set M) (f : M → ℂ)
      (Φ : LocalHolomorphicEquivAt (n := m + 1) (chartAt (ComplexModel (m + 1)) x x)),
      IsOpen U ∧ x ∈ U ∧
      MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) f U ∧
      (∀ y ∈ U, ∀ g, R.mem y g ↔ IsInSpanAt (n := m + 1) (· = f) y g) ∧
      Φ.source ⊆ (chartAt (ComplexModel (m + 1)) x).target ∧
      Φ.toFun (chartAt (ComplexModel (m + 1)) x x) = 0 ∧
      (∀ y ∈ BlowupFlatCoordinates.flatDomain Φ,
        y ∈ E ↔ BlowupFlatCoordinates.flatCoord Φ (Fin.last m) y = 0) ∧
      ∃ hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ
          (fun w => f ((chartAt (ComplexModel (m + 1)) x).symm (Φ.invFun w))) z,
        HolGerm.mk (fun w => f ((chartAt (ComplexModel (m + 1)) x).symm (Φ.invFun w))) hF ≠ 0 ∧
        ¬ HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
          (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate (Fin.last m)) ∣
            HolGerm.mk (fun w => f ((chartAt (ComplexModel (m + 1)) x).symm (Φ.invFun w))) hF := by
  obtain ⟨U, hU, hxU, f, hf, hnon, hgen⟩ := hR x
  obtain ⟨_, _, Φ, hsrc, h0, hflat⟩ := hx
  change Φ.source ⊆ (chartAt (ComplexModel (m + 1)) x).target at hsrc
  change Φ.toFun (chartAt (ComplexModel (m + 1)) x x) = 0 at h0
  have hflat' : ∀ y ∈ BlowupFlatCoordinates.flatDomain Φ,
      y ∈ E ↔ BlowupFlatCoordinates.flatCoord Φ (Fin.last m) y = 0 := by
    intro y hy
    refine (hflat hy.1 hy.2).trans ?_
    constructor
    · intro h
      exact h (Fin.last m) le_rfl
    · intro h i hi
      have heq : i = Fin.last m := Fin.ext (by dsimp at hi ⊢; omega)
      simpa [heq, BlowupFlatCoordinates.flatCoord, complexChartAt] using h
  let T : ComplexModel (m + 1) → M := fun z =>
    (chartAt (ComplexModel (m + 1)) x).symm (Φ.invFun z)
  let F : ComplexModel (m + 1) → ℂ := f ∘ T
  have hxflat := BlowupFlatCoordinates.mem_flatDomain_self Φ
  have hT : Tendsto T (𝓝 0) (𝓝 x) := by
    simpa only [h0] using BlowupFlatCoordinates.tendsto_flatInverse Φ hxflat
  have hforward : Tendsto (fun y : M => Φ.toFun (chartAt (ComplexModel (m + 1)) x y))
      (𝓝 x) (𝓝 (0 : ComplexModel (m + 1))) := by
    simpa only [Function.comp_def, h0] using ((Φ.toFun_holomorphic.differentiableAt
      (Φ.isOpen_source.mem_nhds hxflat.2)).continuousAt.comp
        ((chartAt (ComplexModel (m + 1)) x).continuousAt hxflat.1)).tendsto
  have hfh : HolomorphicAt (m + 1) f x := holomorphicAt_of_mdifferentiableOn hU hf hxU
  have hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ F z := by
    have hh := (holomorphicAt_flatInverse_iff Φ hsrc hxflat f).mpr hfh
    rw [h0] at hh
    exact hh.mono fun _ hz => hz.differentiableAt
  have hFne : HolGerm.mk F hF ≠ 0 := by
    intro hzero
    have hFzero : F =ᶠ[𝓝 (0 : ComplexModel (m + 1))] fun _ => 0 := by
      exact HolGerm.mk_eq_mk_iff.mp (hzero.trans HolGerm.mk_zero.symm)
    have hfzero : f =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(BlowupFlatCoordinates.isOpen_flatDomain Φ).mem_nhds hxflat,
        hforward.eventually hFzero] with y hy hFy
      simpa only [F, Function.comp_apply, T, BlowupFlatCoordinates.flatInverse_flat Φ hy] using hFy
    have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧ f y = 0 := by
      filter_upwards [hU.mem_nhds hxU, hfzero] with y hy hfy
      exact ⟨hy, hfy⟩
    obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hev
    obtain ⟨y, hy, hfy⟩ := hnon V hV (fun z hz => (hVsub hz).1) ⟨x, hxV⟩
    exact hfy (hVsub hy).2
  let A : GermIdeal (m + 1) (ComplexModel (m + 1)) :=
    ⟨fun z g => IsInSpanAt (n := m + 1) (· = F) z g⟩
  have hnot : ¬ HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate (Fin.last m)) ∣
        HolGerm.mk F hF := by
    apply not_coordinate_dvd_of_nonexceptional_witness A F hF (Fin.last m) (fun _ => Iff.rfl)
    obtain ⟨g, hg, hng⟩ := hwitness
    have hgspan := (isInSpanAt_flatInverse_iff Φ hsrc hxflat f g).mp ((hgen x hxU g).mp hg)
    rw [h0] at hgspan
    refine ⟨g ∘ T, hgspan, fun hgE => hng ?_⟩
    refine ⟨GermIdeal.IsInvertible.holomorphicAt_mem hR hg, ?_⟩
    filter_upwards [(BlowupFlatCoordinates.isOpen_flatDomain Φ).mem_nhds hxflat,
      hforward.eventually hgE.2] with y hy hgy hyE
    have hz := hgy ((hflat' y hy).mp hyE)
    simpa only [Function.comp_apply, T, BlowupFlatCoordinates.flatInverse_flat Φ hy] using hz
  exact ⟨U, f, Φ, hU, hxU, hf, hgen, hsrc, h0, hflat', hF, hFne, hnot⟩

/-- Actual invertibility, original off-divisor stalks and genuine nonexceptional
members force support equality across the whole smooth divisor. -/
theorem zeroLocus_eq_of_off_smooth_divisor {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    (R : GermIdeal (m + 1) M) (hR : R.IsInvertible) {E S : Set M}
    (hS : IsClosed S) (hdense : S ⊆ closure (S \ E))
    (hEreg : ∀ x ∈ E, RegularAtDim (n := m + 1) E x m)
    (hoff : ∀ x, x ∉ E → ∀ g, R.mem x g ↔ (vanishingIdeal (n := m + 1) S).mem x g)
    (hwitness : ∀ x ∈ E, ∃ g, R.mem x g ∧ ¬ (vanishingIdeal (n := m + 1) E).mem x g) :
    R.zeroLocus = S := by
  have hcoh := DivisorMetric.isCoherent_of_isInvertible hR
  have hSzero : S ⊆ R.zeroLocus := hdense.trans (closure_minimal (by
    rintro x ⟨hxS, hxE⟩ g hg
    exact ((hoff x hxE g).mp hg).2.self_of_nhds hxS)
      (OrderTaylor.isClosed_zeroLocus_of_isCoherent hcoh))
  apply Subset.antisymm _ hSzero
  intro x hxR
  by_contra hxS
  have hunit : ∀ {y : M}, y ∉ S → (vanishingIdeal (n := m + 1) S).mem y (fun _ => (1 : ℂ)) := by
    intro y hy
    refine ⟨holomorphicAt_const 1, ?_⟩
    filter_upwards [hS.isOpen_compl.mem_nhds hy] with z hz hzS
    exact False.elim (hz hzS)
  by_cases hxE : x ∈ E
  · obtain ⟨U, f, Φ, hU, hxU, hf, hgen, hsrc, h0, hflat, hF, hFne, hnot⟩ :=
      exists_nonexceptional_generator_chart R hR (hEreg x hxE) (hwitness x hxE)
    let T : ComplexModel (m + 1) → M := fun z =>
      (chartAt (ComplexModel (m + 1)) x).symm (Φ.invFun z)
    let F : ComplexModel (m + 1) → ℂ := f ∘ T
    have hxflat := BlowupFlatCoordinates.mem_flatDomain_self Φ
    have hT : Tendsto T (𝓝 0) (𝓝 x) := by
      simpa only [h0] using BlowupFlatCoordinates.tendsto_flatInverse Φ hxflat
    have hT0 : T 0 = x := by
      simpa only [T, h0] using BlowupFlatCoordinates.flatInverse_flat Φ hxflat
    have htarget : (0 : ComplexModel (m + 1)) ∈ Φ.target := by
      rw [← h0]
      exact Φ.mapsTo_toFun hxflat.2
    have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), F z = 0 → z (Fin.last m) = 0 := by
      filter_upwards [Φ.isOpen_target.mem_nhds htarget,
        hT.eventually (hU.mem_nhds hxU), hT.eventually (hS.isOpen_compl.mem_nhds hxS)]
        with z hzT hzU hzS hfz
      have hzflat := BlowupFlatCoordinates.flatInverse_mem Φ hzT hsrc
      by_contra hzlast
      have hzE : T z ∉ E := by
        intro hzE
        have heq := (hflat (T z) hzflat.1).mp hzE
        change Φ.toFun (chartAt (ComplexModel (m + 1)) x (T z)) (Fin.last m) = 0 at heq
        rw [hzflat.2] at heq
        exact hzlast heq
      have h1 := (hgen (T z) hzU _).mp ((hoff (T z) hzE _).mpr (hunit hzS))
      obtain ⟨_, a, _, heq⟩ := isInSpanAt_eq_iff.mp h1
      have hb : (1 : ℂ) = a (T z) * f (T z) := heq.self_of_nhds
      have hfz' : f (T z) = 0 := hfz
      rw [hfz', mul_zero] at hb
      exact one_ne_zero hb
    have hne := ne_zero_at_zero_of_zero_locus_subset_coordinate F hF hFne (Fin.last m) hnot hzero
    apply hne
    have hfx : R.mem x f := (hgen x hxU f).mpr
      (isInSpanAt_self rfl (holomorphicAt_of_mdifferentiableOn hU hf hxU))
    change f (T 0) = 0
    rw [hT0]
    exact hxR f hfx
  · exact one_ne_zero (hxR _ ((hoff x hxE _).mpr (hunit hxS)))

private theorem squarefree_local_generator_of_off_divisor {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    (R : GermIdeal (m + 1) M) {E S : Set M} {x : M}
    (U : Set M) (hU : IsOpen U) (hxU : x ∈ U) (f : M → ℂ)
    (hgen : ∀ y ∈ U, ∀ g, R.mem y g ↔ IsInSpanAt (n := m + 1) (· = f) y g)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) (chartAt (ComplexModel (m + 1)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (m + 1)) x x) = 0)
    (hflat : ∀ y ∈ BlowupFlatCoordinates.flatDomain Φ,
      y ∈ E ↔ BlowupFlatCoordinates.flatCoord Φ (Fin.last m) y = 0)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ
      (fun w => f ((chartAt (ComplexModel (m + 1)) x).symm (Φ.invFun w))) z)
    (hFne : HolGerm.mk (fun w => f ((chartAt (ComplexModel (m + 1)) x).symm (Φ.invFun w))) hF ≠ 0)
    (hnot : ¬ HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate (Fin.last m)) ∣
      HolGerm.mk (fun w => f ((chartAt (ComplexModel (m + 1)) x).symm (Φ.invFun w))) hF)
    (hoff : ∀ y, y ∉ E → ∀ g, R.mem y g ↔ (vanishingIdeal (n := m + 1) S).mem y g) :
    Squarefree (HolGerm.mk (fun w => f ((chartAt (ComplexModel (m + 1)) x).symm (Φ.invFun w))) hF) := by
  let T : ComplexModel (m + 1) → M := fun z =>
    (chartAt (ComplexModel (m + 1)) x).symm (Φ.invFun z)
  let F : ComplexModel (m + 1) → ℂ := f ∘ T
  have hxflat := BlowupFlatCoordinates.mem_flatDomain_self Φ
  have hT : Tendsto T (𝓝 0) (𝓝 x) := by
    simpa only [h0] using BlowupFlatCoordinates.tendsto_flatInverse Φ hxflat
  have htarget : (0 : ComplexModel (m + 1)) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun hxflat.2
  apply squarefree_germ_of_reduced_off_coordinate F hF hFne (Fin.last m) hnot
  filter_upwards [Φ.isOpen_target.mem_nhds htarget, hT.eventually (hU.mem_nhds hxU)]
    with z hzT hzU
  intro hzlast g k hk hg hgp
  have hzflat := BlowupFlatCoordinates.flatInverse_mem Φ hzT hsrc
  have hzE : T z ∉ E := by
    intro hzE
    have heq := (hflat (T z) hzflat.1).mp hzE
    change Φ.toFun (chartAt (ComplexModel (m + 1)) x (T z)) (Fin.last m) = 0 at heq
    rw [hzflat.2] at heq
    exact hzlast heq
  let G : M → ℂ := fun y => g (Φ.toFun (chartAt (ComplexModel (m + 1)) x y))
  have hghol : HolomorphicAt (m + 1) G (T z) :=
    BlowupFlatCoordinates.holomorphicAt_comp_flat Φ hzflat.1
      (by rw [hzflat.2]; exact hg.mono fun _ hw => hw.differentiableAt)
  have hforward : Tendsto (fun y : M => Φ.toFun (chartAt (ComplexModel (m + 1)) x y))
      (𝓝 (T z)) (𝓝 z) := by
    simpa only [Function.comp_def, hzflat.2] using ((Φ.toFun_holomorphic.differentiableAt
      (Φ.isOpen_source.mem_nhds hzflat.1.2)).continuousAt.comp
        ((chartAt (ComplexModel (m + 1)) x).continuousAt hzflat.1.1)).tendsto
  have hgpow : R.mem (T z) (fun y => G y ^ k) := by
    apply (hgen (T z) hzU _).mpr
    obtain ⟨hgpHol, a, ha, heq⟩ := isInSpanAt_eq_iff.mp hgp
    refine isInSpanAt_of_eq_mul rfl
      (BlowupFlatCoordinates.holomorphicAt_comp_flat Φ hzflat.1
        (by rw [hzflat.2]; exact hgpHol.mono fun _ hw => hw.differentiableAt))
      (BlowupFlatCoordinates.holomorphicAt_comp_flat Φ hzflat.1
        (by rw [hzflat.2]; exact ha.mono fun _ hw => hw.differentiableAt)) ?_
    filter_upwards [(BlowupFlatCoordinates.isOpen_flatDomain Φ).mem_nhds hzflat.1,
      hforward.eventually heq] with y hy heqy
    simpa only [G, F, Function.comp_apply, T, BlowupFlatCoordinates.flatInverse_flat Φ hy] using heqy
  have hgvan : (vanishingIdeal (n := m + 1) S).mem (T z) G := by
    have hp := (hoff (T z) hzE _).mp hgpow
    refine ⟨hghol, ?_⟩
    filter_upwards [hp.2] with y hy hyS
    exact (pow_eq_zero_iff (by omega : k ≠ 0)).mp (hy hyS)
  have hspan := (isInSpanAt_flatInverse_iff Φ hsrc hzflat.1 f G).mp
    ((hgen (T z) hzU _).mp ((hoff (T z) hzE _).mpr hgvan))
  rw [hzflat.2] at hspan
  refine InvertibleIdealQuotient.IsInSpanAt.congr' hspan ?_
  filter_upwards [Φ.isOpen_target.mem_nhds hzT] with w hw
  have hm := BlowupFlatCoordinates.flatInverse_mem Φ hw hsrc
  exact congrArg g hm.2

/-- Whole ideal equality across a smooth exceptional divisor is produced
from actual invertibility, original off-divisor reduced stalks, density and
actual nonexceptional members. No whole transformed-ideal equality is an input. -/
theorem eq_vanishingIdeal_of_reduced_off_smooth_divisor {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    (R : GermIdeal (m + 1) M) (hR : R.IsInvertible) {E S : Set M}
    (hS : IsClosed S) (hdense : S ⊆ closure (S \ E))
    (hEreg : ∀ x ∈ E, RegularAtDim (n := m + 1) E x m)
    (hoff : ∀ x, x ∉ E → ∀ g, R.mem x g ↔ (vanishingIdeal (n := m + 1) S).mem x g)
    (hwitness : ∀ x ∈ E, ∃ g, R.mem x g ∧ ¬ (vanishingIdeal (n := m + 1) E).mem x g) :
    R = vanishingIdeal (n := m + 1) S := by
  have hzero := zeroLocus_eq_of_off_smooth_divisor R hR hS hdense hEreg hoff hwitness
  have hcoh := DivisorMetric.isCoherent_of_isInvertible hR
  have hle : R.Le (vanishingIdeal (n := m + 1) S) :=
    BlowupTowerTransforms.le_vanishingIdeal_of_subset_zeroLocus hcoh (by rw [hzero])
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨hle x g, fun hg => ?_⟩)
  by_cases hxE : x ∈ E
  · obtain ⟨U, f, Φ, hU, hxU, _, hgen, hsrc, h0, hflat, hF, hFne, hnot⟩ :=
      exists_nonexceptional_generator_chart R hR (hEreg x hxE) (hwitness x hxE)
    have hsF := squarefree_local_generator_of_off_divisor R U hU hxU f hgen Φ hsrc h0
      hflat hF hFne hnot hoff
    let T : ComplexModel (m + 1) → M := fun z =>
      (chartAt (ComplexModel (m + 1)) x).symm (Φ.invFun z)
    let F : ComplexModel (m + 1) → ℂ := f ∘ T
    let G : ComplexModel (m + 1) → ℂ := g ∘ T
    have hxflat := BlowupFlatCoordinates.mem_flatDomain_self Φ
    have hT : Tendsto T (𝓝 0) (𝓝 x) := by
      simpa only [h0] using BlowupFlatCoordinates.tendsto_flatInverse Φ hxflat
    have hG : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ G z := by
      have hh := (holomorphicAt_flatInverse_iff Φ hsrc hxflat g).mpr hg.1
      rw [h0] at hh
      exact hh.mono fun _ hz => hz.differentiableAt
    have hmem : HolGerm.mk G hG ∈ AnalyticGermDecomposition.vanishingIdeal {z | F z = 0} := by
      apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
      filter_upwards [hT.eventually (hU.mem_nhds hxU), hT.eventually hg.2] with z hzU hgz hFz
      apply hgz
      rw [← hzero]
      intro a ha
      obtain ⟨_, b, _, heq⟩ := isInSpanAt_eq_iff.mp ((hgen (T z) hzU a).mp ha)
      have hb : a (T z) = b (T z) * f (T z) := heq.self_of_nhds
      change f (T z) = 0 at hFz
      rw [hFz, mul_zero] at hb
      exact hb
    rw [vanishingIdeal_eq_span_of_squarefree F hF hFne hsF] at hmem
    obtain ⟨A, hA⟩ := Ideal.mem_span_singleton.mp hmem
    obtain ⟨a, ha, hrep⟩ := HolGerm.exists_eq_mk A
    have heq : G =ᶠ[𝓝 (0 : ComplexModel (m + 1))] fun z => a z * F z := by
      apply HolGerm.mk_eq_mk_iff.mp (show HolGerm.mk G hG =
        HolGerm.mk (fun z => a z * F z) (eventually_differentiableAt_mul ha hF) from ?_)
      rw [HolGerm.mk_mul a F ha hF, mul_comm, ← hrep]
      exact hA
    apply (hgen x hxU g).mpr
    apply (isInSpanAt_flatInverse_iff Φ hsrc hxflat f g).mpr
    rw [h0]
    exact isInSpanAt_of_eq_mul rfl (hG.mono fun _ hz => hz.mdifferentiableAt)
      (ha.mono fun _ hz => hz.mdifferentiableAt) heq
  · exact (hoff x hxE g).mpr hg

/-- The actual controlled ideal of an invertible ideal is invertible; the
centre-power inclusion is pulled back through the actual blowup internally. -/
theorem isInvertible_controlledTransform {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) {I : GermIdeal n X} (hI : I.IsInvertible) (μ : ℕ)
    (hle : I.Le (idealPow (vanishingIdeal (n := n) C) μ)) :
    (BlowupControlledTransform.controlledTransform hπ I μ).IsInvertible := by
  exact ActualInvertibleIdealDifference.isInvertible_colon
    (GermIdealTotalTransform.isInvertible_pullback
      hπ.contMDiff (BlowupExceptionalDivisor.interior_exceptionalLocus_eq_empty hπ) hI)
    (BlowupControlledTransform.isInvertible_idealPow_exceptionalDivisor hπ μ)
    (BlowupControlledTransform.pullback_le_idealPow_exceptionalDivisor hπ hle)

/-- Off the actual centre, the whole controlled ideal is the actual reduced
inverse-image ideal, for every marking. This proves the geometric off-divisor
input required by the reducedness criterion. -/
theorem controlledTransform_vanishingIdeal_mem_iff_of_notMem {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (W : Set X) (μ : ℕ) {y : Y} (hy : π y ∉ C) (g : Y → ℂ) :
    (BlowupControlledTransform.controlledTransform hπ (vanishingIdeal (n := n) W) μ).mem y g ↔
      (vanishingIdeal (n := n) (π ⁻¹' W)).mem y g := by
  have h1C : (vanishingIdeal (n := n) C).mem (π y) (fun _ => (1 : ℂ)) := by
    refine ⟨holomorphicAt_const 1, ?_⟩
    filter_upwards [hπ.1.1.isOpen_compl.mem_nhds hy] with x hx hxC
    exact False.elim (hx hxC)
  have h1D : (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal.mem y (fun _ => (1 : ℂ)) := by
    exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul
      (s := (fun _ : X => (1 : ℂ)) ∘ π) ⟨fun _ => 1, h1C, rfl⟩
      (holomorphicAt_const 1) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp))
  have h1pow := MarkedIdeals.MarkedIdeal.one_mem_idealPow h1D μ
  have hpowhol : ∀ {q}, (idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal μ).mem y q →
      HolomorphicAt n q y := fun hq => GermIdeal.IsInvertible.holomorphicAt_mem
        (BlowupControlledTransform.isInvertible_idealPow_exceptionalDivisor hπ μ) hq
  constructor
  · intro hg
    have hmem := hg.2 (fun _ => (1 : ℂ)) h1pow
    exact (BlowupStrictIdeal.mem_pullback_vanishingIdeal_iff_of_notMem hπ W hy g).mp
      (by simpa using hmem)
  · intro hg
    refine ⟨hg.1, fun q hq => ?_⟩
    apply BlowupStrictIdeal.mem_pullback_vanishingIdeal_of_notMem hπ W hy
    refine ⟨(hpowhol hq).mul hg.1, ?_⟩
    filter_upwards [hg.2] with z hz hzW
    show q z * g z = 0
    rw [hz hzW, mul_zero]

/-- The actual off-centre whole-ideal dictionary also uses the literal
library strict transform; closedness alone supplies the local set germ. -/
theorem controlledTransform_vanishingIdeal_strict_mem_iff_of_notMem {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) {W : Set X} (hW : IsClosed W) (μ : ℕ)
    {y : Y} (hy : π y ∉ C) (g : Y → ℂ) :
    (BlowupControlledTransform.controlledTransform hπ (vanishingIdeal (n := n) W) μ).mem y g ↔
      (vanishingIdeal (n := n) (strictTransform n π W)).mem y g := by
  have heq : ∀ᶠ z in 𝓝 y, z ∈ π ⁻¹' W ↔ z ∈ strictTransform n π W := by
    filter_upwards [(hπ.1.1.preimage hπ.contMDiff.continuous).isOpen_compl.mem_nhds hy] with z hz
    exact (HironakaAdmissibleCalculus.mem_strictTransform_iff_of_notMem hπ.contMDiff.continuous hW
      (fun hexc => hz (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ hexc))).symm
  exact (controlledTransform_vanishingIdeal_mem_iff_of_notMem hπ W μ hy g).trans
    (BlowupStrictIdeal.vanishingIdeal_mem_congr heq g)

/-- With the natural maximum-order bound and actual admissibility, all
reducedness inputs are produced internally from the blowup.  The controlled
ideal equals the complete reduced ideal of the actual next strict transform. -/
theorem controlledTransform_vanishingIdeal_eq_strictTransform {m : ℕ}
    {X Y : CMfd.{u} (m + 1)} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W)
    (hI : (vanishingIdeal (n := m + 1) W).IsInvertible)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m)) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor (m + 1) E) {μ : ℕ} (hμ : 2 ≤ μ)
    (hbound : ∀ x ∈ W, GermIdealOrder.order (m + 1) univ
      (vanishingIdeal (n := m + 1) W) x ≤ (μ : ℕ∞)) {C : Set X}
    (hCadm : (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ :
      MarkedIdeals.MarkedIdeal (m + 1) X).IsAdmissibleCentre C)
    {π : Y → X} (hπ : IsBlowupAlong (m + 1) C π) :
    BlowupControlledTransform.controlledTransform hπ (vanishingIdeal (n := m + 1) W) μ =
      vanishingIdeal (n := m + 1) (strictTransform (m + 1) π W) := by
  let M : MarkedIdeals.MarkedIdeal (m + 1) X := ⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩
  have hcoh := CartanIrreducible.cartanCoherence W hWa
  have hle := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hcoh hCadm.1 hCadm.2.1
  have hwf : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, hcoh, hE,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hCS : C ⊆ W \ regularLocus (n := m + 1) W m := fun x hx =>
    HironakaHypersurfaceStageCenters.cosupport_high_mark_subset_diff_regularLocus hWa.isClosed
      (Nat.lt_succ_self m) hμ (hCadm.2.1 hx)
  have hCorder : ∀ c ∈ C, GermIdealOrder.order (m + 1) univ M.ideal c = (μ : ℕ∞) := by
    intro c hc
    apply le_antisymm (hbound c (hCS hc).1)
    exact (GermIdealOrder.le_order_iff (𝔞 := M.ideal) (fun _ hg => hg.1)).mpr (hCadm.2.1 hc).2
  have hWDense : W ⊆ closure (W \ C) := hpure.trans (closure_mono (by
    intro x hx
    exact ⟨hx.2.1, fun hxC => (hCS hxC).2 hx⟩))
  have hgeo := BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hWDense
  have hSDense : strictTransform (m + 1) π W ⊆
      closure (strictTransform (m + 1) π W \ π ⁻¹' C) := by
    rw [← hgeo]
    apply closure_mono
    intro y hy
    exact ⟨subset_closure hy, hy.2⟩
  have hEnext := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hwf hCadm hπ).isSNCDivisor
  change NormalCrossings.IsSNCDivisor (m + 1)
    (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) at hEnext
  have hDreg : ∀ y ∈ π ⁻¹' C, RegularAtDim (n := m + 1) (π ⁻¹' C) y m := by
    let i : Fin (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]).length :=
      ⟨E.length, by simp⟩
    have hi : (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]).get i = π ⁻¹' C := by
      simp [i, List.get_eq_getElem]
    intro y hy
    simpa only [hi] using SNCGlobalPrimeComponents.regularAtDim_member hEnext i
      (x := y) (by simpa only [hi] using hy)
  apply eq_vanishingIdeal_of_reduced_off_smooth_divisor _ (isInvertible_controlledTransform hπ hI μ hle)
    isClosed_closure hSDense hDreg
    (fun y hy g => controlledTransform_vanishingIdeal_strict_mem_iff_of_notMem hπ hWa.isClosed μ hy g)
  intro z hz
  have hzN : z ∈ BlowupStrictSubmanifold.geoStrictTransform π C M.N := by
    rw [MarkedIdeals.MarkedIdeal.geoStrictTransform_univ hπ]
    exact mem_univ z
  have hnot : π z ∉ GermIdealOrder.cosupport (m + 1) M.N M.ideal (M.d + 1) := by
    intro h
    have hb := (GermIdealOrder.le_order_iff (𝔞 := M.ideal) (fun _ hg => hg.1)).mpr h.2
    rw [hCorder (π z) hz] at hb
    have : μ + 1 ≤ μ := by exact_mod_cast hb
    omega
  obtain ⟨g, hg, hng⟩ := ExceptionalPushforwardAlong.exists_not_isInSpanOnAt_exceptionalDivisor
    hπ hwf.isClosedSubmanifold_N hcoh hCadm.2.1 hz hzN hnot
  refine ⟨g, ?_, fun hgE => hng ?_⟩
  · rwa [MarkedIdeals.MarkedIdeal.geoTransform_ideal_eq_controlledTransform (𝔪 := M) rfl hcoh hπ] at hg
  · exact RelativePrincipalizationSpan.IsInSpanAt.restrict
      (InvertibleIdealQuotient.isInSpanAt_self
        (NonmonomialTransformTower.exceptionalDivisor_mem_of_vanishingIdeal_mem hπ hE hCadm.2.2 hz hgE) hgE.1)

/-- Produce internally the actual maximum-order centre and the complete
next reduced invertible strict ideal, with its exact exceptional factorization. -/
theorem exists_fresh_maximal_order_blowup_strictIdeal {m : ℕ} {X : CMfd.{u} (m + 1)} {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := m + 1) W) (hK : IsCompact W)
    (hI : (vanishingIdeal (n := m + 1) W).IsInvertible)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m)) {E : List (Set X)}
    (hE : NormalCrossings.IsSNCDivisor (m + 1) E)
    (hhigh : ∃ x ∈ W, (2 : ℕ∞) ≤ GermIdealOrder.order (m + 1) univ
      (vanishingIdeal (n := m + 1) W) x) :
    ∃ (μ : ℕ) (C : Set X) (Y : CMfd.{u} (m + 1)) (π : Y → X)
      (hπ : IsBlowupAlong (m + 1) C π), 2 ≤ μ ∧ C.Nonempty ∧
      (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ :
        MarkedIdeals.MarkedIdeal (m + 1) X).IsAdmissibleCentre C ∧
      C ⊆ W \ regularLocus (n := m + 1) W m ∧
      (∀ c ∈ C, GermIdealOrder.order (m + 1) univ (vanishingIdeal (n := m + 1) W) c = (μ : ℕ∞)) ∧
      BlowupControlledTransform.controlledTransform hπ (vanishingIdeal (n := m + 1) W) μ =
        vanishingIdeal (n := m + 1) (strictTransform (m + 1) π W) ∧
      GermIdeal.pullback (m := m + 1) π (vanishingIdeal (n := m + 1) W) =
        (idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal μ).mul
          (vanishingIdeal (n := m + 1) (strictTransform (m + 1) π W)) ∧
      (vanishingIdeal (n := m + 1) (strictTransform (m + 1) π W)).IsInvertible ∧
      IsComplexAnalyticSubset (n := m + 1) (strictTransform (m + 1) π W) ∧
      IsCompact (strictTransform (m + 1) π W) ∧
      NormalCrossings.IsSNCDivisor (m + 1)
        (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) := by
  obtain ⟨μ, C, hμ, hCne, hCadm, hCS, hbound, hCorder⟩ :=
    HironakaHypersurfaceStageCenters.exists_fresh_maximal_order_centre
      hWa hK (Nat.lt_succ_self m) hpure hE hhigh
  have hCint : interior C = ∅ := eq_empty_of_subset_empty ((interior_mono
    (hCS.trans sdiff_subset)).trans
      (HironakaEmbeddedReducible.interior_eq_empty_of_pure (Nat.lt_succ_self m) hpure).subset)
  obtain ⟨Y, π, hπ⟩ := ResolutionDriver.exists_blowup C hCadm.1 hCint
  have hcoh := CartanIrreducible.cartanCoherence W hWa
  have hle := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hcoh hCadm.1 hCadm.2.1
  have hRI := controlledTransform_vanishingIdeal_eq_strictTransform hWa hI hpure hE hμ hbound hCadm hπ
  have hwf : (⟨univ, E, vanishingIdeal (n := m + 1) W, μ⟩ :
      MarkedIdeals.MarkedIdeal (m + 1) X).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, hcoh, hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  refine ⟨μ, C, Y, π, hπ, hμ, hCne, hCadm, hCS, hCorder, hRI, ?_, ?_,
    HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hWa,
    HironakaAdmissibleCalculus.isCompact_strictTransform (IsBlowupSequence.step id C π .refl hπ) hK,
    (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwf hCadm hπ).isSNCDivisor⟩
  · rw [← hRI]
    exact BlowupControlledTransform.pullback_eq_mul_controlledTransform hπ hcoh hle
  · rw [← hRI]
    exact isInvertible_controlledTransform hπ hI μ hle

end
end Hironaka.HironakaHypersurfaceStrictIdeal
