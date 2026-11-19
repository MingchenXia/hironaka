import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.SingularLocus
import Hironaka.Analytic.ClosedFormPullback
import Hironaka.Analytic.NonNefLocusKahlerIndependence
import Hironaka.Blowup.BlowupKahler
import Hironaka.Blowup.BlowupBigPullback
import Hironaka.Blowup.BlowupNonKahlerLocusEq
import Hironaka.Blowup.BlowupKahlerCurrentPullback
import Hironaka.Blowup.BlowupExceptionalCorrection
import Hironaka.Analytic.NonKahlerLocusPoleSet
import Hironaka.Analytic.BoucksomMinimalMultiplicity

set_option autoImplicit false

/-!
# Single-blowup classical inputs for the modification statements

Source: Blanchard / Voisin, *Hodge theory and complex algebraic geometry* I,
Prop. 3.24 (a blowup of a compact Kähler manifold along a closed submanifold is
compact Kähler); CT22, Lemmas 4.1--4.3 (the non-nef and non-Kähler
transformation rules and the bimeromorphic invariance of restricted volumes);
Copy-4, `sec:prelim` and `it:rv-birational`; blueprint `ana:locus-properties`.

**What this module is.**  `Hironaka.LocusProperties` states the modification part
of `ana:locus-properties` for a whole `IsBlowupSequence`.  That inductive type
is a finite composition of blowups with smooth centres, so each of those
statements is an *induction* over the sequence whose only genuine content is the
corresponding statement for ONE blowup.  This module isolates exactly those
one-blowup statements, each with its literature anchor (the open ones with an explicit `sorry`),
so that the sequence-level statements in `Hironaka.LocusProperties` are PROVED
rather than assumed.  Nothing here is weaker than what the manuscript uses, and
nothing here is a restatement of a sequence-level target.  The finite-potential
regularization used below is supplied by the already-imported Boucksom/Demailly
pole-set route rather than by a duplicate bounded-remainder interface.
-/

open Set
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace Hironaka.ModificationInputs

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus
  Hironaka.BlowupSequences Hironaka.HolomorphicMaps
  Hironaka.NumericalRestrictedVolumeScaffold

noncomputable section

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- The blowup of a compact Kähler manifold along a nowhere-dense closed complex submanifold is
again compact Kähler (Blanchard; Voisin I, Prop. 3.24).  PROVED (sorry-free) in
`Hironaka.BlowupKahler`: compactness from the universal property (`Hironaka.BlowupCompact`), and
the Kähler form `π^* ω + ε Θ` with `Θ = ddᶜ log U` for the Blanchard weight
`U = ∑_a χ_a ∑_{i ≥ k} |ζ^a_i|²` of the centre, extended across the exceptional divisor. -/
theorem compactSpace_and_kahler_of_isBlowupAlong [CompactSpace Y]
    (hKahler : Nonempty (KahlerBackground n Y)) {C : Set Y} {g : Z → Y}
    (hg : IsBlowupAlong n C g) :
    CompactSpace Z ∧ Nonempty (KahlerBackground n Z) :=
  BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong hKahler hg

/-- The pullback of a big class under one blowup with smooth centre is big.  PROVED (sorry-free)
in `Hironaka.BlowupBigPullback`: if `T = θ + ddᶜ u ≥ ω'` is a Kähler current, then
`π^* θ + ddᶜ (u ∘ π + ε log (U ∘ π)) ≥ π^* ω' + ε Θ`, where `U` is the Blanchard weight of the
centre and `Θ` its Blanchard form, and `π^* ω' + ε Θ` is Kähler for small `ε`
(`BlowupKahler.exists_isKahler_pullback_add`).  See CT22, Section 4. -/
theorem isBigClass_pullback_of_isBlowupAlong [CompactSpace Y]
    (_hKahler : Nonempty (KahlerBackground n Y))
    (θ : ClosedRealOneOneForm n Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) :
    IsBigClass (RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback hg.contMDiff θ)) :=
  BlowupBigPullback.isBigClass_pullback_of_isBlowupAlong θ hbig hg

/-- Pullback respects addition of a scalar multiple of a closed real `(1,1)`-
form, up to the geometric equality used by Bott--Chern representatives. -/
theorem pullback_add_smul_geometricallyEq {k n : ℕ} {V M : Type*}
    [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a b : ClosedRealOneOneForm n M) (c : ℝ) :
    (ClosedRealOneOneForm.pullback hf (a + c • b)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hf a + c • ClosedRealOneOneForm.pullback hf b).val := by
  intro e z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff hf _ e d hzd,
    ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff hf _ e d hzd,
    SmoothRealForm.pullback_coeff hf _ e d hzd]
  ext v
  simp

/-- The Bott--Chern class version of `pullback_add_smul_geometricallyEq`. -/
theorem ofRepresentative_pullback_add_smul {k n : ℕ} {V M : Type*}
    [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a b : ClosedRealOneOneForm n M) (c : ℝ) :
    RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hf (a + c • b)) =
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hf a) +
        c • RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hf b) := by
  rw [← RealBottChern.ofRepresentative_smul,
    ← RealBottChern.ofRepresentative_add]
  exact RealBottChern.ofRepresentative_eq_of_geometricallyEq
    (pullback_add_smul_geometricallyEq hf a b c)

/-- An arbitrary Kähler perturbation upstairs cofinally dominates the pullback
of a positive Kähler perturbation downstairs.  Concretely, `εω_Z - δπ^*ω_Y`
is Kähler for a suitable `δ > 0`. -/
theorem exists_pos_kahlerBackground_eq_smul_sub_smul_pullback [CompactSpace Z]
    (omegaY : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ K : KahlerBackground n Z,
      K.form = epsilon • omegaZ.form -
        delta • ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form := by
  obtain ⟨A, hA, hKA⟩ := KahlerDomination.exists_pos_isKahler_add_smul omegaZ
    (-ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form)
  let K₀ : KahlerBackground n Z :=
    ⟨-ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form + A • omegaZ.form, hKA⟩
  have hc : 0 < epsilon / A := div_pos hepsilon hA
  refine ⟨epsilon / A, hc, KahlerBackground.smul hc K₀, ?_⟩
  rw [KahlerBackground.smul_form]
  change (epsilon / A) •
      (-ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form + A • omegaZ.form) = _
  rw [smul_add, smul_neg, smul_smul, div_mul_cancel₀ epsilon hA.ne']
  abel

/-- The class-level form of the perturbation cofinality lemma.  It is arranged
so a Kähler current in the pulled-back `δ`-perturbed class can be enlarged,
without changing its potential, to a current in the `ε`-perturbed upstairs
class. -/
theorem exists_pos_kahlerBackground_add_smul_pullback_eq_smul [CompactSpace Z]
    (omegaY : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ K : KahlerBackground n Z,
      delta • RealBottChern.ofRepresentative
          (ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form) +
        RealBottChern.ofRepresentative K.form =
          epsilon • RealBottChern.ofRepresentative omegaZ.form := by
  obtain ⟨delta, hdelta, K, hK⟩ :=
    exists_pos_kahlerBackground_eq_smul_sub_smul_pullback omegaY omegaZ hg hepsilon
  refine ⟨delta, hdelta, K, ?_⟩
  rw [hK, sub_eq_add_neg, RealBottChern.ofRepresentative_add,
    RealBottChern.ofRepresentative_smul, ← neg_smul,
    RealBottChern.ofRepresentative_smul]
  module

/-- The `E_nn` locus upstairs is contained in the inverse image of the
downstairs `E_nn` locus, up to the exceptional locus.  The reverse inclusion is
the genuinely singular direction of the pullback theorem. -/
theorem nonNefLocus_pullback_subset_preimage_union_exceptional [CompactSpace Y]
    (omegaY : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (theta : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) :
    nonNefLocus omegaZ (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff theta)) ⊆
      g ⁻¹' nonNefLocus omegaY (RealBottChern.ofRepresentative theta) ∪
        exceptionalLocus n g := by
  have hcompact : CompactSpace Z := BlowupCompact.compactSpace_of_isBlowupAlong hg
  intro z hz
  obtain ⟨epsilon, hz_epsilon⟩ := mem_nonNefLocus.mp hz
  obtain ⟨delta, hdelta, K, hK⟩ :=
    exists_pos_kahlerBackground_add_smul_pullback_eq_smul omegaY omegaZ hg epsilon.2
  have hclass :
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff theta) +
          delta • RealBottChern.ofRepresentative
            (ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form)) +
        RealBottChern.ofRepresentative K.form =
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff theta) +
        (epsilon : ℝ) • RealBottChern.ofRepresentative omegaZ.form := by
    calc
      _ = RealBottChern.ofRepresentative
            (ClosedRealOneOneForm.pullback hg.contMDiff theta) +
          (delta • RealBottChern.ofRepresentative
              (ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form) +
            RealBottChern.ofRepresentative K.form) := by abel
      _ = _ := by rw [hK]
  have hz_pullback : z ∈ nonKahlerLocus
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff theta) +
        delta • RealBottChern.ofRepresentative
          (ClosedRealOneOneForm.pullback hg.contMDiff omegaY.form)) := by
    intro T
    exact hz_epsilon
      (NonNefLocusKahlerIndependence.KahlerCurrent.ofEq hclass
        (NonNefLocusKahlerIndependence.KahlerCurrent.addKahler T K))
  have hpullclass :=
    ofRepresentative_pullback_add_smul hg.contMDiff theta omegaY.form delta
  have hz_pullback' : z ∈ nonKahlerLocus
      (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff (theta + delta • omegaY.form))) := by
    rw [hpullclass]
    exact hz_pullback
  rcases BlowupNonKahlerLocus.nonKahlerLocus_pullback_subset
      (theta + delta • omegaY.form) hg hz_pullback' with hpreimage | hexc
  · left
    refine mem_nonNefLocus.mpr ⟨⟨delta, hdelta⟩, ?_⟩
    change g z ∈ nonKahlerLocus
      (RealBottChern.ofRepresentative (theta + delta • omegaY.form)) at hpreimage
    simpa only [RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_smul] using hpreimage
  · exact Or.inr hexc

/-- A point in the inverse image of the downstairs non-nef locus remains in
the non-Kähler locus of the *unperturbed* pullback class.  Equivalently, every
Kähler current in the unperturbed pullback class has positive Lelong number at
such a point.  This is the fixed-parameter transport available before one
controls the positive upstairs perturbation. -/
theorem preimage_nonNefLocus_subset_nonKahlerLocus_pullback [CompactSpace Y]
    (hKahler : Nonempty (KahlerBackground n Y))
    (omega : KahlerBackground n Y) (theta : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) :
    g ⁻¹' nonNefLocus omega (RealBottChern.ofRepresentative theta) ⊆
      nonKahlerLocus (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff theta)) := by
  intro z hz
  have hz_nonKahler : g z ∈ nonKahlerLocus (RealBottChern.ofRepresentative theta) := by
    obtain ⟨epsilon, hEpsilon⟩ := mem_nonNefLocus.mp hz
    intro T
    exact hEpsilon (T.addSmulKahler omega epsilon.2)
  rw [BlowupNonKahlerLocusEq.nonKahlerLocus_pullback_eq hKahler theta hg]
  exact Or.inl hz_nonKahler

/-- **`E_nn(π^* α) ⊆ π⁻¹ E_nn(α)`**, with no exceptional exception (CT22, Lemma 4.2, the
inclusion that does not need minimal multiplicities).  The improvement over
`nonNefLocus_pullback_subset_preimage_union_exceptional` is bought by Demailly regularization
alone: contrapositively, a Kähler current `T` downstairs in
`α + δ{ω_Y}` with `ν(T, π z) = 0` is first replaced, by Boucksom's pole-set theorem
(`Hironaka.NonKahlerLocusPoleSet`), by a Kähler current `S` in the same class
whose polar set is exactly `E_nK(α + δ{ω_Y})`, so `S` has a finite potential at `π z`; then
`π^* S + K` is a
Kähler current of `Hironaka.BlowupKahlerCurrentPullback.pullbackAddKahler` in `π^* α + ε{ω_Z}`
whose potential is literally `u_S ∘ π`, finite at `z`, hence of zero Lelong number there — at
exceptional points too.  The Kähler perturbation `K = εω_Z - δπ^*ω_Y` upstairs supplies the
strict positivity that `BlowupBigPullback.pullbackCurrent` has to buy with `ε log (U ∘ π)`, and
it is that logarithmic term — absent here — which creates a pole along the exceptional locus. -/
theorem nonNefLocus_pullback_subset_preimage [CompactSpace Y]
    (omegaY : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (theta : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) :
    nonNefLocus omegaZ (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff theta)) ⊆
      g ⁻¹' nonNefLocus omegaY (RealBottChern.ofRepresentative theta) := by
  have hcompact : CompactSpace Z := BlowupCompact.compactSpace_of_isBlowupAlong hg
  intro z hz
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact mem_nonNefLocus.mpr ⟨⟨1, one_pos⟩,
      fun T => BlowupNonKahlerLocus.lelongNumber_pos_of_dim_eq_zero hn _ _⟩
  by_contra hcon
  obtain ⟨epsilon, hz_epsilon⟩ := mem_nonNefLocus.mp hz
  obtain ⟨delta, hdelta, K, hK⟩ :=
    exists_pos_kahlerBackground_add_smul_pullback_eq_smul omegaY omegaZ hg epsilon.2
  have hnot : g z ∉ nonKahlerLocus (RealBottChern.ofRepresentative theta +
      delta • RealBottChern.ofRepresentative omegaY.form) := fun h =>
    hcon (mem_nonNefLocus.mpr ⟨⟨delta, hdelta⟩, h⟩)
  -- the perturbed class is big: a point off its non-Kähler locus witnesses a Kähler current
  have hbigbeta : IsBigClass (RealBottChern.ofRepresentative theta +
      delta • RealBottChern.ofRepresentative omegaY.form) := by
    by_contra hb
    exact hnot fun T => absurd ⟨T⟩ hb
  -- regularize: a Kähler current in the same class whose polar set is exactly `E_nK`
  obtain ⟨R, -, -, hRpole⟩ :=
    NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hn _ hbigbeta
  have hRfin : R.potential (g z) ≠ ⊥ := fun hbot =>
    hnot (hRpole ▸ (show g z ∈ Hironaka.NumericalRestrictedVolumeScaffold.poleSet R.potential
      from hbot))
  have hcls : RealBottChern.ofRepresentative theta +
      delta • RealBottChern.ofRepresentative omegaY.form =
      RealBottChern.ofRepresentative (theta + delta • omegaY.form) := by
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
  set T' := NonNefLocusKahlerIndependence.KahlerCurrent.ofEq hcls R with hT'
  set S := BlowupKahlerCurrentPullback.pullbackAddKahler T' hg K with hS
  have hcls2 : RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff (theta + delta • omegaY.form)) +
      RealBottChern.ofRepresentative K.form =
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff theta) +
        (epsilon : ℝ) • RealBottChern.ofRepresentative omegaZ.form := by
    rw [ofRepresentative_pullback_add_smul hg.contMDiff theta omegaY.form delta, add_assoc, hK]
  have hpos := hz_epsilon (NonNefLocusKahlerIndependence.KahlerCurrent.ofEq hcls2 S)
  have hzero : lelongNumber (n := n) S.potential z = 0 :=
    BlowupKahlerCurrentPullback.lelongNumber_pullbackAddKahler_eq_zero hn T' hg K hRfin
  rw [show (NonNefLocusKahlerIndependence.KahlerCurrent.ofEq hcls2 S).potential = S.potential from
    rfl, hzero] at hpos
  exact absurd hpos (lt_irrefl 0)

set_option maxHeartbeats 800000 in
/-- **`π⁻¹ E_nn(α) ⊆ E_nn(π^* α)`** (CT22, Lemma 4.2, the inclusion that needs minimal
multiplicities).  The Kähler background upstairs may be taken to be the Blanchard form
`π^* ω_Y + ε Θ` (`nonNefLocus_kahler_independent`).  Then a Kähler current `S` of
`π^* α + t{ω_Z}` is corrected by `tε log (U ∘ π)` into a Kähler current of the pullback class
`π^* (α + t{ω_Y})` (`Hironaka.BlowupExceptionalCorrection`), which pushes down
(`Hironaka.BlowupPushforward`) to a Kähler current of `α + t{ω_Y}` downstairs.  Boucksom's
minimal multiplicity at `π z` bounds the Lelong number of that current from below by a `c₀`
**independent of it**, while the correction cost is at most `tε · ν(log (U ∘ π), z)`, a fixed
finite number times `t`.  Choosing `t` small makes the cost smaller than `c₀`. -/
theorem preimage_nonNefLocus_subset_nonNefLocus_pullback [CompactSpace Y]
    (omegaY : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (theta : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) :
    g ⁻¹' nonNefLocus omegaY (RealBottChern.ofRepresentative theta) ⊆
      nonNefLocus omegaZ (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff theta)) := by
  have hcompact : CompactSpace Z := BlowupCompact.compactSpace_of_isBlowupAlong hg
  intro z hz
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact mem_nonNefLocus.mpr ⟨⟨1, one_pos⟩,
      fun T => BlowupNonKahlerLocus.lelongNumber_pos_of_dim_eq_zero hn _ _⟩
  obtain ⟨D, -, hflatC⟩ := BlowupExceptionalCentre.exists_blanchardData_exceptionalCentre hg
  have hC₂C := BlowupExceptionalCentre.exceptionalCentre_subset hg
  have hexcl : ∀ z', g z' ∉ BlowupExceptionalCentre.exceptionalCentre n g →
      z' ∉ exceptionalLocus n g := fun z' h hE => h ⟨z', hE, rfl⟩
  obtain ⟨F, epsB, hepsB, hK⟩ := BlowupKahler.exists_isKahler_pullback_add_of_flat omegaY hg D
    hflatC (BlowupExceptionalCentre.isClosed_exceptionalCentre hg) hC₂C hexcl
  set omegaB : KahlerBackground n Z := ⟨_, hK⟩ with homegaB
  obtain ⟨c₀, hc₀, t₀, ht₀, hbound⟩ :=
    BoucksomMinimalMultiplicity.exists_uniform_lelongNumber_lowerBound_of_mem_nonNefLocus
      omegaY (RealBottChern.ofRepresentative theta) hz
  -- the exceptional loss factor: a finite number depending only on `z`
  have hqp : ManifoldQuasiPlurisubharmonic (n := n)
      (FactorizedWeightPsh.logWeight (fun z' => D.weight (g z'))) := by
    have h := (FactorizedWeightPsh.thetaPlurisubharmonic_logWeight F one_pos).quasiPlurisubharmonic
    simpa using h
  -- `log (U ∘ π)` is finite off `π⁻¹ C`, which is dense because `π⁻¹ C` has empty interior
  have hnd : LocallyNondegenerate
      (FactorizedWeightPsh.logWeight (fun z' => D.weight (g z'))) := by
    intro x U hU hxU
    have hnotsub : ¬ U ⊆ g ⁻¹' C := fun hsub => by
      have hx := interior_maximal hsub hU hxU
      rw [ExceptionalFibres.interior_preimage_eq_empty hg] at hx
      exact hx
    obtain ⟨z₀, hz₀U, hz₀C⟩ := not_subset.mp hnotsub
    exact ⟨z₀, hz₀U, FactorizedWeightPsh.logWeight_ne_bot_of_pos
      (D.weight_pos_of_notMem fun h2 => hz₀C (hC₂C h2))⟩
  have hnu0top : lelongNumber (n := n)
      (FactorizedWeightPsh.logWeight (fun z' => D.weight (g z'))) z ≠ ⊤ :=
    LelongNumberAdditivity.lelongNumber_ne_top hn hqp hnd z
  -- a positive real below `c₀`
  obtain ⟨q, hq0, hqc⟩ : ∃ q : ℝ, 0 < q ∧ ENNReal.ofReal q ≤ c₀ := by
    rcases eq_or_lt_of_le (le_top : c₀ ≤ (⊤ : ℝ≥0∞)) with h | h
    · exact ⟨1, one_pos, by rw [h]; exact le_top⟩
    · exact ⟨c₀.toReal, ENNReal.toReal_pos hc₀.ne' h.ne, by rw [ENNReal.ofReal_toReal h.ne]⟩
  set r : ℝ := (lelongNumber (n := n)
    (FactorizedWeightPsh.logWeight (fun z' => D.weight (g z'))) z).toReal with hrdef
  have hrnn : 0 ≤ r := ENNReal.toReal_nonneg
  set t : ℝ := min t₀ (q / (2 * epsB * (r + 1))) with htdef
  have htpos : 0 < t := lt_min ht₀ (by positivity)
  have htle : t ≤ t₀ := min_le_left _ _
  have hloss : ENNReal.ofReal (t * epsB) * lelongNumber (n := n)
      (FactorizedWeightPsh.logWeight (fun z' => D.weight (g z'))) z < c₀ := by
    have hnu0eq : lelongNumber (n := n)
        (FactorizedWeightPsh.logWeight (fun z' => D.weight (g z'))) z = ENNReal.ofReal r :=
      (ENNReal.ofReal_toReal hnu0top).symm
    rw [hnu0eq, ← ENNReal.ofReal_mul (by positivity)]
    refine lt_of_lt_of_le ?_ hqc
    refine (ENNReal.ofReal_lt_ofReal_iff hq0).mpr ?_
    have h1 : t ≤ q / (2 * epsB * (r + 1)) := min_le_right _ _
    have h3 : t * (2 * epsB * (r + 1)) ≤ q := by
      rw [← le_div_iff₀ (by positivity)]; exact h1
    nlinarith [mul_pos htpos hepsB, hrnn, hq0]
  -- move to the Blanchard background and give the witness
  rw [NonNefLocusKahlerIndependence.nonNefLocus_kahler_independent omegaZ omegaB]
  refine mem_nonNefLocus.mpr ⟨⟨t, htpos⟩, fun S => ?_⟩
  obtain ⟨S', hS'⟩ := BlowupExceptionalCorrection.exists_blanchardCorrection
    (θ := theta) (omegaY := omegaY) (omegaZ := omegaB) (D := D) hg F hepsB rfl htpos S
  set T' := NonNefLocusKahlerIndependence.KahlerCurrent.ofEq
    (ofRepresentative_pullback_add_smul hg.contMDiff theta omegaY.form t).symm S' with hT'
  obtain ⟨delta, hdelta, psi, hpsi, hZf, hhZ, hid⟩ :=
    BlowupPushforward.exists_pushforward omegaY (theta + t • omegaY.form) hg D F hepsB hK T'
  -- the pushed-down Kähler current downstairs
  have hclsY : RealBottChern.ofRepresentative (theta + t • omegaY.form) =
      RealBottChern.ofRepresentative theta + t • RealBottChern.ofRepresentative omegaY.form := by
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
  have hc₀le : c₀ ≤ lelongNumber (n := n) psi (g z) :=
    hbound t htpos htle
      { representative := theta + t • omegaY.form
        represents := hclsY
        potential := psi
        lowerBound := KahlerBackground.smul hdelta omegaY
        strictlyPsh := by rw [KahlerBackground.smul_form]; exact hpsi }
  -- transport the lower bound upstairs
  have h1 : lelongNumber (n := n) psi (g z) ≤ lelongNumber (n := n) (fun z' => psi (g z')) z :=
    LelongNumberComparison.lelongNumber_le_comp
      ((hg.contMDiff z).mdifferentiableAt (by simp))
      (fun hposl => eq_bot_of_lelongNumber_pos hn hpsi.1 hposl)
  have hv : ManifoldQuasiPlurisubharmonic (n := n)
      (fun z' => ((delta * epsB : ℝ) : EReal) *
        FactorizedWeightPsh.logWeight (fun z'' => D.weight (g z'')) z') :=
    (FactorizedWeightPsh.thetaPlurisubharmonic_logWeight F
      (mul_pos hdelta hepsB)).quasiPlurisubharmonic
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, ((delta * epsB : ℝ) : EReal) *
      FactorizedWeightPsh.logWeight (fun z'' => D.weight (g z'')) z < (Mb : EReal) := by
    induction hval : ((delta * epsB : ℝ) : EReal) *
        FactorizedWeightPsh.logWeight (fun z'' => D.weight (g z'')) z using EReal.rec with
    | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
    | top => exact absurd hval (hv.ne_top z)
    | coe a => exact ⟨a + 1, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
  have hvbound : ∀ᶠ z' in 𝓝[≠] z, ((delta * epsB : ℝ) : EReal) *
      FactorizedWeightPsh.logWeight (fun z'' => D.weight (g z'')) z' ≤ (Mb : EReal) :=
    eventually_nhdsWithin_of_eventually_nhds
      ((hv.upperSemicontinuous z Mb hMb).mono fun _ h => h.le)
  have h2 : lelongNumber (n := n) (fun z' => psi (g z')) z ≤
      lelongNumber (n := n) (fun z' => psi (g z') + ((delta * epsB : ℝ) : EReal) *
        FactorizedWeightPsh.logWeight (fun z'' => D.weight (g z'')) z') z :=
    LelongNumberScaling.lelongNumber_le_add_of_eventually_le_const hvbound
  have h3 : lelongNumber (n := n) (fun z' => psi (g z') + ((delta * epsB : ℝ) : EReal) *
        FactorizedWeightPsh.logWeight (fun z'' => D.weight (g z'')) z') z =
      lelongNumber (n := n) (fun z' => T'.potential z' - (hZf z' : EReal)) z :=
    LelongNumberComparison.lelongNumber_congr (Filter.Eventually.of_forall fun z' => (hid z').symm)
  have h4 : lelongNumber (n := n) (fun z' => T'.potential z' - (hZf z' : EReal)) z ≤
      lelongNumber (n := n) T'.potential z :=
    KahlerCurrentMax.lelongNumber_sub_le
      (KahlerCurrentMax.continuous_of_chartSmooth hhZ).continuousAt
  have hchain : c₀ ≤ lelongNumber (n := n) S.potential z +
      ENNReal.ofReal (t * epsB) * lelongNumber (n := n)
        (FactorizedWeightPsh.logWeight (fun z' => D.weight (g z'))) z :=
    hc₀le.trans (h1.trans ((h2.trans (le_of_eq h3)).trans (h4.trans (hS' z))))
  by_contra hcon
  rw [nonpos_iff_eq_zero.mp (not_lt.mp hcon), zero_add] at hchain
  exact absurd hchain (not_le.mpr hloss)

-- `hbig` is part of the fixed statement of this target and is not renamed; the proof does not
-- use it, because both inclusions hold for an arbitrary class.
set_option linter.unusedVariables false in
/-- **`E_nn(π^* α) = π⁻¹ E_nn(α)`** (CT22, Lemma 4.2).  Unlike the non-Kähler locus, the
exceptional divisor does NOT appear: the non-nef locus is an `ε`-limit of non-Kähler loci and
the exceptional contribution disappears in the limit.  PROVED from
`nonNefLocus_pullback_subset_preimage` (Favre--Kiselman) and
`preimage_nonNefLocus_subset_nonNefLocus_pullback` (Boucksom's minimal multiplicities and the
Lelong-number arithmetic of `Hironaka.LelongNumberAdditivity`). -/
theorem nonNefLocus_pullback_of_isBlowupAlong [CompactSpace Y]
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z)
    (θ : ClosedRealOneOneForm n Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) :
    nonNefLocus omegaZ (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ)) =
      g ⁻¹' nonNefLocus omega (RealBottChern.ofRepresentative θ) :=
  Subset.antisymm (nonNefLocus_pullback_subset_preimage omega omegaZ θ hg)
    (preimage_nonNefLocus_subset_nonNefLocus_pullback omega omegaZ θ hg)

/-- On a compact complex manifold the non-nef locus does not depend on the
chosen Kähler background.  PROVED (sorry-free) in
`Hironaka.NonNefLocusKahlerIndependence`: for `ε > 0` pick `δ > 0` with
`εω - δω'` Kähler (compactness); adding it to a Kähler current in `α + δ{ω'}`
gives one in `α + ε{ω}` with the same potential. -/
theorem nonNefLocus_kahler_independent [CompactSpace Y]
    (omega omega' : KahlerBackground n Y) (alpha : RealBottChern n Y) :
    nonNefLocus omega alpha = nonNefLocus omega' alpha :=
  NonNefLocusKahlerIndependence.nonNefLocus_kahler_independent omega omega' alpha

/-- The non-Kähler locus of the pullback of a big class under one blowup is the preimage of the
non-Kähler locus together with the exceptional locus (CT22, Lemma 4.1).  PROVED (sorry-free) in
`Hironaka.BlowupNonKahlerLocusEq`: `⊆` pulls back a Kähler current with zero Lelong number
(`BlowupNonKahlerLocus`); `⊇` pushes every Kähler current on the blowup down across the
codimension-`≥ 2` exceptional centre (`BlowupPushforward`, Grauert–Remmert extension). -/
theorem nonKahlerLocus_pullback_of_isBlowupAlong [CompactSpace Y]
    (hKahler : Nonempty (KahlerBackground n Y))
    (θ : ClosedRealOneOneForm n Y)
    (_hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) :
    nonKahlerLocus (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ)) =
      g ⁻¹' nonKahlerLocus (RealBottChern.ofRepresentative θ) ∪
        exceptionalLocus n g :=
  BlowupNonKahlerLocusEq.nonKahlerLocus_pullback_eq hKahler θ hg

end

end Hironaka.ModificationInputs
