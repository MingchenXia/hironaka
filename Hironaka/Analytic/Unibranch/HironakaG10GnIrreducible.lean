import Hironaka.Analytic.Unibranch.HironakaG10GnChartFlat
import Hironaka.Analytic.Unibranch.HironakaG10GnBaseFree
import Hironaka.Analytic.Unibranch.HironakaG10GnLocalNearby
import Hironaka.Analytic.Unibranch.HironakaG10RmRelStart
import Hironaka.Analytic.Unibranch.HironakaG10TmLocalFlatness

/-!
# Generic chart flatness over an irreducible analytic base (route N, items N4–N5)

Lane G10GN, run 0081 (`work/hironaka-run0081-20261117/G10GN/hGF-route.md`). Main result:
**`exists_flat_irreducible`**: let `Q ⊆ ℂᵐ` be analytic near `p₀` with irreducible germ (prime vanishing ideal) and
`A` a holomorphic matrix near `(p₀, y₀)`. There is `g`, holomorphic at `p₀` and not vanishing identically on `Q` near
`p₀`, such that for `p ∈ Q` near `p₀` with `g p ≠ 0` the cokernel of `A` is flat over `Q` at `(p, y₀)`
(`ChartFlat m t A (p, y₀) (baseIdeal Q p)`) — Frisch, Invent. Math. 4 (1967), Th. (II,1) (i)+(ii), with ONE
exceptional hypersurface for all degrees.

Proof: Cartan generators of `I_Q` (`CartanIrreducible`); for each row `i` a relative exact start of the rows `> i`
over `Q` (`HironakaG10RmRelStart.exists_relExactStartOn`), which presents the `i`-th cyclic piece of
`coker A ⊗ 𝒪_Q` (`HironakaG10GnChartFlat.cyclicGen_of_start`); **`exists_rowFlat`**: the cyclic piece, an ideal
coherent near `(p₀, y₀)`, has ONE presentation of all its nearby normal cones (`HironakaG10GnLocalNearby`), a
coefficient domain over `𝒪_{Q,p₀}` with one uniform denominator (`HironakaG10GnBaseFree`), hence free normal
cones and flat cyclic quotients off a hypersurface (`HironakaG10GnGradedFree`, `HironakaG10GnChartFlat`); the
product of the row denominators is the exceptional function (prime germ ideal).

Dictionaries: `inSpanAt_iff_germAt_mem_span`, `baseIdeal_eq_span_of_generators`, `splitModel_tangentInclusion`,
`ambientGermEquiv_mk_translate`, `germAt_finset_prod`.

No named input. BP: hironaka-g10gn-hgf.tex.
-/

set_option autoImplicit false

open Set Filter Function
open scoped Topology Manifold

namespace Hironaka.Analytic.Unibranch.HironakaG10GnIrreducible

noncomputable section

open Hironaka Hironaka
open HolGerm OkaRelationSheaf OkaIdealOperations OkaGermBridge HironakaRelativeNormalIdeal
  HironakaRelativeNormalCoherentTranslatedJets Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
  Hironaka.Analytic.Unibranch.HironakaG10GfModStart AnalyticGermDecomposition HironakaG10LocRelative HironakaG10LocFibreOpen

section Span

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

/-- **Finitely generated ideals at a point, as germs.** -/
theorem inSpanAt_iff_germAt_mem_span {μ : Type*} [Fintype μ] (s : μ → Z → ℂ) (y : Z)
    (hs : ∀ k, HolAt (s k) y) (g : Z → ℂ) (hg : HolAt g y) :
    InSpanAt s y g ↔ germAt y g ∈ Ideal.span (range fun k => germAt y (s k)) := by
  classical
  constructor
  · rintro ⟨-, c, hc, he⟩
    have hsum : HolAt (fun x => ∑ k, c k x * s k x) y := HolAt.fintype_sum fun k => (hc k).mul (hs k)
    rw [(germAt_eq_germAt_iff hg hsum).mpr he, germAt_sum Finset.univ fun k _ => (hc k).mul (hs k)]
    exact Ideal.sum_mem _ fun k _ => by
      rw [germAt_mul (hc k) (hs k)]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
  · intro h
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h
    choose c' hc' hc'e using fun k => exists_germAt_eq (c k) y
    refine ⟨hg, c', hc', ?_⟩
    have hsum : HolAt (fun x => ∑ k, c' k x * s k x) y := HolAt.fintype_sum fun k => (hc' k).mul (hs k)
    apply (germAt_eq_germAt_iff hg hsum).mp
    rw [← hc, germAt_sum Finset.univ fun k _ => (hc' k).mul (hs k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [germAt_mul (hc' k) (hs k), hc'e k, smul_eq_mul]

end Span

section Base

variable {d : ℕ}

/-- Germ membership in `baseIdeal P p` is vanishing on `P` near `p`. -/
theorem germAt_mem_baseIdeal_iff (P : Set (ComplexModel d)) (p : ComplexModel d) {f : ComplexModel d → ℂ}
    (hf : HolAt f p) : germAt p f ∈ baseIdeal P p ↔ ∀ᶠ x in 𝓝 p, x ∈ P → f x = 0 := by
  rw [germAt_of_holAt hf, baseIdeal, mem_vanishingIdeal_mk]
  exact (eventually_nhds_iff_translate (p := fun x => x ∈ P → f x = 0) p).symm

/-- **Cartan generators generate every `baseIdeal`.** -/
theorem baseIdeal_eq_span_of_generators (P : Set (ComplexModel d)) {U : Set (ComplexModel d)}
    (hU : IsOpen U) {μ : Type*} [Fintype μ] (r : μ → ComplexModel d → ℂ)
    (hr : ∀ k, DifferentiableOn ℂ (r k) U)
    (hgen : ∀ p ∈ U, ∀ f, vanishingIdealF P p f ↔ InSpanAt r p f) {p : ComplexModel d} (hp : p ∈ U) :
    baseIdeal P p = Ideal.span (range fun k => germAt p (r k)) := by
  have hrp : ∀ k, HolAt (r k) p := fun k => holAt_of_differentiableOn hU (hr k) hp
  ext g
  obtain ⟨f, hf, rfl⟩ := exists_germAt_eq g p
  rw [germAt_mem_baseIdeal_iff P p hf, ← inSpanAt_iff_germAt_mem_span r p hrp f hf, ← hgen p hp f]
  exact ⟨fun h => ⟨hf, h⟩, fun h => h.2⟩

end Base

section Split

variable (d t : ℕ)

theorem splitModel_tangentInclusion (a : ComplexModel d) :
    splitModel d t (tangentInclusion d t a) = (a, 0) := by
  apply Prod.ext
  · rw [splitModel_fst, tangentProjection_tangentInclusion]
  · ext i
    simp [splitModel, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      LinearIsometryEquiv.piLpCongrLeft_apply, tangentInclusion_normal]

/-- The affine chart `w ↦ (p₀, y₀) + split w`. -/
def chartMap (q₀ : ComplexModel d × ComplexModel t) (w : ComplexModel (d+t)) : ComplexModel d × ComplexModel t :=
  q₀ + splitModel d t w

theorem chartMap_translate (q₀ : ComplexModel d × ComplexModel t) (a : ComplexModel d) (w : ComplexModel (d+t)) :
    chartMap d t q₀ (actualAffineTranslation (d+t) (tangentInclusion d t a) w) =
      (q₀ + (a, 0)) + splitModel d t w := by
  simp only [chartMap, actualAffineTranslation, map_add, splitModel_tangentInclusion, add_assoc]

/-- **Library germs of chart functions are chart germs.** -/
theorem ambientGermEquiv_mk_translate (q₀ : ComplexModel d × ComplexModel t) (a : ComplexModel d)
    (S : ComplexModel d × ComplexModel t → ℂ) (hS : HolAt S (q₀ + (a, 0)))
    (h : HolAt (S ∘ chartMap d t q₀ ∘ actualAffineTranslation (d+t) (tangentInclusion d t a)) 0) :
    ambientGermEquiv d t (HolGerm.mk (S ∘ chartMap d t q₀ ∘ actualAffineTranslation (d+t)
      (tangentInclusion d t a)) h) = germAt (q₀ + (a, 0)) S := by
  rw [germAt_of_holAt hS]
  change HolGerm.comapEquiv (splitModel d t).symm (HolGerm.mk _ h) = _
  rw [HolGerm.comapEquiv_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards with v
  simp only [Function.comp_apply, chartMap_translate, ContinuousLinearEquiv.apply_symm_apply]

end Split

section RowFlat

open Hironaka.Analytic.Unibranch.HironakaG10GnChartFlat Hironaka.Analytic.Unibranch.HironakaG10GnGradedFree
  Hironaka.Analytic.Unibranch.HironakaG10GnBaseFree Hironaka.Analytic.Unibranch.HironakaG10GnLocalNearby
  HironakaRelativeNormalCoefficientFunctionAlgebra HironakaSmoothCentreCoherentDomain
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalDeformationInitialRelations

attribute [local instance] coefficientSubalgebraRing

local instance chartAlg' (d t : ℕ) :
    Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

variable {m t : ℕ}

theorem baseIdeal_translate (Q : Set (ComplexModel m)) (p₀ a : ComplexModel m) :
    baseIdeal {w | p₀ + w ∈ Q} a = baseIdeal Q (p₀ + a) := by
  simp only [baseIdeal, mem_ofPred_eq, add_assoc]

/-- **One row: flatness of the cyclic chart quotient off a hypersurface of an irreducible base.** -/
theorem exists_rowFlat (p₀ : ComplexModel m) (y₀ : ComplexModel t) (Q : Set (ComplexModel m))
    (hprime : (baseIdeal Q p₀).IsPrime)
    {Uc : Set (ComplexModel m)} (hUc : IsOpen Uc) (hp₀Uc : p₀ ∈ Uc) {nμ : ℕ}
    (rr : Fin nμ → ComplexModel m → ℂ) (hrr : ∀ l, DifferentiableOn ℂ (rr l) Uc)
    (hgen : ∀ p ∈ Uc, baseIdeal Q p = Ideal.span (range fun l => germAt p (rr l)))
    {c : ℕ} (f : Fin c → ComplexModel m × ComplexModel t → ℂ) {O : Set (ComplexModel m × ComplexModel t)}
    (hO : IsOpen O) (hq₀O : (p₀, y₀) ∈ O) (hf : ∀ k, DifferentiableOn ℂ (f k) O) :
    ∃ g : ComplexModel m → ℂ, HolAt g p₀ ∧ (¬ ∀ᶠ p in 𝓝 p₀, p ∈ Q → g p = 0) ∧
      ∀ᶠ p in 𝓝 p₀, p ∈ Q → g p ≠ 0 →
        CyclicFlat m t (baseIdeal Q p) (fun k => germAt (p, y₀) (f k)) := by
  classical
  -- the generators on the chart side
  let S : Fin c ⊕ Fin nμ → ComplexModel m × ComplexModel t → ℂ := Sum.elim f (fun l z => rr l z.1)
  let O' := O ∩ (Uc ×ˢ (univ : Set (ComplexModel t)))
  have hO' : IsOpen O' := hO.inter (hUc.prod isOpen_univ)
  have hq₀O' : (p₀, y₀) ∈ O' := ⟨hq₀O, hp₀Uc, mem_univ _⟩
  have hS : ∀ n, DifferentiableOn ℂ (S n) O' := by
    rintro (k | l)
    · exact (hf k).mono inter_subset_left
    · intro z hz
      exact (((hrr l).differentiableAt (hUc.mem_nhds hz.2.1)).comp z differentiableAt_fst).differentiableWithinAt
  let φ := chartMap m t (p₀, y₀)
  have hφc : Continuous φ := continuous_const.add (splitModel m t).continuous
  have hφd : ∀ w, DifferentiableAt ℂ φ w := fun w =>
    (differentiableAt_const _).add (splitModel m t).differentiableAt
  let T := φ ⁻¹' O'
  have hT : IsOpen T := hO'.preimage hφc
  have h0T : (0 : ComplexModel (m+t)) ∈ T := by
    change φ 0 ∈ O'
    simpa [φ, chartMap] using hq₀O'
  let S' : Fin (c + nμ) → ComplexModel (m+t) → ℂ := fun n => S (finSumFinEquiv.symm n) ∘ φ
  have hS'd : ∀ n, DifferentiableOn ℂ (S' n) T := fun n w hw =>
    (((hS _).differentiableAt (hO'.mem_nhds hw)).comp w (hφd w)).differentiableWithinAt
  have hS' : ∀ n, MDifferentiableOn 𝓘(ℂ, ComplexModel (m+t)) 𝓘(ℂ, ℂ) (S' n) T := fun n =>
    mdifferentiableOn_iff_differentiableOn.mpr (hS'd n)
  let F : HolomorphicIdealSheaves.GermIdeal (m+t) (ComplexModel (m+t)) := ⟨fun z g => HolomorphicIdealSheaves.IsInSpanAt (n := m+t) (· ∈ range S') z g⟩
  have hF : CoherentOn F T := fun y hy => ⟨T, hT, hy, subset_rfl, c + nμ, S', hS', fun z _ g => Iff.rfl⟩
  obtain ⟨B₁, hB₁, h0B₁, hpoint, C0, hC0, Q₁, -, -, hnearby⟩ :=
    exists_local_finiteType_coefficient_initial_family m t F T hT h0T hF
  -- the base, translated to the origin
  let Qt : Set (ComplexModel m) := {w | p₀ + w ∈ Q}
  have hprime' : (baseIdeal Qt 0).IsPrime := by
    rw [baseIdeal_translate, add_zero]
    exact hprime
  obtain ⟨g, hgB, hgnot, V, hV, h0V, hVB, hfree⟩ := exists_uniform_free_over_base hB₁ h0B₁ C0 hC0 Q₁ Qt hprime'
  have hg0 : HolAt g 0 := hgB 0 h0B₁
  refine ⟨fun p => g (p - p₀), ?_, ?_, ?_⟩
  · have h := HolAt.comp (f := g) (φ := fun p : ComplexModel m => p - p₀) (y := p₀) (by simpa using hg0)
      (continuous_id.sub continuous_const) (fun _ => differentiableAt_id.sub (differentiableAt_const _))
    exact h
  · intro h
    apply hgnot
    have ht : Tendsto (fun w : ComplexModel m => p₀ + w) (𝓝 0) (𝓝 p₀) :=
      (continuous_const.add continuous_id).tendsto' 0 p₀ (by simp)
    filter_upwards [ht.eventually h] with w hw hwQ
    simpa using hw hwQ
  · have ht : Tendsto (fun p : ComplexModel m => p - p₀) (𝓝 p₀) (𝓝 0) :=
      (continuous_id.sub continuous_const).tendsto' p₀ 0 (by simp)
    filter_upwards [ht.eventually (hV.mem_nhds h0V), hUc.mem_nhds hp₀Uc] with p hpV hpUc hpQ hgp
    set a := p - p₀ with ha
    have hpa : p₀ + a = p := by rw [ha]; abel
    have hK_eq : baseIdeal Qt a = baseIdeal Q p := by rw [baseIdeal_translate, hpa]
    rw [← hK_eq]
    have haB : a ∈ B₁ := hVB hpV
    have hTa : tangentInclusion m t a ∈ T := (hpoint a haB).1
    have hφa : φ (tangentInclusion m t a) = (p, y₀) := by
      change (p₀, y₀) + splitModel m t (tangentInclusion m t a) = (p, y₀)
      rw [splitModel_tangentInclusion]
      ext <;> simp [hpa]
    have hpO' : (p, y₀) ∈ O' := hφa ▸ hTa
    have hSp : ∀ n, HolAt (S n) (p, y₀) := fun n => holAt_of_differentiableOn hO' (hS n) hpO'
    -- the library ideal at `(a, 0)`
    have hhol : ∀ n, HolAt (S' n ∘ actualAffineTranslation (m+t) (tangentInclusion m t a)) 0 :=
      fun n => translated_function_holAt hT (hS' n) hTa
    set L := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion m t a)) with hLdef
    have hLspan : L = Ideal.span (range fun n =>
        HolGerm.mk (S' n ∘ actualAffineTranslation (m+t) (tangentInclusion m t a)) (hhol n)) :=
      translated_origin_ideal_eq_span_of_real_generators F S' hT hS' (fun z _ g => Iff.rfl) hTa hhol
    have hq : ((p₀, y₀) : ComplexModel m × ComplexModel t) + (a, 0) = (p, y₀) := by
      ext <;> simp [hpa]
    have hgerm : ∀ n, ambientGermEquiv m t
        (HolGerm.mk (S' n ∘ actualAffineTranslation (m+t) (tangentInclusion m t a)) (hhol n)) =
          germAt (p, y₀) (S (finSumFinEquiv.symm n)) := by
      intro n
      rw [← hq]
      exact ambientGermEquiv_mk_translate m t (p₀, y₀) a (S (finSumFinEquiv.symm n)) (hq ▸ hSp _) (hhol n)
    have hbase : ∀ k ∈ baseIdeal Q p,
        basePullback m t k ∈ Ideal.span (range fun l => germAt (p, y₀) (fun z : ComplexModel m × ComplexModel t => rr l z.1)) := by
      intro k hk
      rw [hgen p hpUc] at hk
      have hmap := Ideal.mem_map_of_mem (basePullback m t) hk
      rw [Ideal.map_span] at hmap
      convert hmap using 2
      ext x
      constructor
      · rintro ⟨l, rfl⟩
        exact ⟨germAt p (rr l), ⟨l, rfl⟩, basePullback_germAt_fst m t (p, y₀) (rr l)
          (holAt_of_differentiableOn hUc (hrr l) hpUc)⟩
      · rintro ⟨_, ⟨l, rfl⟩, rfl⟩
        exact ⟨l, (basePullback_germAt_fst m t (p, y₀) (rr l)
          (holAt_of_differentiableOn hUc (hrr l) hpUc)).symm⟩
    have hrrspan : Ideal.span (range fun l => germAt (p, y₀) (fun z : ComplexModel m × ComplexModel t => rr l z.1)) =
        chartBaseIdeal m t (baseIdeal Q p) := by
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro _ ⟨l, rfl⟩
        show germAt (p, y₀) (fun z : ComplexModel m × ComplexModel t => rr l z.1) ∈ _
        rw [← basePullback_germAt_fst m t (p, y₀) (rr l) (holAt_of_differentiableOn hUc (hrr l) hpUc)]
        apply Ideal.mem_map_of_mem
        rw [hgen p hpUc]
        exact Ideal.subset_span ⟨l, rfl⟩
      · rw [chartBaseIdeal, Ideal.map_le_iff_le_comap]
        intro k hk
        exact hbase k hk
    have hLmap : L.map (ambientGermEquiv m t) =
        Ideal.span (range fun k => germAt (p, y₀) (f k)) ⊔ chartBaseIdeal m t (baseIdeal Qt a) := by
      rw [hK_eq, ← hrrspan, ← Ideal.span_union, hLspan, Ideal.map_span]
      congr 1
      ext x
      simp only [mem_image, mem_range, mem_union, exists_exists_eq_and]
      constructor
      · rintro ⟨n, rfl⟩
        rw [hgerm n]
        rcases h : finSumFinEquiv.symm n with k | l
        · exact Or.inl ⟨k, by simp [S]⟩
        · exact Or.inr ⟨l, by simp [S]⟩
      · rintro (⟨k, rfl⟩ | ⟨l, rfl⟩)
        · exact ⟨finSumFinEquiv (Sum.inl k), by rw [hgerm]; simp [S]⟩
        · exact ⟨finSumFinEquiv (Sum.inr l), by rw [hgerm]; simp [S]⟩
    have hKL : ∀ k ∈ baseIdeal Qt a, tangentPullback m t k ∈ L := by
      intro k hk
      have hmem : ambientGermEquiv m t (tangentPullback m t k) ∈ L.map (ambientGermEquiv m t) := by
        rw [hLmap, ambientGermEquiv_tangentPullback]
        exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hk)
      exact (Ideal.comap_map_of_bijective _ (ambientGermEquiv m t).bijective).le hmem
    haveI : Fact (∀ k ∈ baseIdeal Qt a, tangentPullback m t k ∈ L) := ⟨hKL⟩
    have hK : baseIdeal Qt a ≠ ⊤ := by
      rw [hK_eq]
      intro htop
      have hle := baseIdeal_le_maximalIdeal hpQ
      rw [htop, top_le_iff] at hle
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle
    have hfree' := hfree a hpV hgp
    have hideal : (Ideal.span (range Q₁)).map (MvPolynomial.map (baseGermHom C0 Qt a (hVB hpV))) =
        (originalNormalInitialIdeal m t L).map (MvPolynomial.map (Ideal.Quotient.mk (baseIdeal Qt a))) := by
      rw [← hnearby a (hVB hpV), Ideal.map_map]
      congr 1
      apply RingHom.ext
      intro P
      simp only [RingHom.comp_apply, MvPolynomial.map_map]
    rw [hideal] at hfree'
    have hflat := flat_quotient_of_free_initial m t (baseIdeal Qt a) L hK hfree'
    exact cyclicFlat_of_flat_library m t (baseIdeal Qt a) L (fun k => germAt (p, y₀) (f k)) hLmap hflat

theorem inSpanAt_comp_equiv {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {μ ν : Type*} [Fintype μ]
    [Fintype ν] (e : ν ≃ μ) (s : μ → Z → ℂ) (y : Z) (g : Z → ℂ) :
    InSpanAt (s ∘ e) y g ↔ InSpanAt s y g := by
  constructor
  · rintro ⟨hg, c, hc, he⟩
    refine ⟨hg, fun k => c (e.symm k), fun k => hc _, ?_⟩
    filter_upwards [he] with z hz
    rw [hz]
    exact Fintype.sum_equiv e _ _ (fun j => by simp)
  · rintro ⟨hg, c, hc, he⟩
    refine ⟨hg, fun j => c (e j), fun j => hc _, ?_⟩
    filter_upwards [he] with z hz
    rw [hz]
    exact (Fintype.sum_equiv e _ _ (fun j => by simp)).symm

theorem holAt_finset_prod {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {ι : Type*} (s : Finset ι)
    {f : ι → Z → ℂ} {y : Z} (hf : ∀ i ∈ s, HolAt (f i) y) : HolAt (fun z => ∏ i ∈ s, f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holAt_const 1 y
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem germAt_finset_prod {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {ι : Type*} (s : Finset ι)
    {f : ι → Z → ℂ} {y : Z} (hf : ∀ i ∈ s, HolAt (f i) y) :
    germAt y (fun z => ∏ i ∈ s, f i z) = ∏ i ∈ s, germAt y (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [germAt_const]
    exact map_one _
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, HolAt (f j) y := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    simp only [Finset.prod_insert hi]
    rw [germAt_mul (hf i (Finset.mem_insert_self i s)) (holAt_finset_prod s hs), ih hs]

/-- **Generic chart flatness over an irreducible base.** -/
theorem exists_flat_irreducible (p₀ : ComplexModel m) (y₀ : ComplexModel t) (Q : Set (ComplexModel m))
    (hQ : Hironaka.Analytic.Unibranch.HironakaG10FrRouteG.IsAnalyticNear Q p₀) (hprime : (baseIdeal Q p₀).IsPrime)
    {a b : ℕ} (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
    (hA : ∀ i j, HolAt (A i j) (p₀, y₀)) :
    ∃ g : ComplexModel m → ℂ, HolAt g p₀ ∧ (¬ ∀ᶠ p in 𝓝 p₀, p ∈ Q → g p = 0) ∧
      ∀ᶠ p in 𝓝 p₀, p ∈ Q → g p ≠ 0 → HironakaG10MwWindowFamily.ChartFlat m t A (p, y₀) (baseIdeal Q p) := by
  classical
  obtain ⟨N, hN, hp₀N, r, qg, hqg, hQN⟩ := id hQ
  -- Cartan generators of the vanishing ideal of `Q`
  obtain ⟨U₁, hU₁, hp₀U₁, μ, hμ, rr₀, hrr₀, hgen₀⟩ :=
    CartanIrreducibleReduction.localCartan_of_irreducibleLocalCartan
      (CartanIrreducible.irreducibleLocalCartan m) N hN r qg hqg p₀ hp₀N
  let e := (Fintype.equivFin μ).symm
  let rr : Fin (Fintype.card μ) → ComplexModel m → ℂ := rr₀ ∘ e
  let Uc := U₁ ∩ N
  have hUc : IsOpen Uc := hU₁.inter hN
  have hp₀Uc : p₀ ∈ Uc := ⟨hp₀U₁, hp₀N⟩
  have hrr : ∀ l, DifferentiableOn ℂ (rr l) Uc := fun l => (hrr₀ _).mono inter_subset_left
  have hQZ : ∀ p ∈ N, ∀ f, vanishingIdealF Q p f ↔ vanishingIdealF {w | ∀ i, qg i w = 0} p f := by
    intro p hp f
    have hev : ∀ᶠ x in 𝓝 p, x ∈ N := hN.mem_nhds hp
    constructor
    · rintro ⟨hf, hv⟩
      refine ⟨hf, ?_⟩
      filter_upwards [hv, hev] with x hx hxN hxZ
      apply hx
      have : x ∈ Q ∩ N := by rw [hQN]; exact ⟨hxN, hxZ⟩
      exact this.1
    · rintro ⟨hf, hv⟩
      refine ⟨hf, ?_⟩
      filter_upwards [hv, hev] with x hx hxN hxQ
      have : x ∈ Q ∩ N := ⟨hxQ, hxN⟩
      rw [hQN] at this
      exact hx this.2
  have hgen : ∀ p ∈ Uc, baseIdeal Q p = Ideal.span (range fun l => germAt p (rr l)) := by
    intro p hp
    refine baseIdeal_eq_span_of_generators Q hUc rr hrr (fun p' hp' f => ?_) hp
    rw [hQZ p' hp'.2, hgen₀ p' hp'.1, ← inSpanAt_comp_equiv e rr₀ p' f]
  -- the matrices of the rows below `i`, their relative starts, and one row-flatness function per row
  let A' : Fin a → Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ :=
    fun i l j => if i < l then A l j else fun _ => 0
  have hA' : ∀ i l j, HolAt (A' i l j) (p₀, y₀) := by
    intro i l j
    by_cases h : i < l
    · simp only [A', if_pos h]; exact hA l j
    · simp only [A', if_neg h]; exact holAt_const 0 _
  have hstart := fun i => Hironaka.Analytic.Unibranch.HironakaG10RmRelStart.exists_relExactStartOn y₀ hQ (A' i) (hA' i)
  choose c G W hW hpW hS using hstart
  have hAev : ∀ᶠ z in 𝓝 ((p₀, y₀) : ComplexModel m × ComplexModel t), ∀ i j, DifferentiableAt ℂ (A i j) z :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => hA i j
  obtain ⟨OA, hOAsub, hOA, hq₀OA⟩ := eventually_nhds_iff.mp hAev
  let f : ∀ i, Fin (c i) → ComplexModel m × ComplexModel t → ℂ :=
    fun i k z => ∑ j, A i j z * G i j k z
  have hf : ∀ i k, DifferentiableOn ℂ (f i k) (W i ∩ OA) := by
    intro i k z hz
    have hG : ∀ j, DifferentiableAt ℂ (G i j k) z := fun j =>
      ((hS i).holG j k).differentiableAt ((hW i).mem_nhds hz.1)
    exact (DifferentiableAt.fun_sum fun j _ => (hOAsub z hz.2 i j).mul (hG j)).differentiableWithinAt
  have hrow := fun i => exists_rowFlat p₀ y₀ Q hprime hUc hp₀Uc rr hrr hgen (f i)
    ((hW i).inter hOA) ⟨hpW i, hq₀OA⟩ (hf i)
  choose g hg hgnot hgev using hrow
  refine ⟨fun p => ∏ i, g i p, holAt_finset_prod Finset.univ fun i _ => hg i, ?_, ?_⟩
  · intro h
    have hmem : germAt p₀ (fun p => ∏ i, g i p) ∈ baseIdeal Q p₀ :=
      (germAt_mem_baseIdeal_iff Q p₀ (holAt_finset_prod Finset.univ fun i _ => hg i)).mpr h
    rw [germAt_finset_prod Finset.univ fun i _ => hg i] at hmem
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hprime)).mp hmem
    exact hgnot i ((germAt_mem_baseIdeal_iff Q p₀ (hg i)).mp hi)
  · have hWev : ∀ᶠ p in 𝓝 p₀, ∀ i, (p, y₀) ∈ W i ∩ OA := by
      have ht : Tendsto (fun p : ComplexModel m => (p, y₀)) (𝓝 p₀) (𝓝 (p₀, y₀)) :=
        (continuous_id.prodMk continuous_const).tendsto p₀
      exact eventually_all.mpr fun i => ht.eventually (((hW i).inter hOA).mem_nhds ⟨hpW i, hq₀OA⟩)
    filter_upwards [eventually_all.mpr hgev, hWev] with p hgp hpW' hpQ hg0
    have hgi : ∀ i, g i p ≠ 0 := fun i => by
      intro h0
      exact hg0 (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    have hflat : ∀ i, CyclicFlat m t (baseIdeal Q p) (fun k => germAt (p, y₀) (f i k)) :=
      fun i => hgp i hpQ (hgi i)
    have hAp : ∀ i j, HolAt (A i j) (p, y₀) := fun i j =>
      holAt_of_differentiableOn hOA (fun z hz => (hOAsub z hz i j).differentiableWithinAt) (hpW' i).2
    have hGp : ∀ i j k, HolAt (G i j k) (p, y₀) := fun i j k =>
      holAt_of_differentiableOn (hW i) ((hS i).holG j k) (hpW' i).1
    have hfgerm : ∀ i, (fun k => germAt (p, y₀) (f i k)) =
        fun k => ∑ j, germAt (p, y₀) (A i j) * germAt (p, y₀) (G i j k) := by
      intro i
      funext k
      rw [germAt_sum Finset.univ fun j _ => (hAp i j).mul (hGp i j k)]
      exact Finset.sum_congr rfl fun j _ => germAt_mul (hAp i j) (hGp i j k)
    have hcyc : ∀ i, CyclicGen m t A (p, y₀) (baseIdeal Q p) i (fun k => germAt (p, y₀) (f i k)) := by
      intro i
      rw [hfgerm i]
      obtain ⟨hcomp, hexact⟩ := Hironaka.Analytic.Unibranch.HironakaG10GfModStart.exactStartMod_of_relExactStartOn (hS i) (hW i)
        (hpW' i).1 hpQ
      have hA'germ : ∀ l j, germAt (p, y₀) (A' i l j) = if i < l then germAt (p, y₀) (A l j) else 0 := by
        intro l j
        by_cases h : i < l
        · simp only [A', if_pos h]
        · simp only [A', if_neg h]; exact germAt_zero _
      refine cyclicGen_of_start m t A (p, y₀) (baseIdeal Q p) i (fun j k => germAt (p, y₀) (G i j k)) ?_ ?_
      · intro l hl k
        have := hcomp l k
        simp only [hA'germ, if_pos hl] at this
        exact this
      · intro v hv
        refine hexact v fun l => ?_
        by_cases hl : i < l
        · simp only [hA'germ, if_pos hl]
          exact hv l hl
        · simp only [hA'germ, if_neg hl, zero_mul, Finset.sum_const_zero]
          exact Ideal.zero_mem _
    exact chartFlat_of_cyclicFlat m t A (p, y₀) (baseIdeal Q p) c (fun i k => germAt (p, y₀) (f i k)) hcyc hflat

end RowFlat

end

end Hironaka.Analytic.Unibranch.HironakaG10GnIrreducible
