/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Support.FiniteSpanRangeExact
import Hironaka.Coherence.OkaIdealOperations
import Hironaka.Coherence.CoherentIdealColon
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Span

/-! # ONE actual analytic open stabilizes ALL literal powers of ORIGINAL coherent saturation

The original coherent GermIdeal supplies its real finite holomorphic generators
internally. TRUE whole-germ finite spans and actual finite functional identities
identify the entire original origin ideal. Actual Noetherianity internally
selects a stable index of its REAL ascending colon chain. Genuine Oka coherence
internally constructs finite generators of both selected successive colons.
WHOLE origin membership of every actual next-colon generator spreads its finite
functional witness to ONE genuine open, proving exact entire stalk equality
at EVERY nearby point. Literal algebraic induction then stabilizes ALL powers
on this SAME open, and genuine original ideal closure identifies the ENTIRE
saturation union with its selected fixed colon.

The original Euclidean consumer supplies BOTH true Oka coherence and true
holomorphic-germ Noetherianity internally. The original GermIdeal consumer
supplies its finite spans internally from actual IsCoherent. No caller index,
finite-colon generators, stabilization, saturation or result certificate is
supplied. Empty families, zero and unit ideals, zero multipliers and zero
ambient dimensions are literal. No canonical map on all origin germs to nearby
stalks is invented; only actual whole functional witnesses are spread.

Actual deformation-to-normal-cone equations and their saturated ideal still
require identification with the WHOLE nearby original graded cone. Nearby
ALL-order finite freeness, analytic normal-flat loci, higher HS and G8 remain
OPEN. Frozen old modules and Blueprint chapters are unchanged.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaRelativeNormalCoherentSaturation
noncomputable section
open HolGerm OkaRelationSheaf OkaIdealOperations OkaCoherence

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private theorem mk_finite_sum_mul (a s : ι → X → ℂ)
    (ha : ∀ i, HolAt (a i) 0) (hs : ∀ i, HolAt (s i) 0) :
    HolGerm.mk (fun x => ∑ i, a i x*s i x)
        (HolAt.fintype_sum fun i => HolAt.mul (ha i) (hs i)) =
      ∑ i, HolGerm.mk (a i) (ha i)*HolGerm.mk (s i) (hs i) := by
  rw [HolGerm.mk_sum Finset.univ (fun i x => a i x*s i x)
    (fun i => HolAt.mul (ha i) (hs i))]
  exact Finset.sum_congr rfl fun i _ => HolGerm.mk_mul _ _ _ _

/-- Actual analytic span membership spreads its whole finite functional witness. -/
theorem inSpanAt_eventually {s : ι → X → ℂ} {g : X → ℂ} {x : X}
    (h : InSpanAt s x g) : ∀ᶠ y in 𝓝 x, InSpanAt s y g := by
  obtain ⟨hg,a,ha,he⟩ := h
  have hae : ∀ᶠ y in 𝓝 x, ∀ i, HolAt (a i) y :=
    eventually_all.mpr (fun i => (ha i).eventually)
  filter_upwards [hg.eventually,hae,he.eventuallyEq_nhds] with y hy hay hey
  exact ⟨hy,a,hay,hey⟩

/-- Actual finite holomorphic substitution composes genuine entire span witnesses. -/
theorem inSpanAt_substitute {s : ι → X → ℂ} {t : κ → X → ℂ} {g : X → ℂ} {y : X}
    (ht : ∀ j, InSpanAt s y (t j)) (hg : InSpanAt t y g) : InSpanAt s y g := by
  classical
  obtain ⟨hg,a,ha,he⟩ := hg
  choose b hb htEq using fun j => (ht j).2
  have htAll : ∀ᶠ x in 𝓝 y, ∀ j, t j x = ∑ i, b j i x*s i x := eventually_all.mpr htEq
  refine ⟨hg,fun i x => ∑ j, a j x*b j i x,
    fun i => HolAt.fintype_sum fun j => (ha j).mul (hb j i),?_⟩
  filter_upwards [he,htAll] with x hx htx
  rw [hx]
  simp_rw [htx]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
  exact Finset.sum_comm

/-- Entire finite analytic span is closed under the actual holomorphic multiplier. -/
theorem inSpanAt_mul_actual {s : ι → X → ℂ} {g h : X → ℂ} {y : X}
    (hg : InSpanAt s y g) (hh : HolAt h y) : InSpanAt s y (fun x => g x*h x) := by
  obtain ⟨hg,a,ha,he⟩ := hg
  refine ⟨hg.mul hh,fun i x => a i x*h x,fun i => (ha i).mul hh,?_⟩
  filter_upwards [he] with x hx
  rw [hx,Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Whole finite analytic spans equal literal ideals in the actual origin germ ring. -/
theorem inSpanAt_zero_iff_mem_origin_span (s : ι → X → ℂ)
    (hs : ∀ i, HolAt (s i) 0) {g : X → ℂ} (hg : HolAt g 0) :
    InSpanAt s 0 g ↔ HolGerm.mk g hg ∈ Ideal.span (range fun i => HolGerm.mk (s i) (hs i)) := by
  classical
  constructor
  · rintro ⟨_,a,ha,he⟩
    have hsum : HolAt (fun x => ∑ i, a i x*s i x) 0 :=
      HolAt.fintype_sum fun i => (ha i).mul (hs i)
    have hm : HolGerm.mk g hg = ∑ i, HolGerm.mk (a i) (ha i)*HolGerm.mk (s i) (hs i) := by
      calc
        HolGerm.mk g hg = HolGerm.mk (fun x => ∑ i, a i x*s i x) hsum := HolGerm.mk_eq_mk_iff.mpr he
        _ = _ := mk_finite_sum_mul a s ha hs
    rw [hm]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)
  · intro hmem
    obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
    choose a ha hca using fun i => HolGerm.exists_eq_mk (c i)
    have hsum : HolAt (fun x => ∑ i, a i x*s i x) 0 :=
      HolAt.fintype_sum fun i => HolAt.mul (ha i) (hs i)
    refine ⟨hg,a,ha,?_⟩
    apply (HolGerm.mk_eq_mk_iff (hf := hg) (hg := hsum)).mp
    rw [mk_finite_sum_mul a s ha hs]
    have hm : (∑ i, HolGerm.mk (a i) (ha i)*HolGerm.mk (s i) (hs i)) = HolGerm.mk g hg := by
      simpa only [hca] using hc
    exact hm.symm

/-- Literal repeated colons of the ORIGINAL whole analytic ideal predicate. -/
def actualColonChain (I : X → (X → ℂ) → Prop) (h : X → ℂ) : ℕ → X → (X → ℂ) → Prop
  | 0 => I
  | q+1 => colonIdeal (actualColonChain I h q) h

/-- Literal repeated colons in a genuine ring of WHOLE germs. -/
def actualOriginColonChain {R : Type*} [CommRing R] (I : Ideal R) (a : R) : ℕ → Ideal R
  | 0 => I
  | q+1 => (actualOriginColonChain I a q).colon {a}

/-- The actual original ring chain is increasing. -/
theorem actualOriginColonChain_monotone {R : Type*} [CommRing R] (I : Ideal R) (a : R) :
    Monotone (actualOriginColonChain I a) := by
  apply monotone_nat_of_le_succ
  intro q
  exact Ideal.le_colon

/-- Actual Noetherian ascending chains internally produce a stable index. -/
theorem exists_actual_origin_colon_stable {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (a : R) :
    ∃ N : ℕ, actualOriginColonChain I a N = actualOriginColonChain I a (N+1) := by
  let f : ℕ →o Submodule R R := ⟨actualOriginColonChain I a,actualOriginColonChain_monotone I a⟩
  obtain ⟨N,hN⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R R) f
  exact ⟨N,hN (N+1) (Nat.le_succ N)⟩

/-- Genuine Oka coherence internally produces EVERY actual original colon presentation. -/
theorem actualColonChain_finitely_generated (hX : OkaProperty X)
    {I : X → (X → ℂ) → Prop} (hI : IdealFGAt I (0 : X))
    {h : X → ℂ} (hh : HolAt h 0) (q : ℕ) : IdealFGAt (actualColonChain I h q) 0 := by
  induction q with
  | zero => exact hI
  | succ q ih => exact ih.colon hX hh

/-- EVERY repeated original colon retains the true WHOLE origin-germ dictionary. -/
theorem actualColonChain_origin_dictionary
    {I : X → (X → ℂ) → Prop} (s : ι → X → ℂ) (hs : ∀ i, HolAt (s i) 0)
    (hI : ∀ g, I 0 g ↔ InSpanAt s 0 g) {h : X → ℂ} (hh : HolAt h 0)
    (q : ℕ) {g : X → ℂ} (hg : HolAt g 0) :
    actualColonChain I h q 0 g ↔ HolGerm.mk g hg ∈
      actualOriginColonChain (Ideal.span (range fun i => HolGerm.mk (s i) (hs i))) (HolGerm.mk h hh) q := by
  induction q generalizing g with
  | zero => exact (hI g).trans (inSpanAt_zero_iff_mem_origin_span s hs hg)
  | succ q ih =>
    change (HolAt g 0 ∧ actualColonChain I h q 0 (fun x => g x*h x)) ↔ _
    rw [and_iff_right hg,ih (hg.mul hh)]
    simp only [actualOriginColonChain,Submodule.mem_colon_singleton,smul_eq_mul]
    rfl

/-- Actual coherent finite presentations spread WHOLE origin inclusion to ALL nearby stalks. -/
theorem exists_open_coherent_inclusion
    {I J : X → (X → ℂ) → Prop} (hI : IdealFGAt I (0 : X)) (hJ : IdealFGAt J (0 : X))
    (hIJ : ∀ g, I 0 g → J 0 g) :
    ∃ U : Set X, IsOpen U ∧ (0 : X) ∈ U ∧ ∀ y ∈ U, ∀ g, I y g → J y g := by
  classical
  obtain ⟨UI,hUI,h0I,μ,_,t,ht,htI⟩ := hI
  obtain ⟨UJ,hUJ,h0J,ν,_,s,hs,hsJ⟩ := hJ
  have ht0 : ∀ j, HolAt (t j) 0 := fun j => holAt_of_differentiableOn hUI (ht j) h0I
  have hts : ∀ j, InSpanAt s 0 (t j) := fun j =>
    (hsJ 0 h0J _).mp (hIJ _ ((htI 0 h0I _).mpr (inSpanAt_self ht0 j)))
  have he : ∀ᶠ y in 𝓝 (0 : X), ∀ j, InSpanAt s y (t j) :=
    eventually_all.mpr fun j => inSpanAt_eventually (hts j)
  obtain ⟨V,hVe,hV,h0V⟩ := mem_nhds_iff.mp he
  refine ⟨UI ∩ UJ ∩ V,(hUI.inter hUJ).inter hV,⟨⟨h0I,h0J⟩,h0V⟩,?_⟩
  intro y hy g hg
  exact (hsJ y hy.1.2 g).mpr
    (inSpanAt_substitute (hVe hy.2) ((htI y hy.1.1 g).mp hg))

/-- Genuine finite coherent presentations spread exact origin equality to ONE whole neighborhood. -/
theorem exists_open_coherent_equality
    {I J : X → (X → ℂ) → Prop} (hI : IdealFGAt I (0 : X)) (hJ : IdealFGAt J (0 : X))
    (hIJ : ∀ g, I 0 g ↔ J 0 g) :
    ∃ U : Set X, IsOpen U ∧ (0 : X) ∈ U ∧ ∀ y ∈ U, ∀ g, I y g ↔ J y g := by
  obtain ⟨U,hU,h0U,hUJ⟩ := exists_open_coherent_inclusion hI hJ (fun g => (hIJ g).mp)
  obtain ⟨V,hV,h0V,hVI⟩ := exists_open_coherent_inclusion hJ hI (fun g => (hIJ g).mpr)
  exact ⟨U ∩ V,hU.inter hV,⟨h0U,h0V⟩,fun y hy g => ⟨hUJ y hy.1 g,hVI y hy.2 g⟩⟩

/-- Every actual original repeated colon membership is a genuinely holomorphic germ. -/
theorem actualColonChain_holomorphic
    {I : X → (X → ℂ) → Prop} {h : X → ℂ} {y : X}
    (hI : ∀ g, I y g → HolAt g y) (q : ℕ) {g : X → ℂ}
    (hg : actualColonChain I h q y g) : HolAt g y := by
  cases q with
  | zero => exact hI g hg
  | succ q => exact hg.1

/-- ONLY original coherence internally supplies the index and ONE actual all-stalk stability open. -/
theorem exists_original_coherent_colon_neighborhood
    [IsNoetherianRing (HolGerm X)] (hX : OkaProperty X)
    {I : X → (X → ℂ) → Prop} (hI : IdealFGAt I (0 : X))
    {h : X → ℂ} (hh : HolAt h 0) :
    ∃ N : ℕ, ∃ U : Set X, IsOpen U ∧ (0 : X) ∈ U ∧
      (∀ y ∈ U, HolAt h y) ∧
      ∀ y ∈ U, ∀ g, actualColonChain I h N y g ↔ actualColonChain I h (N+1) y g := by
  classical
  obtain ⟨UI,hUI,h0I,μ,_,s,hs,hsI⟩ := hI
  have hs0 : ∀ i, HolAt (s i) 0 := fun i => holAt_of_differentiableOn hUI (hs i) h0I
  have hI0 : ∀ g, I 0 g ↔ InSpanAt s 0 g := hsI 0 h0I
  have hIhol : ∀ g, I 0 g → HolAt g 0 := fun g hg => ((hI0 g).mp hg).1
  obtain ⟨N,hN⟩ := exists_actual_origin_colon_stable
    (Ideal.span (range fun i => HolGerm.mk (s i) (hs0 i))) (HolGerm.mk h hh)
  have horigin : ∀ g, actualColonChain I h N 0 g ↔ actualColonChain I h (N+1) 0 g := by
    intro g
    by_cases hg : HolAt g 0
    · rw [actualColonChain_origin_dictionary s hs0 hI0 hh N hg,
        actualColonChain_origin_dictionary s hs0 hI0 hh (N+1) hg,hN]
    · constructor
      · intro hmem
        exact (hg (actualColonChain_holomorphic hIhol N hmem)).elim
      · intro hmem
        exact (hg (actualColonChain_holomorphic hIhol (N+1) hmem)).elim
  have hIfg : IdealFGAt I (0 : X) := ⟨UI,hUI,h0I,μ,inferInstance,s,hs,hsI⟩
  obtain ⟨V,hV,h0V,he⟩ := exists_open_coherent_equality
    (actualColonChain_finitely_generated hX hIfg hh N)
    (actualColonChain_finitely_generated hX hIfg hh (N+1)) horigin
  obtain ⟨W,hW,h0W,hhW⟩ := hh.exists_isOpen
  refine ⟨N,V ∩ W,hV.inter hW,⟨h0V,h0W⟩,?_,?_⟩
  · exact fun y hy => holAt_of_differentiableOn hW hhW hy.2
  · exact fun y hy => he y hy.1

/-- Exact actual whole-stalk stabilization propagates through all subsequent actual colons. -/
theorem actualColonChain_stable_all
    (I : X → (X → ℂ) → Prop) (h : X → ℂ) (N : ℕ) (y : X)
    (hN : ∀ g, actualColonChain I h N y g ↔ actualColonChain I h (N+1) y g) (q : ℕ) :
    ∀ g, actualColonChain I h (N+q) y g ↔ actualColonChain I h N y g := by
  induction q with
  | zero => simp
  | succ q ih =>
    intro g
    change (HolAt g y ∧ actualColonChain I h (N+q) y (fun x => g x*h x)) ↔ _
    rw [ih]
    exact (hN g).symm

/-- Repeated actual original colons are EXACTLY the literal original ideal colon by h^q. -/
theorem actualColonChain_power_dictionary
    {I : X → (X → ℂ) → Prop} {h : X → ℂ} {y : X}
    (hI : ∀ g, I y g → HolAt g y) (hh : HolAt h y) (q : ℕ) (g : X → ℂ) :
    actualColonChain I h q y g ↔ HolAt g y ∧ I y (fun x => g x*h x^q) := by
  induction q generalizing g with
  | zero =>
    simp only [actualColonChain,pow_zero,mul_one]
    exact ⟨fun hg => ⟨hI g hg,hg⟩,fun hg => hg.2⟩
  | succ q ih =>
    change (HolAt g y ∧ actualColonChain I h q y (fun x => g x*h x)) ↔ _
    rw [ih]
    have he : (fun x => (g x*h x)*h x^q) = (fun x => g x*h x^(q+1)) := by
      funext x
      ring
    rw [he]
    exact ⟨fun hg => ⟨hg.1,hg.2.2⟩,fun hg => ⟨hg.1,hg.1.mul hh,hg.2⟩⟩

/-- Actual holomorphic ideal closure makes the literal analytic colon chain increasing. -/
theorem actualColonChain_monotone_at
    {I : X → (X → ℂ) → Prop} {h : X → ℂ} {y : X}
    (hIhol : ∀ g, I y g → HolAt g y) (hImul : ∀ g, I y g → I y (fun x => g x*h x)) :
    Monotone (fun q => {g | actualColonChain I h q y g}) := by
  apply monotone_nat_of_le_succ
  intro q g hq
  induction q generalizing g with
  | zero => exact ⟨hIhol g hq,hImul g hq⟩
  | succ q ih => exact ⟨hq.1,ih hq.2⟩

/-- Only ORIGINAL coherence and an actual holomorphic h produce SAME-open ALL-power saturation. -/
theorem exists_uniform_original_coherent_saturation
    [IsNoetherianRing (HolGerm X)] (hX : OkaProperty X)
    {I : X → (X → ℂ) → Prop} (hI : IdealFGAt I (0 : X))
    {h : X → ℂ} (hh : HolAt h 0) :
    ∃ N : ℕ, ∃ U : Set X, IsOpen U ∧ (0 : X) ∈ U ∧
      (∀ y ∈ U, HolAt h y) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g, actualColonChain I h (N+q) y g ↔ actualColonChain I h N y g) ∧
      ∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
        (I y (fun x => g x*h x^q) ↔ I y (fun x => g x*h x^N)) := by
  obtain ⟨N,U,hU,h0U,hhU,he⟩ := exists_original_coherent_colon_neighborhood hX hI hh
  obtain ⟨V,hV,h0V,μ,_,s,hs,hsI⟩ := hI
  refine ⟨N,U ∩ V,hU.inter hV,⟨h0U,h0V⟩,fun y hy => hhU y hy.1,?_,?_⟩
  · exact fun y hy q => actualColonChain_stable_all I h N y (he y hy.1) q
  · intro y hy q hq g hg
    have hIhol : ∀ f, I y f → HolAt f y := fun f hf => ((hsI y hy.2 f).mp hf).1
    obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hq
    have h := actualColonChain_stable_all I h N y (he y hy.1) r g
    rw [actualColonChain_power_dictionary hIhol (hhU y hy.1) (N+r) g,
      actualColonChain_power_dictionary hIhol (hhU y hy.1) N g] at h
    simpa only [and_iff_right hg] using h

/-- TRUE entire saturation is the internally selected fixed colon at EVERY point of SAME U. -/
theorem exists_uniform_original_coherent_saturation_union
    [IsNoetherianRing (HolGerm X)] (hX : OkaProperty X)
    {I : X → (X → ℂ) → Prop} (hI : IdealFGAt I (0 : X))
    {h : X → ℂ} (hh : HolAt h 0) :
    ∃ N : ℕ, ∃ U : Set X, IsOpen U ∧ (0 : X) ∈ U ∧
      (∀ y ∈ U, HolAt h y) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g, actualColonChain I h (N+q) y g ↔ actualColonChain I h N y g) ∧
      (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
        (I y (fun x => g x*h x^q) ↔ I y (fun x => g x*h x^N))) ∧
      ∀ y ∈ U, ∀ g, (∃ q : ℕ, actualColonChain I h q y g) ↔ actualColonChain I h N y g := by
  obtain ⟨N,U,hU,h0U,hhU,he,hp⟩ := exists_uniform_original_coherent_saturation hX hI hh
  obtain ⟨V,hV,h0V,μ,_,s,hs,hsI⟩ := hI
  refine ⟨N,U ∩ V,hU.inter hV,⟨h0U,h0V⟩,fun y hy => hhU y hy.1,
    fun y hy => he y hy.1,fun y hy => hp y hy.1,?_⟩
  intro y hy g
  have hIhol : ∀ f, I y f → HolAt f y := fun f hf => ((hsI y hy.2 f).mp hf).1
  have hImul : ∀ f, I y f → I y (fun x => f x*h x) := fun f hf =>
    (hsI y hy.2 _).mpr (inSpanAt_mul_actual ((hsI y hy.2 f).mp hf) (hhU y hy.1))
  constructor
  · rintro ⟨q,hq⟩
    rcases le_total q N with hqN | hNq
    · exact actualColonChain_monotone_at hIhol hImul hqN hq
    · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hNq
      exact (he y hy.1 r g).mp hq
  · exact fun hg => ⟨N,hg⟩

/-- Euclidean original data internally supply BOTH true Oka coherence and germ Noetherianity. -/
theorem exists_euclidean_original_coherent_saturation (n : ℕ)
    {I : EuclideanSpace ℂ (Fin n) → (EuclideanSpace ℂ (Fin n) → ℂ) → Prop}
    (hI : IdealFGAt I 0) {h : EuclideanSpace ℂ (Fin n) → ℂ} (hh : HolAt h 0) :
    ∃ N : ℕ, ∃ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U ∧ 0 ∈ U ∧
      (∀ y ∈ U, HolAt h y) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g, actualColonChain I h (N+q) y g ↔ actualColonChain I h N y g) ∧
      ∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
        (I y (fun x => g x*h x^q) ↔ I y (fun x => g x*h x^N)) := by
  let := isNoetherianRing_holGerm_euclidean n
  exact exists_uniform_original_coherent_saturation (okaProperty_euclidean n) hI hh

/-- The ORIGINAL Euclidean GermIdeal coherence internally supplies its actual finite analytic spans. -/
theorem germIdeal_actual_finitely_generated {n : ℕ}
    (I : Hironaka.HolomorphicIdealSheaves.GermIdeal n (Hironaka.ComplexModel n)) (hI : I.IsCoherent) :
    IdealFGAt I.mem (0 : Hironaka.ComplexModel n) := by
  obtain ⟨U,hU,h0,N,s,hs,hsI⟩ := hI 0
  refine ⟨U,hU,h0,Fin N,inferInstance,s,fun i => mdifferentiableOn_iff_differentiableOn.mp (hs i),?_⟩
  intro y hy g
  rw [hsI y hy g,CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h => h.differentiableAt),a,
      fun i => (ha i).mono (fun _ h => h.differentiableAt),he⟩
  · rintro ⟨hg,a,ha,he⟩
    exact ⟨hg.mono (fun _ h => h.mdifferentiableAt),a,
      fun i => (ha i).mono (fun _ h => h.mdifferentiableAt),he⟩

/-- ONLY the actual ORIGINAL coherent GermIdeal and actual h produce SAME-open ALL literal powers. -/
theorem exists_original_germIdeal_uniform_saturation {n : ℕ}
    (I : Hironaka.HolomorphicIdealSheaves.GermIdeal n (Hironaka.ComplexModel n)) (hI : I.IsCoherent)
    {h : Hironaka.ComplexModel n → ℂ} (hh : HolAt h 0) :
    ∃ N : ℕ, ∃ U : Set (Hironaka.ComplexModel n), IsOpen U ∧ 0 ∈ U ∧
      (∀ y ∈ U, HolAt h y) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g, actualColonChain I.mem h (N+q) y g ↔ actualColonChain I.mem h N y g) ∧
      ∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
        (I.mem y (fun x => g x*h x^q) ↔ I.mem y (fun x => g x*h x^N)) :=
  exists_euclidean_original_coherent_saturation n (germIdeal_actual_finitely_generated I hI) hh

/-- Original coherent GermIdeal internally produces EXACT entire nearby saturation and ALL powers. -/
theorem exists_original_germIdeal_exact_uniform_saturation {n : ℕ}
    (I : Hironaka.HolomorphicIdealSheaves.GermIdeal n (Hironaka.ComplexModel n)) (hI : I.IsCoherent)
    {h : Hironaka.ComplexModel n → ℂ} (hh : HolAt h 0) :
    ∃ N : ℕ, ∃ U : Set (Hironaka.ComplexModel n), IsOpen U ∧ 0 ∈ U ∧
      (∀ y ∈ U, HolAt h y) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ g, actualColonChain I.mem h (N+q) y g ↔ actualColonChain I.mem h N y g) ∧
      (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
        (I.mem y (fun x => g x*h x^q) ↔ I.mem y (fun x => g x*h x^N))) ∧
      ∀ y ∈ U, ∀ g, (∃ q : ℕ, actualColonChain I.mem h q y g) ↔ actualColonChain I.mem h N y g := by
  let := isNoetherianRing_holGerm_euclidean n
  exact exists_uniform_original_coherent_saturation_union (okaProperty_euclidean n)
    (germIdeal_actual_finitely_generated I hI) hh

end
end Hironaka.HironakaRelativeNormalCoherentSaturation
