/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Manifold.HolomorphicContDiff
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Algebra of holomorphic germs and ideal sheaves

Elementary closure properties of `HolomorphicAt`, `IsInSpanAt` and `GermIdeal.pullback`
(`Hironaka.HolomorphicIdealSheaves`), used to apply the universal property of blowups.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HolomorphicIdealSheaves

noncomputable section

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

section Holomorphic

variable {f g : M → ℂ} {x : M}

theorem HolomorphicAt.mdifferentiableAt (hf : HolomorphicAt n f x) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f x :=
  hf.self_of_nhds

theorem HolomorphicAt.continuousAt (hf : HolomorphicAt n f x) : ContinuousAt f x :=
  hf.mdifferentiableAt.continuousAt

theorem HolomorphicAt.eventually (hf : HolomorphicAt n f x) :
    ∀ᶠ y in 𝓝 x, HolomorphicAt n f y :=
  hf.eventually_nhds

theorem holomorphicAt_const (c : ℂ) : HolomorphicAt n (fun _ : M => c) x :=
  Eventually.of_forall fun _ => mdifferentiableAt_const

theorem HolomorphicAt.add (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    HolomorphicAt n (fun y => f y + g y) x :=
  (hf.and hg).mono fun _ h => h.1.add h.2

theorem HolomorphicAt.mul (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    HolomorphicAt n (fun y => f y * g y) x :=
  (hf.and hg).mono fun _ h => h.1.mul h.2

theorem HolomorphicAt.sum {ι : Type*} (s : Finset ι) {F : ι → M → ℂ}
    (hF : ∀ i ∈ s, HolomorphicAt n (F i) x) :
    HolomorphicAt n (fun y => ∑ i ∈ s, F i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holomorphicAt_const (n := n) (x := x) (0 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem HolomorphicAt.congr (hf : HolomorphicAt n f x) (h : f =ᶠ[𝓝 x] g) :
    HolomorphicAt n g x := by
  filter_upwards [hf.eventually, h.eventually_nhds] with y hy (hfg : f =ᶠ[𝓝 y] g)
  exact hy.mdifferentiableAt.congr_of_eventuallyEq hfg.symm

end Holomorphic

section Smooth

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]

/-- A holomorphic germ pulls back to a holomorphic germ along a smooth map. -/
theorem HolomorphicAt.comp_contMDiff [IsManifold 𝓘(ℂ, ComplexModel m) ∞ Y]
    [IsManifold 𝓘(ℂ, ComplexModel n) ∞ M] {b : M → ℂ} {f : Y → M} {y : Y}
    (hb : HolomorphicAt n b (f y)) (hf : ∀ᶠ y' in 𝓝 y,
      ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y') :
    HolomorphicAt m (b ∘ f) y := by
  have hcont : ContinuousAt f y := hf.self_of_nhds.continuousAt
  filter_upwards [hcont.eventually hb.eventually, hf] with y' hy' hfy'
  exact hy'.mdifferentiableAt.comp y' (hfy'.mdifferentiableAt (by simp))

/-- **Holomorphic maps into a complex Banach space are smooth.**  A map which is holomorphic on a neighbourhood
of `y` is `C^∞` at `y`. -/
theorem contMDiffAt_of_eventually_mdifferentiableAt [IsManifold 𝓘(ℂ, ComplexModel m) ∞ Y]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : Y → E} {y : Y}
    (hF : ∀ᶠ y' in 𝓝 y, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, E) F y') :
    ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, E) ∞ F y := by
  obtain ⟨W, hWsub, hWopen, hyW⟩ := mem_nhds_iff.mp hF
  set e := chartAt (ComplexModel m) y
  set U : Set (ComplexModel m) := e.target ∩ e.symm ⁻¹' (W ∩ e.source)
  have hUopen : IsOpen U := e.isOpen_inter_preimage_symm (hWopen.inter e.open_source)
  have hyU : e y ∈ U := ⟨e.map_source (mem_chart_source _ y), by
    rw [mem_preimage, e.left_inv (mem_chart_source _ y)]; exact ⟨hyW, mem_chart_source _ y⟩⟩
  have hdiff : DifferentiableOn ℂ (F ∘ e.symm) U := by
    intro z hz
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) e.symm z :=
      ((contMDiffOn_chart_symm (n := ∞)).contMDiffAt (e.open_target.mem_nhds hz.1)).mdifferentiableAt
        (by simp)
    have h2 := (hWsub hz.2.1).comp z h1
    exact (mdifferentiableAt_iff_differentiableAt.mp h2).differentiableWithinAt
  have hsmooth : ContDiffAt ℂ ∞ (F ∘ e.symm) (e y) :=
    contDiffAt_of_differentiableOn_complex hdiff hUopen hyU
  rw [contMDiffAt_iff_source]
  exact (contMDiffAt_iff_contDiffAt.mpr hsmooth).contMDiffWithinAt

end Smooth

section Span

variable {x : M} {g h : M → ℂ} {S T : (M → ℂ) → Prop}

theorem IsInSpanAt.holomorphicAt (hg : IsInSpanAt (n := n) S x g) : HolomorphicAt n g x := hg.1

theorem IsInSpanAt.mono (hST : ∀ s, S s → T s) (hg : IsInSpanAt (n := n) S x g) :
    IsInSpanAt (n := n) T x g := by
  obtain ⟨hgh, N, s, a, hs, ha, hsum⟩ := hg
  exact ⟨hgh, N, s, a, fun i => hST _ (hs i), ha, hsum⟩

/-- A single multiple of an element of `S`. -/
theorem isInSpanAt_of_eq_mul {s a : M → ℂ} (hs : S s) (hg : HolomorphicAt n g x)
    (ha : HolomorphicAt n a x) (heq : g =ᶠ[𝓝 x] fun y => a y * s y) :
    IsInSpanAt (n := n) S x g :=
  ⟨hg, 1, fun _ => s, fun _ => a, fun _ => hs, fun _ => ha, by simpa using heq⟩

/-- Membership in the span of a single function. -/
theorem isInSpanAt_eq_iff :
    IsInSpanAt (n := n) (· = h) x g ↔
      HolomorphicAt n g x ∧ ∃ a, HolomorphicAt n a x ∧ g =ᶠ[𝓝 x] fun y => a y * h y := by
  constructor
  · rintro ⟨hg, N, s, a, hs, ha, hsum⟩
    refine ⟨hg, fun y => ∑ i, a i y, HolomorphicAt.sum _ fun i _ => ha i, ?_⟩
    filter_upwards [hsum] with y hy
    rw [hy, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hs i]
  · rintro ⟨hg, a, ha, heq⟩
    exact isInSpanAt_of_eq_mul rfl hg ha heq

/-- Membership in the span of a family of functions which each lie in the span of `h`. -/
theorem IsInSpanAt.of_forall_eq_mul
    (hS : ∀ s, S s → ∃ b, HolomorphicAt n b x ∧ s =ᶠ[𝓝 x] fun y => b y * h y)
    (hg : IsInSpanAt (n := n) S x g) : IsInSpanAt (n := n) (· = h) x g := by
  obtain ⟨hgh, N, s, a, hs, ha, hsum⟩ := hg
  choose b hb hbeq using fun i => hS (s i) (hs i)
  refine isInSpanAt_eq_iff.mpr ⟨hgh, fun y => ∑ i, a i y * b i y,
    HolomorphicAt.sum _ fun i _ => (ha i).mul (hb i), ?_⟩
  have hall : ∀ᶠ y in 𝓝 x, ∀ i, s i y = b i y * h y :=
    eventually_all.mpr fun i => hbeq i
  filter_upwards [hsum, hall] with y hy hy'
  rw [hy, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [hy' i]; ring

end Span

section Unit

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]

/-- Off a closed set `C`, the ideal of `C` pulls back to the unit ideal, which is invertible. -/
theorem isInvertible_pullback_vanishingIdeal_of_disjoint {C : Set M} (hC : IsClosed C)
    {f : Y → M} (hf : ∀ y, f y ∉ C) :
    (GermIdeal.pullback (m := m) f (vanishingIdeal (n := n) C)).IsInvertible := by
  intro x
  refine ⟨univ, isOpen_univ, mem_univ x, fun _ => 1, fun y _ =>
    mdifferentiableAt_const.mdifferentiableWithinAt, fun W _ _ ⟨y, hy⟩ => ⟨y, hy, one_ne_zero⟩,
    fun y _ g => ?_⟩
  constructor
  · intro hg
    exact isInSpanAt_of_eq_mul rfl hg.1 hg.1 (Eventually.of_forall fun _ => by simp)
  · intro hg
    have hone : (vanishingIdeal (n := n) C).mem (f y) (fun _ => 1) := by
      refine ⟨holomorphicAt_const 1, ?_⟩
      filter_upwards [hC.isOpen_compl.mem_nhds (hf y)] with z hz hzC
      exact absurd hzC hz
    exact isInSpanAt_of_eq_mul (s := fun _ => 1) (S := fun s => ∃ a,
      (vanishingIdeal (n := n) C).mem (f y) a ∧ s = a ∘ f) ⟨fun _ => 1, hone, rfl⟩ hg.1 hg.1
      (Eventually.of_forall fun _ => by simp)

end Unit

section Opens

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  (O : TopologicalSpace.Opens Y)

open Classical in
/-- Extension by zero of a function on an open subset. -/
def extendOpens (g : O → ℂ) : Y → ℂ := fun y => if hy : y ∈ O then g ⟨y, hy⟩ else 0

@[simp] theorem extendOpens_val (g : O → ℂ) (x : O) : extendOpens O g x.1 = g x := by
  simp [extendOpens, x.2]

theorem eventually_nhds_val_iff {x : O} {P : Y → Prop} :
    (∀ᶠ y in 𝓝 x.1, P y) ↔ ∀ᶠ x' in 𝓝 x, P x'.1 := by
  rw [← O.isOpen.nhdsWithin_eq x.2]
  exact (eventually_nhds_subtype_iff (O : Set Y) x P).symm

theorem mdifferentiableAt_comp_val_iff {F : Y → ℂ} {x : O} :
    MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (F ∘ Subtype.val) x ↔
      MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) F x.1 := by
  constructor
  · intro h
    exact ((differentiableWithinAt_localInvariantProp).liftPropAt_iff_comp_subtype_val _ _).mpr h
  · intro h
    exact h.comp x ((contMDiff_subtype_val (n := ∞) x).mdifferentiableAt (by simp))

theorem holomorphicAt_comp_val_iff {F : Y → ℂ} {x : O} :
    HolomorphicAt m (F ∘ Subtype.val) x ↔ HolomorphicAt m F x.1 := by
  unfold HolomorphicAt
  rw [eventually_nhds_val_iff O]
  simp only [mdifferentiableAt_comp_val_iff O]

theorem holomorphicAt_iff_extendOpens {g : O → ℂ} {x : O} :
    HolomorphicAt m g x ↔ HolomorphicAt m (extendOpens O g) x.1 := by
  rw [← holomorphicAt_comp_val_iff O]
  have : extendOpens O g ∘ Subtype.val = g := funext fun x => extendOpens_val O g x
  rw [this]

theorem eventually_mem_opens (x : O) : ∀ᶠ y in 𝓝 x.1, y ∈ O :=
  O.isOpen.mem_nhds x.2

/-- Spans of pulled-back families on an open subset agree with spans of the extensions. -/
theorem isInSpanAt_comp_val_iff {S : (Y → ℂ) → Prop} {x : O} {g : O → ℂ} :
    IsInSpanAt (n := m) (fun s' => ∃ s, S s ∧ s' = s ∘ Subtype.val) x g ↔
      IsInSpanAt (n := m) S x.1 (extendOpens O g) := by
  constructor
  · rintro ⟨hg, N, s', a, hs', ha, hsum⟩
    choose s hs hss using hs'
    refine ⟨(holomorphicAt_iff_extendOpens O).mp hg, N, s, fun i => extendOpens O (a i), hs,
      fun i => (holomorphicAt_iff_extendOpens O).mp (ha i), ?_⟩
    have hsum' := (eventually_nhds_val_iff O (x := x) (P := fun y => ∀ hy : y ∈ O,
      g ⟨y, hy⟩ = ∑ i, a i ⟨y, hy⟩ * s' i ⟨y, hy⟩)).mpr (hsum.mono fun x' hx' _ => hx')
    filter_upwards [hsum', eventually_mem_opens O x] with y hy hyO
    have e1 : extendOpens O g y = g ⟨y, hyO⟩ := extendOpens_val O g ⟨y, hyO⟩
    have e2 : ∀ i, extendOpens O (a i) y = a i ⟨y, hyO⟩ := fun i => extendOpens_val O _ ⟨y, hyO⟩
    simp only [e1, e2, hy hyO, hss]
    rfl
  · rintro ⟨hg, N, s, a, hs, ha, hsum⟩
    refine ⟨(holomorphicAt_iff_extendOpens O).mpr hg, N, fun i => s i ∘ Subtype.val,
      fun i => a i ∘ Subtype.val, fun i => ⟨s i, hs i, rfl⟩,
      fun i => (holomorphicAt_comp_val_iff O).mpr (ha i), ?_⟩
    have := (eventually_nhds_val_iff O).mp hsum
    filter_upwards [this] with y hy
    simpa using hy

/-- Invertibility of a pulled-back ideal restricts to open subsets. -/
theorem IsInvertible.pullback_comp_val {f : Y → M} {𝔞 : GermIdeal n M}
    (hinv : (GermIdeal.pullback (m := m) f 𝔞).IsInvertible) :
    (GermIdeal.pullback (m := m) (f ∘ Subtype.val : O → M) 𝔞).IsInvertible := by
  intro x
  obtain ⟨U, hU, hxU, h, hh, hnon, hiff⟩ := hinv x.1
  refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hxU, h ∘ Subtype.val,
    fun x' hx' => ?_, fun W hW hWU ⟨w, hw⟩ => ?_, fun x' hx' g => ?_⟩
  · exact ((mdifferentiableAt_comp_val_iff (m := m) O).mpr
      ((hh x'.1 hx').mdifferentiableAt (hU.mem_nhds hx'))).mdifferentiableWithinAt
  · have hWopen : IsOpen (Subtype.val '' W : Set Y) := O.isOpen.isOpenMap_subtype_val W hW
    obtain ⟨y, ⟨w', hw'W, rfl⟩, hy⟩ := hnon _ hWopen (by
      rintro _ ⟨w', hw', rfl⟩; exact hWU hw') ⟨w.1, w, hw, rfl⟩
    exact ⟨w', hw'W, hy⟩
  · have h1 : (GermIdeal.pullback (m := m) (f ∘ Subtype.val : O → M) 𝔞).mem x' g ↔
        (GermIdeal.pullback (m := m) f 𝔞).mem x'.1 (extendOpens O g) := by
      show IsInSpanAt (n := m) (fun s => ∃ a, 𝔞.mem ((f ∘ Subtype.val) x') a ∧
          s = a ∘ (f ∘ Subtype.val)) x' g ↔
        IsInSpanAt (n := m) (fun s => ∃ a, 𝔞.mem (f x'.1) a ∧ s = a ∘ f) x'.1 (extendOpens O g)
      rw [← isInSpanAt_comp_val_iff (m := m) O]
      constructor <;> refine fun hg => hg.mono fun s' hs' => ?_
      · obtain ⟨a, ha, rfl⟩ := hs'; exact ⟨a ∘ f, ⟨a, ha, rfl⟩, rfl⟩
      · obtain ⟨s, ⟨a, ha, rfl⟩, rfl⟩ := hs'; exact ⟨a, ha, rfl⟩
    have h2 : IsInSpanAt (n := m) (· = h ∘ Subtype.val) x' g ↔
        IsInSpanAt (n := m) (· = h) x'.1 (extendOpens O g) := by
      rw [← isInSpanAt_comp_val_iff (m := m) O]
      constructor <;> refine fun hg => hg.mono fun s' hs' => ?_
      · exact ⟨h, rfl, hs'⟩
      · obtain ⟨s, rfl, rfl⟩ := hs'; rfl
    rw [h1, h2]
    exact hiff x'.1 hx' _

end Opens

end

end Hironaka.HolomorphicIdealSheaves
