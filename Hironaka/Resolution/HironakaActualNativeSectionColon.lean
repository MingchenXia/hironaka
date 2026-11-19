import Hironaka.Resolution.HironakaActualSubmanifoldGermExtension
import Hironaka.Resolution.HironakaActualSectionRestrictedIdeals

/-!
The actual native flattening atlas, through its already constructed holomorphic
germ-extension theorem, gives pullback of restricted spans and their colons.
No global retraction, desired ideal identity, or canonical-history comparison
is an input.  This is a prospective G1 controlled-transform ingredient only;
it does not compare recursive invariant values or produce intrinsic descent.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualNativeSectionColon
noncomputable section

open Hironaka.HolomorphicIdealSheaves
  RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient
  RestrictedIdealExtension RestrictedIdealQuotient SubmanifoldChartedSpace
  HironakaActualSubmanifoldGermExtension

private theorem colonAlong_of_span {r : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel r) M] {A : Set M} {I L : GermIdeal r M}
    {x : M} {g : M → ℂ}
    (hg : IsInSpanAt (n := r) ((colonAlong r A I L).mem x) x g) :
    (colonAlong r A I L).mem x g := by
  obtain ⟨hhol,K,s,c,hs,hc,he⟩ := hg
  refine ⟨hhol,?_⟩
  intro a ha
  apply restrictOn_of_isInSpanAt
  have has : ∀ i, (restrictOn r A I).mem x (fun y => a y*s i y) :=
    fun i => (hs i).2 a ha
  have haHol : HolomorphicAt r (fun y => a y*g y) x := by
    have hex : IsInSpanAt (n := r) ((restrictOn r A I).mem x) x (fun y => a y*g y) := by
      refine ⟨?_,K,fun i y => a y*s i y,c,has,hc,?_⟩
      · have hcspan : IsInSpanAt (n := r) ((restrictOn r A I).mem x) x
            (fun y => ∑ i, c i y*(a y*s i y)) :=
          IsInSpanAt.sum Finset.univ fun i _ => IsInSpanAt.mul_left (hc i)
            (isInSpanAt_self (has i) (has i).1)
        apply HolomorphicAt.congr hcspan.holomorphicAt
        filter_upwards [he] with y hy
        rw [hy,Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      · filter_upwards [he] with y hy
        rw [hy,Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    exact hex.holomorphicAt
  refine ⟨haHol,K,fun i y => a y*s i y,c,has,hc,?_⟩
  filter_upwards [he] with y hy
  rw [hy,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X}

theorem restrictedSpan_native_iff (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀ (A : Set W) (J : GermIdeal n X)
      (_hJ : ∀ z g, J.mem z g → HolomorphicAt n g z) (p : W) (g : X → ℂ),
      IsInSpanOnAt (n := n) ((Subtype.val : W → X) '' A) (J.mem p.val) p.val g ↔
      IsInSpanOnAt (n := k) A
        ((GermIdeal.pullback (m := k) (Subtype.val : W → X) J).mem p) p
        (g ∘ Subtype.val) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A J hJ p g
  have hval := contMDiff_val hk hW
  constructor
  · rintro ⟨K,s,c,hs,hc,he⟩
    refine ⟨K,fun i => s i ∘ Subtype.val,fun i => c i ∘ Subtype.val,?_,?_,?_⟩
    · intro i
      exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨s i,hs i,rfl⟩
        ((hJ _ _ (hs i)).comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt)))
    · intro i
      exact (hc i).comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt)
    · filter_upwards [continuous_subtype_val.continuousAt.eventually he] with q hq hqA
      exact hq ⟨q,hqA,rfl⟩
  · intro h
    have hh : IsInSpanOnAt (n := k) A
        (fun t => ∃ a, J.mem p.val a ∧ t = a ∘ (Subtype.val : W → X)) p
        (g ∘ Subtype.val) :=
      IsInSpanOnAt.trans (fun _ ha => IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp ha)) h
    obtain ⟨K,s,c,hs,hc,he⟩ := hh
    choose a ha has using hs
    have hcoeff (i : Fin K) :
        ∃ C : X → ℂ, HolomorphicAt n C p.val ∧ C ∘ Subtype.val =ᶠ[nhds p] c i :=
      exists_ambient_holomorphic_germ hk hW p (c i) (hc i)
    choose C hC hCe using hcoeff
    refine ⟨K,a,C,ha,hC,?_⟩
    have hnear : {q : W | (q ∈ A → g q.val = ∑ i, c i q*s i q) ∧
        ∀ i : Fin K, C i q.val = c i q} ∈ nhds p := by
      exact he.and (eventually_all.mpr hCe)
    obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype W p _).mp hnear
    filter_upwards [hV] with y hy hyA
    obtain ⟨q,hqA,rfl⟩ := hyA
    obtain ⟨hq,hqC⟩ := hsub hy
    have hq' := hq hqA
    simp only [has,Function.comp_apply] at hq'
    calc
      g q.val = ∑ i, c i q*a i q.val := hq'
      _ = ∑ i, C i q.val*a i q.val := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hqC i]

theorem colonAlong_native_mem_iff (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀ (A : Set W) (I L : GermIdeal n X)
      (_hI : ∀ z g, I.mem z g → HolomorphicAt n g z)
      (_hL : ∀ z g, L.mem z g → HolomorphicAt n g z)
      (p : W) (h : X → ℂ) (_hh : HolomorphicAt n h p.val),
      (colonAlong n ((Subtype.val : W → X) '' A) I L).mem p.val h ↔
      (colonAlong k A
        (GermIdeal.pullback (m := k) (Subtype.val : W → X) I)
        (GermIdeal.pullback (m := k) (Subtype.val : W → X) L)).mem p
        (h ∘ Subtype.val) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A I L hI hL p h hh
  have hval := contMDiff_val hk hW
  have hhB : HolomorphicAt k (h ∘ (Subtype.val : W → X)) p :=
    hh.comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt)
  constructor
  · intro hm
    refine ⟨hhB,?_⟩
    intro b hb
    obtain ⟨hbhol,K,s,c,hs,hc,he⟩ := GermIdeal.mem_pullback_iff.mp hb
    choose a ha has using hs
    apply restrictOn_of_isInSpanAt
    refine ⟨hbhol.mul hhB,K,fun i => (fun z => a i z*h z) ∘ Subtype.val,c,?_,hc,?_⟩
    · intro i
      have hi := (hm.2 (a i) (ha i)).2
      exact ⟨((hL _ _ (ha i)).mul hh).comp_contMDiff
        (Eventually.of_forall fun _ => hval.contMDiffAt),
        (restrictedSpan_native_iff hk hW A I hI p (fun z => a i z*h z)).mp hi⟩
    · filter_upwards [he] with q hq
      change b q*h q.val = _
      rw [hq,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [has,Function.comp_apply]
      ring
  · intro hm
    refine ⟨hh,?_⟩
    intro a ha
    have hb : (GermIdeal.pullback (m := k) (Subtype.val : W → X) L).mem p
        (a ∘ Subtype.val) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨a,ha,rfl⟩
        ((hL _ _ ha).comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt)))
    have ht := (hm.2 (a ∘ Subtype.val) hb).2
    exact ⟨(hL _ _ ha).mul hh,
      (restrictedSpan_native_iff hk hW A I hI p (fun z => a z*h z)).mpr ht⟩

/-- A native regular inclusion commutes with the ENTIRE colon along an arbitrary
intrinsic subset.  Actual coefficient extensions supply the reverse inclusion. -/
theorem pullback_native_colonAlong (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    letI := chartedSpace hk hW
    ∀ (A : Set W) (I L : GermIdeal n X)
      (_hI : ∀ z g, I.mem z g → HolomorphicAt n g z)
      (_hL : ∀ z g, L.mem z g → HolomorphicAt n g z),
      GermIdeal.pullback (m := k) (Subtype.val : W → X)
        (colonAlong n ((Subtype.val : W → X) '' A) I L) =
      colonAlong k A (GermIdeal.pullback (m := k) (Subtype.val : W → X) I)
        (GermIdeal.pullback (m := k) (Subtype.val : W → X) L) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro A I L hI hL
  have hval := contMDiff_val hk hW
  apply GermIdeal.ext
  funext p g
  apply propext
  constructor
  · intro hg
    apply colonAlong_of_span
    apply IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    exact (colonAlong_native_mem_iff hk hW A I L hI hL p a ha.1).mp ha
  · intro hg
    obtain ⟨B,hB,hEq⟩ := exists_ambient_holomorphic_germ hk hW p g hg.1
    have hBB : HolomorphicAt k (B ∘ (Subtype.val : W → X)) p :=
      hB.comp_contMDiff (Eventually.of_forall fun _ => hval.contMDiffAt)
    have hs : (colonAlong n ((Subtype.val : W → X) '' A) I L).mem p.val B := by
      apply (colonAlong_native_mem_iff hk hW A I L hI hL p B hB).mpr
      exact colonAlong_of_span (IsInSpanAt.congr' (isInSpanAt_self hg hg.1) hEq.symm)
    apply GermIdeal.mem_pullback_iff.mpr
    have hspan : IsInSpanAt (n := k)
        (fun c => ∃ a, (colonAlong n ((Subtype.val : W → X) '' A) I L).mem p.val a ∧
          c = a ∘ (Subtype.val : W → X)) p (B ∘ Subtype.val) :=
      isInSpanAt_self ⟨B,hs,rfl⟩ hBB
    exact IsInSpanAt.congr' hspan hEq

end
end Hironaka.HironakaActualNativeSectionColon
