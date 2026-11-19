import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
/-! A pointwise tangent direction from a genuine local family of derivative generators. -/
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualLocalTangentGenerators
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GermIdealOrder DerivativeIdealAlong GiraudAlong TangentDirectionAlong
open DerivativeIdealAlongCoherent RelativePrincipalizationSpan BlowupFlatCoordinates
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
 [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable {N : Set M} {I : GermIdeal n M} {x : M} {k : ℕ}

theorem orderGE_of_iterated_orderGE
 (hI : ∀ y g, I.mem y g → HolomorphicAt n g y)
 (hN : RegularAtDim (n := n) N x k) :
 ∀ (j : ℕ) {q : ℕ}, 1 ≤ q → OrderGE n N (iterDerivIdealAlong N I j) x q →
   OrderGE n N I x (q+j)
 | 0, q, _, h => by simpa only [Nat.add_zero, iterDerivIdealAlong] using h
 | j+1, q, hq, h => by
   have hd : OrderGE n N (iterDerivIdealAlong N I j) x (q+1) :=
     orderGE_succ_of_orderGE_derivIdealAlong
       (holomorphicAt_of_mem_iterDerivIdealAlong hI j) hN hq h
   have hh := orderGE_of_iterated_orderGE hI hN j (by omega : 1 ≤ q+1) hd
   simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh

theorem exists_tangent_of_local_generators
 (hhol : ∀ y g, I.mem y g → HolomorphicAt n g y)
 (hN : RegularAtDim (n := n) N x k) {d : ℕ} (hd : 1 ≤ d)
 (hx : x ∈ cosupport n N I d) (hmax : ¬ OrderGE n N I x (d+1))
 (hloc : ∃ (U : Set M), IsOpen U ∧ x ∈ U ∧
   ∃ (r : ℕ) (s : Fin r → M → ℂ),
     (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (s i) U) ∧
     ∀ y ∈ U, ∀ g, (iterDerivIdealAlong N I (d-1)).mem y g ↔
       IsInSpanAt (n := n) (· ∈ range s) y g) :
 ∃ (U : Set M) (u : M → ℂ), x ∈ U ∧ IsTangentDirectionAlong N I d U u := by
 classical
 obtain ⟨μ', rfl⟩ : ∃ μ', d = μ'+1 := ⟨d-1, by omega⟩
 have hμ : 1 ≤ μ'+1 := by omega
 have hsub : μ'+1-1 = μ' := Nat.add_sub_cancel μ' 1
 have hxN : x ∈ N := hx.1
 obtain ⟨g, hg, hgx⟩ : ∃ g, (iterDerivIdealAlong N I (μ'+1)).mem x g ∧ g x ≠ 0 := by
   by_contra hall
   push Not at hall
   apply hmax
   have hh : OrderGE n N (iterDerivIdealAlong N I (μ'+1)) x 1 := by
     intro f hf
     exact (vanishesToOrderOn_one_iff hxN
       (holomorphicAt_of_mem_iterDerivIdealAlong hhol (μ'+1) x f hf)).mpr (hall f hf)
   have hh' := orderGE_of_iterated_orderGE hhol hN (μ'+1) le_rfl hh
   simpa only [Nat.add_comm 1 (μ'+1)] using hh'
 obtain ⟨-, -, Φ, hΦsrc, hΦx, hflat⟩ := hN
 obtain ⟨U₀, hU₀o, hxU₀, r, s, hs, hgen⟩ := hloc
 simp only [hsub] at hgen
 have hOo : IsOpen (U₀ ∩ flatDomain Φ) := hU₀o.inter (isOpen_flatDomain Φ)
 have hxO : x ∈ U₀ ∩ flatDomain Φ := ⟨hxU₀, mem_flatDomain_self Φ⟩
 have hshol : ∀ i, ∀ z ∈ U₀, HolomorphicAt n (s i) z := fun i z hz =>
   eventually_of_mem (hU₀o.mem_nhds hz) fun w hw => (hs i w hw).mdifferentiableAt (hU₀o.mem_nhds hw)
 have hsmem : ∀ i, ∀ y ∈ U₀, (iterDerivIdealAlong N I μ').mem y (s i) := fun i y hy =>
   (hgen y hy (s i)).mpr (isInSpanAt_of_eq_mul ⟨i, rfl⟩ (hshol i y hy) (holomorphicAt_const 1)
     (Eventually.of_forall fun _ => (one_mul _).symm))
 have hg' := (derivIdealAlong_mem_iff_of_generators hΦsrc hflat hOo inter_subset_right
   (fun i => (hs i).mono inter_subset_left) (fun w hw => hgen w hw.1) hxO g).mp hg
 obtain ⟨-, K, t, a, ht, -, hsum⟩ := hg'
 -- some member of the generating family does not vanish at `x`
 obtain ⟨c, hc⟩ : ∃ c, derivFamilyAlong Φ k s c x ≠ 0 := by
   by_contra hall
   push Not at hall
   apply hgx
   rw [hsum.self_of_nhds]
   refine Finset.sum_eq_zero fun l _ => ?_
   obtain ⟨c, hc⟩ := ht l
   rw [← hc, hall c, mul_zero]
 rcases c with i | j | ⟨i, j⟩
 · -- a generator of `𝓓_N^{μ-1}(I)` vanishes on the cosupport
   exact absurd (apply_eq_zero_of_mem_cosupport hhol hμ hx (by rw [hsub]; exact hsmem i x hxU₀)) hc
 · -- a normal coordinate vanishes at `x`
   exfalso
   by_cases hj : k ≤ j.1
   · apply hc
     have h0 := congrArg (fun w : ComplexModel n => w j) hΦx
     simp only [derivFamilyAlong, hj, if_true, flatCoord]
     exact h0
   · exact hc (by simp [derivFamilyAlong, hj])
 · by_cases hj : j.1 < k
   swap
   · exact absurd (by simp [derivFamilyAlong, hj]) hc
   -- a tangential partial `∂sᵢ/∂ψ_j` does not vanish at `x`: take `u = sᵢ`
   have hne : flatPartial Φ j (s i) x ≠ 0 := by simpa [derivFamilyAlong, hj] using hc
   have hcont : ContinuousAt (flatPartial Φ j (s i)) x :=
     (holomorphicAt_flatPartial j (mem_flatDomain_self Φ) (hshol i x hxU₀)).self_of_nhds.continuousAt
   obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp (hcont.eventually (isOpen_ne.mem_nhds hne))
   refine ⟨V ∩ (U₀ ∩ flatDomain Φ), s i, ⟨hxV, hxO⟩, hVo.inter hOo, fun y hy => ?_, fun y hy _ => ?_⟩
   · rw [hsub]
     exact hsmem i y hy.2.1
   · exact ⟨complexChartAt (n := n) x, flatField Φ (EuclideanSpace.single j 1),
       isTangentField_flatField hΦsrc hflat (single_mem_complexCoordinatePlane hj) hy.2.2, hVsub hy.1⟩
end
end Hironaka.HironakaActualLocalTangentGenerators
