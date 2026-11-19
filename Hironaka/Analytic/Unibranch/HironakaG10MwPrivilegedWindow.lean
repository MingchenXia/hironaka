import Hironaka.Resolution.HironakaG10FlatPrivilegedEuclidean

/-!
# A privileged nested window inside any neighbourhood (G10-01-06, lane G10MW, run 0081)

For a finite matrix `F` holomorphic near a point `x` of `ℂ^t` and ANY neighbourhood `N` of `x`, there are
two compact windows `K₁ ⊆ interior K₀ ⊆ K₀ ⊆ N`, `K₁` a closed polydisc neighbourhood of `x`, and a
relation matrix `G₀` holomorphic on `interior K₀` with `F G₀ = 0` there, such that the restricted
`B(K₁)` start `(G₀, F)` is directly exact.  This is exactly the window input of the same-window Schur
family (`HironakaG10SameWindowOneFamily`), for the fibre module of an actual chart.

Source: Douady 1966 §7 Th. 1 (privileged neighbourhoods), through
`HironakaG10FlatPrivilegedEuclidean.privilegedNbhdsProperty_euclidean` (a neighbourhood-basis statement).
`K₀` is a closed metric thickening of `K₁`.  No named input.
-/

set_option autoImplicit false
open Set Filter Metric
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10MwPrivilegedWindow

noncomputable section

open Hironaka Hironaka OkaRelationSheaf
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart HironakaG10FlatPrivilegedNbhd
  HironakaG10FlatPrivilegedEuclidean

/-- **A privileged nested window inside a prescribed neighbourhood.** -/
theorem exists_privileged_window (t : ℕ) {a b : ℕ} (F : Fin a → Fin b → ComplexModel t → ℂ)
    (x : ComplexModel t) (hF : ∀ i j, HolAt (F i j) x) (N : Set (ComplexModel t)) (hN : N ∈ 𝓝 x) :
    ∃ (K₀ K₁ : Set (ComplexModel t)) (_ : IsCompact K₀) (hK₁ : IsCompact K₁),
      K₁ ∈ closedPolydiscs t ∧ K₁ ∈ 𝓝 x ∧ K₀ ⊆ N ∧ ∃ hK₁₀ : K₁ ⊆ interior K₀,
      ∃ (c : ℕ) (G₀ : Fin b → Fin c → ComplexModel t → ℂ)
        (hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) (interior K₀))
        (hF₀ : ∀ i j, DifferentiableOn ℂ (F i j) (interior K₀)),
        (∀ z ∈ interior K₀, ∀ i l, ∑ j, F i j z * G₀ j l z = 0) ∧
        let : CompactSpace K₁ := isCompact_iff_compactSpace.mp hK₁
        DirectExact (restrictMatrix K₁ hK₁₀ G₀ hG₀) (restrictMatrix K₁ hK₁₀ F hF₀) := by
  have hp := privilegedNbhdsProperty_euclidean t Unit (fun _ => a) (fun _ => b) (fun _ => F) x
    (fun _ => hF)
  obtain ⟨U, m, s, d, hres, hU, hxU, hfirst, hneigh⟩ := hp
  have hN' : interior N ∩ U ∈ 𝓝 x := inter_mem (interior_mem_nhds.mpr hN) (hU.mem_nhds hxU)
  obtain ⟨K, hK, hKN, hKU, hKc, hKn, _, hpriv⟩ := hneigh (interior N ∩ U) hN'
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open (isOpen_interior.inter hU) hKN
  have hδ2 : 0 < δ / 2 := half_pos hδ
  let K₀ : Set (ComplexModel t) := cthickening (δ / 2) K
  have hK₀c : IsCompact K₀ := hKc.cthickening
  have hK₀sub : K₀ ⊆ interior N ∩ U :=
    (cthickening_subset_thickening' hδ (half_lt_self hδ) K).trans hthick
  have hK₁₀ : K ⊆ interior K₀ :=
    (self_subset_thickening hδ2 K).trans
      (interior_maximal (thickening_subset_cthickening (δ / 2) K) isOpen_thickening)
  have hK₀N : K₀ ⊆ N := fun z hz => interior_subset (hK₀sub hz).1
  have hK₀U : interior K₀ ⊆ U := fun z hz => (hK₀sub (interior_subset hz)).2
  have hd0 : d () 0 = F := hfirst ()
  have hF₀ : ∀ i j, DifferentiableOn ℂ (F i j) (interior K₀) := by
    rw [← hd0]
    exact fun i j => ((hres ()).hol 0 i j).mono hK₀U
  let G₀ := d () 1
  have hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) (interior K₀) :=
    fun j l => ((hres ()).hol 1 j l).mono hK₀U
  have hcomp : ∀ z ∈ interior K₀, ∀ i l, ∑ j, F i j z * G₀ j l z = 0 := by
    intro z hz i l
    rw [← hd0]
    exact ((hres ()).exact 0 (hres ()).pos).comp i l z (hK₀U hz)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hex0 := hpriv () 0 (hres ()).pos
  refine ⟨K₀, K, hK₀c, hKc, hK, hKn, hK₀N, hK₁₀, _, G₀, hG₀, hF₀, hcomp, ?_⟩
  have hFU : ∀ i j, DifferentiableOn ℂ (F i j) U := by
    rw [← hd0]
    exact (hres ()).hol 0
  have hrestrict : restrictMatrix K hKU (d () 0) ((hres ()).hol 0) =
      restrictMatrix K hKU F hFU := by
    funext i j
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    change d () 0 i j z = F i j z
    rw [hd0]
  rw [hrestrict] at hex0
  exact hex0

end

end Hironaka.Analytic.Unibranch.HironakaG10MwPrivilegedWindow
