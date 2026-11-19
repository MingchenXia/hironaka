import Hironaka.Analytic.Unibranch.HironakaG10GfRegularChart
import Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
import Hironaka.Resolution.HironakaActualCylinderVanishingIdealExtension

/-!
# Relatively exact starts are exact starts modulo the vanishing ideal (lane G10GF, run 0081, G10-03-05.c2'')

The comparison "(1c)" of lane G10TM's item 1 (`work/hironaka-run0081-20261117/G10TM/STATUS.md`): for a parameter
SET `T ⊆ ℂᵈ` and a point `p = (s, z)` with `s ∈ T`, write `I_T` for the ideal of germs at `s` (translated to the
origin) vanishing on `T`.  Then

* **`germAt_mem_map_basePullback`** (the cylinder identity at a point): a germ at `p` of a function vanishing on
  `T × ℂᵗ` lies in the extension `I_T · 𝒪_{d+t,p}`; this is the library's
  `HironakaActualCylinderVanishingIdealExtension.cylinder_vanishingIdeal_eq_base_extension` (Hadamard division
  + Nakayama, no smoothness of `T`) read on product germs;
* `eventually_eq_zero_of_mem_map_basePullback`: conversely, germs of `I_T · 𝒪_{d+t,p}` vanish on `T × ℂᵗ`;
* **`exactStartMod_of_relExactStartOn`**: a relatively exact start `(G, F)` over `T` (library
  `HironakaG10LocRelative.RelExactStartOn`) is an exact start of `F` modulo `I_T · 𝒪` at `p`, in exactly the form
  of `ExactStartModAt` of lane G10LF's item (1b) (`F G ≡ 0` and every relation modulo `I_T` is a combination of
  the columns of `G` modulo `I_T`);
* `vanishingIdeal_le_maximalIdeal`: `I_T` is proper (`s ∈ T`).

So flatness over `T` in the relative Tor₁ form (`RelFibreFlatAt T F p`) yields the fibre exactness of a start
modulo `I_T`, the hypothesis of the chart local criterion (1b).  No named input.
Blueprint: `hironaka-g10gf-relative.tex`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GfModStart

noncomputable section

open Hironaka Hironaka OkaRelationSheaf OkaGermBridge
  HironakaG10LocRelative HironakaRelativeNormalIdeal HironakaActualCylinderRelativeHadamard
  HironakaActualCylinderVanishingIdealExtension AnalyticGermDecomposition
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen

variable {d t : ℕ}

/-- The ideal of germs at `s` (translated to the origin) vanishing on `T`. -/
abbrev baseIdeal (T : Set (ComplexModel d)) (s : ComplexModel d) : Ideal (HolGerm (ComplexModel d)) :=
  vanishingIdeal {w : ComplexModel d | s + w ∈ T}

/-- **The cylinder identity at a point**: germs of functions vanishing on `T × ℂᵗ` lie in `I_T · 𝒪`. -/
theorem germAt_mem_map_basePullback {T : Set (ComplexModel d)} {p : ComplexModel d × ComplexModel t}
    {h : ComplexModel d × ComplexModel t → ℂ} (hh : HolAt h p)
    (hvan : ∀ᶠ q in 𝓝 p, q.1 ∈ T → h q = 0) :
    germAt p h ∈ (baseIdeal T p.1).map (basePullback d t) := by
  set W : Set (ComplexModel d) := {w : ComplexModel d | p.1 + w ∈ T} with hWdef
  let φ : ComplexModel (d + t) → ComplexModel d × ComplexModel t := fun w => p + splitModel d t w
  have hφc : Continuous φ := continuous_const.add (splitModel d t).continuous
  have hφd : ∀ w, DifferentiableAt ℂ φ w := fun w =>
    (differentiableAt_const p).add (splitModel d t).differentiableAt
  have hφ0 : φ 0 = p := by simp [φ]
  have hhol : HolAt (h ∘ φ) 0 := HolAt.comp (by rw [hφ0]; exact hh) hφc hφd
  let g : HolGerm (ComplexModel (d + t)) := HolGerm.mk (h ∘ φ) hhol
  have hg : g ∈ vanishingIdeal (cylinderCarrier d t W) := by
    apply mem_vanishingIdeal_mk.2
    have ht : Tendsto φ (𝓝 0) (𝓝 p) := by
      have := hφc.tendsto 0
      rwa [hφ0] at this
    filter_upwards [ht.eventually hvan] with w hw hwC
    apply hw
    change p.1 + (splitModel d t w).1 ∈ T
    rw [splitModel_fst]
    exact hwC
  rw [cylinder_vanishingIdeal_eq_base_extension] at hg
  have hmap := Ideal.mem_map_of_mem (ambientGermEquiv d t).toRingHom hg
  rw [Ideal.map_map] at hmap
  have hcomp : (ambientGermEquiv d t).toRingHom.comp (tangentPullback d t).toRingHom =
      basePullback d t :=
    RingHom.ext fun a => ambientGermEquiv_tangentPullback d t a
  rw [hcomp] at hmap
  have hg' : (ambientGermEquiv d t).toRingHom g = germAt p h := by
    rw [germAt_of_holAt hh]
    change HolGerm.comapEquiv (splitModel d t).symm (HolGerm.mk (h ∘ φ) hhol) = _
    rw [HolGerm.comapEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.2
    filter_upwards with v
    simp [φ]
  rw [← hg']
  exact hmap

/-- Germs of the extended base ideal vanish on `T × ℂᵗ`. -/
theorem map_basePullback_le (W : Set (ComplexModel d)) :
    (vanishingIdeal W).map (basePullback d t) ≤
      vanishingIdeal {v : ComplexModel d × ComplexModel t | v.1 ∈ W} := by
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
  rw [Ideal.mem_comap, basePullback, HolGerm.comap_mk]
  apply mem_vanishingIdeal_mk.2
  have ht : Tendsto (fun v : ComplexModel d × ComplexModel t => v.1) (𝓝 0) (𝓝 0) :=
    continuous_fst.tendsto' 0 0 rfl
  filter_upwards [ht.eventually (mem_vanishingIdeal_mk.1 hg)] with v hv hvW
  exact hv hvW

/-- Conversely, a germ at `p` of the extended base ideal comes from a function vanishing on `T × ℂᵗ`. -/
theorem eventually_eq_zero_of_mem_map_basePullback {T : Set (ComplexModel d)}
    {p : ComplexModel d × ComplexModel t} {h : ComplexModel d × ComplexModel t → ℂ} (hh : HolAt h p)
    (hmem : germAt p h ∈ (baseIdeal T p.1).map (basePullback d t)) :
    ∀ᶠ q in 𝓝 p, q.1 ∈ T → h q = 0 := by
  have h1 := map_basePullback_le (t := t) {w : ComplexModel d | p.1 + w ∈ T} hmem
  rw [germAt_of_holAt hh] at h1
  have h2 := mem_vanishingIdeal_mk.1 h1
  rw [eventually_nhds_iff_translate (p := fun q : ComplexModel d × ComplexModel t => q.1 ∈ T → h q = 0) p]
  filter_upwards [h2] with v hv hvT
  exact hv hvT

/-- The base ideal at a point of `T` is proper. -/
theorem baseIdeal_le_maximalIdeal {T : Set (ComplexModel d)} {s : ComplexModel d} (hs : s ∈ T) :
    baseIdeal T s ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
  rw [HolGerm.mem_maximalIdeal_iff, HolGerm.eval_mk]
  have := (mem_vanishingIdeal_mk.1 hg).self_of_nhds
  exact this (by simpa using hs)

/-- **A relatively exact start over `T` is an exact start modulo `I_T · 𝒪` at `p`** (the form of lane G10LF's
`ExactStartModAt`). -/
theorem exactStartMod_of_relExactStartOn {T : Set (ComplexModel d)} {a b c : ℕ}
    {W : Set (ComplexModel d × ComplexModel t)} {G : Fin b → Fin c → ComplexModel d × ComplexModel t → ℂ}
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ} (h : RelExactStartOn T W G F)
    (hW : IsOpen W) {p : ComplexModel d × ComplexModel t} (hpW : p ∈ W) (hpT : p.1 ∈ T) :
    (∀ i k, ∑ j, germAt p (F i j) * germAt p (G j k) ∈ (baseIdeal T p.1).map (basePullback d t)) ∧
    ∀ v : Fin b → HolGerm (ComplexModel d × ComplexModel t),
      (∀ i, ∑ j, germAt p (F i j) * v j ∈ (baseIdeal T p.1).map (basePullback d t)) →
        ∃ w : Fin c → HolGerm (ComplexModel d × ComplexModel t),
          ∀ j, v j - ∑ k, germAt p (G j k) * w k ∈ (baseIdeal T p.1).map (basePullback d t) := by
  have hF : ∀ i j, HolAt (F i j) p := fun i j => holAt_of_differentiableOn hW (h.holA i j) hpW
  have hG : ∀ j k, HolAt (G j k) p := fun j k => holAt_of_differentiableOn hW (h.holG j k) hpW
  refine ⟨fun i k => ?_, fun v hv => ?_⟩
  · -- `F G` vanishes on `T × ℂᵗ`
    have hsum : HolAt (fun q => ∑ j, F i j q * G j k q) p :=
      HolAt.fintype_sum fun j => (hF i j).mul (hG j k)
    have e : ∑ j, germAt p (F i j) * germAt p (G j k) = germAt p (fun q => ∑ j, F i j q * G j k q) := by
      rw [germAt_sum Finset.univ fun j _ => (hF i j).mul (hG j k)]
      exact Finset.sum_congr rfl fun j _ => (germAt_mul (hF i j) (hG j k)).symm
    rw [e]
    apply germAt_mem_map_basePullback hsum
    filter_upwards [hW.mem_nhds hpW] with q hq hqT
    exact h.comp i k q hq hqT
  · -- a relation modulo `I_T` is a relation over `T`
    choose vf hvf hvfe using fun j => exists_germAt_eq (v j) p
    have hrelhol : ∀ i, HolAt (fun q => ∑ j, vf j q * F i j q) p := fun i =>
      HolAt.fintype_sum fun j => (hvf j).mul (hF i j)
    have hrel : ∀ i, ∀ᶠ q in 𝓝 p, q.1 ∈ T → ∑ j, vf j q * F i j q = 0 := by
      intro i
      apply eventually_eq_zero_of_mem_map_basePullback (hrelhol i)
      have e : germAt p (fun q => ∑ j, vf j q * F i j q) = ∑ j, germAt p (F i j) * v j := by
        rw [germAt_sum Finset.univ fun j _ => (hvf j).mul (hF i j)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [germAt_mul (hvf j) (hF i j), hvfe j, mul_comm]
      rw [e]
      exact hv i
    obtain ⟨cf, hcf, hcfe⟩ := h.exact p hpW hpT vf hvf hrel
    refine ⟨fun k => germAt p (cf k), fun j => ?_⟩
    have hdiff : HolAt (fun q => vf j q - ∑ k, cf k q * G j k q) p :=
      (hvf j).sub (HolAt.fintype_sum fun k => (hcf k).mul (hG j k))
    have e : v j - ∑ k, germAt p (G j k) * germAt p (cf k) =
        germAt p (fun q => vf j q - ∑ k, cf k q * G j k q) := by
      rw [germAt_of_holAt hdiff, ← hvfe j, germAt_of_holAt (hvf j)]
      rw [show (∑ k, germAt p (G j k) * germAt p (cf k)) =
          germAt p (fun q => ∑ k, cf k q * G j k q) by
        rw [germAt_sum Finset.univ fun k _ => (hcf k).mul (hG j k)]
        exact Finset.sum_congr rfl fun k _ => by rw [germAt_mul (hcf k) (hG j k), mul_comm]]
      rw [germAt_of_holAt (HolAt.fintype_sum fun k => (hcf k).mul (hG j k)), ← HolGerm.mk_sub]
    rw [e]
    apply germAt_mem_map_basePullback hdiff
    filter_upwards [hcfe j] with q hq hqT
    rw [hq hqT, sub_self]

end

end Hironaka.Analytic.Unibranch.HironakaG10GfModStart
