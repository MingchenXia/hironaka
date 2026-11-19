import Hironaka.Resolution.HironakaG10FiniteIdealFamilyArithmetic
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Uniform powers from pointwise radical containment -/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10UniformRadicalPower

open Hironaka.HironakaG10HirIdealGerms
  Hironaka.HironakaG10FiniteIdealFamilyArithmetic

/-- Coherent stalk families with pointwise radical containment on a compact
  set admit one power inclusion on an open neighborhood of the whole set. -/
theorem exists_uniform_power_on_compact {X : LocallyRingedSpace.{0}}
    (V K : Set X) (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (I J : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hI : IsLocallyFinitelyGeneratedOn X V I) (hJ : IsLocallyFinitelyGeneratedOn X V J)
    (hrad : ∀ x ∈ K, I x ≤ (J x).radical) :
    ∃ (W : Set X) (N : ℕ), IsOpen W ∧ K ⊆ W ∧ W ⊆ V ∧
      ∀ y ∈ W, ∀ n ≥ N, I y ^ n ≤ J y := by
  classical
  have hloc : ∀ x ∈ K, ∃ U ∈ 𝓝 x, ∃ n : ℕ, U ⊆ V ∧ ∀ y ∈ U, I y ^ n ≤ J y := by
    intro x hx
    have hxV := hKV hx
    obtain ⟨O,hxO,r,s,hs⟩ := hI x hxV
    have hfg : (I x).FG := by
      rw [hs x hxO hxV]
      exact Submodule.fg_span (Set.finite_range _)
    obtain ⟨n,hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (hrad x hx) hfg
    have hev := eventually_le_of_le (isLocallyFinitelyGeneratedOn_pow V I hI n) hJ
      hV hV hxV hxV hn
    refine ⟨{y | I y ^ n ≤ J y} ∩ V, inter_mem hev (hV.mem_nhds hxV), n, inter_subset_right, ?_⟩
    exact fun _ hy => hy.1
  choose U hU n hn using hloc
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun p : K => interior (U p.1 p.2))
    (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,mem_interior_iff_mem_nhds.mpr (hU x hx)⟩)
  refine ⟨⋃ p ∈ s, interior (U p.1 p.2), s.sup fun p => n p.1 p.2,
    isOpen_biUnion fun _ _ => isOpen_interior, hs, ?_, ?_⟩
  · intro y hy
    obtain ⟨p,hp,hyU⟩ := mem_iUnion₂.mp hy
    exact (hn p.1 p.2).1 (interior_subset hyU)
  · intro y hy m hm
    obtain ⟨p,hp,hyU⟩ := mem_iUnion₂.mp hy
    have hnm : n p.1 p.2 ≤ m := (Finset.le_sup (f := fun p : K => n p.1 p.2) hp).trans hm
    exact (Ideal.pow_le_pow_right hnm).trans ((hn p.1 p.2).2 y (interior_subset hyU))

end Hironaka.Analytic.Unibranch.HironakaG10UniformRadicalPower
