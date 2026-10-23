/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Curves.Basic
import DeJongAlterations.StableModification.CurvesField.StableDownGeometricGraph

/-!
# Topology of curves and their contracted fibres (Temkin, proof of Lemma 4.4.2)

Topological glue for the stability criterion (M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), `references/temkin10-stable-modification/source/semi-stable.tex`,
Lemma 4.4.2, T:3106–3133; blueprint `lem:sm-stability-criterion`, chapter
`sm-blow-down-criterion.tex`): the fibres of the curves over `V` are quasi-sober `T₀` spaces of
dimension at most one, the contracted fibres `Z = f⁻¹(x)` are connected, and a connected `Z`
containing a component of the curve is a union of components (Temkin's "`Z` is a curve").

## Main results

* `topologicalKrullDim_le_one_of_forall_irreducibleComponents`: a quasi-sober `T₀` space whose
  irreducible components have dimension at most one has dimension at most one.
* `not_mem_genericPoints_of_isClosed`: in a space whose irreducible components have dimension one,
  a closed point is not a generic point.
* `isConnected_preimage_of_isEmbedding`: connectedness of a subset of the range of an embedding
  pulls back.
* `exists_mem_genericPoints_of_isConnected`: in a Noetherian space of dimension at most one, a
  connected closed subset containing a generic point is the union of the closures of the generic
  points it contains.
-/

namespace DeJongAlterations.StableModification.BlowDown

open Topology TopologicalSpace

universe u v

section Dimension

variable {T : Type u} [TopologicalSpace T] [QuasiSober T] [T0Space T]

/-- **Krull dimension at most one through specializations**: a quasi-sober `T₀` space has
dimension at most one iff every point is closed under specialization up to inseparability or has
no proper generization. -/
theorem topologicalKrullDim_le_one_iff_specializes :
    topologicalKrullDim T ≤ 1 ↔
      ∀ x : T, (∀ a, x ⤳ a → a ⤳ x) ∨ (∀ b, b ⤳ x → x ⤳ b) := by
  let := specializationOrder T
  rw [Curves.topologicalKrullDim_eq_krullDim, Order.krullDim_le_one_iff]
  exact Iff.rfl

/-- **Dimension of a curve from its components**: if every irreducible component of the
quasi-sober `T₀` space `T` has dimension at most one, so has `T` (a chain `b ⤳ x ⤳ a` of proper
specializations lies in the irreducible component of `b`). -/
theorem topologicalKrullDim_le_one_of_forall_irreducibleComponents
    (h : ∀ W ∈ irreducibleComponents T, topologicalKrullDim W ≤ 1) :
    topologicalKrullDim T ≤ 1 := by
  rw [topologicalKrullDim_le_one_iff_specializes]
  intro x
  by_contra hx
  push Not at hx
  obtain ⟨⟨a, hxa, hax⟩, ⟨b, hbx, hxb⟩⟩ := hx
  let W := irreducibleComponent b
  have hW : W ∈ irreducibleComponents T := irreducibleComponent_mem_irreducibleComponents b
  have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
  have hbW : b ∈ W := mem_irreducibleComponent
  have hxW : x ∈ W := hbx.mem_closed hWc hbW
  have haW : a ∈ W := hxa.mem_closed hWc hxW
  have : QuasiSober W := hWc.isClosedEmbedding_subtypeVal.quasiSober
  have hdimW := (topologicalKrullDim_le_one_iff_specializes (T := W)).1 (h W hW) ⟨x, hxW⟩
  have hind : IsInducing (Subtype.val : W → T) := IsInducing.subtypeVal
  rcases hdimW with hm | hM
  · exact hax (hind.specializes_iff.2 (hm ⟨a, haW⟩ (hind.specializes_iff.1 hxa)))
  · exact hxb (hind.specializes_iff.2 (hM ⟨b, hbW⟩ (hind.specializes_iff.1 hbx)))

omit [QuasiSober T] [T0Space T] in
/-- **No isolated points**: if every irreducible component has dimension one, a closed point is not
a generic point (its closure would be a component of dimension zero). -/
theorem not_mem_genericPoints_of_isClosed
    (h : ∀ W ∈ irreducibleComponents T, topologicalKrullDim W = 1) {x : T}
    (hx : IsClosed ({x} : Set T)) : x ∉ genericPoints T := by
  intro hg
  have hcomp : closure {x} ∈ irreducibleComponents T := hg
  rw [hx.closure_eq] at hcomp
  have h1 := h {x} hcomp
  have : Subsingleton ({x} : Set T) := Set.subsingleton_singleton.coe_sort
  have h0 := topologicalKrullDim_zero_of_discreteTopology ({x} : Set T)
  rw [h1] at h0
  exact absurd h0 (by decide)

end Dimension

section Connected

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Connectedness pulls back along an embedding** for subsets of its range. -/
theorem isConnected_preimage_of_isEmbedding {e : Y → X} (he : IsEmbedding e) {A : Set X}
    (hA : A ⊆ Set.range e) (h : _root_.IsConnected A) : _root_.IsConnected (e ⁻¹' A) := by
  have himage : e '' (e ⁻¹' A) = A := Set.image_preimage_eq_of_subset hA
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := h.nonempty
    obtain ⟨y, rfl⟩ := hA ha
    exact ⟨y, ha⟩
  · rw [← he.isInducing.isPreconnected_image, himage]
    exact h.isPreconnected

end Connected

section Curve

variable {T : Type u} [TopologicalSpace T] [QuasiSober T] [T0Space T] [NoetherianSpace T]

/-- **A connected subcurve is a union of components** (Temkin's "`Z` is a curve", T:3106–3109):
in a Noetherian quasi-sober `T₀` space of dimension at most one, a closed connected set `Z`
containing a generic point is the union of the closures of the generic points it contains. The
points of `Z` on no such component form a finite set of closed points (they lie on components not
contained in `Z`, which meet `Z` in finitely many points), closed and open in `Z`. -/
theorem exists_mem_genericPoints_of_isConnected (hdim : topologicalKrullDim T ≤ 1) {Z : Set T}
    (hZc : IsClosed Z) (hZ : _root_.IsConnected Z) (hv : ∃ v ∈ Z, v ∈ genericPoints T) :
    ∀ z ∈ Z, ∃ v ∈ Z, v ∈ genericPoints T ∧ z ∈ closure {v} := by
  have hfin : (genericPoints T).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  -- the components in `Z` and the components meeting `Z` but not contained in it
  set A := ⋃ v ∈ {v | v ∈ Z ∧ v ∈ genericPoints T}, closure ({v} : Set T) with hA
  set F := Z ∩ ⋃ w ∈ {w | w ∉ Z ∧ w ∈ genericPoints T}, closure ({w} : Set T) with hF
  have hAc : IsClosed A :=
    (hfin.subset fun _ h => h.2).isClosed_biUnion fun _ _ => isClosed_closure
  have hFc : IsClosed F :=
    hZc.inter ((hfin.subset fun _ h => h.2).isClosed_biUnion fun _ _ => isClosed_closure)
  have hFfin : F.Finite := by
    refine CurvesField.Genus.finite_of_isClosed_of_disjoint_genericPoints hdim hFc
      fun η hη hgen => ?_
    obtain ⟨hηZ, hη'⟩ := hη
    obtain ⟨w, ⟨hwZ, hwg⟩, hηw⟩ := Set.mem_iUnion₂.1 hη'
    have := (CurvesField.Genus.mem_genericPoints_iff η).1 hgen w (specializes_iff_mem_closure.2 hηw)
    exact hwZ (this ▸ hηZ)
  -- every point of `Z` is in `A` or in `F`
  have hcov : Z ⊆ A ∪ F := by
    intro z hz
    let c : irreducibleComponents T :=
      ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
    let w := (genericPoints.ofComponent c).1
    have hwg : w ∈ genericPoints T := (genericPoints.ofComponent c).2
    have hzw : z ∈ closure {w} := by
      rw [(genericPoints.isGenericPoint_ofComponent c).def]
      exact mem_irreducibleComponent
    by_cases hwZ : w ∈ Z
    · exact Or.inl (Set.mem_biUnion (x := w) ⟨hwZ, hwg⟩ hzw)
    · exact Or.inr ⟨hz, Set.mem_biUnion (x := w) ⟨hwZ, hwg⟩ hzw⟩
  -- the finite set `F ∖ A` of closed points is closed
  have hB : IsClosed (F \ A) := by
    rw [← Set.biUnion_of_singleton (F \ A)]
    refine (hFfin.subset Set.sdiff_subset).isClosed_biUnion fun z hz => ?_
    have hzg : z ∉ genericPoints T := fun hg => hz.2 (Set.mem_biUnion (x := z) ⟨hz.1.1, hg⟩
      (subset_closure rfl))
    have : CompactSpace T := NoetherianSpace.compactSpace T
    exact CurvesField.Genus.isClosed_singleton_of_not_mem_genericPoints hdim hzg
  obtain ⟨v, hvZ, hvg⟩ := hv
  have hvA : v ∈ A := Set.mem_biUnion (x := v) ⟨hvZ, hvg⟩ (subset_closure rfl)
  have hsub : Z ⊆ A := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hZ.isPreconnected A (F \ A) hAc hB
        (fun z hz => by
          rcases hcov hz with h | h
          · exact Or.inl h
          · by_cases hzA : z ∈ A
            · exact Or.inl hzA
            · exact Or.inr ⟨h, hzA⟩)
        (by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro z ⟨-, hzA, -, hzA'⟩
          exact hzA' hzA) with h | h
    · exact h
    · exact absurd (h hvZ).2 (not_not.2 hvA)
  intro z hz
  obtain ⟨w, ⟨hwZ, hwg⟩, hzw⟩ := Set.mem_iUnion₂.1 (hsub hz)
  exact ⟨w, hwZ, hwg, hzw⟩

end Curve

end DeJongAlterations.StableModification.BlowDown
