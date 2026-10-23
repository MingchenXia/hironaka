import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Properties

/-!
# Whole irreducibility from an actual open fibrewise dense locus

The native open-map/dense-good-fibre theorem avoids any supplied
dominating-component or whole-irreducibility certificate.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace DeJongAlterations.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Density on all actual residue fibres implies density in the whole scheme. -/
theorem dense_of_fiberwise_dense {T S : Scheme.{u}} (p : T ⟶ S) (U : Set T)
    (h : ∀ s : S, Dense ((p.fiberι s) ⁻¹' U)) : Dense U := by
  apply dense_iff_inter_open.mpr
  intro W hW hWne
  obtain ⟨x, hx⟩ := hWne
  let z := (p.fiberHomeo (p x)).symm ⟨x, rfl⟩
  have hz : z ∈ (p.fiberι (p x)) ⁻¹' W := by
    simpa [z] using hx
  obtain ⟨w, hwU, hwW⟩ := (h (p x)).exists_mem_open
    (hW.preimage (p.fiberι (p x)).continuous) ⟨z, hz⟩
  exact ⟨p.fiberι (p x) w, hwW, hwU⟩

/-- A genuinely open restriction with dense actual fibres determines whole irreducibility. -/
theorem irreducibleSpace_of_open_locus {T S : Scheme.{u}} [IsIntegral S]
    (p : T ⟶ S) (U : T.Opens) (hopen : IsOpenMap (fun x : U => p x))
    (hd : ∀ s : S, Dense ((p.fiberι s) ⁻¹' (U : Set T)))
    [IrreducibleSpace (p.fiber (genericPoint S))] : IrreducibleSpace T := by
  have hUd : Dense (U : Set T) := dense_of_fiberwise_dense p U hd
  let : IrreducibleSpace (p ⁻¹' {genericPoint S}) :=
    (p.fiberHomeo (genericPoint S)).irreducibleSpace_iff.mp inferInstance
  have hη : IsPreirreducible (p ⁻¹' {genericPoint S}) :=
    isPreirreducible_iff_preirreducibleSpace.mpr inferInstance
  let q : U → S := fun x => p x
  have hηU : IsPreirreducible (q ⁻¹' {genericPoint S}) :=
    hη.preimage U.isOpenEmbedding
  have hgood : (Set.univ : Set S) ⊆
      closure (Set.univ ∩ {s | IsPreirreducible (q ⁻¹' {s})}) := by
    have hs : ({genericPoint S} : Set S) ⊆
        {s | IsPreirreducible (q ⁻¹' {s})} := Set.singleton_subset_iff.mpr hηU
    have H := closure_mono hs
    rw [(genericPoint_spec S).def] at H
    simpa only [Set.univ_inter] using H
  have hUpre : IsPreirreducible (q ⁻¹' (Set.univ : Set S)) :=
    PreirreducibleSpace.isPreirreducible_univ.preimage_of_dense_isPreirreducible_fiber
      q hopen hgood
  let : PreirreducibleSpace U := ⟨by simpa only [Set.preimage_univ] using hUpre⟩
  have hUset : IsPreirreducible (U : Set T) := by
    exact isPreirreducible_iff_preirreducibleSpace.mpr (by
      change PreirreducibleSpace U
      infer_instance)
  let : PreirreducibleSpace T := ⟨hUd.closure_eq ▸ hUset.closure⟩
  let : Nonempty T := Nonempty.map (p.fiberι (genericPoint S)) inferInstance
  exact ⟨inferInstance⟩

end DeJongAlterations.Geometry.CurveFibrationBaseChange
