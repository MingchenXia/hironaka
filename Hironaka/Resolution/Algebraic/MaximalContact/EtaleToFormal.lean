/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquiv
public import Hironaka.Resolution.Algebraic.MaximalContact.FormalEquiv
public import Hironaka.Scheme.Smooth.GraphFormal
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.Smooth.GraphCompletion
import Hironaka.Scheme.Smooth.SubschemeStalk

/-!
# From étale equivalence to formal equivalence

[Kol07, Definition 91] ends by noting that `ψ` is invertible after completion, so that
"`φ := ψ̂' ∘ ψ̂⁻¹ : X̂ → X̂` is the automorphism we seek". This file proves the statement behind
that sentence: if `ψ(u) = ψ'(u) = p` with `ψ, ψ'` étale and
trivial residue field extensions at `u`, then `ψ̂, ψ̂' : Ô_{p,X} → Ô_{u,U}` are isomorphisms and `φ`
is a formal equivalence at `p` whenever (1′)–(4′) hold on a neighbourhood of `u`.

**The setting.** A point `u ∈ U` over `p` along both maps with `κ(u) = κ(p)` is an
`EtaleNbhdPair X p` (`W := U`, `q := u`); its `stalkHom`, `stalkHom'` are the local homomorphisms
`ψ^*, ψ'^* : 𝒪_{X,p} → 𝒪_{U,u}`, whose completions `ψ̂, ψ̂'` are bijective
(`bijective_completionMap_stalkHom`). On functions Kollár's `φ` is the `k`-algebra automorphism
`φ^* := ψ̂⁻¹ ∘ ψ̂'` of `Ô_{X,p}`, the inverse of `formalAutomorphism = ψ̂'⁻¹ ∘ ψ̂`, so that (91.1)
reads `φ^*(Ĥ') = Ĥ` exactly from (1′) `ψ⁻¹(H) = ψ'⁻¹(H')`.

* **(91.1)–(91.3)** are transports of ideals: `map_completionMap_stalkHom` gives
  `ψ̂(Ĵ) = (ψ^*J)^` for every ideal sheaf `J` (and the same for `ψ'`), so
  `φ^*(Ĵ') = ψ̂⁻¹(ψ̂'(Ĵ')) = ψ̂⁻¹((ψ'^*J')^) = ψ̂⁻¹((ψ^*J)^) = Ĵ` whenever `ψ^*J = ψ'^*J'`
  (`map_formalAutomorphism_symm_completionIdeal`, applied to (1′), (2′), (3′)).
* **`k`-linearity.** `ψ ≫ f = ψ' ≫ f` (Kollár's maps of `k`-varieties, the field `comp_eq` of
  `EtaleEquiv`): `ψ^*` and `ψ'^*` both carry the `k`-structure of `𝒪_{X,p}` induced by `f` to the
  one of `𝒪_{U,u}` induced by `ψ ≫ f = ψ' ≫ f` (`stalkHom_algebraMap`), so `ψ̂'(c) = ψ̂(c)` for
  `c ∈ k` and `φ^*` fixes `k` (`formalAutomorphism_symm_algebraMap`).
* **(91.4)** is the substance. By [Kol07, Lemma 74 (4)] `MC(ψ^*I) = ψ^*MC(I)`
  (`MC_comap_of_etale`), so (4′) says `ψ ∘ ι = ψ' ∘ ι` on `V(M)` for `M := ψ^*MC(I)`, and we need
  `ĥ − φ^*ĥ ∈ MC(I)^` for every `ĥ ∈ Ô_{X,p}`, i.e. (applying the injective `ψ̂` and the
  transport) `ψ̂ĥ − ψ̂'ĥ ∈ M̂ := M_u Ô_{U,u}`.
  - *Stalk step* (Kollár's own reading of (4′), "`ψ^*(h) − ψ'^*(h) ∈ MC ψ^*(I)`"): for
    `a ∈ 𝒪_{X,p}`, `ψ^*a − ψ'^*a ∈ M_u`. If `u ∉ V(M)` then `M_u = 𝒪_{U,u}`; otherwise `u = ι(z)`,
    the kernel of `ι^* : 𝒪_{U,u} → 𝒪_{V(M),z}` is `M_u` (`ker_stalkMap_subschemeι`), and on a
    section `s` representing `a`, `ι^*ψ^*s = (ψ ∘ ι)^*s = (ψ' ∘ ι)^*s = ι^*ψ'^*s`
    (`germ_app_sub_germ_app_mem_stalkIdeal`).
  - *Completion step* (not in the sources): `ĥ` agrees with some `a ∈ 𝒪_{X,p}` to order `n`
    (`ĥ − a ∈ 𝔪̂ⁿ`; `Ô = lim 𝒪/𝔪ⁿ`, [Kol07, Definition 55]), and `ψ̂, ψ̂'` preserve the powers of
    the maximal ideals, so `ψ̂ĥ − ψ̂'ĥ ∈ M̂ + 𝔪̂_Uⁿ` for every `n`. The ideal `M̂ = M_u Ô_{U,u}` is
    closed in the `𝔪̂`-adic topology of the completion of the Noetherian local ring `𝒪_{U,u}`, the
    Krull-intersection remark of [Kol07, Definition 55] in the form: completion is exact on finite
    modules (Artin–Rees, Mathlib's `AdicCompletion.map_exact`), so `M̂` is the kernel of
    `Ô_{U,u} → (𝒪_{U,u}/M_u)^`, and the target is Hausdorff
    (`mem_map_algebraMap_adicCompletion_of_forall`).

Two forms are proved: `formallyEquivalentAt_of_etaleNbhdPair`, the neighbourhood form on an
`EtaleNbhdPair` with (1′)–(4′) (the graph neighbourhood `U₁(p)` in the proof of Theorem 92 is
such a pair and need not cover the cosupport), and `formallyEquivalentAt_of_etaleEquiv` for an
étale equivalence `Q : EtaleEquiv f I m E H H'` and a point `u ∈ U` over `p`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IsLocalRing

namespace Hironaka.Local

open IsLocalRing

section Closedness

variable {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]

local notation "Ŝ" => AdicCompletion (maximalIdeal S) S

/-- `Ô = lim 𝒪/𝔪ⁿ` ([Kol07, Definition 55]): every element of the completion `Ŝ` of a Noetherian
local ring agrees with an element of `S` to any prescribed order, `x − a ∈ 𝔪̂ⁿ`. -/
theorem exists_sub_algebraMap_mem_maximalIdeal_pow (x : Ŝ) (n : ℕ) :
    ∃ a : S, x - algebraMap S Ŝ a ∈ maximalIdeal Ŝ ^ n := by
  obtain ⟨a, ha⟩ :=
    Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal S) S n x)
  refine ⟨a, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem S,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal S).fg_of_isNoetherianRing,
    LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply,
    AdicCompletion.eval_of, Submodule.mkQ_apply, ha, sub_self]

/-- The Krull-intersection remark of [Kol07, Definition 55]: the extension `JŜ` of an ideal `J` of
a Noetherian local ring `S` to the completion `Ŝ` is closed, i.e. an element of `Ŝ` lying in
`JŜ + 𝔪̂ⁿ` for every `n` lies in `JŜ`. Proof: completion is exact on finitely generated modules
(Artin–Rees, Mathlib's `AdicCompletion.map_exact`), so `JŜ` (the image of the completion of `J`,
`range_adicCompletion_map_subtype`) is the kernel of `Ŝ → (S/J)^`, and `(S/J)^` is `𝔪`-adically
Hausdorff. -/
theorem mem_map_algebraMap_adicCompletion_of_forall (J : Ideal S) (x : Ŝ)
    (hx : ∀ n : ℕ, ∃ y ∈ J.map (algebraMap S Ŝ), x - y ∈ maximalIdeal Ŝ ^ n) :
    x ∈ J.map (algebraMap S Ŝ) := by
  have hex : Function.Exact (AdicCompletion.map (maximalIdeal S) J.subtype)
      (AdicCompletion.map (maximalIdeal S) J.mkQ) :=
    AdicCompletion.map_exact J.injective_subtype (LinearMap.exact_subtype_mkQ J) J.mkQ_surjective
  suffices hgx : AdicCompletion.map (maximalIdeal S) J.mkQ x = 0 by
    have := LinearMap.mem_range.mpr ((hex x).mp hgx)
    rwa [range_adicCompletion_map_subtype] at this
  refine IsHausdorff.haus (inferInstance :
    IsHausdorff (maximalIdeal S) (AdicCompletion (maximalIdeal S) (S ⧸ J))) _ fun n => ?_
  rw [SModEq.zero]
  obtain ⟨y, hy, hxy⟩ := hx n
  have hy0 : AdicCompletion.map (maximalIdeal S) J.mkQ y = 0 := by
    refine (hex y).mpr (LinearMap.mem_range.mp ?_)
    rwa [range_adicCompletion_map_subtype]
  rw [← sub_add_cancel x y, map_add, hy0, add_zero]
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem S,
    ← Ideal.smul_top_eq_map] at hxy
  have := Submodule.mem_map_of_mem
    (f := (AdicCompletion.map (maximalIdeal S) J.mkQ).restrictScalars S) hxy
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

end Closedness

end Hironaka.Local

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Kollár's reading of (4′), "`ψ^*(h) − ψ'^*(h) ∈ MC ψ^*(I)` for every `h ∈ 𝒪_X`"
([Kol07, Definition 91]), at a point of the support: if `ψ, ψ' : W ⟶ X` agree on the closed
subscheme `V(M)` (`AgreeOn`) and `w ∈ V(M)`, the germs at `w` of `ψ^*s` and `ψ'^*s` differ by an
element of the stalk `M_w`, for every section `s` of `𝒪_X` near `ψ(w) = ψ'(w)`. Proof: `w = ι(z)`
for the closed immersion `ι : V(M) ⟶ W`, whose stalk map at `z` has kernel `M_w`
(`ker_stalkMap_subschemeι`), and `ι^*ψ^*s = (ι ≫ ψ)^*s = (ι ≫ ψ')^*s = ι^*ψ'^*s`. -/
theorem germ_app_sub_germ_app_mem_stalkIdeal {W : Scheme.{u}} (ψ ψ' : W ⟶ X)
    (M : W.IdealSheafData) (h : AgreeOn ψ ψ' M) {w : W} (hw : w ∈ M.support) (V : X.Opens)
    (s : Γ(X, V)) (h1 : ψ.base w ∈ V) (h2 : ψ'.base w ∈ V) :
    W.presheaf.germ (ψ ⁻¹ᵁ V) w h1 (ψ.app V s) -
        W.presheaf.germ (ψ' ⁻¹ᵁ V) w h2 (ψ'.app V s) ∈ M.stalkIdeal w := by
  obtain ⟨z, rfl⟩ := M.exists_subschemeι_eq hw
  rw [← M.ker_stalkMap_subschemeι z, RingHom.mem_ker, map_sub, sub_eq_zero]
  have key : ∀ (g g' : M.subscheme ⟶ X) (e : g = g') (hz : g.base z ∈ V) (hz' : g'.base z ∈ V),
      g.stalkMap z (X.presheaf.germ V _ hz s) = g'.stalkMap z (X.presheaf.germ V _ hz' s) := by
    rintro g g' rfl hz hz'
    rfl
  have e1 : M.subschemeι.stalkMap z (W.presheaf.germ (ψ ⁻¹ᵁ V) _ h1 (ψ.app V s)) =
      (M.subschemeι ≫ ψ).stalkMap z (X.presheaf.germ V ((M.subschemeι ≫ ψ) z) h1 s) :=
    (Scheme.Hom.germ_stalkMap_apply M.subschemeι (ψ ⁻¹ᵁ V) z h1 (ψ.app V s)).trans
      (Scheme.Hom.germ_stalkMap_apply (M.subschemeι ≫ ψ) V z h1 s).symm
  have e2 : M.subschemeι.stalkMap z (W.presheaf.germ (ψ' ⁻¹ᵁ V) _ h2 (ψ'.app V s)) =
      (M.subschemeι ≫ ψ').stalkMap z (X.presheaf.germ V ((M.subschemeι ≫ ψ') z) h2 s) :=
    (Scheme.Hom.germ_stalkMap_apply M.subschemeι (ψ' ⁻¹ᵁ V) z h2 (ψ'.app V s)).trans
      (Scheme.Hom.germ_stalkMap_apply (M.subschemeι ≫ ψ') V z h2 s).symm
  exact e1.trans ((key _ _ h h1 h2).trans e2.symm)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.EtaleNbhdPair

open AlgebraicGeometry.Scheme.IdealSheafData IsLocalRing

variable {X : Scheme.{u}} {p : X} (Q : EtaleNbhdPair X p)

/-- The condition (4′) read on the stalks at `q`: for an étale neighbourhood pair `Q` of `p` whose
maps agree on `V(M)`, `ψ^*a − ψ'^*a ∈ M_q` for every `a ∈ 𝒪_{X,p}`. Off the support of `M` the
stalk `M_q` is the whole ring (`mem_support_iff_stalkIdeal_le_maximalIdeal`); on it,
`germ_app_sub_germ_app_mem_stalkIdeal` on a representing section (`stalkHom_germ`). -/
theorem stalkHom_sub_stalkHom'_mem (M : Q.W.IdealSheafData) (h : AgreeOn Q.ψ Q.ψ' M)
    (a : X.presheaf.stalk p) : Q.stalkHom a - Q.stalkHom' a ∈ M.stalkIdeal Q.q := by
  by_cases hq : Q.q ∈ M.support
  · obtain ⟨V, hpV, s, rfl⟩ := X.presheaf.exists_germ_eq a
    rw [Q.stalkHom_germ, Q.stalkHom'_germ]
    exact germ_app_sub_germ_app_mem_stalkIdeal Q.ψ Q.ψ' M h hq V s _ _
  · have : M.stalkIdeal Q.q = ⊤ := by
      by_contra hne
      exact hq ((mem_support_iff_stalkIdeal_le_maximalIdeal M Q.q).mpr (le_maximalIdeal hne))
    rw [this]
    exact Submodule.mem_top

/-- The condition (4′) for elements of the completion: for an étale neighbourhood pair `Q` of `p`
on a locally Noetherian `X` whose maps agree on `V(M)`, `ψ̂ĥ − ψ̂'ĥ ∈ M_q Ô_{W,q}` for every
`ĥ ∈ Ô_{X,p}`. Approximate `ĥ` by `a ∈ 𝒪_{X,p}` to order `n`
(`exists_sub_algebraMap_mem_maximalIdeal_pow`), use `stalkHom_sub_stalkHom'_mem` for `a` and the
preservation of `𝔪̂ⁿ` by `ψ̂, ψ̂'` (`completionMap_mem_maximalIdeal_pow`), and close with
`mem_map_algebraMap_adicCompletion_of_forall`. -/
theorem completionMap_stalkHom_sub_mem [IsLocallyNoetherian X]
    (M : Q.W.IdealSheafData) (h : AgreeOn Q.ψ Q.ψ' M)
    (x : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) :
    completionMap Q.stalkHom x - completionMap Q.stalkHom' x ∈
      (M.stalkIdeal Q.q).map (algebraMap _
        (AdicCompletion (maximalIdeal (Q.W.presheaf.stalk Q.q)) (Q.W.presheaf.stalk Q.q))) := by
  have := Q.etale_ψ
  have := LocallyOfFiniteType.isLocallyNoetherian Q.ψ
  refine Hironaka.Local.mem_map_algebraMap_adicCompletion_of_forall _ _ fun n => ?_
  obtain ⟨a, ha⟩ := Hironaka.Local.exists_sub_algebraMap_mem_maximalIdeal_pow x n
  refine ⟨algebraMap _ _ (Q.stalkHom a - Q.stalkHom' a),
    Ideal.mem_map_of_mem _ (Q.stalkHom_sub_stalkHom'_mem M h a), ?_⟩
  have e : completionMap Q.stalkHom x - completionMap Q.stalkHom' x -
      algebraMap _ _ (Q.stalkHom a - Q.stalkHom' a) =
      completionMap Q.stalkHom (x - algebraMap _ _ a) -
        completionMap Q.stalkHom' (x - algebraMap _ _ a) := by
    simp only [map_sub, completionMap_algebraMap]
    ring
  rw [e]
  exact Ideal.sub_mem _ (completionMap_mem_maximalIdeal_pow _ ha)
    (completionMap_mem_maximalIdeal_pow _ ha)

section Linear

variable {k : Type u} [Field k]

/-- Kollár's `ψ : U → X` is a morphism of `k`-varieties: `ψ^*` carries the `k`-structure of
`𝒪_{X,p}` induced by `f : X ⟶ Spec k` (`stalkAlgebra`) to the one of `𝒪_{W,q}` induced by
`ψ ≫ f`. -/
theorem stalkHom_algebraMap (f : X ⟶ Spec (.of k)) (c : k) :
    Q.stalkHom (@algebraMap k _ _ _ (f.stalkAlgebra p) c) =
      @algebraMap k _ _ _ ((Q.ψ ≫ f).stalkAlgebra Q.q) c := by
  have hc : @algebraMap k _ _ _ (f.stalkAlgebra p) c =
      X.presheaf.germ (f ⁻¹ᵁ ⊤) p (show p ∈ f ⁻¹ᵁ ⊤ from trivial)
        (f.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv c)) := rfl
  rw [hc, Q.stalkHom_germ]
  rfl

/-- `stalkHom_algebraMap` for the second map `ψ'`. -/
theorem stalkHom'_algebraMap (f : X ⟶ Spec (.of k)) (c : k) :
    Q.stalkHom' (@algebraMap k _ _ _ (f.stalkAlgebra p) c) =
      @algebraMap k _ _ _ ((Q.ψ' ≫ f).stalkAlgebra Q.q) c := by
  have hc : @algebraMap k _ _ _ (f.stalkAlgebra p) c =
      X.presheaf.germ (f ⁻¹ᵁ ⊤) p (show p ∈ f ⁻¹ᵁ ⊤ from trivial)
        (f.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv c)) := rfl
  rw [hc, Q.stalkHom'_germ]
  rfl

/-- Kollár's `ψ, ψ' : U ⇉ X` are morphisms of `k`-varieties (`EtaleEquiv.comp_eq`): when
`ψ ≫ f = ψ' ≫ f`, `ψ^*` and `ψ'^*` agree on the constants `k ⊆ 𝒪_{X,p}`. -/
theorem stalkHom'_algebraMap_eq_stalkHom (f : X ⟶ Spec (.of k)) (hf : Q.ψ ≫ f = Q.ψ' ≫ f)
    (c : k) :
    Q.stalkHom' (@algebraMap k _ _ _ (f.stalkAlgebra p) c) =
      Q.stalkHom (@algebraMap k _ _ _ (f.stalkAlgebra p) c) := by
  rw [Q.stalkHom_algebraMap f c, Q.stalkHom'_algebraMap f c, hf]

/-- Kollár's `φ := ψ̂' ∘ ψ̂⁻¹` read on functions: the inverse of `formalAutomorphism` is
`φ^* = ψ̂⁻¹ ∘ ψ̂'`, i.e. `ψ̂ ∘ φ^* = ψ̂'`. -/
theorem completionMap_stalkHom_formalAutomorphism_symm
    (ha : Function.Bijective (completionMap Q.stalkHom))
    (ha' : Function.Bijective (completionMap Q.stalkHom'))
    (x : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) :
    completionMap Q.stalkHom ((Q.formalAutomorphism ha ha').symm x) =
      completionMap Q.stalkHom' x := by
  have := Q.completionMap_stalkHom'_formalAutomorphism ha ha' ((Q.formalAutomorphism ha ha').symm x)
  rwa [RingEquiv.apply_symm_apply, eq_comm] at this

/-- `φ` is an automorphism of `X̂ = Spec_k Ô_{p,X}` over `k`: for `ψ ≫ f = ψ' ≫ f`,
`φ^* = ψ̂⁻¹ ∘ ψ̂'` fixes the constants `k ⊆ Ô_{X,p}` (the `k`-structure of `FormallyEquivalentAt`,
`f.stalkAlgebra p` extended to the completion). -/
theorem formalAutomorphism_symm_algebraMap (f : X ⟶ Spec (.of k)) (hf : Q.ψ ≫ f = Q.ψ' ≫ f)
    (ha : Function.Bijective (completionMap Q.stalkHom))
    (ha' : Function.Bijective (completionMap Q.stalkHom')) (c : k) :
    letI := f.stalkAlgebra p
    (Q.formalAutomorphism ha ha').symm
        (algebraMap k (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) c) =
      algebraMap k (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) c := by
  apply ha.1
  rw [Q.completionMap_stalkHom_formalAutomorphism_symm, AdicCompletion.algebraMap_apply,
    completionMap_of, completionMap_of, Q.stalkHom'_algebraMap_eq_stalkHom f hf c]

end Linear

section Transport

/-- The conditions (91.1)–(91.3) of [Kol07, Definition 91] from (1′)–(3′): if `ψ^*J = ψ'^*J'` then
`φ^*(Ĵ') = Ĵ` for `φ^* = ψ̂⁻¹ ∘ ψ̂'`, by the transports `ψ̂(Ĵ) = (ψ^*J)^`, `ψ̂'(Ĵ') = (ψ'^*J')^` and
the injectivity of `ψ̂`. With `J = H`, `J' = H'` this is (91.1); with `J = J' = I` (91.2); with
`J = J' = Eⁱ` (91.3). -/
theorem map_formalAutomorphism_symm_completionIdeal
    (ha : Function.Bijective (completionMap Q.stalkHom))
    (ha' : Function.Bijective (completionMap Q.stalkHom')) (J J' : X.IdealSheafData)
    (hJ : J.comap Q.ψ = J'.comap Q.ψ') :
    (J'.completionIdeal p).map (Q.formalAutomorphism ha ha').symm = J.completionIdeal p := by
  rw [Ideal.map_symm, completionIdeal_eq, completionIdeal_eq, ← Ideal.comap_coe]
  have hφ : (Q.formalAutomorphism ha ha' : _ →+* _) =
      (RingEquiv.ofBijective _ ha').symm.toRingHom.comp (completionMap Q.stalkHom) :=
    RingHom.ext fun x => rfl
  have hψ' : ((RingEquiv.ofBijective _ ha' : _ ≃+* _) : _ →+* _) = completionMap Q.stalkHom' :=
    RingHom.ext fun x => rfl
  rw [hφ, ← Ideal.comap_comap, RingEquiv.toRingHom_eq_coe, Ideal.comap_coe, Ideal.comap_symm,
    ← Ideal.map_coe, hψ', map_completionMap_stalkHom' Q, ← hJ, ← map_completionMap_stalkHom Q,
    Ideal.comap_map_of_bijective _ ha]

/-- The condition (91.4) of [Kol07, Definition 91] from (4′): if `ψ, ψ'` agree on `V(ψ^*M)` then
`ĥ − φ^*ĥ ∈ M̂` for every `ĥ ∈ Ô_{X,p}`, for `φ^* = ψ̂⁻¹ ∘ ψ̂'`: apply the injective `ψ̂`, transport
`ψ̂(M̂) = (ψ^*M)^` and use `completionMap_stalkHom_sub_mem`. -/
theorem sub_formalAutomorphism_symm_mem [IsLocallyNoetherian X]
    (ha : Function.Bijective (completionMap Q.stalkHom))
    (ha' : Function.Bijective (completionMap Q.stalkHom')) (M : X.IdealSheafData)
    (h : AgreeOn Q.ψ Q.ψ' (M.comap Q.ψ))
    (x : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) :
    x - (Q.formalAutomorphism ha ha').symm x ∈ M.completionIdeal p := by
  rw [completionIdeal_eq, ← Ideal.comap_map_of_bijective (completionMap Q.stalkHom) ha
    (I := (M.stalkIdeal p).map (algebraMap _ _)), Ideal.mem_comap, map_sub,
    map_completionMap_stalkHom Q, Q.completionMap_stalkHom_formalAutomorphism_symm]
  exact Q.completionMap_stalkHom_sub_mem _ h x

end Transport

end AlgebraicGeometry.EtaleNbhdPair

namespace AlgebraicGeometry.Scheme.IdealSheafData

open AlgebraicGeometry IsLocalRing

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Kollár's "`φ := ψ̂' ∘ ψ̂⁻¹ : X̂ → X̂` is the automorphism we seek" ([Kol07, Definition 91]), in
neighbourhood form: for `X` smooth over `k` and
an étale neighbourhood pair `Q` of `p` (`EtaleNbhdPair`: `ψ, ψ' : W ⟶ X` étale, `ψ(q) = ψ'(q) = p`,
trivial residue field extensions at `q`) with `ψ ≫ f = ψ' ≫ f` and (1′)–(4′) on `W`, `H` and `H'`
are formally equivalent at `p` with respect to `(X, I, E)` (`FormallyEquivalentAt`), through the
`k`-automorphism `φ^* = ψ̂⁻¹ ∘ ψ̂'` of `Ô_{X,p}`. `X` and `W` are locally Noetherian (`X` of finite
type over `k`, `ψ` étale); (91.1)–(91.3) are `map_formalAutomorphism_symm_completionIdeal`, (91.4)
is `sub_formalAutomorphism_symm_mem` with `MC(ψ^*I) = ψ^*MC(I)` (`MC_comap_of_etale`). -/
theorem formallyEquivalentAt_of_etaleNbhdPair (f : X ⟶ Spec (.of k)) [Smooth f]
    (I : X.IdealSheafData) (m : ℕ) (E : DivisorFamily X) (H H' : X.IdealSheafData) {p : X}
    (Q : EtaleNbhdPair X p) (hf : Q.ψ ≫ f = Q.ψ' ≫ f) (h1 : H.comap Q.ψ = H'.comap Q.ψ')
    (h2 : I.comap Q.ψ = I.comap Q.ψ')
    (h3 : ∀ i, (E.component i).comap Q.ψ = (E.component i).comap Q.ψ')
    (h4 : AgreeOn Q.ψ Q.ψ' (MC (Q.ψ ≫ f) (I.comap Q.ψ) m)) :
    FormallyEquivalentAt f I m E H H' p := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Q.W := LocallyOfFiniteType.isLocallyNoetherian Q.ψ
  have ha := bijective_completionMap_stalkHom Q
  have ha' := bijective_completionMap_stalkHom' Q
  unfold FormallyEquivalentAt
  let _inst : Algebra k (X.presheaf.stalk p) := f.stalkAlgebra p
  refine ⟨AlgEquiv.ofRingEquiv (f := (Q.formalAutomorphism ha ha').symm)
    (Q.formalAutomorphism_symm_algebraMap f hf ha ha'), ?_, ?_, ?_, ?_⟩
  · exact Q.map_formalAutomorphism_symm_completionIdeal ha ha' H H' h1
  · exact Q.map_formalAutomorphism_symm_completionIdeal ha ha' I I h2
  · exact fun i => Q.map_formalAutomorphism_symm_completionIdeal ha ha' _ _ (h3 i)
  · intro x
    refine Q.sub_formalAutomorphism_symm_mem ha ha' (MC f I m) ?_ x
    rwa [← MC_comap_of_etale f Q.ψ I m]

/-- For an étale equivalence `Q` of `H` and `H'` with respect to `(X, I, E)` and a point `u ∈ U`
with `ψ(u) = ψ'(u) = p` and trivial residue field extensions at `u`, `H` and `H'` are formally
equivalent at `p`: `formallyEquivalentAt_of_etaleNbhdPair` for the neighbourhood pair
`(U, u, ψ, ψ')` with `Q`'s conditions (1′)–(4′) and `comp_eq`. -/
theorem formallyEquivalentAt_of_etaleEquiv (f : X ⟶ Spec (.of k)) [Smooth f]
    (I : X.IdealSheafData) (m : ℕ) (E : DivisorFamily X) (H H' : X.IdealSheafData)
    (Q : EtaleEquiv f I m E H H') {u : Q.U} {p : X} (hu : Q.ψ.base u = p)
    (hu' : Q.ψ'.base u = p) [IsIso (Q.ψ.residueFieldMap u)] [IsIso (Q.ψ'.residueFieldMap u)] :
    FormallyEquivalentAt f I m E H H' p :=
  formallyEquivalentAt_of_etaleNbhdPair f I m E H H'
    (⟨Q.U, u, Q.ψ, Q.ψ', inferInstance, inferInstance, hu, hu', inferInstance, inferInstance⟩ :
      EtaleNbhdPair X p) Q.comp_eq Q.h1 Q.h2 Q.h3 Q.h4

end AlgebraicGeometry.Scheme.IdealSheafData
