/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership
public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.Smooth.ChartDefs
import Hironaka.Scheme.BlowUp.Composite.Transition
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.ChartIso
import Hironaka.Scheme.Smooth.StandardChart
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The stalks of the blow-up of a chart, read in the chart rings

`Hironaka.Scheme.Smooth.ChartIso` identifies the blow-up `B_{Z∩U} U` of a chart `U` of étale
coordinates adapted to `Z` with the affine blow-up `Proj` of the Rees algebra of `J = (v_0, …,
v_{r-1}) ⊆ Γ(U)`, covers it by the standard charts `Spec Γ(U)[J/v_j]`, and reads the stalk at a
point `p` of the chart of `v_j` as the localization `Γ(U)[J/v_j]_p` ([Hau14, Definitions 4.15–4.16,
Theorem 4.19]; [Kol07, Definition 60]). This module packages what the chart computation of the total
transform needs: at every point `b` of `B_{Z∩U} U` there are a chart index `j < r`, a prime `p` of
the chart ring and ring isomorphisms `𝒪_{B,b} ≃ 𝒪_{Proj, chart p} ≃ Γ(U)[J/v_j]_p` under which **the
stalk of the inverse image of any ideal sheaf `D` of `X` with `D(U) = Q` is `Q · Γ(U)[J/v_j]_p`**
(`exists_chart_point_map_stalkIdeal_eq`). For `D = Z` this is the exceptional ideal `(v_j)`; for a
component `D = (v_c = 0)` of the divisor it is the principal ideal of the image of `v_c`, which
`Hironaka.Scheme.Snc.ChartSncData` writes in the chart coordinates.

**Why the lemmas hold.** On the affine `U ≅ Spec Γ(U)` an ideal sheaf `D` with `D(U) = Q` is the
ideal sheaf of `Q`, so `π_U^{-1} D` corresponds to `π^{-1}(specIdealSheaf Q)` on the affine blow-up
(the isomorphism lies over `U ≅ Spec Γ(U)`). On the chart of `v_j`,
`chart ≫ π = Spec (Γ(U) → Γ(U)[J/v_j])`, so the pull-back of `specIdealSheaf Q` is
`specIdealSheaf (Q Γ(U)[J/v_j])`, whose stalk at `p` is `Q Γ(U)[J/v_j]` extended to the stalk of
`Spec` at `p`; the stalk of `Spec` at `p` is the localization at `p`, compatibly with the germs of
elements of the chart ring (`exists_ringEquiv_stalk_localization`). Open immersions and isomorphisms
induce isomorphisms of stalks carrying the stalk ideals of inverse images to the stalk ideals.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal Scheme.IdealSheafData

namespace AlgebraicGeometry

section Affine

variable {X : Scheme.{u}}

/-- An ideal sheaf `D` of `X` with `D(U) = Q` on the affine open `U` is, on `U ≅ Spec Γ(U)`, the
ideal sheaf of `Q` (the generalization of `comap_toSpecΓ_specIdealSheaf` from the centre to any
ideal sheaf). -/
theorem comap_toSpecΓ_specIdealSheaf_of_ideal_eq (D : X.IdealSheafData) (U : X.affineOpens)
    (Q : Ideal Γ(X, U.1)) (hQ : D.ideal U = Q) :
    (specIdealSheaf Q).comap U.1.toSpecΓ = D.comap U.1.ι := by
  have : IsAffine (U.1 : Scheme.{u}) := U.2
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  have e : (⊤ : (U.1 : Scheme.{u}).Opens) ≤ U.1.ι ⁻¹ᵁ U.1 := fun y _ => y.2
  have h1 : (D.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Q.map U.1.topIso.inv.hom := by
    rw [D.ideal_comap_of_le U.1.ι U ⟨⊤, isAffineOpen_top _⟩ e, hQ]
    exact congrArg (fun φ : Γ(X, U) ⟶ Γ(U.1, ⊤) => Q.map φ.hom) (ι_appLE_top_eq_topIso_inv U.1 e)
  have h2 : ((specIdealSheaf Q).comap U.1.toSpecΓ).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Q.map U.1.topIso.inv.hom := by
    rw [ideal_comap_specIdealSheaf]
    exact congrArg (fun φ => Ideal.map φ Q) (sectionsHom_toSpecΓ_top U.1)
  exact h2.trans h1.symm

end Affine

section Chart

variable {R : Type u} [CommRing R] (J : Ideal R) (a : J)

/-- The stalk of the ideal sheaf of `Q'` on `Spec S` at `p` is `Q'` extended along the germ map
(`stalkIdeal_ofIdealTop` in the `specGerm` spelling). -/
theorem stalkIdeal_specIdealSheaf_specGerm {S : Type u} [CommRing S] (Q' : Ideal S)
    (p : Spec (.of S)) : (specIdealSheaf Q').stalkIdeal p = Q'.map (specGerm p) := by
  rw [stalkIdeal_ofIdealTop, Ideal.map_map]
  rfl

/-- On the chart of `a`, the inverse image of the ideal sheaf of `Q ⊆ R` is the ideal sheaf of
`Q R[J/a]`. -/
theorem comap_chart_comap_π_specIdealSheaf (Q : Ideal R) :
    ((specIdealSheaf Q).comap (affineBlowUp.π J)).comap (affineBlowUp.chart J a) =
      specIdealSheaf (Q.map (algebraMap R (affineBlowUpAlgebra J a))) := by
  rw [← Scheme.IdealSheafData.comap_comp, affineBlowUp.chart_π, comap_specIdealSheaf_Spec_map]

/-- Under the isomorphism `e` of the stalk of the affine blow-up at the point `chart p` with the
localization `R[J/a]_p`, the stalk of the inverse image of the ideal sheaf of `Q ⊆ R` is
`Q R[J/a]_p`. -/
theorem map_stalkIdeal_comap_π_specIdealSheaf (Q : Ideal R)
    (p : Spec (.of (affineBlowUpAlgebra J a)))
    (e : (affineBlowUp J).presheaf.stalk (affineBlowUp.chart J a p) ≃+*
      Localization.AtPrime p.asIdeal (hp := PrimeSpectrum.isPrime p))
    (he : ∀ c : affineBlowUpAlgebra J a,
      (affineBlowUp.chart J a).stalkMap p (e.symm (algebraMap _ _ c)) = specGerm p c) :
    (((specIdealSheaf Q).comap (affineBlowUp.π J)).stalkIdeal
        (affineBlowUp.chart J a p)).map e =
      (Q.map (algebraMap R (affineBlowUpAlgebra J a))).map
        (algebraMap (affineBlowUpAlgebra J a)
          (Localization.AtPrime p.asIdeal (hp := PrimeSpectrum.isPrime p))) := by
  set K := (specIdealSheaf Q).comap (affineBlowUp.π J) with hK
  set Q' := Q.map (algebraMap R (affineBlowUpAlgebra J a)) with hQ'
  set st := ((affineBlowUp.chart J a).stalkMap p).hom with hst
  set es : Localization.AtPrime p.asIdeal (hp := PrimeSpectrum.isPrime p) →+*
      (affineBlowUp J).presheaf.stalk (affineBlowUp.chart J a p) := e.symm.toRingHom with hes
  have hbij : Function.Bijective st := ConcreteCategory.bijective_of_isIso _
  -- the stalk of `K` pulled back to the chart is `Q' R[J/a]_p` read through the germs
  have h1 : (K.stalkIdeal (affineBlowUp.chart J a p)).map st = Q'.map (specGerm p) := by
    rw [← Scheme.IdealSheafData.stalkIdeal_comap, hK, comap_chart_comap_π_specIdealSheaf,
      stalkIdeal_specIdealSheaf_specGerm]
  -- `e.symm` followed by the chart's stalk map is the germ map on `algebraMap`
  have h2 : ((Q'.map (algebraMap (affineBlowUpAlgebra J a)
      (Localization.AtPrime p.asIdeal (hp := PrimeSpectrum.isPrime p)))).map es).map st =
      Q'.map (specGerm p) := by
    rw [Ideal.map_map, Ideal.map_map]
    refine congrArg (Ideal.map · Q') (RingHom.ext fun c => ?_)
    exact he c
  have h3 : (Q'.map (algebraMap (affineBlowUpAlgebra J a)
      (Localization.AtPrime p.asIdeal (hp := PrimeSpectrum.isPrime p)))).map es =
      K.stalkIdeal (affineBlowUp.chart J a p) := by
    have := congrArg (Ideal.comap st) (h2.trans h1.symm)
    rwa [Ideal.comap_map_of_bijective st hbij, Ideal.comap_map_of_bijective st hbij] at this
  rw [← h3]
  change Ideal.map e.toRingHom _ = _
  rw [Ideal.map_map]
  have hid : e.toRingHom.comp es = RingHom.id _ := by
    ext c
    simp [hes]
  rw [hid, Ideal.map_id]

end Chart

section BlowUp

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n r : ℕ}
  {Z : X.IdealSheafData} {x₀ : X}

/-- Every point of the affine blow-up of `J = (v_0, …, v_{r-1})` lies in the chart of some `v_j`,
`j < r`. -/
theorem exists_mem_opensRange_chart_coord (E : EtaleCoordinatesAdapted f n r Z x₀)
    (b' : affineBlowUp E.centerIdeal) :
    ∃ (j : Fin n) (hj : j.val < r),
      b' ∈ (affineBlowUp.chart E.centerIdeal (E.coord j hj)).opensRange := by
  obtain ⟨y, hmem⟩ := affineBlowUp.exists_mem_opensRange_chart_of_span_eq E.centerIdeal
    (Set.range fun i : {i : Fin n // i.val < r} => E.v i.1) rfl b'
  obtain ⟨⟨j, hj⟩, hyj⟩ := Set.mem_range.mp y.2
  obtain ⟨a₀, ha₀, hmem⟩ : ∃ a₀ : E.centerIdeal, (a₀ : Γ(X, E.U)) = y ∧
      b' ∈ (affineBlowUp.chart E.centerIdeal a₀).opensRange := ⟨_, rfl, hmem⟩
  obtain rfl : E.coord j hj = a₀ := Subtype.ext (hyj.trans ha₀.symm)
  exact ⟨j, hj, hmem⟩

/-- The chart model of a point ([Hau14, Definitions 4.15–4.16, Theorem 4.19];
[Kol07, Definition 60]): every point `b` of `B_{Z∩U} U` lies in the chart of some `v_j` (`j < r`) as
a prime `p` of the chart ring `Γ(U)[J/v_j]`, with ring isomorphisms
`𝒪_{B,b} ≃ 𝒪_{Proj, chart p} ≃ Γ(U)[J/v_j]_p` under which the stalk of the inverse image of any
ideal sheaf `D` of `X` with `D(U) = Q` is `Q Γ(U)[J/v_j]_p`. -/
theorem exists_chart_point_map_stalkIdeal_eq (E : EtaleCoordinatesAdapted f n r Z x₀)
    (b : blowUp (Z.comap E.U.1.ι)) :
    ∃ (j : Fin n) (hj : j.val < r)
      (p : Spec (.of (affineBlowUpAlgebra E.centerIdeal (E.coord j hj))))
      (e₁ : (blowUp (Z.comap E.U.1.ι)).presheaf.stalk b ≃+*
        (affineBlowUp E.centerIdeal).presheaf.stalk
          (affineBlowUp.chart E.centerIdeal (E.coord j hj) p))
      (e₂ : (affineBlowUp E.centerIdeal).presheaf.stalk
          (affineBlowUp.chart E.centerIdeal (E.coord j hj) p) ≃+*
        Localization.AtPrime p.asIdeal (hp := PrimeSpectrum.isPrime p)),
      ∀ (D : X.IdealSheafData) (Q : Ideal Γ(X, E.U)), D.ideal E.U = Q →
        ((((D.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).stalkIdeal b).map e₁).map e₂ =
          (Q.map (algebraMap Γ(X, E.U) (affineBlowUpAlgebra E.centerIdeal (E.coord j hj)))).map
            (algebraMap (affineBlowUpAlgebra E.centerIdeal (E.coord j hj))
              (Localization.AtPrime p.asIdeal (hp := PrimeSpectrum.isPrime p))) := by
  classical
  have hΦex := exists_iso_blowUp_affineBlowUp E
  let Φ : blowUp (Z.comap E.U.1.ι) ≅ affineBlowUp E.centerIdeal := hΦex.choose
  have hΦ : Φ.hom ≫ affineBlowUp.π E.centerIdeal =
      blowUpπ (Z.comap E.U.1.ι) ≫ E.U.1.toSpecΓ := hΦex.choose_spec
  -- the point lies in the chart of some `v_j`
  have hjex := exists_mem_opensRange_chart_coord E (Φ.hom b)
  obtain ⟨j, hj, hmem⟩ := hjex
  have hpex := Scheme.Hom.mem_opensRange.mp hmem
  obtain ⟨p, hp⟩ := hpex
  have hb : b = Φ.inv (affineBlowUp.chart E.centerIdeal (E.coord j hj) p) := by
    rw [hp, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  subst hb
  let q := affineBlowUp.chart E.centerIdeal (E.coord j hj) p
  have he₂ex := exists_ringEquiv_stalk_chart E.centerIdeal (E.coord j hj) p
  obtain ⟨e₂, he₂⟩ := he₂ex
  have hbij : Function.Bijective (Φ.inv.stalkMap q).hom := ConcreteCategory.bijective_of_isIso _
  refine ⟨j, hj, p, RingEquiv.ofBijective (Φ.inv.stalkMap q).hom hbij, e₂, fun D Q hQ => ?_⟩
  -- the inverse image of `D` on `B_{Z∩U} U` is the inverse image of `specIdealSheaf Q` along `Φ`
  have hD : (D.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι)) =
      ((specIdealSheaf Q).comap (affineBlowUp.π E.centerIdeal)).comap Φ.hom := by
    rw [← comap_toSpecΓ_specIdealSheaf_of_ideal_eq D E.U Q hQ,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hΦ]
  -- its stalk at `Φ.inv q`, carried along `Φ.inv`, is the stalk at `q`
  have hstalk : ∀ K : (affineBlowUp E.centerIdeal).IdealSheafData,
      ((K.comap Φ.hom).stalkIdeal (Φ.inv q)).map (Φ.inv.stalkMap q).hom = K.stalkIdeal q := by
    intro K
    rw [← Scheme.IdealSheafData.stalkIdeal_comap, ← Scheme.IdealSheafData.comap_comp,
      Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  change ((((D.comap E.U.1.ι).comap (blowUpπ (Z.comap E.U.1.ι))).stalkIdeal (Φ.inv q)).map
    (Φ.inv.stalkMap q).hom).map e₂ = _
  have hgoal := map_stalkIdeal_comap_π_specIdealSheaf E.centerIdeal (E.coord j hj) Q p e₂ he₂
  exact (congrArg (Ideal.map e₂) ((congrArg (fun L : (blowUp (Z.comap E.U.1.ι)).IdealSheafData =>
    (L.stalkIdeal (Φ.inv q)).map (Φ.inv.stalkMap q).hom) hD).trans
      (hstalk ((specIdealSheaf Q).comap (affineBlowUp.π E.centerIdeal))))).trans hgoal

end BlowUp

end AlgebraicGeometry
