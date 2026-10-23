import DeJongAlterations.Geometry.ProjectiveGraphModification

/-!
# The actual complement-at-infinity argument for Chow graph closures

Two compatible separated-target maps which on an actual dense source factor
through the same two original open immersions have equal inverse-image opens.
The density of every required open restriction is derived internally.
This does not yet construct the finite-family Chow modification.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ChowLemmaOpenLocus

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S X C Y W V : Scheme.{u}}

/-- The original coordinate open forces the original base open on an actual dense graph closure. -/
theorem restriction_projection_eq
    (p : X ⟶ S) [IsSeparated p] (q : C ⟶ S)
    (π : Y ⟶ X) (g : Y ⟶ C) [IsReduced Y]
    (hbase : π ≫ p = g ≫ q)
    (i : W ⟶ X) [IsOpenImmersion i] (e : W ⟶ C) [IsOpenImmersion e]
    (hW : i ≫ p = e ≫ q)
    (j : V ⟶ Y) [IsDominant j] (a : V ⟶ W)
    (hπ : j ≫ π = a ≫ i) (hg : j ≫ g = a ≫ e) :
    (g ⁻¹ᵁ e.opensRange).ι ≫ π =
      (g ∣_ e.opensRange) ≫ e.isoOpensRange.inv ≫ i := by
  let O : Y.Opens := g ⁻¹ᵁ e.opensRange
  let b : O.toScheme ⟶ W := (g ∣_ e.opensRange) ≫ e.isoOpensRange.inv
  have hb : b ≫ e = O.ι ≫ g := by
    dsimp [b]
    rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  let : IsDominant (j ∣_ O) := IsZariskiLocalAtTarget.restrict ‹IsDominant j› O
  have hjb : (j ∣_ O) ≫ b = (j ⁻¹ᵁ O).ι ≫ a := by
    apply (cancel_mono e).mp
    rw [Category.assoc, hb, morphismRestrict_ι_assoc, hg]
    simp only [Category.assoc]
  have heq : O.ι ≫ π = b ≫ i := by
    apply ext_of_isDominant_of_isSeparated p ?_ (j ∣_ O) ?_
    · calc
        (O.ι ≫ π) ≫ p = O.ι ≫ g ≫ q := by rw [Category.assoc, hbase]
        _ = b ≫ e ≫ q := by
          simpa only [Category.assoc] using congrArg (fun t => t ≫ q) hb.symm
        _ = (b ≫ i) ≫ p := by
          simpa only [Category.assoc] using congrArg (fun t => b ≫ t) hW.symm
    · rw [morphismRestrict_ι_assoc, hπ]
      simpa only [Category.assoc] using congrArg (fun t => t ≫ i) hjb.symm
  simpa only [b, Category.assoc] using heq

/-- The original coordinate open forces the original base open on an actual dense graph closure. -/
theorem preimage_openRange_le
    (p : X ⟶ S) [IsSeparated p] (q : C ⟶ S)
    (π : Y ⟶ X) (g : Y ⟶ C) [IsReduced Y]
    (hbase : π ≫ p = g ≫ q)
    (i : W ⟶ X) [IsOpenImmersion i] (e : W ⟶ C) [IsOpenImmersion e]
    (hW : i ≫ p = e ≫ q)
    (j : V ⟶ Y) [IsDominant j] (a : V ⟶ W)
    (hπ : j ≫ π = a ≫ i) (hg : j ≫ g = a ≫ e) :
    g ⁻¹ᵁ e.opensRange ≤ π ⁻¹ᵁ i.opensRange := by
  have heq := restriction_projection_eq p q π g hbase i e hW j a hπ hg
  intro y hy
  refine ⟨((g ∣_ e.opensRange) ≫ e.isoOpensRange.inv) ⟨y, hy⟩, ?_⟩
  exact (congrArg (fun m : (g ⁻¹ᵁ e.opensRange).toScheme ⟶ X => m ⟨y, hy⟩) heq).symm

/-- Both actual open inverse images coincide; neither desired inclusion nor density is a premise. -/
theorem preimage_openRange_eq
    (p : X ⟶ S) [IsSeparated p] (q : C ⟶ S) [IsSeparated q]
    (π : Y ⟶ X) (g : Y ⟶ C) [IsReduced Y]
    (hbase : π ≫ p = g ≫ q)
    (i : W ⟶ X) [IsOpenImmersion i] (e : W ⟶ C) [IsOpenImmersion e]
    (hW : i ≫ p = e ≫ q)
    (j : V ⟶ Y) [IsDominant j] (a : V ⟶ W)
    (hπ : j ≫ π = a ≫ i) (hg : j ≫ g = a ≫ e) :
    g ⁻¹ᵁ e.opensRange = π ⁻¹ᵁ i.opensRange :=
  le_antisymm
    (preimage_openRange_le p q π g hbase i e hW j a hπ hg)
    (preimage_openRange_le q p g π hbase.symm e i hW.symm j a hg hπ)

private theorem isImmersion_of_recoverable_graph
    {T : Scheme.{u}} {ι : Type*} (p : X ⟶ S) (q : T ⟶ S)
    (π : Y ⟶ X) (g : Y ⟶ T) (hbase : π ≫ p = g ≫ q)
    [IsImmersion (pullback.lift π g hbase)]
    (O : ι → T.Opens) (hcover : ⨆ i, g ⁻¹ᵁ O i = ⊤)
    (r : ∀ i, (O i).toScheme ⟶ X)
    (hr : ∀ i, r i ≫ p = (O i).ι ≫ q)
    (hπ : ∀ i, (g ⁻¹ᵁ O i).ι ≫ π = (g ∣_ O i) ≫ r i) :
    IsImmersion g := by
  let : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion := {
    postcomp := fun i hi f hf => by
      let := hi
      let := hf
      infer_instance }
  apply IsZariskiLocalAtTarget.of_range_subset_iSup O
  · rintro _ ⟨y, rfl⟩
    have hy : y ∈ ⨆ i, g ⁻¹ᵁ O i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    let k : (O i).toScheme ⟶ pullback p q := pullback.lift (r i) (O i).ι (hr i)
    have heq : (g ∣_ O i) ≫ k = (g ⁻¹ᵁ O i).ι ≫ pullback.lift π g hbase := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, k, pullback.lift_fst] using (hπ i).symm
      · simpa only [Category.assoc, k, pullback.lift_snd] using morphismRestrict_ι g (O i)
    have : IsImmersion ((g ∣_ O i) ≫ k) := by
      rw [heq]
      infer_instance
    exact IsImmersion.of_comp _ k

/-- The projection of an actual dense graph closure is an immersion when its original coordinate opens cover the original base. -/
theorem isImmersion_of_dense_graph_open_cover
    {T : Scheme.{u}} {ι : Type*} (p : X ⟶ S) [IsSeparated p] (q : T ⟶ S)
    (π : Y ⟶ X) (g : Y ⟶ T) [IsReduced Y] (hbase : π ≫ p = g ≫ q)
    [IsImmersion (pullback.lift π g hbase)]
    (C : ι → Scheme.{u}) (qC : ∀ i, C i ⟶ S) [∀ i, IsSeparated (qC i)]
    (r : ∀ i, T ⟶ C i) (hr : ∀ i, r i ≫ qC i = q)
    (W : ι → Scheme.{u}) (i : ∀ t, W t ⟶ X) [∀ t, IsOpenImmersion (i t)]
    (e : ∀ t, W t ⟶ C t) [∀ t, IsOpenImmersion (e t)]
    (hW : ∀ t, i t ≫ p = e t ≫ qC t)
    (hcover : ⨆ t, (i t).opensRange = ⊤)
    (j : V ⟶ Y) [IsDominant j] (a : ∀ t, V ⟶ W t)
    (hπ : ∀ t, j ≫ π = a t ≫ i t)
    (hg : ∀ t, j ≫ g ≫ r t = a t ≫ e t) : IsImmersion g := by
  let O : ι → T.Opens := fun t => r t ⁻¹ᵁ (e t).opensRange
  let b : ∀ t, (O t).toScheme ⟶ X :=
    fun t => (r t ∣_ (e t).opensRange) ≫ (e t).isoOpensRange.inv ≫ i t
  have hb : ∀ t, b t ≫ p = (O t).ι ≫ q := by
    intro t
    dsimp [b]
    rw [Category.assoc, Category.assoc, hW,
      ← Category.assoc (e t).isoOpensRange.inv, Scheme.Hom.isoOpensRange_inv_comp,
      ← Category.assoc, morphismRestrict_ι, Category.assoc, hr]
  have hbaseC (t) : π ≫ p = (g ≫ r t) ≫ qC t := by
    rw [Category.assoc, hr, hbase]
  have heq (t) : g ⁻¹ᵁ O t = π ⁻¹ᵁ (i t).opensRange :=
    preimage_openRange_eq p (qC t) π (g ≫ r t) (hbaseC t)
      (i t) (e t) (hW t) j (a t) (hπ t) (by simpa only [Category.assoc] using hg t)
  have hcov : ⨆ t, g ⁻¹ᵁ O t = ⊤ := by
    simp_rw [heq]
    rw [← Scheme.Hom.preimage_iSup, hcover]
    rfl
  apply isImmersion_of_recoverable_graph p q π g hbase O hcov b hb
  intro t
  have H := restriction_projection_eq p (qC t) π (g ≫ r t) (hbaseC t)
    (i t) (e t) (hW t) j (a t) (hπ t) (by simpa only [Category.assoc] using hg t)
  simpa only [morphismRestrict_comp, Category.assoc, b, O, Scheme.Hom.comp_preimage] using H

end DeJongAlterations.Geometry.ChowLemmaOpenLocus
