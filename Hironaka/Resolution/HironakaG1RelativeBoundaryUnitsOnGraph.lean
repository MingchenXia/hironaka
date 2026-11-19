import Hironaka.Resolution.HironakaG1RelativeBoundaryUnitLifts
import Hironaka.Resolution.HironakaActualAnalyticSubspaceIntrinsicLifting

/-! Simultaneous representatives of the relative native boundary units on
the genuine paired graph. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1RelativeBoundaryUnitsOnGraph
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings BlowupFlatCoordinates HolGerm
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceResidue
  HironakaReducedComplexAnalyticSpaces HironakaHolomorphicJetRankLoci
  HironakaActualAnalyticSubspaceLocalFunctions HironakaG1RelativeBoundaryUnitLifts
  HironakaActualIntrinsicLabelledBoundaryIdeals HironakaG1QuotientLabelledBoundaryFrame

variable {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m}

/-- An actual ambient unit has an original holomorphic function
representative which is nonzero throughout a neighborhood of the point. -/
theorem ambient_unit_representative (p : M)
    (v : (actualComplexStructureStalk (n := n) p)ˣ) :
    ∃ (f : M → ℂ) (hf : HolomorphicAt n f p),
      actualOriginalFunctionGerm p f hf = v ∧
      ∀ᶠ x in 𝓝 p, HolomorphicAt n f x ∧ f x ≠ 0 := by
  obtain ⟨U, hpU, s, hs⟩ :=
    (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq
      (show actualComplexStructureStalk (n := n) p from v)
  let f := sectionExtension U s
  have hf : HolomorphicAt n f p := sectionExtension_holomorphicAt U s p hpU
  have hRep := (actualOriginalFunctionGerm_eq_section U p hpU s f hf EventuallyEq.rfl).trans hs
  have hUnit : IsUnit (actualOriginalFunctionGerm p f hf) := hRep.symm ▸ v.isUnit
  rw [← isUnit_map_iff (actualStalkChartEquiv (n := n) p), actualOriginalFunctionGerm_chart,
    HolGerm.isUnit_iff_eval_ne_zero] at hUnit
  change f ((chartAt (ComplexModel n) p).symm (0 + chartAt (ComplexModel n) p p)) ≠ 0 at hUnit
  rw [zero_add, (chartAt (ComplexModel n) p).left_inv (mem_chart_source _ p)] at hUnit
  exact ⟨f, hf, hRep, hf.eventually.and
    (hf.continuousAt.eventually (isOpen_ne.mem_nhds hUnit))⟩

private theorem original_mul (p : M) {f g : M → ℂ}
    (hf : HolomorphicAt n f p) (hg : HolomorphicAt n g p) :
    actualOriginalFunctionGerm p (fun x => f x * g x) (hf.mul hg) =
      actualOriginalFunctionGerm p f hf * actualOriginalFunctionGerm p g hg := by
  apply (actualStalkChartEquiv (n := n) p).injective
  rw [map_mul, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

private theorem graph_section_relation {C : Set M} {D : Set N}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (p : C) (U : Opens M) (V : Opens N) (hpU : p.val ∈ U) (hpV : (e.base p).val ∈ V)
    (s : actualComplexSection (n := n) U) (t : actualComplexSection (n := m) V)
    (h : (actualSubspaceInclusion (n := n) C).stalkMap p
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ U p.val hpU s) =
      e.stalkMap p ((actualSubspaceInclusion (n := m) D).stalkMap (e.base p)
        ((actualComplexStructureSheaf (n := m) N).presheaf.germ V (e.base p).val hpV t))) :
    ∀ᶠ x : C in 𝓝 p, sectionExtension U s x.val = sectionExtension V t (e.base x).val := by
  let i := actualSubspaceInclusion (n := n) C
  let j := actualSubspaceInclusion (n := m) D
  let k := e ≫ j
  let A := (Opens.map i.base).obj U
  let B := (Opens.map k.base).obj V
  let S := (actualSubspaceSheaf (n := n) C).presheaf
  let a := i.c.app (op U) s
  let b := k.c.app (op V) t
  have hG : S.germ A p hpU a = S.germ B p hpV b := by
    exact (LocallyRingedSpace.stalkMap_germ_apply i U p hpU s).symm.trans
      (h.trans ((ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp e j p) _).symm.trans
        (LocallyRingedSpace.stalkMap_germ_apply k V p hpV t)))
  obtain ⟨W, hpW, l, r, hEq⟩ := S.germ_eq p hpU hpV a b hG
  filter_upwards [W.isOpen.mem_nhds hpW] with x hx
  have hxU : x ∈ A := l.le hx
  have hxV : x ∈ B := r.le hx
  have hg := S.germ_ext (hxU := hxU) (hxV := hxV) W hx l r hEq
  change S.germ A x hxU a = S.germ B x hxV b at hg
  have hxU' : x.val ∈ U := hxU
  have hxV' : (e.base x).val ∈ V := hxV
  have hg' := (LocallyRingedSpace.stalkMap_germ_apply i U x hxU' s).trans
    (hg.trans (LocallyRingedSpace.stalkMap_germ_apply k V x hxV' t).symm)
  let v := (actualComplexStructureSheaf (n := m) N).presheaf.germ V (e.base x).val hxV' t
  calc
    _ = s ⟨x.val, hxU'⟩ := sectionExtension_apply U s x.val hxU'
    _ = actualSubspaceStalkEval (n := n) C x
        (i.stalkMap x ((actualComplexStructureSheaf (n := n) M).presheaf.germ U x.val hxU' s)) :=
      (actualSubspaceStalkEval_inclusion_germ C U s x hxU').symm
    _ = actualSubspaceStalkEval (n := n) C x (k.stalkMap x v) :=
      congrArg (actualSubspaceStalkEval (n := n) C x) hg'
    _ = actualSubspaceStalkEval (n := n) C x (e.stalkMap x (j.stalkMap (e.base x) v)) :=
      congrArg (actualSubspaceStalkEval (n := n) C x)
        (ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp e j x) v)
    _ = actualSubspaceStalkEval (n := m) D (e.base x) (j.stalkMap (e.base x) v) :=
      actualSubspaceMap_eval_of_point_compatible e he x _
    _ = t ⟨(e.base x).val, hxV'⟩ := actualSubspaceStalkEval_inclusion_germ D V t (e.base x) hxV'
    _ = _ := (sectionExtension_apply V t (e.base x).val hxV').symm

/-- A relation between original ambient function germs in the actual
quotient stalk specializes to their values along the actual native graph. -/
theorem original_germ_relation_on_graph {C : Set M} {D : Set N}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (p : C) {f : M → ℂ} {g : N → ℂ} (hf : HolomorphicAt n f p.val)
    (hg : HolomorphicAt m g (e.base p).val)
    (h : (actualSubspaceInclusion (n := n) C).stalkMap p (actualOriginalFunctionGerm p.val f hf) =
      e.stalkMap p ((actualSubspaceInclusion (n := m) D).stalkMap (e.base p)
        (actualOriginalFunctionGerm (e.base p).val g hg))) :
    ∀ᶠ x : C in 𝓝 p, f x.val = g (e.base x).val := by
  obtain ⟨U, hpU, s, hs⟩ := exists_actual_section_of_original_holomorphicAt p.val f hf
  obtain ⟨V, hpV, t, ht⟩ := exists_actual_section_of_original_holomorphicAt (e.base p).val g hg
  rw [actualOriginalFunctionGerm_eq_section U p.val hpU s f hf hs,
    actualOriginalFunctionGerm_eq_section V (e.base p).val hpV t g hg ht] at h
  have hgraph := graph_section_relation e he p U V hpU hpV s t h
  have hs' := continuous_subtype_val.continuousAt.eventually hs
  have ht' := (continuous_subtype_val.comp e.base.hom.continuous).continuousAt.eventually ht
  filter_upwards [hgraph, hs', ht'] with x h₀ h₁ h₂
  exact h₁.symm.trans (h₀.trans h₂)

private abbrev ambient (p : M) := actualComplexStructureStalk (n := n) p
private abbrev native (C : Set M) (p : C) := ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier

/-- A finite paired family of ambient lifts has simultaneous nonvanishing
holomorphic representatives. Both representatives give the same ratio
along the actual native graph. -/
theorem simultaneous_unit_representatives {ι : Type} [Finite ι]
    {C : Set M} {D : Set N}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (p : C) (f : ι → M → ℂ) (g : ι → N → ℂ)
    (hf : ∀ i, HolomorphicAt n (f i) p.val)
    (hg : ∀ i, HolomorphicAt m (g i) (e.base p).val)
    (v : ι → (ambient p.val)ˣ) (w : ι → (ambient (e.base p).val)ˣ)
    (hUnit : ∀ i, e.stalkMap p ((actualSubspaceInclusion (n := m) D).stalkMap (e.base p)
      (w i : ambient (e.base p).val)) =
        (actualSubspaceInclusion (n := n) C).stalkMap p (v i : ambient p.val))
    (hRatio : ∀ i, e.stalkMap p ((actualSubspaceInclusion (n := m) D).stalkMap (e.base p)
      (actualOriginalFunctionGerm (e.base p).val (g i) (hg i))) =
        (actualSubspaceInclusion (n := n) C).stalkMap p
          ((v i : ambient p.val) * actualOriginalFunctionGerm p.val (f i) (hf i))) :
    ∃ (a : ι → M → ℂ) (b : ι → N → ℂ)
      (ha : ∀ i, HolomorphicAt n (a i) p.val) (hb : ∀ i, HolomorphicAt m (b i) (e.base p).val)
      (U : Opens M) (V : Opens N),
      p.val ∈ U ∧ (e.base p).val ∈ V ∧
      (∀ i, actualOriginalFunctionGerm p.val (a i) (ha i) = (v i : ambient p.val)) ∧
      (∀ i, actualOriginalFunctionGerm (e.base p).val (b i) (hb i) = (w i : ambient (e.base p).val)) ∧
      (∀ x ∈ U, ∀ i, HolomorphicAt n (a i) x ∧ a i x ≠ 0) ∧
      (∀ y ∈ V, ∀ i, HolomorphicAt m (b i) y ∧ b i y ≠ 0) ∧
      ∀ x : C, x.val ∈ U → (e.base x).val ∈ V ∧
        ∀ i, a i x.val = b i (e.base x).val ∧
          g i (e.base x).val = a i x.val * f i x.val := by
  classical
  choose a ha hga hna using fun i => ambient_unit_representative p.val (v i)
  choose b hb hgb hnb using fun i => ambient_unit_representative (e.base p).val (w i)
  obtain ⟨Vs, hVs, hVo, hpV⟩ := mem_nhds_iff.mp (Filter.eventually_all.mpr hnb)
  let V : Opens N := ⟨Vs, hVo⟩
  have hv (i : ι) : ∀ᶠ x : C in 𝓝 p, a i x.val = b i (e.base x).val := by
    apply original_germ_relation_on_graph e he p (ha i) (hb i)
    rw [hga i, hgb i]
    exact (hUnit i).symm
  have hr (i : ι) : ∀ᶠ x : C in 𝓝 p, g i (e.base x).val = a i x.val * f i x.val := by
    have h : ∀ᶠ x : C in 𝓝 p, a i x.val * f i x.val = g i (e.base x).val := by
      apply original_germ_relation_on_graph e he p ((ha i).mul (hf i)) (hg i)
      rw [original_mul p.val (ha i) (hf i), hga i]
      exact (hRatio i).symm
    exact h.mono fun _ hx => hx.symm
  have hV : ∀ᶠ x : C in 𝓝 p, (e.base x).val ∈ V :=
    (continuous_subtype_val.comp e.base.hom.continuous).continuousAt.eventually
      (V.isOpen.mem_nhds hpV)
  have hG : ∀ᶠ x : C in 𝓝 p, (e.base x).val ∈ V ∧
      ∀ i, a i x.val = b i (e.base x).val ∧ g i (e.base x).val = a i x.val * f i x.val :=
    hV.and (Filter.eventually_all.mpr fun i => (hv i).and (hr i))
  rw [nhds_subtype_eq_comap, Filter.eventually_comap] at hG
  obtain ⟨Us, hUs, hUo, hpU⟩ := mem_nhds_iff.mp ((Filter.eventually_all.mpr hna).and hG)
  exact ⟨a, b, ha, hb, ⟨Us, hUo⟩, V, hpU, hpV, hga, hgb,
    (fun x hx => (hUs hx).1), (fun y hy => hVs hy), fun x hx => (hUs hx).2 x rfl⟩

/-- The whole original label is a flat coordinate for an active slot and
the constant one for an absent slot. -/
def labelledFunction {p : M}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
    {k : ℕ} (κ : Fin k → Option (Fin n)) (i : Fin k) (x : M) : ℂ :=
  match κ i with
  | none => 1
  | some j => flatCoord Φ j x

theorem labelledFunction_holomorphicAt {p : M}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
    {k : ℕ} (κ : Fin k → Option (Fin n)) (i : Fin k) {x : M} (hx : x ∈ flatDomain Φ) :
    HolomorphicAt n (labelledFunction Φ κ i) x := by
  cases h : κ i with
  | none =>
    have he : labelledFunction Φ κ i = fun _ : M => (1 : ℂ) := by
      funext z
      simp [labelledFunction, h]
    rw [he]
    exact holomorphicAt_const 1
  | some j =>
    have he : labelledFunction Φ κ i = flatCoord Φ j := by
      funext z
      simp [labelledFunction, h]
    rw [he]
    exact holomorphicAt_flatCoord Φ j hx

private theorem original_congr_eq (p : M) {f g : M → ℂ}
    (hf : HolomorphicAt n f p) (hg : HolomorphicAt n g p) (he : f = g) :
    actualOriginalFunctionGerm p f hf = actualOriginalFunctionGerm p g hg := by
  subst g
  rfl

/-- The original function representing a label maps to the literal
quotient boundary germ, including the constant-one slot. -/
theorem labelledFunction_quotient {p : M}
    (C : Set M) (x : C)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
    {k : ℕ} (κ : Fin k → Option (Fin n)) (i : Fin k) (hx : x.val ∈ flatDomain Φ) :
    (actualSubspaceInclusion (n := n) C).stalkMap x
      (actualOriginalFunctionGerm x.val (labelledFunction Φ κ i) (labelledFunction_holomorphicAt Φ κ i hx)) =
      quotientBoundaryGerm C Φ κ x hx i := by
  cases h : κ i with
  | none =>
    have he : labelledFunction Φ κ i = fun _ : M => (1 : ℂ) := by
      funext z
      simp [labelledFunction, h]
    have h1 : actualOriginalFunctionGerm x.val (fun _ : M => (1 : ℂ))
        (holomorphicAt_const (n := n) 1) = 1 := by
      apply (actualStalkChartEquiv (n := n) x.val).injective
      rw [map_one, actualOriginalFunctionGerm_chart]
      exact HolGerm.mk_one (E := ComplexModel n)
    have hg : actualOriginalFunctionGerm x.val (labelledFunction Φ κ i)
        (labelledFunction_holomorphicAt Φ κ i hx) = 1 :=
      (original_congr_eq x.val _ (holomorphicAt_const 1) he).trans h1
    rw [hg]
    exact (map_one ((actualSubspaceInclusion (n := n) C).stalkMap x).hom).trans
      (by simp [quotientBoundaryGerm, h])
  | some j =>
    have he : labelledFunction Φ κ i = flatCoord Φ j := by
      funext z
      simp [labelledFunction, h]
    have hg : actualOriginalFunctionGerm x.val (labelledFunction Φ κ i)
        (labelledFunction_holomorphicAt Φ κ i hx) =
        actualOriginalFunctionGerm x.val (flatCoord Φ j) (holomorphicAt_flatCoord Φ j hx) :=
      original_congr_eq x.val _ _ he
    rw [hg]
    simp [quotientBoundaryGerm, h]

set_option maxHeartbeats 550000 in
/-- The genuine paired labelled frames have simultaneous ambient holomorphic
unit representatives. The two unit values agree on the native graph, where
they relate the selected coordinates pointwise. -/
theorem exists_relative_labelled_units_on_graph
    (C : Set M) (D : Set N)
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (p : C) {E : List (Set M)} {F : List (Set N)}
    (hE : IsSNCDivisor n E) (hF : IsSNCDivisor m F) (τ : Fin E.length ≃ Fin F.length)
    (hI : ∀ i : Fin E.length, Ideal.map (e.hom.stalkMap p).hom
      (actualLabelledBoundaryTraceIdeal D F (τ i) (e.hom.base p)) =
        actualLabelledBoundaryTraceIdeal C E i p) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p.val p.val))
      (κ : Fin E.length → Option (Fin n))
      (Ψ : LocalHolomorphicEquivAt (n := m)
        (chartAt (ComplexModel m) (e.hom.base p).val (e.hom.base p).val))
      (κ' : Fin F.length → Option (Fin m))
      (U : Opens M) (V : Opens N) (a : Fin E.length → M → ℂ) (b : Fin E.length → N → ℂ),
      Φ.source ⊆ (chartAt (ComplexModel n) p.val).target ∧
      Ψ.source ⊆ (chartAt (ComplexModel m) (e.hom.base p).val).target ∧
      Φ.toFun (chartAt (ComplexModel n) p.val p.val) = 0 ∧
      Ψ.toFun (chartAt (ComplexModel m) (e.hom.base p).val (e.hom.base p).val) = 0 ∧
      Set.InjOn κ {i | p.val ∈ E.get i} ∧
      Set.InjOn κ' {i | (e.hom.base p).val ∈ F.get i} ∧
      (∀ y ∈ flatDomain Φ, ∀ i, y ∈ E.get i ↔ ∃ j, κ i = some j ∧ flatCoord Φ j y = 0) ∧
      (∀ y ∈ flatDomain Ψ, ∀ i, y ∈ F.get i ↔ ∃ j, κ' i = some j ∧ flatCoord Ψ j y = 0) ∧
      (∀ i, p.val ∈ E.get i ↔ (e.hom.base p).val ∈ F.get (τ i)) ∧
      p.val ∈ U ∧ (e.hom.base p).val ∈ V ∧ (U : Set M) ⊆ flatDomain Φ ∧ (V : Set N) ⊆ flatDomain Ψ ∧
      (∀ x ∈ U, ∀ i, HolomorphicAt n (a i) x ∧ a i x ≠ 0) ∧
      (∀ y ∈ V, ∀ i, HolomorphicAt m (b i) y ∧ b i y ≠ 0) ∧
      ∀ x : C, x.val ∈ U → (e.hom.base x).val ∈ V ∧
        ∀ i, a i x.val = b i (e.hom.base x).val ∧
          labelledFunction Ψ κ' (τ i) (e.hom.base x).val =
            a i x.val * labelledFunction Φ κ i x.val := by
  classical
  let p' := e.hom.base p
  let ε := (asIso (e.hom.stalkMap p)).commRingCatIsoToRingEquiv
  obtain ⟨Φ, κ, Ψ, κ', hΦ, hΨ, hz, hz', hi, hi', hm, hm', hact, hu⟩ :=
    exists_relative_labelled_unit_lifts C D p p' hE hF τ ε hI
  have hExist (i : Fin E.length) := (hu i).2.2
  choose r v w hRel hV hW using hExist
  let f := labelledFunction Φ κ
  let g := fun i => labelledFunction Ψ κ' (τ i)
  have hf (i : Fin E.length) := labelledFunction_holomorphicAt Φ κ i (mem_flatDomain_self Φ)
  have hg (i : Fin E.length) := labelledFunction_holomorphicAt Ψ κ' (τ i) (mem_flatDomain_self Ψ)
  have hUnit (i : Fin E.length) :
      e.hom.stalkMap p ((actualSubspaceInclusion (n := m) D).stalkMap p' (w i : ambient p'.val)) =
        (actualSubspaceInclusion (n := n) C).stalkMap p (v i : ambient p.val) := by
    have hleft := congrArg (fun z : (native C p)ˣ => (z : native C p)) (hV i)
    have hright := congrArg (fun z : (native D p')ˣ => (z : native D p')) (hW i)
    change (actualSubspaceInclusion (n := n) C).stalkMap p (v i : ambient p.val) = _ at hleft
    change (actualSubspaceInclusion (n := m) D).stalkMap p' (w i : ambient p'.val) =
      ε.symm (r i : native C p) at hright
    rw [hright, hleft]
    exact ε.apply_symm_apply _
  have hRatio (i : Fin E.length) :
      e.hom.stalkMap p ((actualSubspaceInclusion (n := m) D).stalkMap p'
          (actualOriginalFunctionGerm p'.val (g i) (hg i))) =
        (actualSubspaceInclusion (n := n) C).stalkMap p
          ((v i : ambient p.val) * actualOriginalFunctionGerm p.val (f i) (hf i)) := by
    change _ = ((actualSubspaceInclusion (n := n) C).stalkMap p).hom _
    rw [map_mul, labelledFunction_quotient D p' Ψ κ' (τ i) (mem_flatDomain_self Ψ),
      labelledFunction_quotient C p Φ κ i (mem_flatDomain_self Φ)]
    have hleft := congrArg (fun z : (native C p)ˣ => (z : native C p)) (hV i)
    change ((actualSubspaceInclusion (n := n) C).stalkMap p).hom (v i : ambient p.val) = _ at hleft
    rw [hleft]
    exact hRel i
  obtain ⟨a, b, _, _, U₀, V₀, hpU, hpV, _, _, ha, hb, hG⟩ :=
    simultaneous_unit_representatives e.hom he p f g hf hg v w hUnit hRatio
  let V : Opens N := ⟨(V₀ : Set N) ∩ flatDomain Ψ, V₀.isOpen.inter (isOpen_flatDomain Ψ)⟩
  have hpV' : p'.val ∈ V := ⟨hpV, mem_flatDomain_self Ψ⟩
  have hNear : ∀ᶠ x : C in 𝓝 p, (e.hom.base x).val ∈ V :=
    (continuous_subtype_val.comp e.hom.base.hom.continuous).continuousAt.eventually
      (V.isOpen.mem_nhds hpV')
  rw [nhds_subtype_eq_comap, Filter.eventually_comap] at hNear
  obtain ⟨S, hS, hSo, hpS⟩ := mem_nhds_iff.mp hNear
  let U : Opens M := ⟨(U₀ : Set M) ∩ (flatDomain Φ ∩ S),
    U₀.isOpen.inter ((isOpen_flatDomain Φ).inter hSo)⟩
  have hpU' : p.val ∈ U := ⟨hpU, mem_flatDomain_self Φ, hpS⟩
  exact ⟨Φ, κ, Ψ, κ', U, V, a, b, hΦ, hΨ, hz, hz', hi, hi', hm, hm', hact,
    hpU', hpV', (fun _ h => h.2.1), (fun _ h => h.2), (fun x hx => ha x hx.1),
    (fun y hy => hb y hy.1), fun x hx => ⟨hS hx.2.2 x rfl, (hG x hx.1).2⟩⟩

end
end Hironaka.HironakaG1RelativeBoundaryUnitsOnGraph
