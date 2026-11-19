import Hironaka.Resolution.HironakaG4OptionalBoundaryTransform

/-! Combinatorics of distinct transverse divisor coordinates under a monomial step. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaG4OptionalDivisorMasks

variable {n : ℕ}

def DivisorMasksValid {ι : Type*} (S : Finset (Fin n)) (m : ι → Option (Fin n)) : Prop :=
  (∀ i k, m i = some k → k ∉ S) ∧
  ∀ i j k, m i = some k → m j = some k → i = j

def nextDivisorMask {ι : Type*} (σ : Fin n ≃ Fin n) (j : Fin n)
    (m : ι → Option (Fin n)) : ι ⊕ Unit → Option (Fin n)
  | .inl i => (m i).bind fun k => if σ k = j then none else some (σ k)
  | .inr _ => some j

/-- Distinct transverse singleton masks remain so, after permuting, deleting
pivot members, and adjoining the exceptional pivot. -/
theorem nextDivisorMask_valid {ι : Type*} (S : Finset (Fin n))
    (m : ι → Option (Fin n)) (hvalid : DivisorMasksValid S m)
    (σ : Fin n ≃ Fin n) (j : Fin n) (hj : j ∉ S.image σ) :
    DivisorMasksValid (S.image σ) (nextDivisorMask σ j m) := by
  classical
  constructor
  · intro i k hk
    cases i with
    | inl i =>
      cases hm : m i with
      | none => simp [nextDivisorMask, hm] at hk
      | some a =>
        by_cases ha : σ a = j
        · simp [nextDivisorMask, hm, ha] at hk
        · have hka : σ a = k := by simpa [nextDivisorMask, hm, ha] using hk
          subst k
          intro hkS
          obtain ⟨a', ha'S, ha'⟩ := Finset.mem_image.mp hkS
          have : a' = a := σ.injective ha'
          subst a'
          exact hvalid.1 i a hm ha'S
    | inr i =>
      cases i
      have hk' : j = k := by simpa [nextDivisorMask] using hk
      subst k
      exact hj
  · intro i l k hi hl
    cases i with
    | inl i =>
      cases l with
      | inl l =>
        cases hmi : m i with
        | none => simp [nextDivisorMask, hmi] at hi
        | some a =>
          cases hml : m l with
          | none => simp [nextDivisorMask, hml] at hl
          | some b =>
            by_cases ha : σ a = j
            · simp [nextDivisorMask, hmi, ha] at hi
            · by_cases hb : σ b = j
              · simp [nextDivisorMask, hml, hb] at hl
              · have hka : σ a = k := by simpa [nextDivisorMask, hmi, ha] using hi
                have hkb : σ b = k := by simpa [nextDivisorMask, hml, hb] using hl
                have hab : a = b := σ.injective (hka.trans hkb.symm)
                subst b
                exact congrArg Sum.inl (hvalid.2 i l a hmi hml)
      | inr l =>
        cases l
        cases hmi : m i with
        | none => simp [nextDivisorMask, hmi] at hi
        | some a =>
          by_cases ha : σ a = j
          · simp [nextDivisorMask, hmi, ha] at hi
          · have hka : σ a = k := by simpa [nextDivisorMask, hmi, ha] using hi
            have hkj : j = k := by simpa [nextDivisorMask] using hl
            exact (ha (hka.trans hkj.symm)).elim
    | inr i =>
      cases i
      cases l with
      | inl l =>
        cases hml : m l with
        | none => simp [nextDivisorMask, hml] at hl
        | some b =>
          by_cases hb : σ b = j
          · simp [nextDivisorMask, hml, hb] at hl
          · have hkb : σ b = k := by simpa [nextDivisorMask, hml, hb] using hl
            have hkj : j = k := by simpa [nextDivisorMask] using hi
            exact (hb (hkb.trans hkj.symm)).elim
      | inr l => cases l; rfl


/-- Present singleton masks use the same successor operation as general
optional coordinate masks. -/
theorem successorMask_singleton (σ : Fin n ≃ Fin n) (j : Fin n)
    (o : Option (Fin n)) :
    HironakaG4OptionalBoundaryTransform.successorMask σ j (o.map (fun k => {k})) =
      ((o.bind fun k => if σ k = j then none else some (σ k)).map (fun k => {k})) := by
  classical
  cases o with
  | none => rfl
  | some k =>
    by_cases h : σ k = j
    · simp [HironakaG4OptionalBoundaryTransform.successorMask, h]
    · simp [HironakaG4OptionalBoundaryTransform.successorMask, h, Ne.symm h]

/-- Off the centre, old coordinates are unchanged and the new exceptional
member is absent. -/
theorem offCentreDivisorMask_valid {ι : Type*} (S : Finset (Fin n))
    (m : ι → Option (Fin n)) (hvalid : DivisorMasksValid S m) :
    DivisorMasksValid S (Sum.elim m (fun _ : Unit => none)) := by
  constructor
  · intro i k hk
    cases i with
    | inl i => exact hvalid.1 i k hk
    | inr i => cases i; simp at hk
  · intro i j k hi hj
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hvalid.2 i j k hi hj)
      | inr j => cases j; simp at hj
    | inr i => cases i; simp at hi

end Hironaka.HironakaG4OptionalDivisorMasks
