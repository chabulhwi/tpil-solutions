/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 7

## Injections
-/

namespace Function

variable {α : Sort u} {β : Sort v} {f : α → β}

namespace Injective

/-- An injection is a function with the following property: if two elements of the range are the
same, they are assigned to the same element of the domain. -/
theorem def_iff : Injective f ↔ ∀ ⦃x y : α⦄, f x = f y → x = y :=
  Iff.rfl

/-- No two different elements of the domain have the same function value. -/
theorem corollary01 (hinj : Injective f) : ¬∃ (x y : α), x ≠ y ∧ f x = f y := by
  intro ⟨x, y, hne, hfun⟩
  have heq : x = y := hinj hfun
  contradiction

/-- Two different elements of the domain have different function values. -/
theorem corollary02 (hinj : Injective f) {x y : α} (h : x ≠ y) : f x ≠ f y := by
  intro hfun
  have heq : x = y := hinj hfun
  contradiction

open Classical

/-- An alternative definition of an injection. This requires classical logic. See
`Function.Injective.corollary01`. -/
theorem def01 : Injective f ↔ ¬∃ (x y : α), x ≠ y ∧ f x = f y := by
  refine ⟨corollary01, fun h ↦ ?_⟩
  simp only [not_exists, not_and, ← ne_eq, Decidable.not_imp_not] at h
  assumption

/-- Another definition of an injection. This requires classical logic. See
`Function.Injective.corollary02`. -/
theorem def02 : Injective f ↔ ∀ ⦃x y : α⦄, x ≠ y → f x ≠ f y := by
  refine ⟨corollary02, fun h ↦ ?_⟩
  simp only [Decidable.not_imp_not] at h
  assumption

end Injective

end Function
