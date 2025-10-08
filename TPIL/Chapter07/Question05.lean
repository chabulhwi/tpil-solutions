/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

set_option warn.sorry false

/-!
# Chapter 7 Quiz

## Question 5
-/

namespace Question05

example : Inhabited Bool := sorry

example : Inhabited Nat := sorry

section

variable {α : Type u} {β : Type v}

example {inst1 : Inhabited α} {inst2 : Inhabited β} : Inhabited (α × β) :=
  sorry

example {inst : Inhabited β} : Inhabited (α → β) :=
  sorry

end

end Question05
