/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

set_option warn.sorry false

/-!
# Chapter 7 Quiz

## Question 2
-/

namespace Question02

/-- An inductive type with a finite, enumerated list of days of the week. -/
inductive DayOfWeek where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

namespace DayOfWeek

/-- If `d` is a weekday, `DayOrEnd d` is the type of vectors with five days of the week; otherwise,
it's the type of vectors with two days of the week. -/
def DayOrEnd (d : DayOfWeek) : Type :=
  match d with
  | sunday    => Vector DayOfWeek 2
  | monday    => sorry
  | tuesday   => sorry
  | wednesday => sorry
  | thursday  => sorry
  | friday    => sorry
  | saturday  => sorry

/-- If `d` is a weekday, `listDayOrEnd d` is the vector with weekdays; otherwise, it's the vector
with the days in the weekend. -/
def listDayOrEnd (d : DayOfWeek) : DayOrEnd d :=
  match d with
  | sunday    => #v[sunday, saturday]
  | monday    => sorry
  | tuesday   => sorry
  | wednesday => sorry
  | thursday  => sorry
  | friday    => sorry
  | saturday  => sorry

end DayOfWeek

end Question02

/-!
## Question 3
-/

namespace Question03

namespace Bool

/-- Boolean “or”, also known as disjunction. -/
def or (a b : Bool) : Bool :=
  sorry

/-- Boolean “and”, also known as conjunction. -/
def and (a b : Bool) : Bool :=
  sorry

/-- Boolean negation, also known as Boolean complement. -/
def not (a : Bool) : Bool :=
  sorry

/-- `Bool.not_not`. -/
theorem not_involutive (a : Bool) : not (not a) = a :=
  sorry

/-- `Bool.and_comm`. -/
theorem and_commutative (a b : Bool) : and a b = and b a :=
  sorry

end Bool

end Question03

/-!
## Question 4
-/

namespace Question04

def Function.partComp {α : Type u} {β : Type v} {γ : Type w} (f : β → Option γ) (g : α → Option β)
    (x : α) : Option γ :=
  sorry

end Question04

/-!
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

/-!
## Question 6
-/

namespace Question06

def Nat.Odd : Type := sorry

example : Nat.Odd := sorry
example : Nat.Odd := sorry
example : Nat.Odd := sorry

end Question06
