/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

set_option warn.sorry false

/-!
# Chapter 7 Quiz

## Question 15
-/

namespace Question15

namespace Nat

mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end

theorem odd_one : Odd 1 :=
  sorry

theorem even_two : Even 2 :=
  sorry

end Nat

end Question15

/-!
## Question 16
-/

namespace Question16

inductive FinTree (α : Type u) where
  | mk : α → List (FinTree α) → FinTree α

/-- a finite tree that has nodes labelled by natural numbers and corresponds to the following ASCII
art:
```
     0
   / | \
  1  2  3
 / \     \
4   5     6
```
-/
def q16 : FinTree Nat :=
  sorry

end Question16
