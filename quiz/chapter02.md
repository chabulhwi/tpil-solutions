# Chapter 2 Quiz

## Question 1

Use the `#check` command to give the type of each expression listed below.

\(a\) `-2` \
\(b\) `3.14` \
\(c\) `'L'` \
\(d\) `"Lean"` \
\(e\) `[0, 1, 2]` \
\(f\) `1 + 1 = 2`

## Question 2

Use the `#eval` command to give the value of each expression listed below.

\(a\) `-3 / 5` \
\(b\) `Float.sin 0.0` \
\(c\) `Char.toNat 'L'` \
\(d\) `String.length "Lean"` \
\(e\) `List.tail [0, 1, 2]` \
\(f\) `1.0 + 1.0 == 2.0`

## Question 3

There's an error in the following code; fix the expression after the `#eval`
command to evaluate it.

```lean
namespace Question03

def f (x : Nat) := 2 * x - 1
#eval f(1)

end Question03
```

## Question 4

Use the `def` keyword to declare a new constant of each type listed below.

\(a\) `Bool → Bool` \
\(b\) `(Bool → Bool) → Bool` \
\(c\) `Bool → (Bool → Bool)` \
\(d\) `Bool → Bool → Bool`

## Question 5

Use the `def` keyword to declare a new constant of each type listed below.

\(a\) `Bool × Bool` \
\(b\) `(Bool × Bool) × Bool` \
\(c\) `Bool × (Bool × Bool)` \
\(d\) `Bool × Bool × Bool`

## Question 6

Give the value of each expression listed below.

\(a\) `Nat.succ 0` \
\(b\) `Nat.add 3 7` \
\(c\) `('L', 4).1` \
\(d\) `('L', 4).2`

## Question 7

Give the type of each expression listed below.

\(a\) `Bool → Bool` \
\(b\) `Bool × Bool`

## Question 8

Let `Type.id` be a function from `Type` to `Type`, defined as follows:

```lean
def Type.id : Type → Type := fun x : Type ↦ x
```

Give the type of the expression `Type.id Nat`.

## Question 9

Define a constant of each type listed below.

\(a\) `Prod (Type 0) (Type 1)` \
\(b\) `Type 2 → Type 3`

## Question 10

Define the following two universe-polymorphic functions, replacing each `sorry`
identifier with an actual definition.

```lean
namespace Question10

def f.{u, v, w} : Type u → Type v → Type w → Type (max u v w) :=
  sorry

def g.{u, v, w} : Type u → Type v → Type w → Type (max u v w) :=
  sorry

end Question10
```

## Question 11

Is the function `Type.id` of [Question 8](#question-8) universe-polymorphic?

## Question 12

Are the constants you defined in [Question 9](#question-9) universe-polymorphic?

## Question 13

Give the value of the expression `(λ x : Int => -x + 2) 3`.

## Question 14

Define a function that takes a natural number as input, and returns `true :
Bool` if the number is non-zero and `false : Bool` if the number is zero.

## Question 15

Is the expression `fun x : Nat ↦ x` a *constant* function?

## Question 16

Is the expression `fun x : Nat ↦ 0` the *identity* function on `Nat`?

## Question 17

Define the following function, replacing the `sorry` identifier with an actual
expression *containing* the arguments `f`, `g`, and `s`.

```lean
def q17 (f : List Char → Nat) (g : (List Char → Nat) → (String → Nat)) (s : String) : Nat :=
  sorry
```

## Question 18

Are the following functions alpha-equivalent?

* `fun (s : String) (n : Nat) ↦ String.drop s n`
* `fun (bulhwi : String) (cha : Nat) ↦ String.drop bulhwi cha`

## Question 19

Which of the following functions are alpha-equivalent?

```lean
namespace Question19

def a (n : Nat) := n ^ 2 + 1

def f (a : Nat → Nat) (n : Nat) := a (a n)
def g (b : Nat → Nat) (n : Nat) := b (b n)
def h (a : Nat → Nat) (n : Nat) := Question19.a (a n)

end Question19
```

## Question 20

Define a function that takes two natural numbers as input arguments, and returns
the one less than or equal to the other one.

You can type the less-than-or-equal-to sign `≤` with `\le`.

## Question 21

Why does the definition of `foo` below type check, but the definition of `bar`
doesn't?

```lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```
