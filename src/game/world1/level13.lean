import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 13: `calc` keyword

Let's try some more examples. The theorem `two_mul a` says
that `a + a = 2 * a`. The theorems `add_mul` and `mul_add`
express the distributivity of multiplication over addition,
and the theorem `add_assoc` expresses the associativity of addition.
Use the `#check` command to see the precise statements.
-/

variables a b : ℝ

/- Example : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin [maths_in_lean_game]

  rw [mul_add, add_mul, add_mul],
  rw [←add_assoc, add_assoc (a * a)],
  rw [mul_comm b a, ←two_mul]

end

/-Whereas it is possible to figure out what it going on in this proof
by stepping through it in the editor,
it is hard to read on its own.
Lean provides a more structured way of writing proofs like this
using the `calc` keyword.
-/

variables a b : ℝ

/- Example : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin [maths_in_lean_game]
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
          by rw [mul_add, add_mul, add_mul]
  ... = a * a + (b * a + a * b) + b * b :
          by rw [←add_assoc, add_assoc (a * a)]
  ... = a * a + 2 * (a * b) + b * b     :
          by rw [mul_comm b a, ←two_mul]
end

/-
Notice that there is no more `begin ... end` block:
an expression that begins with `calc` is a *proof term*.
A `calc` expression can also be used inside a tactic proof,
but Lean interprets it as the instruction to use the resulting
proof term to solve the goal.

The `calc` syntax is finicky: the dots and colons and justification
have to be in the format indicated above.
Lean ignores whitespace like spaces, tabs, and returns,
so you have some flexibility to make the calculation look more attractive.
One way to write a `calc` proof is to outline it first
using the `sorry` tactic for justification,
make sure Lean accepts the expression modulo these,
and then justify the individual steps using tactics.

Try inserting this code block
```
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
    begin
      sorry
    end
  ... = a * a + (b * a + a * b) + b * b : by sorry
  ... = a * a + 2 * (a * b) + b * b     : by sorry
```
and filling in the `sorry`s yourself!
-/

/- Lemma : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
lemma example13 : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin [maths_in_lean_game]
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) :
    begin
      sorry
    end
  ... = a * a + (b * a + a * b) + b * b : by sorry
  ... = a * a + 2 * (a * b) + b * b     : by sorry
end

end calculating