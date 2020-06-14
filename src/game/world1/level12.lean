import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 11: `section` and `#check`

We can delimit the scope of the declaration by putting it
in a `section ... end` block.

Finally, Lean provides us with a command
to determine the type of an expression:
-/

section
variables a b c : ℝ

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm
#check @mul_comm

end

/-
The `#check` command works for both objects and facts.
In response to the command `#check a`, Lean reports that `a` has type `ℝ`.
In response to the command `#check mul_comm a b`,
Lean reports that `mul_comm a b` is a proof of the fact `a * b = b * a`.
The command `#check (a : ℝ)` states our expectation that the
type of `a` is `ℝ`,
and Lean will raise an error if that is not the case.
We will explain the output of the last three `#check` commands later,
but in the meanwhile, you can take a look at them,
and experiment with some `#check` commands of your own.
-/

end calculating -- hide