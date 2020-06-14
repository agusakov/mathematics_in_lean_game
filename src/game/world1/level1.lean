import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 1: The `rw` tactic.

We generally learn to carry out mathematical calculations
without thinking of them as proofs.
But when we justify each step in a calculation,
as Lean requires us to do,
the net result is a proof that the left-hand side of the calculation
is equal to the right-hand side.

In Lean, stating a theorem is tantamount to stating a goal,
namely, the goal of proving the theorem.
Lean provides the `rewrite` tactic, abbreviated `rw`,
to replace the left-hand side of an identity by the right-hand side
in the goal. If `a`, `b`, and `c` are real numbers,
`mul_assoc a b c`  is the identity `a * b * c = a * (b * c)`
and `mul_comm a b` is the identity `a * b = b * a`.
In Lean, multiplication associates to the left,
so the left-hand side of `mul_assoc` could also be written `(a * b) * c`.
However, it is generally good style to be mindful of Lean's
notational conventions and leave out parentheses when Lean does as well.

Let's try out `rw`.
-/

/- Lemma : no-side-bar
-/
lemma example1 (a b c : ℝ) : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  rw mul_assoc b a c

end

/-
As you move your cursor past each step of the proof,
you can see the goal of the proof change.
The `import` line at the beginning of the example
imports the theory of the real numbers from `mathlib`.
For the sake of brevity,
we generally suppress information like this when it
is repeated from example to example.
-/
  
end calculating -- hide