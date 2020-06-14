import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 7: Hypotheses

In the Lean editor mode,
when a cursor is in the middle of a tactic proof,
Lean reports on the current *proof state*.
A typical proof state in Lean might look as follows:

    ```1 goal
    x y : ℕ,
    h₁ : prime x,
    h₂ : ¬even x,
    h₃ : y > x
    ⊢ y ≥ 4```

The lines before the one that begins with `⊢` denote the *context*:
they are the objects and assumptions currently at play.
In this example, these include two objects, `x` and `y`,
each a natural number.
They also include three assumptions,
labelled `h₁`, `h₂`, and `h₃`.
In Lean, everything in a context is labelled with an identifier.
You can type these subscripted labels as `h\1`, `h\2`, and `h\3`,
but any legal identifiers would do:
you can use `h1`, `h2`, `h3` instead,
or `foo`, `bar`, and `baz`.
The last line represents the *goal*,
that is, the fact to be proved.
Sometimes people use *target* for the fact to be proved,
and *goal* for the combination of the context and the target.
In practice, the intended meaning is usually clear.

You an also use `rw` with facts from the local context.
-/

/- Lemma : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
lemma example7 (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
begin [maths_in_lean_game]
  rw h',
  rw ←mul_assoc,
  rw h,
  rw mul_assoc
  
end

end calculating -- hide