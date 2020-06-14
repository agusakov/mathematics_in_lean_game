import data.real.basic --imports the real numbers
import tactic.maths_in_lean_game -- hide
namespace calculating -- hide

/-
#Calculating

## Level 18: `ring` tactic

We close this section by noting that `mathlib` provides a
useful bit of automation with a `ring` tactic,
which is designed to prove identities in any ring.
-/

variables a b c d : ℝ

/- Example : no-side-bar
-/
example : (c * b) * a = b * (a * c) :=
    by ring

/- Example : no-side-bar
-/
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    by ring

/- Example : no-side-bar
-/
example : (a + b) * (a - b) = a^2 - b^2 :=
    by ring

/-
Try it out for yourself (you will need to make some rewrites first!)
-/

/- Lemma : no-side-bar
For all natural numbers $a$, we have
$$a + \operatorname{succ}(0) = \operatorname{succ}(a).$$
-/
lemma example15 (hyp : c = d * a + b) (hyp' : b = a * d) :
    c = 2 * a * d :=
begin [maths_in_lean_game]




    sorry
end

/-
The `ring` tactic is imported indirectly when we
import `data.real.basic`,
but we will see in the next section that it can be used
for calculations on structures other than the real numbers.
It can be imported explicitly with the command
`import tactic`.
-/

end calculating -- hide