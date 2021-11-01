import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:
  that relatest to β, then for all a of type α 
  when p is applied to a it implies q.
  Likewise, it also states that p is related to α
  and q is related to β 

-/


-- Give your formal proof here
begin
  assume h k,
  cases h with c d,
  cases k with e f,
  apply exists.intro _ _,
  have beta : β := c e,
  exact beta,
  apply d,
  exact f,
end
  

/- 
To start, we have two assumptions: one for the general function f
and another for a and b
We then do case analysis on each assumption where we find that
alhpa relates to beta and that alpha is proven,
-/