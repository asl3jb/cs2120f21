import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.

1) Since all the elements in set L are the same, 
they are already a subset of itself.
The intersection of set L with itself is L since every
element of L is in itself. 
-/
theorem eq_is_refl : L ∩ L → L :=

begin

end

/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.


2) The order of the set does not change their relation to each other,. 
Thereforefore the union operator on sets is commutative.
-/

example: Π {α : Type}  ⦃x y⦄, (x ∪ y = y ∪ x)
begin 
end



/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.

3) If x is a subset of y (x ⊆ y), then every element of 
x is related to y, which makes every element reflexive. Additionally,
if x is a subset of y, and y=z then x=z since they are related, 
making the ⊆ transitive.
-/


/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.

4) ∪ is associative since the order of the two sets
does not matter. the expression because the outcome 
will be all the elements in both the set and will be 
the same regardless of which set comes first. 
 ∩ is also associative since it does not matter 
the order of the two sets in the expression; the outcome 
will be a new set with the all elements from both sets.
-/
(α β : Type)
  (x : α → Prop)
  (y : β → Prop)
example: Π {α : Type}  ⦃x y⦄, (x ∪ y = y ∪ x) v (x ∩ y = y ∩ x):=
begin
end 


/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among many other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/


/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/