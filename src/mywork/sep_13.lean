namespace implies

axioms (P Q : Prop)

def if_P_is_true_so_is_Q : Prop := P → Q

axiom p : P 
-- assume P is true > assume we have a proof of P (p)

axiom pq : P → Q
--assume we have a proof, pq, of P → Q

--intro for implies: assume premise, show conclusion
--elimination rule for implies: apply P → Q to a proof of P. 

#check pq
#check p

/-- 
Suppose P and Q are propositions and you know that P → Q
and that P are both true.
Show that Q is true.Pi
Proof: Apply the truth of P → Q to the truth of P
to derive the truth of Q.
Proof: By the elimination rule for → with pq 
applied to p.
-/
end implies

namespace all
/--
FOR ALL
-/

axioms (T: Type)
(P : T → Prop)
(propertyT : T → Prop)
(t : T)
(a : ∀ (x : T), P x)

--does little t have property P?
-- (every x of type T has property P? yes)

example : P t := a t
#check a t

end all

/- And and → 
Want a prood of P ∧ Q-/
axioms (P Q : Prop)

