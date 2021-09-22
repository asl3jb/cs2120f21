/-
Allison Lai asl3jb
  HOMEWORK 3
  
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.

to prove x ∨ y → z
you need to prove x → z AND y → z
-/

--QUESTION 1
/-Using the introduction rule for true, it is already known/proven
 true is true.-/
example : true := 
true.intro

--QUESTION 2
/-This is a trick question because there is no way to prove false. 
The proof does not exist-/
example : false := _   

--QUESTION 3
/-Proof. We assume that P is an arbitrary 
but specific proposition, and then use the iff introduction rule to split 
problem into two parts. What now
remains to be proved is P ∨ P → P and P → P ∨ P. We can
construct a proof of this proposition by applying
the and elimination rule to a proof of (P \or P). We can then assume that P is true.
Since P → P, we can use 'exact' here and have finished the forward goal.
We can also assume and exact p for the backwards proof and after this, we
need to show that P ∨ P is true. 
But this is easily done by the application of
or introduction rule to either side of P ∨ P. QED. -/
example : ∀ (P : Prop), P ∨ P ↔ P := /-p or p implies p-/
begin
  assume P,
  apply iff.intro _ _,
  --forward P ∨ P → P
  assume porp,
  apply or.elim porp,
  --left disjunct is true
  assume p, 
  exact p,
  --right disjunct is true
  assume p,
  exact p,
  --backwards: assume P, show that P or P is true
  assume p,
  exact or.intro_left P p,
end

--QUESTION 4
/-Proof. We assume that P is an arbitrary 
but specific proposition, and then use the iff introduction rule to split 
problem into two parts. What now
remains to be proved is P ∧ P → P and P → P ∧ P. First, we can assume
that P ∧ P itself is true. We can then break down this proposition by applying
the and elimination rule to the right side of a proof of (P ∧ P).
For the second goal, we can assume P is true.
After this, we need to show that P ∧  P is true. Since we have a proof of P
already, this is easily done by the application of
and introduction rule of P ∧ P and we are left to prove P, which
has already been done. QED. -/
example : ∀ (P : Prop), P ∧ P ↔ P := --if P and P is true
begin
assume P,
apply iff.intro _ _,
assume pandp,
apply and.elim_right pandp,
assume p,
apply and.intro p,
exact p,
end

--QUESTION 5
/-Proof. We assume that P  and are arbitrary 
but specific propositions, and then use the iff introduction rule to split 
problem into two parts. What now
remains to be proved is P ∨ Q → Q ∨ P and Q ∨ P → ∧ P ∨ Q. First, we can assume
that P ∨ Q itself is true with porq. We can then apply
the or elimination rule to porq. Then, we can assume P (p). What remains to
be proven is P ∨ Q, and we can then apply the or introduction rule to get rid
of Q and we are left with P to prove. This can be done by 'exact' since we 
already have a proof of P.
For the second goal, we can repeat the process above, but with Q. First,
we assume Q. Then, we apply the elimination rule to the left side, and are
left to prove Q and this is done with exact again.
After this, we need to split the last goal into parts again. We can assume
h (Q ∨ P) is true and then apply the or elimination rule to h. This leads 
to a similar setup for the first two goals. Now, we can assume Q again
and use the or intro rule to get goal to prove Q.
The same can be done for the P side. QED. -/
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
assume P Q,
apply iff.intro _ _,
assume porq,
apply or.elim porq,
assume p,
apply or.intro_right,
exact p,
--first goal accomplished
assume q,
apply or.intro_left,
exact q,
--second goal accomplished
assume h,
apply or.elim h,
assume q1,
apply or.intro_right,
exact q1,
assume p1,
apply or.intro_left,
exact p1,
end

--QUESTION 6
/-Proof. We assume that P and Q are arbitrary 
but specific propositions, and then use the iff introduction rule to split 
problem into two parts. What now
remains to be proved is P ∧ Q → Q ∧ P and Q ∨ P → P ∧ Q First, we can assume
that P ∧ Q itself is true. We can then break down this proposition by applying
the and intro rule to get a goal of P and a goal of Q. These can both be proven
by applying the and elimination rule to the right and left sides of pandq respectively.
For the last goal, we can assume Q ∧ P is true.
We can then repeat the process for the first goal, using and.intro
to split the goal into two parts and using the and elimination rule
for each side to obtain proofs for P and Q. QED. -/
example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume pandq,
  apply and.intro,
  apply and.elim_right pandq,
  apply and.elim_left pandq,
  --first and second goals accomplished
  assume h,
  apply and.intro,
  apply and.elim_right h,
  apply and.elim_left h,
end

--QUESTION 7
--I did not manage to solve this but will explain  what I did so far
/-Proof. We assume that P Q and R are arbitrary 
but specific propositions, and then use the iff introduction rule to split 
problem into two parts. What now
remains to be proved is P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R and P ∧ Q ∨ P ∧ R  → P ∧ (Q ∨ R).
First, we assume P ∧ (Q ∨ R). using the introduction rule for and, this can be 
broken down further. To obtain a proof of P, we can use the elimination rule on the
left side of pqr. However, the second goal of Q is not possible to solve with what
I have so far. -/
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  assume pqr,
  apply or.intro_left,
  apply and.intro,
  apply and.elim_left pqr,
  --goal 1  
end

--QUESTION 8
--I did not manage to solve this but will explain what I did so far
/-Proof. We assume that P Q and R are arbitrary 
but specific propositions, and then use the iff introduction rule to split 
problem into two parts. What now remains to be proved is 
P ∨ Q ∧ R → (P ∨ Q) ∧ (P ∨ R) and (P ∨ Q) ∧ (P ∨ R)  → P ∨ Q ∧ R.
First, we assume  P ∨ Q ∧ R as h. Then use the or elimination rule
to get 2 parts of this to prove. -/
example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  assume h,
  apply or.elim h,
  assume p,
  apply and.intro,
  apply or.intro_left,
  exact p,
  apply or.intro_left,
  exact p,
  --first and second goal accomplished
  assume qandr,
  apply and.intro,
  apply or.intro_right,
  apply and.elim_left qandr,
  --sub goal 1
end

--QUESTION 9
/-Proof. We assume that P and Q are arbitrary 
but specific propositions, and then use the iff introduction rule to split 
problem into two parts. What now
remains to be proved is P ∧ (P ∨ Q) → P and P → P ∧ (P ∨ Q) First, we can assume
that P ∧ (P ∨ Q) itself is true. We then get P → P ∧ (P ∨ Q).
Next, we assume P as p. What remains is P. We already have a proof of this, so use exact.
For the backwards goal, we need to solve P ∨ Q.
Since wealready have a proof of P, we can use thhe or intro rule on
the left side and then prove P using exact. QED. -/
example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume h,
  apply and.elim_left h,
  assume p,
  apply and.intro,
  exact p,
  --first goal accomplished
  apply or.intro_left,
  exact p,
end

--QUESTION 10
/-Proof. We assume that P and Q are arbitrary 
but specific propositions, and then use the iff introduction rule to split 
problem into two parts. What now
remains to be proved is P ∨ P ∧ Q /imp P and P →  P ∨ P ∧ Q. First, we can assume
that  P ∨ P ∧ Q is true. We can change P ∨ P into P → P with the or elimination rule.
This is easily proven by assuming P and using exact to show that P → P.
What remains to be proven is P ∧ Q. We can use the and elimination rule on
both sides to get p (P) and q(Q) and the we just need to prove P again.
Next, we need to prove P → P ∨ P ∧ Q. By assuming P agan and using the or
introduction rule to the left side (where the Ps are) we are left once again
with only P to prove. This can be done with exact.
 QED. -/
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
assume P Q, 
apply iff.intro _ _,
assume ppq,
apply or.elim ppq,
assume p,
exact p,
assume pandq,
have q : Q := and.elim_right pandq,
have p : P := and.elim_left pandq,
exact p,
--first goal accomplished
assume p1,
apply or.intro_left,
exact p1,
end

--QUESTION 11
/-Proof. We assume that P i8s an arbitrary
but specific proposition, and then use the iff introduction rule to split 
problem into two parts. What now
remains to be proved is P ∨ true → true and true → P ∨ true. First, we can assume
that P ∨ true is true. We can use true introduction rule to prove this.
Next, we assume true is true. What remains is P ∨ true. 
We can use the introduction rule to get rid of the left side, and all
that remains to be proven is true → true. We can use exact for this. QED. -/
example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
assume P,
apply iff.intro _ _,
assume portrue,
exact true.intro,
assume p,
apply or.intro_right,
exact p,
end

--QUESTION 12
/-Proof. We assume that P is an arbitrary
but specific proposition, and then use the iff introduction rule to split 
problem into two parts. What now
remains to be proved is P ∨ false → P and P → P ∨ false. First, we can assume
that P ∨ false is true. Using the elimination rule, we are left with a goal of P → P
which is easily proven with exact.
Next in order to prove something is false we just need to use case analysis
and show that there is nothing left to prove.
Finally we can prove P ∨ false with the or introduction rule to get a goal of P again.
 This is true by the axiom of equality.QED. -/
example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
assume P,
apply iff.intro _ _,
assume porfalse,
apply or.elim porfalse,
assume p,
exact p,
--first goal accomplished
assume f,
cases f,
--second goal accomplished
assume p,
apply or.intro_left,
exact p,
end

--QUESTION 13
/-Proof. We assume that P is an arbitrary
but specific proposition, and then use the iff introduction rule to split 
problem into two parts. What now
remains to be proved is P ∧  true → P and P → P ∧ true. First, we can assume
that P ∧ true is true.  We need to get a proof of P to solve this,
so we apply the elimination rule which allows ujs to get a proof of P.
What remains to be solved is P ∧ true. Using our proof of P and the and introduction
rule, we can apply ikt to this goal to get a goal of true. This is already true because
of the true introduction rule; anything true is true.
QED. -/
example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
assume P,
apply iff.intro _ _,
assume h,
apply and.elim_left h,
assume p,
apply and.intro p,
exact true.intro,
end

--QUESTION 14
/-Proof. We assume that P is an arbitrary
but specific proposition, and then use the iff introduction rule to split 
problem into two parts. What now
remains to be proved is P ∧ false → false and false → P ∨ ∧ false.
First, we assume P ∧ false. We need to get an assumptikon of false
for the rest of this problem so we use the elimination rule on the right
side of porfalse.
Finally, we assume f as false. In order to show there is no proof for false,
we can do case analysis. This turns up no goals left to solve so 
we do not have to do anything else.
 QED. -/
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
assume P,
apply iff.intro _ _,
assume porfalse,
apply and.elim_right porfalse,
assume f,
cases f,
end


