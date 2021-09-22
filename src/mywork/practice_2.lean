/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.

to prove x ∨ y → z
you need to prove x → z AND y → z
-/

--QUESTION 1
example : true := true.intro

--QUESTION 2
example : false := _    -- trick question. no proof for false

--QUESTION 3
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
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  assume h,
  apply and.elim h,
  assume p,
  assume qr,
  
end

--QUESTION 8
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

end

--QUESTION 9
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
example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
assume P,
apply iff.intro _ _,
assume porfalse,
apply or.elim porfalse,
assume p1,
exact p1,
--first goal accomplished
assume f,


end

--QUESTION 13
example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

--QUESTION 14
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
end


