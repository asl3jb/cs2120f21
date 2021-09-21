/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.

to prove x ∨ y → z
you need to prove x → z AND y → z
-/

example : true := true.intro

example : false := _    -- trick question? why? Yes

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

example : ∀ (P : Prop), P ∧ P ↔ P := --if P and P is true
begin
assume p,
apply and.intro p
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
end


