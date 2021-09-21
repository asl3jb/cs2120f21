-- ¬P (Negation)
--if ¬P is true, then there is no proof of P
/- to show that P has no proofs: if u assume thta P DOES have a proof,
then that is a contradiction > something impossible happens. therefore
there must be no proof of P. [we do this because there are no proofs of false]

false implies false: -/

example : false → false :=
begin
  assume f,
  exact f,
end

example : false → true :=
begin
  assume f,
  exact true.intro,
end

--this proposition is false because we don't have a proof for false
example : true → false :=
begin
  assume t,
  --stuck for now
end


/- PROOF FOR ¬P
For any proposition P, we define ¬P to be the proposition P → false
(***If there is a prof of P → false, then you can conclude ¬P.
This is the introduction rule for ¬ ***)-/

example : ¬ false :=
begin
assume f,
exact f,
end 

example : ¬ (0 = 1) :=
begin
  assume h,
  --no way to prove current goal
  cases h, --case analysis: nothing left to prove 
  --elimination rule for proof of false
end

theorem false_elim (P : Prop) (f : false) : P :=
begin
  exact false.elim f,
  --OR cases f,
end