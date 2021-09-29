
/-
A simple predicate.
-/
def ev (n : ℕ) : Prop := n%2=0


/-
Introduction rule for exists
-/
example : exists (n : ℕ), ev n :=
begin
  --to prove something even, we need a witness such as even number 4.
  --then we need to prove 4 mod 2 is 0.
  --use eq.refl to show 0=0.
end

example : exists n, ev n := _


def pythagorean_triple (a b c : ℕ) : Prop :=
a*a + b*c = c*c
example : exists (a b c : ℕ), pythagorean_triple 3 4 5 := 
begin
unfold pythagorean_triple,
apply
end


example : ∀ (n : ℕ), ∃ (m : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro _,
  
end

example : ∀ (m : ℕ), ∃ (n : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro (2*m),
end

example : (∃ (n : nat), ev n) → true :=
begin
assume h,
cases h with v pf,
intros,
end

--elimination rule for exists
--the thing exists so you give it an arbitrary name. now we can use that name.