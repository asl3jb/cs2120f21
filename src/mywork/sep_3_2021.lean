/--
Theorem: Equality is Symmetric.
--/

theorem eq_symm : 
  ∀ (T : Type) (x y : T), x = y → y = x := 
  begin
    assume (T : Type), 
    assume (x y : T),
    assume (e : x = y),
    rw e,
  end

  /--
  Theorem: equality is symmetric. in other words,  
  ∀ (T : Type) (x y : T), x = y → y = x := x.

  Proof: first we assume that T is any type and we
  have objects x and y of this type. what remains 
  to be shown is that x = y → y = x. to prove this,
  we'll assume the premise that x = y, and in this
  context we need to prove y = x. by the axiom of
  substitutability of equals, and using the fact that
  x = y, we can rewrite x in the goal as y, yielding
  y = y as our new proof goal. but this is already 
  true by the axion of reflexivity of equality. QED.
  -/

  /-
  Prove that equality is transitive.
  -/

  theorem eq_trans :
    ∀ (T : Type) (x y z : T), x = y → y = z → x = z :=
    begin
      assume ( T : Type),
      assume ( x y z : T),
      assume (e1 : x = y),
      assume (e2 : y = z),
      rw e1,
      exact e2,
    end