--REVIEW INTRODUCTION AND ELIMINATION RULES FOR EXISTS 

--It is true that if not everyone likes themselves, then there is someone who doesnt like themself?

axioms
  (Person : Type)
  (Likes : Person → Person → Prop)
  --likes is a binary relation 

  example :
  --if its not the case that everyone likes themselves, then there is some person p
  --that doesnt like themself (solve it forwards and backwards)
  ¬ (∀ p : Person, Likes p p) ↔ 
  ∃ p : Person, ¬ Likes p p := 
  begin
    apply iff.intro _ _,
    assume h,
    --apply excluded middle to any proposition p, get a proof of p or not p
    have f := classical.em (∃ (p : Person), ¬ Likes p p),
    --proof of disjunction. use cases
    cases f, --either someone dislikes themself, or not. we can do casees on props
    --case 1: there IS someone who dislikes themself
    assumption,
    --case 2: there IS NOT someone who dislikes themself
    --introduce an assumption into the environment for which we dont have a proof
    have contra : ∀ (p : Person), Likes p p := _,
    --we're just assuming that everyone likes themself. to be proved later
    contradiction,
    --now we have to prove contra is true
    assume p,

    --same trick again
    have g := classical.em(Likes p p),
    cases g, --goal is true
    exact g,
    have a : ∃ (p : Person), ¬ Likes p p := exists.intro p g,
    contradiction,

    --backward
    assume h,
    cases h with p l,
    assume a,
    have d := a p,
    contradiction,
  end 