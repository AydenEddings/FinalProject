# FinalProject
Where I'll be placing the code for my final project

My final project code is Notes4/final.lean. In which I've proven that all cyclic groups are Abelian. I first define abelian groups and cyclic groups, 
  along with exponentiation. I use an axiom to relate multiplication and exponentiation, as this seemed the easiest way to implement exponents in Lean.
  
I then have a theorm "cyclic_is_abelian", of type 'CyclicGroup G -> AbelianGroup G. I need only prove commutivity as Lean has a built in "toGroup" based 
  on the way I defined CyclicGroup G.
  
I proved the commutativity law by defining g1 and g2, along with n1 n2, such that e^n1 = g1, and e^n2 = g2. I then used the calc tactic
  to prove that g1*g2 = g2*g1. This concluded that proof. Then I only needed to apply AbelianGroup.mk and that finished the proof.
  
