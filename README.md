# $\sqrt{2}$ is Irrational
This repository contains a proof in the Lean 4 language that $\sqrt{2}$ is irrational. 

The proof sketch is as follows. 

## Proof (in English)
Assume for the sake of contradiction that $\sqrt{2}$ is rational. 

This means that there exist integers $a, b \in \mathbb{Z}$ such that 
$\sqrt{2} = \frac{a}b$. This further means that there exist $a', b' \in \mathbb{Z}$ 
such that $\gcd(a', b') = 1$ and $\frac{a}b = \frac{a'}{b'}$, since if there are any 
common prime factors between $a'$ and $b'$, we can cancel them out. 

Now, we can square both sides of $\sqrt{2} = \frac{a'}{b'}$ and do some rearranging to obtain 
$2 {b'}^2 = {a'}^2$. We have two cases to consider. 

* Case 1 ($a'$ is even): In this case, there exists some $k_a$ such that $2 k_a = a$, giving
  $2 {b'}^2 = 4 k_a^2$. This further means that ${b'}^2 = 2 k_a^2$, which means that $b'$
  is even as well, giving us a contradiction on $\gcd(a', b') = 1$ (the gcd is at least 2). 
* Case 2 ($a'$ is odd): In this case, there exists some $k_a$ such that $2 k_a + 1 = a$, giving
  $2 {b'}^2 = 4 k_a^2 + 4 k_a + 1$. Finally, this means that 
  $2 {b'}^2 = 2 (2 k_a^2 + 2 k_a) + 1$, 
  but this means that the left hand side is even, but the right hand side is odd, giving us 
  a contradiction. 
  
In both cases, we arrive at a contradiction for the assumption that $\sqrt{2}$ is rational, 
which must mean that $\sqrt{2}$ is irrational. 

## Motivation
Lean 4 is fun. I am very bullish in the future of theorem provers such as lean 4, given that
we need quick and reliable verification in the future if the output of generative models is to 
be trusted for more performance or correctness sensitive applications. 

This particular problem has been highlighted in the 
[100 problems in lean](https://leanprover-community.github.io/100.html) page as an exercise 
to gain familiarity with the theorem prover. 

