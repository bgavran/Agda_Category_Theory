# Formalization of Category Theory in Agda

I find that I often make simple, avoidable errors when reasoning about mathematics.
This is mostly because information in processed in the mind in a fuzzy, often error-prone way, and not as rigorously as we can process it today in modern computers.
Given that _we have_ these modern computers, it seems foolish not to use their power.

This is why in this repository I'm using the power of the dependently typed system of Agda to explicitly write down and systematically check the constructions I'm using in my work (constructions which are of mostly category-theoretic nature).

In a sense, I'm hoping to outsource a part of my cognition to the type-checker and - together with this type-checker - I'm hoping to become a part of a system that's a better mathematician than me alone.
As such this repository is a long-term investment into my mathematical career.
It's a Work In Progress with many rough edges all around.

> Hopefully, the structures specified in this repository will closely mirror those in my mind.

---

In order to be more efficient at moving towards the goal of understanding [fundamental principles of intelligence](https://www.brunogavranovic.com/about.html), I realized I need to be more efficient at rigorous mathematical reasoning. I often make [simple, avoidable errors](https://twitter.com/bgavran3/status/1166852731899957249) that could be eliminated by the usage of type system, much in the same way in programming the usage of a type system eliminates whole classes of bugs.

What were my previous endeavors of "playing around with proof assistants" are now starting to become serious considerations, especially after watching [Voevodsky's talk](https://www.youtube.com/watch?v=E9RiR9AcXeE) on the same topic. He seems to come to the conclusion that using proof assistants, as we scale up our mathematical endeavours, will become the only manageable way to do mathematics. I've assembled a list of most important paragraphs from the slides in his linked talk.

> Mathematical research currently relies on a complex system of mutual trust based on reputations. By the time Simpson's paper appeared, both Kapranov and I had strong reputations. Simpson's paper created doubts in our result, which led to it being unused by other researchers, but no one came forward and challenged us on it. (slide @20:46)

> But to do the work at the level of rigor and precision I felt was necessary would take an enormous amount of effort and would produce text that would be very difficult to read. And who would ensure that I did not forget something and did not make a mistake, if even the mistakes in much more simple arguments take years to uncover? 

> It soon became clear that the only long-term solution to the problems that I encountered is to start using computers in the verification of mathematical reasoning. (slide @26:00)

> Formulating mathematical reasoning in a language precise enough for a computer to follow meant using a foundational system of mathematics not as a standard of consistency applied only to establish a few fundamental theorems, but as a tool that can be employed in everyday mathematical work. (slide @32:50)

> I now do my mathematics with a proof assistant and do not have to worry all the time about mistakes in my arguments or about how to convince others that my arguments are correct

> But I think that the sense of urgency that pushed me to hurry with the program remains. Sooner or later computer proof assistants will become the norm, but the longer this process takes the more misery associated with mistakes and with unnecessary self-verification the practitioners will have to endure. (slide @47:37)

To put it in more practical terms, I believe the combination of me and a proof assistant is better mathematician than just me - after an initial investment of time to learn this tool. 
One more reason is that mathematical work is not done in isolation. If we want to actually apply our mathematical solutions at one point, we would need to formally write them down, implement them and verify them - why not do it sooner (and potentially find errors in our reasoning), rather than later, after we have already built up on these potentially erroneous results?

In other words, I believe I can be of more use once I write down all these mathematical structures in a sufficiently expressive type-checked language and confirm I actually understand them. If you don't think this is something that can be done, just look at the depth and breadth of the official [Agda category theory library](https://github.com/agda/agda-categories/tree/master/Categories).

Proof assistants are also thought of as tools that only help with abstract mathematical reasoning, unusable in the "real world of programming". Recent projects such as [Idris](https://www.youtube.com/watch?v=DRq2NgeFcO0) show us that this is not the case. They show us that we can enjoy the benefits of modern proof assistants while interacting with and reasoning about the real world.

---

Development of this library is guided by the design choices found in the official [Agda category theory library](https://github.com/agda/agda-categories/tree/master/Categories).

Many of the constructions are similar, due to the simple nature of these constructions. However, special care is taken to make as many arguments as implicit as it is sensible to do so, mirroring the way we _reason_ about these implicit arguments. 


Miscellaneous:
* To denote function composition `λ x → g(f(x))` instead of `g ∘ f` I reverse the order of arguments and use the filled circle as the symbol: `f ● g`. This has proven to be an effective measure for reducing the cognitive load when reasoning about complex chains of compositions.
* There exist some type-holes which I use, but haven't provided proofs of yet.
