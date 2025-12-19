import Game.Levels.L11Levels.L01_IsCauchyOfLim
import Game.Levels.L11Levels.L02_IsCauchyOfSum
import Game.Levels.L11Levels.L03_IsBddOfCauchy

World "Lecture11"
Title "Lecture 11: The Real Numbers I"

Introduction "
# Lecture 11: The Real Numbers I

**SOCRATES:** So far we've learned that *if* a sequence converges, then it's bounded, and moreover that any subsequence of it also converges to the same limit.

**SIMPLICIO:** Yeah, so what?

**SOCRATES:** And we saw that there can be sequences which do not themselves converge -- for example, $(-1)^n$ -- but which are bounded and have subsequences that do converge. The even-indexed terms, in this example, are all equal 1.

**SIMPLICIO:** What are you getting at?

**SOCRATES:** Well, what's a question that a mathematician might naturally ask given that information?

**SIMPLICIO:** You mean whether that always happens?

**SOCRATES:** Yes, something like that. Can you elaborate?

**SIMPLICIO:** Okay, I'll play along. You're trying to get me to formulate some kind of converse. If a sequence is bounded, then... it converges? No, that can't be right -- a bounded sequence can bounce around without converging, like $(-1)^n$ itself.

Ah, but maybe there's always *some* subsequence that converges? Hmm, but that can't be right either, since the sequence `aₙ = n` has no convergent subsequence -- it just escapes to infinity.

Oh! But wait, that sequence isn't bounded. Are you saying that if all I know about a sequence is that it's bounded, then there's always *some* subsequence that converges?

**SOCRATES:** Yes, precisely! This important fact is called the \"Bolzano-Weierstrass theorem\". But here's where it gets **really** subtle. Think about the sequence of fractions: `a (0) = 1 / 1`, `a (1) = 14 / 10`, `a (2) = 141 / 100`, `a (3) = 1414 / 1000`, ... getting closer and closer to $1.4142\\dots = \\sqrt 2$. The sequence is bounded (by $2$, to be crude), and even increasing, but its limit is not a rational number! So the Bolzano-Weierstrass theorem is not true for the rationals. As I warned you long ago, we'll have to eventually face the fact that we don't even know what the real numbers *are*. I think that time is now.

**SIMPLICIO:** Fine, I'm ready; tell me what they are.

**SOCRATES:** Unfortunately, it's rather complicated, and it'll take us some time to arrive at the answer, and to see why it *is* the answer. Let's take a step back. What would you *like* to be able to say about the real numbers?

**SIMPLICIO:** Well, I guess I'd like to say something like: they're the limits of their decimal expansions. So they're limits of rational sequences. Like, $\\sqrt{2}$ is the limit of that sequence you just mentioned: $1, 1.4, 1.41, 1.414, \\dots$

**SOCRATES:** Good! So you want to define a real number as \"the limit of a sequence of rationals.\" But remind me, what does it mean for a sequence to have a limit?

**SIMPLICIO:** It means that for all `ε > 0`, there exists an `N`, yadda yadda. The terms get arbitrarily close to some number $L$.

**SOCRATES:** And what is this mysterious number $L$? What *type* of number it?

**SIMPLICIO:** It's... a real number. Oh no.

**SOCRATES:** Exactly! We have a circular definition. We're trying to define the real numbers as limits of rational sequences, but the very notion of \"limit\" that we've been using presupposes that we already know what the real numbers are!

**SIMPLICIO:** So we're stuck? We can't define the real numbers?

**SOCRATES:** Sure seems like it! But this is where Cauchy had a **brilliant** insight. He realized the same thing you did: he can't use real numbers to define limits. He wants to say: \"$a_n$ gets closer and closer to $L$\" but without reference to $L$ itself. He needs to find *something else* that he can say $a_n$ gets close to.

**SIMPLICIO:** But he *has* nothing else.

**SOCRATES:** Exactly!! So...?

**SIMPLICIO:** So if all he has is the sequence $a_n$, and he has to compare it to something, and he has nothing else... Oh!!! He has to compare it to **itself**!?! But how?

**SOCRATES:** Wow, you got it! Yes, exactly, How?

**SIMPLICIO:** Well of course it's pointless to ask if `|aₙ - aₙ| < ε`. But... you could ask for `|aₙ - aₘ| < ε`, once `n` and `m` are *both* large enough?

**SOCRATES:** Ha, you did it! Yes, exactly, if $a_n$ and $a_m$ are both within $\\varepsilon$ of **each other**, that should be a substitute for convergence.

**SIMPLICIO:** That's so clever! So instead of saying \"the sequence converges to $L$,\" we say \"the terms of the sequence get arbitrarily close to each other\"?

**SOCRATES:** Precisely. Can you make this formal, using `ε`'s and `N`'s?

**SIMPLICIO:** I think so. I guess we should say that a sequence $a_n$ has a limit if: for every $\\varepsilon > 0$, there exists an $N$ such that for all $m, n \\geq N$, we have $|a_m - a_n| < \\varepsilon$.

**SOCRATES:** Beautiful! But since we already have a different meaning for the notion of  \"has a limit\", we'll call this property \"Cauchy\". So we say that **a sequence is Cauchy** if, as you said:

`∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε`

(It will be very convenient later to know which of `m` and `n` is bigger, instead of needing to break into cases;
 so we can just say `m ≥ n`.)

This is one of the most important definitions in **all of mathematics**.
It appears not only here in real analysis, but also in higher arithmetic when building the p-adic numbers, in functional analysis when studying Banach spaces and Hilbert spaces, and in topology and geometry when \"completing\" metric spaces. Anywhere mathematicians want to talk about  \"convergence\" but without knowing *a priori* where things converge *to*, they reach for a version of Cauchy's definition.

But before we return to the real numbers, let's first get more familiar
with this definition and what it can do.

**SIMPLICIO:** I like it; let's go!

"
