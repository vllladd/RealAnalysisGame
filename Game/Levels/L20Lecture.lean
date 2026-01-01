import Game.Levels.L20Levels.L01
import Game.Levels.L20Levels.L02
import Game.Levels.L20Levels.L03
import Game.Levels.L20Levels.L04

World "Lecture20"
Title "Lecture 20: Function Limits"

Introduction "
# Lecture 20: Function Limits

**SIMPLICIO:** FUNCTIONS!!!

**SOCRATES:** Oh please don't shout, I'm standing right here.

**SIMPLICIO:** Sorry! I just got a little over excited that we're moving on to functions.
Please tell me about them!

**SOCRATES:** Ah, right. Very good. Let's start at the beginning. What's the first thing you
learn in Calculus?

**SIMPLICIO:** Hmmm. The derivative?

**SOCRATES:** Ok, we can see about starting there. Tell me, what does it mean to
compute the derivative of a function $f : \\R \\to \\R$ at some point $x = c$.

**SIMPLICIO:** Well, it's the slope of the tangent line.

**SOCRATES:** Yes, of course; I mean, what expression are you trying to evaluate?

**SIMPLICIO:** Oh! I remember: it's the limit as $h \\to 0$ of
$(f(x+h)-f(x)) / h$.

**SOCRATES:** Which word there is problematic?

**SIMPLICIO:** Ah, of course; \"limit\"! We don't know yet what limits are for functions. And I already know from experience that
you can't just stick in $h=0$, since both the numerator and denominator vanish.

**SOCRATES:** Right. So we need to figure out what it means for a limit of a *function* to exist. Let's think about this carefully. What do we want to be true when we write $\\lim_{x \\to c} f(x) = L$?

**SIMPLICIO:** Well, we want $f(x)$ to get close to $L$ when $x$ gets close to $c$.

**SOCRATES:** Exactly! Now, do you remember our Engineer and Machinist from when we discussed sequence limits?

**SIMPLICIO:** Yes! The Engineer specified a tolerance $\\varepsilon > 0$ for how close the output needed to be, and the Machinist replied with how many steps $N$ were needed to guarantee that tolerance.

**SOCRATES:** Perfect! Now with functions, there's a beautiful twist. The Engineer still specifies a tolerance $\\varepsilon > 0$ for the output—that is, we want $|f(x) - L| < \\varepsilon$. But what do you think the Machinist's response should be this time?

**SIMPLICIO:** Hmm. With sequences, the Machinist said \"run the process for at least $N$ steps.\" But with functions, we don't have \"steps\"... we have values of $x$.

**SOCRATES:** Precisely! So instead of saying \"wait $N$ steps,\" how should the Machinist respond?

**SIMPLICIO:** Oh! So the Machinist needs to give a tolerance on the *input* side, not a number of steps. So he needs to say something like: \"make sure your input $x$ is within distance $\\delta$ of the target point $c$\"?


**SOCRATES:** Exactly! The conversation goes like this:

- **Engineer:** \"I need $f(x)$ to be within $\\varepsilon$ of $L$.\"
- **Machinist:** \"No problem! Just make sure your input $x$ is within distance $\\delta$ of $c$, and I'll guarantee your output tolerance.\"

And just like with sequences, we say the limit exists if this conversation can continue for *any* tolerance $\\varepsilon > 0$ the Engineer demands—the Machinist can always respond with some appropriate $\\delta > 0$.

**SIMPLICIO:** So the definition would be: for every $\\varepsilon > 0$, there exists a $\\delta > 0$ such that if $|x - c| < \\delta$, then $|f(x) - L| < \\varepsilon$?

**SOCRATES:** Beautifully stated! Yes, that's *almost* it. Let's write out what you said formally:

$$\\lim_{x \\to c} f(x) = L \\text{ means: } \\forall \\varepsilon > 0, \\exists \\delta > 0, \\forall x, |x - c| < \\delta \\Rightarrow |f(x) - L| < \\varepsilon$$

This is called an $\\varepsilon$-$\\delta$ definition. There's only one problem with this definition.

**SIMPLICIO:** Hmm. I really don't see, what's wrong?

**SOCRATES:** Well, think again back to informal calculus. What does it mean for a function
$f : \\R \\to \\R$
 to be
*continuous* at $x=c$.

**SIMPLICIO:** Ok, that's when $\\lim_{x \\to c}f(x)$ exists, and is actually equal to the value of
$f(c)$.

**SOCRATES:** Yes, exactly! Remember when we spoke of derivatives, we don't want to evaluate
the limit when $h$ is literally equal to zero, where we get $0 / 0$. But look
again at your definition. Where do you ensure that?

**SIMPLICIO:** Oh, I see! So we have to update the definition of a limit
to make sure that we don't actually allow $x = c$. So does this work?

$$\\lim_{x \\to c} f(x) = L \\text{ means: } \\forall \\varepsilon > 0, \\exists \\delta > 0, \\forall x \\ne c, |x - c| < \\delta \\Rightarrow |f(x) - L| < \\varepsilon$$

**SOCRATES:** That's the ticket! Some people write $0 < |x - c| < \\delta$, but I think
it'll be easier to just record $x \\ne c$ separately.
The set of such $x$ is called a *punctured neighborhood* of $c$—we've removed the center point. This way, the limit only cares about the behavior of $f$ *near* $c$, not *at* $c$.

**SIMPLICIO:** So this means $f(c)$ doesn't even need to be defined for the limit to exist?

**SOCRATES:** Correct! Remember when you started learning calculus and had to do things like find the limit of $f(x) = \\frac{x^2 - 1}{x - 1}$ as $x$ goes to $1$?


**SIMPLICIO:** Yes! This function is undefined at $x = 1$ (actually in Lean, as I've learned, it's perfectly well defined, since $0/0 = 0$ -- which means that it's certainly *not* continuous there...). But for $x \\neq 1$, we can factor: $f(x) = \\frac{(x-1)(x+1)}{x-1} = x + 1$. So $\\lim_{x \\to 1} f(x) = 2$, even though $f(1)$ doesn't exist!

And this is exactly like the derivative situation. The difference quotient $\\frac{f(x+h) - f(x)}{h}$ is undefined at $h = 0$, but we can still take the limit as $h \\to 0$.

**SOCRATES:** Precisely! You've understood the key point. The limit tells us about the *tendency* of a function as we approach a point, not necessarily what happens *at* that point.

**SIMPLICIO:** So to summarize:
- For limits, we assume $|x - c| < \\delta$ **and**  $x \\ne c$ (punctured neighborhood)
- For continuity, we only need $|x - c| < \\delta$; this is equivalent to:
the limit exists AND equals $f(c)$.

**SOCRATES:** You've got it! Let's go.

"
