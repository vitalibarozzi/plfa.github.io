---
src       : src/plfa/Equality.lagda
title     : "Equality: Equality and equational reasoning"
layout    : page
prev      : /Relations/
permalink : /Equality/
next      : /Isomorphism/
---

<pre class="Agda">{% raw %}<a id="171" class="Keyword">module</a> <a id="178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}" class="Module">plfa.Equality</a> <a id="192" class="Keyword">where</a>{% endraw %}</pre>

Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.


## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda, imports equality.  Since we define equality
here, any import would create a conflict.


## Equality

We declare equality as follows.
<pre class="Agda">{% raw %}<a id="728" class="Keyword">data</a> <a id="_≡_"></a><a id="733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">_≡_</a> <a id="737" class="Symbol">{</a><a id="738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#738" class="Bound">A</a> <a id="740" class="Symbol">:</a> <a id="742" class="PrimitiveType">Set</a><a id="745" class="Symbol">}</a> <a id="747" class="Symbol">(</a><a id="748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#748" class="Bound">x</a> <a id="750" class="Symbol">:</a> <a id="752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#738" class="Bound">A</a><a id="753" class="Symbol">)</a> <a id="755" class="Symbol">:</a> <a id="757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#738" class="Bound">A</a> <a id="759" class="Symbol">→</a> <a id="761" class="PrimitiveType">Set</a> <a id="765" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="778" class="Symbol">:</a> <a id="780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#748" class="Bound">x</a> <a id="782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#748" class="Bound">x</a>{% endraw %}</pre>
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equal to itself, and we have no other way of showing values
equal.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.

We declare the precedence of equality as follows.
<pre class="Agda">{% raw %}<a id="1449" class="Keyword">infix</a> <a id="1455" class="Number">4</a> <a id="1457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">_≡_</a>{% endraw %}</pre>
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.


## Equality is an equivalence relation

An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equality, via the
constructor `refl`.  It is straightforward to show symmetry.
<pre class="Agda">{% raw %}<a id="sym"></a><a id="1928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1928" class="Function">sym</a> <a id="1932" class="Symbol">:</a> <a id="1934" class="Symbol">∀</a> <a id="1936" class="Symbol">{</a><a id="1937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1937" class="Bound">A</a> <a id="1939" class="Symbol">:</a> <a id="1941" class="PrimitiveType">Set</a><a id="1944" class="Symbol">}</a> <a id="1946" class="Symbol">{</a><a id="1947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1947" class="Bound">x</a> <a id="1949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1949" class="Bound">y</a> <a id="1951" class="Symbol">:</a> <a id="1953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1937" class="Bound">A</a><a id="1954" class="Symbol">}</a>
  <a id="1958" class="Symbol">→</a> <a id="1960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1947" class="Bound">x</a> <a id="1962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="1964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1949" class="Bound">y</a>
    <a id="1970" class="Comment">-----</a>
  <a id="1978" class="Symbol">→</a> <a id="1980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1949" class="Bound">y</a> <a id="1982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="1984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1947" class="Bound">x</a>
<a id="1986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1928" class="Function">sym</a> <a id="1990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="1995" class="Symbol">=</a> <a id="1997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>
How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.

It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!

Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type.

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

This completes the definition as given above.

Transitivity is equally straightforward.
<pre class="Agda">{% raw %}<a id="trans"></a><a id="3672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3672" class="Function">trans</a> <a id="3678" class="Symbol">:</a> <a id="3680" class="Symbol">∀</a> <a id="3682" class="Symbol">{</a><a id="3683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3683" class="Bound">A</a> <a id="3685" class="Symbol">:</a> <a id="3687" class="PrimitiveType">Set</a><a id="3690" class="Symbol">}</a> <a id="3692" class="Symbol">{</a><a id="3693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3693" class="Bound">x</a> <a id="3695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3695" class="Bound">y</a> <a id="3697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3697" class="Bound">z</a> <a id="3699" class="Symbol">:</a> <a id="3701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3683" class="Bound">A</a><a id="3702" class="Symbol">}</a>
  <a id="3706" class="Symbol">→</a> <a id="3708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3693" class="Bound">x</a> <a id="3710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="3712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3695" class="Bound">y</a>
  <a id="3716" class="Symbol">→</a> <a id="3718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3695" class="Bound">y</a> <a id="3720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="3722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3697" class="Bound">z</a>
    <a id="3728" class="Comment">-----</a>
  <a id="3736" class="Symbol">→</a> <a id="3738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3693" class="Bound">x</a> <a id="3740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="3742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3697" class="Bound">z</a>
<a id="3744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3672" class="Function">trans</a> <a id="3750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="3755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>  <a id="3761" class="Symbol">=</a>  <a id="3764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>
Again, a useful exercise is to carry out an interactive development,
checking how Agda's knowledge changes as each of the two arguments is
instantiated.

## Congruence and substitution {#cong}

Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both.
<pre class="Agda">{% raw %}<a id="cong"></a><a id="4104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4104" class="Function">cong</a> <a id="4109" class="Symbol">:</a> <a id="4111" class="Symbol">∀</a> <a id="4113" class="Symbol">{</a><a id="4114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4114" class="Bound">A</a> <a id="4116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4116" class="Bound">B</a> <a id="4118" class="Symbol">:</a> <a id="4120" class="PrimitiveType">Set</a><a id="4123" class="Symbol">}</a> <a id="4125" class="Symbol">(</a><a id="4126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4126" class="Bound">f</a> <a id="4128" class="Symbol">:</a> <a id="4130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4114" class="Bound">A</a> <a id="4132" class="Symbol">→</a> <a id="4134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4116" class="Bound">B</a><a id="4135" class="Symbol">)</a> <a id="4137" class="Symbol">{</a><a id="4138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4138" class="Bound">x</a> <a id="4140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4140" class="Bound">y</a> <a id="4142" class="Symbol">:</a> <a id="4144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4114" class="Bound">A</a><a id="4145" class="Symbol">}</a>
  <a id="4149" class="Symbol">→</a> <a id="4151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4138" class="Bound">x</a> <a id="4153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4140" class="Bound">y</a>
    <a id="4161" class="Comment">---------</a>
  <a id="4173" class="Symbol">→</a> <a id="4175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4126" class="Bound">f</a> <a id="4177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4138" class="Bound">x</a> <a id="4179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4126" class="Bound">f</a> <a id="4183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4140" class="Bound">y</a>
<a id="4185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4104" class="Function">cong</a> <a id="4190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4190" class="Bound">f</a> <a id="4192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>  <a id="4198" class="Symbol">=</a>  <a id="4201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Congruence of functions with two arguments is similar.
<pre class="Agda">{% raw %}<a id="cong₂"></a><a id="4286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4286" class="Function">cong₂</a> <a id="4292" class="Symbol">:</a> <a id="4294" class="Symbol">∀</a> <a id="4296" class="Symbol">{</a><a id="4297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4297" class="Bound">A</a> <a id="4299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4299" class="Bound">B</a> <a id="4301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4301" class="Bound">C</a> <a id="4303" class="Symbol">:</a> <a id="4305" class="PrimitiveType">Set</a><a id="4308" class="Symbol">}</a> <a id="4310" class="Symbol">(</a><a id="4311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4311" class="Bound">f</a> <a id="4313" class="Symbol">:</a> <a id="4315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4297" class="Bound">A</a> <a id="4317" class="Symbol">→</a> <a id="4319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4299" class="Bound">B</a> <a id="4321" class="Symbol">→</a> <a id="4323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4301" class="Bound">C</a><a id="4324" class="Symbol">)</a> <a id="4326" class="Symbol">{</a><a id="4327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4327" class="Bound">u</a> <a id="4329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4329" class="Bound">x</a> <a id="4331" class="Symbol">:</a> <a id="4333" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4297" class="Bound">A</a><a id="4334" class="Symbol">}</a> <a id="4336" class="Symbol">{</a><a id="4337" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4337" class="Bound">v</a> <a id="4339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4339" class="Bound">y</a> <a id="4341" class="Symbol">:</a> <a id="4343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4299" class="Bound">B</a><a id="4344" class="Symbol">}</a>
  <a id="4348" class="Symbol">→</a> <a id="4350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4327" class="Bound">u</a> <a id="4352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4329" class="Bound">x</a>
  <a id="4358" class="Symbol">→</a> <a id="4360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4337" class="Bound">v</a> <a id="4362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4339" class="Bound">y</a>
    <a id="4370" class="Comment">-------------</a>
  <a id="4386" class="Symbol">→</a> <a id="4388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4311" class="Bound">f</a> <a id="4390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4327" class="Bound">u</a> <a id="4392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4337" class="Bound">v</a> <a id="4394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4311" class="Bound">f</a> <a id="4398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4329" class="Bound">x</a> <a id="4400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4339" class="Bound">y</a>
<a id="4402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4286" class="Function">cong₂</a> <a id="4408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4408" class="Bound">f</a> <a id="4410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="4415" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>  <a id="4421" class="Symbol">=</a>  <a id="4424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms.
<pre class="Agda">{% raw %}<a id="cong-app"></a><a id="4612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4612" class="Function">cong-app</a> <a id="4621" class="Symbol">:</a> <a id="4623" class="Symbol">∀</a> <a id="4625" class="Symbol">{</a><a id="4626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4626" class="Bound">A</a> <a id="4628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4628" class="Bound">B</a> <a id="4630" class="Symbol">:</a> <a id="4632" class="PrimitiveType">Set</a><a id="4635" class="Symbol">}</a> <a id="4637" class="Symbol">{</a><a id="4638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4638" class="Bound">f</a> <a id="4640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4640" class="Bound">g</a> <a id="4642" class="Symbol">:</a> <a id="4644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4626" class="Bound">A</a> <a id="4646" class="Symbol">→</a> <a id="4648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4628" class="Bound">B</a><a id="4649" class="Symbol">}</a>
  <a id="4653" class="Symbol">→</a> <a id="4655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4638" class="Bound">f</a> <a id="4657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4640" class="Bound">g</a>
    <a id="4665" class="Comment">---------------------</a>
  <a id="4689" class="Symbol">→</a> <a id="4691" class="Symbol">∀</a> <a id="4693" class="Symbol">(</a><a id="4694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4694" class="Bound">x</a> <a id="4696" class="Symbol">:</a> <a id="4698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4626" class="Bound">A</a><a id="4699" class="Symbol">)</a> <a id="4701" class="Symbol">→</a> <a id="4703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4638" class="Bound">f</a> <a id="4705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4694" class="Bound">x</a> <a id="4707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4640" class="Bound">g</a> <a id="4711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4694" class="Bound">x</a>
<a id="4713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4612" class="Function">cong-app</a> <a id="4722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="4727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4727" class="Bound">x</a> <a id="4729" class="Symbol">=</a> <a id="4731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second.
<pre class="Agda">{% raw %}<a id="subst"></a><a id="4894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4894" class="Function">subst</a> <a id="4900" class="Symbol">:</a> <a id="4902" class="Symbol">∀</a> <a id="4904" class="Symbol">{</a><a id="4905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4905" class="Bound">A</a> <a id="4907" class="Symbol">:</a> <a id="4909" class="PrimitiveType">Set</a><a id="4912" class="Symbol">}</a> <a id="4914" class="Symbol">{</a><a id="4915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4915" class="Bound">x</a> <a id="4917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4917" class="Bound">y</a> <a id="4919" class="Symbol">:</a> <a id="4921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4905" class="Bound">A</a><a id="4922" class="Symbol">}</a> <a id="4924" class="Symbol">(</a><a id="4925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4925" class="Bound">P</a> <a id="4927" class="Symbol">:</a> <a id="4929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4905" class="Bound">A</a> <a id="4931" class="Symbol">→</a> <a id="4933" class="PrimitiveType">Set</a><a id="4936" class="Symbol">)</a>
  <a id="4940" class="Symbol">→</a> <a id="4942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4915" class="Bound">x</a> <a id="4944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="4946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4917" class="Bound">y</a>
    <a id="4952" class="Comment">---------</a>
  <a id="4964" class="Symbol">→</a> <a id="4966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4925" class="Bound">P</a> <a id="4968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4915" class="Bound">x</a> <a id="4970" class="Symbol">→</a> <a id="4972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4925" class="Bound">P</a> <a id="4974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4917" class="Bound">y</a>
<a id="4976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4894" class="Function">subst</a> <a id="4982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4982" class="Bound">P</a> <a id="4984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a> <a id="4989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4989" class="Bound">px</a> <a id="4992" class="Symbol">=</a> <a id="4994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4989" class="Bound">px</a>{% endraw %}</pre>


## Chains of equations

Here we show how to support reasoning with chains of equations, as
used throughout the book.  We package the declarations into a module,
named `≡-Reasoning`, to match the format used in Agda's standard
library.
<pre class="Agda">{% raw %}<a id="5258" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="5265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5265" class="Module">≡-Reasoning</a> <a id="5277" class="Symbol">{</a><a id="5278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5278" class="Bound">A</a> <a id="5280" class="Symbol">:</a> <a id="5282" class="PrimitiveType">Set</a><a id="5285" class="Symbol">}</a> <a id="5287" class="Keyword">where</a>

  <a id="5296" class="Keyword">infix</a>  <a id="5303" class="Number">1</a> <a id="5305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5353" class="Function Operator">begin_</a>
  <a id="5314" class="Keyword">infixr</a> <a id="5321" class="Number">2</a> <a id="5323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5433" class="Function Operator">_≡⟨⟩_</a> <a id="5329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">_≡⟨_⟩_</a>
  <a id="5338" class="Keyword">infix</a>  <a id="5345" class="Number">3</a> <a id="5347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5633" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="5353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5353" class="Function Operator">begin_</a> <a id="5360" class="Symbol">:</a> <a id="5362" class="Symbol">∀</a> <a id="5364" class="Symbol">{</a><a id="5365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5365" class="Bound">x</a> <a id="5367" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5367" class="Bound">y</a> <a id="5369" class="Symbol">:</a> <a id="5371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5278" class="Bound">A</a><a id="5372" class="Symbol">}</a>
    <a id="5378" class="Symbol">→</a> <a id="5380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5365" class="Bound">x</a> <a id="5382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5367" class="Bound">y</a>
      <a id="5392" class="Comment">-----</a>
    <a id="5402" class="Symbol">→</a> <a id="5404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5365" class="Bound">x</a> <a id="5406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5367" class="Bound">y</a>
  <a id="5412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5353" class="Function Operator">begin</a> <a id="5418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5418" class="Bound">x≡y</a>  <a id="5423" class="Symbol">=</a>  <a id="5426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5418" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="5433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5433" class="Function Operator">_≡⟨⟩_</a> <a id="5439" class="Symbol">:</a> <a id="5441" class="Symbol">∀</a> <a id="5443" class="Symbol">(</a><a id="5444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5444" class="Bound">x</a> <a id="5446" class="Symbol">:</a> <a id="5448" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5278" class="Bound">A</a><a id="5449" class="Symbol">)</a> <a id="5451" class="Symbol">{</a><a id="5452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5452" class="Bound">y</a> <a id="5454" class="Symbol">:</a> <a id="5456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5278" class="Bound">A</a><a id="5457" class="Symbol">}</a>
    <a id="5463" class="Symbol">→</a> <a id="5465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5444" class="Bound">x</a> <a id="5467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5452" class="Bound">y</a>
      <a id="5477" class="Comment">-----</a>
    <a id="5487" class="Symbol">→</a> <a id="5489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5444" class="Bound">x</a> <a id="5491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5452" class="Bound">y</a>
  <a id="5497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5497" class="Bound">x</a> <a id="5499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5433" class="Function Operator">≡⟨⟩</a> <a id="5503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5503" class="Bound">x≡y</a>  <a id="5508" class="Symbol">=</a>  <a id="5511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5503" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="5518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">_≡⟨_⟩_</a> <a id="5525" class="Symbol">:</a> <a id="5527" class="Symbol">∀</a> <a id="5529" class="Symbol">(</a><a id="5530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5530" class="Bound">x</a> <a id="5532" class="Symbol">:</a> <a id="5534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5278" class="Bound">A</a><a id="5535" class="Symbol">)</a> <a id="5537" class="Symbol">{</a><a id="5538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5538" class="Bound">y</a> <a id="5540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5540" class="Bound">z</a> <a id="5542" class="Symbol">:</a> <a id="5544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5278" class="Bound">A</a><a id="5545" class="Symbol">}</a>
    <a id="5551" class="Symbol">→</a> <a id="5553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5530" class="Bound">x</a> <a id="5555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5538" class="Bound">y</a>
    <a id="5563" class="Symbol">→</a> <a id="5565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5538" class="Bound">y</a> <a id="5567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5540" class="Bound">z</a>
      <a id="5577" class="Comment">-----</a>
    <a id="5587" class="Symbol">→</a> <a id="5589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5530" class="Bound">x</a> <a id="5591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5540" class="Bound">z</a>
  <a id="5597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5597" class="Bound">x</a> <a id="5599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">≡⟨</a> <a id="5602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5602" class="Bound">x≡y</a> <a id="5606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">⟩</a> <a id="5608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5608" class="Bound">y≡z</a>  <a id="5613" class="Symbol">=</a>  <a id="5616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3672" class="Function">trans</a> <a id="5622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5602" class="Bound">x≡y</a> <a id="5626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5608" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="5633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5633" class="Function Operator">_∎</a> <a id="5636" class="Symbol">:</a> <a id="5638" class="Symbol">∀</a> <a id="5640" class="Symbol">(</a><a id="5641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5641" class="Bound">x</a> <a id="5643" class="Symbol">:</a> <a id="5645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5278" class="Bound">A</a><a id="5646" class="Symbol">)</a>
      <a id="5654" class="Comment">-----</a>
    <a id="5664" class="Symbol">→</a> <a id="5666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5641" class="Bound">x</a> <a id="5668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="5670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5641" class="Bound">x</a>
  <a id="5674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5674" class="Bound">x</a> <a id="5676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5633" class="Function Operator">∎</a>  <a id="5679" class="Symbol">=</a>  <a id="5682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>

<a id="5688" class="Keyword">open</a> <a id="5693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5265" class="Module">≡-Reasoning</a>{% endraw %}</pre>
This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including other nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.

As an example, let's look at a proof of transitivity
as a chain of equations.
<pre class="Agda">{% raw %}<a id="trans′"></a><a id="6340" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6340" class="Function">trans′</a> <a id="6347" class="Symbol">:</a> <a id="6349" class="Symbol">∀</a> <a id="6351" class="Symbol">{</a><a id="6352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6352" class="Bound">A</a> <a id="6354" class="Symbol">:</a> <a id="6356" class="PrimitiveType">Set</a><a id="6359" class="Symbol">}</a> <a id="6361" class="Symbol">{</a><a id="6362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6362" class="Bound">x</a> <a id="6364" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6364" class="Bound">y</a> <a id="6366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6366" class="Bound">z</a> <a id="6368" class="Symbol">:</a> <a id="6370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6352" class="Bound">A</a><a id="6371" class="Symbol">}</a>
  <a id="6375" class="Symbol">→</a> <a id="6377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6362" class="Bound">x</a> <a id="6379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="6381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6364" class="Bound">y</a>
  <a id="6385" class="Symbol">→</a> <a id="6387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6364" class="Bound">y</a> <a id="6389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="6391" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6366" class="Bound">z</a>
    <a id="6397" class="Comment">-----</a>
  <a id="6405" class="Symbol">→</a> <a id="6407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6362" class="Bound">x</a> <a id="6409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="6411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6366" class="Bound">z</a>
<a id="6413" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6340" class="Function">trans′</a> <a id="6420" class="Symbol">{</a><a id="6421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6421" class="Bound">A</a><a id="6422" class="Symbol">}</a> <a id="6424" class="Symbol">{</a><a id="6425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6425" class="Bound">x</a><a id="6426" class="Symbol">}</a> <a id="6428" class="Symbol">{</a><a id="6429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6429" class="Bound">y</a><a id="6430" class="Symbol">}</a> <a id="6432" class="Symbol">{</a><a id="6433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6433" class="Bound">z</a><a id="6434" class="Symbol">}</a> <a id="6436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6436" class="Bound">x≡y</a> <a id="6440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6440" class="Bound">y≡z</a> <a id="6444" class="Symbol">=</a>
  <a id="6448" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5353" class="Function Operator">begin</a>
    <a id="6458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6425" class="Bound">x</a>
  <a id="6462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">≡⟨</a> <a id="6465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6436" class="Bound">x≡y</a> <a id="6469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">⟩</a>
    <a id="6475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6429" class="Bound">y</a>
  <a id="6479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">≡⟨</a> <a id="6482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6440" class="Bound">y≡z</a> <a id="6486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">⟩</a>
    <a id="6492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6433" class="Bound">z</a>
  <a id="6496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5633" class="Function Operator">∎</a>{% endraw %}</pre>
According to the fixity declarations, the body parses as follows:

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:

    trans x≡y (trans y≡z refl)

We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` than ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.


## Chains of equations, another example

As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict.
<pre class="Agda">{% raw %}<a id="8197" class="Keyword">data</a> <a id="ℕ"></a><a id="8202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a> <a id="8204" class="Symbol">:</a> <a id="8206" class="PrimitiveType">Set</a> <a id="8210" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="8218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="InductiveConstructor">zero</a> <a id="8223" class="Symbol">:</a> <a id="8225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="8229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a>  <a id="8234" class="Symbol">:</a> <a id="8236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a> <a id="8238" class="Symbol">→</a> <a id="8240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="8243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">_+_</a> <a id="8247" class="Symbol">:</a> <a id="8249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a> <a id="8251" class="Symbol">→</a> <a id="8253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a> <a id="8255" class="Symbol">→</a> <a id="8257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a>
<a id="8259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="InductiveConstructor">zero</a>    <a id="8267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="8269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8269" class="Bound">n</a>  <a id="8272" class="Symbol">=</a>  <a id="8275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8269" class="Bound">n</a>
<a id="8277" class="Symbol">(</a><a id="8278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="8282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8282" class="Bound">m</a><a id="8283" class="Symbol">)</a> <a id="8285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="8287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8287" class="Bound">n</a>  <a id="8290" class="Symbol">=</a>  <a id="8293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="8297" class="Symbol">(</a><a id="8298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8282" class="Bound">m</a> <a id="8300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="8302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8287" class="Bound">n</a><a id="8303" class="Symbol">)</a>{% endraw %}</pre>

To save space we postulate (rather than prove in full) two lemmas.
<pre class="Agda">{% raw %}<a id="8397" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="8409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8409" class="Postulate">+-identity</a> <a id="8420" class="Symbol">:</a> <a id="8422" class="Symbol">∀</a> <a id="8424" class="Symbol">(</a><a id="8425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Bound">m</a> <a id="8427" class="Symbol">:</a> <a id="8429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a><a id="8430" class="Symbol">)</a> <a id="8432" class="Symbol">→</a> <a id="8434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Bound">m</a> <a id="8436" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="8438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="InductiveConstructor">zero</a> <a id="8443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="8445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Bound">m</a>
  <a id="+-suc"></a><a id="8449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8449" class="Postulate">+-suc</a> <a id="8455" class="Symbol">:</a> <a id="8457" class="Symbol">∀</a> <a id="8459" class="Symbol">(</a><a id="8460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8460" class="Bound">m</a> <a id="8462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8462" class="Bound">n</a> <a id="8464" class="Symbol">:</a> <a id="8466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a><a id="8467" class="Symbol">)</a> <a id="8469" class="Symbol">→</a> <a id="8471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8460" class="Bound">m</a> <a id="8473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="8475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="8479" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8462" class="Bound">n</a> <a id="8481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="8483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="8487" class="Symbol">(</a><a id="8488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8460" class="Bound">m</a> <a id="8490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="8492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8462" class="Bound">n</a><a id="8493" class="Symbol">)</a>{% endraw %}</pre>
This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.

We then repeat the proof of commutativity.
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="8859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8859" class="Function">+-comm</a> <a id="8866" class="Symbol">:</a> <a id="8868" class="Symbol">∀</a> <a id="8870" class="Symbol">(</a><a id="8871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8871" class="Bound">m</a> <a id="8873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8873" class="Bound">n</a> <a id="8875" class="Symbol">:</a> <a id="8877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a><a id="8878" class="Symbol">)</a> <a id="8880" class="Symbol">→</a> <a id="8882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8871" class="Bound">m</a> <a id="8884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="8886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8873" class="Bound">n</a> <a id="8888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="8890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8873" class="Bound">n</a> <a id="8892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="8894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8871" class="Bound">m</a>
<a id="8896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8859" class="Function">+-comm</a> <a id="8903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8903" class="Bound">m</a> <a id="8905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="InductiveConstructor">zero</a> <a id="8910" class="Symbol">=</a>
  <a id="8914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5353" class="Function Operator">begin</a>
    <a id="8924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8903" class="Bound">m</a> <a id="8926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="8928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="InductiveConstructor">zero</a>
  <a id="8935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">≡⟨</a> <a id="8938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8409" class="Postulate">+-identity</a> <a id="8949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8903" class="Bound">m</a> <a id="8951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">⟩</a>
    <a id="8957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8903" class="Bound">m</a>
  <a id="8961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5433" class="Function Operator">≡⟨⟩</a>
    <a id="8969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="InductiveConstructor">zero</a> <a id="8974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="8976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8903" class="Bound">m</a>
  <a id="8980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5633" class="Function Operator">∎</a>
<a id="8982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8859" class="Function">+-comm</a> <a id="8989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8989" class="Bound">m</a> <a id="8991" class="Symbol">(</a><a id="8992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="8996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8996" class="Bound">n</a><a id="8997" class="Symbol">)</a> <a id="8999" class="Symbol">=</a>
  <a id="9003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5353" class="Function Operator">begin</a>
    <a id="9013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8989" class="Bound">m</a> <a id="9015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="9017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="9021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8996" class="Bound">n</a>
  <a id="9025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">≡⟨</a> <a id="9028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8449" class="Postulate">+-suc</a> <a id="9034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8989" class="Bound">m</a> <a id="9036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8996" class="Bound">n</a> <a id="9038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">⟩</a>
    <a id="9044" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="9048" class="Symbol">(</a><a id="9049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8989" class="Bound">m</a> <a id="9051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="9053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8996" class="Bound">n</a><a id="9054" class="Symbol">)</a>
  <a id="9058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">≡⟨</a> <a id="9061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4104" class="Function">cong</a> <a id="9066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="9070" class="Symbol">(</a><a id="9071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8859" class="Function">+-comm</a> <a id="9078" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8989" class="Bound">m</a> <a id="9080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8996" class="Bound">n</a><a id="9081" class="Symbol">)</a> <a id="9083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5518" class="Function Operator">⟩</a>
    <a id="9089" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="9093" class="Symbol">(</a><a id="9094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8996" class="Bound">n</a> <a id="9096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="9098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8989" class="Bound">m</a><a id="9099" class="Symbol">)</a>
  <a id="9103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5433" class="Function Operator">≡⟨⟩</a>
    <a id="9111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="9115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8996" class="Bound">n</a> <a id="9117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="9119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8989" class="Bound">m</a>
  <a id="9123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5633" class="Function Operator">∎</a>{% endraw %}</pre>
The reasoning here is similar to that in the
preceding section.  We use
`_≡⟨⟩_` when no justification is required.
One can think of `_≡⟨⟩_` as equivalent to `_≡⟨ refl ⟩_`.

Agda always treats a term as equivalent to its
simplified term.  The reason that one can write

      suc (n + m)
    ≡⟨⟩
      suc n + m

is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write

      suc n + m
    ≡⟨⟩
      suc (n + m)

and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.


#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}{% link out/plfa/Relations.md%})
can be written in a more readable form by using an anologue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.



## Rewriting

Consider a property of natural numbers, such as being even.
We repeat the earlier definition.
<pre class="Agda">{% raw %}<a id="10298" class="Keyword">data</a> <a id="even"></a><a id="10303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="10308" class="Symbol">:</a> <a id="10310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a> <a id="10312" class="Symbol">→</a> <a id="10314" class="PrimitiveType">Set</a>
<a id="10318" class="Keyword">data</a> <a id="odd"></a><a id="10323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10323" class="Datatype">odd</a>  <a id="10328" class="Symbol">:</a> <a id="10330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a> <a id="10332" class="Symbol">→</a> <a id="10334" class="PrimitiveType">Set</a>

<a id="10339" class="Keyword">data</a> <a id="10344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="10349" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="10358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10358" class="InductiveConstructor">even-zero</a> <a id="10368" class="Symbol">:</a> <a id="10370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="10375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="10383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10383" class="InductiveConstructor">even-suc</a> <a id="10392" class="Symbol">:</a> <a id="10394" class="Symbol">∀</a> <a id="10396" class="Symbol">{</a><a id="10397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10397" class="Bound">n</a> <a id="10399" class="Symbol">:</a> <a id="10401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a><a id="10402" class="Symbol">}</a>
    <a id="10408" class="Symbol">→</a> <a id="10410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10323" class="Datatype">odd</a> <a id="10414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10397" class="Bound">n</a>
      <a id="10422" class="Comment">------------</a>
    <a id="10439" class="Symbol">→</a> <a id="10441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="10446" class="Symbol">(</a><a id="10447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="10451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10397" class="Bound">n</a><a id="10452" class="Symbol">)</a>

<a id="10455" class="Keyword">data</a> <a id="10460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10323" class="Datatype">odd</a> <a id="10464" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="10472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10472" class="InductiveConstructor">odd-suc</a> <a id="10480" class="Symbol">:</a> <a id="10482" class="Symbol">∀</a> <a id="10484" class="Symbol">{</a><a id="10485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10485" class="Bound">n</a> <a id="10487" class="Symbol">:</a> <a id="10489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a><a id="10490" class="Symbol">}</a>
    <a id="10496" class="Symbol">→</a> <a id="10498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="10503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10485" class="Bound">n</a>
      <a id="10511" class="Comment">-----------</a>
    <a id="10527" class="Symbol">→</a> <a id="10529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10323" class="Datatype">odd</a> <a id="10533" class="Symbol">(</a><a id="10534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="10538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10485" class="Bound">n</a><a id="10539" class="Symbol">)</a>{% endraw %}</pre>
In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.

Agda includes special notation to support just this kind of reasoning,
the `rewrite` notation we encountered earlier.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equality.
<pre class="Agda">{% raw %}<a id="10953" class="Symbol">{-#</a> <a id="10957" class="Keyword">BUILTIN</a> EQUALITY <a id="10974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">_≡_</a> <a id="10978" class="Symbol">#-}</a>{% endraw %}</pre>

We can then prove the desired property as follows.
<pre class="Agda">{% raw %}<a id="even-comm"></a><a id="11058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11058" class="Function">even-comm</a> <a id="11068" class="Symbol">:</a> <a id="11070" class="Symbol">∀</a> <a id="11072" class="Symbol">(</a><a id="11073" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11073" class="Bound">m</a> <a id="11075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11075" class="Bound">n</a> <a id="11077" class="Symbol">:</a> <a id="11079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a><a id="11080" class="Symbol">)</a>
  <a id="11084" class="Symbol">→</a> <a id="11086" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="11091" class="Symbol">(</a><a id="11092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11073" class="Bound">m</a> <a id="11094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="11096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11075" class="Bound">n</a><a id="11097" class="Symbol">)</a>
    <a id="11103" class="Comment">------------</a>
  <a id="11118" class="Symbol">→</a> <a id="11120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="11125" class="Symbol">(</a><a id="11126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11075" class="Bound">n</a> <a id="11128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="11130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11073" class="Bound">m</a><a id="11131" class="Symbol">)</a>
<a id="11133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11058" class="Function">even-comm</a> <a id="11143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11143" class="Bound">m</a> <a id="11145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11145" class="Bound">n</a> <a id="11147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11147" class="Bound">ev</a>  <a id="11151" class="Keyword">rewrite</a> <a id="11159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8859" class="Function">+-comm</a> <a id="11166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11145" class="Bound">n</a> <a id="11168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11143" class="Bound">m</a>  <a id="11171" class="Symbol">=</a>  <a id="11174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11147" class="Bound">ev</a>{% endraw %}</pre>
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it is also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equality, and that equality is used to rewrite the type of the
goal and of any variable in scope.

It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

Now we add the rewrite.

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm n m = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

    Goal: even (m + n)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.  The command `C-c C-a` performs an
automated search, including checking whether a variable in scope has
the same type as the goal.


## Multiple rewrites

One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities.
<pre class="Agda">{% raw %}<a id="+-comm′"></a><a id="12853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12853" class="Function">+-comm′</a> <a id="12861" class="Symbol">:</a> <a id="12863" class="Symbol">∀</a> <a id="12865" class="Symbol">(</a><a id="12866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12866" class="Bound">m</a> <a id="12868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12868" class="Bound">n</a> <a id="12870" class="Symbol">:</a> <a id="12872" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a><a id="12873" class="Symbol">)</a> <a id="12875" class="Symbol">→</a> <a id="12877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12866" class="Bound">m</a> <a id="12879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="12881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12868" class="Bound">n</a> <a id="12883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="12885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12868" class="Bound">n</a> <a id="12887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="12889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12866" class="Bound">m</a>
<a id="12891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12853" class="Function">+-comm′</a> <a id="12899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="InductiveConstructor">zero</a>    <a id="12907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12907" class="Bound">n</a>  <a id="12910" class="Keyword">rewrite</a> <a id="12918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8409" class="Postulate">+-identity</a> <a id="12929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12907" class="Bound">n</a>            <a id="12942" class="Symbol">=</a>  <a id="12945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>
<a id="12950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12853" class="Function">+-comm′</a> <a id="12958" class="Symbol">(</a><a id="12959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8229" class="InductiveConstructor">suc</a> <a id="12963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12963" class="Bound">m</a><a id="12964" class="Symbol">)</a> <a id="12966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12966" class="Bound">n</a>  <a id="12969" class="Keyword">rewrite</a> <a id="12977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8449" class="Postulate">+-suc</a> <a id="12983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12966" class="Bound">n</a> <a id="12985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12963" class="Bound">m</a> <a id="12987" class="Symbol">|</a> <a id="12989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8859" class="Function">+-comm</a> <a id="12996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12963" class="Bound">m</a> <a id="12998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12966" class="Bound">n</a>  <a id="13001" class="Symbol">=</a>  <a id="13004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>{% endraw %}</pre>
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.


## Rewriting expanded

The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction.
<pre class="Agda">{% raw %}<a id="even-comm′"></a><a id="13569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13569" class="Function">even-comm′</a> <a id="13580" class="Symbol">:</a> <a id="13582" class="Symbol">∀</a> <a id="13584" class="Symbol">(</a><a id="13585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13585" class="Bound">m</a> <a id="13587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13587" class="Bound">n</a> <a id="13589" class="Symbol">:</a> <a id="13591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a><a id="13592" class="Symbol">)</a>
  <a id="13596" class="Symbol">→</a> <a id="13598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="13603" class="Symbol">(</a><a id="13604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13585" class="Bound">m</a> <a id="13606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="13608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13587" class="Bound">n</a><a id="13609" class="Symbol">)</a>
    <a id="13615" class="Comment">------------</a>
  <a id="13630" class="Symbol">→</a> <a id="13632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="13637" class="Symbol">(</a><a id="13638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13587" class="Bound">n</a> <a id="13640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="13642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13585" class="Bound">m</a><a id="13643" class="Symbol">)</a>
<a id="13645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13569" class="Function">even-comm′</a> <a id="13656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13656" class="Bound">m</a> <a id="13658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13658" class="Bound">n</a> <a id="13660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13660" class="Bound">ev</a> <a id="13663" class="Keyword">with</a>   <a id="13670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13656" class="Bound">m</a> <a id="13672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="13674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13658" class="Bound">n</a>  <a id="13677" class="Symbol">|</a> <a id="13679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8859" class="Function">+-comm</a> <a id="13686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13656" class="Bound">m</a> <a id="13688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13658" class="Bound">n</a>
<a id="13690" class="Symbol">...</a>                  <a id="13711" class="Symbol">|</a> <a id="13713" class="DottedPattern Symbol">.(</a><a id="13715" class="DottedPattern Bound">n</a> <a id="13717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="DottedPattern Function Operator">+</a> <a id="13719" class="DottedPattern Bound">m</a><a id="13720" class="DottedPattern Symbol">)</a> <a id="13722" class="Symbol">|</a> <a id="13724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>       <a id="13735" class="Symbol">=</a> <a id="13737" class="Bound">ev</a>{% endraw %}</pre>
In general, one can follow `with` by any number of expressions,
separated by bars, where each following equation has the same number
of patterns.  We often write expressions and the corresponding
patterns so they line up in columns, as above. Here the first column
asserts that `m + n` and `n + m` are identical, and the second column
justifies that assertion with evidence of the appropriate equality.
Note also the use of the _dot pattern_, `.(n + m)`.  A dot pattern
consists of a dot followed by an expression, and is used when other
information forces the value matched to be equal to the value of the
expression in the dot pattern.  In this case, the identification of `m
+ n` and `n + m` is justified by the subsequent matching of `+-comm m
n` against `refl`.  One might think that the first clause is redundant
as the information is inherent in the second clause, but in fact Agda
is rather picky on this point: omitting the first clause or reversing
the order of the clauses will cause Agda to report an error.  (Try it
and see!)

In this case, we can avoid rewrite by simply applying the substitution
function defined earlier.
<pre class="Agda">{% raw %}<a id="even-comm″"></a><a id="14901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14901" class="Function">even-comm″</a> <a id="14912" class="Symbol">:</a> <a id="14914" class="Symbol">∀</a> <a id="14916" class="Symbol">(</a><a id="14917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14917" class="Bound">m</a> <a id="14919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14919" class="Bound">n</a> <a id="14921" class="Symbol">:</a> <a id="14923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8202" class="Datatype">ℕ</a><a id="14924" class="Symbol">)</a>
  <a id="14928" class="Symbol">→</a> <a id="14930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="14935" class="Symbol">(</a><a id="14936" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14917" class="Bound">m</a> <a id="14938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="14940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14919" class="Bound">n</a><a id="14941" class="Symbol">)</a>
    <a id="14947" class="Comment">------------</a>
  <a id="14962" class="Symbol">→</a> <a id="14964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="14969" class="Symbol">(</a><a id="14970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14919" class="Bound">n</a> <a id="14972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8243" class="Function Operator">+</a> <a id="14974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14917" class="Bound">m</a><a id="14975" class="Symbol">)</a>
<a id="14977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14901" class="Function">even-comm″</a> <a id="14988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14988" class="Bound">m</a> <a id="14990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14990" class="Bound">n</a>  <a id="14993" class="Symbol">=</a>  <a id="14996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4894" class="Function">subst</a> <a id="15002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10303" class="Datatype">even</a> <a id="15007" class="Symbol">(</a><a id="15008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8859" class="Function">+-comm</a> <a id="15015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14988" class="Bound">m</a> <a id="15017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14990" class="Bound">n</a><a id="15018" class="Symbol">)</a>{% endraw %}</pre>
Nonetheless, rewrite is a vital part of the Agda toolkit.  We will use
it sparingly, but it is occasionally essential.


## Leibniz equality

The form of asserting equality that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equality.

Leibniz equality is usually formalised to state that `x ≐ y` holds if
every property `P` that holds of `x` also holds of `y`.  Perhaps
surprisingly, this definition is sufficient to also ensure the
converse, that every property `P` that holds of `y` also holds of `x`.

Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`.
<pre class="Agda">{% raw %}<a id="_≐_"></a><a id="16165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16165" class="Function Operator">_≐_</a> <a id="16169" class="Symbol">:</a> <a id="16171" class="Symbol">∀</a> <a id="16173" class="Symbol">{</a><a id="16174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16174" class="Bound">A</a> <a id="16176" class="Symbol">:</a> <a id="16178" class="PrimitiveType">Set</a><a id="16181" class="Symbol">}</a> <a id="16183" class="Symbol">(</a><a id="16184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16184" class="Bound">x</a> <a id="16186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16186" class="Bound">y</a> <a id="16188" class="Symbol">:</a> <a id="16190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16174" class="Bound">A</a><a id="16191" class="Symbol">)</a> <a id="16193" class="Symbol">→</a> <a id="16195" class="PrimitiveType">Set₁</a>
<a id="16200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16165" class="Function Operator">_≐_</a> <a id="16204" class="Symbol">{</a><a id="16205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16205" class="Bound">A</a><a id="16206" class="Symbol">}</a> <a id="16208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16208" class="Bound">x</a> <a id="16210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16210" class="Bound">y</a> <a id="16212" class="Symbol">=</a> <a id="16214" class="Symbol">∀</a> <a id="16216" class="Symbol">(</a><a id="16217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16217" class="Bound">P</a> <a id="16219" class="Symbol">:</a> <a id="16221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16205" class="Bound">A</a> <a id="16223" class="Symbol">→</a> <a id="16225" class="PrimitiveType">Set</a><a id="16228" class="Symbol">)</a> <a id="16230" class="Symbol">→</a> <a id="16232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16217" class="Bound">P</a> <a id="16234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16208" class="Bound">x</a> <a id="16236" class="Symbol">→</a> <a id="16238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16217" class="Bound">P</a> <a id="16240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16210" class="Bound">y</a>{% endraw %}</pre>
We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.

This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russell's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.

Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition.
<pre class="Agda">{% raw %}<a id="refl-≐"></a><a id="17080" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17080" class="Function">refl-≐</a> <a id="17087" class="Symbol">:</a> <a id="17089" class="Symbol">∀</a> <a id="17091" class="Symbol">{</a><a id="17092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17092" class="Bound">A</a> <a id="17094" class="Symbol">:</a> <a id="17096" class="PrimitiveType">Set</a><a id="17099" class="Symbol">}</a> <a id="17101" class="Symbol">{</a><a id="17102" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17102" class="Bound">x</a> <a id="17104" class="Symbol">:</a> <a id="17106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17092" class="Bound">A</a><a id="17107" class="Symbol">}</a>
  <a id="17111" class="Symbol">→</a> <a id="17113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17102" class="Bound">x</a> <a id="17115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16165" class="Function Operator">≐</a> <a id="17117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17102" class="Bound">x</a>
<a id="17119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17080" class="Function">refl-≐</a> <a id="17126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17126" class="Bound">P</a> <a id="17128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17128" class="Bound">Px</a>  <a id="17132" class="Symbol">=</a>  <a id="17135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17128" class="Bound">Px</a>

<a id="trans-≐"></a><a id="17139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17139" class="Function">trans-≐</a> <a id="17147" class="Symbol">:</a> <a id="17149" class="Symbol">∀</a> <a id="17151" class="Symbol">{</a><a id="17152" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17152" class="Bound">A</a> <a id="17154" class="Symbol">:</a> <a id="17156" class="PrimitiveType">Set</a><a id="17159" class="Symbol">}</a> <a id="17161" class="Symbol">{</a><a id="17162" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17162" class="Bound">x</a> <a id="17164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17164" class="Bound">y</a> <a id="17166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17166" class="Bound">z</a> <a id="17168" class="Symbol">:</a> <a id="17170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17152" class="Bound">A</a><a id="17171" class="Symbol">}</a>
  <a id="17175" class="Symbol">→</a> <a id="17177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17162" class="Bound">x</a> <a id="17179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16165" class="Function Operator">≐</a> <a id="17181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17164" class="Bound">y</a>
  <a id="17185" class="Symbol">→</a> <a id="17187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17164" class="Bound">y</a> <a id="17189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16165" class="Function Operator">≐</a> <a id="17191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17166" class="Bound">z</a>
    <a id="17197" class="Comment">-----</a>
  <a id="17205" class="Symbol">→</a> <a id="17207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17162" class="Bound">x</a> <a id="17209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16165" class="Function Operator">≐</a> <a id="17211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17166" class="Bound">z</a>
<a id="17213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17139" class="Function">trans-≐</a> <a id="17221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17221" class="Bound">x≐y</a> <a id="17225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17225" class="Bound">y≐z</a> <a id="17229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17229" class="Bound">P</a> <a id="17231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17231" class="Bound">Px</a>  <a id="17235" class="Symbol">=</a>  <a id="17238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17225" class="Bound">y≐z</a> <a id="17242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17229" class="Bound">P</a> <a id="17244" class="Symbol">(</a><a id="17245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17221" class="Bound">x≐y</a> <a id="17249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17229" class="Bound">P</a> <a id="17251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17231" class="Bound">Px</a><a id="17253" class="Symbol">)</a>{% endraw %}</pre>

Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well.
<pre class="Agda">{% raw %}<a id="sym-≐"></a><a id="17431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17431" class="Function">sym-≐</a> <a id="17437" class="Symbol">:</a> <a id="17439" class="Symbol">∀</a> <a id="17441" class="Symbol">{</a><a id="17442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17442" class="Bound">A</a> <a id="17444" class="Symbol">:</a> <a id="17446" class="PrimitiveType">Set</a><a id="17449" class="Symbol">}</a> <a id="17451" class="Symbol">{</a><a id="17452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17452" class="Bound">x</a> <a id="17454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17454" class="Bound">y</a> <a id="17456" class="Symbol">:</a> <a id="17458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17442" class="Bound">A</a><a id="17459" class="Symbol">}</a>
  <a id="17463" class="Symbol">→</a> <a id="17465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17452" class="Bound">x</a> <a id="17467" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16165" class="Function Operator">≐</a> <a id="17469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17454" class="Bound">y</a>
    <a id="17475" class="Comment">-----</a>
  <a id="17483" class="Symbol">→</a> <a id="17485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17454" class="Bound">y</a> <a id="17487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16165" class="Function Operator">≐</a> <a id="17489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17452" class="Bound">x</a>
<a id="17491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17431" class="Function">sym-≐</a> <a id="17497" class="Symbol">{</a><a id="17498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17498" class="Bound">A</a><a id="17499" class="Symbol">}</a> <a id="17501" class="Symbol">{</a><a id="17502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17502" class="Bound">x</a><a id="17503" class="Symbol">}</a> <a id="17505" class="Symbol">{</a><a id="17506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17506" class="Bound">y</a><a id="17507" class="Symbol">}</a> <a id="17509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17509" class="Bound">x≐y</a> <a id="17513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17513" class="Bound">P</a>  <a id="17516" class="Symbol">=</a>  <a id="17519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17601" class="Function">Qy</a>
  <a id="17524" class="Keyword">where</a>
    <a id="17534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17534" class="Function">Q</a> <a id="17536" class="Symbol">:</a> <a id="17538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17498" class="Bound">A</a> <a id="17540" class="Symbol">→</a> <a id="17542" class="PrimitiveType">Set</a>
    <a id="17550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17534" class="Function">Q</a> <a id="17552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17552" class="Bound">z</a> <a id="17554" class="Symbol">=</a> <a id="17556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17513" class="Bound">P</a> <a id="17558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17552" class="Bound">z</a> <a id="17560" class="Symbol">→</a> <a id="17562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17513" class="Bound">P</a> <a id="17564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17502" class="Bound">x</a>
    <a id="17570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17570" class="Function">Qx</a> <a id="17573" class="Symbol">:</a> <a id="17575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17534" class="Function">Q</a> <a id="17577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17502" class="Bound">x</a>
    <a id="17583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17570" class="Function">Qx</a> <a id="17586" class="Symbol">=</a> <a id="17588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17080" class="Function">refl-≐</a> <a id="17595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17513" class="Bound">P</a>
    <a id="17601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17601" class="Function">Qy</a> <a id="17604" class="Symbol">:</a> <a id="17606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17534" class="Function">Q</a> <a id="17608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17506" class="Bound">y</a>
    <a id="17614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17601" class="Function">Qy</a> <a id="17617" class="Symbol">=</a> <a id="17619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17509" class="Bound">x≐y</a> <a id="17623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17534" class="Function">Q</a> <a id="17625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17570" class="Function">Qx</a>{% endraw %}</pre>
Given `x ≐ y`, a specific `P`, and a proof of `P y`, we have to
construct a proof of `P x`.  To do so, we instantiate the equality
with a predicate `Q` such that `Q z` holds if `P z` implies `P x`.
The property `Q x` is trivial by reflexivity, and hence `Q y` follows
from `x ≐ y`.  But `Q y` is exactly a proof of what we require, that
`P y` implies `P x`.

We now show that Martin Löf equality implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equality of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`.
<pre class="Agda">{% raw %}<a id="≡-implies-≐"></a><a id="18306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18306" class="Function">≡-implies-≐</a> <a id="18318" class="Symbol">:</a> <a id="18320" class="Symbol">∀</a> <a id="18322" class="Symbol">{</a><a id="18323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18323" class="Bound">A</a> <a id="18325" class="Symbol">:</a> <a id="18327" class="PrimitiveType">Set</a><a id="18330" class="Symbol">}</a> <a id="18332" class="Symbol">{</a><a id="18333" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18333" class="Bound">x</a> <a id="18335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18335" class="Bound">y</a> <a id="18337" class="Symbol">:</a> <a id="18339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18323" class="Bound">A</a><a id="18340" class="Symbol">}</a>
  <a id="18344" class="Symbol">→</a> <a id="18346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18333" class="Bound">x</a> <a id="18348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="18350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18335" class="Bound">y</a>
    <a id="18356" class="Comment">-----</a>
  <a id="18364" class="Symbol">→</a> <a id="18366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18333" class="Bound">x</a> <a id="18368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16165" class="Function Operator">≐</a> <a id="18370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18335" class="Bound">y</a>
<a id="18372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18306" class="Function">≡-implies-≐</a> <a id="18384" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18384" class="Bound">x≡y</a> <a id="18388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18388" class="Bound">P</a>  <a id="18391" class="Symbol">=</a>  <a id="18394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4894" class="Function">subst</a> <a id="18400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18388" class="Bound">P</a> <a id="18402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18384" class="Bound">x≡y</a>{% endraw %}</pre>
This direction follows from substitution, which we showed earlier.

In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`. 
<pre class="Agda">{% raw %}<a id="≐-implies-≡"></a><a id="18622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18622" class="Function">≐-implies-≡</a> <a id="18634" class="Symbol">:</a> <a id="18636" class="Symbol">∀</a> <a id="18638" class="Symbol">{</a><a id="18639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18639" class="Bound">A</a> <a id="18641" class="Symbol">:</a> <a id="18643" class="PrimitiveType">Set</a><a id="18646" class="Symbol">}</a> <a id="18648" class="Symbol">{</a><a id="18649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18649" class="Bound">x</a> <a id="18651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18651" class="Bound">y</a> <a id="18653" class="Symbol">:</a> <a id="18655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18639" class="Bound">A</a><a id="18656" class="Symbol">}</a>
  <a id="18660" class="Symbol">→</a> <a id="18662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18649" class="Bound">x</a> <a id="18664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16165" class="Function Operator">≐</a> <a id="18666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18651" class="Bound">y</a>
    <a id="18672" class="Comment">-----</a>
  <a id="18680" class="Symbol">→</a> <a id="18682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18649" class="Bound">x</a> <a id="18684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="18686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18651" class="Bound">y</a>
<a id="18688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18622" class="Function">≐-implies-≡</a> <a id="18700" class="Symbol">{</a><a id="18701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18701" class="Bound">A</a><a id="18702" class="Symbol">}</a> <a id="18704" class="Symbol">{</a><a id="18705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18705" class="Bound">x</a><a id="18706" class="Symbol">}</a> <a id="18708" class="Symbol">{</a><a id="18709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18709" class="Bound">y</a><a id="18710" class="Symbol">}</a> <a id="18712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18712" class="Bound">x≐y</a>  <a id="18717" class="Symbol">=</a>  <a id="18720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18794" class="Function">Qy</a>
  <a id="18725" class="Keyword">where</a>
    <a id="18735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18735" class="Function">Q</a> <a id="18737" class="Symbol">:</a> <a id="18739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18701" class="Bound">A</a> <a id="18741" class="Symbol">→</a> <a id="18743" class="PrimitiveType">Set</a>
    <a id="18751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18735" class="Function">Q</a> <a id="18753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18753" class="Bound">z</a> <a id="18755" class="Symbol">=</a> <a id="18757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18705" class="Bound">x</a> <a id="18759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#733" class="Datatype Operator">≡</a> <a id="18761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18753" class="Bound">z</a>
    <a id="18767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18767" class="Function">Qx</a> <a id="18770" class="Symbol">:</a> <a id="18772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18735" class="Function">Q</a> <a id="18774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18705" class="Bound">x</a>
    <a id="18780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18767" class="Function">Qx</a> <a id="18783" class="Symbol">=</a> <a id="18785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#773" class="InductiveConstructor">refl</a>
    <a id="18794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18794" class="Function">Qy</a> <a id="18797" class="Symbol">:</a> <a id="18799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18735" class="Function">Q</a> <a id="18801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18709" class="Bound">y</a>
    <a id="18807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18794" class="Function">Qy</a> <a id="18810" class="Symbol">=</a> <a id="18812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18712" class="Bound">x≐y</a> <a id="18816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18735" class="Function">Q</a> <a id="18818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18767" class="Function">Qx</a>{% endraw %}</pre>
The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equality, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.

(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)


## Universe polymorphism {#unipoly}

As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?

The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following.
<pre class="Agda">{% raw %}<a id="19989" class="Keyword">open</a> <a id="19994" class="Keyword">import</a> <a id="20001" href="https://agda.github.io/agda-stdlib/Level.html" class="Module">Level</a> <a id="20007" class="Keyword">using</a> <a id="20013" class="Symbol">(</a><a id="20014" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20019" class="Symbol">;</a> <a id="20021" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="20024" class="Symbol">)</a> <a id="20026" class="Keyword">renaming</a> <a id="20035" class="Symbol">(</a><a id="20036" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#611" class="Primitive">zero</a> <a id="20041" class="Symbol">to</a> <a id="20044" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#611" class="Primitive">lzero</a><a id="20049" class="Symbol">;</a> <a id="20051" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">suc</a> <a id="20055" class="Symbol">to</a> <a id="20058" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="20062" class="Symbol">)</a>{% endraw %}</pre>
We rename constructors `zero` and `suc` to `lzero` and `lsuc` to avoid confusion
between levels and naturals.

Levels are isomorphic to natural numbers, and have similar constructors:

    lzero : Level
    lsuc  : Level → Level

The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

and so on. There is also an operator

    _⊔_ : Level → Level → Level

that given two levels returns the larger of the two.

Here is the definition of equality, generalised to an arbitrary level.
<pre class="Agda">{% raw %}<a id="20646" class="Keyword">data</a> <a id="_≡′_"></a><a id="20651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20651" class="Datatype Operator">_≡′_</a> <a id="20656" class="Symbol">{</a><a id="20657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20657" class="Bound">ℓ</a> <a id="20659" class="Symbol">:</a> <a id="20661" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20666" class="Symbol">}</a> <a id="20668" class="Symbol">{</a><a id="20669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20669" class="Bound">A</a> <a id="20671" class="Symbol">:</a> <a id="20673" class="PrimitiveType">Set</a> <a id="20677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20657" class="Bound">ℓ</a><a id="20678" class="Symbol">}</a> <a id="20680" class="Symbol">(</a><a id="20681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20681" class="Bound">x</a> <a id="20683" class="Symbol">:</a> <a id="20685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20669" class="Bound">A</a><a id="20686" class="Symbol">)</a> <a id="20688" class="Symbol">:</a> <a id="20690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20669" class="Bound">A</a> <a id="20692" class="Symbol">→</a> <a id="20694" class="PrimitiveType">Set</a> <a id="20698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20657" class="Bound">ℓ</a> <a id="20700" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="20708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20708" class="InductiveConstructor">refl′</a> <a id="20714" class="Symbol">:</a> <a id="20716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20681" class="Bound">x</a> <a id="20718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20651" class="Datatype Operator">≡′</a> <a id="20721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20681" class="Bound">x</a>{% endraw %}</pre>
Similarly, here is the generalised definition of symmetry.
<pre class="Agda">{% raw %}<a id="sym′"></a><a id="20806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20806" class="Function">sym′</a> <a id="20811" class="Symbol">:</a> <a id="20813" class="Symbol">∀</a> <a id="20815" class="Symbol">{</a><a id="20816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20816" class="Bound">ℓ</a> <a id="20818" class="Symbol">:</a> <a id="20820" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="20825" class="Symbol">}</a> <a id="20827" class="Symbol">{</a><a id="20828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20828" class="Bound">A</a> <a id="20830" class="Symbol">:</a> <a id="20832" class="PrimitiveType">Set</a> <a id="20836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20816" class="Bound">ℓ</a><a id="20837" class="Symbol">}</a> <a id="20839" class="Symbol">{</a><a id="20840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20840" class="Bound">x</a> <a id="20842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20842" class="Bound">y</a> <a id="20844" class="Symbol">:</a> <a id="20846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20828" class="Bound">A</a><a id="20847" class="Symbol">}</a>
  <a id="20851" class="Symbol">→</a> <a id="20853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20840" class="Bound">x</a> <a id="20855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20651" class="Datatype Operator">≡′</a> <a id="20858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20842" class="Bound">y</a>
    <a id="20864" class="Comment">------</a>
  <a id="20873" class="Symbol">→</a> <a id="20875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20842" class="Bound">y</a> <a id="20877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20651" class="Datatype Operator">≡′</a> <a id="20880" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20840" class="Bound">x</a>
<a id="20882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20806" class="Function">sym′</a> <a id="20887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20708" class="InductiveConstructor">refl′</a> <a id="20893" class="Symbol">=</a> <a id="20895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20708" class="InductiveConstructor">refl′</a>{% endraw %}</pre>
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.

Here is the generalised definition of Leibniz equality.
<pre class="Agda">{% raw %}<a id="_≐′_"></a><a id="21189" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21189" class="Function Operator">_≐′_</a> <a id="21194" class="Symbol">:</a> <a id="21196" class="Symbol">∀</a> <a id="21198" class="Symbol">{</a><a id="21199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21199" class="Bound">ℓ</a> <a id="21201" class="Symbol">:</a> <a id="21203" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#408" class="Postulate">Level</a><a id="21208" class="Symbol">}</a> <a id="21210" class="Symbol">{</a><a id="21211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21211" class="Bound">A</a> <a id="21213" class="Symbol">:</a> <a id="21215" class="PrimitiveType">Set</a> <a id="21219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21199" class="Bound">ℓ</a><a id="21220" class="Symbol">}</a> <a id="21222" class="Symbol">(</a><a id="21223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21223" class="Bound">x</a> <a id="21225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21225" class="Bound">y</a> <a id="21227" class="Symbol">:</a> <a id="21229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21211" class="Bound">A</a><a id="21230" class="Symbol">)</a> <a id="21232" class="Symbol">→</a> <a id="21234" class="PrimitiveType">Set</a> <a id="21238" class="Symbol">(</a><a id="21239" href="https://agda.github.io/agda-stdlib/Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="21244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21199" class="Bound">ℓ</a><a id="21245" class="Symbol">)</a>
<a id="21247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21189" class="Function Operator">_≐′_</a> <a id="21252" class="Symbol">{</a><a id="21253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21253" class="Bound">ℓ</a><a id="21254" class="Symbol">}</a> <a id="21256" class="Symbol">{</a><a id="21257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21257" class="Bound">A</a><a id="21258" class="Symbol">}</a> <a id="21260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21260" class="Bound">x</a> <a id="21262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21262" class="Bound">y</a> <a id="21264" class="Symbol">=</a> <a id="21266" class="Symbol">∀</a> <a id="21268" class="Symbol">(</a><a id="21269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21269" class="Bound">P</a> <a id="21271" class="Symbol">:</a> <a id="21273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21257" class="Bound">A</a> <a id="21275" class="Symbol">→</a> <a id="21277" class="PrimitiveType">Set</a> <a id="21281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21253" class="Bound">ℓ</a><a id="21282" class="Symbol">)</a> <a id="21284" class="Symbol">→</a> <a id="21286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21269" class="Bound">P</a> <a id="21288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21260" class="Bound">x</a> <a id="21290" class="Symbol">→</a> <a id="21292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21269" class="Bound">P</a> <a id="21294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21262" class="Bound">y</a>{% endraw %}</pre>
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (lsuc ℓ)` as the type of a
term that includes `Set ℓ`.

Further information on levels can be found in the [Agda Wiki][wiki].

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


## Standard library

Definitions similar to those in this chapter can be found in the
standard library.
<pre class="Agda">{% raw %}<a id="21759" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="21813" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="21877" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>{% endraw %}</pre>
Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.


## Unicode

This chapter uses the following unicode.

    ≡  U+2261  IDENTICAL TO (\==)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
