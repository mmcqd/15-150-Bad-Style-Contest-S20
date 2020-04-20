(*****************

  Jacob asked me to write a sorting function in SML, but the type system keeps
  getting in my way. Everyone knows that untyped languages are better anyway
  (if you're mumbling something about "unityped" under your breath, sorry,
  I can't hear you). I'm trying to get poached by Church Inc. (don't tell
  the head TAs!), so I figured I'd use their proprietary language. Thankfully,
  it turns out SML is actually good for one (and only one) thing: directly
  embedding untyped lambda calculus >:)

 *****************)

open Fn

(* Deprecated language features are fun! *)
abstype M = Term of M -> M
with
  val ` = Term
  val ! = fn (Term m) => m
  val $ = fn (m,n) => ! m n
end
infix $

(* My identity function, please don't take it. Identity theft is not a joke *)
val id  = `(fn x => x)


(* Sorry Scott encoding enthusiasts *)
fun to_church_nat 0 = `(fn f => `(fn x => x))
  | to_church_nat n = `(fn f => `(fn x => f $ ((to_church_nat (n-1) $ f $ x))))

val % = to_church_nat

val to_church_list = foldr (fn (a,b) => (`(fn x => `(fn xs => `(fn g => `(fn z => g $ x $ (xs $ g $ z)))))) $ a $ b) (`(fn g => `(fn z => z)))

val to_church_int = fn n => if n < 0 then (`(fn x => `(fn y => `(fn f => f $ x $ y)))) $ ((`(fn f => `(fn x => x)))) $ (%(~n)) else (`(fn x => `(fn y => `(fn f => f $ x $ y)))) $ (%n) $ ((`(fn f => `(fn x => x))))


(*
 * I'm running out of val declarations guys, Jacob only gave me so many to
 * use for this contest. Thankfully using lambda calculus makes it easy to
 * turn even recursive functions into expressions.
 * Lambda calculus doesn't have things like lists and tuples and
 * numbers, so we'll just have to encode them as functions.
 * If you're curious, just check out the wikipedia page on
 * church encoding!
 *)

val mergesort = `(fn f => `(fn x => x $ x) $ `(fn x => `(fn y => f $ (x $ x) $ y))) $ `(fn mergesort => `(fn lt => `(fn xs => ((`(fn xs => `(fn nil' => `(fn cons' => ((`(fn xs => xs $ `(fn _ => `(fn _ => (`(fn x => `(fn y => y $ id))))) $ (`(fn x => `(fn y => x $ id))))) $ xs) $ `(fn _ => nil') $ `(fn _ => cons' $ ((`(fn xs => xs $ `(fn y => `(fn _ => y)) $ (`(fn x => `(fn y => y $ id))))) $ xs) $ ((`(fn l => `(fn c => `(fn n => l $ `(fn h => `(fn t => `(fn g => g $ h $ (t $ c)))) $ `(fn t => n) $ `(fn h => `(fn t => t)))))) $ xs)))))) $ xs) $ (`(fn g => `(fn z => z))) $ `(fn x => `(fn xs' => ((`(fn xs => `(fn nil' => `(fn cons' => ((`(fn xs => xs $ `(fn _ => `(fn _ => (`(fn x => `(fn y => y $ id))))) $ (`(fn x => `(fn y => x $ id))))) $ xs) $ `(fn _ => nil') $ `(fn _ => cons' $ ((`(fn xs => xs $ `(fn y => `(fn _ => y)) $ (`(fn x => `(fn y => y $ id))))) $ xs) $ ((`(fn l => `(fn c => `(fn n => l $ `(fn h => `(fn t => `(fn g => g $ h $ (t $ c)))) $ `(fn t => n) $ `(fn h => `(fn t => t)))))) $ xs)))))) $ xs') $ ((`(fn x => `(fn xs => `(fn g => `(fn z => g $ x $ (xs $ g $ z)))))) $ x $ (`(fn g => `(fn z => z)))) $ `(fn y => `(fn ys => let val p = (`(fn f => `(fn x => x $ x) $ `(fn x => `(fn y => f $ (x $ x) $ y))) $ `(fn split => `(fn xs => ((`(fn xs => `(fn nil' => `(fn cons' => ((`(fn xs => xs $ `(fn _ => `(fn _ => (`(fn x => `(fn y => y $ id))))) $ (`(fn x => `(fn y => x $ id))))) $ xs) $ `(fn _ => nil') $ `(fn _ => cons' $ ((`(fn xs => xs $ `(fn y => `(fn _ => y)) $ (`(fn x => `(fn y => y $ id))))) $ xs) $ ((`(fn l => `(fn c => `(fn n => l $ `(fn h => `(fn t => `(fn g => g $ h $ (t $ c)))) $ `(fn t => n) $ `(fn h => `(fn t => t)))))) $ xs)))))) $ xs) $ ((`(fn x => `(fn y => `(fn f => f $ x $ y)))) $ (`(fn g => `(fn z => z))) $ (`(fn g => `(fn z => z)))) $ `(fn y => `(fn ys => ((`(fn xs => `(fn nil' => `(fn cons' => ((`(fn xs => xs $ `(fn _ => `(fn _ => (`(fn x => `(fn y => y $ id))))) $ (`(fn x => `(fn y => x $ id))))) $ xs) $ `(fn _ => nil') $ `(fn _ => cons' $ ((`(fn xs => xs $ `(fn y => `(fn _ => y)) $ (`(fn x => `(fn y => y $ id))))) $ xs) $ ((`(fn l => `(fn c => `(fn n => l $ `(fn h => `(fn t => `(fn g => g $ h $ (t $ c)))) $ `(fn t => n) $ `(fn h => `(fn t => t)))))) $ xs)))))) $ ys) $ ((`(fn x => `(fn y => `(fn f => f $ x $ y)))) $ ((`(fn x => `(fn xs => `(fn g => `(fn z => g $ x $ (xs $ g $ z)))))) $ y $ (`(fn g => `(fn z => z)))) $ (`(fn g => `(fn z => z)))) $ `(fn z => `(fn zs => let val p = split $ zs in (`(fn x => `(fn y => `(fn f => f $ x $ y)))) $ ((`(fn x => `(fn xs => `(fn g => `(fn z => g $ x $ (xs $ g $ z)))))) $ y $ ((`(fn p => p $ `(fn x => `(fn _ => x)))) $ p)) $ ((`(fn x => `(fn xs => `(fn g => `(fn z => g $ x $ (xs $ g $ z)))))) $ z $ ((`(fn p => p $ `(fn _ => `(fn x => x)))) $ p)) end))))))) $ xs in (`(fn f => `(fn x => x $ x) $ `(fn x => `(fn y => f $ (x $ x) $ y))) $ `(fn merge => `(fn lt => `(fn xs => `(fn ys => ((`(fn xs => `(fn nil' => `(fn cons' => ((`(fn xs => xs $ `(fn _ => `(fn _ => (`(fn x => `(fn y => y $ id))))) $ (`(fn x => `(fn y => x $ id))))) $ xs) $ `(fn _ => nil') $ `(fn _ => cons' $ ((`(fn xs => xs $ `(fn y => `(fn _ => y)) $ (`(fn x => `(fn y => y $ id))))) $ xs) $ ((`(fn l => `(fn c => `(fn n => l $ `(fn h => `(fn t => `(fn g => g $ h $ (t $ c)))) $ `(fn t => n) $ `(fn h => `(fn t => t)))))) $ xs)))))) $ xs) $ ys $ `(fn x => `(fn xs' => ((`(fn xs => `(fn nil' => `(fn cons' => ((`(fn xs => xs $ `(fn _ => `(fn _ => (`(fn x => `(fn y => y $ id))))) $ (`(fn x => `(fn y => x $ id))))) $ xs) $ `(fn _ => nil') $ `(fn _ => cons' $ ((`(fn xs => xs $ `(fn y => `(fn _ => y)) $ (`(fn x => `(fn y => y $ id))))) $ xs) $ ((`(fn l => `(fn c => `(fn n => l $ `(fn h => `(fn t => `(fn g => g $ h $ (t $ c)))) $ `(fn t => n) $ `(fn h => `(fn t => t)))))) $ xs)))))) $ ys) $ xs $ `(fn y => `(fn ys' => (lt $ x $ y) $ `(fn _ => (`(fn x => `(fn xs => `(fn g => `(fn z => g $ x $ (xs $ g $ z)))))) $ x $ (merge $ lt $ xs' $ ys)) $ `(fn _ => (`(fn x => `(fn xs => `(fn g => `(fn z => g $ x $ (xs $ g $ z)))))) $ y $ (merge $ lt $ xs $ ys')) ))))))))) $ lt $ (mergesort $ lt $ ((`(fn p => p $ `(fn x => `(fn _ => x)))) $ p)) $ (mergesort $ lt $ ((`(fn p => p $ `(fn _ => `(fn x => x)))) $ p)) end ))))))) $ (`(fn n => `(fn m => (`(fn n => `(fn m => (`(fn n => n $ `(fn x => (`(fn x => `(fn y => y $ id)))) $ (`(fn x => `(fn y => x $ id))))) $ ((`(fn n => `(fn m => (m $ (`(fn n => (`(fn p => p $ `(fn x => `(fn _ => x)))) $  (n $ `(fn p => (`(fn x => `(fn y => `(fn f => f $ x $ y)))) $ ((`(fn p => p $ `(fn _ => `(fn x => x)))) $ p) $   ((`(fn n => `(fn f => `(fn x => f $ (n $ f $ x))))) $ ((`(fn p => p $ `(fn _ => `(fn x => x)))) $ p))) $ ((`(fn x => `(fn y => `(fn f => f $ x $ y)))) $ (`(fn f => `(fn x => x))) $ (`(fn f => `(fn x =>     x)))))))) $ n))) $ n $ m)))) $ ((`(fn n => `(fn m => `(fn f => `(fn x => (n $ f) $ (m $ f $ x)))))) $ ((`(fn p => p $ `(fn x => `(fn _ => x)))) $ n) $ ((`(fn p => p $ `(fn _ => `(fn x => x)))) $ m)) $ ((`(fn n => `(fn m => `(fn f => `(fn x => (n $ f) $ (m $ f $ x)))))) $ ((`(fn p => p $ `(fn x => `(fn _ => x)))) $ m) $ ((`(fn p => p $ `(fn _ => `(fn x => x)))) $ n))))
)


(*
 * Hurray, we did it! Now we can sort numbers in SML by encoding them into
 * lambda calulus. Except we've run into a problem. Jacob (curse him) wants
 * this sorting function to return an SML list, and we can turn an SML list
 * into a lambda calculus list, but we can't go the other way, since SML
 * is stupid and won't give us back the useless type information we erased...
 * Or can we?
 *)

structure Don'tTryThisAtHomeKids = Unsafe
val ? = Don'tTryThisAtHomeKids.cast
val ?! = fn x => ?(!x)
val `? = fn x => `(?x)

(* Why should function application/composition only go in one, consistent direction? *)
fun --> (x,f) = f x
fun ==> (f,g) = g o f
fun <-- (f,x) = f x
fun <== (f,g) = f o g
infixr <-- ==>
infix 1 --> <==


(*
 * If you're already familiar with church encodings, then perhaps you've been
 * bored so far. Here's the fun part.
 * Notice: the lambda terms we get from encoding integers and lists
 * have basically the same structure as the equivalent System F encodings.
 * They just lack the relevant type.
 * Maybe if we ask the state of New Jersey really nicely, we can convince the
 * compiler to shove some types back in there...
 * (I've obfuscated these for maximum *bad style*, see explanation at the end)
 *)
val typify_nat : M -> ('a -> 'a) -> 'a -> 'a =
  fn m => fn f => `? ==> ?! <== !(!m(`?(?! ==> `? <== f)))


val typify_list : M -> (M -> 'b -> 'b) -> 'b -> 'b =
  fn m => fn g => `? ==> ?! <== !(!m(`?(fn y=> `?(?! ==> `? <== g y))))

val from_church_nat = fn n => typify_nat n (curry op+ 1) 0

val from_church_int = fn n => from_church_nat ((`(fn p => p $ `(fn x => `(fn _ => x)))) $ n) - from_church_nat ((`(fn p => p $ `(fn _ => `(fn x => x)))) $ n)

val from_church_int_list = fn xs => typify_list xs (fn x => fn xs => from_church_int x::xs) []


val sort = fn x =>
  map (fn x => Real.toString <-- x --> Real.fromInt --> curry (flip op/) 10.0) <--
  from_church_int_list <--
  !mergesort <--
  x -->
  map (fn x => to_church_int <-- Real.toInt IEEEReal.TO_NEAREST <-- x --> curry op* 10.0) -->
  to_church_list


(****************

So what’s going on here? The idea is that we want to take our lambda calculus functions,
and make them operate on regular SML functions. Of course the issue is that lambda terms
can only operate on other lambda terms (according to the type system at least). You might
think to just Unsafe.cast this restriction away, but that won't work. When we apply a
lambda term, we first unpack it, stripping the Term constructor. If SML/NJ tries to do this
to a plain old function, we get a runtime error. What we ultimately need is a way to lift
plain SML values into lambda terms, which allows us to use actual lambda terms as basically
vehicles for function application, and then extract the result at the end. The first step
to solving this is being able to turn arbitrary SML values into lambda terms.
*)
val into0 = fn x => `(? x)
(*
Notice that into0 == `?. It Unsafe.casts a value to have type M -> M, and then applies `,
which is an alias for the Term constructor (which is hidden by the long since deprecated
abstype interface, just to be silly). Now we can have things like (Term (fn x => x+1))
and (Term 1). This is useful, but it isn’t enough. What if we try to apply a hidden function to a hidden argument?

(Term (fn x => x+1)) $ (Term 1) ==> (fn x => x+1) (Term 1).

Note that in this expression, (fn x => x+1) actually has type M -> M, so there’s no type
errors here, but there will be a runtime error when we try to add 1 to (Term 1). So we’ll
need to unpack the argument before supplying it to our function. First, we need a way to
extract the arbitrary values we’ve hidden in a Term.
*)
val out = fn x => ?(! x)
(*
Notice that  out == ?!. It strips a Term constructor, and then Unsafe.casts from M -> M to
whatever we want. Now we work on effectively lifting functions. A first attempt might be:
*)
val into1 = fn f => into0 (f o out)
(*
This almost works. The issue is that once we apply this thing, we’ll be left with value with
no Term wrapper. This becomes a problem if we want to apply anymore lambda calculus functions
to our result. To complete this, we need to hide the result of f.
*)
val into1 = fn f => into0 (into0 o f o out)
(*
Now we can lift 1-ary functions and their arguments into lambda terms. Check it out:

into1 (fn x => x+1) $ into0 1 ⇒
into0 (into0 o (fn x => x+1) o out) $ into0 1 ⇒
Term (into0 o (fn x => x+1) o out) $ Term 1 ⇒
(into0 o (fn x => x+1) o out) (Term 1) ⇒
into0 ((fn x => x+1) (out (Term 1))) ⇒
into0 ((fn x => x+1) 1) ⇒
Into0 2 ⇒
Term 2

We can then use out to extract 2 from (Term 2). Now we can turn a church encoded nat in untyped
lambda calculus into a church encoded nat into a value of type (‘a -> ‘a) -> ‘a -> ‘a by lifting
the two arguments into lambda terms, using the church nat to apply them, and finally extracting
the result. Using our nice names:
*)
val typify_nat : M -> ('a -> 'a) -> 'a -> 'a =
  fn m => fn f => fn x => out (m $ (into1 f) $ (into0 x))
(*
Typifying church lists is a similar process, except we now have to lift a
curried function whose first argument is an actual lambda term.
*)
val into2 = fn f => into0 (fn y => into0 (into0 o (f y) o out))

val typify_list : M -> (M -> 'b -> 'b) -> 'b -> 'b =
  fn m => fn g => fn z => out(m $ (into2 g) $ (into0 z))
(*
*****************)
