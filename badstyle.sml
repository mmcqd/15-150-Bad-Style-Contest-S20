(****************

  Jacob asked me to write a sorting function in SML, but the type system keeps
  getting in my way. Everyone knows that untyped languages are better anyway
  (if you're mumbling something about "unityped" under your breath, sorry,
  I can't hear you). I'm trying to get poached by Church Inc. (don't tell
  the head TAs!), so I figured I'd use their proprietary language. Thankfully,
  it turns out SML is actually good for one (and only one) thing: directly
  embedding untyped lambda calculus >:)

 ****************)

datatype M = ` of M -> M
val $ = fn (`f,x) => f x
infix $

(* My identity function, please don't take it. Identity theft is not a joke *)
val id  = `(fn x => x)

(* Lazy booleans baybee *)
val tt  = `(fn x => `(fn y => x $ id))
val ff  = `(fn x => `(fn y => y $ id))
val &&  = `(fn a => `(fn b => a $ `(fn _ => b) $ `(fn _ => ff)))


fun to_church_nat 0 = `(fn f => `(fn x => x))
  | to_church_nat n = `(fn f => `(fn x => f $ ((to_church_nat (n-1) $ f $ x))))

val % = to_church_nat

val zero = `(fn f => `(fn x => x))
val succ = `(fn n => `(fn f => `(fn x => f $ (n $ f $ x))))

(* Who needs product types? *)
val Pair = `(fn x => `(fn y => `(fn f => f $ x $ y)))

(* SML functions are actually just macros now *)
val & = fn (x,y) => Pair $ x $ y
infix &
val fst = `(fn p => p $ `(fn x => `(fn _ => x)))
val snd = `(fn p => p $ `(fn _ => `(fn x => x)))

val pred = `(fn n => fst $ (n $ `(fn p => (snd $ p) & (succ $ (snd $ p))) $ (zero & zero)))
val isZ = `(fn n => n $ `(fn x => ff) $ tt)
val ifZ = `(fn n => `(fn z => `(fn s => (isZ $ n) $ `(fn _ => z) $ `(fn _ => s $ (pred $ n)))))
val add = `(fn n => `(fn m => `(fn f => `(fn x => (n $ f) $ (m $ f $ x)))))
val sub = `(fn n => `(fn m => (m $ pred) $ n))
val lte = `(fn n => `(fn m => isZ $ (sub $ n $ m)))

(* Lists are their associated catamorphism *)
(* (Using big PL words actually makes your code go faster) *)
val Nil = `(fn g => `(fn z => z))
val Cons = `(fn x => `(fn xs => `(fn g => `(fn z => g $ x $ (xs $ g $ z)))))
val isNil = `(fn xs => xs $ `(fn _ => `(fn _ => ff)) $ tt)
val hd = `(fn xs => xs $ `(fn y => `(fn _ => y)) $ ff)
val tl = `(fn l => `(fn c => `(fn n => l $ `(fn h => `(fn t => `(fn g => g $ h $ (t $ c)))) $ `(fn t => n) $ `(fn h => `(fn t => t)))))
val matchList = `(fn p => `(fn xs => `(fn nil' => `(fn cons' => (p $ xs) $ `(fn _ => nil') $ `(fn _ => cons' $ (hd $ xs) $ (tl $ xs))))))
val ifNil = matchList $ isNil
val ::: = fn (x,y) => Cons $ x $ y
infixr :::

val to_church_list = foldr op::: Nil

val to_church_int = fn n => if n < 0 then (zero) & (%(~n)) else (%n) & (zero)
val lte_int = `(fn n => `(fn m => lte $ (add $ (fst $ n) $ (snd $ m)) $ (add $ (fst $ m) $ (snd $ n))))


(*
 * I'm running out of val declarations guys, Jacob only gave me so many to
 * use for this contest. Thankfully using lambda calculus makes it easy to
 * turn even "recursive" (I don't see a val rec, do you?) functions into expressions.
 *)

val mergesort = `(fn f => `(fn x => x $ x) $ `(fn x => `(fn y => f $ (x $ x) $ y))) $ `(fn mergesort => `(fn lt => `(fn xs => (ifNil $ xs) $ Nil $ `(fn x => `(fn xs' => (ifNil $ xs') $ (x:::Nil) $ `(fn y => `(fn ys => let val p = (`(fn f => `(fn x => x $ x) $ `(fn x => `(fn y => f $ (x $ x) $ y))) $ `(fn split => `(fn xs => (ifNil $ xs) $ (Nil & Nil) $ `(fn y => `(fn ys => (ifNil $ ys) $ ((y:::Nil) & Nil) $ `(fn z => `(fn zs => let val p = split $ zs in (y:::(fst $ p)) & (z:::(snd $ p)) end))))))) $ xs in (`(fn f => `(fn x => x $ x) $ `(fn x => `(fn y => f $ (x $ x) $ y))) $ `(fn merge => `(fn lt => `(fn xs => `(fn ys => (ifNil $ xs) $ ys $ `(fn x => `(fn xs' => (ifNil $ ys) $ xs $ `(fn y => `(fn ys' => (lt $ x $ y) $ `(fn _ => x:::(merge $ lt $ xs' $ ys)) $ `(fn _ => y:::(merge $ lt $ xs $ ys')) ))))))))) $ lt $ (mergesort $ lt $ (fst $ p)) $ (mergesort $ lt $ (snd $ p)) end )))))))


(*
 * Hurray, we did it! Now we can sort numbers in SML by encoding them into
 * lambda calulus. Except we've run into a problem. Jacob (curse him) wants
 * this sorting function to return an SML list, and we can turn an SML list
 * into a lambda calculus list, but we can't go the other way, since SML
 * is stupid and won't give us back the useless type information we erased...
 * Or can we?
 *)

structure Don'tTryThisAtHomeKids = Unsafe
val ! = fn (`m) => m
val ? = Don'tTryThisAtHome.cast
val ?! = fn x => ?(!x)
val `? = fn x => `(?x)

(*
 * Here's the thing: the lambda terms we get from encoding integers and lists
 * have baaaaaaasically the same structure as the equivalent System F encodings.
 * Maybe if we ask the state of New Jersey really nicely, we can convince the
 * compiler to shove some types back in there...
 *)
val typify_nat : M -> ('a -> 'a) -> 'a -> 'a =
  fn m => fn f => fn x => ?!(!(!m(`?(fn y=> `?(f(?!y)))))(`?x))

val typify_list : M -> ('a -> 'b -> 'b) -> 'b -> 'b =
  fn m => fn g => fn z => ?!(!(!m(`?(fn y=> `?(fn z=> `?(g(y)(?!z))))))(`?z))

val from_church_nat = fn n => typify_nat n (Fn.curry op+ 1) 0

val from_church_int = fn n => from_church_nat (fst $ n) - from_church_nat (snd $ n)

val from_church_int_list = fn xs => typify_list xs (fn x => fn xs => from_church_int x::xs) []



fun >>> (f,g) = g o f
infix >>>

val sort =
  map ((fn x => x*10.0) >>> Real.toInt IEEEReal.TO_NEAREST >>> to_church_int) >>>
  to_church_list >>>
  !(mergesort $ lte_int) >>>
  from_church_int_list >>>
  map (Real.fromInt >>> (fn x => x / 10.0) >>> Real.toString)

