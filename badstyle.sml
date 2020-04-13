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


fun to_church_nat 0 = `(fn f => `(fn x => x))
  | to_church_nat n = `(fn f => `(fn x => f $ ((to_church_nat (n-1) $ f $ x))))

val % = to_church_nat

val to_church_list = foldr (fn (a,b) => (`(fn x => `(fn xs => `(fn g => `(fn z => g $ x $ (xs $ g $ z)))))) $ a $ b) (`(fn g => `(fn z => z)))

val to_church_int = fn n => if n < 0 then (`(fn x => `(fn y => `(fn f => f $ x $ y)))) $ ((`(fn f => `(fn x => x)))) $ (%(~n)) else (`(fn x => `(fn y => `(fn f => f $ x $ y)))) $ (%n) $ ((`(fn f => `(fn x => x))))


(*
 * I'm running out of val declarations guys, Jacob only gave me so many to
 * use for this contest. Thankfully using lambda calculus makes it easy to
 * turn even "recursive" (I don't see a val rec, do you?) functions into expressions.
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
val ! = fn (`m) => m
val ? = Don'tTryThisAtHomeKids.cast
val ?! = fn x => ?(!x)
val `? = fn x => `(?x)

(*
 * If you're already familiar with church encodings, then perhaps you've been
 * bored so far. Here's the real magic.
 * Notice: the lambda terms we get from encoding integers and lists
 * have baaaaaaasically the same structure as the equivalent System F encodings.
 * They just lack the relevant type.
 * Maybe if we ask the state of New Jersey really nicely, we can convince the
 * compiler to shove some types back in there...
 *)
val typify_nat : M -> ('a -> 'a) -> 'a -> 'a =
  fn m => fn f => fn x => ?!(!(!m(`?(fn y=> `?(f(?!y)))))(`?x))

val typify_list : M -> ('a -> 'b -> 'b) -> 'b -> 'b =
  fn m => fn g => fn z => ?!(!(!m(`?(fn y=> `?(fn z=> `?(g(y)(?!z))))))(`?z))

val from_church_nat = fn n => typify_nat n (Fn.curry op+ 1) 0

val from_church_int = fn n => from_church_nat ((`(fn p => p $ `(fn x => `(fn _ => x)))) $ n) - from_church_nat ((`(fn p => p $ `(fn _ => `(fn x => x)))) $ n)

val from_church_int_list = fn xs => typify_list xs (fn x => fn xs => from_church_int x::xs) []



fun >>> (f,g) = g o f
infix >>>

val sort =
  map ((fn x => x*10.0) >>> Real.toInt IEEEReal.TO_NEAREST >>> to_church_int) >>>
  to_church_list >>>
  !mergesort >>>
  from_church_int_list >>>
  map (Real.fromInt >>> (fn x => x / 10.0) >>> Real.toString)

