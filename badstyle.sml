(****************

  Everyone knows that dynamically typed languages are better than statically
  typed languages. So I decided to implement my sorting function in the original
  dynamic language: untyped lambda calculus! I could've implemented a full
  interpreter, but why do all that work? We can just embed LC directly into SML.
  I guess that's the one thing static languages are good for: hosting dynamic ones.

 ****************)

datatype M = ` of M -> M
val ! = fn (`m) => m
val $ = fn (f,x) => !f x
infix $
val `+ = Fn.curry op+

val Y = `(fn f => `(fn x => x $ x) $ `(fn x => `(fn y => f $ (x $ x) $ y)))

fun to_church_nat 0 = `(fn f => `(fn x => x))
  | to_church_nat n = `(fn f => `(fn x => !f (!(!(to_church_nat (n-1)) f) x)))

val % = to_church_nat

val pred =
  `(fn n => `(fn f => `(fn x =>
    n $ `(fn g => `(fn h => h $ (g $ f))) $ `(fn u => x) $ `(fn u => u))))

val id  = `(fn x => x)
val tt  = `(fn x => `(fn y => x $ id))
val ff  = `(fn x => `(fn y => y $ id))
val &&  = `(fn a => `(fn b => a $ `(fn _ => b) $ `(fn _ => ff)))
val isZ = `(fn n => n $ `(fn x => ff) $ tt)
val ifZ = `(fn n => `(fn z => `(fn s => (isZ $ n) $ `(fn _ => z) $ `(fn _ => s $ (pred $ n)))))
val add = `(fn n => `(fn m => `(fn f => `(fn x => (n $ f) $ (m $ f $ x)))))
val sub = `(fn n => `(fn m => (m $ pred) $ n))
val lte = `(fn n => `(fn m => isZ $ (sub $ n $ m)))

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

val Pair = `(fn x => `(fn y => `(fn f => f $ x $ y)))
val & = fn (x,y) => Pair $ x $ y
infix &
val fst = `(fn p => p $ `(fn x => `(fn _ => x)))
val snd = `(fn p => p $ `(fn _ => `(fn x => x)))

val to_church_int = fn n => if n < 0 then (%0) & (%(~n)) else (%n) & (%0)
val lte_int = `(fn n => `(fn m => lte $ (add $ (fst $ n) $ (snd $ m)) $ (add $ (fst $ m) $ (snd $ n))))


(*
 * Frankly we've used far to many declarations at this point. Real lambda
 * calculus doesn't have declarations! I said I wanted dynamic typing, not
 * imperative dynamics!
 *)

val mergesort = `(fn f => `(fn x => x $ x) $ `(fn x => `(fn y => f $ (x $ x) $
y))) $ `(fn mergesort => `(fn lt => `(fn xs => (ifNil $ xs) $ Nil $ `(fn x =>
`(fn xs' => (ifNil $ xs') $ (x:::Nil) $ `(fn y => `(fn ys => let val p = (`(fn f => `(fn x => x $ x) $ `(fn x => `(fn y => f $ (x $ x) $ y))) $ `(fn split => `(fn xs => (ifNil $ xs) $ (Nil & Nil) $ `(fn y => `(fn ys => (ifNil $ ys) $ ((y:::Nil) & Nil) $ `(fn z => `(fn zs => let val p = split $ zs in (y:::(fst $ p)) & (z:::(snd $ p)) end))))))
) $ xs in (`(fn f => `(fn x => x $ x) $ `(fn x => `(fn y => f $ (x $ x) $ y))) $ `(fn merge => `(fn lt => `(fn xs => `(fn ys => (ifNil $ xs) $ ys $ `(fn x => `(fn xs' => (ifNil $ ys) $ xs $ `(fn y => `(fn ys' => (lt $ x $ y) $ `(fn _ => x:::(merge $ lt $ xs' $ ys)) $ `(fn _ => y:::(merge $ lt $ xs $ ys')) ))))))))
) $ lt $ (mergesort $ lt $ (fst $ p)) $ (mergesort $ lt $ (snd $ p)) end )))))))


(*
 * Ok... so we can encode our list of numbers into lambda calculus, but we can't
 * it back. There's no way to convince the compiler to give us back the type
 * information we erased... Or is there?
 *)

val ? = Unsafe.cast
val ?! = fn x => ?(!x)
val `? = fn x => `(?x)

(*
 * Our encoded lambda terms look just like regular functions!
 * Maybe if we ask really nicely we can get SML/NJ to shove
 * some types back in there
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

