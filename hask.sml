(*                      {-# LANGUAGE LongArrows, DataTypeDec #-}
*)
(*                      --People like to argue whether cons ought to be (:) or (::)
*                       --I take the controversial stance that it really ought to be (:::)
*)

                        datatype
('a,                    'List) a = Nil
                                 | :::
of                                   'a
* ('a,                                'List) a
                        infixr :::
                                                                                                                                                                                                                                                                                                                                                                                                                  open Real
                                                                                                                                                                                                                                                                                                                                                                                                                  val (a,List,Ord,Real,String,-->,==>,merge,split,mergesort,sort,show,$) = ((),Fn.id,Fn.id,(),(),fn _ => [],fn _ => [],(),(),(),(),toString,fn (f,x) => f x);fun `<$> (f,Nil) = Nil | `<$>(f,x:::xs) = f x ::: `<$>(f,xs);fun <$> (f,g) x = `<$>(f, g x);val rec fromList = fn [] => Nil | x::xs => x:::fromList xs;val rec toList = fn Nil => [] | x:::xs => x::toList xs;fun *** (f,g) (a,b) = (f a,g b);fun >>> (f,g) = g o f;infix 7 --> ==>;infixr $ <$> *** >>>


val _ =                 split :: List a --> (List a,List a)
fun                     split Nil          = (Nil,Nil)
|                       split (x:::Nil)    = (x:::Nil,Nil)
|                       split (x:::y:::ys) = let
val                                            (a,b) = split ys
                                             in
                                               (x:::a,y:::b)
end


val _ =                 merge :: Ord a ==> (List a,List a) --> List a
fun                     merge (Nil,b) = b
|                       merge (a,Nil) = a
|                       merge (x:::xs,y:::ys) = if x < y then x:::merge(xs,y:::ys) else y:::merge(x:::xs,ys)

val _ =                 mergesort :: Ord a ==> List a --> List a
fun                     mergesort Nil = Nil
|                       mergesort (x:::Nil) = (x:::Nil)
|                       mergesort xs = let
val                                      (a,b) = split xs
                                       in
                                         merge $ (mergesort *** mergesort) $ split xs
end


val _ =                 sort :: List Real --> List String
val                     sort = fromList >>> (show <$> mergesort) >>> toList
