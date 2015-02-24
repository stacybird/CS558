
(defsig EnvSig
  (sig (type (Env a))
       (data (Result a) (#found a) (#notFound)) 
       (val lookup ((Env a) -> Int -> (Result a)))
       (val extend (Int -> a -> (Env a) -> (Env a)))
       (val empty (Env a))))
